(* jpl_ast.ml — the SHARED READER for the JPL.5 tool family (front end + emitter).

 * Extracted from jpl_front.ml at 5-B.2 so the emitter consumes exactly the same
 * reading the subset gate is built on, instead of re-implementing a second
 * resolution of the artifact's AST.  One reader, two consumers: that is the
 * single-source rule applied on the tooling side (JPL.md §Design) — two
 * independent AST walks over the same bytes is how a transpiler starts
 * disagreeing with its own gate.

 * Contents: the implementation environment (bindings, arity, recursion, mutual
 * groups), the interface environment (value signatures, type declarations and
 * their constructors), the emitter's DECLARED subset, the per-binding
 * measurement (expression/pattern class census, allocation census, edges, and
 * the self-call count that distinguishes a loop from a nat-destruct), the
 * root-parameterised transitive closure, the TYPE VOCABULARY the closure reaches
 * (§6 — the domain of the C layout table, shared so the reporter and the emitter
 * cannot compute two domains), and the roots as a CLI parameter (§7).

 * It READS the artifact and re-encodes no kernel semantics.

 * OCaml 5.5 Parsetree facts measured while writing this (each was a compile error
 * first, so they are recorded here rather than re-derived by trial; also in
 * JPL.md's HISTORY):  Parsetree.constant is a RECORD {pconst_desc; pconst_loc}
 * and Pconst_integer of string * char option absorbs the old int32/int64/nativeint
 * constructors (the suffix is the char option); case fields are pc_lhs / pc_guard
 * / pc_rhs; Longident is Ldot of t loc * string loc with BOTH components located;
 * Ppat_record and Ppat_tuple carry a closed_flag and Ppat_tuple's elements are
 * (string option * pattern) pairs; Ppat_construct carries
 * (string loc list * pattern) option while Ppat_variant carries a PLAIN string
 * label; Pexp_fun is GONE — `fun x -> e` and `function | p -> e` are both
 * Pexp_function of function_param list * type_constraint option * function_body,
 * so a binding's syntactic arity is the length of its parameter list and a bare
 * `function` is params = [] with a Pfunction_cases body; Pexp_open /
 * Pexp_letmodule / Pexp_letexception are folded into Pexp_struct_item;
 * Ptyp_tuple is (string option * core_type) list; Psig_typesubst takes ONE
 * argument list; Pexp_ifthenelse's else branch is an expression option; and
 * Ast_mapper.mapper is a RECORD of functions, NOT a class, which is why the
 * traversal below is Ast_iterator.iterator over default_iterator with open
 * recursion through `self`. *)
open Parsetree
open Asttypes
open Longident

let bump t k = Hashtbl.replace t k (try Hashtbl.find t k + 1 with Not_found -> 1)
let add t k n = Hashtbl.replace t k (try Hashtbl.find t k + n with Not_found -> n)

let fail msg =
  prerr_endline ("jpl: FATAL: " ^ msg);
  exit 2

let li =
  let rec go = function
    | Lident s -> s
    | Ldot (m, s) -> go m.txt ^ "." ^ s.txt
    | Lapply _ -> "?"
  in
  go

(* ─────────────────────── 1. the implementation: bindings ─────────────────── *)

type binding =
  { b_rec : bool; b_mutual : bool; b_arity : int; b_body : expression }

let binds : (string, binding) Hashtbl.t = Hashtbl.create 200
let bind_order : string list ref = ref []
let mutual_groups = ref 0

let rec pat_vars p acc =
  match p.ppat_desc with
  | Ppat_var { txt } -> txt :: acc
  | Ppat_alias (p, { txt }) -> txt :: pat_vars p acc
  | Ppat_tuple (l, _) -> List.fold_left (fun a (_, p) -> pat_vars p a) acc l
  | Ppat_array l -> List.fold_right pat_vars l acc
  | Ppat_or (a, b) -> pat_vars b (pat_vars a acc)
  | Ppat_constraint (p, _) -> pat_vars p acc
  | Ppat_construct (_, Some (_, p)) -> pat_vars p acc
  | Ppat_variant (_, Some p) -> pat_vars p acc
  | Ppat_record (flds, _) -> List.fold_left (fun a (_, p) -> pat_vars p a) acc flds
  | Ppat_lazy p -> pat_vars p acc
  | Ppat_open (_, p) -> pat_vars p acc
  | Ppat_exception p -> pat_vars p acc
  | Ppat_effect (p, q) -> pat_vars q (pat_vars p acc)
  | _ -> acc

(* A binding's arity is its leading parameter list; a bare `function | …` has an
   empty one, which is why the emitter must read the body shape as well. *)
let syntactic_arity e =
  match e.pexp_desc with
  | Pexp_function (ps, _, _) ->
      List.fold_left
        (fun k (p : function_param) ->
          match p.pparam_desc with Pparam_val _ -> k + 1 | Pparam_newtype _ -> k)
        0 ps
  | _ -> 0

let nm_of_pat p =
  match p.ppat_desc with
  | Ppat_var { txt } -> txt
  | Ppat_alias (_, { txt }) -> txt
  | _ -> "?"

let rec add_struct prefix items =
  List.iter
    (fun (i : structure_item) ->
      match i.pstr_desc with
      | Pstr_value (rf, bs) ->
          let mutual = rf = Recursive && List.length bs > 1 in
          if mutual then incr mutual_groups;
          List.iter
            (fun (vb : value_binding) ->
              let nm = nm_of_pat vb.pvb_pat in
              let full = if prefix = "" then nm else prefix ^ "." ^ nm in
              if not (Hashtbl.mem binds full) then begin
                Hashtbl.replace binds full
                  { b_rec = rf = Recursive; b_mutual = mutual;
                    b_arity = syntactic_arity vb.pvb_expr; b_body = vb.pvb_expr };
                bind_order := full :: !bind_order
              end)
            bs
      | Pstr_module { pmb_name = { txt = Some nm; _ };
                      pmb_expr = { pmod_desc = Pmod_structure inner; _ }; _ } ->
          add_struct (if prefix = "" then nm else prefix ^ "." ^ nm) inner
      | _ -> ())
    items

(* ─────────────────────── 2. the interface: types and signatures ──────────── *)

let vals : (string, core_type) Hashtbl.t = Hashtbl.create 200
let tydecls : (string, type_declaration) Hashtbl.t = Hashtbl.create 40
let tycons : (string, int) Hashtbl.t = Hashtbl.create 40

let rec cty t =
  match t.ptyp_desc with
  | Ptyp_any -> "_"
  | Ptyp_var v -> "'" ^ v
  | Ptyp_arrow (_, a, b) ->
      let left = match a.ptyp_desc with Ptyp_arrow _ -> "(" ^ cty a ^ ")" | _ -> cty a in
      left ^ " -> " ^ cty b
  | Ptyp_tuple l -> "(" ^ String.concat " * " (List.map (fun (_, t) -> cty t) l) ^ ")"
  | Ptyp_constr ({ txt }, []) -> li txt
  | Ptyp_constr ({ txt }, [ a ]) -> cty a ^ " " ^ li txt
  | Ptyp_constr ({ txt }, l) -> "(" ^ String.concat ", " (List.map cty l) ^ ") " ^ li txt
  | Ptyp_alias (a, _) -> cty a
  | Ptyp_variant (_, _, _) -> "[`…]"
  | Ptyp_poly (_, t) -> cty t
  | Ptyp_package _ -> "(module …)"
  | Ptyp_object _ -> "object …"
  | Ptyp_class _ -> "#…"
  | Ptyp_open (_, t) -> cty t
  | Ptyp_extension _ -> "[%%…]"
  | Ptyp_functor _ -> "functor …"

and tycon_names t =
  match t.ptyp_desc with
  | Ptyp_constr ({ txt }, l) -> [ li txt ] @ List.concat_map tycon_names l
  | Ptyp_arrow (_, a, b) -> tycon_names a @ tycon_names b
  | Ptyp_tuple l -> List.concat_map (fun (_, t) -> tycon_names t) l
  | Ptyp_alias (a, _) -> tycon_names a
  | Ptyp_poly (_, t) -> tycon_names t
  | Ptyp_open (_, t) -> tycon_names t
  | _ -> []

let collect_tycons t =
  match t.ptyp_desc with
  | Ptyp_constr ({ txt }, _) -> bump tycons (li txt)
  | _ -> ()

let add_sig items =
  List.iter
    (fun (i : signature_item) ->
      match i.psig_desc with
      | Psig_value { pval_name = { txt }; pval_type = t; _ } ->
          Hashtbl.replace vals txt t
      | Psig_type (_, ds) | Psig_typesubst ds ->
          List.iter (fun (d : type_declaration) ->
            Hashtbl.replace tydecls d.ptype_name.txt d) ds
      | _ -> ())
    items

(* ─────────────────────── 3. the supported subset ────────────────────────── *)

(* JPL.5's DECLARED subset: the constructs the emitter being built in JPL.5 is
   specified to lower by layout.  Anything else in the shipped closure is a hard
   failure, not a TODO — the fix belongs on the Rocq side (as 5-A.2/3/7 did for
   glob, setv and the expander), never in a silent fallback here. *)
let supported_expr =
  [ "ident"; "constant"; "function"; "apply"; "match"; "if"; "let"; "tuple";
    "construct"; "variant"; "record"; "field" ]

let supported_pat =
  [ "any"; "var"; "constant"; "tuple"; "construct"; "variant"; "or" ]

let eclass e =
  match e.pexp_desc with
  | Pexp_ident _ -> "ident"
  | Pexp_constant _ -> "constant"
  | Pexp_function _ -> "function"
  | Pexp_apply _ -> "apply"
  | Pexp_match _ -> "match"
  | Pexp_ifthenelse _ -> "if"
  | Pexp_let (Nonrecursive, _, _) -> "let"
  | Pexp_let (Recursive, _, _) -> "LET-REC (nested)"
  | Pexp_sequence _ -> "SEQUENCE (;)"
  | Pexp_tuple _ -> "tuple"
  | Pexp_construct _ -> "construct"
  | Pexp_variant _ -> "variant"
  | Pexp_record _ -> "record"
  | Pexp_field _ -> "field"
  | Pexp_try _ -> "TRY"
  | Pexp_while _ -> "while (already a loop)"
  | Pexp_for _ -> "for (already a loop)"
  | Pexp_array _ -> "ARRAY literal"
  | Pexp_setfield _ -> "MUTATION setfield"
  | Pexp_constraint _ -> "type constraint"
  | Pexp_coerce _ -> "coercion"
  | Pexp_lazy _ -> "LAZY"
  | Pexp_assert _ -> "ASSERT"
  | Pexp_letop _ -> "let operator"
  | Pexp_struct_item _ -> "let module / open"
  | Pexp_pack _ -> "first-class module"
  | Pexp_extension _ -> "extension point"
  | Pexp_newtype _ -> "newtype"
  | Pexp_poly _ -> "method"
  | Pexp_object _ -> "object"
  | Pexp_send _ -> "method call"
  | Pexp_new _ -> "class"
  | Pexp_setinstvar _ -> "MUTATION instance var"
  | Pexp_override _ -> "object override"
  | Pexp_unreachable -> "false-elimination"

let pclass p =
  match p.ppat_desc with
  | Ppat_any -> "any"
  | Ppat_var _ -> "var"
  | Ppat_alias _ -> "ALIAS (as)"
  | Ppat_constant _ -> "constant"
  | Ppat_interval _ -> "INTERVAL (a..b)"
  | Ppat_tuple _ -> "tuple"
  | Ppat_construct _ -> "construct"
  | Ppat_variant _ -> "variant"
  | Ppat_record _ -> "RECORD pattern"
  | Ppat_array _ -> "ARRAY pattern"
  | Ppat_or _ -> "or (|)"
  | Ppat_constraint _ -> "type constraint"
  | Ppat_type _ -> "in-line record field"
  | Ppat_lazy _ -> "LAZY"
  | Ppat_unpack _ -> "module unpack"
  | Ppat_exception _ -> "EXCEPTION pattern"
  | Ppat_effect _ -> "EFFECT pattern"
  | Ppat_extension _ -> "extension point"
  | Ppat_open _ -> "qualified pattern"

(* ─────────────────────── 4. per-binding measurement ─────────────────────── *)

type measure =
  { e_cnt : (string, int) Hashtbl.t;   (* expression classes *)
    p_cnt : (string, int) Hashtbl.t;   (* pattern classes *)
    edges : (string, unit) Hashtbl.t;  (* calls to other top-level bindings *)
    alloc : (string, int) Hashtbl.t;   (* value-building sites *)
    ctors : (string, int) Hashtbl.t;   (* variant constructors, pattern or expr *)
    fuel : int ref;                    (* nat-decrement idioms *)
    self : int ref }                   (* direct self-calls *)

let mk () =
  { e_cnt = Hashtbl.create 16; p_cnt = Hashtbl.create 16;
    edges = Hashtbl.create 16; alloc = Hashtbl.create 16;
    ctors = Hashtbl.create 16; fuel = ref 0; self = ref 0 }

(* The idiom ExtrOcamlNatInt emits for every Coq Fixpoint that recurses on a
   nat:   (fun fO fS n -> if n = 0 then fO () else fS (n - 1)) <base> <step> <fuel>
   Recognising it lets the emitter turn a recursion into `while` by reading the
   loop's condition and decrement off the artifact, instead of inventing its own
   fuel law. *)
let pv_name = function
  | { pparam_desc = Pparam_val (_, _, { ppat_desc = Ppat_var { txt }; _ }); _ } -> Some txt
  | _ -> None

(* small recognisers, each reading one node of the idiom, so the shapes are
   checkable independently instead of nesting six deep in one pattern *)
let is_ident0 op e =
  match e.pexp_desc with
  | Pexp_ident { txt = Lident s; _ } -> s = op
  | _ -> false

let is_nat_lit k e =
  match e.pexp_desc with
  | Pexp_constant { pconst_desc = Pconst_integer (s, None); _ } -> s = string_of_int k
  | _ -> false

let is_var e =
  match e.pexp_desc with
  | Pexp_ident { txt = Lident s; _ } -> Some s
  | _ -> None

(* `(fun fO fS n -> if n = 0 then fO () else fS (n - 1)) base step fuel` *)
let is_fuel_idiom (ps : function_param list) (body : function_body) =
  match ps, body with
  | [ a; b; c ],
    Pfunction_body { pexp_desc = Pexp_ifthenelse (test, base, Some step); _ } ->
      let names =
        match pv_name a, pv_name b, pv_name c with
        | Some x, Some y, Some z -> Some (x, y, z)
        | _ -> None
      in
      (match names with
       | Some (fO, fS, n) when fO <> fS && fS <> n && fO <> n ->
           (* test: n = 0 *)
           (match test.pexp_desc with
            | Pexp_apply (f, [ (Nolabel, x); (Nolabel, y) ]) when is_ident0 "=" f ->
                is_var x = Some n && is_nat_lit 0 y
            | _ -> false)
           && (* base: fO () *)
           (match base.pexp_desc with
            | Pexp_apply (f, [ (Nolabel, arg) ]) when is_ident0 fO f ->
                (match arg.pexp_desc with
                 | Pexp_construct ({ txt = Lident "()"; _ }, None) -> true
                 | _ -> false)
            | _ -> false)
           && (* step: fS (n - 1) *)
           (match step.pexp_desc with
            | Pexp_apply (f, [ (Nolabel, inner) ]) when is_ident0 fS f ->
                (match inner.pexp_desc with
                 | Pexp_apply (g, [ (Nolabel, p); (Nolabel, q) ]) when is_ident0 "-" g ->
                     is_var p = Some n && is_nat_lit 1 q
                 | _ -> false)
            | _ -> false)
       | _ -> false)
  | _ -> false

let cur : measure ref = ref (mk ())
let sh : string list ref = ref []
let root : string ref = ref ""

let rec it : Ast_iterator.iterator =
  { Ast_iterator.default_iterator with
    expr =
      (fun self e ->
        let m = !cur in
        bump m.e_cnt (eclass e);
        (match e.pexp_desc with
         | Pexp_ident { txt = Lident s } ->
             if not (List.mem s !sh) && Hashtbl.mem binds s then begin
               Hashtbl.replace m.edges s ();
               if s = !root then incr m.self
             end
         | Pexp_constant { pconst_desc = c } ->
             (match c with
              | Pconst_integer (_, None) -> bump m.alloc "literal: nat"
              | Pconst_integer (_, Some ch) ->
                  bump m.alloc ("literal: suffixed-int" ^ String.make 1 ch)
              | Pconst_char _ -> bump m.alloc "literal: char"
              | Pconst_string _ -> bump m.alloc "literal: string"
              | Pconst_float _ -> bump m.alloc "literal: float")
         | Pexp_construct ({ txt }, eo) ->
             let nm = li txt in
             bump m.ctors nm;
             (match nm with
              | "::" -> bump m.alloc "cons  (one value cell)"
              | "[]" -> bump m.alloc "nil   (no cell)"
              | "Some" | "None" -> bump m.alloc ("option " ^ nm)
              | "()" -> bump m.alloc "unit"
              | _ -> bump m.alloc ("ctor " ^ nm))
         | Pexp_variant (n, eo) ->
             bump m.ctors ("`" ^ n);
             if eo <> None then bump m.alloc ("variant `" ^ n)
         | Pexp_tuple _ -> bump m.alloc "tuple (value cell)"
         | Pexp_record (flds, _) ->
             bump m.alloc ("record (" ^ string_of_int (List.length flds) ^ " fields)")
         | Pexp_function (ps, _, body) ->
             if is_fuel_idiom ps body then incr m.fuel
         | _ -> ());
        let n0 = List.length !sh in
        (match e.pexp_desc with
         | Pexp_function (ps, _, _) ->
             List.iter (fun (p : function_param) ->
               match p.pparam_desc with
               | Pparam_val (_, _, pat) -> sh := pat_vars pat [] @ !sh
               | Pparam_newtype _ -> ()) ps
         | Pexp_let (_, bs, _) ->
             List.iter (fun (vb : value_binding) ->
               sh := pat_vars vb.pvb_pat [] @ !sh) bs
         | Pexp_for (p, _, _, _, _) -> sh := pat_vars p [] @ !sh
         | _ -> ());
        Ast_iterator.default_iterator.expr self e;
        sh := List.filteri (fun i _ -> i < n0) !sh);

    (* a case's pattern variables scope over its rhs, so they are pushed around
       the whole case, not only around the pattern *)
    case =
      (fun self c ->
        if c.pc_guard <> None then bump (!cur).alloc "OFF-SUBSET case guard";
        let n0 = List.length !sh in
        sh := pat_vars c.pc_lhs [] @ !sh;
        Ast_iterator.default_iterator.case self c;
        sh := List.filteri (fun i _ -> i < n0) !sh);

    pat =
      (fun self p ->
        let m = !cur in
        bump m.p_cnt (pclass p);
        (match p.ppat_desc with
         | Ppat_construct ({ txt }, _) -> bump m.ctors ("pat " ^ li txt)
         | Ppat_variant (l, _) -> bump m.ctors ("pat `" ^ l)
         | Ppat_constant _ -> bump m.alloc "pattern literal"
         | _ -> ());
        Ast_iterator.default_iterator.pat self p);

    typ =
      (fun self t ->
        collect_tycons t;
        Ast_iterator.default_iterator.typ self t);
  }

(* ─────────────────────── 5. the closure ─────────────────────────────────── *)

let closure : (string, measure) Hashtbl.t = Hashtbl.create 64
let closure_order : string list ref = ref []

let reach roots =
  let q = ref (List.rev roots) in
  while !q <> [] do
    let n = List.hd !q in
    q := List.tl !q;
    if not (Hashtbl.mem binds n) then
      fail (Printf.sprintf "root %s is not a binding of the implementation" n)
    else if not (Hashtbl.mem closure n) then begin
      let m = mk () in
      cur := m;
      root := n;
      sh := [];
      it.expr it (Hashtbl.find binds n).b_body;
      Hashtbl.replace closure n m;
      closure_order := n :: !closure_order;
      Hashtbl.iter (fun e _ -> if not (Hashtbl.mem closure e) then q := e :: !q) m.edges
    end
  done

(* ─────────────────────── 6. the type vocabulary ─────────────────────────── *)

(* Every type NAMED by a closure signature, closed under the artifact's own type
   declarations, plus the census of the built-in type constructors reached.
   This is the DOMAIN of the C layout table: a declaration the shipped closure
   does not reach must not be emitted (no unused code), and one it reaches must
   be laid out from the .mli rather than from memory.  It lives in the shared
   reader because the reporter prints it and the emitter consumes it — the two
   must not compute two different domains over the same bytes. *)
let vocab : (string, unit) Hashtbl.t = Hashtbl.create 20
let builtins : (string, int) Hashtbl.t = Hashtbl.create 10

let rec add_vocab_type name =
  if not (Hashtbl.mem vocab name) && Hashtbl.mem tydecls name then begin
    Hashtbl.replace vocab name ();
    let d = Hashtbl.find tydecls name in
    let add_ct t =
      List.iter
        (fun c -> if Hashtbl.mem tydecls c then add_vocab_type c else bump builtins c)
        (tycon_names t)
    in
    (match d.ptype_manifest with Some t -> add_ct t | None -> ());
    match d.ptype_kind with
    | Ptype_variant cs ->
        List.iter
          (fun (c : constructor_declaration) ->
            match c.pcd_args with
            | Pcstr_tuple l -> List.iter add_ct l
            | Pcstr_record ls ->
                List.iter (fun (l : label_declaration) -> add_ct l.pld_type) ls)
          cs
    | Ptype_record ls ->
        List.iter (fun (l : label_declaration) -> add_ct l.pld_type) ls
    | _ -> ()
  end

(* members = the closure's binding names, in artifact order *)
let type_vocab members =
  List.iter
    (fun n ->
      if Hashtbl.mem vals n then
        List.iter
          (fun c -> if Hashtbl.mem tydecls c then add_vocab_type c else bump builtins c)
          (tycon_names (Hashtbl.find vals n)))
    members

(* ─────────────────────── 7. the roots, as a CLI parameter ───────────────── *)

(* The roots are a parameter, not a convention: the subset verdict — and with it
   JPL.6's Rule-6 (no recursion) verdict — binds the code we SHIP, so a caller must
   be able to name the shipped roots and watch the oracle cluster fall out.  That is
   §9.2's decision 1, made mechanically instead of asserted.  Both consumers take the
   same argument, so the parser and the default live here rather than being written
   twice. *)
let split_commas str =
  let out = ref [] and cur = Buffer.create 16 in
  String.iter
    (fun c ->
      begin
        if c = ',' then begin
          (* an empty buffer means an empty field; skip it rather than emit "" *)
          if Buffer.length cur > 0 then begin
            out := Buffer.contents cur :: !out;
            Buffer.clear cur
          end
        end
        else Buffer.add_char cur c
      end)
    str;
  if Buffer.length cur > 0 then out := Buffer.contents cur :: !out;
  List.rev !out

let default_roots = [ "mrun_c"; "step_c" ]

(* The closure's members, in artifact order. *)
let closure_members () =
  List.filter (fun n -> Hashtbl.mem closure n) (List.rev !bind_order)

