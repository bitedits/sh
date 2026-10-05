(* jpl_ast.ml — the SHARED READER for the JPL.5 tool family (front end, layout
 * emitter, lowering census).

 * Extracted from jpl_front.ml at 5-B.2 so the emitter consumes exactly the same
 * reading the subset gate is built on, instead of re-implementing a second
 * resolution of the artifact's AST.  One reader, three consumers (the front end
 * jpl_front.ml, the layout emitter jpl_emit.ml, the lowering census
 * jpl_lower.ml): that is the single-source rule applied on the tooling side
 * (JPL.md §Design) — two independent AST walks over the same bytes is how a
 * transpiler starts disagreeing with its own gate.

 * Contents: the implementation environment (bindings, arity, recursion, mutual
 * groups), the interface environment (value signatures, type declarations and
 * their constructors), the emitter's DECLARED subset, the per-binding
 * measurement (expression/pattern class census, allocation census, edges, and
 * the self-call count that distinguishes a loop from a nat-destruct), the
 * root-parameterised transitive closure, the TYPE VOCABULARY the closure reaches
 * (§6 — the domain of the C layout table, shared so the reporter and the emitter
 * cannot compute two domains), the roots as a CLI parameter (§7), and — moved in
 * from jpl_emit.ml at 5-B.3 so the lowering census reasons over one type view —
 * the value-type model `lt` with its reader `of_ct` and short names (§8), the
 * constant folder that turns the artifact's capacity DATA into decimals (§9),
 * and the cap table itself (§10).

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

(* `(fun fO fS n -> if n = 0 then fO () else fS (n - 1)) base step fuel`
   Returns the idiom's three binder names when the node IS the idiom, so a consumer
   can ask which name carries the decremented fuel instead of re-matching the shape:
   the 5-B.3 census has to prove that every recursive call of a fuel loop passes the
   `fS` binder (the value one less) rather than some other argument that happens to
   be named similarly.  One shape match, in the reader, for all three consumers. *)
let fuel_idiom (ps : function_param list) (body : function_body) =
  match ps, body with
  | [ a; b; c ],
    Pfunction_body { pexp_desc = Pexp_ifthenelse (test, base, Some step); _ } ->
      (match pv_name a, pv_name b, pv_name c with
       | Some fO, Some fS, Some n when fO <> fS && fS <> n && fO <> n ->
           (* test: n = 0 *)
           let ok_test =
             match test.pexp_desc with
             | Pexp_apply (f, [ (Nolabel, x); (Nolabel, y) ]) when is_ident0 "=" f ->
                 is_var x = Some n && is_nat_lit 0 y
             | _ -> false
           in
           (* base: fO () *)
           let ok_base =
             match base.pexp_desc with
             | Pexp_apply (f, [ (Nolabel, arg) ]) when is_ident0 fO f ->
                 (match arg.pexp_desc with
                  | Pexp_construct ({ txt = Lident "()"; _ }, None) -> true
                  | _ -> false)
             | _ -> false
           in
           (* step: fS (n - 1) *)
           let ok_step =
             match step.pexp_desc with
             | Pexp_apply (f, [ (Nolabel, inner) ]) when is_ident0 fS f ->
                 (match inner.pexp_desc with
                  | Pexp_apply (g, [ (Nolabel, p); (Nolabel, q) ])
                    when is_ident0 "-" g ->
                     is_var p = Some n && is_nat_lit 1 q
                  | _ -> false)
             | _ -> false
           in
           if ok_test && ok_base && ok_step then Some (fO, fS, n) else None
       | _ -> None)
  | _ -> None

let is_fuel_idiom ps body = match fuel_idiom ps body with Some _ -> true | None -> false

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
   §9.2's decision 1, made mechanically instead of asserted.  All three consumers take the
   same parameter, so the parser and the default live here rather than being written three
   times. *)
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

(* ─────────────── 8. the shared VALUE-TYPE view (moved out of jpl_emit.ml) ── *)

(* Just enough structure to decide a representation or to type a subexpression.
   Moved here at 5-B.3 because the lowering census has to reason about the SAME
   type view the layout table was built from: if the emitter's `of_ct` and the
   lowering's inference were two readings of one `.mli`, the two could disagree
   about which value is a word and which is a cell, and a transpiler that
   disagrees with its own type layer is wrong in a way no compiler can report.

   L_word is the artifact's `text`: its `.mli` says `type text = int list`, and
   the model's bounded counterpart is sh_jpl.v §4's `bword = BW { bw_bytes : text;
   bw_len : nat }` with `bw_len <= MAX_WORD` — a length-carrying bounded array.
   So a word is an ARRAY WITH ITS COUNT, not a cons list: that is a reading of
   the model, not a convenience.  L_bres is the model's saturate-to-error result
   (sh_jpl.v §2). *)
type lt =
  | L_nat
  | L_bool
  | L_unit
  | L_word
  | L_list of lt
  | L_opt of lt
  | L_pair of lt * lt
  | L_bres of lt
  | L_named of string
  | L_fun of lt * lt
  | L_var of string
  (* The one constructor no layout can be built from, added at 5-B.3 for the
     lowering census: a bottom-up inference over the artifact's bodies meets
     values it cannot type (a free identifier the `.mli` does not describe, a
     construct outside the vocabulary).  The census must REPORT those sites, so
     they need a value in the shared type view rather than an exception that
     would abort the whole reading — and `tn` refuses one, so an unknown can
     never be mistaken for a laid-out type.  The emitter's own signatures never
     produce it: they come from `of_ct` over the `.mli`. *)
  | L_unk of string

let w4 = 4

let rec of_ct (t : core_type) : lt =
  match t.ptyp_desc with
  | Ptyp_any -> fail "of_ct: '_' in an emitted signature"
  | Ptyp_var v -> L_var v
  | Ptyp_alias (a, _) -> of_ct a
  | Ptyp_arrow (_, a, b) -> L_fun (of_ct a, of_ct b)
  | Ptyp_poly (_, a) -> of_ct a
  | Ptyp_open (_, a) -> of_ct a
  | Ptyp_tuple l ->
      (* the artifact only builds binary pairs; an n-ary tuple would need a layout
         decision, so it is refused rather than silently right-nested *)
      (match List.map (fun (_, x) -> of_ct x) l with
       | [ a; b ] -> L_pair (a, b)
       | _ -> fail "of_ct: tuple is not binary")
  | Ptyp_constr ({ txt }, args) ->
      let nm = li txt in
      (match (nm, args) with
       | "int", [] -> L_nat
       | "bool", [] -> L_bool
       | "unit", [] -> L_unit
       | "text", [] -> L_word
       | "list", [ a ] -> L_list (of_ct a)
       | "option", [ a ] -> L_opt (of_ct a)
       | "bres", [ a ] -> L_bres (of_ct a)
       | "list", [] | "option", [] | "bres", [] ->
           fail ("of_ct: " ^ nm ^ " without its type argument")
       | _, _ when Hashtbl.mem tydecls nm -> L_named nm
       | _ -> fail ("of_ct: type outside the artifact's vocabulary: " ^ nm))
  | Ptyp_variant _ -> fail "of_ct: polymorphic variant"
  | Ptyp_object _ -> fail "of_ct: object type"
  | Ptyp_class _ -> fail "of_ct: class type"
  | Ptyp_package _ -> fail "of_ct: first-class module"
  | Ptyp_extension _ -> fail "of_ct: extension point"
  | Ptyp_functor _ -> fail "of_ct: functor type"

let rec has_var = function
  | L_var _ -> true
  | L_list a | L_opt a | L_bres a -> has_var a
  | L_pair (a, b) -> has_var a || has_var b
  | L_fun (a, b) -> has_var a || has_var b
  | _ -> false

(* `has_fun` is the OTHER half of what R8 has to answer.  `has_var` says an instance is
   closed — every variable resolved — and a closed instance is the condition under which
   one C function exists for it.  It is not sufficient: a resolved instance can still be
   a function-typed VALUE, and D-60411's ban on function pointers means such a parameter
   has no C type at all.  `tn` refuses one, which is right for the representation layer
   and fatal for a rung that must REPORT the case, so the refusal is exposed here as a
   predicate instead of an exception. *)
let rec has_fun = function
  | L_fun _ -> true
  | L_list a | L_opt a | L_bres a -> has_fun a
  | L_pair (a, b) -> has_fun a || has_fun b
  | _ -> false

(* The one TYPE EQUATION the artifact states outright: `type text = int list`
   (sh_run_c.mli).  R2 gives `text` the ARRAY representation, so a value the code
   builds with `::`/`[]` at element `int` is not a cons list — it is a word under
   construction, and a census that called it a list would size the wrong pool.
   `norm` applies that reading, and `int_list_is_word` DERIVES it from the
   declaration instead of assuming it: if the manifest ever stops saying
   `int list`, R2's array and the artifact's own type disagree, and normalising on
   anyway would be wrong in a way no compiler can report.  A function, not a
   module-level value, because the declarations are only in the table after
   `add_sig` has run. *)
let int_list_is_word () =
  if not (Hashtbl.mem tydecls "text") then false
  else
    match (Hashtbl.find tydecls "text").ptype_manifest with
    | Some t -> (match of_ct t with L_list L_nat -> true | _ -> false)
    | None -> false

let norm t =
  match t with
  | L_list L_nat when int_list_is_word () -> L_word
  | _ -> t

(* True of whatever occupies exactly one uint32_t WITHOUT being laid out first: a
   scalar, a word handle, a list handle, a node handle.  Used to check that a
   positional slot can hold a pooled node's payload — the check is on the TYPE, so
   it cannot pass silently for a by-value struct that happens to be 4 bytes today. *)
let single_word = function
  | L_nat | L_bool | L_unit | L_word | L_list _ | L_named _ -> true
  | L_opt _ | L_pair _ | L_bres _ | L_fun _ | L_var _ | L_unk _ -> false

(* The canonical short name of a value-space type.  Every emitted C identifier is
   built from it, so it has to be injective: nat, bool, unit, text, <e>_list,
   opt_<e>, bres_<e>, pair_<a>_<b>, and the declared names. *)
let rec tn = function
  | L_nat -> "nat"
  | L_bool -> "bool"
  | L_unit -> "unit"
  | L_word -> "text"
  | L_list e -> tn e ^ "_list"
  | L_opt e -> "opt_" ^ tn e
  | L_bres e -> "bres_" ^ tn e
  | L_pair (a, b) -> "pair_" ^ tn a ^ "_" ^ tn b
  | L_named n -> n
  | L_fun _ -> fail "tn: a function-typed value has no layout"
  | L_var v -> fail ("tn: an un-instantiated type variable reached the layout: '" ^ v)
  | L_unk w -> fail ("tn: an un-inferable type reached the layout: " ^ w)

let show_lt t = tn t

(* The C NAME of a value of this layout type, in one place.  The representation layer
   (jpl_emit.ml) registers the same rule where it lays `text` out: a text VALUE is a
   word-slab handle, so it is `jpl_wref`, while `jpl_text` names the storage the handle
   points into.  Every other type's value name is `jpl_` prefixed to its canonical
   layout name.  The census's 5-B.3b ABI renders its instance prototypes through this,
   because a second copy of the exception would be a second reading of §6.2's R2 — and
   the gate's C compile is what catches the case where the header and this name stop
   agreeing. *)
let value_name t = match t with L_word -> "jpl_wref" | _ -> "jpl_" ^ tn t

(* The C NAME of a function and of a data constant, in the same place as the name of a
   type.  Two header layers are built from these rules — the representation layer's
   prototypes and the census's ABI — and the gate compiles them together, so a symbol
   spelled differently in the two would be a link error JPL.7 pays for.  Extraction
   lower-cases the leading letter of a capitalised identifier, which is why an artifact
   name can contain a `.` or a mixed case that C cannot. *)
let c_fn n = "jpl_" ^ String.map (fun ch -> if ch = '.' then '_' else ch) n

let c_upper n =
  String.uppercase_ascii (String.map (fun ch -> if ch = '.' then '_' else ch) n)

(* 5-B.3b-ii: an arity-0 value's C name, given the macro the caps table already carries
   for it.  A capacity keeps the `JPL_MAX_*` name the header dimensioned its pools with;
   any other folded constant is `JPL_C_*`.  The caller supplies the former because it is a
   property of the artifact's cap table, and this is the rule that reads it. *)
let data_macro ?cap n = match cap with Some m -> m | None -> "JPL_C_" ^ c_upper n

(* A signature's arrow spine, read off the .mli's core_type. *)
let rec arrow_spine acc (t : core_type) =
  match t.ptyp_desc with
  | Ptyp_arrow (_, a, b) -> arrow_spine (a :: acc) b
  | _ -> (List.rev acc, t)

let sig_of n =
  let ds, r = arrow_spine [] (Hashtbl.find vals n) in
  (List.map of_ct ds, of_ct r)

(* Parameter names come from the artifact's own binding, so a prototype reads like
   the code it describes.  They are documentation; the types are the contract. *)
let param_names e =
  match e.pexp_desc with
  | Pexp_function (ps, _, _) ->
      List.filter_map
        (fun (p : function_param) ->
          match p.pparam_desc with
          | Pparam_val (_, _, { ppat_desc = Ppat_var { txt }; _ }) -> Some txt
          | _ -> None)
        ps
  | _ -> []

(* ─────────────────── 9. the constant folder (moved out of jpl_emit.ml) ───── *)

(* ExtrOcamlNatInt renders every Coq nat as `int` and every literal as a chain of
   Stdlib.Int.succ, and the model writes each capacity as a sum, product or
   difference of those.  Folding them back to decimals is the step that turns the
   artifact's capacity DATA into C array dimensions.  The recognised operations are
   exactly the ones the artifact uses, and an unrecognised one is a hard failure: a
   silently-misfolded capacity is the worst possible defect in this pipeline.
   Operators are recognised ONLY in head position — `let rec add = (+)` must not
   fold to a number.  `fold` is fatal (a capacity must be exact); `try_fold`
   reports, for the arity-0 bindings that are not capacities. *)
let folded = Hashtbl.create 24

exception Unfoldable of string

(* The artifact's own aliases and Stdlib's qualified forms: legal as the head of an
   application, never as a value. *)
let operator_names =
  [ "+"; "*"; "-"; "add"; "mul"; "sub"; "max"; "Nat.add"; "Nat.mul"; "Nat.sub" ]

let describe_const c =
  match c with
  | Pconst_integer (s, None) -> "int " ^ s
  | Pconst_integer (s, Some ch) -> "int" ^ String.make 1 ch ^ " " ^ s
  | Pconst_char _ -> "char"
  | Pconst_string _ -> "string"
  | Pconst_float _ -> "float"

let rec fold_e (e : expression) : int =
  match e.pexp_desc with
  | Pexp_constant { pconst_desc = Pconst_integer (s, None); _ } -> int_of_string s
  | Pexp_constant { pconst_desc = c; _ } ->
      raise (Unfoldable ("non-integer literal: " ^ describe_const c))
  | Pexp_ident { txt } ->
      let nm = li txt in
      if List.mem nm operator_names then raise (Unfoldable ("operator alias: " ^ nm))
      else if Hashtbl.mem folded nm then Hashtbl.find folded nm
      else if Hashtbl.mem binds nm then begin
        let v = fold_e (Hashtbl.find binds nm).b_body in
        Hashtbl.replace folded nm v;
        v
      end
      else raise (Unfoldable ("not a capacity: " ^ nm))
  | Pexp_apply (f, args) ->
      let op = match f.pexp_desc with Pexp_ident { txt } -> li txt | _ -> "?" in
      let a = List.map (fun (_, e) -> fold_e e) args in
      (match (op, a) with
       | ("Stdlib.Int.succ", [ x ]) -> x + 1
       | (("add" | "Nat.add" | "+" | "Stdlib.Int.add"), [ x; y ]) -> x + y
       | (("mul" | "Nat.mul" | "*" | "Stdlib.Int.mul"), [ x; y ]) -> x * y
       | (("Nat.sub" | "sub" | "-"), [ x; y ]) ->
           (* Nat.sub saturates at 0 — the artifact's own Nat.sub is hooked to
              Stdlib.max 0 (x - y) — so saturate rather than wrap *)
           (if x < y then 0 else x - y)
       | (("Nat.max" | "max" | "Stdlib.max"), [ x; y ]) -> max x y
       | _ ->
           raise
             (Unfoldable
                ("operation inside a capacity expression: " ^ op ^ " /"
                ^ string_of_int (List.length a))))
  | _ -> raise (Unfoldable "not built from nat arithmetic")

let fold e =
  try fold_e e with Unfoldable m -> fail ("capacity folding failed: " ^ m)

let try_fold e = try Some (fold_e e) with Unfoldable _ -> None

(* ─────────── 10. the cap table as shared data (moved out of jpl_emit.ml) ─── *)

type caps =
  { c_width : int; c_word : int; c_argv : int; c_env : int; c_list : int;
    c_cmd : int; c_stack : int; c_words : int; c_glob : int; c_fuel : int }

(* (artifact field name, C macro, model name, what sh_jpl.v §1 says it bounds) *)
let cap_fields =
  [ ("jpl_width", "JPL_MAX_WIDTH", "MAX_WIDTH", "bits in the fixed-width word");
    ("jpl_word", "JPL_MAX_WORD", "MAX_WORD", "codes per word (text length)");
    ("jpl_argv", "JPL_MAX_ARGV", "MAX_ARGV", "argument words per simple command");
    ("jpl_env", "JPL_MAX_ENV", "MAX_ENV", "simultaneously live shell variables");
    ("jpl_list", "JPL_MAX_LIST", "MAX_LIST", "any intermediate list length");
    ("jpl_cmd", "JPL_MAX_CMD", "MAX_CMD", "node pool for one lowered cmd tree");
    ("jpl_stack", "JPL_MAX_STACK", "MAX_STACK", "explicit machine stack frames");
    ("jpl_words", "JPL_MAX_WORDS", "MAX_WORDS", "word (text) cells in the slab");
    ("jpl_glob_fuel", "JPL_GLOB_FUEL", "GLOB_FUEL", "iterations of one full-width scan");
    ("jpl_fuel", "JPL_MAX_FUEL", "MAX_FUEL", "iterations the machine may run at all") ]

let caps_of c field =
  match field with
  | "jpl_width" -> c.c_width | "jpl_word" -> c.c_word | "jpl_argv" -> c.c_argv
  | "jpl_env" -> c.c_env | "jpl_list" -> c.c_list | "jpl_cmd" -> c.c_cmd
  | "jpl_stack" -> c.c_stack | "jpl_words" -> c.c_words
  | "jpl_glob_fuel" -> c.c_glob | "jpl_fuel" -> c.c_fuel
  | _ -> fail ("caps_of: no such capacity " ^ field)

let read_caps () =
  if not (Hashtbl.mem binds "jpl_caps_table") then
    fail "the artifact carries no jpl_caps_table: sh_jpl.v §1.1 is not extracted";
  match (Hashtbl.find binds "jpl_caps_table").b_body.pexp_desc with
  | Pexp_record (flds, _) ->
      let m =
        List.fold_left
          (fun a (({ txt }, v) : Longident.t loc * expression) ->
            Hashtbl.replace a (li txt) (fold v); a)
          (Hashtbl.create 16) flds
      in
      let get k =
        if Hashtbl.mem m k then Hashtbl.find m k
        else fail ("jpl_caps_table has no field " ^ k)
      in
      { c_width = get "jpl_width"; c_word = get "jpl_word";
        c_argv = get "jpl_argv"; c_env = get "jpl_env"; c_list = get "jpl_list";
        c_cmd = get "jpl_cmd"; c_stack = get "jpl_stack"; c_words = get "jpl_words";
        c_glob = get "jpl_glob_fuel"; c_fuel = get "jpl_fuel" }
  | _ -> fail "jpl_caps_table is not a record literal, so its capacities cannot be read"

(* The one place the caps are held, so the layout emitter and the lowering census
   read the same ten numbers out of the same extracted record. *)
let caps_r : caps option ref = ref None

let c () =
  match !caps_r with
  | Some x -> x
  | None -> fail "capacity used before the cap table was read"

(* The artifact's name for a model-side capacity: Extraction lower-cases the leading
   letter of a capitalised identifier, so MAX_STACK is exported as mAX_STACK and
   GLOB_FUEL as gLOB_FUEL.  Both consumers need this — the emitter to avoid naming one
   number twice, the census to say which macro a rendered body may cite — so it is the
   reader's rule and not either tool's local knowledge. *)
let cap_data model_name =
  let ch = String.get model_name 0 in
  if ch >= 'A' && ch <= 'Z' then
    String.make 1 (Char.lowercase_ascii ch)
    ^ String.sub model_name 1 (String.length model_name - 1)
  else model_name

let cap_macro_of_data nm =
  List.find_map
    (fun (_, macro, model, _) -> if cap_data model = nm then Some macro else None)
    cap_fields

(* Is this data binding already a capacity the header defines under its own name? *)
let is_cap_data nm = cap_macro_of_data nm <> None

