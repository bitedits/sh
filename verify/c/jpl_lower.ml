(* jpl_lower.ml — JPL.5-B.3a: the LOWERING CENSUS, over the shared reader.

 * Fourth consumer of jpl_ast.ml (after the front end jpl_front.ml and the layout
 * emitter jpl_emit.ml, which already share it).  It emits NO C: no function body, no
 * ABI, no statement.  What it settles first — and the reason JPL.5-B.3 is split in
 * two — is that a transpiler has to know the SHAPE of every control flow before it
 * writes any of it.  JPL.md §9.1's 5-B.1 rows recorded an ESTIMATE of the recursion
 * split; this tool MEASURES it, binding by binding, off the same vendored bytes the
 * gate already binds, and adds three measurements an estimate cannot contain:
 *
 *   1. SCHEMA.  Each closure member is classified by reading the artifact's own
 *      control flow: an operator alias (the body IS an operator, so there is no C
 *      function to emit), a FUEL loop (the head of the body is the ExtrOcamlNatInt nat
 *      idiom, which becomes `while` with the loop's condition and decrement read off
 *      the idiom), a STRUCTURAL TAIL LOOP (every self-call in tail position), a
 *      BOUNDED FOLD (a self-call in a non-tail position — which is precisely what
 *      D-60411's no-recursion rule forbids, so it is a rewrite obligation rather than
 *      a formality), or straight-line.  A binding that fits none of those is BLOCKED
 *      with the reason named; it is never quietly lowered as something else.
 *   2. DECREASE WITNESS.  A loop is only a loop if something provably shrinks.  For a
 *      fuel loop the witness is the idiom's own decremented fuel, and every recursive
 *      call is checked to pass THAT binder, not an argument that merely looks like it;
 *      for a structural loop the witness must be a variable bound by a cons-tail
 *      pattern enclosing the call.  Both are read off the Parsetree, so the termination
 *      argument stays the artifact's and does not become the emitter's invention.
 *   3. TYPE DEMAND.  JPL.md §6.2's R8 left 5 bindings PENDING because their `.mli`
 *      signatures mention type variables.  Monomorphization is the answer, and the
 *      instance set is a measurement: every closure body is typed against the declared
 *      signature it is given (expectation flows down from the `.mli`, uses flow up from
 *      the code) and each use of a polymorphic binding records the concrete instance it
 *      was used at.  A site that CONTRADICTS its declaration is a conflict, and the
 *      census refuses to report at all — a tool that prints a census it does not trust
 *      is worse than one that prints nothing.  A site it cannot type is an UNKNOWN:
 *      counted, listed, and lowered to a PENDING row.
 *
 * The same inference gives the allocation census its REPRESENTATION, which is what
 * turns "24 cons sites" into "which pool, for what element": `text` is the word slab
 * (R2's array — and the artifact's own `type text = int list` is the equation
 * jpl_ast.ml derives and `norm` applies, so a list of `int` IS a word under
 * construction), while `(text * text) list` is the environment's pair-cell pool (R3).
 * The pool names that yields are this tool's NEED list, and jpl_lower.sh compares them
 * against the header's own `extern … pool[…]` lines: two independent readings —
 * allocation sites here, the layout table there — of one artifact.  That is the general
 * shape of the 5-B.2c defect (a pooled type declared and never sized), not a patch for
 * its one known instance.
 *
 * It READS the artifact and re-encodes no kernel semantics.
 *
 * OCaml 5.5 Parsetree facts this file adds to the ones recorded in jpl_ast.ml: a
 * constructor's `Pcstr_tuple l` carries ONE element per comma-separated type, so
 * `Oeffect of a * b * c * d` is a FOUR-element argument list whose payload EXPRESSION
 * and pattern are both n-ary tuples — which is why an n-ary tuple is encoded here as a
 * right-nested `L_pair` (`mk_tuple`): an encoding used only to unify element types,
 * never to name a layout, since `tn` would refuse it and the emitter builds a flat
 * struct straight from the declaration's own argument list. *)
open Jpl_ast
open Parsetree
open Asttypes
open Longident

let src_path = ref ""

(* OCaml 5.5 spells a source position's type `Location.t`; `Parsetree.loc` is gone. *)
let line (l : Location.t) = l.loc_start.pos_lnum

let sortl h =
  List.sort
    (fun (a, x) (b, y) -> if y <> x then compare y x else String.compare a b)
    (Hashtbl.fold (fun k v a -> (k, v) :: a) h [])

let section title = Printf.printf "\n==== %s ====\n" title

let starts s p =
  String.length s >= String.length p && String.sub s 0 (String.length p) = p

(* ──────────── 2. the unifier, over the shared value-type view ──────────── *)

(* One store for the whole run, so an instance recorded at a call site can be read
   after the fact: the fresh variables of a freshened signature get bound by whatever the
   surrounding applications force on them, and resolving one at print time is reading
   that call site's instance.  `resolve` applies `norm`, so the artifact's
   `text = int list` equation is in force everywhere a type is OBSERVED — which is the
   only place it can be put, since a cons cell of `int` has to be seen as a word by the
   pool census and by the emitter alike. *)
exception Conflict of string

let store : (string, lt option) Hashtbl.t = Hashtbl.create 256
let vnum = ref 0

let newv () =
  incr vnum;
  let n = "iv" ^ string_of_int !vnum in
  Hashtbl.replace store n None;
  L_var n

let rec resolve t =
  norm
    (match t with
     | L_var v when Hashtbl.mem store v ->
         (match Hashtbl.find store v with Some t' -> resolve t' | None -> t)
     | L_list a -> L_list (resolve a)
     | L_opt a -> L_opt (resolve a)
     | L_bres a -> L_bres (resolve a)
     | L_pair (a, b) -> L_pair (resolve a, resolve b)
     | L_fun (a, b) -> L_fun (resolve a, resolve b)
     | _ -> t)

let rec occurs v = function
  | L_var w -> w = v
  | L_list a | L_opt a | L_bres a -> occurs v a
  | L_pair (a, b) -> occurs v a || occurs v b
  | L_fun (a, b) -> occurs v a || occurs v b
  | _ -> false

(* `type text = int list` and `type stack = frame list` are the artifact's OWN equations,
   read off the `.mli`: a declared name with no parameters, an abstract kind and a
   manifest IS that manifest, so the empty list at a `stack` position unifies instead of
   contradicting.  Nothing else unfolds — a variant or a record has no manifest, and a
   parameterized alias would need its arguments instantiated before it could. *)
let alias_of n =
  match Hashtbl.find_opt tydecls n with
  | Some d ->
      (match d.ptype_params, d.ptype_kind, d.ptype_manifest with
       | [], Ptype_abstract, Some ct ->
           let u = of_ct ct in
           (match u with L_named n2 when n2 = n -> None | _ -> Some u)
       | _ -> None)
  | None -> None

let rec unify a b =
  let a = resolve a in
  let b = resolve b in
  match (a, b) with
  (* an unknown demands nothing: it is a reported site, not a contradiction *)
  | L_unk _, _ | _, L_unk _ -> ()
  | L_var x, L_var y when x = y -> ()
  | L_var x, _ ->
      if occurs x b then raise (Conflict ("occurs check on " ^ x));
      Hashtbl.replace store x (Some b)
  | _, L_var x -> unify b a
  | L_nat, L_nat | L_bool, L_bool | L_unit, L_unit | L_word, L_word -> ()
  | L_list p, L_list q -> unify p q
  (* `type text = int list` is the artifact's own equation, read off its declaration by
     the shared reader rather than assumed here.  A list whose element is still unknown,
     DEMANDED at a word, has element nat — which is why the empty list at a `text`
     position is not a contradiction, and why the same arm refuses a `bool list` used as
     a word. *)
  | (L_word, L_list e | L_list e, L_word) ->
      if int_list_is_word () then unify e L_nat
      else raise (Conflict (pr_lt a ^ " vs " ^ pr_lt b))
  | L_opt p, L_opt q -> unify p q
  | L_bres p, L_bres q -> unify p q
  | L_pair (p, q), L_pair (p', q') ->
      unify p p';
      unify q q'
  | L_named x, L_named y when x = y -> ()
  | (L_named x, y | y, L_named x) ->
      (match alias_of x with
       | Some u -> unify u y
       | None -> raise (Conflict (pr_lt a ^ " vs " ^ pr_lt b)))
  | L_fun (p, q), L_fun (p', q') ->
      unify p p';
      unify q q'
  | _ -> raise (Conflict (pr_lt a ^ " vs " ^ pr_lt b))

(* The census's own printer.  `tn`/`show_lt` in the shared reader are LAYOUT names and
   refuse a function type or an unresolved variable, which is right for a typedef and
   wrong for a diagnostic. *)
and pr_lt t =
  match resolve t with
  | L_nat -> "nat"
  | L_bool -> "bool"
  | L_unit -> "unit"
  | L_word -> "text"
  | L_list a -> pr_lt a ^ " list"
  | L_opt a -> "opt(" ^ pr_lt a ^ ")"
  | L_bres a -> "bres(" ^ pr_lt a ^ ")"
  | L_pair (a, b) -> "(" ^ pr_lt a ^ " * " ^ pr_lt b ^ ")"
  | L_named n -> n
  | L_fun (a, b) -> pr_lt a ^ " -> " ^ pr_lt b
  | L_var v -> "'" ^ v
  | L_unk m -> "?(" ^ m ^ ")"

(* A freshening replaces a declared type's own parameters: every occurrence of one
   declared 'a becomes the same fresh variable and nothing else is disturbed, so the map
   is per instantiation. *)
let fmap : (string, lt) Hashtbl.t = Hashtbl.create 8

let rec freshen = function
  | L_var v ->
      (try Hashtbl.find fmap v
       with Not_found ->
         let x = newv () in
         Hashtbl.replace fmap v x;
         x)
  | L_list a -> L_list (freshen a)
  | L_opt a -> L_opt (freshen a)
  | L_bres a -> L_bres (freshen a)
  | L_pair (a, b) -> L_pair (freshen a, freshen b)
  | L_fun (a, b) -> L_fun (freshen a, freshen b)
  | t -> t

let instantiate t =
  Hashtbl.reset fmap;
  freshen t

(* a constructor's argument list AND its result, freshened together: the declared
   parameter is one variable, so `BOk of 'a` and `'a bres` must share the replacement.
   Two `instantiate` calls would reset the map between them and turn one parameter into
   two unrelated variables. *)
let instantiate_pair (args : lt list) (res : lt) =
  Hashtbl.reset fmap;
  (List.map freshen args, freshen res)

(* an n-ary constructor payload as a value type: right-nested pairs, so a four-field
   payload unifies field by field.  A binary tuple keeps exactly the shape R5 lays out,
   which is why this is not a second encoding of a layout. *)
let rec mk_tuple = function
  | [ t ] -> t
  | t :: more -> L_pair (t, mk_tuple more)
  | [] -> L_unit

(* ───────────── 3. the artifact's own constructor and label indexes ───────── *)

(* Built from the `.mli`, never written here: which constructor belongs to which
   declared type, and what its arguments are.  The builtins the `.mli` does not declare
   (`[]`, `::`, Some/None, true/false, unit) are exactly the ones `of_ct` already maps to
   vocabulary, and they are listed once, in `is_builtin_ctor`. *)
let ctor_idx : (string, lt list * lt) Hashtbl.t = Hashtbl.create 64
let label_idx : (string, lt * lt) Hashtbl.t = Hashtbl.create 64

(* The declared name APPLIED TO ITS OWN PARAMETERS, in the reader's vocabulary.  The
   artifact has exactly one parameterized type — `type 'a bres` — and a signature uses it
   applied (`bword bres`), which `of_ct` reads as `L_bres bword`.  A constructor of that
   type whose result was recorded as the bare NAME `bres` would contradict every one of
   its uses, so the parameter travels with the result and gets freshened with it. *)
let declared_result nm (params : (core_type * (variance * injectivity)) list) =
  match (nm, params) with
  | _, [] -> L_named nm
  | "bres", [ (ct, (_, _)) ] -> L_bres (of_ct ct)
  | "option", [ (ct, (_, _)) ] -> L_opt (of_ct ct)
  | "list", [ (ct, (_, _)) ] -> L_list (of_ct ct)
  | n, _ :: _ -> fail (n ^ ": a parameterized declared type the reader has no vocabulary for")

let build_indices () =
  Hashtbl.iter
    (fun nm d ->
      let res = declared_result nm d.ptype_params in
      match d.ptype_kind with
      | Ptype_variant cs ->
          List.iter
            (fun (c : constructor_declaration) ->
              let args =
                match c.pcd_args with
                | Pcstr_tuple l -> List.map of_ct l
                | Pcstr_record ls ->
                    List.map (fun (l : label_declaration) -> of_ct l.pld_type) ls
              in
              Hashtbl.replace ctor_idx c.pcd_name.txt (args, res))
            cs
      | Ptype_record ls ->
          List.iter
            (fun (l : label_declaration) ->
              Hashtbl.replace label_idx l.pld_name.txt (of_ct l.pld_type, res))
            ls
      | Ptype_abstract | Ptype_open | Ptype_external _ -> ())
    tydecls

(* Operators the artifact applies in head position, and nothing else.  These are types,
   not numbers: they describe the extracted kernel's use of Stdlib and Nat, which `vals`
   does not carry because the `.mli` does not export them.  An operator not listed here
   becomes an UNKNOWN row, never a guess. *)
let int2 = L_fun (L_nat, L_fun (L_nat, L_nat))
let bool2 = L_fun (L_bool, L_fun (L_bool, L_bool))
let nat_bool = L_fun (L_nat, L_bool)
let cmp t = L_fun (t, L_fun (t, L_bool))
let ops : (string, lt) Hashtbl.t = Hashtbl.create 32

let build_ops () =
  List.iter
    (fun (k, v) -> Hashtbl.replace ops k v)
    [ ("Stdlib.Int.succ", L_fun (L_nat, L_nat));
      ("Stdlib.Int.pred", L_fun (L_nat, L_nat));
      ("Stdlib.Int.sub", int2);
      ("Stdlib.Int.add", int2);
      ("Stdlib.Int.mul", int2);
      ("Stdlib.Int.of_int", L_fun (L_nat, L_nat));
      ("Stdlib.max", int2);
      ("Stdlib.min", int2);
      ("Stdlib.not", L_fun (L_bool, L_bool));
      ("Nat.add", int2);
      ("Nat.mul", int2);
      ("Nat.sub", int2);
      ("Nat.div", int2);
      ("Nat.modulo", int2);
      ("Nat.max", int2);
      ("Nat.min", int2);
      ("Nat.le", nat_bool);
      ("Nat.lt", nat_bool);
      ("Nat.to_int", L_fun (L_nat, L_opt L_nat));
      ("+", int2);
      ("*", int2);
      ("-", int2);
      ("/", int2);
      ("mod", int2);
      ("max", int2);
      ("min", int2);
      ("&&", bool2);
      ("||", bool2);
      ("not", L_fun (L_bool, L_bool));
      ("=", cmp (L_var "eqa"));
      ("<>", cmp (L_var "eqb"));
      ("<=", cmp (L_var "orda"));
      ("<", cmp (L_var "ordb"));
      (">=", cmp (L_var "ordc"));
      (">", cmp (L_var "ordd")) ]

let is_builtin_ctor = function
  | "[]" | "::" | "Some" | "None" | "true" | "false" | "()" -> true
  | _ -> false

(* The artifact's own capacity DATA bindings: Extraction lower-cases the leading letter
   of a capitalised identifier, so MAX_STACK is exported as mAX_STACK and GLOB_FUEL as
   gLOB_FUEL. *)
let cap_data model_name =
  let c = String.get model_name 0 in
  if c >= 'A' && c <= 'Z' then
    String.make 1 (Char.lowercase_ascii c)
    ^ String.sub model_name 1 (String.length model_name - 1)
  else model_name

let cap_macro_of_data nm =
  List.find_map
    (fun (_, macro, model, _) -> if cap_data model = nm then Some macro else None)
    cap_fields

(* ─────────────────────── 4. what the census records ─────────────────────── *)

let unknowns : (string, int) Hashtbl.t = Hashtbl.create 32
let cur_name = ref ""

(* allocation sites: (what built it, the type of the value, the binding, the line) *)
let sites : (string * lt * string * int) list ref = ref []
let site kind t ln = sites := (kind, t, !cur_name, ln) :: !sites

(* monomorphization demand: every USE of a polymorphic binding records the fresh instance
   it was used at, so the instance set is a measurement of the code *)
let demand : (string, (lt * string * int) list) Hashtbl.t = Hashtbl.create 16

let decl_full n = of_ct (Hashtbl.find vals n)

let add_demand nm t ln =
  if has_var (decl_full nm) then
    Hashtbl.replace demand nm ((t, !cur_name, ln) :: try Hashtbl.find demand nm with Not_found -> [])

(* bound checks: (binding, operator, the operand's type, the cap's data name, its macro,
   the line) *)
let guards : (string * string * string * string * string * int) list ref = ref []
let guard nm op ty capn capm ln = guards := (nm, op, ty, capn, capm, ln) :: !guards

(* every lambda the closure builds, and what happens to it: D-60411 forbids function
   pointers, so the difference between a fuel continuation, a lambda inlined at a known
   call site, and a function value that ESCAPES is the difference between a lowering and
   a blocker *)
type lambda_use =
  | LkFuel of string
  | LkPassed of string
  | LkBody
  | LkOther of string

let lambdas : (string * int * lambda_use * string) list ref = ref []
let lambda use ty ln = lambdas := (!cur_name, ln, use, ty) :: !lambdas

let lambda_use_name = function
  | LkFuel w -> "fuel continuation (" ^ w ^ ")"
  | LkPassed n -> "argument at the call site of " ^ n
  | LkBody -> "the binding's own curried value"
  | LkOther s -> s

(* ───────────────────────── 5. the inference proper ──────────────────────── *)

type env = (string, lt) Hashtbl.t

let bind env n t = Hashtbl.replace env n t

let copy (e : env) : env =
  Hashtbl.fold (fun k v a -> bind a k v; a) e (Hashtbl.create 16)

let decl_full n = of_ct (Hashtbl.find vals n)

(* an operand of a comparison, if it is one of the artifact's capacities: `n = 0` is a
   loop test and not a bound check, so only a capacity constant counts *)
let cap_ref e =
  match e.pexp_desc with
  | Pexp_ident { txt } ->
      let nm = li txt in
      if cap_macro_of_data nm <> None then Some (nm, match cap_macro_of_data nm with Some m -> m | None -> "?")
      else None
  | _ -> None

let rec spine t k =
  match (k, resolve t) with
  | 0, _ -> Some ([], t)
  | n, L_fun (a, b) ->
      (match spine b (n - 1) with
       | Some (ps, r) -> Some (a :: ps, r)
       | None -> None)
  | _ -> None

(* The whole declared type of a binding is what its body must have, so the expectation
   flows from there and `fun a b -> …` and a bare `function | …` are read by one rule; a
   body that disagrees with its `.mli` raises Conflict. *)
let rec te env (expe : lt option) (e : expression) : lt =
  match e.pexp_desc with
  | Pexp_ident { txt } ->
      let nm = li txt in
      if Hashtbl.mem env nm then resolve (Hashtbl.find env nm)
      else if is_builtin_ctor nm then te_ctor env expe nm None (line e.pexp_loc)
      else if Hashtbl.mem ops nm then begin
        let t = instantiate (Hashtbl.find ops nm) in
        (match expe with Some x -> unify t x | None -> ());
        t
      end
      else if Hashtbl.mem ctor_idx nm then te_ctor env expe nm None (line e.pexp_loc)
      else if Hashtbl.mem vals nm then begin
        let t = instantiate (decl_full nm) in
        (match expe with Some x -> unify t x | None -> ());
        add_demand nm t (line e.pexp_loc);
        t
      end
      else begin
        bump unknowns
          ("identifier with neither a signature nor a local binding: " ^ nm);
        L_unk ("ident " ^ nm)
      end
  | Pexp_constant { pconst_desc = c } ->
      (match c with
       | Pconst_integer (_, None) ->
           (match expe with Some x -> unify x L_nat | None -> ());
           site "nat literal" L_nat (line e.pexp_loc);
           L_nat
       | Pconst_integer (s, Some ch) ->
           bump unknowns
             ("suffixed integer literal (a native or 64-bit constant): " ^ s
             ^ String.make 1 ch);
           L_unk "suffixed literal"
       | _ ->
           bump unknowns
             ("constant outside the artifact's nat vocabulary: " ^ describe_const c);
           L_unk "non-nat constant")
  | Pexp_apply (f, args) ->
      if List.exists (fun (l, _) -> l <> Nolabel) args then begin
        bump unknowns "a labelled application (the artifact applies only Nolabel)";
        List.iter (fun (_, a) -> ignore (te env None a)) args;
        ignore (te env None f);
        L_unk "labelled apply"
      end
      else te_apply env expe f (List.map snd args) (line e.pexp_loc)
  | Pexp_function (ps, _, body) -> te_fun env expe ps body (line e.pexp_loc)
  | Pexp_match (scrut, cs) ->
      let ts = te env None scrut in
      let res = match expe with Some x -> x | None -> newv () in
      List.iter
        (fun (c : case) ->
          let env' = copy env in
          tp env' ts c.pc_lhs;
          (match c.pc_guard with
           | Some g ->
               bump unknowns "an off-subset case guard";
               ignore (te env' (Some L_bool) g)
           | None -> ());
          unify res (te env' (Some res) c.pc_rhs))
        cs;
      resolve res
  | Pexp_let (rf, bs, body) ->
      if rf = Recursive then bump unknowns "a nested let-rec (off-subset for the emitter)";
      List.iter
        (fun (vb : value_binding) ->
          let t = te env None vb.pvb_expr in
          tp env t vb.pvb_pat)
        bs;
      te env expe body
  | Pexp_ifthenelse (c, br, el) ->
      unify (te env None c) L_bool;
      let res = match expe with Some x -> x | None -> newv () in
      unify res (te env (Some res) br);
      (match el with Some e2 -> unify res (te env (Some res) e2) | None -> ());
      resolve res
  | Pexp_tuple l ->
      let xs = List.map snd l in
      let exp_ts =
        match expe with
        | Some x ->
            let vs = List.map (fun _ -> newv ()) xs in
            unify x (mk_tuple vs);
            List.map (fun v -> Some v) vs
        | None -> List.map (fun _ -> None) xs
      in
      let ts = List.map2 (fun a p -> te env p a) xs exp_ts in
      let t = mk_tuple ts in
      site "tuple" t (line e.pexp_loc);
      resolve t
  | Pexp_construct ({ txt }, eo) -> te_ctor env expe (li txt) eo (line e.pexp_loc)
  | Pexp_record (flds, base) ->
      let owners =
        List.map
          (fun ({ txt }, _) ->
            match Hashtbl.find_opt label_idx (li txt) with
            | Some (_, o) -> o
            | None ->
                raise (Conflict ("a record label the .mli does not declare: " ^ li txt)))
          flds
      in
      (match List.sort_uniq (fun p q -> String.compare (pr_lt p) (pr_lt q)) owners with
       | [ owner ] ->
           (* ONE freshening per record expression: a declared parameter is the same
              variable in the owner's type and in every field's type.  The artifact's
              records carry no parameters, so this is the identity today and the rule that
              stays right if one is ever added. *)
           Hashtbl.reset fmap;
           let t = freshen owner in
           (match expe with Some x -> unify x t | None -> ());
           List.iter
             (fun ({ txt }, v) ->
               let (lt, _) = Hashtbl.find label_idx (li txt) in
               ignore (te env (Some (freshen lt)) v))
             flds;
           (match base with Some b -> ignore (te env (Some t) b) | None -> ());
           site "record" t (line e.pexp_loc);
           t
       | _ ->
           raise
             (Conflict
                ("a record expression spanning more than one declared type: "
                ^ String.concat ", " (List.map pr_lt owners))))
  | Pexp_field (x, { txt }) ->
      let nm = li txt in
      (match Hashtbl.find_opt label_idx nm with
       | Some (lt, owner) ->
           Hashtbl.reset fmap;
           ignore (te env (Some (freshen owner)) x);
           freshen lt
       | None ->
           bump unknowns ("field of an undeclared label: " ^ nm);
           ignore (te env None x);
           L_unk ("field " ^ nm))
  | Pexp_constraint (x, ct) ->
      let t = of_ct ct in
      (match expe with Some x2 -> unify x2 t | None -> ());
      te env (Some t) x
  | Pexp_sequence (a, b) ->
      ignore (te env None a);
      te env expe b
  | Pexp_variant (l, eo) ->
      bump unknowns ("polymorphic variant `" ^ l);
      (match eo with Some x -> ignore (te env None x) | None -> ());
      L_unk ("variant " ^ l)
  | _ ->
      bump unknowns ("expression class the emitter does not lower: " ^ eclass e);
      L_unk ("class " ^ eclass e)

(* The head of an application: its declared arrows type the arguments, so a `[]` or a
   `fun` in an argument position is typed by the function that receives it.  Too few
   arrows and the arguments decide the head's type instead, which is still where a
   disagreement with a declaration becomes a Conflict. *)
and te_apply env expe f args loc =
  let head = match f.pexp_desc with Pexp_ident { txt } -> li txt | _ -> "" in
  let is_fuel =
    match f.pexp_desc with
    | Pexp_function (ps, _, b) -> fuel_idiom ps b <> None
    | _ -> false
  in
  let tf = te env None f in
  match spine tf (List.length args) with
  | Some (ps, r) ->
      let i = ref 0 in
      List.iter2
        (fun (a : expression) (p : lt) ->
          incr i;
          let is_fun = match a.pexp_desc with Pexp_function _ -> true | _ -> false in
          ignore (te env (Some p) a);
          if is_fun then
            lambda
              (if is_fuel && (!i = 1 || !i = 2) then
                 LkFuel (if !i = 1 then "base" else "step")
               else LkPassed (if head = "" then "(an applied value)" else head))
              (pr_lt p) (line a.pexp_loc))
        args ps;
      (match expe with Some x -> unify r x | None -> ());
      record_guard head ps args loc;
      resolve r
  | None ->
      let rec go t rest =
        match rest with
        | [] -> t
        | a :: more ->
            let ta = te env None a in
            let rr = newv () in
            unify t (L_fun (ta, rr));
            go rr more
      in
      let r = go tf args in
      (match expe with Some x -> unify r x | None -> ());
      resolve r

(* A comparison whose operand is a capacity constant is a BOUND CHECK: the code's own
   enforcement of a cap.  Listing them is what stops "the caps bound the machine" from
   being read out of a table of sizes that no comparison consults. *)
and record_guard head ps args loc =
  if head <> "" && List.mem head [ "="; "<="; "<"; ">="; ">"; "<>" ] then
    match (cap_ref (List.nth args 0), cap_ref (List.nth args 1)) with
    | Some (capn, capm), _ ->
        guard !cur_name head
          (if List.length ps > 1 then pr_lt (List.nth ps 1) else "(untyped)")
          capn capm loc
    | None, Some (capn, capm) ->
        guard !cur_name head
          (if List.length ps > 0 then pr_lt (List.nth ps 0) else "(untyped)")
          capn capm loc
    | None, None -> ()

(* the value a constructor builds, and the type it gives its payload *)
and te_ctor env expe nm eo loc =
  let a = newv () in
  let t, argt =
    match nm with
    | "[]" -> (L_list a, None)
    | "::" -> (L_list a, Some (L_pair (a, L_list a)))
    | "Some" -> (L_opt a, Some a)
    | "None" -> (L_opt a, None)
    | "true" | "false" -> (L_bool, None)
    | "()" -> (L_unit, None)
    | _ ->
        let args, declared_res =
          match Hashtbl.find_opt ctor_idx nm with
          | Some x -> x
          | None -> raise (Conflict ("constructor neither declared nor builtin: " ^ nm))
        in
        let (args, res) = instantiate_pair args declared_res in
        (* A constructor APPLIED to a payload is an application, so the expression's type
           is the RESULT; the curried form is a bare constructor reference, and the
           artifact has both (`Onext {…}` in an arm and `Some` inside `(Some c)`).  The
           builtin arms above already return the result type, so this is the same rule. *)
        ( (match eo with
           | Some _ -> res
           | None ->
               if args = [] then res
               else List.fold_right (fun p r -> L_fun (p, r)) args res),
          if args = [] then None else Some (mk_tuple args) )
  in
  (match expe with Some x -> unify x t | None -> ());
  (match (eo, argt) with
   | None, _ -> ()
   | Some x, Some p -> ignore (te env (Some p) x)
   | Some x, None ->
       bump unknowns ("a constructor carrying a payload the index does not name: " ^ nm);
       ignore (te env None x));
  site nm t loc;
  resolve t

(* a pattern consumes the type of what it matches, so a case's binders carry the
   artifact's own types into its right-hand side *)
and tp env t (p : pattern) =
  match p.ppat_desc with
  | Ppat_var { txt } -> bind env txt t
  | Ppat_any -> ()
  | Ppat_alias (q, { txt }) ->
      tp env t q;
      bind env txt t
  | Ppat_constant { pconst_desc = c } ->
      (match c with
       | Pconst_integer _ | Pconst_char _ -> unify t L_nat
       | _ -> bump unknowns "a pattern constant that is not a nat")
  | Ppat_tuple (l, _) ->
      let ps = List.map (fun (_, x) -> x) l in
      let vs = List.map (fun _ -> newv ()) ps in
      unify t (mk_tuple vs);
      List.iter2 (fun q v -> tp env v q) ps vs
  | Ppat_construct ({ txt }, po) ->
      let nm = li txt in
      if nm = "::" then begin
        let el = newv () in
        unify t (L_list el);
        (match po with
         | Some (_, q) -> tp env (L_pair (el, L_list el)) q
         | None -> ())
      end
      else if nm = "[]" then unify t (L_list (newv ()))
      else if nm = "Some" then begin
        let el = newv () in
        unify t (L_opt el);
        (match po with Some (_, q) -> tp env el q | None -> ())
      end
      else if nm = "None" then unify t (L_opt (newv ()))
      else if nm = "true" || nm = "false" then unify t L_bool
      else if nm = "()" then unify t L_unit
      else
        (match Hashtbl.find_opt ctor_idx nm with
         | Some (args, declared_res) ->
             let (args, res) = instantiate_pair args declared_res in
             (* as in `te_ctor`: a pattern built with a constructor has the RESULT type,
                since the payload is matched inside it, never curried outside *)
             unify t res;
             (match (po, args) with
              | Some (_, q), [] ->
                  bump unknowns ("a nullary constructor pattern carrying a payload: " ^ nm)
              | None, _ :: _ ->
                  bump unknowns ("a constructor pattern with no payload: " ^ nm)
              | Some (_, q), _ -> tp env (mk_tuple args) q
              | None, [] -> ())
         | None ->
             bump unknowns ("pattern of an undeclared constructor: " ^ nm);
             (match po with Some (_, q) -> tp env (newv ()) q | None -> ()))
  | Ppat_or (a, b) ->
      tp env t a;
      tp env t b
  | Ppat_constraint (q, ct) ->
      let t' = of_ct ct in
      unify t t';
      tp env t' q
  | Ppat_variant (l, qo) ->
      bump unknowns ("polymorphic variant pattern `" ^ l);
      (match qo with Some q -> tp env (newv ()) q | None -> ())
  | _ -> bump unknowns ("pattern class the census does not type: " ^ pclass p)

and te_fun env expe ps body loc =
  (* The parameters come from the expectation when it reaches far enough and are fresh
     variables otherwise.  A bare `function | …` has NO parameter list and a hidden
     scrutinee, which counts as one more domain — that is why `length` shows arity 0 in
     the closure table and still types as `'a list -> int` here. *)
  let extra = match body with Pfunction_cases _ -> 1 | _ -> 0 in
  let np = List.length ps + extra in
  let (expect_ps, expect_r) =
    match (expe, Option.bind expe (fun x -> spine x np)) with
    | _, Some (a, b) -> (a, b)
    | _ ->
        (* no expectation, or not an arrow of this length: nothing is known about the
           parameter types here, and the unification with the expectation at the end of
           this function is what turns a disagreement into a Conflict *)
        (List.init np (fun _ -> newv ()), newv ())
  in
  let env' = copy env in
  let ptys =
    List.mapi
      (fun i (p : function_param) ->
        match p.pparam_desc with
        | Pparam_val (lbl, def, pat) ->
            (match lbl with
             | Nolabel -> ()
             | _ -> bump unknowns "a labelled or optional parameter");
            let t = List.nth expect_ps i in
            (* `Pparam_val`'s middle field is an OPTIONAL ARGUMENT'S DEFAULT, not a type
               constraint: extraction never emits one, so its presence is recorded rather
               than trusted. *)
            (match def with Some d -> unify t (te env' (Some t) d) | None -> ());
            tp env' t pat;
            t
        | Pparam_newtype _ ->
            bump unknowns "a generative parameter (newtype)";
            newv ())
      ps
  in
  let scrut = if extra = 1 then [ List.nth expect_ps (List.length ps) ] else [] in
  let res =
    match body with
    | Pfunction_body b ->
        lambda
          (if List.length ps = 0 then LkOther "nullary function body" else LkBody)
          "(the binding's own type)" loc;
        te env' (Some expect_r) b
    | Pfunction_cases (cs, _, _) ->
        lambda (LkOther "bare function: hidden scrutinee")
          (pr_lt (mk_tuple (ptys @ scrut))) loc;
        let ts = List.nth expect_ps (List.length ps) in
        List.iter
          (fun (c : case) ->
            let e2 = copy env' in
            tp e2 ts c.pc_lhs;
            unify expect_r (te e2 (Some expect_r) c.pc_rhs))
          cs;
        expect_r
  in
  let built = List.fold_right (fun p q -> L_fun (p, q)) (ptys @ scrut) res in
  (match expe with Some x -> unify x built | None -> ());
  resolve built

(* ───────────────── 6. control flow: tail position and the witness ───────── *)

(* One traversal, hand-written over the emitter's OWN declared subset: the front end has
   already refused anything outside it, so the cases below cover the shipped closure
   exactly.  A class that is not one of them lands in `unhandled` and makes the census
   refuse, and the self-call counts are cross-checked against the shared reader's own
   measurement — which turns "the traversal covered everything" from an assertion into a
   check. *)
type csite =
  { c_self : bool;
    c_tail : bool;
    c_head : string;
    c_args : expression list;
    c_line : int;
    c_dec : string list }

let unhandled : (string, int) Hashtbl.t = Hashtbl.create 8

(* the variables the artifact itself proves smaller than the scrutinee: the tail bound by
   a `p :: rest` pattern, recursively through tuple and or-patterns *)
let rec cons_vars p acc =
  match p.ppat_desc with
  | Ppat_construct
      ( { txt = Lident "::" },
        Some (_, { ppat_desc = Ppat_tuple (l, _); _ }) ) ->
      (match List.map (fun (_, x) -> x) l with
       | [ _; tl ] ->
           (match tl.ppat_desc with
            | Ppat_var { txt } -> txt :: acc
            | _ -> cons_vars tl acc)
       | _ -> acc)
  | Ppat_construct (_, Some (_, q)) -> cons_vars q acc
  | Ppat_tuple (l, _) -> List.fold_left (fun a (_, q) -> cons_vars q a) acc l
  | Ppat_or (a, b) -> cons_vars b (cons_vars a acc)
  | Ppat_constraint (q, _) | Ppat_alias (q, _) -> cons_vars q acc
  | _ -> acc

let rec walks (s : csite -> unit) (dec : string list) (tail : bool) (e : expression) =
  match e.pexp_desc with
  | Pexp_apply (f, args) ->
      let argl = List.map snd args in
      let head = match f.pexp_desc with Pexp_ident { txt } -> li txt | _ -> "" in
      if head <> "" then
        s { c_self = head = !cur_name; c_tail = tail; c_head = head; c_args = argl;
            c_line = line e.pexp_loc; c_dec = dec }
      else walks s dec false f;
      (* inside the fuel idiom's step, the decremented fuel binder is a decreasing value,
         so a loop that passes it is proven by the idiom itself *)
      let extra =
        match f.pexp_desc with
        | Pexp_function (ps, _, body) ->
            (match (fuel_idiom ps body, argl) with
             | Some (_, fS, _), [ _; _; _ ] -> [ fS ]
             | _ -> [])
        | _ -> []
      in
      List.iter (fun a -> walks s (dec @ extra) false a) argl
  | Pexp_function (ps, _, body) ->
      let dec' =
        List.fold_left
          (fun a (p : function_param) ->
            match p.pparam_desc with
            | Pparam_val (_, _, pat) -> cons_vars pat [] @ a
            | _ -> a)
          dec ps
      in
      (* a lambda body is its own return, so tail restarts as true inside it *)
      (match body with
       | Pfunction_body b -> walks s dec' true b
       | Pfunction_cases (cs, _, _) ->
           List.iter
             (fun (c : case) -> walks s (cons_vars c.pc_lhs dec') true c.pc_rhs)
             cs)
  | Pexp_match (scrut, cs) ->
      walks s dec false scrut;
      List.iter
        (fun (c : case) ->
          let dec' = cons_vars c.pc_lhs dec in
          (match c.pc_guard with Some g -> walks s dec' false g | None -> ());
          walks s dec' tail c.pc_rhs)
        cs
  | Pexp_ifthenelse (c, br, el) ->
      walks s dec false c;
      walks s dec tail br;
      (match el with Some e2 -> walks s dec tail e2 | None -> ())
  | Pexp_let (_, bs, body) ->
      List.iter (fun (vb : value_binding) -> walks s dec false vb.pvb_expr) bs;
      let dec' =
        List.fold_left (fun a (vb : value_binding) -> cons_vars vb.pvb_pat a) dec bs
      in
      walks s dec' tail body
  | Pexp_sequence (a, b) ->
      walks s dec false a;
      walks s dec tail b
  | Pexp_construct (_, Some x) -> walks s dec false x
  (* a nullary constructor carries nothing, so there is no subexpression to walk:
     `Olimit`, `()`, `[]`, `BLimit` and the `cmd` leaves all appear here *)
  | Pexp_construct (_, None) -> ()
  | Pexp_variant (_, Some x) -> walks s dec false x
  | Pexp_tuple l -> List.iter (fun (_, x) -> walks s dec false x) l
  | Pexp_record (flds, base) ->
      List.iter (fun (_, x) -> walks s dec false x) flds;
      (match base with Some x -> walks s dec false x | None -> ())
  | Pexp_field (x, _) -> walks s dec false x
  | Pexp_constraint (x, _) -> walks s dec tail x
  | Pexp_ident _ | Pexp_constant _ -> ()
  | _ -> bump unhandled (eclass e)

(* ───────────────────────── 7. the schema of one binding ─────────────────── *)

type schema =
  { s_name : string;
    s_class : string;
    s_shape : string;
    s_witness : string;
    s_fuel : string;
    s_self : int;
    s_walk : int;
    s_tail : int;
    s_nontail : int;
    s_note : string }

let fuel_at_head e =
  match e.pexp_desc with
  | Pexp_apply (f, args) ->
      (match f.pexp_desc with
       | Pexp_function (ps, _, body) ->
           (match (fuel_idiom ps body, args) with
            | Some names, [ (Nolabel, base); (Nolabel, step); (Nolabel, fuel) ] ->
                Some (names, base, step, fuel)
            | _ -> None)
       | _ -> None)
  | _ -> None

(* where the loop's initial fuel comes from: a capacity the artifact exports, a folded
   constant, a literal, or a parameter — and a parameter means the CALLER supplies it,
   which the row below then shows the caller having to have established *)
let fuel_source (e : expression) : string =
  match e.pexp_desc with
  | Pexp_ident { txt } ->
      let nm = li txt in
      (match cap_macro_of_data nm with
       | Some m -> nm ^ " (" ^ m ^ ")"
       | None ->
           if Hashtbl.mem binds nm then
             match try_fold (Hashtbl.find binds nm).b_body with
             | Some v -> nm ^ " = " ^ string_of_int v
             | None -> "parameter " ^ nm ^ ", supplied by the caller"
           else "parameter " ^ nm)
  | Pexp_constant { pconst_desc = Pconst_integer (s, None); _ } -> s
  | _ ->
      (match try_fold e with
       | Some v -> string_of_int v
       | None -> "(a " ^ eclass e ^ ", not a capacity constant)")

let classify nm body (m : measure) =
  cur_name := nm;
  let self = !(m.self) in
  let acc = ref [] in
  walks (fun c -> if c.c_self then acc := c :: !acc) [] true body;
  let mine = List.rev !acc in
  let nt = List.filter (fun c -> not c.c_tail) mine in
  let tl = List.filter (fun c -> c.c_tail) mine in
  let witness_of c =
    match
      List.find_opt
        (fun a ->
          match a.pexp_desc with
          | Pexp_ident { txt } -> List.mem (li txt) c.c_dec
          | _ -> false)
        c.c_args
    with
    | Some a -> (match a.pexp_desc with Pexp_ident { txt } -> li txt | _ -> "?")
    | None -> ""
  in
  match fuel_at_head body with
  | Some ((fO, fS, n), base, step, fuel) ->
      let step_calls =
        let r = ref [] in
        walks (fun c -> if c.c_self then r := c :: !r) [ fS ] true step;
        List.rev !r
      in
      let base_self =
        let r = ref 0 in
        walks (fun c -> if c.c_self then incr r) [] false base;
        !r
      in
      let unproven =
        List.map string_of_int
          (List.filter_map
             (fun c -> if witness_of c = "" then Some c.c_line else None)
             step_calls)
      in
      let cls =
        if unproven <> [] then "FUEL LOOP, DECREASE UNPROVEN"
        else if base_self > 0 then "FUEL LOOP, RECURSION IN ITS OWN BASE"
        else if List.length step_calls <> self then "FUEL LOOP, CALL COUNT MISMATCH"
        else "fuel tail loop"
      in
      { s_name = nm;
        s_class = cls;
        s_shape = "while (fuel > 0) { fuel -= 1; body }";
        s_witness = fS ^ " = " ^ n ^ " - 1, the idiom's own decrement";
        s_fuel = fuel_source fuel;
        s_self = self;
        s_walk = List.length mine;
        s_tail = List.length step_calls;
        s_nontail = base_self;
        s_note =
          "continuations " ^ fO ^ "/" ^ fS
          ^ (if unproven = [] then ""
             else "; calls not passing the decremented fuel at lines "
                  ^ String.concat "," unproven)
          ^ (if List.length step_calls = self then ""
             else "; the shared reader counted " ^ string_of_int self ^ " references") }
  | None ->
      if self = 0 then
        (match body.pexp_desc with
         | Pexp_ident { txt } when List.mem (li txt) operator_names ->
             { s_name = nm; s_class = "operator alias";
               s_shape = "the C operator itself; no function is emitted";
               s_witness = "-"; s_fuel = "-"; s_self = 0; s_walk = List.length mine;
               s_tail = 0; s_nontail = 0; s_note = "the body is " ^ li txt }
         | Pexp_ident { txt } ->
             { s_name = nm; s_class = "value alias"; s_shape = "a call, or a rename";
               s_witness = "-"; s_fuel = "-"; s_self = 0; s_walk = List.length mine;
               s_tail = 0; s_nontail = 0;
               s_note = "the body is the identifier " ^ li txt }
         | _ ->
             { s_name = nm; s_class = "straight-line"; s_shape = "a C function body";
               s_witness = "-"; s_fuel = "-"; s_self = 0; s_walk = List.length mine;
               s_tail = 0; s_nontail = 0;
               s_note =
                 if mine <> [] then
                   "calls "
                   ^ String.concat ","
                       (List.sort_uniq String.compare (List.map (fun c -> c.c_head) mine))
                 else "" })
      else if nt <> [] then
        { s_name = nm; s_class = "BOUNDED FOLD (non-tail)";
          s_shape =
            "rewrite required: D-60411 forbids recursion, and a non-tail call cannot \
             become a while";
          s_witness =
            (match List.map witness_of nt with
             | w :: _ when w <> "" -> w ^ " (a cons tail, but not a tail call)"
             | _ -> "NONE FOUND");
          s_fuel = "-"; s_self = self; s_walk = List.length mine;
          s_tail = List.length tl; s_nontail = List.length nt;
          s_note =
            "non-tail self-calls at lines "
            ^ String.concat "," (List.map (fun c -> string_of_int c.c_line) nt) }
      else
        let ws = List.map witness_of tl in
        let missing =
          List.map string_of_int
            (List.filter_map (fun c -> if witness_of c = "" then Some c.c_line else None) tl)
        in
        if missing <> [] then
          { s_name = nm; s_class = "BLOCKED: recursion with no witness";
            s_shape = "refused: no C form until the artifact shows what decreases";
            s_witness = "-"; s_fuel = "-"; s_self = self; s_walk = List.length mine;
            s_tail = List.length tl; s_nontail = 0;
            s_note = "tail calls with no decreasing argument at lines "
                     ^ String.concat "," missing }
        else
          { s_name = nm; s_class = "structural tail loop";
            s_shape =
              "while (handle != JPL_NIL) { cell = pool[handle]; body; handle = cell.next }";
            s_witness = String.concat "," (List.sort_uniq String.compare ws);
            s_fuel = "-"; s_self = self; s_walk = List.length mine;
            s_tail = List.length tl; s_nontail = 0;
            s_note = "decreases on a cons tail bound by the enclosing case" }

(* ─────────────── 8. representation: which pool a value lives in ─────────── *)

(* A type's pool, if it needs one, derived from the type and the artifact's own
   declarations:
     - `text` is the word slab (R2's length-carrying array, and `norm` is what makes the
       artifact's `type text = int list` the same value as a word);
     - any list is a cons-cell pool (R3), named after its element;
     - a declared type that REACHES ITSELF has no by-value layout at any setting of the
       caps (that is JPL.md §6's measurement of cmd/frame/stack), so it is a node pool;
     - anything else is by value and needs no capacity.
   This is not a copy of §6.2's hand-written decision 1: `reaches_itself` is a property of
   the declaration, and if the emitter's `pooled_types` list ever disagrees with it, the
   cross-check in jpl_lower.sh is where that shows up. *)
let comps_of nm =
  let d = Hashtbl.find tydecls nm in
  let n t = tycon_names t in
  (match d.ptype_manifest with Some t -> n t | None -> [])
  @ (match d.ptype_kind with
     | Ptype_variant cs ->
         List.concat_map
           (fun (c : constructor_declaration) ->
             match c.pcd_args with
             | Pcstr_tuple l -> List.concat_map n l
             | Pcstr_record ls ->
                 List.concat_map (fun (l : label_declaration) -> n l.pld_type) ls)
           cs
     | Ptype_record ls ->
         List.concat_map (fun (l : label_declaration) -> n l.pld_type) ls
     | _ -> [])

let rec reaches start nm seen =
  if List.mem nm seen then false
  else
    let comps = comps_of nm in
    List.mem start comps
    || List.exists
         (fun c -> Hashtbl.mem tydecls c && reaches start c (nm :: seen))
         comps

let reaches_itself nm = Hashtbl.mem tydecls nm && reaches nm nm []

(* follow a declared alias, so a signature written `stack` is seen for what the artifact
   defines it to be (`frame list`) and its values land in the right pool *)
let rec unfold t =
  match resolve t with
  | L_named n when Hashtbl.mem tydecls n ->
      let d = Hashtbl.find tydecls n in
      (match d.ptype_manifest with
       | Some ct ->
           let u = of_ct ct in
           (match u with L_named n2 when n2 = n -> u | _ -> unfold u)
       | None -> t)
  | t -> resolve t

let pool_of t =
  match unfold t with
  | L_word -> Some ("jpl_word_pool", "jpl_text")
  | L_list e ->
      if has_var e then None
      else Some ("jpl_" ^ tn e ^ "_list_pool", "jpl_" ^ tn e ^ "_list_cell")
  | L_named n ->
      if reaches_itself n then Some ("jpl_" ^ n ^ "_pool", "jpl_" ^ n ^ "_node")
      else None
  | _ -> None

(* the same reading over a signature, so a value that only ENTERS the closure through a
   root parameter still demands its pool: `step_c` takes a `cfg` whose `ck` is the machine
   stack, and the frame cells it points at must exist even if no binding inside the
   closure conses them *)
let rec sig_pools acc t =
  match t with
  | L_var _ | L_nat | L_bool | L_unit | L_unk _ -> acc
  | (L_word | L_list _ | L_named _) as x ->
      (match pool_of x with Some p -> p :: acc | None -> acc)
  | L_opt a | L_bres a -> sig_pools acc a
  | L_pair (a, b) -> sig_pools (sig_pools acc a) b
  | L_fun (a, b) -> sig_pools (sig_pools acc a) b

(* ───────────────────────────── 9. the report ───────────────────────────── *)

let rec lt_spine t acc =
  match resolve t with
  | L_fun (a, b) -> lt_spine b (a :: acc)
  | _ -> (List.rev acc, resolve t)

let print_schema schemas =
  section "LOWERING SCHEMA (one row per closure member, artifact order)";
  Printf.printf "  %-20s %-27s %5s %5s %5s %5s  %s\n" "name" "schema" "self" "walk" "tail" "nont"
    "decrease witness, and where the loop's first fuel comes from";
  List.iter
    (fun s ->
      Printf.printf "  %-20s %-27s %5d %5d %5d %5d  %s%s\n" s.s_name s.s_class s.s_self s.s_walk
        s.s_tail s.s_nontail s.s_witness
        (if s.s_fuel = "-" then "" else "  first fuel <- " ^ s.s_fuel);
      if s.s_class <> "straight-line" && s.s_class <> "operator alias" && s.s_class <> "value alias"
      then Printf.printf "  %-20s   -> %s\n" "" s.s_shape;
      if s.s_note <> "" then Printf.printf "  %-20s   note: %s\n" "" s.s_note)
    schemas;
  section "SCHEMA CENSUS";
  let sc = Hashtbl.create 12 in
  List.iter (fun s -> bump sc s.s_class) schemas;
  List.iter (fun (k, v) -> Printf.printf "  %-34s %d\n" k v) (sortl sc);
  List.filter (fun s -> starts s.s_class "BLOCKED" || starts s.s_class "FUEL LOOP,") schemas

let print_instances members =
  section "MONOMORPHIZATION: THE R8 INSTANCE SET, MEASURED AT THE CALL SITES";
  let poly = List.filter (fun n -> has_var (decl_full n)) members in
  if poly = [] then print_endline "  (no polymorphic binding in the closure)"
  else
    List.iter
      (fun n ->
        let uses = try Hashtbl.find demand n with Not_found -> [] in
        let rendered =
          List.map (fun (t, owner, ln) -> (pr_lt t, owner, ln, has_var (resolve t))) uses
        in
        let uniq = List.sort_uniq String.compare (List.map (fun (s, _, _, _) -> s) rendered) in
        Printf.printf "\n  %s : declared %s\n" n (cty (Hashtbl.find vals n));
        Printf.printf "     uses in the shipped closure %d, distinct instances %d\n"
          (List.length uses) (List.length uniq);
        List.iter
          (fun s ->
            let here = List.filter (fun (x, _, _, _) -> x = s) rendered in
            let open_ = List.exists (fun (_, _, _, o) -> o) here in
            Printf.printf "     instance  %-46s  %s\n" s
              (if open_ then "STILL OPEN: no layout, so nothing to emit"
               else "closed: one C function for this instance");
            List.iter
              (fun (_, owner, ln, _) ->
                Printf.printf "               used by %-16s at %s:%d\n" owner !src_path ln)
              here)
          uniq)
      poly

let print_pools members =
  section "ALLOCATION BY REPRESENTATION, AND THE POOL DEMAND IT MAKES";
  let repr : (string, int) Hashtbl.t = Hashtbl.create 16 in
  let owners : (string, string list) Hashtbl.t = Hashtbl.create 12 in
  let elems : (string, string) Hashtbl.t = Hashtbl.create 12 in
  let count : (string, int) Hashtbl.t = Hashtbl.create 12 in
  let unresolved = ref 0 in
  List.iter
    (fun (kind, t, owner, _ln) ->
      match pool_of t with
      | Some (arr, elem) ->
          bump repr (kind ^ "  ->  " ^ arr);
          bump count arr;
          Hashtbl.replace elems arr elem;
          let l = try Hashtbl.find owners arr with Not_found -> [] in
          if not (List.mem owner l) then Hashtbl.replace owners arr (owner :: l)
      | None ->
          if has_var (resolve t) then incr unresolved
          else bump repr ("by value (" ^ pr_lt t ^ "), no cell: " ^ kind))
    !sites;
  Printf.printf "  %-64s %s\n" "what is built, and where its value lives" "sites";
  List.iter (fun (k, v) -> Printf.printf "  %-64s %d\n" k v) (sortl repr);
  let sig_pool : (string, string) Hashtbl.t = Hashtbl.create 12 in
  List.iter
    (fun n ->
      if Hashtbl.mem vals n then
        List.iter (fun (arr, elem) -> Hashtbl.replace sig_pool arr elem)
          (sig_pools [] (decl_full n)))
    members;
  let all =
    List.sort String.compare
      (List.sort_uniq String.compare
         (Hashtbl.fold (fun k _ a -> k :: a) count []
         @ Hashtbl.fold (fun k _ a -> k :: a) sig_pool []))
  in
  Printf.printf "\n  %-44s %-32s %7s %7s  %s\n" "pool array" "element" "sites" "in a sig"
    "built by";
  List.iter
    (fun arr ->
      let elem = try Hashtbl.find elems arr with Not_found -> Hashtbl.find sig_pool arr in
      let nsites = try Hashtbl.find count arr with Not_found -> 0 in
      let in_sig = if Hashtbl.mem sig_pool arr then "yes" else "no" in
      let own =
        try String.concat ", " (List.sort String.compare (Hashtbl.find owners arr))
        with Not_found -> "-"
      in
      Printf.printf "  %-44s %-32s %7d %7s  %s\n" arr elem nsites in_sig own)
    all;
  Printf.printf "\n  pools the shipped closure demands: %d\n" (List.length all);
  Printf.printf "  allocation sites still carrying a type variable (the artifact leaves\n\
                \  them open, so no representation follows from them): %d\n" !unresolved;
  all

let print_caps members =
  section "BOUND CHECKS AGAINST THE LOCKED CAPS (the code's own enforcement)";
  let gs =
    List.sort
      (fun (a, _, _, _, _, x) (b, _, _, _, _, y) ->
        if a <> b then String.compare a b else compare x y)
      !guards
  in
  if gs = [] then print_endline "  (none)"
  else
    List.iter
      (fun (n, op, ty, capn, capm, ln) ->
        Printf.printf "  %-18s %s:%-6d %-3s  %-24s against %s (%s)\n" n !src_path ln op ty capn
          capm)
      gs;
  section "CAPACITIES: exported as data, reached by the closure, compared in a check";
  Printf.printf "  %-12s %-16s %-9s %-9s %s\n" "model name" "data binding" "exported"
    "members" "checks";
  List.iter
    (fun (_, _, model, _) ->
      let nm = cap_data model in
      let exported = if Hashtbl.mem binds nm then "yes" else "NO" in
      let n_reach =
        List.fold_left
          (fun a k -> if Hashtbl.mem (Hashtbl.find closure k).edges nm then a + 1 else a)
          0 members
      in
      let checks =
        List.fold_left
          (fun a (_, _, _, capn, _, _) -> if capn = nm then a + 1 else a)
          0 !guards
      in
      Printf.printf "  %-12s %-16s %-9s %-9d %d\n" model nm exported n_reach checks)
    cap_fields

let print_lambdas () =
  section "FIRST-CLASS FUNCTIONS (what is a value, and what may stay one)";
  List.iter
    (fun (n, ln, use, ty) ->
      Printf.printf "  %-18s %s:%-6d %-36s %s\n" n !src_path ln (lambda_use_name use) ty)
    (List.sort (fun (a, x, _, _) (b, y, _, _) -> if a <> b then String.compare a b else compare x y)
       !lambdas);
  let other =
    List.filter_map
      (fun (n, ln, use, _) -> match use with LkOther d -> Some (n, ln, d) | _ -> None)
      !lambdas
  in
  Printf.printf "  A fuel continuation is consumed by the loop the idiom builds; a lambda at\n\
                \  a known call site is inlined there; a binding's own curried value becomes\n\
                \  its C function.  Anything else would have to be a function pointer, which\n\
                \  D-60411 forbids.  Sites in that remaining class: %d\n"
    (List.length other);
  List.iter
    (fun (n, ln, d) -> Printf.printf "    %-18s %s:%-6d %s\n" n !src_path ln d)
    other

let print_obligations schemas pools =
  section "WHAT THIS CENSUS CANNOT ANSWER";
  Printf.printf "  1. EXTENT, not site count.  The pool rows above count allocation SITES; a\n\
                \     pool capacity needs the maximum number of cells LIVE at one step\n\
                \     boundary, which is sites x loop trips and is not computable from the\n\
                \     artifact's text.  JPL.md §6.2's headroom factor therefore stays\n\
                \     provisional until 5-B.3b emits bodies and JPL.7 measures the high-water\n\
                \     mark against the %d pools this census demands.\n"
    (List.length pools);
  let folds = List.filter (fun s -> s.s_class = "BOUNDED FOLD (non-tail)") schemas in
  Printf.printf "  2. NON-TAIL RECURSION: %d bindings recurse where a while cannot go.  Each is\n\
                \     a MODEL-side rewrite obligation, as 5-A.2, 5-A.3 and 5-A.7 were, not an\n\
                \     emitter-side invention:\n"
    (List.length folds);
  List.iter (fun s -> Printf.printf "       %-18s %s\n" s.s_name s.s_note) folds;
  let stack_checks =
    List.fold_left
      (fun a (_, _, _, capn, _, _) -> if capn = cap_data "MAX_STACK" then a + 1 else a)
      0 !guards
  in
  let stack_lengths =
    Hashtbl.fold
      (fun _ uses a ->
        a
        + List.fold_left
            (fun k (t, _, _) -> if starts (pr_lt t) "frame" || starts (pr_lt t) "stack" then k + 1 else k)
            0 uses)
      demand 0
  in
  Printf.printf "  3. STACK DEPTH.  MAX_STACK sizes the frame pool; bound checks in the shipped\n\
                \     closure that consult MAX_STACK: %d.  Instances of the polymorphic helpers\n\
                \     at a frame or stack type: %d.\n"
    stack_checks stack_lengths;
  if stack_checks = 0 && stack_lengths = 0 then
    Printf.printf "     So NOTHING in the code the emitter lowers bounds the machine's stack\n\
                  \     depth: the pool exists because sh_jpl.v §1 counted frames, and no guard\n\
                  \     reads that count.  Either 5-B.3b emits a saturating depth check or the\n\
                  \     model proves the bound the pool size already assumes — JPL.md §6's named\n\
                  \     debt, and this measurement is what keeps it named.\n"
  else
    Printf.printf "     The closure does bound it; the rows above are the evidence.\n";
  Printf.printf "  4. UNKNOWN SITES: %d classes the census could not type, so no representation\n\
                \     follows from them.\n"
    (Hashtbl.length unknowns);
  List.iter (fun (k, v) -> Printf.printf "       %-62s %d\n" k v) (sortl unknowns)

(* ───────────────────────────── 10. main ────────────────────────────────── *)

type row =
  { r_schema : schema;
    r_inferred : lt;
    r_declared : lt }

let main ml mli roots =
  src_path := ml;
  let items = Parse.implementation (Lexing.from_channel (open_in ml)) in
  add_struct "" items;
  add_sig (Parse.interface (Lexing.from_channel (open_in mli)));
  build_indices ();
  build_ops ();
  Printf.printf "INPUT      %s\n           %s\n" ml mli;
  Printf.printf "artifact   %d bindings, %d typed signatures, %d type declarations\n"
    (Hashtbl.length binds) (Hashtbl.length vals) (Hashtbl.length tydecls);
  reach roots;
  let members = closure_members () in
  let recs = List.filter (fun n -> (Hashtbl.find binds n).b_rec) members in
  Printf.printf "roots      %s  ->  %d bindings, %d recursive\n" (String.concat ", " roots)
    (List.length members) (List.length recs);

  (* REFUSAL FIRST.  A census over a closure the emitter may not read would be a
     measurement of nothing, so the front end's subset rule is re-applied here in this
     tool's own words: a mutual fixpoint has no per-binding control-flow shape at all,
     because the bindings in the group are defined in terms of each other. *)
  let mutual = List.filter (fun n -> (Hashtbl.find binds n).b_mutual) members in
  let e_all = Hashtbl.create 32 in
  Hashtbl.iter (fun _ m -> Hashtbl.iter (fun k v -> add e_all k v) m.e_cnt) closure;
  let off = List.filter (fun (k, _) -> not (List.mem k supported_expr)) (sortl e_all) in
  if mutual <> [] || off <> [] then begin
    Printf.printf "\nLOWER REFUSAL: no lowering schema exists for this root set.\n";
    if mutual <> [] then
      Printf.printf "  mutual fixpoint: these bindings are defined in terms of each other, so\n\
                    \  no per-binding shape covers them and no single-binding loop rewrite\n\
                    \  can terminate one without the others: %s\n"
        (String.concat ", " mutual);
    List.iter (fun (k, v) -> Printf.printf "  off-subset expression %-22s %d\n" k v) off;
    exit 1
  end;

  let rows =
    List.map
      (fun n ->
        let b = Hashtbl.find binds n in
        let m = Hashtbl.find closure n in
        let s = classify n b.b_body m in
        if not (Hashtbl.mem vals n) then begin
          bump unknowns "a closure member with no signature in the interface";
          { r_schema = s; r_inferred = L_unk "no signature"; r_declared = L_unk "no signature" }
        end
        else begin
          let env = Hashtbl.create 16 in
          let d = decl_full n in
          (* a contradiction names the binding it was found under: the refusal is a
             measurement of one body, and without the name it is not actionable *)
          let r =
            try te env (Some d) b.b_body with
            | Conflict m -> raise (Conflict (n ^ ": " ^ m))
          in
          { r_schema = s; r_inferred = r; r_declared = d }
        end)
      members
  in
  let schemas = List.map (fun r -> r.r_schema) rows in
  let blocked = print_schema schemas in
  print_instances members;

  section "SIGNATURE CONSISTENCY (each body unified against the interface it exports)";
  Printf.printf "  No row here re-derives a type: the `.mli`'s type is pushed DOWN into the\n\
                \  body and every use is unified against it, so what this section can find is\n\
                \  a CONTRADICTION — and a contradiction aborts this run rather than being\n\
                \  reported, because a census that disagrees with itself is not a measurement.\n\
                \  What is listed is the residue the test leaves open.\n";
  let residuals =
    List.filter_map
      (fun r ->
        let _, res = lt_spine r.r_inferred [] in
        if has_var res then Some (r.r_schema.s_name, pr_lt r.r_inferred) else None)
      rows
  in
  Printf.printf "  bodies whose result type is still open after unification: %d\n"
    (List.length residuals);
  List.iter (fun (n, t) -> Printf.printf "    %-18s %s\n" n t) residuals;
  let poly_members = List.filter (fun n -> has_var (decl_full n)) members in
  Printf.printf "  of those, bindings the interface itself declares polymorphic: %s\n"
    (String.concat ", " (List.sort String.compare poly_members));

  print_lambdas ();
  let pools = print_pools members in
  print_caps members;
  print_obligations schemas pools;

  if Hashtbl.length unhandled > 0 then begin
    Printf.printf "\nLOWER REFUSAL: the control-flow walk met expression classes outside the\n\
                  \  emitter's declared subset, so its tail analysis is incomplete:\n";
    List.iter (fun (k, v) -> Printf.printf "  %-30s %d\n" k v) (sortl unhandled);
    exit 2
  end;
  let mism = List.filter (fun s -> s.s_self <> s.s_walk) schemas in
  Printf.printf "\n==== SELF-REFERENCE AUDIT (this walk against the shared reader) ====\n";
  Printf.printf "  direct self-references agree for %d of %d members\n"
    (List.length schemas - List.length mism) (List.length schemas);
  List.iter
    (fun s ->
      Printf.printf "  MISMATCH %-18s reader %d, walk %d (%s)\n" s.s_name s.s_self s.s_walk
        s.s_class)
    mism;
  if mism <> [] || blocked <> [] then begin
    Printf.printf "\nLOWER REFUSAL: ";
    if mism <> [] then
      Printf.printf "two readings of the same bytes disagree about the self-calls.\n";
    if blocked <> [] then begin
      Printf.printf "these bindings have no lowering schema:\n";
      List.iter (fun s -> Printf.printf "  %-18s %s — %s\n" s.s_name s.s_class s.s_note) blocked
    end;
    exit 1
  end;
  Printf.printf "\nCENSUS COMPLETE: %d members, %d pools demanded, %d bound checks against the\n\
                \  caps, %d non-tail recursions to rewrite, %d unknown site classes.\n"
    (List.length members) (List.length pools) (List.length !guards)
    (List.length (List.filter (fun s -> s.s_class = "BOUNDED FOLD (non-tail)") schemas))
    (Hashtbl.length unknowns)

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [ ml; mli ] ->
      (try main ml mli default_roots with
       | Conflict m -> fail ("the artifact contradicts its own interface: " ^ m))
  | [ ml; mli; rs ] ->
      (try main ml mli (split_commas rs) with
       | Conflict m -> fail ("the artifact contradicts its own interface: " ^ m))
  | _ -> fail "usage: jpl_lower <ml> <mli> [comma-separated-roots]"
