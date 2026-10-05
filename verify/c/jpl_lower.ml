(* jpl_lower.ml — JPL.5-B.3a's LOWERING CENSUS, over the shared reader, plus 5-B.3b-i's
 * R8 ABI: the closed instance set rendered as C DECLARATIONS.
 *
 * Third consumer of jpl_ast.ml — the last of the three its header enumerates: the front end
 * jpl_front.ml, the layout emitter jpl_emit.ml, this census.  It lowers NO code: no
 * statement, no expression, no function body.  What it settles first — and the reason JPL.5-B.3 is
 * split in two — is that a transpiler has to know the SHAPE of every control flow before
 * it writes any of it.  The one piece of C it does write is the ABI of an instance set it
 * has measured, because that is where a measurement becomes checkable: the header is
 * compiled against the representation layer's own, so the C compiler — not this file —
 * decides whether a closed instance really has a type for every place.  JPL.md §9.1's 5-B.1 rows recorded an ESTIMATE of the recursion
 * split; this tool MEASURES it, binding by binding, off the same vendored bytes the
 * gate already binds, and adds four measurements an estimate cannot contain:
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
 *   4. ABI (5-B.3b-i).  A CLOSED instance is a statement about its type, not yet about
 *      its call: D-60411 forbids function pointers, so an instance with a function-typed
 *      parameter has no C prototype even though every variable in it is resolved.  This
 *      section renders the closed set — a prototype for each instance that can be named,
 *      a refusal for each one that cannot, and the binding's own schema beside it, because
 *      a prototype for a BOUNDED FOLD is a declaration whose body is still the model's to
 *      rewrite.  The counts are then asserted against the section that produced them (the
 *      `abi_*` keys against `instances_closed`), so a rendering that lost or invented an
 *      instance fails this census instead of failing a later build.
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

let rec take_while f l =
  match l with x :: more when f x -> x :: take_while f more | _ -> []

let ord n =
  if n = 1 then "1st"
  else if n = 2 then "2nd"
  else if n = 3 then "3rd"
  else string_of_int n ^ "th"

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
  (* An arrow's LEFT operand keeps the parens OCaml's own printer puts there.  Flattened,
     the one higher-order instance in the closed set reads
     `text -> bool -> text list -> bool`, i.e. a three-argument first-order function, which
     is the exact distinction its refusal makes. *)
  | L_fun (a, b) ->
      let left = match resolve a with L_fun _ -> "(" ^ pr_lt a ^ ")" | _ -> pr_lt a in
      left ^ " -> " ^ pr_lt b
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

(* The artifact's capacity DATA bindings and the macro each one already has are the shared
   reader's rule (`cap_data`, `cap_macro_of_data`, `is_cap_data`), the same one the
   representation layer applies when it decides whether to name a number twice. *)

(* ─────────────────────── 4. what the census records ─────────────────────── *)

let unknowns : (string, int) Hashtbl.t = Hashtbl.create 32
let cur_name = ref ""

(* The report's own counts, collected as each section prints.  The SUMMARY section at the
   end reads these, so the gate's numbers and the prose above describe one measurement —
   and a key that is missing is a section that stopped printing, which the gate reports
   as a failure rather than as a zero. *)
let tally : (string, int) Hashtbl.t = Hashtbl.create 24
(* `mark`, not `note`: the schema rows already use a `s_note` field, and one of the
   capacity prints binds a local `note` string. *)
let mark k v = Hashtbl.replace tally k v

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

(* capacities handed to a call: (the binding that holds the site, its line, the callee,
   the argument position, the cap's data name, and whether that argument IS the constant
   itself or only contains it).  Only the FUEL position of a loop this census found is
   recorded — see !fuel_loops — because that is where a cap becomes a bound the machine
   obeys; a cap inside a comparison is already counted as a bound check, and a cap inside
   another cap's own definition is arithmetic, not enforcement. *)
let cap_args : (string * int * string * int * string * bool) list ref = ref []
let fuel_loops : string list ref = ref []

(* every lambda the closure builds, and what happens to it: D-60411 forbids function
   pointers, so the difference between a fuel continuation, a lambda inlined at a known
   call site, and a function value that ESCAPES is the difference between a lowering and
   a blocker.

   The four resolving positions are set by the construct that HOLDS the lambda,
   immediately before it infers that lambda, and `te_fun` reads the position exactly once
   — so a lambda in a position this walk has not named is reported as unresolved instead
   of being quietly called "the binding's own value", and a lambda is never counted twice
   (which it was when the call site recorded a use and `te_fun` recorded one too). *)
type lambda_use =
  | LkFuel of string
  | LkPassed of string
  | LkRedex
  | LkDef
  | LkOpen of string

(* A recorded site keeps the TYPES and not a rendered string: an instance variable that
   is still open when the lambda is walked can be closed by a later unification, and a
   frozen name would then contradict the MONOMORPHIZATION section, which resolves at
   print time.  One census, one reading of one store. *)
let lambdas : (string * int * lambda_use * lt list * bool) list ref = ref []

let lambda use ptys one ln =
  lambdas := (!cur_name, ln, use, ptys, one) :: !lambdas

let lambda_use_name = function
  | LkFuel w -> "fuel continuation (" ^ w ^ ")"
  | LkPassed n -> "argument at the call site of " ^ n
  | LkRedex -> "applied at its own site, so lowering inlines it"
  | LkDef -> "the binding's own value, so it becomes its C function"
  | LkOpen s -> s

let pending_use : lambda_use option ref = ref None

let with_use u th =
  pending_use := Some u;
  let r = th () in
  pending_use := None;
  r

let take_use () =
  match !pending_use with
  | Some u ->
      pending_use := None;
      u
  | None -> LkOpen "a function value in a position this walk does not name"

(* the parameters a lambda takes, which is all that is known before its body is inferred *)
let dom_note ps =
  if ps = [] then "(no parameters)"
  else "takes " ^ String.concat ", " (List.map pr_lt ps)

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
      if Hashtbl.mem env nm then
        (* a local binder's type is still checked against what the site expects —
           dropping the expectation here would leave the instance open and the
           monomorphization set would measure nothing *)
        let t = resolve (Hashtbl.find env nm) in
        (match expe with Some x -> unify t x | None -> ());
        t
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
  (* the head of `(fun … ) a b c` is a lambda that never becomes a value *)
  let head_fun = match f.pexp_desc with Pexp_function _ -> true | _ -> false in
  let tf = if head_fun then with_use LkRedex (fun () -> te env None f) else te env None f in
  match spine tf (List.length args) with
  | Some (ps, r) ->
      let i = ref 0 in
      List.iter2
        (fun (a : expression) (p : lt) ->
          incr i;
          let use =
            match f.pexp_desc with
            | Pexp_function _ when is_fuel && (!i = 1 || !i = 2) ->
                LkFuel (if !i = 1 then "base" else "step")
            | _ -> LkPassed (if head = "" then "(an applied value)" else head)
          in
          (match a.pexp_desc with
           | Pexp_function _ -> ignore (with_use use (fun () -> te env (Some p) a))
           | _ -> ignore (te env (Some p) a));
          if !i = 1 && List.mem head !fuel_loops then
            List.iter
              (fun (cn, exact) ->
                cap_args := (!cur_name, line a.pexp_loc, head, !i, cn, exact) :: !cap_args)
              (caps_handed a))
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

(* Where a capacity is APPLIED rather than compared.  The artifact's loops are bounded by
   the fuel they are HANDED, not by a comparison against the cap, so an argument-position
   reference is this census's evidence that a cap reaches the machine — and its absence is
   what makes "0 checks" a finding instead of a mystery.

   Scanned to one level of application, which is how the artifact writes a computed fuel
   (`add gLOB_FUEL (length pats)`); a cap nested deeper is not counted, and the report
   says which of the two forms it found. *)
and caps_handed (e : expression) =
  let cap nm = cap_macro_of_data nm <> None in
  match e.pexp_desc with
  | Pexp_ident { txt } ->
      let nm = li txt in
      if cap nm then [ (nm, true) ] else []
  | Pexp_apply (_, args) ->
      List.filter_map
        (fun ((_, x) : (arg_label * expression)) ->
          match x.pexp_desc with
          | Pexp_ident { txt } when cap (li txt) -> Some (li txt, false)
          | _ -> None)
        args
  | _ -> []

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
  (* read the position first: an optional-parameter default is itself an expression, and
     a lambda there must not be mistaken for the lambda being positioned *)
  let use = take_use () in
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
        lambda use ptys false loc;
        te env' (Some expect_r) b
    | Pfunction_cases (cs, _, _) ->
        lambda use (ptys @ scrut) true loc;
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

let param_of e =
  match e.pexp_desc with
  | Pexp_function (ps, _, _) ->
      List.fold_left
        (fun a p -> match pv_name p with Some x -> x :: a | None -> a)
        [] ps
  | _ -> []

let rec walks (s : csite -> unit) (dec : string list) (tail : bool) (e : expression) =
  match e.pexp_desc with
  | Pexp_apply (f, args) ->
      let argl = List.map snd args in
      let head = match f.pexp_desc with Pexp_ident { txt } -> li txt | _ -> "" in
      if head <> "" then
        s { c_self = head = !cur_name; c_tail = tail; c_head = head; c_args = argl;
            c_line = line e.pexp_loc; c_dec = dec };
      (* inside the fuel idiom's STEP, the step's own binder carries the decremented
         fuel, so a loop that passes it is proven by the idiom itself.  The base and the
         fuel argument get no such witness: a self-call in the BASE is reported as the
         loop recursing in its own exit. *)
      let idiom =
        match f.pexp_desc with
        | Pexp_function (ps, _, b) -> fuel_idiom ps b
        | _ -> None
      in
      (match (idiom, argl) with
       | Some _, [ base; step; fuel_expr ] ->
           walks s dec false f;
           (* the base is the loop's EXIT: nothing decreases there *)
           walks s dec false base;
           (* the step's binder IS the decremented fuel *)
           walks s (param_of step @ dec) false step;
           (* the fuel expression is the loop's starting value, not its body *)
           walks s dec false fuel_expr
       | _ ->
           walks s dec false f;
           List.iter (fun a -> walks s dec false a) argl)
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

(* `b_body` is a binding's WHOLE expression, so for `let rec f a b c = …` it is the lambda
   over the parameters and the fuel idiom sits UNDER it.  Peeling returns the binder names
   — which is how a row can say that the loop's first fuel is this binding's own argument
   rather than some global — and the expression the idiom check needs.  A `function | …`
   body is not peeled: it has no parameter list to skip, and its hidden scrutinee is the
   first domain. *)
let rec peel_params e acc =
  match e.pexp_desc with
  | Pexp_function (ps, _, Pfunction_body b) ->
      let acc' =
        List.fold_left
          (fun a p -> match pv_name p with Some x -> x :: a | None -> a)
          acc ps
      in
      peel_params b acc'
  | _ -> (List.rev acc, e)

(* where the loop's initial fuel comes from: a capacity the artifact exports, a folded
   constant, a literal, or a parameter — and a parameter means the CALLER supplies it,
   which the row below then shows the caller having to have established *)
let fuel_source pnames e =
  match e.pexp_desc with
  | Pexp_ident { txt } ->
      let nm = li txt in
      if List.mem nm pnames then
        "parameter " ^ nm ^ " (argument "
        ^ string_of_int (1 + List.length (take_while (fun x -> x <> nm) pnames))
        ^ " of this binding), so the CALLER's fuel arrives here"
      else
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
  let pnames, head_body = peel_params body [] in
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
  match fuel_at_head head_body with
  | Some ((fO, fS, n), base, step, fuel) ->
      (* the step lambda's OWN binder is the value `n - 1`: `fS (n-1)` applies the step to
         the decremented fuel, so inside the step a call that passes that binder is proven
         by the idiom.  `fS` itself is not in scope there. *)
      let step_names = param_of step in
      let step_calls =
        let r = ref [] in
        walks (fun c -> if c.c_self then r := c :: !r) step_names true step;
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
        else if self = 0 then "fuel idiom, one trip (no self-call)"
        else "fuel tail loop"
      in
      { s_name = nm;
        s_class = cls;
        s_shape =
          (if self = 0 then
             "no loop: its step never calls the binding, so the idiom runs one trip"
           else "while (fuel > 0) { fuel -= 1; body }");
        s_witness =
          (if step_names = [] then
             "its step binder is unnamed, so the decremented fuel is discarded: one trip"
           else String.concat ", " step_names ^ " = " ^ n ^ " - 1, the idiom's own decrement");
        s_fuel = fuel_source pnames fuel;
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

(* ─────────────── 8b. the R8 ABI: what a closed instance becomes in C ─────── *)

(* The MONOMORPHIZATION section above says a closed instance is one C function.  That is
   true of its TYPE and not sufficient for its CALL: D-60411 forbids function pointers, so
   an instance whose parameter or result is a function-typed value has no C prototype even
   though every variable in it is resolved.  This section takes the closed set as the
   measurement it is and renders what follows from it — a prototype for every instance with
   a name for every place, a refusal with its reason for every one that cannot be named, and
   the schema each instance's binding carries, because a prototype whose binding is a
   non-tail fold is a declaration the emitter still cannot give a body to.

   No type is invented here: `value_name`/`tn` are the shared reader's rule, the same one the
   representation layer applied when it emitted sh_run_jpl.h, and the gate compiles this
   header after that one so the C compiler is what checks the two agree. *)

(* An arrow spine read off the inferred value type, the same shape `sig_of` produces from
   the `.mli` — here of an INSTANCE, whose type came from the call sites. *)
let rec lt_spine t acc =
  match resolve t with
  | L_fun (a, b) -> lt_spine b (a :: acc)
  | _ -> (List.rev acc, resolve t)

type abi_row =
  { a_binding : string;      (* the polymorphic binding *)
    a_index : int;           (* its n-th closed instance, in this census's order *)
    a_symbol : string;       (* the C function name *)
    a_params : lt list;
    a_result : lt;
    a_render : string;       (* the instance exactly as MONOMORPHIZATION printed it *)
    a_users : (string * int) list;
    a_schema : string;
    a_block : string }       (* "" when every place has a C name *)

let schema_class schemas n =
  match List.find_opt (fun (s : schema) -> s.s_name = n) schemas with
  | Some s -> s.s_class
  | None -> "(a binding the schema census did not classify)"

(* A body is expressible only when the binding's own schema is one §6.3 says a `while` or an
   ordinary statement can carry.  A fold is not: its prototype can be named today and its
   body is the model-side rewrite the census already owns.  An alias gets no function at all,
   so it is not expressible either — naming it here would emit a symbol the operator replaces. *)
let body_expressible_class = function
  | "straight-line" | "fuel tail loop" | "structural tail loop"
  | "fuel idiom, one trip (no self-call)" ->
      true
  | _ -> false

let rec first_fun k = function
  | [] -> None
  | p :: rest -> if has_fun p then Some (k, p) else first_fun (k + 1) rest

let blocker_of ps res =
  let places = ps @ [ res ] in
  let last = List.length places - 1 in
  match first_fun 0 places with
  | Some (i, t) ->
      "its "
      ^ (if i = last then "result" else "argument " ^ string_of_int (i + 1))
      ^ " is function-typed (" ^ pr_lt t
      ^ "), so no C type names it and D-60411 forbids the only alternative — no function \
         pointer is emitted here"
  | None ->
      if List.exists has_var places then
        "an unresolved variable reached an instance the census called closed"
      else if
        List.exists (function L_unk _ -> true | _ -> false) places
      then
        "a place the reader could not type"
      else ""

let print_abi members schemas =
  section "R8 ABI: WHAT EACH CLOSED INSTANCE BECOMES IN C, AND WHAT CANNOT BE NAMED";
  Printf.printf "  A closed TYPE is not yet a callable C function: D-60411 forbids function\n\
                \  pointers, so an instance whose parameter or result is a function-typed value\n\
                \  is refused here even though MONOMORPHIZATION closed it.  The schema is the\n\
                \  other half: a prototype for a binding whose schema is a BOUNDED FOLD is a\n\
                \  declaration whose body is still the model's to rewrite (§6.3).\n";
  let poly = List.filter (fun n -> has_var (decl_full n)) members in
  let rows =
    List.concat_map
      (fun n ->
        let uses = try Hashtbl.find demand n with Not_found -> [] in
        let rendered =
          List.map
            (fun (t, owner, ln) -> (t, pr_lt t, owner, ln, has_var (resolve t)))
            uses
        in
        let uniq = List.sort_uniq String.compare (List.map (fun (_, s, _, _, _) -> s) rendered) in
        let cls = schema_class schemas n in
        let idx = ref 0 in
        List.filter_map
          (fun s ->
            let here = List.filter (fun (_, x, _, _, _) -> x = s) rendered in
            if List.exists (fun (_, _, _, _, o) -> o) here then None
            else begin
              incr idx;
              let t =
                match here with
                | (t, _, _, _, _) :: _ -> resolve t
                | [] -> L_unk "no use rendered for this instance"
              in
              let ps, res = lt_spine t [] in
              Some
                { a_binding = n;
                  a_index = !idx;
                  a_symbol = "jpl_" ^ n ^ "_" ^ string_of_int !idx;
                  a_params = ps;
                  a_result = res;
                  a_render = s;
                  a_users =
                    List.sort_uniq compare
                      (List.map (fun (_, _, owner, ln, _) -> (owner, ln)) here);
                  a_schema = cls;
                  a_block = blocker_of ps res }
            end)
          uniq)
      poly
  in
  List.iter
    (fun r ->
      Printf.printf "\n  %s\n" r.a_symbol;
      Printf.printf "    binding   %s (instance %d of its closed set), schema %s\n"
        r.a_binding r.a_index r.a_schema;
      Printf.printf "    layout    %s\n" r.a_render;
      Printf.printf "    places    %s\n"
        (String.concat ", "
           (List.mapi
              (fun i p ->
                "arg" ^ string_of_int (i + 1) ^ " " ^ pr_lt p
                ^ (if has_fun p then " [no C name]" else ""))
              r.a_params)
        ^ (if r.a_params = [] then "" else ", ")
        ^ "result " ^ pr_lt r.a_result
        ^ (if has_fun r.a_result then " [no C name]" else ""));
      Printf.printf "    body      %s\n"
        (if r.a_block <> "" then "not reached: the prototype itself cannot be named"
         else if body_expressible_class r.a_schema then
           "expressible under §6.3 — this schema has a C form"
         else "OWED: §6.3 says this schema needs a model-side rewrite first");
      List.iter
        (fun (o, ln) -> Printf.printf "    used by   %-16s at %s:%d\n" o !src_path ln)
        r.a_users;
      if r.a_block <> "" then Printf.printf "    REFUSED   %s\n" r.a_block)
    rows;
  let blocked = List.filter (fun r -> r.a_block <> "") rows in
  let emittable = List.filter (fun r -> r.a_block = "") rows in
  let owed = List.filter (fun r -> not (body_expressible_class r.a_schema)) emittable in
  let expressible = List.filter (fun r -> body_expressible_class r.a_schema) emittable in
  (* A refusal must not be a NEW obligation: the only route to a callable `forallb` is the
     fold rewrite §6.3 already lists for it, so a blocked instance whose binding has an
     expressible schema would mean this plan is missing an owner. *)
  let outside = List.filter (fun r -> body_expressible_class r.a_schema) blocked in
  section "ABI SUMMARY";
  Printf.printf "  closed instances rendered          %d\n" (List.length rows);
  Printf.printf "  prototypes emitted                 %d\n" (List.length emittable);
  Printf.printf "  refused, no C type exists          %d\n" (List.length blocked);
  List.iter (fun r -> Printf.printf "    %-26s %s\n" r.a_symbol r.a_block) blocked;
  Printf.printf "  bodies expressible under §6.3      %d\n" (List.length expressible);
  List.iter (fun r -> Printf.printf "    %-26s %s\n" r.a_symbol r.a_schema) expressible;
  Printf.printf "  declarations whose body is owed    %d\n" (List.length owed);
  List.iter (fun r -> Printf.printf "    %-26s %s\n" r.a_symbol r.a_schema) owed;
  Printf.printf "  blocked outside the fold set       %d\n" (List.length outside);
  List.iter (fun r -> Printf.printf "    %-26s %s\n" r.a_binding r.a_schema) outside;
  mark "abi_instances" (List.length rows);
  mark "abi_prototypes" (List.length emittable);
  mark "abi_refused_no_c_type" (List.length blocked);
  mark "abi_bodies_expressible" (List.length expressible);
  mark "abi_bodies_owed" (List.length owed);
  mark "abi_blocked_outside_fold_set" (List.length outside);
  (* The arithmetic is asserted, not printed for information: a rendering that lost or
     invented an instance would still leave a plausible-looking header. *)
  let measured = Hashtbl.find_opt tally "instances_closed" in
  let problems =
    List.flatten
      [
        (match measured with
         | Some n when n = List.length rows -> []
         | Some n ->
             [ "this ABI names " ^ string_of_int (List.length rows)
               ^ " closed instances; MONOMORPHIZATION measured " ^ string_of_int n ]
         | None -> [ "instances_closed was never marked, so this ABI has nothing to agree with" ]);
        (if List.length blocked + List.length emittable = List.length rows then []
         else [ "prototypes + refusals do not add up to the rendered instances" ]);
        (if List.length expressible + List.length owed = List.length emittable then []
         else [ "expressible + owed bodies do not add up to the emitted prototypes" ]);
        (if outside = [] then []
         else
           [ "a refusal belongs to no rewrite §6.3 lists: "
             ^ String.concat ", " (List.map (fun r -> r.a_binding) outside) ]);
      ]
  in
  if problems <> [] then begin
    Printf.printf "\nLOWER REFUSAL: the ABI does not account for the census's own closed set:\n";
    List.iter (fun m -> Printf.printf "  %s\n" m) problems;
    exit 1
  end;
  Printf.printf "\nABI CONSISTENT: every closed instance is accounted for, and every refusal\n\
                \  belongs to a binding §6.3 already lists as a model-side rewrite.\n";
  rows

(* The header this section renders.  Names are positional — the n-th closed instance of a
   binding — which is why the file is vendored and byte-compared instead of regenerated
   silently: a shift in the instance set moves a symbol, and the gate is what notices. *)
let write_abi path rows =
  let b = Buffer.create 4096 in
  let fmt s = Printf.ksprintf (fun x -> Buffer.add_string b x) s in
  fmt "/* sh_run_jpl_abi.h — the R8 instance ABI, rendered by the lowering census.\n\
      \   GENERATED by verify/c/jpl_lower.ml from the vendored extraction\n\
      \   (src/kernel/sh_run_c.ml{,i}) over roots mrun_c,step_c — DO NOT EDIT, and do not\n\
      \   hand-write a body next to a declaration here.\n\
      \   Every type name below is the rule the representation layer applied when it emitted\n\
      \   sh_run_jpl.h, so this file is valid only AFTER that one:\n\
      \     #include \"sh_run_jpl.h\"\n\
      \   Declarations only: no function in this file has a body, and the ones marked OWED\n\
      \   must not get one until JPL.md §6.3's model-side rewrite lands. */\n\
      \n\
      #ifndef SH_RUN_JPL_ABI_H\n\
      #define SH_RUN_JPL_ABI_H\n";
  List.iter
    (fun r ->
      fmt "\n/* %s : %s\n" r.a_binding r.a_render;
      fmt "   instance %d, schema %s\n" r.a_index r.a_schema;
      fmt "   used by %s */\n"
        (String.concat ", "
           (List.map (fun (o, ln) -> o ^ ":" ^ string_of_int ln) r.a_users));
      if r.a_block <> "" then
        fmt "/* NOT EMITTED — %s: %s */\n" r.a_symbol r.a_block
      else begin
        fmt "%s %s(%s);\n" (value_name r.a_result) r.a_symbol
          (if r.a_params = [] then "void"
           else
             String.concat ", "
               (List.mapi
                  (fun i p -> value_name p ^ " a" ^ string_of_int (i + 1))
                  r.a_params));
        if not (body_expressible_class r.a_schema) then
          fmt "/* declaration only: no body until the §6.3 rewrite for this schema lands\n\
   \   (schema: %s) */\n" r.a_schema
      end)
    rows;
  fmt "\n#endif /* SH_RUN_JPL_ABI_H */\n";
  let oc = open_out path in
  output_string oc (Buffer.contents b);
  close_out oc

(* ───────── 8c. renderability: can this body be written at all yet? ───────── *)

(* §6.3 decided each binding's SHAPE.  Before a single statement can be written there is a
   second question, and it has exactly three negatives — does this body need a pool, an
   allocator, or a function value (JPL.md §6.4)?  This section does not answer it from the
   outside: THE VERDICT IS THE RENDERER'S OWN TRIAL RESULT.  A census that classified bodies
   by rules of its own and a renderer that followed different ones would be two models of one
   artifact, which is the failure §2 forbids — so the census asks the renderer to render, and
   reports what came back.  "Renderable" therefore means "this file produced C for it", and
   every refusal is the renderer's own sentence rather than a category the census hoped for.

   What the trial is not left to guess it takes from the sections above: §7's schema class,
   §6's self-call count, and §8's `pool_of` over the sites §5 recorded and over the binding's
   own signature.  The rules are tried in dependency order — an operator alias has no
   definition to write, a folded constant already has a name in 2e's header, a self-call has
   no statement form until §6.3's rewrite lands, a body that touches a pooled value has no
   cell until decision 3's copying lands — and only last comes the renderer's own set of
   refusals, which is the single class that shrinks when this file grows a rule. *)

type verdict =
  { v_name : string;
    v_class : string;        (* §7's schema, kept beside the verdict so the two readings meet *)
    v_verdict : string;
    v_reason : string;
    v_def : string;          (* the rendered definition; "" unless the verdict is RENDER *)
    v_cites : string list;   (* data macros the body cites, so the gate can find each one *)
    v_calls : string list }  (* bindings it calls, each of which had to render first *)

(* The trial's two escapes.  `Waiting` is what makes this a fixpoint instead of a first
   guess: a body may be renderable only once what it calls is known to be, and `is_name`
   over `is_alpha` is exactly that case. *)
exception Refused of string
exception Waiting of string

let refuse m = raise (Refused m)

(* §6.4's licensed operators: what the artifact writes, and what C writes.  `=` becomes `==`
   ONLY because every operand is checked scalar first: a `text` is a word-slab handle,
   handle equality is not word equality, and structural equality is a binding of its own
   (`teqb`) for exactly that reason — a renderer that licensed `=` over a `text` would lower
   the wrong program and the differential sweep would never see it. *)
let c_infix =
  [ ("=", "=="); ("<>", "!="); ("<=", "<="); ("<", "<"); (">=", ">="); (">", ">");
    ("&&", "&&"); ("||", "||"); ("+", "+"); ("-", "-") ]

let c_prefix = [ "not"; "Stdlib.not" ]

(* Names a C definition cannot take, checked rather than assumed: the artifact's binders are
   the parameter names 2e printed in the prototype this definition has to match, and one that
   collides with a keyword would be a compile error in the emitted file instead of a
   measurement here. *)
let c_keywords =
  [ "auto"; "break"; "case"; "char"; "const"; "continue"; "default"; "do"; "double";
    "else"; "enum"; "extern"; "float"; "for"; "goto"; "if"; "inline"; "int"; "long";
    "register"; "return"; "short"; "signed"; "sizeof"; "static"; "struct"; "switch";
    "typedef"; "union"; "unsigned"; "void"; "volatile"; "while" ]

(* which layouts the renderer may compute on without touching a cell *)
let scalar_lt t = match resolve t with L_nat | L_bool | L_unit -> true | _ -> false

(* A DATA binding's C name: the macro the caps table already carries when it has one, the
   header's own `JPL_C_` spelling when it does not.  Both halves are the shared reader's
   rule, so 2e's prototype layer and this trial cannot name one number two ways. *)
let macro_for nm = data_macro nm ?cap:(cap_macro_of_data nm)

let rec render_e scope done_v cites calls (e : expression) : string * lt =
  match e.pexp_desc with
  | Pexp_constant { pconst_desc = Pconst_integer (s, None); _ } -> (s ^ "u", L_nat)
  | Pexp_constant { pconst_desc = c; _ } -> refuse ("a " ^ describe_const c ^ " literal")
  | Pexp_ident { txt } -> render_name scope done_v cites (li txt)
  | Pexp_construct ({ txt }, arg) ->
      (match li txt, arg with
       | "true", None -> ("1u", L_bool)
       | "false", None -> ("0u", L_bool)
       | nm, _ ->
           refuse (Printf.sprintf "the %s it builds, which is a value with a representation and not a literal"
                     nm))
  | Pexp_ifthenelse (cnd, tru, Some fls) ->
      let cc, ct = render_e scope done_v cites calls cnd in
      let tc, tt = render_e scope done_v cites calls tru in
      let fc, ft = render_e scope done_v cites calls fls in
      if not (scalar_lt ct) then
        refuse (Printf.sprintf "a condition of type %s, which is not a scalar" (pr_lt ct))
      else if resolve tt <> resolve ft then
        refuse (Printf.sprintf "two branches of different layouts (%s and %s)" (pr_lt tt) (pr_lt ft))
      else ("(" ^ cc ^ " ? " ^ tc ^ " : " ^ fc ^ ")", tt)
  | Pexp_ifthenelse _ -> refuse "an if without an else, which is a statement and not an expression"
  | Pexp_apply (f, args) ->
      (* A numeral the artifact wrote as a unary `succ` chain folds to ONE C constant, which
         is what makes `is_digit`'s upper bound renderable at all: the shared reader's folder
         is where that equation lives, and this file does not re-derive it. *)
      (match try_fold e with
       | Some v -> (string_of_int v ^ "u", L_nat)
       | None ->
         if not (List.for_all (fun (l, _) -> l = Nolabel) args) then refuse "a labelled argument"
         else
           let al = List.map snd args in
           match f.pexp_desc with
           | Pexp_ident { txt } when List.mem_assoc (li txt) c_infix ->
               render_infix scope done_v cites calls (li txt) al
           | Pexp_ident { txt } when List.mem (li txt) c_prefix ->
               (match al with
                | [ x ] ->
                    let a, t = render_e scope done_v cites calls x in
                    if resolve t <> L_bool then
                      refuse (Printf.sprintf "not applied to %s, which is not a bool" (pr_lt t))
                    else ("(! " ^ a ^ ")", L_bool)
                | _ -> refuse (Printf.sprintf "a prefix operator applied to %d arguments" (List.length al)))
           | Pexp_ident { txt } -> render_call scope done_v cites calls (li txt) al
           | _ -> refuse ("an applied " ^ eclass f ^ ", which is a function value"))
  | Pexp_tuple _ -> refuse "a tuple, which builds a cell"
  | Pexp_function _ -> refuse "a function value inside the body"
  | Pexp_let _ -> refuse "a nested let, which is a statement sequence"
  | Pexp_record _ -> refuse "a record value, which is §6.2's decision 1"
  | Pexp_field _ -> refuse "a field read, whose layout this file does not own"
  | Pexp_match _ -> refuse "a match, whose arms read a tag and a payload out of a cell"
  | _ -> refuse (Printf.sprintf "%s, which is outside §6.4's licensed scalar set" (eclass e))

(* A name that is not a binder of the body being rendered.  A DATA binding lends the macro
   the header already defines for it — never a re-typed numeral, which would be the second
   name §6.4 forbids — and a rendered binding is licensed only APPLIED, not as a value. *)
and render_name scope done_v cites nm =
  if Hashtbl.mem scope nm then (nm, resolve (Hashtbl.find scope nm))
  else if List.mem nm operator_names then
    refuse (Printf.sprintf "the operator %s used as a value, which needs the function pointer D-60411 forbids" nm)
  else if not (Hashtbl.mem binds nm) then refuse ("an unbound name " ^ nm)
  else
    match Hashtbl.find_opt done_v nm with
    | None -> raise (Waiting nm)
    | Some v when v.v_verdict = "DATA" ->
        let m = macro_for nm in
        cites := m :: !cites;
        (m, if Hashtbl.mem vals nm then snd (lt_spine (decl_full nm) []) else L_nat)
    | Some v when v.v_verdict = "RENDER" ->
        refuse (Printf.sprintf "names %s as a value; only a call of it is licensed" nm)
    | Some v -> refuse (v.v_name ^ " is " ^ v.v_verdict ^ ", so nothing exists for it to refer to")

(* Both operands of a licensed infix operator, checked against the family that operator is
   defined over: the C spelling is equivalent only where the artifact's own types say the
   values are scalars of one kind. *)
and render_infix scope done_v cites calls op al =
  if List.length al <> 2 then
    refuse (Printf.sprintf "%s applied to %d arguments, and §6.4 licenses no curried call"
             op (List.length al))
  else begin
    let a, ta = render_e scope done_v cites calls (List.nth al 0) in
    let b, tb = render_e scope done_v cites calls (List.nth al 1) in
    let logic = op = "&&" || op = "||" in
    let arith = op = "+" || op = "-" in
    let ok =
      if logic then resolve ta = L_bool && resolve tb = L_bool
      else if arith then resolve ta = L_nat && resolve tb = L_nat
      else scalar_lt ta && scalar_lt tb
           && (match resolve ta, resolve tb with
               | L_nat, L_nat -> true
               | L_bool, L_bool -> op = "=" || op = "<>"
               | L_unit, L_unit -> op = "=" || op = "<>"
               | _ -> false)
    in
    if not ok then
      refuse (Printf.sprintf "%s over %s and %s, which §6.4 licenses only within one scalar family"
               op (pr_lt ta) (pr_lt tb))
    else ("(" ^ a ^ " " ^ List.assoc op c_infix ^ " " ^ b ^ ")", if arith then L_nat else L_bool)
  end

(* A call is licensed only once the callee rendered, and its arity and result come from the
   interface it exports — not from this walk's opinion of the argument list. *)
and render_call scope done_v cites calls nm al =
  if not (Hashtbl.mem binds nm) then
    refuse (Printf.sprintf "an applied %s that is not a binding of this artifact" nm)
  else
    match Hashtbl.find_opt done_v nm with
    | None -> raise (Waiting nm)
    | Some v when v.v_verdict <> "RENDER" ->
        refuse (Printf.sprintf "calls %s, whose verdict is %s, so no definition exists to call"
                 nm v.v_verdict)
    | Some _ ->
        let ps, res = lt_spine (decl_full nm) [] in
        if List.length ps <> List.length al then
          refuse (Printf.sprintf "calls %s with %d arguments and its interface has %d"
                   nm (List.length al) (List.length ps))
        else begin
          let rendered = List.map (fun x -> fst (render_e scope done_v cites calls x)) al in
          calls := nm :: !calls;
          (c_fn nm ^ "(" ^ String.concat ", " rendered ^ ")", res)
        end

(* One binding's definition, or the renderer's refusal in its own words.  The parameter names
   are the artifact's own, which is the rule 2e applied to the prototype this definition must
   agree with, so the two files cannot state different signatures for one function. *)
let render_def n done_v =
  try
    if not (Hashtbl.mem vals n) then refuse "no signature in the interface, so nothing to match";
    let b = Hashtbl.find binds n in
    let ps, res = lt_spine (decl_full n) [] in
    let names, body = peel_params b.b_body [] in
    if List.length names <> List.length ps then
      refuse (Printf.sprintf "its %d binder names do not line up with the %d parameters it exports"
               (List.length names) (List.length ps));
    List.iter
      (fun nm ->
        if nm = "" || nm = "_" then refuse "an unnamed parameter, which C cannot declare";
        if List.mem nm c_keywords then
          refuse (Printf.sprintf "a parameter named %s, which is a C keyword" nm))
      names;
    if not (List.for_all scalar_lt ps) || not (scalar_lt res) then
      refuse "a parameter or result that is not a scalar";
    let scope = Hashtbl.create 8 in
    List.iter2 (fun nm t -> Hashtbl.replace scope nm (resolve t)) names ps;
    let cites = ref [] and calls = ref [] in
    let expr, got = render_e scope done_v cites calls body in
    if resolve got <> resolve res then
      refuse (Printf.sprintf "its body computes %s and the interface it exports says %s"
               (pr_lt got) (pr_lt res));
    (* C's `&&`, `||` and every comparison yield `int`; a `jpl_bool` is one word, so the
       conversion is made explicit instead of being left for -Wconversion to flag. *)
    let value = if resolve res = L_bool then "(jpl_bool) " ^ expr else expr in
    let args =
      if ps = [] then "void"
      else String.concat ", " (List.map2 (fun nm t -> value_name (resolve t) ^ " " ^ nm) names ps)
    in
    Ok (Printf.sprintf "%s %s(%s)\n{\n  return %s;\n}" (value_name res) (c_fn n) args value,
        List.sort_uniq String.compare !cites,
        List.sort_uniq String.compare !calls)
  with Refused m -> Error m

(* The three verdicts that need no knowledge of any other binding, in the order §6.4 lists
   them.  None is not a verdict — it is the trial's turn. *)
let base_verdict n schemas =
  let b = Hashtbl.find binds n in
  let self = !((Hashtbl.find closure n).self) in  let cls = schema_class schemas n in
  let v vd rs =
    Some { v_name = n; v_class = cls; v_verdict = vd; v_reason = rs;
           v_def = ""; v_cites = []; v_calls = [] }
  in
  if cls = "operator alias" || cls = "value alias" then
    v "ALIAS" "the body IS an operator, so C spells it at the use site and no function exists"
  else if Hashtbl.mem vals n
          && (match lt_spine (decl_full n) [] with ([], _) -> true | _ -> false)
          && try_fold b.b_body <> None then
    match try_fold b.b_body with
    | Some x ->
        v "DATA"
          (Printf.sprintf "a folded constant (= %d); its C name is %s, which 2e's header already defines"
             x (macro_for n))
    | None -> None
  else if self > 0 || starts cls "BOUNDED FOLD" || starts cls "FUEL LOOP"
          || starts cls "BLOCKED" then
    v "OWED-SCHEMA"
      (Printf.sprintf "%s, and %d direct self-call(s) have no statement form until §6.3's\n\
        \     rewrite for this schema lands" cls self)
  else None

(* Does this body touch a pooled value?  BOTH directions count: building one needs the
   allocator, and reading one needs the cell to exist already.  `raw_bword` and `expand_c`
   are the rows that show the difference — straight-line, consing nothing, and still taking
   or returning a word slab — so a rule that looked only at allocation sites would have
   called them renderable and handed JPL.6 a body that could not compile.  `teqb` is the
   same shape one rung earlier: it reads a slab too, and is refused for its schema before
   this rule is ever consulted, which is exactly why the rules are tried in dependency
   order and only the last of them is the renderer's own set. *)
let pools_of n =
  let own = if Hashtbl.mem vals n then sig_pools [] (decl_full n) else [] in
  let built =
    List.filter_map
      (fun (kind, t, owner, ln) ->
        if owner <> n then None
        else match pool_of t with Some (arr, _) -> Some (kind, arr, ln) | None -> None)
      !sites
  in
  (own, built)

(* Does the sweep cover this body's whole domain?  A body of one nat parameter is run on
   every value the artifact's own fuel cap bounds, so the differential over it is exhaustive
   rather than sampled; anything else (arity 0, arity >1, a bool parameter) is run on a
   DIAGONAL — one index driving every argument — and the claim for it has to say so. *)
let sweep_params n = fst (lt_spine (decl_full n) [])

let sweep_total r =
  match sweep_params r.v_name with
  | [ t ] -> resolve t = L_nat
  | _ -> false

(* The census: every member exactly once, in artifact order, the trial re-run until nothing is
   still waiting on a callee.  A cycle cannot normally reach here — a self-call is OWED-SCHEMA
   above and a mutual fixpoint was refused before any of this ran — so a row that never
   settles is printed as what it is rather than given a verdict this file invented. *)
let print_render members schemas =
  section "RENDERABILITY: WHICH BODIES NEED NO POOL, NO ALLOCATOR AND NO FUNCTION VALUE";
  Printf.printf "  The verdict below is the renderer's OWN trial result, not a class this file\n\
                \  assigned: JPL.md §6.4's licensed scalar set is implemented once, above, and run\n\
                \  here as a question.  A body the trial refuses is reported in the refusal's own\n\
                \  words, so the census cannot claim a body is renderable that the emitter then\n\
                \  could not write.\n";
  let vd : (string, verdict) Hashtbl.t = Hashtbl.create 64 in
  let set v = Hashtbl.replace vd v.v_name v in
  let owed n verdict rs =
    set { v_name = n; v_class = schema_class schemas n; v_verdict = verdict; v_reason = rs;
          v_def = ""; v_cites = []; v_calls = [] }
  in
  List.iter (fun n -> match base_verdict n schemas with Some v -> set v | None -> ()) members;
  let trial n =
    match pools_of n with
    | [], [] ->
        (match render_def n vd with
         | Ok (def, cites, calls) ->
             set { v_name = n; v_class = schema_class schemas n; v_verdict = "RENDER";
                   v_reason = "no pool, no cell, no function value: the trial rendered it";
                   v_def = def; v_cites = cites; v_calls = calls }
         | Error m -> owed n "OWED-CONSTRUCT" m
         (* Waiting is not a verdict: the body stays undecided and this pass simply moves on,
            so the NEXT pass asks the same question with one more callee already answered. *)
         | exception Waiting _ -> ())
    | _, (kind, arr, ln) :: _ ->
        owed n "OWED-REPRESENTATION"
          (Printf.sprintf "builds %s at line %d, whose cells live in %s" kind ln arr)
    | (arr, _) :: _, [] ->
        owed n "OWED-REPRESENTATION"
          (Printf.sprintf "takes or returns %s, whose cells decision 3's step-boundary copying produces" arr)
  in
  let rec loop waiting =
    let todo = List.filter (fun n -> not (Hashtbl.mem vd n)) members in
    match todo with
    | [] -> ()
    | _ ->
        List.iter trial todo;
        let still = List.filter (fun n -> not (Hashtbl.mem vd n)) members in
        (* a body only ever stays undecided by waiting on a callee, so `waiting` remembers
           what it was waiting for and the finding can name it *)
        if still <> [] && still <> waiting then loop still
        else
          List.iter
            (fun n -> owed n "OWED-SCHEMA" "its calls never settled: the bodies it needs depend on it")
            still
  in
  loop [];
  let rows = List.filter_map (fun n -> Hashtbl.find_opt vd n) members in
  let by v = List.filter (fun r -> r.v_verdict = v) rows in
  Printf.printf "\n  %-20s %-36s %-22s %s\n" "binding" "§6.3 schema" "verdict" "what the trial said";
  List.iter
    (fun r ->
      Printf.printf "  %-20s %-36s %-22s %s\n" r.v_name r.v_class r.v_verdict r.v_reason)
    rows;
  let rendered = by "RENDER" in
  Printf.printf "\n  RENDERED BODIES (%d), and what each one cites:\n" (List.length rendered);
  List.iter
    (fun r ->
      Printf.printf "\n  %s\n" (c_fn r.v_name);
      Printf.printf "    cites   %s\n"
        (if r.v_cites = [] then "(no data constant)" else String.concat ", " r.v_cites);
      Printf.printf "    calls   %s\n"
        (if r.v_calls = [] then "(no other binding)" else String.concat ", " r.v_calls);
      Printf.printf "    arity   %d, sweep %s\n"
        (List.length (fst (lt_spine (decl_full r.v_name) [])))
        (if sweep_total r then "EXHAUSTIVE over 0 … MAX_FUEL (its one nat argument is the index)"
         else "DIAGONAL: 0 … MAX_FUEL, every argument derived from one index"))
    rendered;
  Printf.printf "\n  RENDER PARTITION (every closure member, exactly once)\n";
  List.iter
    (fun (v, key, what) ->
      let n = List.length (by v) in
      mark key n;
      Printf.printf "  %-24s %4d   %-24s %s\n" v n key what)
    [ ("DATA", "data_bindings", "arity-0 constants; the header already names them");
      ("ALIAS", "alias_bindings", "bodies that ARE an operator, so no function is emitted");
      ("RENDER", "bodies_renderable", "no pool, no cell, no function value: emitted here");
      ("OWED-REPRESENTATION", "owed_representation", "touch a pooled value, to build it or to read it");
      ("OWED-SCHEMA", "owed_schema", "their §6.3 shape has no statement form yet");
      ("OWED-CONSTRUCT", "owed_construct", "the renderer named the construct it cannot write") ];
  let total = List.length rows in
  let unaccounted = List.length members - total in
  let citing = List.length (List.filter (fun r -> r.v_cites <> []) rendered) in
  mark "render_unaccounted" unaccounted;
  mark "bodies_citing_data" citing;
  Printf.printf "  %-24s %4d   %s\n" "rows" total "one verdict per member visited";
  Printf.printf "  %-24s %4d   %s\n" "render_unaccounted" unaccounted
    "a member that received no verdict; must be 0";
  Printf.printf "  %-24s %4d   %s\n" "bodies_citing_data" citing
    "rendered bodies that cite a data constant by its header macro";
  (* One line per DATA binding, in a form the gate can grep rather than re-read as prose:
     each name below has to be a `#define` in sh_run_jpl.h, because a rendered body that
     cites a constant the header never defined would be a link error JPL.7 pays for.  The
     set is closed under the citations — render_name cites only through this same
     `macro_for`, so a cited macro that fails to resolve would already appear here. *)
  Printf.printf "\n  THE DATA NAMES A RENDERED BODY CAN RESOLVE TO (the gate finds each one\n\
                \  as a #define in sh_run_jpl.h)\n";
  List.iter
    (fun r -> Printf.printf "  DATA-MACRO %-14s %s\n" r.v_name (macro_for r.v_name))
    (by "DATA");
  (* The differential the gate runs against this file, stated as a measurement rather than
     as a promise: the domain is the artifact's own fuel cap, and what the cap bounds is
     printed per body so an exhaustive claim and a diagonal one cannot be confused. *)
  let fuel = (c ()).c_fuel in
  let exhaustive = List.fold_left (fun a r -> if sweep_total r then a + 1 else a) 0 rendered in
  let diagonal = List.length rendered - exhaustive in
  mark "sweep_domain" fuel;
  mark "bodies_swept_exhaustive" exhaustive;
  mark "bodies_swept_diagonal" diagonal;
  Printf.printf "\n  THE DIFFERENTIAL THE GATE RUNS ON THE RENDERED BODIES\n";
  Printf.printf "    domain     0 … %d  (MAX_FUEL, read from the artifact's own jpl_caps_table:\n\
                \               the same cap the C allocates against, so neither driver picks\n\
                \               a range for the claim it is testing)\n" fuel;
  Printf.printf "    lines      %d per driver, one per index, one field per body in artifact order\n\
                \               (the two drivers are GENERATED from these same RENDER rows, so a\n\
                \               body the census invented a test for would show up as a\n\
                \               transcript whose field count disagrees with this report)\n"
    (fuel + 1);
  Printf.printf "    bodies     %d rendered: %d swept EXHAUSTIVELY (one nat parameter = the index),\n\
                \               %d swept on the DIAGONAL\n" (List.length rendered) exhaustive
    diagonal;
  if diagonal > 0 then
    Printf.printf "\n    SWEEP COVERAGE FINDING: %d rendered body(s) take %s, so 0 … MAX_FUEL\n\
                  \    exercises only the diagonal of their argument space.  The differential\n\
                  \    proves agreement there and nowhere else for them; a product sweep needs a\n\
                  \    budget of its own, which §6.4 does not license this stage to invent.\n"
      diagonal "more than one argument, or none";
  (* The ALIAS rows carry a consequence this census can see and cannot fix: 2e's header
     prototypes `jpl_add`/`jpl_mul` because it reads them as bindings, and §6.3 says an
     operator alias has no function to define.  Printed as a finding with its owner, because
     a call left in the artifact would be a link error JPL.7 pays for, not a measurement this
     file can make up. *)
  let aliases = by "ALIAS" in
  if aliases <> [] then begin
    Printf.printf "\n  FINDING, with an owner (not a failure): %d alias binding(s) have a\n\
                  \  prototype in sh_run_jpl.h and no definition anywhere, because their body\n\
                  \  IS a C operator.  Either the representation layer drops those prototypes or\n\
                  \  JPL.6's lint forbids calling them by name; inventing a definition here\n\
                  \  would be a second lowering of an operator §6.3 already replaced.\n"
      (List.length aliases);
    List.iter (fun r -> Printf.printf "    %-20s %s\n" (c_fn r.v_name) r.v_class) aliases
  end;
  if unaccounted <> 0 || total <> List.length members then begin
    Printf.printf "\nLOWER REFUSAL: the renderability verdicts do not partition the closure\n\
                  \  (%d rows over %d members), so the census would be reporting an opinion\n\
                  \  about bindings it did not visit.\n"
      total (List.length members);
    exit 1
  end;
  Printf.printf "\nRENDERABILITY CONSISTENT: %d of %d members carry one verdict each, and the %d\n\
                \  rendered bodies are the ones this file can actually print — which is the only\n\
                \  sense in which a body is renderable.\n"
    total (List.length members) (List.length rendered);
  rows

(* The file this section's RENDER rows add up to.  Each definition answers a prototype
   2e already emitted, so the vendored bytes are checkable against the header they belong
   to rather than against this file's memory of it. *)
let write_bodies path rows =
  let b = Buffer.create 4096 in
  let fmt s = Printf.ksprintf (fun x -> Buffer.add_string b x) s in
  let rendered = List.filter (fun r -> r.v_verdict = "RENDER") rows in
  fmt "/* sh_run_jpl_bodies.c — the function BODIES the lowering census could render,\n\
      \   JPL.5-B.3b-ii-a.\n\
      \   GENERATED by verify/c/jpl_lower.ml from the vendored extraction\n\
      \   (src/kernel/sh_run_c.ml{,i}) over roots mrun_c,step_c — DO NOT EDIT.\n\
      \   Every definition here ANSWERS a prototype in sh_run_jpl.h, so it is valid only with\n\
      \   that header, and the gate compiles the two together:\n\
      \     #include \"sh_run_jpl.h\"\n\
      \   A body is here because JPL.md §6.4's render trial accepted it: no pool, no allocator,\n\
      \   no function value.  Nothing here allocates, so nothing here measures the extent that\n\
      \   §6.2's headroom factor still owes.  The bodies that were refused, and the construct or\n\
      \   schema that refused each, are in lowering.txt — the count in this file is not the\n\
      \   census's opinion of itself, it is the same measurement with C attached. */\n\
      \n\
      #include \"sh_run_jpl.h\"\n";
  List.iter
    (fun r ->
      fmt "\n/* %s : %s\n" r.v_name (pr_lt (decl_full r.v_name));
      fmt "   schema %s, verdict %s\n" r.v_class r.v_verdict;
      fmt "   %s */\n"
        (if r.v_cites = [] && r.v_calls = [] then "cites no data constant, calls no binding"
         else
           Printf.sprintf "cites %s; calls %s"
             (if r.v_cites = [] then "nothing" else String.concat ", " r.v_cites)
             (if r.v_calls = [] then "nothing" else String.concat ", " r.v_calls));
      fmt "%s\n" r.v_def)
    rendered;
  fmt "\n/* rendered bodies: %d of %d closure members; the other verdicts are measured in\n\
      \   lowering.txt and owned by JPL.md §6.3 (§6.4's table says which) */\n"
    (List.length rendered) (List.length rows);
  let oc = open_out path in
  output_string oc (Buffer.contents b);
  close_out oc

(* ─────────── 8d. the differential the RENDER rows are tested by ─────────── *)

(* "Renderable" is a claim about CONSTRUCTS; correctness of the C is a different claim, and
   the two drivers here are what make it.  Both are GENERATED from the same RENDER rows this
   census printed, in the same order, because a hand-typed list of the functions to sweep
   would be a second model of which bodies exist: the day the renderer gains a rule and the
   driver list is not updated, the gate would be proving a subset while reporting the whole.
   The index drives every argument (`i` for a nat, `i mod 2` for a bool), so a body of one
   nat parameter is swept over its entire bounded domain and anything else is swept on a
   diagonal — which the report above measures and prints, rather than hiding.

   The domain is JPL_MAX_FUEL on the C side and `mAX_FUEL` on the OCaml side.  Both are the
   artifact's own cap — one because 2e defined the macro from the extracted record, the other
   because it IS that record's field — so neither driver chooses the range of the claim it is
   testing, and a transcript length the gate checks against the census's `sweep_domain` key
   closes the loop.

   These are HOST programs, not shipped kernel code: they include <stdio.h>, they use printf,
   and JPL.6's lint does not apply to them.  The kernel's own conformance is sh_run_jpl.h +
   sh_run_jpl_bodies.c, which check 6 compiles under the full flag set. *)

(* An argument of the rendered body, in each language, derived from the one sweep index.
   The three cases are exhaustive because a RENDER row exists only for a body whose every
   parameter passed `scalar_lt` — nat, bool or unit — so no other layout can reach here. *)
let c_sweep_arg t =
  match resolve t with
  | L_nat -> "i"
  | L_bool -> "((jpl_bool) ((i % 2u) != 0u))"
  | _ -> "((jpl_unit) 0u)"

let ml_sweep_arg t =
  match resolve t with
  | L_nat -> "i"
  | L_bool -> "((i mod 2) = 1)"
  | _ -> "()"

(* The call, and the conversion that makes the two languages print one digit per result:
   OCaml's `true`/`false` becomes 1/0, its `()` becomes 0, and C's `jpl_bool` is already a
   one-word 0/1 — so a C bool that ever held 2 would show up as a transcript difference
   instead of being smoothed over by printing both sides as words. *)
let c_call r =
  let ps, _ = lt_spine (decl_full r.v_name) [] in
  c_fn r.v_name ^ "("
  ^ (if ps = [] then "void" else String.concat ", " (List.map c_sweep_arg ps))
  ^ ")"

let ml_call r =
  let ps, res = lt_spine (decl_full r.v_name) [] in
  (* The artifact's own OCaml name, dots and all: extraction qualifies a name like `Nat.add`
     with a module path this driver could not spell, and no such binding is a RENDER row —
     if one ever became one, the OCaml build of the driver would fail rather than silently
     test nothing.  Every call is parenthesised because the driver passes it straight to
     `Printf.printf`, where an unparenthesised `f x` would be read as two arguments. *)
  let app = "Sh_run_c." ^ r.v_name
            ^ (if ps = [] then "" else " " ^ String.concat " " (List.map ml_sweep_arg ps))
  in
  let e = "(" ^ app ^ ")" in
  match resolve res with
  | L_bool -> "(if " ^ e ^ " then 1 else 0)"
  | L_unit -> "(" ^ e ^ "; 0)"
  | _ -> e

let write_diff_c path rows =
  let rendered = List.filter (fun r -> r.v_verdict = "RENDER") rows in
  let fields = 1 + List.length rendered in
  let lines = (c ()).c_fuel + 1 in
  let oc = open_out path in
  Printf.fprintf oc "\
/* jpl_bodies_diff.c — the C half of the rendered-bodies differential, 5-B.3b-ii-a.
   GENERATED by verify/c/jpl_lower.ml from the same RENDER rows that wrote
   sh_run_jpl_bodies.c — DO NOT EDIT, and do not add a function to it by hand.
   Link with sh_run_jpl_bodies.c; print the %d lines (%d fields: the index, then one
   per rendered body in artifact order) the OCaml driver jpl_bodies_diff.ml prints,
   over 0 … JPL_MAX_FUEL — the cap the artifact carries, not a range chosen here.
   A HOST driver: <stdio.h> and printf are this file's business, not the shipped
   kernel's, so JPL.6's lint does not audit it. */

#include <stdio.h>
#include \"sh_run_jpl.h\"

int main(void)
{
  jpl_nat i;
  for (i = 0u; i <= JPL_MAX_FUEL; i = i + 1u) {
    printf(\"%s\\n\", %s);
  }
  return 0;
}
"
    lines fields
    (String.concat " " (List.init fields (fun _ -> "%u")))
    (String.concat ", " ("i" :: List.map c_call rendered));
  close_out oc

let write_diff_ml path rows =
  let rendered = List.filter (fun r -> r.v_verdict = "RENDER") rows in
  let fields = 1 + List.length rendered in
  let lines = (c ()).c_fuel + 1 in
  let args = String.concat " " ("i" :: List.map ml_call rendered) in
  let oc = open_out path in
  Printf.fprintf oc "\
(* jpl_bodies_diff.ml — the OCaml half of the rendered-bodies differential,
   5-B.3b-ii-a.  GENERATED by verify/c/jpl_lower.ml from the same RENDER rows that
   wrote sh_run_jpl_bodies.c — DO NOT EDIT, and do not add a call to it by hand.
   Compiled against the vendored extraction (src/kernel/sh_run_c.ml{,i}), the SAME
   artifact the census read, and printing the SAME %d lines (%d fields) as the C
   driver jpl_bodies_diff.c, over 0 … mAX_FUEL.  `cmp` of the two transcripts is
   the rung that turns \"the renderer wrote C\" into \"the C computes what the
   extracted kernel computes\", over every bounded input. *)

let () =
  let fuel = Sh_run_c.mAX_FUEL in
  for i = 0 to fuel do
    Printf.printf \"%s\\n\" %s
  done
"
    lines fields
    (String.concat " " (List.init fields (fun _ -> "%d")))
    args;
  close_out oc

(* ───────────────────────────── 9. the report ───────────────────────────── *)

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
  let opened = ref 0 in
  let closed = ref 0 in
  let poly = List.filter (fun n -> has_var (decl_full n)) members in
  mark "polymorphic_bindings" (List.length poly);
  if poly = [] then print_endline "  (no polymorphic binding in the closure)"
  else
    begin
      Printf.printf "  An instance is named by a variable of THIS census, never by the artifact's `'a1`:\n\
                    \  each binding's declared type is freshened before it is pushed into the body, so a\n\
                    \  name that appears in two rows is a sharing the code really has (app's use inside\n\
                    \  rev is rev's own parameter) and two names are two unresolved use POINTS.  Counting\n\
                    \  those points is what R8 needs: a closed instance is one C function, an open one is\n\
                    \  nothing to emit yet.\n";
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
              if open_ then incr opened else incr closed;
              Printf.printf "     instance  %-46s  %s\n" s
                (if open_ then "STILL OPEN: no layout, so nothing to emit"
                 else "closed: one C function for this instance");
              List.iter
                (fun (_, owner, ln, _) ->
                  Printf.printf "               used by %-16s at %s:%d\n" owner !src_path ln)
                here)
            uniq;
          mark "instance_uses" ((try Hashtbl.find tally "instance_uses" with Not_found -> 0)
                                + List.length uses))
        poly;
      mark "instances_open" !opened;
      mark "instances_closed" !closed
    end

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
          else bump repr ("no pool demanded here: " ^ kind ^ "  :  " ^ pr_lt t))
    !sites;
  Printf.printf "  %-64s %s\n" "what is built, and what this walk derives from it" "sites";
  List.iter (fun (k, v) -> Printf.printf "  %-64s %d\n" k v) (sortl repr);
  Printf.printf "  A row that names a pool is that site's DEMAND for one.  A row that names none\n\
                \  claims only that this walk derives no cell from it: whether such a value is\n\
                \  a by-value struct or a pooled node handle is JPL.md §6.2's decision 1, which\n\
                \  is wider than the reach-itself rule this walk can read off the artifact's\n\
                \  text — `frame` is the case that shows the difference, and the header\n\
                \  cross-check in jpl_lower.sh is where the two readings are compared.\n";
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
  mark "pools_demanded" (List.length all);
  mark "open_allocation_sites" !unresolved;
  mark "allocation_sites" (List.length !sites);
  all

let print_caps members =
  section "BOUND CHECKS AGAINST THE LOCKED CAPS (the code's own enforcement)";
  let gs =
    List.sort
      (fun (a, _, _, _, _, x) (b, _, _, _, _, y) ->
        if a <> b then String.compare a b else compare x y)
      !guards
  in
  mark "bound_checks" (List.length gs);
  if gs = [] then print_endline "  (none)"
  else
    List.iter
      (fun (n, op, ty, capn, capm, ln) ->
        Printf.printf "  %-18s %s:%-6d %-3s  %-24s against %s (%s)\n" n !src_path ln op ty capn
          capm)
      gs;
  section "CAPACITIES: the artifact's own numbers, and the ways the closure consults them";
  Printf.printf "  A cap reaches the machine three ways: compared in a bound check, handed to a\n\
                \  call as an argument (which is how FUEL bounds a loop, and the reason a cap\n\
                \  with 0 checks is not necessarily unenforced), or not at all — and the last is\n\
                \  a finding, which is why the column is printed even when it is zero.\n";
  Printf.printf "  %-12s %-14s %-9s %-11s %-8s %-7s %s\n" "model name" "data binding" "exported"
    "jpl_caps_tbl" "members" "checks" "handed";
  List.iter
    (fun (field, _, model, _) ->
      let nm = cap_data model in
      let exported = if Hashtbl.mem binds nm then "yes" else "NO" in
      let n_reach =
        List.fold_left
          (fun a k -> if Hashtbl.mem (Hashtbl.find closure k).edges nm then a + 1 else a)
          0 members
      in
      let checks =
        List.fold_left (fun a (_, _, _, capn, _, _) -> if capn = nm then a + 1 else a) 0 !guards
      in
      let handed =
        List.fold_left (fun a (_, _, _, _, capn, _) -> if capn = nm then a + 1 else a) 0 !cap_args
      in
      Printf.printf "  %-12s %-14s %-9s %-11d %-8d %-7d %d\n" model nm exported
        (caps_of (c ()) field) n_reach checks handed)
    cap_fields;
  section "CAPACITIES HANDED TO A CALL (the bound the code applies without comparing it)";
  let cs =
    List.sort
      (fun (a, x, _, _, _, _) (b, y, _, _, _, _) ->
        if a <> b then String.compare a b else compare x y)
      !cap_args
  in
  if cs = [] then
    print_endline "  (none: no capacity constant reaches a call argument in the shipped closure)"
  else
    List.iter
      (fun (n, ln, callee, k, cn, exact) ->
        let note =
          if exact then ""
          else
            "\n    — inside a computed expression: the bound handed to this call is a SUM, so\n\
            \      its limit is a proof (sh_jpl.v §1), not a constant the code compares"
        in
        Printf.printf "  %-18s %s:%-6d the %s argument of %-16s is %s (%s)%s\n" n !src_path ln
          (ord k) callee cn
          (Option.value ~default:"?" (cap_macro_of_data cn))
          note)
      cs;
  mark "caps_handed_to_a_call" (List.length cs)

let print_lambdas () =
  section "FIRST-CLASS FUNCTIONS (what is a value, and what may stay one)";
  List.iter
    (fun (n, ln, use, ptys, one) ->
      Printf.printf "  %-18s %s:%-6d %-36s %s\n" n !src_path ln (lambda_use_name use)
        (if one then pr_lt (mk_tuple ptys) ^ ", matched as one scrutinee" else dom_note ptys))
    (List.sort
       (fun (a, x, _, _, _) (b, y, _, _, _) ->
         if a <> b then String.compare a b else compare x y)
       !lambdas);
  let other =
    List.filter_map
      (fun (n, ln, use, _, _) -> match use with LkOpen d -> Some (n, ln, d) | _ -> None)
      !lambdas
  in
  mark "function_value_sites" (List.length !lambdas);
  mark "function_value_sites_unnamed" (List.length other);
  Printf.printf "  Four positions make a function value safe: a fuel continuation is consumed by\n\
                \  the loop the idiom builds; a lambda at a known call site is inlined there; a\n\
                \  lambda applied at its own site is a redex the lowering folds away; and a\n\
                \  binding's own value becomes that binding's C function.  Anything else would\n\
                \  have to be a function pointer, which D-60411 forbids.  Sites in that remaining\n\
                \  class: %d\n"
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

(* ─────────────── 9e. the second debt (JPL.5-B.3b-ii-b-0, JPL.md §6.5) ─────────────── *)

(* §6.4's rules stop at the first match, which is what the partition needs and what the PLAN
   does not: an OWED-SCHEMA row has never printed the pools its signature takes or returns,
   so nothing in the report says whether a `while` form would render it.  This section asks
   the SAME question the renderability trial asks — `pool_of` over the signature and the
   binding's own allocation sites, the same reading, nothing re-derived — for every member,
   and prints both debts beside the one verdict.  It licenses nothing: no verdict changes, no
   body is emitted here, and the only new claim is about which slice of §6.5's table a row
   belongs to. *)

(* "no pool" needs a REASON before it can be read as freedom, because the walk stops in three
   different places (§6.5's second table): a signature that really is scalar, a list-shaped
   position whose element is still a type variable, and a declared record or variant whose
   FIELDS the walk does not enter — `step_c : cfg -> out` is the third, and `cfg`'s `ck` field
   IS the machine stack.  A count that conflated them would let a zero read as a licence. *)
type sight =
  { so_pools : (string * string) list; (* (pool array, cell or node type) *)
    so_open : int;                     (* positions whose type the interface has not decided *)
    so_opaque : string list }            (* declared types whose fields the walk cannot see *)

(* A named type the walk stops at: declared in the artifact, with no alias to follow, and not
   one of the self-referential names §6.2 pools by node. *)
let opaque_ty n =
  Hashtbl.mem tydecls n
  && (match alias_of n with Some _ -> false | None -> true)
  && not (reaches_itself n)

let rec sight acc t =
  match t with
  | L_var _ | L_unk _ -> { acc with so_open = acc.so_open + 1 }
  | L_nat | L_bool | L_unit -> acc
  | (L_word | L_list _ | L_named _) as x ->
      let a =
        match resolve x with
        | L_list e when has_var e -> { acc with so_open = acc.so_open + 1 }
        | L_named n when opaque_ty n -> { acc with so_opaque = n :: acc.so_opaque }
        | _ -> acc
      in
      (match pool_of x with Some p -> { a with so_pools = p :: a.so_pools } | None -> a)
  | L_opt e | L_bres e -> sight acc e
  | L_pair (p, q) | L_fun (p, q) -> sight (sight acc p) q

(* Both directions, exactly as §6.4's `pools_of` reads them: what a signature carries in, and
   what this binding's own body builds.  A row whose sites are all still variables lands in
   `so_open` rather than silently counting as pool-free. *)
let sight_of n =
  let z = { so_pools = []; so_open = 0; so_opaque = [] } in
  let s = if Hashtbl.mem vals n then sight z (decl_full n) else z in
  List.fold_left
    (fun a (_kind, t, owner, _ln) -> if owner <> n then a else sight a t)
    s
    !sites

(* §6.3's shape debt, read the way §6.4's rule reads it: a direct self-call, or a class whose
   first statement has no C form.  The two tail-loop classes are named by their exact printed
   class rather than by a prefix, and the four one-trip fuel idioms are deliberately NOT in
   the debt set, because §6.3 says their step binder never calls back and JPL.6 must not read
   that as recursion.  The agreement between this predicate and §6.4's rule is asserted below
   as `debt_unaccounted`, not assumed: if the two ever disagree, the census refuses. *)
let shape_debt schemas n =
  let cls = schema_class schemas n in
  let self = !((Hashtbl.find closure n).self) in
  self > 0
  || cls = "fuel tail loop"
  || cls = "structural tail loop"
  || starts cls "BOUNDED FOLD"
  || starts cls "BLOCKED"

(* What the ABI already decided about a variable-classified row: the closed instances §6.3
   rendered from the CALL SITES, which are the artifact's answer to a signature the interface
   left polymorphic.  A row that is pool-free "because a variable is unresolved" and has a
   closed instance at `jpl_text_list` is not free in the sense the slice order cares about —
   the cell type exists, in sh_run_jpl_abi.h, and only this walk failed to see it. *)
let instance_pools binding abi_rows =
  let rows = List.filter (fun (r : abi_row) -> r.a_binding = binding) abi_rows in
  let pools =
    List.concat_map
      (fun (r : abi_row) ->
        List.fold_left (fun a p -> sig_pools a p) (sig_pools [] r.a_result) r.a_params)
      rows
  in
  ( List.length rows,
    List.sort_uniq String.compare (List.map fst pools) )

let print_debts schemas abi_rows rows =
  section "THE SECOND DEBT: WHAT AN OWED ROW ALSO TOUCHES (JPL.md §6.5)";
  Printf.printf "  A row has ONE verdict because §6.4's rules run in dependency order and the first\n\
                \  match owns it.  A row can still owe TWO debts: §6.3's shape and §6.2/decision 3's\n\
                \  representation.  The two columns below are the readings the renderability trial\n\
                \  already consults, asked of every member rather than only of the one that won — so\n\
                \  this section cannot claim a pool the trial declined to look at, and it changes no\n\
                \  verdict.\n";
  let pool_names s = List.sort_uniq String.compare (List.map fst s.so_pools) in
  let free_as s =
    if s.so_pools <> [] then ""
    else if s.so_opaque <> [] then "opaque"
    else if s.so_open > 0 then "var"
    else "scalar"
  in
  let unaccounted = ref ([] : (string * string) list) in
  Printf.printf "\n  %-20s %-21s %-7s %-5s %-9s %s\n" "binding" "§6.4 verdict" "§6.3" "pool"
    "free as" "pools the walk sees, or why it sees none";
  List.iter
    (fun (r : verdict) ->
      let s = sight_of r.v_name in
      let shape = shape_debt schemas r.v_name || starts r.v_reason "its calls never settled" in
      let pooled = s.so_pools <> [] in
      let why = free_as s in
      let note =
        if pooled then String.concat ", " (pool_names s)
        else if why = "opaque" then
          Printf.sprintf "no cell — %s (a declared type whose fields this walk does not enter)"
            (String.concat ", " (List.sort_uniq String.compare s.so_opaque))
        else if why = "var" then
          Printf.sprintf "no cell — %d position(s) whose type the interface has not decided"
            s.so_open
        else if why = "scalar" then "no cell — every position is nat/bool/unit"
        else "(a DATA/ALIAS/RENDER row: no debt of either kind)"
      in
      (* The consistency assertion of §6.5: a verdict must be EXPLAINED by the debts on its own\n
         row.  A member refused for a pool the walk cannot find, or refused while owing nothing,\n\
         would mean §6.4's rule order is not the dependency order the report claims. *)
      let bad what = unaccounted := (r.v_name, what) :: !unaccounted in
      (match r.v_verdict with
       | "OWED-REPRESENTATION" ->
           if not pooled then
             bad "verdicted OWED-REPRESENTATION with no pool in its signature or its sites"
       | "OWED-SCHEMA" ->
           if not shape && not pooled then
             bad "verdicted OWED-SCHEMA while owing neither debt this section measures"
       | _ ->
           if pooled || shape then
             bad
               (Printf.sprintf "verdicted %s while %s" r.v_verdict
                  (if pooled then "touching a pool the trial never consulted"
                   else "carrying a §6.3 shape the rule order should have caught first")));
      Printf.printf "  %-20s %-21s %-7s %-5s %-9s %s\n" r.v_name r.v_verdict
        (if shape then "yes" else "no")
        (if pooled then "yes" else "no")
        (if why = "" then "-" else why) note)
    rows;
  let refused =
    List.filter
      (fun (r : verdict) ->
        r.v_verdict = "OWED-SCHEMA" || r.v_verdict = "OWED-CONSTRUCT"
        || r.v_verdict = "OWED-REPRESENTATION")
      rows
  in
  let schema_rows = List.filter (fun (r : verdict) -> r.v_verdict = "OWED-SCHEMA") rows in
  let pools_of_verdict vs =
    List.filter (fun (r : verdict) -> (sight_of r.v_name).so_pools <> []) vs
  in
  let with_pool = pools_of_verdict schema_rows in
  let free = List.filter (fun (r : verdict) -> (sight_of r.v_name).so_pools = []) schema_rows in
  let by_reason k =
    List.filter
      (fun (r : verdict) ->
        let s = sight_of r.v_name in
        s.so_pools = [] && free_as s = k)
      free
  in
  let var_rows = by_reason "var" in
  let opaque_rows = by_reason "opaque" in
  let scalar_rows = by_reason "scalar" in
  let construct_rows =
    List.filter (fun (r : verdict) -> r.v_verdict = "OWED-CONSTRUCT") rows
  in
  let refused_pool = pools_of_verdict refused in
  (* BOTH debts, not "a refused row with a pool": an OWED-REPRESENTATION row carries the pool
     and no shape (§6.4's order makes the two sets disjoint by construction), so this count is
     the schema set's overlap and nothing else — the wider number is printed with it. *)
  let dual =
    List.filter
      (fun (r : verdict) ->
        (shape_debt schemas r.v_name || starts r.v_reason "its calls never settled")
        && (sight_of r.v_name).so_pools <> [])
      refused
  in
  let inst_pooled =
    List.filter
      (fun (r : verdict) -> snd (instance_pools r.v_name abi_rows) <> [])
      var_rows
  in
  Printf.printf "\n  THE SHAPE SET, SPLIT BY ITS SECOND DEBT (%d OWED-SCHEMA rows)\n"
    (List.length schema_rows);
  List.iter
    (fun (k, v, what) ->
      mark k (List.length v);
      Printf.printf "  %-38s %4d   %s\n" k (List.length v) what)
    [ ("owed_schema_also_pool", with_pool,
       "a §6.3 shape AND a pool: the loop form alone renders nothing");
      ("owed_schema_pool_free", free,
       "no pool THIS WALK can see — read the reason rows below, never this number, as freedom");
      ("owed_schema_pool_free_var", var_rows,
       "a position is still a TYPE VARIABLE, so the interface never decided the cell");
      ("owed_schema_pool_free_opaque", opaque_rows,
       "a position is a declared record/variant whose fields the walk does not enter");
      ("owed_schema_pool_free_scalar", scalar_rows,
       "every position is nat/bool/unit: pool-free in the sense ii-b-3 could use today");
      ("owed_construct_also_pool", pools_of_verdict construct_rows,
       "an OWED-CONSTRUCT row that also touches a pool: 0 is the §6.4 rule order holding, since\n\
        \     the trial consults pools BEFORE it consults its licensed set");
      ("dual_debt_rows", dual,
       "rows carrying BOTH debts, counted over every refused verdict");
      ("owed_schema_free_var_pooled_instance", inst_pooled,
       "variable-classified schema rows whose closed instance in sh_run_jpl_abi.h IS pooled") ];
  Printf.printf "  %-38s %4d   %s\n" "rows (both columns, every member)" (List.length rows)
    "the same 47 §6.4 partitions, read twice instead of once";
  List.iter
    (fun (r : verdict) ->
      Printf.printf "    FINDING %-18s %s — %s\n" r.v_name r.v_verdict
        (String.concat ", " (pool_names (sight_of r.v_name))))
    (pools_of_verdict construct_rows);
  Printf.printf "\n  THE DUAL ROWS, ONE LINE EACH (%d of the %d refused rows that touch a pool;\n                \  the other %d are the §6.4 OWED-REPRESENTATION rows, which carry the pool and\n                \  no shape — %d + %d + %d = %d is asserted by 2f's check 5)\n"
    (List.length dual) (List.length refused_pool)
    (List.length refused_pool - List.length dual)
    (List.length with_pool) (List.length (pools_of_verdict construct_rows))
    (List.length refused_pool - List.length dual - List.length (pools_of_verdict construct_rows))
    (List.length refused_pool);
  List.iter
    (fun (r : verdict) ->
      Printf.printf "    %-18s %-38s %-21s %s\n" r.v_name r.v_class r.v_verdict
        (String.concat ", " (pool_names (sight_of r.v_name))))
    dual;
  (* The cross-check §6.5 commissions: a variable is not a freedom when the call sites have\n
     already closed it.  Printed per row, because which rows is the finding. *)
  Printf.printf "\n  WHAT THE ABI ALREADY DECIDED ABOUT THE VARIABLE-CLASSIFIED ROWS\n";
  Printf.printf "  A row above whose signature carries a type variable is pool-free only while the\n\
                \  interface is the authority: §6.3's instance set closes the same variable at the\n\
                \  CALL SITES, and sh_run_jpl_abi.h is the artifact's answer.  This is one\n\
                \  measurement read against another, not a third claim about the bytes.\n";
  List.iter
    (fun (r : verdict) ->
      let n, pools = instance_pools r.v_name abi_rows in
      Printf.printf "    %-18s %d closed instance(s) — %s\n" r.v_name n
        (if pools <> [] then "POOLED as " ^ String.concat ", " pools
         else if n = 0 then "the shipped closure never closed it (§6.3's open set)"
         else "no pool in any closed instance"))
    var_rows;
  Printf.printf "\n  THE READING THIS COLUMN EXISTS FOR: %d of the %d §6.3-shape rows carry the\n\
                \  representation debt as well; %d more are pool-free only because a TYPE VARIABLE\n\
                \  is unresolved (and %d of those have a closed instance that IS pooled, so the\n\
                \  cell type exists and only this walk could not see it); %d are pool-free because\n\
                \  the walk stops at a declared type's FIELDS; %d are pool-free in the plain sense.\n\
                \  A `while' statement form therefore renders bodies only where that last number is\n\
                \  nonzero, and §6.5 puts ii-b-1 and ii-b-2 before ii-b-3 and ii-b-4 because this\n\
                \  measures it, not because the plan prefers it.\n"
    (List.length with_pool) (List.length schema_rows) (List.length var_rows)
    (List.length inst_pooled) (List.length opaque_rows) (List.length scalar_rows);
  if scalar_rows <> [] then begin
    Printf.printf "\n  SLICE FINDING: %d schema row(s) really are pool-free, so ii-b-3/ii-b-4 has\n\
                  \  work that does not wait on the allocator:\n"
      (List.length scalar_rows);
    List.iter (fun (r : verdict) -> Printf.printf "    %-18s %s\n" r.v_name r.v_class) scalar_rows
  end;
  (* The floor wording, printed rather than left to the reader: the walk stops at a field\n
     boundary, so a count of pool-free rows is a FLOOR, and 2f's check 3 already sees the\n\
     evidence — a frame pool declared by §6.2's decision 1 and demanded by nothing. *)
  Printf.printf "\n  A FLOOR, NOT A CEILING: this walk reads aliases, lists, options, pairs and\n\
                \  arrows, and stops at a declared record or variant.  That is why 2e's header\n\
                \  declares jpl_frame_pool (§6.2's decision 1) while the census demands no frame\n\
                \  NODE cell from anything: the machine's stack reaches the roots through cfg and\n\
                \  cstate, behind a field boundary.  Every pool-free count above is a FLOOR.\n\
                \  Entering record fields would move rows between §6.4's verdicts, so it is a\n\
                \  slice of its own and not something this section does quietly.\n";
  let bad = List.rev !unaccounted in
  mark "debt_unaccounted" (List.length bad);
  Printf.printf "  %-38s %4d   %s\n" "debt_unaccounted" (List.length bad)
    "a row whose debts do not explain its verdict; must be 0";
  if bad <> [] then begin
    Printf.printf "\nLOWER REFUSAL: §6.4's verdicts and §6.5's debts disagree for %d member(s), so\n\
                  \  either the rule order is not the dependency order this report claims, or a\n\
                  \  refusal printed here has no measurement behind it:\n"
      (List.length bad);
    List.iter (fun (n, w) -> Printf.printf "    %-18s %s\n" n w) bad;
    exit 1
  end;
  Printf.printf "\nDEBTS CONSISTENT: every verdict in the partition is explained by the debts\n\
                \  measured on the same row — %d refused members, %d of them carrying both.\n"
    (List.length refused) (List.length dual)
(* ───────────────────────────── 10. main ────────────────────────────────── *)

(* The gate reads keys, not prose.  Every value below was marked by the section that
   measured it, so the SUMMARY cannot drift away from the report above it — and a key
   whose owner never ran is a failure, not a zero. *)
let summary_keys =
  [ ("members", "the shipped closure");
    ("recursive", "of those, defined by fixpoint");
    ("polymorphic_bindings", "whose interface carries a type variable");
    ("instance_uses", "uses of a polymorphic binding, counted at the call sites");
    ("instances_closed", "distinct closed instances: one C function each");
    ("instances_open", "distinct instances still carrying a variable: nothing to emit");
    ("function_value_sites", "lambda values this walk positioned");
    ("function_value_sites_unnamed", "in a position no rule covers, so a function pointer would be needed");
    ("allocation_sites", "expression sites that build a value");
    ("open_allocation_sites", "of those, still carrying a type variable");
    ("pools_demanded", "pool arrays the closure needs");
    ("bound_checks", "comparisons against a locked cap");
    ("caps_handed_to_a_call", "cap constants handed to a call as an argument");
    ("fuel_tail_loops", "bindings whose schema is a fuel loop");
    ("fuel_idiom_one_trip", "fuel idioms whose step never calls back, so they run one trip");
    ("non_tail_rewrites", "bindings a while cannot express");
    ("unknown_site_classes", "expression classes this census could not type");
    ("self_reference_mismatches", "where two readings of the same bytes disagree");
    ("abi_instances", "closed instances the ABI section rendered");
    ("abi_prototypes", "of those, ones with a C type for every place");
    ("abi_refused_no_c_type", "closed instances no C prototype can name (D-60411)");
    ("abi_bodies_expressible", "prototypes whose binding has a C form under §6.3");
    ("abi_bodies_owed", "prototypes whose body waits on a model-side rewrite");
    ("abi_blocked_outside_fold_set", "a refusal §6.3 assigns to no owner; must be 0");
    ("data_bindings", "members that are a folded constant the header already names");
    ("alias_bindings", "members whose body IS an operator, so no function is emitted");
    ("bodies_renderable", "members the §6.4 render trial accepted, and emitted as C");
    ("owed_representation", "members that build or read a pooled cell");
    ("owed_schema", "members whose §6.3 shape has no statement form yet");
    ("owed_construct", "members the renderer refused, in the refusal's own words");
    ("bodies_citing_data", "rendered bodies that cite a data constant by its header macro");
    ("render_unaccounted", "a member that received no verdict; must be 0");
    ("sweep_domain", "the last index both generated drivers sweep (the artifact's MAX_FUEL)");
    ("bodies_swept_exhaustive", "rendered bodies whose whole bounded domain the sweep covers");
    ("bodies_swept_diagonal", "rendered bodies the sweep only exercises along one diagonal");
    ("owed_schema_also_pool", "members owing a §6.3 shape AND a pool (§6.5's dual debt)");
    ("owed_schema_pool_free", "members owing a §6.3 shape and no pool THIS WALK sees");
    ("owed_schema_pool_free_var", "of those: a position the interface left a type variable");
    ("owed_schema_pool_free_opaque", "of those: a position behind a declared type's fields");
    ("owed_schema_pool_free_scalar", "of those: pool-free in the sense a loop form could use today");
    ("owed_schema_free_var_pooled_instance",
     "of those, rows whose closed instance in the ABI header IS pooled");
    ("owed_construct_also_pool", "members refused for a construct that also touch a pool; must be 0");
    ("dual_debt_rows", "refused members carrying both the shape debt and the pool debt");
    ("debt_unaccounted", "a verdict its own row's debts do not explain; must be 0") ]

let print_summary () =
  section "SUMMARY (one key per line, for the gate to read instead of formatted prose)";
  Printf.printf "  Every value below was marked by the section that measured it; a missing key is\n\
                \  reported as a failure, because an absent measurement is not a zero.\n";
  let missing =
    List.filter_map
      (fun (k, what) ->
        match Hashtbl.find_opt tally k with
        | Some v ->
            Printf.printf "  %-28s %-6d  %s\n" k v what;
            None
        | None -> Some (k, what))
      summary_keys
  in
  List.iter (fun (k, what) -> Printf.printf "  %-28s MISSING   %s\n" k what) missing;
  if missing <> [] then begin
    Printf.printf "\nLOWER REFUSAL: %d summary key(s) were never marked, so the census is\n\
                  \  incomplete and its counts must not be read as measurements.\n"
      (List.length missing);
    exit 1
  end

type row =
  { r_schema : schema;
    r_inferred : lt;
    r_declared : lt }

let main ml mli roots abi_out bodies_out diff_out =
  src_path := ml;
  let items = Parse.implementation (Lexing.from_channel (open_in ml)) in
  add_struct "" items;
  add_sig (Parse.interface (Lexing.from_channel (open_in mli)));
  build_indices ();
  build_ops ();
  (* the artifact's OWN cap table, read the same way the representation layer reads it, so
     the census reports the numbers the header was built from instead of a second copy *)
  caps_r := Some (read_caps ());
  Printf.printf "INPUT      %s\n           %s\n" ml mli;
  Printf.printf "artifact   %d bindings, %d typed signatures, %d type declarations\n"
    (Hashtbl.length binds) (Hashtbl.length vals) (Hashtbl.length tydecls);
  reach roots;
  let members = closure_members () in
  let recs = List.filter (fun n -> (Hashtbl.find binds n).b_rec) members in
  Printf.printf "roots      %s  ->  %d bindings, %d recursive\n" (String.concat ", " roots)
    (List.length members) (List.length recs);
  mark "members" (List.length members);
  mark "recursive" (List.length recs);

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

  (* Classified FIRST: whether a call hands a cap to a loop is a question about the
     callee's shape, and the shape is read off the text, not off inference. *)
  let schemas = List.map (fun n -> classify n (Hashtbl.find binds n).b_body (Hashtbl.find closure n)) members in
  fuel_loops :=
    List.filter_map (fun s -> if starts s.s_class "fuel" then Some s.s_name else None) schemas;
  let rows =
    List.map2
      (fun s n ->
        (* the binding being inferred is also the binding every site recorded below is
           attributed to, so it has to be set here and not only during classification *)
        cur_name := n;
        let b = Hashtbl.find binds n in
        if not (Hashtbl.mem vals n) then begin
          bump unknowns "a closure member with no signature in the interface";
          { r_schema = s; r_inferred = L_unk "no signature"; r_declared = L_unk "no signature" }
        end
        else begin
          let env = Hashtbl.create 16 in
          (* FRESHENED, not used as written: the declared `'a1` is a variable of the
             interface, and pushing it into a body unbinds it in the store, so every
             polymorphic binding would share one entry and the last binding inferred would
             name all of them.  One freshening per binding is what makes an instance
             countable — see the note above MONOMORPHIZATION. *)
          let d = instantiate (decl_full n) in
          (* a contradiction names the binding it was found under: the refusal is a
             measurement of one body, and without the name it is not actionable *)
          let r =
            try with_use LkDef (fun () -> te env (Some d) b.b_body) with
            | Conflict m -> raise (Conflict (n ^ ": " ^ m))
          in
          { r_schema = s; r_inferred = r; r_declared = d }
        end)
      schemas
      members
  in
  let blocked = print_schema (List.map (fun r -> r.r_schema) rows) in
  print_instances members;
  (* the closed set rendered as C, and the refusals that rendering makes visible *)
  let abi_rows = print_abi members schemas in
  (* the same rendering question, asked of every member rather than only of the R8 instances *)
  let render_rows = print_render members schemas in
  (* the same rows, read a second time for the debt §6.4's rule order suppresses (§6.5) *)
  print_debts schemas abi_rows render_rows;

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
  mark "fuel_tail_loops"
    (List.length (List.filter (fun s -> s.s_class = "fuel tail loop") schemas));
  mark "fuel_idiom_one_trip"
    (List.length
       (List.filter (fun s -> s.s_class = "fuel idiom, one trip (no self-call)") schemas));
  mark "non_tail_rewrites"
    (List.length (List.filter (fun s -> s.s_class = "BOUNDED FOLD (non-tail)") schemas));
  mark "unknown_site_classes" (Hashtbl.length unknowns);

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
  mark "self_reference_mismatches" (List.length mism);
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
    (Hashtbl.length unknowns);
  print_summary ();
  (* The header, the bodies and the two drivers are written only on a complete run: a census
     that refused would otherwise leave a plausible-looking ABI, plausible-looking C and a
     plausible-looking differential next to a measurement that does not support them. *)
  (match abi_out with
   | Some p -> write_abi p abi_rows
   | None -> ());
  (match bodies_out with
   | Some p -> write_bodies p render_rows
   | None -> ());
  (match diff_out with
   | Some (c_path, ml_path) ->
       write_diff_c c_path render_rows;
       write_diff_ml ml_path render_rows
   | None -> ())

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [ ml; mli ] ->
      (try main ml mli default_roots None None None with
       | Conflict m -> fail ("the artifact contradicts its own interface: " ^ m))
  | [ ml; mli; rs ] ->
      (try main ml mli (split_commas rs) None None None with
       | Conflict m -> fail ("the artifact contradicts its own interface: " ^ m))
  | [ ml; mli; rs; abi ] ->
      (try main ml mli (split_commas rs) (Some abi) None None with
       | Conflict m -> fail ("the artifact contradicts its own interface: " ^ m))
  | [ ml; mli; rs; abi; bodies ] ->
      (try main ml mli (split_commas rs) (Some abi) (Some bodies) None with
       | Conflict m -> fail ("the artifact contradicts its own interface: " ^ m))
  | [ ml; mli; rs; abi; bodies; diff_c; diff_ml ] ->
      (try main ml mli (split_commas rs) (Some abi) (Some bodies) (Some (diff_c, diff_ml)) with
       | Conflict m -> fail ("the artifact contradicts its own interface: " ^ m))
  | _ ->
      fail "usage: jpl_lower <ml> <mli> [comma-separated-roots] \
            [path-for-the-abi-header] [path-for-the-rendered-bodies] \
            [path-for-the-c-differential-driver] [path-for-the-ocaml-differential-driver]"
