(* jpl_front.ml — the JPL.5 emitter's FRONT END (step 5-B.1): the report and
 * the subset verdict, over the shared reader in jpl_ast.ml.  See that file's
 * header for what the reading covers; the gate wires this file's EXIT STATUS
 * (0 = the shipped closure is inside the subset, 1 = a violation is named,
 * 2 = the tool could not run) and keeps a byte-checked copy of the report as
 * verify/c/closure.txt. *)

open Jpl_ast
open Parsetree
open Asttypes
open Longident
(* ─────────────────────── 6. reporting and the subset verdict ────────────── *)

let sortl h =
  List.sort (fun (a, x) (b, y) ->
    if y <> x then compare y x else String.compare a b)
    (Hashtbl.fold (fun k v a -> (k, v) :: a) h [])

let section title = Printf.printf "\n==== %s ====\n" title

let print_kv title l =
  section title;
  if l = [] then print_endline "  (none)"
  else List.iter (fun (k, v) -> Printf.printf "  %-34s %d\n" k v) l

(* The roots, their CLI parser and the default live in the shared reader
   (jpl_ast.ml §7), because the emitter takes exactly the same argument. *)
let main ml mli roots =
  let items = Parse.implementation (Lexing.from_channel (open_in ml)) in
  add_struct "" items;
  add_sig (Parse.interface (Lexing.from_channel (open_in mli)));
  Printf.printf "INPUT      %s\n           %s\n" ml mli;
  Printf.printf "artifact   %d bindings, %d typed signatures, %d type declarations\n"
    (Hashtbl.length binds) (Hashtbl.length vals) (Hashtbl.length tydecls);
  reach roots;

  let members = closure_members () in
  section "CLOSURE MEMBERS (artifact order)";
  Printf.printf "  %-20s %-5s %-4s %-10s %-5s %s\n" "name" "arity" "rec" "nat-match" "self" "signature";
  List.iter
    (fun n ->
      let b = Hashtbl.find binds n in
      let m = Hashtbl.find closure n in
      let v = try cty (Hashtbl.find vals n) with Not_found -> "(not in interface)" in
      Printf.printf "  %-20s %-5d %-4s %-10d %-5d %s\n" n b.b_arity
        (if b.b_rec then "yes" else "no") !(m.fuel) !(m.self) v)
    members;
  let recs = List.filter (fun n -> (Hashtbl.find binds n).b_rec) members in
  Printf.printf "\nroots      %s  ->  %d bindings, %d recursive\n"
    (String.concat ", " roots)
    (List.length members) (List.length recs);
  Printf.printf "           mutual let-rec groups in the whole file: %d\n" !mutual_groups;

  let e_all = Hashtbl.create 32 and p_all = Hashtbl.create 32
  and a_all = Hashtbl.create 40 and c_all = Hashtbl.create 80 in
  Hashtbl.iter
    (fun _ m ->
      Hashtbl.iter (fun k v -> add e_all k v) m.e_cnt;
      Hashtbl.iter (fun k v -> add p_all k v) m.p_cnt;
      Hashtbl.iter (fun k v -> add a_all k v) m.alloc;
      Hashtbl.iter (fun k v -> add c_all k v) m.ctors)
    closure;
  print_kv "EXPRESSION CLASSES IN THE CLOSURE" (sortl e_all);
  print_kv "PATTERN CLASSES IN THE CLOSURE" (sortl p_all);

  let bad_e = List.filter (fun (k, _) -> not (List.mem k supported_expr)) (sortl e_all) in
  let bad_p = List.filter (fun (k, _) -> not (List.mem k supported_pat)) (sortl p_all) in
  let mutual = List.filter (fun n -> (Hashtbl.find binds n).b_mutual) members in
  section "SUBSET VERDICT";
  Printf.printf "  emitter supports expressions: %s\n" (String.concat ", " supported_expr);
  Printf.printf "  emitter supports patterns:    %s\n" (String.concat ", " supported_pat);
  List.iter (fun (k, v) -> Printf.printf "  OFF-SUBSET expression  %-22s %d\n" k v) bad_e;
  List.iter (fun (k, v) -> Printf.printf "  OFF-SUBSET pattern     %-22s %d\n" k v) bad_p;
  if mutual <> [] then
    Printf.printf "  OFF-SUBSET mutual fixpoint: %s\n" (String.concat ", " mutual);
  let ok = bad_e = [] && bad_p = [] && mutual = [] in
  Printf.printf "\n%s\n"
    (if ok then "SUBSET OK: the shipped closure is inside the emitter's subset."
     else "SUBSET VIOLATION: the emitter must not run on this artifact.");

  print_kv "ALLOCATION SITES IN THE CLOSURE (sizes the memory-model decision)"
    (sortl a_all);
  print_kv "VALUE CONSTRUCTORS USED IN THE CLOSURE" (sortl c_all);

  (* the type vocabulary: every type named by a closure signature, and the
     declarations reachable from it.  Computed in the shared reader (jpl_ast.ml
     §6), because the emitter has to lay out exactly this domain. *)
  type_vocab members;
  section "TYPE VOCABULARY THE CLOSURE NEEDS (the layout table's domain)";
  Hashtbl.iter
    (fun k _ ->
      let d = Hashtbl.find tydecls k in
      let kind =
        match d.ptype_kind with
        | Ptype_variant cs ->
            "variant of "
            ^ String.concat ", "
                (List.map
                   (fun (c : constructor_declaration) ->
                     let n =
                       match c.pcd_args with
                       | Pcstr_tuple l -> List.length l
                       | Pcstr_record l -> List.length l
                     in
                     c.pcd_name.txt ^ (if n = 0 then "" else "/" ^ string_of_int n))
                   cs)
        | Ptype_record ls ->
            "record of "
            ^ String.concat ", "
                (List.map (fun (l : label_declaration) -> l.pld_name.txt ^ ":" ^ cty l.pld_type) ls)
        | Ptype_abstract ->
            "abstract"
            ^ (match d.ptype_manifest with Some t -> " = " ^ cty t | None -> "")
        | Ptype_open -> "open"
        | Ptype_external _ -> "external"
      in
      Printf.printf "  %-12s %s\n" k kind)
    vocab;
  Printf.printf "  %-12s %s\n" "(builtins)"
    (String.concat ", " (List.map (fun (k, v) -> k ^ " x" ^ string_of_int v) (sortl builtins)));
  ok

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [ ml; mli ] -> if main ml mli default_roots then exit 0 else exit 1
  | [ ml; mli; rs ] -> if main ml mli (split_commas rs) then exit 0 else exit 1
  | _ -> fail "usage: jpl_front <ml> <mli> [comma-separated-roots]"
