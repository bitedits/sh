(* jpl_emit.ml — JPL.5-B.2: the C99 REPRESENTATION LAYER, derived from the artifact.

 * Second consumer of the shared reader (jpl_ast.ml), whose own header enumerates its three.
 * The reporter reads the shipped
 * closure and says whether it is inside the emitter's subset; this tool reads the
 * SAME bindings plus the artifact's cap table and WRITES the C type layer that
 * closure must be lowered into — typedefs, capacities, pool declarations and
 * prototypes.  It lowers no code: no expression, no control flow, no body.  What it
 * settles is JPL.md §9.2 decision 3's open question, what a value of each type in
 * the artifact's vocabulary OCCUPIES in C99, and it settles it by derivation:
 *
 *   - every capacity comes from the artifact's own `jpl_caps_table` (sh_jpl.v §1.1,
 *     sub-step 5-B.2a), constant-folded out of the extracted term.  This tool holds
 *     no capacity number of its own.
 *   - every type laid out comes from the artifact's own `.mli`, restricted to the
 *     vocabulary the shipped closure reaches — the same reachability the reporter
 *     prints, shared through jpl_ast.ml §6 so the two cannot compute two domains.
 *   - the encoding of each type follows ONE rule set (§4 below), applied by
 *     construction, so any line of the header re-derives from one line of the
 *     artifact.
 *   - every emitted struct is followed by a compile-time sizeof check, so the byte
 *     counts computed here are verified by the C compiler instead of trusted.
 *
 * Three things are deliberately NOT derived, and each is numbered in the report so
 * it cannot be mistaken for a proof: (1) which declared types are POOLED — a type's
 * shape does not say how many of itself are live at once, only the model's cap
 * comments do; (2) which cap sizes which list pool; (3) the headroom factor on a
 * pooled capacity, which is an allocation-bound question JPL.5-B.3 must answer.
 *
 * What it REFUTES, and therefore reports instead of emitting: JPL.md §6's claim
 * that the live set is bounded by the caps fails for the WORD slab.  The caps bound
 * NODES and LIST LENGTHS; words are reachable from nodes (Ext, For, Case patterns),
 * so live words are bounded only by a PRODUCT of caps, and no entry of the LOCKED
 * table is the capacity of a word.  Sizing that pool needs a new capacity in the
 * model, not a number invented here, so the slab is declared, left unsized, and
 * listed under "WHAT THIS LAYER COULD NOT SIZE" — with the range the existing caps
 * do imply.  The report's FINDINGS list also carries the second refutation: §6's
 * "no monomorphization" fails, because the closure reaches polymorphic helpers.

 * Usage: jpl_emit <ml> <mli> <out.h> [comma-separated-roots]
 * Exit codes: 0 the header was written; 2 the artifact is outside what this layer
 *             can represent, or the tool could not run (the violation is named).
 *             A PENDING finding is not a failure: it is this layer reporting a
 *             question it must not answer by invention. *)
open Jpl_ast
open Parsetree
open Asttypes
open Longident

(* ───────── 1-3. the type view, the constant folder, the cap table ──────────

   Those live in the SHARED READER (jpl_ast.ml §8-§10), not here: the layout
   emitter, the subset reporter and the 5-B.3 lowering census must not compute
   three readings of one `.mli`, and `of_ct` refusing a type outside the
   artifact's vocabulary is a decision all three need at once.  So this file
   consumes `lt`, `of_ct`, `tn`, `show_lt`, `sig_of`, `param_names`,
   `single_word`, `has_var`, `w4`, the folder (`fold`, `try_fold`) and the caps
   (`caps`, `cap_fields`, `caps_of`, `read_caps`, `c ()`) from there, and applies
   the rule set below. *)
(* ───────────── 4. the layout rule set, and the registry that applies it ──── *)

(* One rule set, applied by construction:
     R1 nat/bool/unit    -> uint32_t.  Every scalar is one word, so every struct
                            size is a SUM of 4s and each emitted sizeof check can
                            state an exact byte count.
     R2 text             -> jpl_text, a length-carrying fixed array (the model's
                            bword shape), referenced ONLY through a jpl_wref index
                            into the word pool.  Codes stay uint32_t, NOT uint8_t:
                            sh_concrete.v §1 says each code is "intended to be
                            < 256", which is an intent and not a lemma, and
                            JPL-conformant C may not rest on an intent.  The report
                            carries the cost of that honesty.
     R3 any other list   -> cons-cell pool: the element inline in the cell plus a
                            next index; the list VALUE is one index (0 = JPL_NIL).
     R4 option / bres    -> by-value struct: tag + payload (BLimit is tag 1, per the
                            model's saturate-to-error shape).
     R5 pair             -> by-value struct: two fields in the artifact's order.
     R6 declared RECORD  -> by-value struct, fields in the .mli's order.
     R7 declared VARIANT -> three cases, in this order:
                             every ctor nullary   -> uint32 enum + #defines;
                             pooled (decision 1)  -> a NODE: tag + positional
                                  single-word slots, checked against the
                                  declarations.  One cell per node, no union (JPL
                                  forbids them), and the cmd -> cmd cycle is broken
                                  because a slot holds an index, not a value;
                             otherwise            -> a FAT struct: tag plus one
                                  named payload struct per constructor, so again no
                                  union and an exact, checkable size.
     R8 a signature mentioning a type variable is NOT emitted: a C function needs a
        concrete instance per call site, which is measured and reported.

   No rule inspects a type NAME except to ask the artifact for its declaration. *)

(* Hand-written decision 1: which declared types are POOLED.  A type's shape cannot
   say how many of itself are live; the model's cap comments can — sh_jpl.v §1 calls
   MAX_CMD the "node-pool capacity for one lowered cmd tree" and MAX_STACK the
   "explicit machine stack frames".  A type absent from this list is laid out by
   value, so it needs no capacity and no pool.  The two halves of this decision are
   checked against each other: a name in pooled_types with no capacity here is a
   hard refusal, because the alternative is that a declared-pooled type silently
   falls through to a by-value layout. *)
let pooled_types = [ "cmd"; "frame" ]

(* The capacity lookup for decision 1: (cells, the cap macro it came from, and why
   that cap is the right one), sized from the artifact's own cap table. *)
let pool_cap c nm =
  if nm = "cmd" then
    Some (c.c_cmd, "JPL_MAX_CMD", "nodes of one lowered cmd tree (sh_jpl.v §1 MAX_CMD)")
  else if nm = "frame" then
    Some (c.c_stack, "JPL_MAX_STACK", "frames of the explicit machine stack (sh_jpl.v §1 MAX_STACK)")
  else None

(* Hand-written decision 2: which cap sizes which list pool, taken from the model's
   own bounds — sh_jpl.v §5's wf_benv proves the env pair list <= MAX_ENV and the
   artifact's only `(text * text) list` is cstate.cenv; `stack` IS frame list and
   MAX_STACK counts frames; MAX_LIST is §1's cap for "any intermediate list". *)
let list_cap c el =
  match el with
  | L_pair (L_word, L_word) ->
      (c.c_env, "JPL_MAX_ENV", "the environment's pair list (sh_jpl.v §5 wf_benv)")
  | L_named "frame" -> (c.c_stack, "JPL_MAX_STACK", "the machine stack = frame list")
  | _ -> (c.c_list, "JPL_MAX_LIST", "an intermediate list (sh_jpl.v §1 MAX_LIST)")

(* Hand-written decision 3: headroom.  A pool sized exactly to its cap holds a LIVE
   set of that size; a step boundary or a mutation that builds its replacement
   before releasing the original needs one more cell per live cell.  2 is the
   smallest factor that survives copy-then-swap at full occupancy, which is what
   JPL.md §6's copying-collection commitment implies.  JPL.5-B.3 must either prove
   the live-set bound and take the factor to 1, or prove 2 is needed; stating it
   here is what keeps it out of an array dimension unnoticed. *)
let headroom = 2

(* Output regions, assembled into the header in this order. *)
let tags_b = Buffer.create 2048
let types_b = Buffer.create 8192
let pools_b = Buffer.create 4096
let protos_b = Buffer.create 4096

let emit b fmt = Printf.ksprintf (fun s -> Buffer.add_string b s) fmt

(* Registry: memo maps a short type name to (C name, bytes); defined stops the same
   typedef being emitted twice; in_progress catches a by-value cycle, which would
   mean the rule set needs a pool and this tool must say so instead of looping. *)
let memo : (string, string * int) Hashtbl.t = Hashtbl.create 32
let defined = Hashtbl.create 32
let in_progress = Hashtbl.create 8

type row = { name : string; kind : string; size : int; fields : string }

let rows : (string, row) Hashtbl.t = Hashtbl.create 32
let row_order : string list ref = ref []

type pool =
  { p_elem : string; p_arr : string; p_count : int option; p_from : string;
    p_why : string }

let pools : pool list ref = ref []
let findings : string list ref = ref []

(* Which rows got a `sizeof` assertion of their own, recorded by sizeof_check itself, so
   the report's count of checked vs family-covered rows is measured, not hand-typed. *)
let checked : string list ref = ref []

let note fmt = Printf.ksprintf (fun s -> findings := s :: !findings) fmt

let size_of_name n = try (Hashtbl.find rows n).size with Not_found -> 0

(* define: register one C type and emit its lines once.  The sizeof check travels
   with the definition, so a wrong byte count anywhere in this file is a compile
   error in the gate, not a comment. *)
let define name size kind fields lines =
  if not (Hashtbl.mem defined name) then begin
    Hashtbl.replace defined name ();
    List.iter (fun l -> emit types_b "%s\n" l) lines;
    Hashtbl.replace rows name { name; kind; size; fields };
    row_order := name :: !row_order
  end

let sizeof_check name size =
  if not (List.mem name !checked) then checked := name :: !checked;
  Printf.sprintf
    "typedef char jpl_check_%s_is_%d[((sizeof (%s) == %du) ? 1 : -1)];" name size
    name size

(* Every row that gets no check of its own is, by the rules that made it, exactly as
   wide as the word it typedefs (R1 scalars, R3 handles, R7's all-nullary variant).
   Saying that once, as a compiler-checked assertion over those rows, is what lets this
   file claim that NO emitted type's size is unverified. *)
let family_check () =
  let unchecked =
    List.rev
      (List.filter_map
         (fun n ->
           let r = Hashtbl.find rows n in
           if List.mem n !checked then None else Some (r.name, r.size))
         !row_order)
  in
  if unchecked <> [] then begin
    emit types_b "typedef char jpl_check_one_word_families[((%s) ? 1 : -1)];\n"
      (String.concat ") && ("
         (List.map (fun (n, sz) -> Printf.sprintf "sizeof (%s) == %du" n sz)
            unchecked));
    note "%d rows carry no sizeof check of their own and are covered conjunctively by jpl_check_one_word_families: %s"
      (List.length unchecked)
      (String.concat ", " (List.map fst unchecked))
  end

(* ─────────── 5. the layers: each applies one rule and registers itself ───── *)

(* R1 *)
let scalar_layer name comment =
  define name w4 "scalar" "-"
    [ Printf.sprintf "typedef uint32_t %s;   /* %s */" name comment ]

let rec scalars () =
  scalar_layer "jpl_nat"
    "Coq nat after ExtrOcamlNatInt; every value is provably <= JPL_MAX_FUEL, so it cannot wrap";
  (* The width check needs jpl_nat to name, so it lives here rather than with the
     other compile-time assertions, which sit above the type layer. *)
  emit types_b "typedef char jpl_check_word_is_the_declared_width[((8u * sizeof (jpl_nat)) == JPL_MAX_WIDTH) ? 1 : -1];\n";
  scalar_layer "jpl_bool" "OCaml bool: 0 or 1; one word, so no cell needs padding";
  scalar_layer "jpl_unit" "OCaml unit: a value that carries no information";
  scalar_layer "jpl_ref" "pool handle; JPL_NIL is the empty list, index 0 is never allocated";
  List.iter (fun (k, n) -> Hashtbl.replace memo k (n, w4))
    [ ("nat", "jpl_nat"); ("bool", "jpl_bool"); ("unit", "jpl_unit");
      ("ref", "jpl_ref") ];
  emit tags_b "#define JPL_NIL 0u          /* the empty list */\n\
               #define JPL_FALSE 0u\n\
               #define JPL_TRUE 1u\n\
               #define JPL_NONE 0u         /* option tag   */\n\
               #define JPL_SOME 1u         /* option tag   */\n\
               #define JPL_BRES_OK 0u      /* sh_jpl.v §2  */\n\
               #define JPL_BRES_LIMIT 1u   /* saturate-to-error */\n\n"

(* R2 *)
and word_layer () =
  let sz = w4 + w4 * (c ()).c_word in
  define "jpl_wref" w4 "word handle" "jpl_ref"
    [ "typedef jpl_ref jpl_wref;   /* a text VALUE is a word-slab index */" ];
  Hashtbl.replace memo "text" (value_name L_word, w4);
  define "jpl_text" sz "word (pool element)" "len + code[JPL_MAX_WORD]"
    [ "/* text = int list, bounded in LENGTH by MAX_WORD (sh_jpl.v §4's bword shape).";
      "   The codes stay uint32_t: sh_concrete.v §1 only INTENDS each to be < 256, and";
      "   an intent is not a lemma, so narrowing them here would be an unproved claim. */";
      "typedef struct {";
      "  jpl_nat wt_len;";
      "  jpl_nat wt_code[JPL_MAX_WORD];";
      "} jpl_text;";
      sizeof_check "jpl_text" sz ];
  pools :=
    { p_elem = "jpl_text"; p_arr = "jpl_word_pool";
      p_count = Some (headroom * (c ()).c_words);
      p_from = "JPL_MAX_WORDS";
      p_why =
        "sh_jpl.v §1's MAX_WORDS, a sum of the already-locked caps: MAX_STACK cells for\n\
  \    the words a pool-fitting tree holds (§7.1 cmd_fits_words, from cmd_words <= 2*\n\
  \    cmd_count and cmd_fits), a second MAX_STACK for the runtime-expanded copies an\n\
  \    FFor/FCase frame holds (the OWED step-machine invariant \"one live frame per\n\
  \    source node\" — named in §1, not yet proved), 2*MAX_ENV for the environment's\n\
  \    name/value cells (§5 benv_words_le), and 2 per-step temporaries." }
    :: !pools;
  ("jpl_wref", w4)   (* = value_name L_word, which is the rule the ABI renderer shares *)

(* R3 *)
and list_layer e =
  let (en, esz) = require e in
  let k = tn e ^ "_list" in
  let handle = "jpl_" ^ k in
  let cell = handle ^ "_cell" in
  let sz = esz + w4 in
  define handle w4 "list handle" handle
    [ Printf.sprintf "typedef jpl_ref %s;   /* %s list: index of the first cell, or JPL_NIL */"
        handle (show_lt e) ];
  define cell sz "cons cell (pool element)"
    (Printf.sprintf "%s + next" en)
    [ Printf.sprintf "typedef struct {";
      Printf.sprintf "  %s %s_hd;   /* the element, inline in the cell */" en k;
      Printf.sprintf "  jpl_ref %s_next;" k;
      Printf.sprintf "} %s;" cell;
      sizeof_check cell sz ];
  let (cap, macro, why) = list_cap (c ()) e in
  pools :=
    { p_elem = cell; p_arr = "jpl_" ^ k ^ "_pool";
      p_count = Some (headroom * cap); p_from = macro; p_why = why }
    :: !pools;
  (handle, w4)

(* R4 *)
and tagged_layer prefix inner =
  let (in_name, in_sz) = require inner in
  let name = "jpl_" ^ prefix ^ "_" ^ tn inner in
  let sz = w4 + in_sz in
  define name sz "by-value tagged" (prefix ^ " of " ^ in_name)
    [ Printf.sprintf "typedef struct {";
      Printf.sprintf "  jpl_nat %s_tag;   /* %s: JPL_%s / JPL_%s */" prefix
        (show_lt inner)
        (if prefix = "opt" then "NONE" else "BRES_OK")
        (if prefix = "opt" then "SOME" else "BRES_LIMIT");
      Printf.sprintf "  %s %s_val;" in_name prefix;
      Printf.sprintf "} %s;" name;
      sizeof_check name sz ];
  (name, sz)

(* R5 *)
and pair_layer a b =
  let (an, asz) = require a in
  let (bn, bsz) = require b in
  let name = "jpl_pair_" ^ tn a ^ "_" ^ tn b in
  let sz = asz + bsz in
  define name sz "by-value pair" (an ^ " + " ^ bn)
    [ Printf.sprintf "typedef struct {";
      Printf.sprintf "  %s p_fst;   /* %s */" an (tn a);
      Printf.sprintf "  %s p_snd;   /* %s */" bn (tn b);
      Printf.sprintf "} %s;" name;
      sizeof_check name sz ];
  (name, sz)

and ctor_args (cd : constructor_declaration) =
  match cd.pcd_args with
  | Pcstr_tuple l -> l
  | Pcstr_record ls -> List.map (fun (l : label_declaration) -> l.pld_type) ls

and ctor_arity cd = List.length (ctor_args cd)

and ctor_arg_names cd = List.map (fun t -> tn (of_ct t)) (ctor_args cd)

(* R7, case 1: every constructor nullary — a plain enumeration. *)
and enum_layer nm cs =
  define ("jpl_" ^ nm) w4 "enum"
    (String.concat "|" (List.map (fun cd -> cd.pcd_name.txt) cs))
    [ Printf.sprintf "typedef uint32_t jpl_%s;   /* variant of %d nullary constructors */"
        nm (List.length cs) ];
  emit tags_b "/* tags for %s, in the artifact's own constructor order */\n" nm;
  List.iteri
    (fun i cd ->
      emit tags_b "#define JPL_%s_%s %du\n" (String.uppercase_ascii nm)
        (String.uppercase_ascii cd.pcd_name.txt) i)
    cs;
  emit tags_b "\n";
  ("jpl_" ^ nm, w4)

(* R7, case 2: a pooled NODE — tag + positional single-word slots, plus the pool
   decision 1 names it into.  Every payload component is checked to be one word
   BEFORE the cell is emitted, so a node whose constructor widened is reported, not
   silently truncated.  The capacity arrives from pool_cap: a type can only reach
   this rule by being declared pooled AND capped. *)
and node_layer nm (cap, cap_macro, why) =
  let d = Hashtbl.find tydecls nm in
  let cs =
    match d.ptype_kind with
    | Ptype_variant cs -> cs
    | _ -> fail ("pooled type " ^ nm ^ " is not a variant, so it has no node shape")
  in
  List.iter
    (fun cd ->
      List.iter
        (fun t ->
          let lt = of_ct t in
          if not (single_word lt) then
            fail
              ("a pooled node's constructor argument is wider than one word: " ^ nm
              ^ "." ^ cd.pcd_name.txt ^ " carries " ^ tn lt
              ^ " — the model must narrow it, or the node needs a variable payload"))
        (ctor_args cd))
    cs;
  let slots = List.fold_left (fun k cd -> max k (ctor_arity cd)) 0 cs in
  let node = "jpl_" ^ nm ^ "_node" in
  let handle = "jpl_" ^ nm in
  let sz = w4 * (1 + slots) in
  define handle w4 "node handle" "jpl_ref"
    [ Printf.sprintf "typedef jpl_ref %s;   /* a %s VALUE is a node-pool index */"
        handle nm ];
  (* Settle the handle before the node body, so a constructor naming its own type
     (cmd -> cmd) resolves here instead of recursing. *)
  Hashtbl.replace memo nm (handle, w4);
  define node sz "pooled node"
    (Printf.sprintf "tag + %d slot%s" slots (if slots = 1 then "" else "s"))
    ([ "typedef struct {";
       Printf.sprintf "  jpl_nat %s_tag;   /* one of JPL_%s_* */" nm
         (String.uppercase_ascii nm) ]
     @ List.init slots (fun i -> Printf.sprintf "  jpl_nat %s_slot%d;" nm i)
     @ [ Printf.sprintf "} %s;" node; sizeof_check node sz ]);
  pools :=
    { p_elem = node; p_arr = "jpl_" ^ nm ^ "_pool";
      p_count = Some (headroom * cap); p_from = cap_macro; p_why = why }
    :: !pools;
  emit tags_b "/* tags and slot meanings for %s, from the artifact's declaration order.\n\
              \   A pooled cell has one shape, so a constructor's arguments occupy\n\
              \   consecutive slots and the tag says how many of them mean anything. */\n"
    nm;
  List.iteri
    (fun i cd ->
      let a = ctor_arg_names cd in
      emit tags_b "#define JPL_%s_%s %du   /* %s%s */\n"
        (String.uppercase_ascii nm) (String.uppercase_ascii cd.pcd_name.txt) i
        cd.pcd_name.txt
        (if a = [] then " (no payload)" else " of " ^ String.concat ", " a))
    cs;
  emit tags_b "\n";
  (* The payload component types are laid out AFTER the node, so a self-reference
     resolves against the settled handle. *)
  List.iter
    (fun cd -> List.iter (fun t -> ignore (require (of_ct t))) (ctor_args cd)) cs;
  (handle, w4)

(* R7, case 3: a non-recursive variant with payloads — one named payload struct per
   constructor plus the tag.  No union (JPL forbids them), so the struct holds every
   constructor's payload; the report totals what that fatness costs. *)
and fat_layer nm cs =
  let payloads =
    List.filter_map
      (fun (cd : constructor_declaration) ->
        let a = ctor_args cd in
        if a = [] then None
        else
          let lts = List.map of_ct a in
          let sized =
            List.map (fun lt -> let (cn, sz) = require lt in (cn, sz, lt)) lts
          in
          let psz = List.fold_left (fun k (_, s, _) -> k + s) 0 sized in
          let name = "jpl_" ^ nm ^ "_" ^ cd.pcd_name.txt in
          define name psz "by-value payload"
            (String.concat "+" (List.map (fun (cn, _, _) -> cn) sized))
            ([ Printf.sprintf "typedef struct {   /* %s of %s */" cd.pcd_name.txt nm ]
             @ List.mapi
                 (fun i (cn, _, lt) -> Printf.sprintf "  %s a%d;   /* %s */" cn i (tn lt))
                 sized
             @ [ Printf.sprintf "} %s;" name; sizeof_check name psz ]);
          Some (name, psz, cd))
      cs
  in
  let sz = w4 + List.fold_left (fun k (_, s, _) -> k + s) 0 payloads in
  let np = List.length payloads in
  define ("jpl_" ^ nm) sz "fat variant (by value)"
    (Printf.sprintf "tag + %d payload%s" np (if np = 1 then "" else "s"))
    ([ "/* No union (JPL forbids them), so every constructor's payload is present and\n\
      \   the tag selects which ones mean anything.  Returned and stored by value. */";
       "typedef struct {";
       Printf.sprintf "  jpl_nat %s_tag;   /* one of JPL_%s_* */" nm
         (String.uppercase_ascii nm) ]
     @ List.map
         (fun (name, _, cd) -> Printf.sprintf "  %s %s;" name (nm ^ "_" ^ cd.pcd_name.txt))
         payloads
     @ [ Printf.sprintf "} jpl_%s;" nm; sizeof_check ("jpl_" ^ nm) sz ]);
  emit tags_b "/* tags for %s, in the artifact's own constructor order */\n" nm;
  List.iteri
    (fun i cd ->
      let a = ctor_arg_names cd in
      emit tags_b "#define JPL_%s_%s %du   /* %s */\n" (String.uppercase_ascii nm)
        (String.uppercase_ascii cd.pcd_name.txt) i
        (if a = [] then "nullary" else String.concat ", " a))
    cs;
  emit tags_b "\n";
  ("jpl_" ^ nm, sz)

(* R6: a declared record — fields in the .mli's order, by value. *)
and record_layer nm ls =
  let sized =
    List.map
      (fun (l : label_declaration) ->
        let lt = of_ct l.pld_type in
        let (cn, sz) = require lt in
        (cn, sz, l.pld_name.txt, lt))
      ls
  in
  let sz = List.fold_left (fun k (_, s, _, _) -> k + s) 0 sized in
  define ("jpl_" ^ nm) sz "record (by value)"
    (String.concat "+" (List.map (fun (cn, _, _, _) -> cn) sized))
    ([ Printf.sprintf "typedef struct {" ]
     @ List.map
         (fun (cn, _, lbl, lt) -> Printf.sprintf "  %s %s;   /* %s */" cn lbl (tn lt))
         sized
     @ [ Printf.sprintf "} jpl_%s;" nm; sizeof_check ("jpl_" ^ nm) sz ]);
  ("jpl_" ^ nm, sz)

(* R7's dispatcher, over the artifact's own declaration. *)
and named_layer nm =
  if nm = "text" then word_layer ()
  else if not (Hashtbl.mem tydecls nm) then
    fail ("named_layer: " ^ nm ^ " is not declared in the artifact")
  else begin
    let d = Hashtbl.find tydecls nm in
    (match d.ptype_params with
     | [] -> ()
     | _ -> note "PENDING parameterised declaration %s: a C layout needs a concrete instance" nm);
    match d.ptype_kind with
    | Ptype_abstract ->
        (match d.ptype_manifest with
         | Some t -> require (of_ct t)
         | None -> fail ("abstract type with no manifest: " ^ nm))
    | Ptype_record ls -> record_layer nm ls
    | Ptype_variant cs ->
        if List.for_all (fun cd -> ctor_arity cd = 0) cs then enum_layer nm cs
        else if List.mem nm pooled_types then
          node_layer nm
            (match pool_cap (c ()) nm with
             | Some s -> s
             | None ->
                 fail
                   ("pooled_types names " ^ nm
                   ^ " but pool_cap gives it no capacity: a pooled type must be sized, \
                     never left to fall through to a by-value layout"))
        else fat_layer nm cs
    | Ptype_open -> fail ("open type cannot be laid out: " ^ nm)
    | Ptype_external _ -> fail ("external type cannot be laid out: " ^ nm)
  end

(* The entry point: the C name and byte size of a place holding a value of this
   type, emitting every definition it needs first, so the header is dependency
   ordered by construction. *)
and require (t : lt) : string * int =
  let k = tn t in
  if Hashtbl.mem memo k then Hashtbl.find memo k
  else if Hashtbl.mem in_progress k then
    fail ("a by-value layout of " ^ k ^ " contains itself: it must be pooled (decision 1) or narrowed by the model")
  else begin
    Hashtbl.replace in_progress k ();
    let r = build t in
    Hashtbl.remove in_progress k;
    Hashtbl.replace memo k r;
    r
  end

and build t =
  match t with
  | L_nat -> (Hashtbl.find memo "nat")
  | L_bool -> (Hashtbl.find memo "bool")
  | L_unit -> (Hashtbl.find memo "unit")
  | L_word -> word_layer ()
  | L_list e -> list_layer e
  | L_opt a -> tagged_layer "opt" a
  | L_bres a -> tagged_layer "bres" a
  | L_pair (a, b) -> pair_layer a b
  | L_named n -> named_layer n
  | L_fun _ ->
      fail "a function-typed value reached the layout table (JPL.5-A.4 removed the phi parameter; if this reappears, the model changed)"
  | L_var v ->
      fail ("an un-instantiated type variable reached the layout: '" ^ v)
  | L_unk m ->
      fail ("a type the reader could not infer reached the layout: " ^ m)

(* ─────────────── 6. the header's opening, pools, and its assembly ───────── *)

let caps_section () =
  emit tags_b "/* ── capacities, constant-folded out of the artifact's own\n\
              \   jpl_caps_table (sh_jpl.v §1.1).  No number in this section was written\n\
              \   by hand: it is generated from the extracted term, and the gate diffs it\n\
              \   against the artifact EVALUATED by the OCaml runtime. ── */\n";
  List.iter
    (fun (field, macro, model_name, why) ->
      emit tags_b "#define %s %du   /* %s: %s */\n" macro (caps_of (c ()) field)
        model_name why)
    cap_fields;
  emit tags_b "\n\
  /* The total order sh_jpl.v §1 proves (cap_order, cap_words_order, cap_fuel_order)\n\
  \   and the two derived margins, re-checked in C so a cap that drifts fails the\n\
  \   build and not only the proof.  The last check is the one that matters for the\n\
  \   word slab: MAX_WORDS is not an independent number, it is the sum §1 names, so\n\
  \   the C macro is pinned against its own decomposition. */\n\
  typedef char jpl_check_cap_order[((JPL_MAX_WIDTH <= JPL_MAX_WORD) && (JPL_MAX_ARGV <= JPL_MAX_ENV) && (JPL_MAX_ENV <= JPL_MAX_LIST) && (JPL_MAX_LIST <= JPL_MAX_CMD) && (JPL_MAX_CMD <= JPL_MAX_STACK)) ? 1 : -1];\n\
  typedef char jpl_check_cap_fuel_order[((JPL_MAX_STACK <= JPL_GLOB_FUEL) && (JPL_GLOB_FUEL <= JPL_MAX_FUEL)) ? 1 : -1];\n\
  typedef char jpl_check_cmd_is_the_fuel_margin[((JPL_MAX_CMD + JPL_GLOB_FUEL) == JPL_MAX_FUEL) ? 1 : -1];\n\
  typedef char jpl_check_stack_is_two_cmd_pools[((2u * JPL_MAX_CMD) == JPL_MAX_STACK) ? 1 : -1];\n\
  typedef char jpl_check_words_is_the_named_sum[((2u * JPL_MAX_STACK + 2u * JPL_MAX_ENV + 2u) == JPL_MAX_WORDS) ? 1 : -1];\n\
  typedef char jpl_check_words_order[((JPL_MAX_STACK <= JPL_MAX_WORDS) && (JPL_MAX_WORDS <= JPL_GLOB_FUEL)) ? 1 : -1];\n\
  typedef char jpl_check_fuel_fits_the_word[(JPL_MAX_FUEL < 4294967295u) ? 1 : -1];\n\n"

let pools_section () =
  emit pools_b "/* ── the pools.  Definitions live in the emitted translation unit\n\
                \   (JPL.md §6: no dynamic allocation); they are declared here so every\n\
                \   consumer compiles against one capacity.  Index 0 is JPL_NIL and is\n\
                \   never allocated, so a capacity counts the reserved cell too. ── */\n";
  List.iter
    (fun p ->
      match p.p_count with
      | Some n ->
          let macro =
            let n = String.length p.p_arr in
            let s0 = if String.sub p.p_arr 0 (min 4 n) = "jpl_" then 4 else 0 in
            let s1 =
              if n >= 5 && String.sub p.p_arr (n - 5) 5 = "_pool" then n - 5 else n
            in
            "JPL_POOL_" ^ String.uppercase_ascii (String.sub p.p_arr s0 (s1 - s0))
          in
          emit pools_b "#define %s %du   /* from %s, %d cells, x headroom %d; %s */\n\
                        extern %s %s[%s];\n\n" macro n p.p_from (n / headroom)
            headroom p.p_why p.p_elem p.p_arr macro
      | None ->
          emit pools_b "/* PENDING CAPACITY — %s is declared, and nothing sizes it:\n%s */\n\
                        extern %s %s[];\n\n"
            p.p_arr p.p_why p.p_elem p.p_arr)
    (List.rev !pools)

let header_text ml mli =
  let b = Buffer.create 16384 in
  emit b "/* GENERATED by verify/c/jpl_emit.ml from\n\
  \   %s\n\
  \   %s\n\
  \   DO NOT EDIT — the gate re-runs the emitter and byte-compares this file.\n\
  \   JPL.md §6 is the normative contract; §9.2 decision 3 is why a recursive type\n\
  \   is a handle into a static pool and never an inline array.  This is the TYPE\n\
  \   LAYER only: no function body is emitted here, and JPL.5-B.3 owns the\n\
  \   lowering into it.\n\
  \n\
  \   Three choices are NOT derived from the artifact, and layout.txt numbers them:\n\
  \   which declared types are pooled, which cap sizes which list pool, and the\n\
  \   pool headroom factor.  Everything else follows from a line of the .mli plus a\n\
  \   capacity folded out of the .ml, and every struct's byte count is checked by\n\
  \   the compiler through the typedef that follows it. */\n\n\
               #ifndef SH_RUN_JPL_H\n\
               #define SH_RUN_JPL_H\n\n\
               #include <stdint.h>\n\n" ml mli;
  Buffer.add_string b (Buffer.contents tags_b);
  emit b "/* ── the fixed-width vocabulary, then the type layer in dependency order ── */\n";
  Buffer.add_string b (Buffer.contents types_b);
  Buffer.add_string b "\n";
  Buffer.add_string b (Buffer.contents pools_b);
  emit b "\n/* ── prototypes for the shipped closure: parameter names are the artifact's\n\
  \   own, and every type comes from the .mli signature mapped by the rule set. */\n";
  Buffer.add_string b (Buffer.contents protos_b);
  Buffer.add_string b "\n#endif /* SH_RUN_JPL_H */\n";
  Buffer.contents b

(* ────────────── 7. prototypes, constants, and what is PENDING ───────────── *)

let c_fn n = "jpl_" ^ String.map (fun ch -> if ch = '.' then '_' else ch) n

let c_upper n =
  String.uppercase_ascii (String.map (fun ch -> if ch = '.' then '_' else ch) n)

(* How many closure bindings call this one: the measurement that turns "needs a
   monomorphization" from an assertion into a number. *)
let callers_of n =
  Hashtbl.fold
    (fun _ m acc -> if Hashtbl.mem m.edges n then acc + 1 else acc)
    closure 0

(* The cap bindings are folded once into the JPL_MAX_* macros above; re-emitting
   them as JPL_C_* would be a second name for one number. *)
let cap_bindings =
  [ ("mAX_WIDTH", "JPL_MAX_WIDTH"); ("mAX_WORD", "JPL_MAX_WORD");
    ("mAX_ARGV", "JPL_MAX_ARGV"); ("mAX_ENV", "JPL_MAX_ENV");
    ("mAX_LIST", "JPL_MAX_LIST"); ("gLOB_FUEL", "JPL_GLOB_FUEL");
    ("mAX_FUEL", "JPL_MAX_FUEL") ]

let emit_prototypes members =
  let nf = ref 0 and nv = ref 0 and np = ref 0 in
  List.iter
    (fun nm ->
      if nm = "jpl_caps_table" then
        emit protos_b "/* jpl_caps_table is READ, not lowered: its nine capacities became\n\
        \   the #defines above, which is why the shipped C carries no cap record. */\n"
      else if not (Hashtbl.mem vals nm) then
        note "%s has no .mli signature, so no prototype was emitted" nm
      else begin
        let args, res = sig_of nm in
        let ty = cty (Hashtbl.find vals nm) in
        if has_var res || List.exists has_var args then begin
          emit protos_b
            "/* PENDING polymorphic %s : %s\n\
            \   reached from %d closure bindings; a C instance must be chosen per call\n\
            \   site, so JPL.md §6's \"no monomorphization\" claim is refuted by this\n\
            \   binding and the instance set belongs to JPL.5-B.3's call-site census. */\n"
            nm ty (callers_of nm);
          incr np
        end
        else if args = [] then
          (* an arity-0 value: a foldable nat becomes a #define, anything else needs
             an initialiser, which is the lowering's business, not this layer's *)
          match try_fold (Hashtbl.find binds nm).b_body with
          | Some v ->
              (match List.assoc_opt nm cap_bindings with
               | Some macro ->
                   emit protos_b
                     "/* %s : %s = %d is already defined above as %s — one number, one\n\
                     \   name, so the cap the C allocates against is the cap the artifact carries. */\n"
                     nm ty v macro
               | None ->
                   emit protos_b "#define JPL_C_%s %du   /* %s : %s */\n" (c_upper nm) v
                     nm ty);
              incr nv
          | None ->
              emit protos_b
                "/* PENDING constant %s : %s — not a foldable nat, so it needs an\n\
                \   initialiser in the lowering (JPL.5-B.3), not a #define here. */\n"
                nm ty;
              incr np
        else begin
          let names = param_names (Hashtbl.find binds nm).b_body in
          let rn = List.length args in
          let ps =
            if List.length names = rn then names
            else List.init rn (fun i -> "a" ^ string_of_int i)
          in
          let (rt, _) = require res in
          let ct = List.map (fun a -> let (n, _) = require a in n) args in
          emit protos_b "%s %s(%s);\n" rt (c_fn nm)
            (String.concat ", "
               (List.map2 (fun t p -> Printf.sprintf "%s %s" t p) ct ps));
          incr nf
        end
      end)
    members;
  (!nf, !nv, !np)

(* ───────────────────────────── 8. the report ────────────────────────────── *)

let kb x = Printf.sprintf "%.1f KiB" (float_of_int x /. 1024.0)

let section title = Printf.printf "\n==== %s ====\n" title

let indent s =
  String.concat "\n"
    (List.map (fun l -> "     " ^ l) (String.split_on_char '\n' s))

let report ml mli members vocabulary nf nv np =
  let caps = c () in
  Printf.printf "INPUT      %s\n           %s\n" ml mli;
  Printf.printf "artifact   %d bindings, %d typed signatures, %d type declarations\n"
    (Hashtbl.length binds) (Hashtbl.length vals) (Hashtbl.length tydecls);
  section "CAPACITIES, FOLDED OUT OF THE ARTIFACT'S jpl_caps_table";
  (* The record FIELD is printed as well as the model name and the C macro, so the
     gate's differential check can pair each folded number with the field the
     OCaml runtime reads out of the same record, by name rather than by position. *)
  List.iter
    (fun (field, macro, model_name, why) ->
      Printf.printf "  %-14s %-13s %-18s %8d   %s\n" field model_name macro
        (caps_of caps field) why)
    cap_fields;
  section "LAYOUT TABLE (the vocabulary the shipped closure reaches)";
  Printf.printf "  %-26s %-22s %8s  %s\n" "C type" "rule" "bytes" "components";
  List.iter
    (fun n ->
      let r = Hashtbl.find rows n in
      Printf.printf "  %-26s %-22s %8d  %s\n" r.name r.kind r.size r.fields)
    (List.rev !row_order);
  Printf.printf "\n  %d C types emitted: %d each followed by its own sizeof check, the\n\
    \  other %d one-word typedefs (R1 scalars, R3 handles, R7's all-nullary variant)\n\
    \  covered by jpl_check_one_word_families — no emitted type's size is left to the\n\
    \  reader.\n"
    (List.length !row_order) (List.length !checked)
    (List.length !row_order - List.length !checked);
  section "DOMAIN CHECK (the reporter's vocabulary vs this emitter's layout)";
  Printf.printf "  %d declared vocabulary types carry no parameters, and each reached a\n"
    (List.length vocabulary);
  Printf.printf "  layout rule: %s\n"
    (String.concat ", " (List.sort String.compare vocabulary));
  Printf.printf "  main's check is bidirectional: a vocabulary type with no rule, or a laid\n";
  Printf.printf "  out type the closure does not reach, is a hard failure (exit 2).\n";
  section "STATIC POOLS (cells x cell size, from the caps above)";
  Printf.printf "  %-26s %-24s %8s %10s %12s  %s\n" "array" "element" "cells"
    "bytes" "size" "sized from";
  let total = ref 0 and unsized = ref [] in
  List.iter
    (fun p ->
      let esz = size_of_name p.p_elem in
      match p.p_count with
      | Some n ->
          let b = n * esz in
          total := !total + b;
          Printf.printf "  %-26s %-24s %8d %10d %12s  %s\n" p.p_arr p.p_elem n b
            (kb b) p.p_from
      | None ->
          unsized := p :: !unsized;
          Printf.printf "  %-26s %-24s %8s %10d %12s  %s\n" p.p_arr p.p_elem "PENDING"
            esz (kb esz ^ " per word") p.p_from)
    (List.rev !pools);
  Printf.printf "\n  bounded static total  %s (%d bytes)%s\n" (kb !total) !total
    (if !unsized = [] then ", and every declared pool is inside it"
     else ", excluding the unsized pools");
  section "WHAT THIS LAYER COULD NOT SIZE";
  if !unsized = [] then begin
    Printf.printf "  Nothing: every pool the header declares now carries a capacity read out\n";
    Printf.printf "  of jpl_caps_table.  The last gap was the word slab.  sh_jpl.v §1 added\n";
    Printf.printf "  MAX_WORDS on 2026-10-05 as the sum 2*MAX_STACK + 2*MAX_ENV + 2, whose\n";
    Printf.printf "  tree half and environment half are PROVED (§7.1 cmd_fits_words from\n";
    Printf.printf "  cmd_words <= 2*cmd_count; §5 benv_words_le) and whose expanded-copy half\n";
    Printf.printf "  is the NAMED OBLIGATION \"one live frame per source node\" — so the header\n";
    Printf.printf "  allocates against a decomposition with one recorded debt, not a guess,\n";
    Printf.printf "  and jpl_check_words_is_the_named_sum pins the C macro to that sum.\n";
    Printf.printf "  Cost of the decision, measured: the slab is %s, which is %d cells x %d\n"
      (kb (headroom * caps.c_words * size_of_name "jpl_text"))
      (headroom * caps.c_words) (size_of_name "jpl_text");
    Printf.printf "  bytes per cell, and it dominates every other pool.  The per-cell size is\n";
    Printf.printf "  MAX_WORD uint32 codes; narrowing them needs a proved `code < 256`, which\n";
    Printf.printf "  sh_concrete.v §1 only intends — see JPL.md §6's follow-on note.\n\n"
  end
  else
  List.iter
    (fun p ->
      let esz = size_of_name p.p_elem in
      let low = caps.c_cmd in
      let high = caps.c_cmd * caps.c_list in
      Printf.printf "  %s (element %d bytes) has no capacity in the cap table.\n" p.p_arr
        esz;
      Printf.printf "%s\n" (indent p.p_why);
      Printf.printf "     What the locked caps DO imply, as a range of live words:\n";
      Printf.printf "       lower    %7d words (one per cmd node)                = %s\n"
        low (kb (low * esz));
      Printf.printf "       upper    %7d words (every node owning a full list)   = %s\n"
        high (kb (high * esz));
      Printf.printf "     The model must fix one number in that range and prove it.  Nothing\n";
      Printf.printf "     in the header allocates against a guess.\n\n")
    (List.rev !unsized);
  section "THE THREE NON-DERIVED CHOICES";
  Printf.printf "  1. pooled types            %s — from sh_jpl.v §1's cap comments, each with\n"
    (String.concat ", " pooled_types);
  List.iter
    (fun nm ->
      match pool_cap caps nm with
      | Some (_, macro, _) ->
          Printf.printf "                             %s -> jpl_%s_pool of %s cells x headroom %d\n"
            nm nm macro headroom
      | None -> Printf.printf "                             %s -> NO CAPACITY\n" nm)
    pooled_types;
  Printf.printf "                             (the two halves are cross-checked: naming a type pooled without\n\
                \                             capping it is a refusal, not a silent fall-through to a by-value\n\
                \                             layout).  Every other vocabulary type is by value and needs no\n\
                \                             capacity\n";
  Printf.printf "  2. list pool sizing        pair(text,text) -> JPL_MAX_ENV, frame list -> JPL_MAX_STACK,\n";
  Printf.printf "                             every other list kind -> JPL_MAX_LIST\n";
  Printf.printf "  3. headroom factor         %d, pending JPL.5-B.3's allocation-bound proof\n"
    headroom;
  section "FUNCTIONS AND VALUES";
  Printf.printf "  closure members         %d\n" (List.length members);
  Printf.printf "  prototypes emitted      %d\n" nf;
  Printf.printf "  constant #defines       %d\n" nv;
  Printf.printf "  PENDING                 %d\n" np;
  section "FINDINGS";
  List.iter (fun s -> Printf.printf "  %s\n" s) (List.rev !findings);
  if !findings = [] then print_endline "  (none)"

(* ───────────────────────────── 9. main ──────────────────────────────────── *)

let main ml mli out_h roots =
  let items = Parse.implementation (Lexing.from_channel (open_in ml)) in
  add_struct "" items;
  add_sig (Parse.interface (Lexing.from_channel (open_in mli)));
  let caps = read_caps () in
  caps_r := Some caps;
  reach roots;
  let members = closure_members () in
  scalars ();
  let nf, nv, np = emit_prototypes members in
  (* DOMAIN CHECK.  The reporter prints the vocabulary the closure reaches, computed
     in the shared reader; the emitter lays out what its own signatures required.  If
     the two sets differ, one of them is wrong about the artifact, and a header built
     on a smaller domain than the closure needs would compile and then be wrong at
     run time — so this is a hard failure, not a note. *)
  type_vocab members;
  let no_params n =
    match (Hashtbl.find tydecls n).ptype_params with [] -> true | _ -> false
  in
  let vocabulary = Hashtbl.fold (fun n _ a -> n :: a) vocab [] in
  let needed = List.filter no_params vocabulary in
  let absent = List.filter (fun n -> not (Hashtbl.mem memo n)) needed in
  if absent <> [] then
    fail
      ("the closure's vocabulary is not the layout's domain: "
      ^ String.concat ", " absent ^ " reached no layout rule");
  let extra =
    List.filter
      (fun k -> Hashtbl.mem tydecls k && no_params k && not (List.mem k vocabulary))
      (Hashtbl.fold (fun k _ a -> k :: a) memo [])
  in
  if extra <> [] then
    fail
      ("the emitter laid out declared types the closure does not reach: "
      ^ String.concat ", " extra);
  caps_section ();
  pools_section ();
  family_check ();
  let oc = open_out out_h in
  output_string oc (header_text ml mli);
  close_out oc;
  report ml mli members needed nf nv np

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [ ml; mli; out_h ] -> main ml mli out_h default_roots
  | [ ml; mli; out_h; rs ] -> main ml mli out_h (split_commas rs)
  | _ -> fail "usage: jpl_emit <ml> <mli> <out.h> [comma-separated-roots]"
