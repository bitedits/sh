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
let runtime_b = Buffer.create 4096
let edges_b = Buffer.create 4096
let edge_defs_b = Buffer.create 8192
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
    p_why : string;
    (* The handle type this pool's cells are reached through, recorded by whichever rule
       registered the pool.  Every handle is a `uint32_t`, so C cannot tell a word handle
       from a cmd handle; the registry can, and JPL.md §6.6's allocator returns the one it
       was given instead of a bare `jpl_ref` — which is what lets a lowering ask "what
       allocates a value of this type?" without a table of pool names of its own. *)
    p_handle : string }

let pools : pool list ref = ref []
let findings : string list ref = ref []

(* A pool's STEM is the one substring three things need: the capacity macro
   JPL_POOL_<KIND>, the runtime names jpl_<stem>_alloc / _reset / _is_live and its four
   counters.  It is read out of the array name the registering rule chose, so a pool
   renamed by decision 1 renames its allocator, its counters and its macro in one keystroke
   — a second spelling of the stem in this file would be a name a reader could get wrong. *)
let pool_stem p =
  let n = String.length p.p_arr in
  let s0 = if String.sub p.p_arr 0 (min 4 n) = "jpl_" then 4 else 0 in
  let s1 =
    if n >= 5 && String.sub p.p_arr (n - 5) 5 = "_pool" then n - 5 else n
  in
  String.sub p.p_arr s0 (s1 - s0)

let pool_macro p = "JPL_POOL_" ^ String.uppercase_ascii (pool_stem p)

(* §6.6's rule is bidirectional: no capacity without an allocator, and no allocator for a
   pool that cannot be sized.  The unsized pools are therefore excluded from the runtime
   and REPORTED, never skipped quietly — the report's pools_without_capacity key is the
   count, and the gate asserts the allocators and the sized pools are the same number. *)
let sized_pools () = List.filter (fun p -> p.p_count <> None) (List.rev !pools)

(* Every symbol the runtime puts in the shared C namespace.  The gate needs this list
   because §6.3's ABI and §6.6's runtime both emit `jpl_<something>` into one translation
   unit, so a collision is not a style point but a duplicate definition. *)
let runtime_names () =
  let base =
    List.concat_map
      (fun p ->
        let s = pool_stem p in
        [ "jpl_" ^ s ^ "_next"; "jpl_" ^ s ^ "_peak"; "jpl_" ^ s ^ "_taken";
          "jpl_" ^ s ^ "_refused"; "jpl_" ^ s ^ "_alloc"; "jpl_" ^ s ^ "_reset";
          "jpl_" ^ s ^ "_is_live"; "jpl_" ^ s ^ "_edge" ])
      (sized_pools ())
  in
  if base = [] then [] else base @ [ "jpl_pools_refusals" ]

(* ──────────── 6a-bis. the cell shapes the edge tables are derived from ────── *)

(* JPL.md §6.7's first slice needs, for every pool, "what does one cell of this pool point
   at".  The layout already knows: the rules that emitted the cell's fields walked the
   declared types to get there.  So the shape is RECORDED by those rules as they run — a
   table transcribed here would be a second model of the artifact, and §6.7's whole claim is
   that reachability is read from one reading rather than asserted by another.
   A position is one WORD — or, for an array field, one ELEMENT — of a cell, in the cell's own
   field order, so the table's row width is the cell's sizeof divided by the word and the two
   are cross-checked at compile time.
     P_tag   — the node's tag word: it SELECTS the row, so it is not itself an edge.
     P_lt t  — a payload whose declared type the layout resolved.
     P_tail  — a cons cell's `next`, which is an edge into the pool it lives in.
     P_leaf t — the words the fields before it left in the cell, one element of `t` per group:
               an ARRAY field, whose length the cell's width supplies and no declaration does.
     P_void  — padding past this constructor's arity: a word that was never written. *)
type position =
  | P_tag
  | P_lt of lt
  | P_tail
  | P_leaf of lt
  | P_void

type cell_row = { r_label : string; r_pos : position list }

(* The shape is recorded DURING the layout, but its widths are computed after it: a pooled
   node's payload types are laid out after the node itself, so their byte sizes — which this
   reading must use, because they are the numbers the emitted `sizeof` checks pin — do not
   exist yet when the node registers itself. *)
type cell_shape =
  { s_stem : string; s_elem : string; s_tagged : bool; s_rows : cell_row list }

let shapes : (string, cell_shape) Hashtbl.t = Hashtbl.create 8

let record_shape stem elem tagged rows =
  if not (Hashtbl.mem shapes stem) then
    Hashtbl.replace shapes stem
      { s_stem = stem; s_elem = elem; s_tagged = tagged; s_rows = rows }

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
      p_handle = "jpl_wref";
      p_from = "JPL_MAX_WORDS";
      p_why =
        "sh_jpl.v §1's MAX_WORDS, a sum of the already-locked caps: MAX_STACK cells for\n\
  \    the words a pool-fitting tree holds (§7.1 cmd_fits_words, from cmd_words <= 2*\n\
  \    cmd_count and cmd_fits), a second MAX_STACK for the runtime-expanded copies an\n\
  \    FFor/FCase frame holds (the OWED step-machine invariant \"one live frame per\n\
  \    source node\" — named in §1, not yet proved), 2*MAX_ENV for the environment's\n\
  \    name/value cells (§5 benv_words_le), and 2 per-step temporaries." }
    :: !pools;
  (* §6.7's LEAF case, DERIVED rather than filled: the cell is `{ jpl_nat wt_len; jpl_nat
     wt_code[JPL_MAX_WORD] }`, so both fields are the type this rule emitted them as, and the
     array's element count comes from the cell's own width.  Every word therefore resolves
     through the same walk a payload uses — and none of them is an edge, which is a conclusion
     here rather than a guess. *)
  record_shape "word" "jpl_text" false
    [ { r_label = "len + code[]"; r_pos = [ P_lt L_nat; P_leaf L_nat ] } ];
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
      p_count = Some (headroom * cap); p_from = macro; p_why = why;
      p_handle = handle }
    :: !pools;
  (* One row, because a cons cell has no tag: the hd is a payload of the element type — by
     value if the element is an aggregate, an edge if it is itself a handle — and the tail is
     an edge into this pool. *)
  record_shape k cell false
    [ { r_label = show_lt e ^ " cell"; r_pos = [ P_lt e; P_tail ] } ];
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
      p_count = Some (headroom * cap); p_from = cap_macro; p_why = why;
      p_handle = handle }
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
  (* The node's rows, recorded for §6.7 before the payload types are laid out below: the
     positions are the artifact's constructor arguments in order, so a model change to a
     constructor changes the table in the same run and nothing has to remember it. *)
  record_shape nm node true
    (List.map
       (fun cd ->
         { r_label = cd.pcd_name.txt;
           r_pos = P_tag :: List.map (fun t -> P_lt (of_ct t)) (ctor_args cd) })
       cs);
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
          let macro = pool_macro p in
          emit pools_b "#define %s %du   /* from %s, %d cells, x headroom %d; %s */\n\
                        extern %s %s[%s];\n\n" macro n p.p_from (n / headroom)
            headroom p.p_why p.p_elem p.p_arr macro
      | None ->
          emit pools_b "/* PENDING CAPACITY — %s is declared, and nothing sizes it:\n%s */\n\
                        extern %s %s[];\n\n"
            p.p_arr p.p_why p.p_elem p.p_arr)
    (List.rev !pools)

(* ───────────────── 6b. the pool runtime (JPL.md §6.6, 5-B.3b-ii-b-1) ────── *)

(* The header half: declarations only, so the type layer stays a type layer and every
   body lives in the generated translation unit below.  What is emitted here is derived
   from the same `!pools` registry the capacity section above walked, which is the whole
   point of §6.6's rule — a pool that gained a cell type and a capacity cannot be given a
   runtime by remembering to write one, and a runtime cannot name a handle the registry
   never settled. *)
(* One pool's declarations, assembled line by line from NAMED parts.  The stem, the
   capacity macro, the cell type and the handle are arguments to each `sprintf` rather
   than the thirtieth through fortieth position of one format string, because the whole
   runtime is one design repeated eight times and a half-changed template is precisely the
   bug a positional format invites. *)
let runtime_decl p =
  let s = pool_stem p in
  let m = pool_macro p in
  String.concat ""
    [
      Printf.sprintf "/* %s: %s of %s cells of %s, handled as %s */\n" s p.p_arr m
        p.p_elem p.p_handle;
      Printf.sprintf
        "extern jpl_ref jpl_%s_next;     /* lowest index never handed out; 1u is an empty\
         \ region */\n"
        s;
      Printf.sprintf
        "extern jpl_ref jpl_%s_peak;     /* widest any one region got: decision 4's\
         \ quantity, measured */\n"
        s;
      Printf.sprintf "extern jpl_ref jpl_%s_taken;    /* cells served since the program\
                      \ started */\n"
        s;
      Printf.sprintf
        "extern jpl_ref jpl_%s_refused;  /* allocations that found no cell: §6.6's\
         \ saturate-to-error edge */\n"
        s;
      Printf.sprintf
        "typedef char jpl_check_%s_capacity_fits_the_counter[((%s < JPL_REF_TOP) ? 1 : -1)];\n"
        s m;
      Printf.sprintf "%s jpl_%s_alloc(void);   /* JPL_NIL once the region of %s cells is\
                      \ full */\n" p.p_handle s m;
      Printf.sprintf "jpl_ref jpl_%s_reset(void);   /* cells returned; next goes back to\
                      \ 1u */\n" s;
      Printf.sprintf "jpl_bool jpl_%s_is_live(jpl_ref h);   /* h names a cell of THIS\
                      \ region */\n\n"
        s;
    ]

let runtime_section () =
  let ps = sized_pools () in
  emit runtime_b "/* ── the pool runtime (JPL.md §6.6, 5-B.3b-ii-b-1): one bounded region per\n\
                \   pool above.  Declarations only — the definitions and bodies are in the\n\
                \   generated translation unit sh_run_jpl_pools.c, which includes this header,\n\
                \   and that file is the only C in this tree holding a mutable static.  Index 0\n\
                \   is JPL_NIL and is never handed out, so a pool of C cells serves C-1.\n\
                \   Reclamation is at region granularity because a per-cell free needs the\n\
                \   reachability rule §6.5's ii-b-2 owns before it is safe, not a function; a\n\
                \   reset does NOT clear cells, since clearing them at every step boundary would\n\
                \   price the step by the pool rather than by the data and no lemma requires the\n\
                \   bytes to be zero.  is_live is the guard rail that makes a handle carried\n\
                \   across a reset observable — not a liveness analysis. */\n";
  emit runtime_b "#define JPL_REF_TOP 4294967295u   /* counters saturate here, never wrap (§4.2) */\n\
                  typedef char jpl_check_ref_top_is_the_handle_word[((sizeof (jpl_ref) == 4u) ? 1 : -1)];\n\n";
  List.iter (fun p -> Buffer.add_string runtime_b (runtime_decl p)) ps;
  if ps <> [] then
    emit runtime_b "/* §4.2 wants one observable place: the saturating sum of every pool's refusals.\n\
                    \   A lowering reads a nil handle as the same edge a fired branch_guardb is\n\
                    \   (§5), and the host reads this as the run's verdict. */\n\
                    jpl_nat jpl_pools_refusals(void);\n\n";
  List.iter
    (fun p ->
      match p.p_count with
      | None ->
          emit runtime_b "/* NO RUNTIME for %s: it has no capacity, so it can be neither defined\n\
                          \   nor handed out (§6.6's rule cuts both ways). */\n\n"
            p.p_arr
      | Some _ -> ())
    (List.rev !pools)

(* ───────────── 6c. the pool edge tables (JPL.md §6.7, 5-B.3b-ii-b-2a) ─────── *)

(* R7 stores a pooled node as `tag + n single-word slots`, which erases what a slot MEANS:
   to the runtime a handle and a count are the same uint32_t.  §6.7's collector therefore
   cannot be written until the meaning comes back, and it must come back from the SAME
   reading that laid the cell out — a table typed by hand beside the layout would be two
   models of one artifact, agreeing today and drifting the first time a constructor changes.
   So the classes below are computed from the `position`s the layout rules recorded, and the
   only arithmetic borrowed is the byte width those same rules memoised (`size_of_name`),
   which is what lets a `jpl_check_*` typedef pin the table against the cell it describes. *)
(* One class per WORD of a cell, not per declared field: R3 puts a list's element INLINE, so
   a `(text * text)` cons cell's element is two words with two meanings, and a per-field
   table would need a second table saying how a field splits.  Flattening to words here makes
   the identity `NPOS * 4 == sizeof (cell)` exact and lets a collector walk one array with no
   recursive read of another.  A word is a value, a word this row never writes, or a handle
   into the pool named by the stem — and the stems come from the registry, so a pool decision
   1 adds becomes a target class in the same run rather than a name a table has to learn. *)
type edge_class =
  | E_scalar
  | E_unused
  | E_edge of string

(* The class ids as C.  The two fixed ones are named; an edge names the TARGET pool, and the
   ids come from the registry, so a pool that is renamed or added renumbers the targets that
   cite it rather than leaving a table pointing at a name that no longer exists. *)
let edge_pool_ids () =
  let stems = List.sort String.compare (List.map pool_stem (List.rev !pools)) in
  let tbl = Hashtbl.create 16 in
  List.iteri (fun i s -> Hashtbl.replace tbl s (i + 3)) stems;
  tbl

let edge_class_macro = function
  | E_scalar -> "JPL_EDGE_SCALAR"
  | E_unused -> "JPL_EDGE_UNUSED"
  | E_edge s -> "JPL_EDGE_TO_" ^ String.uppercase_ascii s ^ "_POOL"

(* Which pool, if any, a value of this lowered type is a HANDLE into.  Read out of the
   registry by handle name, so decision 1, decision 2 and R2's word exception are answered
   by the pools the layout actually built rather than by a second copy of their rules. *)
let edge_target lt =
  match List.find_opt (fun p -> p.p_handle = value_name lt) (List.rev !pools) with
  | Some p -> Some (pool_stem p)
  | None -> None

(* How many words a cell occupies, read from the layout's own memoised size — the same number
   the emitted `sizeof` check pins, so a table that disagreed with the struct it describes is
   a compile error and not a comment.  A leaf's single position spans the whole cell, which is
   why the identity `NPOS * 4 == sizeof (cell)` holds for every pool without an exception. *)
let edge_cell_words elem =
  let esz = size_of_name elem in
  if esz = 0 then
    fail ("the edge table has no size for the cell type " ^ elem)
  else if esz mod w4 <> 0 then
    fail
      ("cell type " ^ elem ^ " is " ^ string_of_int esz
      ^ " bytes, not a whole number of words: every emitted struct is a sum of uint32_t, so\n\
         \   a remainder means the layout and this reading disagree")
  else esz / w4

(* Which pool each WORD of a declared type is a handle into, in field order.  A handle is one
   word and the whole answer; a by-value aggregate is flattened into its leaf words.  What
   the walk can only answer CONDITIONALLY is refused: an option's or a fat variant's payload
   words mean nothing under one tag value, and a per-word table has no place to say "under
   which tag" — a collector reading them would forward a stale word as if it were live, which
   is the failure mode §6.7 refuses to inherit.  Nothing pooled contains one today: R7 checks
   a node's slots are single words before this runs, and R3's element types are the only
   aggregates inline in a cell.  If the model later puts a tagged aggregate there, the emitter
   stops rather than inventing a third table to say what it means. *)
let rec edge_expand seen t =
  match edge_target t with
  | Some s -> [ E_edge s ]
  | None ->
      (match t with
      | L_nat | L_bool | L_unit -> [ E_scalar ]
      | L_word ->
          fail
            "a word reached the edge walk without the word pool answering to its handle name"
      | L_list _ ->
          fail
            ("a list handle reached the edge walk with no pool behind it: decision 2 sizes\n\
             \   every list kind, so this is a pool the layout registered under a name this\n\
             \   reading did not find")
      | L_opt a | L_bres a ->
          fail
            ("the edge walk met the tagged aggregate " ^ show_lt t ^ " (payload "
            ^ show_lt a
            ^ ") inline in a pooled cell: its payload words are meaningful only under one\n\
               \   tag, which a per-word class cannot state")
      | L_pair (a, b) -> edge_expand seen a @ edge_expand seen b
      | L_named n ->
          if List.mem n seen then
            fail
              ("the edge walk reopened " ^ n ^ " inside itself: the layout refuses a by-value\n\
                 \   cycle before this point, so reaching one means the two readings disagree")
          else
            let d = Hashtbl.find tydecls n in
            let opens l = List.concat_map (fun x -> edge_expand (n :: seen) x) l in
            begin
            match d.ptype_kind with
            | Ptype_record ls -> opens (List.map (fun x -> of_ct x.pld_type) ls)
            | Ptype_variant cs ->
                if List.for_all (fun cd -> ctor_arity cd = 0) cs then [ E_scalar ]
                else
                  fail
                    ("the edge walk met the variant " ^ n
                    ^ " with payloads: its payload words are selected by a tag, which a\n\
                       \   per-word class cannot state")
            | Ptype_abstract ->
                (match d.ptype_manifest with
                | Some m -> opens [ of_ct m ]
                | None ->
                    fail
                      ("the edge walk reached the abstract type " ^ n
                      ^ " with no manifest, so what its words mean is unknowable"))
            | Ptype_open -> fail ("the edge walk reached the open type " ^ n)
            | Ptype_external _ ->
                fail ("the edge walk reached the external type " ^ n)
            end
      | L_fun _ -> fail "the edge walk met a function-typed value, which has no layout"
      | L_var v ->
          fail ("the edge walk met an un-instantiated type variable: '" ^ v)
      | L_unk w -> fail ("the edge walk met an un-inferable type: " ^ w))

(* How many positions flattened to more than one word — the sites where a pooled cell holds
   an aggregate BY VALUE and this reading is what says how many of its words are edges.  The
   report publishes the count so the gate can assert that the two pair cells are the only
   ones, rather than that being a claim in a comment. *)
let edge_flattened : int ref = ref 0

(* The census the report prints: per pool, its cell type, the row count, the words per row,
   and how the three classes divide those words.  The classes partition a table's entries, so
   the three counters must sum to rows x words — an identity the gate re-derives from the
   emitted text rather than trusting here. *)
let edge_census : (string * string * int * int * int * int * int) list ref = ref []

(* One position's classes.  A P_lt's classes must COVER its own bytes exactly: a payload the walk
   flattens to a different number of words than the layout sized is the two readings of one
   declaration disagreeing, and the table would then describe a struct that does not exist.
   P_leaf is not answerable here because an array's element count is a property of the ROW, so
   edge_row handles it and hands back the classes of one element by asking this function. *)
let edge_classes_of p pos =
  match pos with
  | P_tag -> [ E_scalar ]
  | P_void -> [ E_unused ]
  | P_tail ->
      (* A cons cell's tail is an edge into the pool the cell itself lives in — the one edge
         this reading can only learn from its enclosing pool, because `jpl_ref` is handle-typed
         and pool-less until the cell registers itself. *)
      [ E_edge (pool_stem p) ]
  | P_lt t ->
      let c = edge_expand [] t in
      let sz = size_of_name (value_name t) in
      if List.length c * w4 <> sz then
        fail
          ("the edge walk flattened " ^ show_lt t ^ " to "
          ^ string_of_int (List.length c) ^ " word(s), but the layout gives it "
          ^ string_of_int sz ^ " bytes")
      else begin
        if List.length c > 1 then incr edge_flattened;
        c
      end
  | P_leaf _ -> []

(* A row is the cell's fields in order, so an array field covers the words the fields before it
   did not: `text` is { len; code[MAX_WORD] }, and the count of codes is the cell's width minus
   the length word rather than a number any declaration states.  An element type whose classes do
   not DIVIDE the remaining words is a refusal, because the alternative is a table that stops
   short of the cell and a collector that never scans its last words. *)
let edge_row p width positions =
  let rec go consumed = function
    | [] -> []
    | P_leaf elem :: rest ->
        let per = edge_classes_of p (P_lt elem) in
        let left = width - consumed in
        let per_words = List.length per in
        if left <= 0 || left mod per_words <> 0 then
          fail
            ("the leaf cell " ^ p.p_elem ^ " leaves " ^ string_of_int left
            ^ " word(s) for elements of " ^ string_of_int per_words
            ^ " (" ^ show_lt elem ^ "): the array the struct declares does not fill the cell \
               the layout sized")
        else
          let groups = List.init (left / per_words) (fun _ -> per) in
          List.flatten groups @ go width rest
    | pos :: rest ->
        let c = edge_classes_of p pos in
        c @ go (consumed + List.length c) rest
  in
  go 0 positions

(* The tables in the order the pools are declared, so the header reads top-down: capacity,
   runtime, edges — three sections about one object.  Only SIZED pools get one, which is
   §6.6's rule applied to §6.7's instrument: an undefined array has no cell to describe, and
   the report says which pools that left out rather than the table section silently agreeing
   to be shorter.  Rows are padded to the cell's width with UNUSED, which is what makes
   reading past a constructor's arity a class instead of an accident; a row WIDER than the
   cell is a refusal, because the only way that happens is the recorded positions and the
   emitted struct disagreeing, and the alternative is a table that drops an edge — i.e. a live
   cell the collector frees. *)
let edge_tables () =
  List.map
    (fun p ->
      let s = pool_stem p in
      let sh =
        match Hashtbl.find_opt shapes s with
        | Some sh -> sh
        | None ->
            fail
              ("pool " ^ p.p_arr
              ^ " carries no recorded cell shape, so §6.7's reachability rule cannot be\n\
                 \   derived for it: every rule that registers a pool records its rows in\n\
                 \   the same breath, so an unshaped pool is a pool that grew elsewhere")
      in
      if sh.s_elem <> p.p_elem then
        fail
          ("pool " ^ p.p_arr ^ " was registered with cell " ^ p.p_elem
          ^ " but the recorded shape names " ^ sh.s_elem);
      let width = edge_cell_words p.p_elem in
      let rows =
        List.map
          (fun r ->
            let c = edge_row p width r.r_pos in
            if List.length c > width then
              fail
                ("row " ^ r.r_label ^ " of pool " ^ p.p_arr ^ " flattens to "
                ^ string_of_int (List.length c)
                ^ " words inside a cell of " ^ string_of_int width)
            else if not sh.s_tagged && List.length c <> width then
              fail
                ("the untagged cell " ^ p.p_arr ^ " describes "
                ^ string_of_int (List.length c) ^ " of its "
                ^ string_of_int width
                ^ " words.  Only a constructor row may be shorter than its cell, because\n\
                 \   padding is that row's arity; padding a cell's own row would hide a field\n\
                 \   this reading never walked")
            else (r.r_label, c @ List.init (width - List.length c) (fun _ -> E_unused)))
          sh.s_rows
      in
      (p, sh, width, rows))
    (sized_pools ())

(* Declarations in the header, definitions in the runtime's translation unit: the same split
   §6.6 used, because a table the collector reads at run time is a runtime object.  The row
   width and the row count are MACROS rather than literals in the array dimension, so the
   gate can re-derive them from the emitted text and compare against the typedef below, which
   is the compiler's own answer to "does this row cover the cell exactly?". *)
let edge_decl p sh width rows =
  let s = pool_stem p in
  let u = String.uppercase_ascii s in
  let rows_n = List.length rows in
  let leaf_row =
    match rows with
    | [ (_, c) ] -> List.for_all (fun x -> x = E_scalar) c
    | _ -> false
  in
  let gloss =
    if sh.s_tagged then
      "one row per constructor, in the artifact's declaration order"
    else if leaf_row then
      "the cell is a LEAF: every word is a value, so its scan copies it and follows nothing"
    else "a cons cell: the element inline in the cell, then the tail"
  in
  String.concat ""
    [
      Printf.sprintf "/* %s: %d row%s x %d word%s per %s — %s */\n" s rows_n
        (if rows_n = 1 then "" else "s") width (if width = 1 then "" else "s") sh.s_elem
        gloss;
      Printf.sprintf "#define JPL_%s_NPOS %du    /* words per cell */\n" u width;
      Printf.sprintf
        "#define JPL_%s_NROWS %du   /* rows: %s */\n" u rows_n
        (if sh.s_tagged then "constructors" else "1, an untagged cell");
      Printf.sprintf "#define JPL_%s_NEDGE (JPL_%s_NROWS * JPL_%s_NPOS)\n" u u u;
      Printf.sprintf "extern const jpl_nat jpl_%s_edge[JPL_%s_NEDGE];\n" s u;
      Printf.sprintf
        "typedef char jpl_check_%s_edge_covers_the_cell[((JPL_%s_NPOS * %du) == sizeof (%s)) ? 1 : -1];\n\n"
        s u w4 sh.s_elem;
    ]

(* One row per line-group of six words, with the constructor or cell labelled above it: the
   label is a comment, so what a reader trusts is the entry, not the label — but a label that
   matches the `.mli`'s own constructor names is what makes a wrong table visible in review. *)
let edge_chunk n l =
  let rec go k acc rest =
    match (k, rest) with
    | 0, _ | _, [] -> (List.rev acc, rest)
    | _, x :: xs -> go (k - 1) (x :: acc) xs
  in
  go n [] l

let edge_definition s rows =
  let body =
    List.map
      (fun (label, c) ->
        let items = List.map edge_class_macro c in
        let rec go l =
          match l with
          | [] -> []
          | _ ->
              let a, b = edge_chunk 6 l in
              String.concat ", " a :: go b
        in
        "  /* " ^ label ^ " */\n  "
        ^ String.concat "\n  " (List.map (fun x -> x ^ ",") (go items)) ^ "\n")
      rows
  in
  String.concat ""
    [
      Printf.sprintf "const jpl_nat jpl_%s_edge[JPL_%s_NEDGE] = {\n" s
        (String.uppercase_ascii s);
      String.concat "" body;
      "};\n\n";
    ]

(* One class-defining block, then one declaration and one definition per pool.  The ids come
   from the registry, so a number typed wrong here fails a check typedef somewhere else rather
   than becoming a table that points at nothing. *)
let edge_section () =
  let ids = edge_pool_ids () in
  let tables = edge_tables () in
  let unsized = List.filter (fun p -> p.p_count = None) (List.rev !pools) in
  emit edges_b "/* ── the pool edge tables (JPL.md §6.7, 5-B.3b-ii-b-2a): what each WORD of a\n\
                \   pool cell means, so a collector's reachability rule is read from a table\n\
                \   the layout derived rather than invented by a body.  R7's slots are one\n\
                \   uint32_t each and cannot tell a handle from a count; this is the second\n\
                \   reading of the same declarations that says which is which — one class per\n\
                \   word, because R3 keeps a list's element inline, so a pair cell's element\n\
                \   is two words and no second table is needed to say how a field splits.  A\n\
                \   by-value aggregate whose words mean something only under a tag (an option,\n\
                \   a fat variant) has NO reading here: the emitter refuses one rather than\n\
                \   guessing which words are live.  Declarations here, definitions in\n\
                \   sh_run_jpl_pools.c with the runtime they serve, and every row width pinned\n\
                \   against its cell's sizeof by the typedef under it. ── */\n";
  emit edges_b "#define JPL_EDGE_SCALAR 0u   /* a value: nothing to forward */\n\
                #define JPL_EDGE_UNUSED 1u   /* past this row's arity: a word never written */\n";
  List.iter
    (fun (stem, id) ->
      emit edges_b "#define JPL_EDGE_TO_%s_POOL %du   /* target: jpl_%s_pool */\n"
        (String.uppercase_ascii stem) id stem)
    (Hashtbl.to_seq ids |> List.of_seq |> List.sort (fun (a, _) (b, _) -> String.compare a b));
  emit edges_b "#define JPL_EDGE_POOL_COUNT %du   /* targets an edge may name */\n\n"
    (Hashtbl.length ids);
  edge_census := [];
  List.iter
    (fun (p, sh, width, rows) ->
      Buffer.add_string edges_b (edge_decl p sh width rows);
      Buffer.add_string edge_defs_b (edge_definition (pool_stem p) rows);
      let sc, un, ed =
        List.fold_left
          (fun (a, b, c) (_, words) ->
            List.fold_left
              (fun (a, b, c) e ->
                match e with
                | E_scalar -> (a + 1, b, c)
                | E_unused -> (a, b + 1, c)
                | E_edge _ -> (a, b, c + 1))
              (a, b, c) words)
          (0, 0, 0) rows
      in
      edge_census :=
        (pool_stem p, sh.s_elem, List.length rows, width, sc, un, ed) :: !edge_census)
    tables;
  if unsized <> [] then begin
    emit edges_b "/* NO EDGE TABLE for: ";
    List.iter (fun p -> emit edges_b "%s " p.p_arr) unsized;
    emit edges_b "— an unsized pool is neither defined nor handed out (§6.6), so it has no\n\
                  \   cell for a row to describe.  The report counts them; the gate asserts\n\
                  \   tables == pools_with_capacity, which is this sentence in a number. */\n\n"
  end

let pool_definition p =
  let s = pool_stem p in
  let m = pool_macro p in
  String.concat ""
    [
      Printf.sprintf "/* ── %s: %s cells of %s, handled as %s ── */\n" s m p.p_elem
        p.p_handle;
      Printf.sprintf "%s %s[%s];\n" p.p_elem p.p_arr m;
      Printf.sprintf "jpl_ref jpl_%s_next = 1u;   /* index 0 is JPL_NIL and stays\
                      \ reserved (§6.6) */\n"
        s;
      Printf.sprintf "jpl_ref jpl_%s_peak = 0u;\n" s;
      Printf.sprintf "jpl_ref jpl_%s_taken = 0u;\n" s;
      Printf.sprintf "jpl_ref jpl_%s_refused = 0u;\n\n" s;
      Printf.sprintf "%s jpl_%s_alloc(void) {\n  %s h = JPL_NIL;\n" p.p_handle s p.p_handle;
      Printf.sprintf "  if (jpl_%s_next < %s) {\n    h = jpl_%s_next;\n" s m s;
      Printf.sprintf "    jpl_%s_next = jpl_%s_next + 1u;\n" s s;
      Printf.sprintf "    if (jpl_%s_peak < h) {\n      jpl_%s_peak = h;\n    }\n" s s;
      Printf.sprintf "    if (jpl_%s_taken < JPL_REF_TOP) {\n      jpl_%s_taken = jpl_%s_taken + 1u;\n    }\n" s s s;
      "  } else {\n";
      Printf.sprintf "    if (jpl_%s_refused < JPL_REF_TOP) {\n      jpl_%s_refused = jpl_%s_refused + 1u;\n    }\n" s s s;
      "  }\n  return h;\n}\n\n";
      Printf.sprintf "jpl_ref jpl_%s_reset(void) {\n" s;
      "  /* next >= 1u by construction, so this subtraction cannot wrap. */\n";
      Printf.sprintf "  jpl_ref returned = jpl_%s_next - 1u;\n  jpl_%s_next = 1u;\n" s s;
      "  return returned;\n}\n\n";
      Printf.sprintf "jpl_bool jpl_%s_is_live(jpl_ref h) {\n  jpl_bool r = JPL_FALSE;\n" s;
      Printf.sprintf "  if ((h != JPL_NIL) && (h < jpl_%s_next)) {\n    r = JPL_TRUE;\n" s;
      "  }\n  return r;\n}\n\n";
    ]

let pools_c_text ml mli =
  let b = Buffer.create 8192 in
  emit b "/* GENERATED by verify/c/jpl_emit.ml from\n\
          \   %s\n\
          \   %s\n\
          \   DO NOT EDIT — the gate re-runs the emitter and byte-compares this file.\n\
          \   sh_run_jpl_pools.c — the pool DEFINITIONS and the JPL.md §6.6 runtime: the\n\
          \   only C in this tree that owns a mutable static, and the reason a handle in\n\
          \   sh_run_jpl.h points at something rather than at a comment.  No number below\n\
          \   is typed: every dimension is the header's own JPL_POOL_* macro. */\n\n\
          #include \"sh_run_jpl.h\"\n\n" ml mli;
  List.iter (fun p -> Buffer.add_string b (pool_definition p)) (sized_pools ());
  emit b "/* ── §6.7's edge tables: one row per constructor (or per untagged cell), one class\n\
          \   per word of the cell, in the cell's own field order.  The dimension is the\n\
          \   header's own JPL_<stem>_NEDGE and the width under it is pinned to the cell's\n\
          \   sizeof by jpl_check_<stem>_edge_covers_the_cell, so a table's length is a\n\
          \   property of the cell it describes rather than of how many entries were typed.\n\
          \   Every entry names its class; no bare number appears in a row. ── */\n";
  Buffer.add_string b (Buffer.contents edge_defs_b);
  let unsized = List.filter (fun p -> p.p_count = None) (List.rev !pools) in
  if unsized <> [] then begin
    emit b "/* UNDEFINED POOLS — declared by the layout, sized by nothing, so they\n\
            \   get neither a definition here nor an allocator (§6.6):\n";
    List.iter (fun p -> emit b "     %s\n" p.p_arr) unsized;
    emit b "*/\n\n"
  end;
  emit b "/* One saturating sum, so a breach has one readable place (§4.2).  Static on\n\
          \   purpose: the only exported names are the per-pool ones the header declares. */\n\
          static jpl_nat jpl_pools_add_saturating(jpl_nat a, jpl_nat b) {\n\
          \  jpl_nat r = a;\n\
          \  if (r > (JPL_REF_TOP - b)) {\n\
          \    r = JPL_REF_TOP;\n\
          \  } else {\n\
          \    r = r + b;\n\
          \  }\n\
          \  return r;\n\
          }\n\n\
          jpl_nat jpl_pools_refusals(void) {\n\
          \  jpl_nat r = 0u;\n";
  List.iter
    (fun p -> emit b "  r = jpl_pools_add_saturating(r, jpl_%s_refused);\n" (pool_stem p))
    (sized_pools ());
  emit b "  return r;\n}\n";
  Buffer.contents b

let header_text ml mli =
  let b = Buffer.create 16384 in
  emit b "/* GENERATED by verify/c/jpl_emit.ml from\n\
  \   %s\n\
  \   %s\n\
  \   DO NOT EDIT — the gate re-runs the emitter and byte-compares this file.\n\
  \   JPL.md §6 is the normative contract; §9.2 decision 3 is why a recursive type\n\
  \   is a handle into a static pool and never an inline array.  This is the TYPE\n\
  \   LAYER only: no function body is emitted here, and JPL.5-B.3 owns the\n\
  \   lowering into it.  The pool runtime below (JPL.md §6.6) is declarations only\n\
  \   as well: the pool arrays themselves and the allocator bodies are in the\n\
  \   generated translation unit sh_run_jpl_pools.c, which includes this header.\n\
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
  Buffer.add_string b (Buffer.contents runtime_b);
  Buffer.add_string b (Buffer.contents edges_b);
  emit b "\n/* ── prototypes for the shipped closure: parameter names are the artifact's\n\
  \   own, and every type comes from the .mli signature mapped by the rule set. */\n";
  Buffer.add_string b (Buffer.contents protos_b);
  Buffer.add_string b "\n#endif /* SH_RUN_JPL_H */\n";
  Buffer.contents b

(* ────────────── 7. prototypes, constants, and what is PENDING ───────────── *)

(* `c_fn` and `c_upper` are the SHARED reader's naming rules now (jpl_ast.ml §9), the same
   ones the census's ABI renders prototypes through: two header layers compiled as one
   translation unit cannot own two spellings of one symbol. *)

(* How many closure bindings call this one: the measurement that turns "needs a
   monomorphization" from an assertion into a number. *)
let callers_of n =
  Hashtbl.fold
    (fun _ m acc -> if Hashtbl.mem m.edges n then acc + 1 else acc)
    closure 0

(* The cap bindings are folded once into the JPL_MAX_* macros above; re-emitting them as
   JPL_C_* would be a second name for one number.  WHICH ones they are is derived from the
   artifact's own cap table (`cap_macro_of_data`, in the reader), not from a list typed
   here: 5-B.3a's census asks the same question of the same ten names, and a hand-written
   copy in this file would be a second model of a fact the extraction already carries. *)

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
              (match cap_macro_of_data nm with
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
  section "POOL RUNTIME (JPL.md §6.6): one bounded region per sized pool";
  let ps = sized_pools () in
  let unsized = List.filter (fun p -> p.p_count = None) (List.rev !pools) in
  Printf.printf "  %-22s %-26s %-30s %-26s %s\n" "stem" "capacity macro" "cells of"
    "handled as" "runtime names";
  List.iter
    (fun p ->
      Printf.printf "  %-22s %-26s %-30s %-26s _alloc, _reset, _is_live, _next, _peak,\
                    \ _taken, _refused\n"
        (pool_stem p) (pool_macro p) p.p_elem p.p_handle)
    ps;
  if unsized <> [] then
    Printf.printf "  NO RUNTIME for: %s — unsized pools can be neither defined nor handed\
                   \ out,\n   which is §6.6's rule cutting both ways.\n"
      (String.concat ", " (List.map (fun p -> p.p_arr) unsized));
  Printf.printf "\n  Reclamation is at REGION granularity: a reset returns every cell at once,\n\
    \  because a per-cell free needs the reachability rule §6.5's ii-b-2 owns before it is\n\
    \  safe, not a function.  A reset does not clear cells, and `is_live` is the guard rail\n\
    \  that makes a handle carried across one observable (§6.6).  `peak` is the quantity\n\
    \  decision 4 said no walk over the artifact's text could produce — a run measures it.\n\
    \  With no kernel that allocates yet, every peak in this tree is 0: this is the\n\
    \  instrument, not the number, and the gate prints that zero as one.\n";
  section "RUNTIME SUMMARY (the keys verify/c/jpl_emit.sh asserts — a missing key is a failure)";
  let n = List.length ps in
  let cells =
    List.fold_left
      (fun a p -> match p.p_count with Some v -> a + v | None -> a)
      0 (List.rev !pools)
  in
  let bytes =
    List.fold_left
      (fun a p -> match p.p_count with Some v -> a + v * size_of_name p.p_elem | None -> a)
      0 (List.rev !pools)
  in
  let rt_names = runtime_names () in
  let closure_names = List.map c_fn members in
  let collide =
    List.filter (fun x -> List.mem x closure_names) rt_names
  in
  let handles_ok =
    List.length (List.filter (fun p -> Hashtbl.mem rows p.p_handle) ps)
  in
  List.iter
    (fun (k, v, gloss) -> Printf.printf "  %-40s %8d   %s\n" k v gloss)
    [
      ("pools_declared", List.length !pools, "arrays the layout section declares");
      ("pools_with_capacity", n, "the ones sized from the cap table");
      ("pools_without_capacity", List.length unsized, "sized by nothing, so runtime-free");
      ("allocators_emitted", n, "one jpl_<stem>_alloc per sized pool");
      ("resets_emitted", n, "one jpl_<stem>_reset per sized pool");
      ("live_checks_emitted", n, "one jpl_<stem>_is_live per sized pool");
      ("counters_emitted", 4 * n, "next, peak, taken, refused per sized pool");
      ("pool_arrays_defined", n, "arrays the generated translation unit defines");
      ("refusals_sum_terms", n, "terms in jpl_pools_refusals's saturating sum");
      ("allocator_handles_defined_in_layout", handles_ok, "an allocator's return type is a typedef the layout emitted");
      ("runtime_names_colliding_with_prototypes", List.length collide, "a runtime name that is also a closure symbol — must be 0");
      ("runtime_cells_total", cells, "cells across every sized pool");
      ("runtime_bytes_total", bytes, "bytes of static storage the pools occupy");
    ];
  if n = 0 then begin
    Printf.printf "RUNTIME REFUSED: %d sized pools, so the runtime would be an empty file.\n"
      n;
    exit 1
  end;
  if collide <> [] then begin
    Printf.printf "RUNTIME REFUSED: the generated names %s collide with closure prototypes.\n"
      (String.concat ", " collide);
    Printf.printf "   Two definitions of one symbol in one translation unit is not a style\n\
      \   point, and §6.3's ABI and §6.6's runtime share the namespace.\n";
    exit 1
  end;
  if handles_ok <> n then begin
    Printf.printf "RUNTIME REFUSED: %d of %d allocators return a handle the layout never\
                   \ typedef'd.\n"
      (n - handles_ok) n;
    exit 1
  end;
  Printf.printf "\nRUNTIME EMITTED: %d pools, %d cells, %s of static storage, one bounded\
                 \ region each.\n"
    n cells (kb bytes);
  section "EDGE TABLES (JPL.md §6.7, 5-B.3b-ii-b-2a): one class per WORD of every sized pool";
  let cs = List.rev !edge_census in
  Printf.printf "  %-22s %-30s %5s %6s %8s %8s %8s\n" "stem" "cell" "rows"
    "words" "scalar" "unused" "edges";
  List.iter
    (fun (s, elem, rows, width, sc, un, ed) ->
      Printf.printf "  %-22s %-30s %5d %6d %8d %8d %8d\n" s elem rows width sc un ed)
    cs;
  let e_rows = List.fold_left (fun a (_, _, r, _, _, _, _) -> a + r) 0 cs in
  let sum f = List.fold_left (fun a c -> a + f c) 0 cs in
  let e_entries = sum (fun (_, _, r, w, _, _, _) -> r * w) in
  let e_scalars = sum (fun (_, _, _, _, s, _, _) -> s) in
  let e_unuseds = sum (fun (_, _, _, _, _, u, _) -> u) in
  let e_edges = sum (fun (_, _, _, _, _, _, d) -> d) in
  Printf.printf "\n  %d tables, %d rows, %d classes, and the three of them partition the\n\
    \  table exactly: %d scalar + %d unused + %d edges = %d.\n\
    \  %d position(s) flattened a by-value aggregate into its leaf words — the sites where a\n\
    \  pooled cell holds an inline pair, which is why the table is per word and not per field\n\
    \  (§6.7).  A per-field table would have needed a second table saying how the field\n\
    \  splits; this one pins its own width against the cell's sizeof in the header instead.\n\
    \  An edge may name %d target pools — every pool this header declares.\n"
    (List.length cs) e_rows e_entries e_scalars e_unuseds e_edges e_entries
    !edge_flattened (List.length cs);
  section "EDGE SUMMARY (the keys verify/c/jpl_emit.sh asserts — a missing key is a failure)";
  List.iter
    (fun (k, v, gloss) -> Printf.printf "  %-40s %8d   %s\n" k v gloss)
    [
      ("edge_tables_emitted", List.length cs, "one jpl_<stem>_edge per sized pool");
      ("edge_rows_derived", e_rows, "constructors, plus one row per untagged cell");
      ("edge_entries_derived", e_entries, "classes across every table = rows x words per cell");
      ("edge_class_scalars", e_scalars, "words holding a value: nothing to forward");
      ("edge_class_unuseds", e_unuseds, "words past a constructor's arity: never written");
      ("edge_class_edges", e_edges, "words holding a handle: what evacuation must copy");
      ("edge_target_pools", List.length cs, "pools an edge may name, from the registry");
      ("edge_aggregates_flattened", !edge_flattened, "positions whose type is inline by value");
      ("edge_width_checks_emitted", List.length cs, "jpl_check_<stem>_edge_covers_the_cell typedefs");
      ("edge_class_partition_residual", e_entries - (e_scalars + e_unuseds + e_edges), "must be 0: the classes are a partition");
    ];
  if cs = [] then begin
    Printf.printf "EDGE REFUSED: %d sized pools produced no table.\n" (List.length cs);
    exit 1
  end;
  if e_entries <> e_scalars + e_unuseds + e_edges then begin
    Printf.printf "EDGE REFUSED: %d entries split into %d + %d + %d.\n" e_entries e_scalars
      e_unuseds e_edges;
    Printf.printf "   A word with no class is a live cell a collector frees, and the only\n\
      \   honest reading of a mismatch is that the walk stopped early.\n";
    exit 1
  end;
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

let main ml mli out_h out_c roots =
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
  runtime_section ();
  edge_section ();
  family_check ();
  let oc = open_out out_h in
  output_string oc (header_text ml mli);
  close_out oc;
  let oc2 = open_out out_c in
  output_string oc2 (pools_c_text ml mli);
  close_out oc2;
  report ml mli members needed nf nv np

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [ ml; mli; out_h; out_c ] -> main ml mli out_h out_c default_roots
  | [ ml; mli; out_h; out_c; rs ] -> main ml mli out_h out_c (split_commas rs)
  | _ ->
      fail "usage: jpl_emit <ml> <mli> <out.h> <out.c> [comma-separated-roots]"
