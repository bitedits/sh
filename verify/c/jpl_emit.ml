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

(* JPL.md §6.7 paragraph 4 reads that factor as a NUMBER OF INTERVALS rather than as slack: a
   copy-then-swap boundary needs one space holding the live set and one receiving the copies, so
   `headroom` spaces of `cap + 1` indices each, and an array of `headroom * (cap + 1)` indices.
   The `+ 1` is the off-by-one §6.6 made a gate rung out of, now charged PER SPACE because each
   region reserves its own index 0: a capacity of exactly `2 * cap` would hand a region only
   `cap - 1` cells, i.e. one less live cell than the artifact declares, and the shortfall would
   surface at run time as the `BLimit` the model does not produce.  Every number below is derived
   from the cap the registering rule supplied, so nothing else in this file states a capacity. *)
let spaces = headroom

let region_indices cap = cap + 1
let interval_indices cap = spaces * region_indices cap

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
  { p_elem : string; p_arr : string;
    (* The artifact's cap: the cells ONE space must serve (§6.7 paragraph 4).  Kept beside the
       array's total dimension rather than recovered from it, because the two are the numbers the
       emitted typedefs pin against each other — `2 * (cap + 1)` read back by integer division
       would agree with an array that was sized wrong, and the whole point of the `+ 1` is that
       it is NOT slack this file is free to lose. *)
      p_cap : int option;
      p_count : int option;
      p_from : string; p_why : string;
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

(* The interval macros, spelled from the stem here and nowhere else.  Six per pool, all
   read through one prefix, because the header's `#define`s, the runtime bodies that expand
   them and the report that counts them have to agree on seven characters of naming — a
   second spelling is the mistake §6.6's derived-name rule exists to prevent.  `CAP` is the
   artifact's cells per space, `SPACE` the indices a space occupies (its own reserved nil
   plus those cells), and the four bounds that follow are the pair the runtime selects with
   `jpl_pools_space`, which is why they are macros rather than numbers in the bodies: a body
   that said `2 * cap + 2` anywhere would be a second model of the capacity. *)
let pool_upper p = String.uppercase_ascii (pool_stem p)
let m_cap p = "JPL_" ^ pool_upper p ^ "_CAP"
let m_space p = "JPL_" ^ pool_upper p ^ "_SPACE"
let m_lo_base p = "JPL_" ^ pool_upper p ^ "_LO_BASE"
let m_hi_base p = "JPL_" ^ pool_upper p ^ "_HI_BASE"
let m_cur_base p = "JPL_" ^ pool_upper p ^ "_CUR_BASE"
let m_cur_top p = "JPL_" ^ pool_upper p ^ "_CUR_TOP"

(* §6.7 paragraph 5bis's other pair.  A boundary SWAPS FIRST, so after the flip `CUR_*` already
   names the interval the copies go into and §6.6's allocator needs no to-space twin; what no
   existing macro names is the region being read FROM, whose handles `evac` must bound before it
   indexes `origin` with them.  Hence OTHER, not TO: naming it would invent a second truth about
   which half the boundary fills. *)
let m_other_base p = "JPL_" ^ pool_upper p ^ "_OTHER_BASE"
let m_other_top p = "JPL_" ^ pool_upper p ^ "_OTHER_TOP"
let interval_macros =
  [ m_cap; m_space; m_lo_base; m_hi_base; m_cur_base; m_cur_top; m_other_base; m_other_top ]
let spaces_macro = "JPL_POOL_SPACES"
let space_global = "jpl_pools_space"
let swap_fn = "jpl_pools_swap"

(* An origin entry is a handle, so the parallel array is `jpl_ref` per INDEX of the pool, not
   per cell: index 0 and index cap+1 are each region's reserved nil and get a slot they can
   never be asked about.  §6.7 paragraph 4's price is that width x the same domain. *)
let origin_arr p = "jpl_" ^ pool_stem p ^ "_origin"

(* §6.6's rule is bidirectional: no capacity without an allocator, and no allocator for a
   pool that cannot be sized.  The unsized pools are therefore excluded from the runtime
   and REPORTED, never skipped quietly — the report's pools_without_capacity key is the
   count, and the gate asserts the allocators and the sized pools are the same number. *)
let sized_pools () = List.filter (fun p -> p.p_count <> None) (List.rev !pools)

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

(* The same argument for the cell's MEMBER NAMES.  §6.7 paragraph 5bis's scan rewrites one
   word of a to-space cell, which needs an index-to-field mapping, and the only sound source
   for it is the struct the layout rule just wrote: a path typed into the accessor generator
   would be a second model of the cell, free to drift from the typedef above it.  So each rule
   that lays out a POOLED cell registers its members here, in the order it emitted them:
     fs_path   — the member name as written, or the prefix an expansion walks under,
     fs_words  — how many words that member occupies (the layout's own byte size / 4),
     fs_expand — the declared type when the member is an aggregate held BY VALUE and its words
                 need their own paths (`(text * text)`'s element: `_hd.p_fst`, `_hd.p_snd`),
     fs_array  — the member is an array, so one ranged arm covers it and the cell's own width
                 supplies the count, exactly as edge_row does for the classes. *)
type field_spec =
  { fs_path : string; fs_words : int; fs_expand : lt option; fs_array : bool }

let cell_fields : (string, field_spec list) Hashtbl.t = Hashtbl.create 8

let record_fields stem fs =
  if not (Hashtbl.mem cell_fields stem) then
    Hashtbl.replace cell_fields stem fs

(* A pool's recorded shape, and the one cross-check that goes with it: the cell the rows describe
   must be the cell the pool registered.  Both §6.7's table (rows) and its scan (word accessors)
   read the same registry, so an unshaped pool is refused once, here, in two flavours. *)
let pool_shape p =
  match Hashtbl.find_opt shapes (pool_stem p) with
  | Some sh ->
      if sh.s_elem <> p.p_elem then
        fail
          ("pool " ^ p.p_arr ^ " was registered with cell " ^ p.p_elem
          ^ " but the recorded shape names " ^ sh.s_elem)
      else sh
  | None ->
      fail
        ("pool " ^ p.p_arr
        ^ " carries no recorded cell shape, so §6.7's reachability rule cannot be\n\
           \   derived for it: every rule that registers a pool records its rows in\n\
           \   the same breath, so an unshaped pool is a pool that grew elsewhere")

(* Every symbol the runtime puts in the shared C namespace.  The gate needs this list
   because §6.3's ABI and §6.6's runtime both emit `jpl_<something>` into one translation
   unit, so a collision is not a style point but a duplicate definition.  badtag is in it only
   for a pool whose cell HAS a tag, which is the same condition the declaration and the body
   are emitted under: a name listed here for a pool that never declares it would make this
   list a claim about the runtime rather than a reading of it. *)
let runtime_names () =
  let base =
    List.concat_map
      (fun p ->
        let s = pool_stem p in
        [ "jpl_" ^ s ^ "_next"; "jpl_" ^ s ^ "_peak"; "jpl_" ^ s ^ "_taken";
          "jpl_" ^ s ^ "_refused"; "jpl_" ^ s ^ "_origin"; "jpl_" ^ s ^ "_scan";
          "jpl_" ^ s ^ "_copied"; "jpl_" ^ s ^ "_forwarded"; "jpl_" ^ s ^ "_badref" ]
        @ (if (pool_shape p).s_tagged then [ "jpl_" ^ s ^ "_badtag" ] else [])
        @ [ "jpl_" ^ s ^ "_alloc"; "jpl_" ^ s ^ "_reset"; "jpl_" ^ s ^ "_is_live";
            "jpl_" ^ s ^ "_word_at"; "jpl_" ^ s ^ "_word_put"; "jpl_" ^ s ^ "_evac";
            "jpl_" ^ s ^ "_queue_start"; "jpl_" ^ s ^ "_scan_one"; "jpl_" ^ s ^ "_drain";
            "jpl_" ^ s ^ "_edge" ])
      (sized_pools ())
  in
  if base = [] then []
  else
    base
    @ [ "jpl_pools_refusals"; space_global; swap_fn; "jpl_pools_unclassified";
        "jpl_pools_evac_by_class" ]

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
      p_cap = Some (c ()).c_words;
      p_count = Some (interval_indices (c ()).c_words);
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
  (* The cell's members, in the order the struct above writes them.  The array's element
     count is MAX_WORD, the same number the typedef under the struct pins, and §6.7
     paragraph 5bis reaches those words with ONE ranged arm rather than one arm per code. *)
  record_fields "word"
    [ { fs_path = "wt_len"; fs_words = 1; fs_expand = None; fs_array = false };
      { fs_path = "wt_code";
        fs_words = (c ()).c_word;
        fs_expand = None;
        fs_array = true } ];
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
      p_cap = Some cap; p_count = Some (interval_indices cap);
      p_from = macro; p_why = why;
      p_handle = handle }
    :: !pools;
  (* One row, because a cons cell has no tag: the hd is a payload of the element type — by
     value if the element is an aggregate, an edge if it is itself a handle — and the tail is
     an edge into this pool. *)
  record_shape k cell false
    [ { r_label = show_lt e ^ " cell"; r_pos = [ P_lt e; P_tail ] } ];
  (* The element is INLINE, so its words are reached through `_hd` and the pair case needs
     dotted paths — which is why this registers the element's TYPE and not a word count: the
     accessor walk below expands it with the same sizes the layout memoised. *)
  record_fields k
    [ { fs_path = k ^ "_hd";
        fs_words = esz / w4;
        fs_expand = Some e;
        fs_array = false };
      { fs_path = k ^ "_next"; fs_words = 1; fs_expand = None; fs_array = false } ];
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
      p_cap = Some cap; p_count = Some (interval_indices cap);
      p_from = cap_macro; p_why = why;
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
  (* The node's members are positional by construction — R7 gives every constructor the same
     cell — so the accessor walk needs no type here: a slot is one word whatever it holds, and
     which of them mean anything is the tag's answer, which the edge table already carries. *)
  record_fields nm
    ({ fs_path = nm ^ "_tag"; fs_words = 1; fs_expand = None; fs_array = false }
     :: List.init slots (fun i ->
            { fs_path = Printf.sprintf "%s_slot%d" nm i;
              fs_words = 1;
              fs_expand = None;
              fs_array = false }));
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

(* §6.7 paragraph 4's arithmetic, checked where it is emitted rather than assumed: the array
   dimension is registered as SPACES x (cap + 1) by the rule that sized the pool, and every bound
   below is read off that same registered cap.  A pool whose dimension is not SPACES x (cap + 1)
   is refused HERE, before a single file is written, because every emitted typedef would still
   pass — they are derived from the same two numbers — while the runtime handed out one cell fewer
   per space than the artifact declares, and that shortfall surfaces as a `BLimit` no lemma
   produces.  A cap without a dimension (or the reverse) is the same refusal in a different
   costume: §6.6's rule cutting both ways, now read through §6.7. *)
let interval_check p =
  match (p.p_cap, p.p_count) with
  | (Some cap, Some n) when n <> interval_indices cap ->
      Printf.printf
        "INTERVAL REFUSED: %s registers %d indices for an artifact cap of %d cells, but %d\
        \ spaces of (cap + 1) is %d.\n"
        p.p_arr n cap spaces (interval_indices cap);
      Printf.printf "   Each space reserves its own index 0, so a dimension of 2 * cap would\
        \ serve cap - 1\n   cells: one less live cell than sh_jpl.v §1 declares, discovered only\
        \ when a run\n   saturates.  The registering rule supplies the cap and this file\
        \ derives the dimension;\n   a disagreement between them is a typing mistake in the\
        \ one place the capacity is stated.\n";
      exit 1
  | (Some _, None) | (None, Some _) ->
      Printf.printf
        "INTERVAL REFUSED: %s carries %s without %s.\n" p.p_arr
        (if p.p_cap <> None then "a cap" else "a dimension")
        (if p.p_cap <> None then "its dimension" else "its cap");
      Printf.printf "   One array, two intervals: neither half of that can be emitted from\
        \ only one number.\n";
      exit 1
  | _ -> ()

let pools_section () =
  emit pools_b "/* ── the pools.  Definitions live in the emitted translation unit\n\
                \   (JPL.md §6: no dynamic allocation); they are declared here so every\n\
                \   consumer compiles against one capacity.  Index 0 is JPL_NIL and is\n\
                \   never allocated, so a capacity counts the reserved cell too — and\n\
                \   since §6.7's ii-b-2b there is one reserved index PER SPACE, because\n\
                \   each interval is a region in its own right: the array below is not two\n\
                \   pools, it is one index domain holding a from-space and a to-space that\n\
                \   move together when %s() says so. ── */\n"
    swap_fn;
  emit pools_b "#define %s %du   /* §6.7 paragraph 4: the headroom factor IS a number of\n\
                \                        intervals — %d — rather than slack: one space holds the\n\
                \                        live set and the rest receive the copies a step boundary\n\
                \                        builds before releasing the original */\n\
                extern jpl_nat %s;   /* which interval is current; one writer, %s() */\n\n"
    spaces_macro spaces spaces space_global swap_fn;
  List.iter
    (fun p ->
      interval_check p;
      match p.p_count with
      | Some n ->
          let cap = Option.get p.p_cap in
          let macro = pool_macro p in
          emit pools_b "#define %s %du   /* %d spaces x (cap + 1) indices: %d cells per space\n\
                        \                        each keeping its own reserved 0; from %s; %s */\n\
                        #define %s %du   /* cells ONE space serves = the artifact's number */\n\
                        #define %s (%s + 1u)   /* indices a space occupies */\n\
                        #define %s 0u\n\
                        #define %s %s\n\
                        #define %s (%s * %s)   /* the current interval, read through the\n\
                        \                        space indicator */\n\
                        #define %s (%s + %s)\n\
                        #define %s (((%s + 1u) %% %s) * %s)   /* the interval a boundary reads\n\
                        \                        FROM once it has swapped: the swap makes CUR_*\n\
                        \                        the space the copies land in, so the pair still\n\
                        \                        worth naming is the one being abandoned */\n\
                        #define %s (%s + %s)\n\
                        extern %s %s[%s];\n\
                        extern jpl_ref %s[%s];   /* §6.7: where a copied cell came from, one\n\
                        \                        entry per INDEX so a handle is the only key;\n\
                        \                        zero is JPL_NIL, i.e. not copied from anywhere\n\
                        \                        (paragraph 4) */\n\
                        typedef char jpl_check_%s_two_regions[((%s == (%s * %s)) ? 1 : -1)];\n\
                        typedef char jpl_check_%s_region_serves_the_cap[((%s - 1u) == %s) ? 1 : -1];\n\
                        typedef char jpl_check_%s_regions_tile_the_array[((%s + %s) == %s) ? 1 : -1];\n\
                        typedef char jpl_check_%s_origin_is_the_index_domain[((sizeof (%s) == (%s * sizeof (jpl_ref))) ? 1 : -1)];\n\n"
            macro n spaces cap p.p_from p.p_why
            (m_cap p) cap
            (m_space p) (m_cap p)
            (m_lo_base p)
            (m_hi_base p) (m_space p)
            (m_cur_base p) space_global (m_space p)
            (m_cur_top p) (m_cur_base p) (m_space p)
            (m_other_base p) space_global spaces_macro (m_space p)
            (m_other_top p) (m_other_base p) (m_space p)
            p.p_elem p.p_arr macro
            (origin_arr p) macro
            (pool_stem p) macro spaces_macro (m_space p)
            (pool_stem p) (m_space p) (m_cap p)
            (pool_stem p) (m_hi_base p) (m_space p) macro
            (pool_stem p) (origin_arr p) macro
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
  let cap = Option.get p.p_cap in
  let sh = pool_shape p in
  String.concat ""
    [
      Printf.sprintf "/* %s: %s of %s indices x %d spaces, %d cells per space, handled as %s\n\
                      \   (JPL.md §6.7 paragraph 4).  Which space is current is ONE global for the\n\
                      \   whole runtime, not one flag per pool: the graph moves together at a step\n\
                      \   boundary, so per-pool indicators would be several chances to disagree about\n\
                      \   a fact that has one cause. */\n"
        s p.p_arr m spaces cap p.p_handle;
      Printf.sprintf
        "extern jpl_ref jpl_%s_next;     /* an ABSOLUTE index into %s, always inside the current\n\
         \                                    interval: the lowest index not yet handed out, so\n\
         \                                    CUR_BASE + 1u is an empty region */\n"
        s m;
      Printf.sprintf
        "extern jpl_ref jpl_%s_peak;     /* the most cells ANY ONE region served — a count, not\n\
         \                                    the high-water index of one big array (decision 4's\n\
         \                                    quantity is cells) */\n"
        s;
      Printf.sprintf "extern jpl_ref jpl_%s_taken;    /* cells served since the program\
                      \ started */\n"
        s;
      Printf.sprintf
        "extern jpl_ref jpl_%s_refused;  /* allocations that found no cell: §6.6's\
         \ saturate-to-error edge */\n"
        s;
      Printf.sprintf
        "extern jpl_ref jpl_%s_scan;     /* the to interval's second pointer: the lowest index\n\
         \                                    whose cells edges have not been rewritten.  It is a\n\
         \                                    counter only in the sense that `next` is one —\n\
         \                                    §6.7 paragraph 5bis's drain is what reads it, and it\n\
         \                                    starts where reset rewinds next to, so an empty queue\n\
         \                                    and an empty region are the same index */\n"
        s;
      Printf.sprintf
        "extern jpl_ref jpl_%s_copied;   /* cells evacuated into the to interval, cumulative like\n\
         \                                    taken: a boundary's copy count is its delta (§6.7) */\n"
        s;
      Printf.sprintf
        "extern jpl_ref jpl_%s_forwarded; /* references answered by an existing copy rather than\n\
         \                                    a second cell — the sharing the forwarding pointer\n\
         \                                    exists to buy, measured instead of claimed */\n"
        s;
      Printf.sprintf
        "extern jpl_ref jpl_%s_badref;   /* evac called on a handle outside the interval it reads\n\
         \                                    from: a copy of a copy, a reserved base, an index past\n\
         \                                    the array.  5bis's refuse-and-count edge, one per pool\n\
         \                                    because which pool was asked is the readable fact */\n"
        s;
      (if sh.s_tagged then
         Printf.sprintf
           "extern jpl_ref jpl_%s_badtag; /* a tag word with no row in %s_edge: the scan stops on\n\
           \                                    that cell rather than walking its slots as scalars\n\
           \                                    (§6.7 paragraph 5bis).  Emitted only for a tagged\n\
           \                                    pool — an untagged cell has no tag to be wrong, and\n\
           \                                    §6.2 refuses a counter nothing writes */\n"
           s s
       else "");
      Printf.sprintf
        "typedef char jpl_check_%s_capacity_fits_the_counter[((%s < JPL_REF_TOP) ? 1 : -1)];\n"
        s m;
      Printf.sprintf "%s jpl_%s_alloc(void);   /* JPL_NIL once the CURRENT interval of %d cells\
                      \ is full */\n" p.p_handle s cap;
      Printf.sprintf "jpl_ref jpl_%s_reset(void);   /* cells returned; next rewinds to the\
                      \ CURRENT interval's own base + 1u */\n" s;
      Printf.sprintf "jpl_bool jpl_%s_is_live(jpl_ref h);   /* h in the current interval and\
                      \ below next: after\n\
                      \   a swap a handle from the other interval reads dead WHILE SITTING BELOW\n\
                      \   next, which is the case §6.6's `h < next` could not distinguish and\n\
                      \   §6.7's aliasing debt named */\n"
        s;
      Printf.sprintf
        "jpl_ref jpl_%s_word_at(jpl_ref h, jpl_ref i);   /* one WORD of %s, in the struct's own\n\
         \                                    field order: i is a position, not a byte, and an\n\
         \                                    index past the cell answers JPL_NIL (§6.7 paragraph\n\
         \                                    5bis).  The chain is derived from the members the\n\
         \                                    layout rule that emitted %s registered, so it cannot\n\
         \                                    describe a cell other than the one %s_edge classes */\n"
        s p.p_elem p.p_elem s;
      Printf.sprintf
        "void jpl_%s_word_put(jpl_ref h, jpl_ref i, jpl_ref v);   /* the scan's one write, over the\n\
         \                                    same arms as jpl_%s_word_at: no cell in this tree is\n\
         \                                    written through an address */\n"
        s s;
      Printf.sprintf
        "jpl_ref jpl_%s_evac(jpl_ref h);   /* copy %s's cell h into the current interval and\n\
         \                                    return the copy, or forward to the copy already made\n\
         \                                    (§6.7 paragraph 5bis: the four-arm test on %s_origin,\n\
         \                                    one C99 structure assignment, and alloc clearing the\n\
         \                                    origin of every cell it hands out) */\n"
        s p.p_elem s;
      Printf.sprintf "void jpl_%s_queue_start(void);   /* scan = CUR_BASE + 1u, the same expression\n\
                      \                                    reset uses, after evac has copied the\n\
                      \                                    roots that make the queue non-empty */\n"
        s;
      Printf.sprintf "void jpl_%s_scan_one(void);   /* rewrite %s's EDGE words at scan and advance\n\
                      \                                    scan by one cell */\n" s s;
      Printf.sprintf "void jpl_%s_drain(void);   /* scan_one until scan reaches next: a fixpoint\n\
                      \                                    over %s's to region, bounded by the\n\
                      \                                    interval (R3) and not recursive (R4) */\n\n"
        s s;
    ]

let runtime_section () =
  let ps = sized_pools () in
  emit runtime_b "/* ── the pool runtime (JPL.md §6.6, 5-B.3b-ii-b-1; two intervals since\n\
                \   5-B.3b-ii-b-2b, §6.7 paragraph 4): one bounded region per SPACE per pool\n\
                \   above.  Declarations only — the definitions and bodies are in the generated\n\
                \   translation unit sh_run_jpl_pools.c, which includes this header, and that\n\
                \   file is the only C in this tree holding a mutable static.  Each interval\n\
                \   reserves its own index 0 as JPL_NIL, so a space of CAP + 1 indices serves\n\
                \   CAP cells and the array's C = 2 * (CAP + 1) indices serve 2 * CAP.  Index 0\n\
                \   and index CAP + 1 are the two reserved slots and belong to no cell (§6.7).\n\
                \   Reclamation is at region granularity because a per-cell free needs the\n\
                \   reachability rule §6.5's ii-b-2 owns before it is safe, not a function; a\n\
                \   reset does NOT clear cells, since clearing them at every step boundary would\n\
                \   price the step by the pool rather than by the data and no lemma requires the\n\
                \   bytes to be zero — the same argument covers `origin`, whose stale entries sit\n\
                \   in the interval that becomes the to-space and are written before any scan\n\
                \   reads them.  is_live is the guard rail that makes a handle carried across a\n\
                \   reset or a swap observable: a comparison against the current interval, not a\n\
                \   liveness analysis.  The SCAN POINTER is here since ii-b-2c (§6.7 paragraph\n\
                \   5bis), and so is everything it reads: one word accessor pair, one evac, one\n\
                \   queue start, one scan step, one drain per pool, plus the counters that make\n\
                \   the copy measured rather than described.  Every one of them has a writer in\n\
                \   the generated translation unit below — §6.2's rule against a counter nothing\n\
                \   writes is why the badtag counter appears only under a pool whose cell has a\n\
                \   tag to get wrong. */\n";
  emit runtime_b "#define JPL_REF_TOP 4294967295u   /* counters saturate here, never wrap (§4.2) */\n\
                  typedef char jpl_check_ref_top_is_the_handle_word[((sizeof (jpl_ref) == 4u) ? 1 : -1)];\n\n";
  List.iter (fun p -> Buffer.add_string runtime_b (runtime_decl p)) ps;
  if ps <> [] then begin
    emit runtime_b "/* §4.2 wants one observable place: the saturating sum of every pool's refusals.\n\
                    \   A lowering reads a nil handle as the same edge a fired branch_guardb is\n\
                    \   (§5), and the host reads this as the run's verdict. */\n\
                    jpl_nat jpl_pools_refusals(void);\n\n";
    emit runtime_b "/* Which of the two intervals is current is ONE mutable global (§6.7 paragraph 4),\n\
                    \   declared beside the pools section that sizes them and written by ONE function.\n\
                    \   A second writer would be a second cause for a fact the graph agrees on, and\n\
                    \   the gate counts assignments to the global rather than trusting this sentence:\n\
                    \   it is the only name in this runtime whose value every pool's bounds read. */\n\
                    jpl_nat %s(void);   /* advance to the next interval; returns the new index,\n\
                         \                  so a caller can observe the flip without reading the\n\
                         \                  global it is the one writer of */\n\
                    typedef char jpl_check_pools_flip_cycles_the_intervals[\n\
                    \   (((1u %% %s) == 1u) && ((1u + 1u) %% %s == 0u)) ? 1 : -1];   /* the flip\n\
                    \   is a TWO-interval cycle, which is exactly what each pool's _two_regions\n\
                    \   check sizes its array for: raise the headroom factor to three and this fails\n\
                    \   at compile time instead of leaving a third interval no bound ever selects */\n\n"
      swap_fn spaces_macro spaces_macro;
    emit runtime_b "/* The scan's word is a handle whose POOL the edge table says, not one the\n\
                    \   cell's own type says, so the dispatch over the class ids is ONE function\n\
                    \   for the whole runtime (§6.7 paragraph 5bis) rather than eight that would\n\
                    \   each need a second table to name the target.  unclassified is its\n\
                    \   refuse-and-count edge: the one global that says a class was read that no\n\
                    \   arm covers, which the gate measures against the target set the tables\n\
                    \   were built from.  A lowering owns the order — queue_start, evac the roots,\n\
                    \   drain — and this layer only supplies the parts. */\n\
                    extern jpl_nat jpl_pools_unclassified;\n\
                    jpl_ref jpl_pools_evac_by_class(jpl_nat cls, jpl_ref h);\n\n"
  end;
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
      let sh = pool_shape p in
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
  let sorted_ids =
    Hashtbl.to_seq ids |> List.of_seq |> List.sort (fun (a, _) (b, _) -> String.compare a b)
  in
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
    sorted_ids;
  emit edges_b "#define JPL_EDGE_POOL_COUNT %du   /* targets an edge may name */\n"
    (Hashtbl.length ids);
  emit edges_b
    "\ntypedef char jpl_check_dispatch_arms_cover_every_target[\n\
    \    ((JPL_EDGE_POOL_COUNT + 2u) == JPL_EDGE_TO_%s_POOL) ? 1 : -1];   /* the target ids\n\
    \     are handed out in the sorted-stem order above, starting one past the two fixed\n\
    \     classes, so the highest id in the domain is COUNT + 2u and it belongs to %s.  The\n\
    \     dispatch in the pools TU has one arm per target, so this says the LAST arm it can\n\
    \     reach is the LAST id a table can contain: an unreachable class would be a table\n\
    \     word whose target no arm names, i.e. a live cell the scan leaves in the interval\n\
    \     the boundary abandons.  Pinned here rather than in a sentence because the count,\n\
    \     the order and the id base are three numbers only the emitter's own sort ties. */\n\n"
    (String.uppercase_ascii (fst (List.nth sorted_ids (List.length sorted_ids - 1))))
    (fst (List.nth sorted_ids (List.length sorted_ids - 1)));
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

(* ────────── 6d. the evacuation of one cell (JPL.md §6.7, 5-B.3b-ii-b-2c) ─── *)

(* One word of a cell, addressed the way the struct declares it.  `wa_count > 1` is an ARRAY
   member: one ranged arm covers it, because the slab is 257 words and a chain that named each
   one would be 257 lines of emitted C restating a single dimension.  A single-word arm is the
   member's own path, dotted where R3 put an aggregate inline. *)
type word_arm = { wa_first : int; wa_count : int; wa_path : string }

(* The one-word paths of a value held BY VALUE inside a cell.  A handle and a scalar are each
   exactly one word — the layout's own byte size answers, so this is not a test on a type NAME —
   and the only aggregate that splits is a pair, whose members `pair_layer` named
   `p_fst`/`p_snd`.  Anything wider that is not a pair is refused rather than guessed at: an
   option's or a variant's payload words mean something only under a tag, and §6.7's rule is
   that the collector never reads those as edges. *)
let rec word_paths prefix lt =
  match edge_target lt with
  | Some _ -> [ prefix ]
  | None ->
      let sz = size_of_name (value_name lt) in
      if sz = w4 then [ prefix ]
      else
        match lt with
        | L_pair (a, b) ->
            word_paths (prefix ^ ".p_fst") a @ word_paths (prefix ^ ".p_snd") b
        | _ ->
            fail
              ("the word accessor walk met " ^ show_lt lt ^ ", which the layout gives "
              ^ string_of_int sz
              ^ " bytes and which splits into no member names this reading has: a by-value\n\
                 \   aggregate inline in a pooled cell must be one whose fields the layout\n\
                 \   registered, and only a pair's are named today (p_fst, p_snd)")

(* The arms for one pool's cell, in word order, refusing anything that would leave the emitted
   chain describing a different cell than the edge table above it describes: members that do not
   reach the width, an array that is not the cell's trailing words (only then can the loop index
   alone address it), a member whose registered word count disagrees with the paths its type
   expands to. *)
let cell_arms p width =
  let s = pool_stem p in
  let fs =
    match Hashtbl.find_opt cell_fields s with
    | Some f -> f
    | None ->
        fail
          ("pool " ^ p.p_arr
          ^ " registers no cell members, so §6.7's scan could not rewrite one word of it: the\n\
             \   rule that emits a pooled struct records its fields in the same breath")
  in
  let rec go k acc = function
    | [] ->
        if k <> width then
          fail
            ("the members of " ^ p.p_elem ^ " cover " ^ string_of_int k
            ^ " of its " ^ string_of_int width
            ^ " words: the accessor chain and the edge table would describe different cells")
        else List.rev acc
    | f :: rest ->
        if f.fs_array then begin
          if rest <> [] || k + f.fs_words <> width then
            fail
              ("the array member " ^ f.fs_path ^ " of " ^ p.p_elem
              ^ " is not the cell's trailing " ^ string_of_int f.fs_words
              ^ " words: an array is addressed by the scan's own index, which only a\
                 \   trailing one can be given")
          else
            go (k + f.fs_words)
              ({ wa_first = k; wa_count = f.fs_words; wa_path = f.fs_path } :: acc)
              rest
        end
        else begin
          let paths =
            match f.fs_expand with
            | Some t -> word_paths f.fs_path t
            | None ->
                if f.fs_words <> 1 then
                  fail
                    ("the member " ^ f.fs_path ^ " of " ^ p.p_elem ^ " registers "
                    ^ string_of_int f.fs_words
                    ^ " words and no type to split them")
                else [ f.fs_path ]
          in
          if List.length paths <> f.fs_words then
            fail
              ("the member " ^ f.fs_path ^ " of " ^ p.p_elem ^ " registers "
              ^ string_of_int f.fs_words ^ " word(s) but its type "
              ^ show_lt (Option.get f.fs_expand) ^ " splits into "
              ^ string_of_int (List.length paths))
          else
            go (k + f.fs_words)
              (List.fold_left
                 (fun a (j, x) -> { wa_first = k + j; wa_count = 1; wa_path = x } :: a) acc
                 (List.mapi (fun j x -> (j, x)) paths))
              rest
        end
  in
  go 0 [] fs

(* The chain, emitted twice with different statements over the same arms.  Every arm tests its
   own index and there is NO bare `else`: a read past the cell's last word answers `JPL_NIL`,
   which is the empty list and therefore already means "no child", whereas a catch-all arm would
   answer the last member's value for an index that has no member.  The array arm's upper bound
   is the pool's own `JPL_<stem>_NPOS`, so the chain cites the macro the edge table is
   dimensioned by instead of a literal that could disagree with it. *)
let arm_test u a =
  if a.wa_count > 1 then
    Printf.sprintf "((i >= %du) && (i < JPL_%s_NPOS))" a.wa_first u
  else Printf.sprintf "(i == %du)" a.wa_first

let arm_slot p a =
  if a.wa_count > 1 then
    Printf.sprintf "%s[h].%s[i - %du]" p.p_arr a.wa_path a.wa_first
  else Printf.sprintf "%s[h].%s" p.p_arr a.wa_path

let arm_chain p arms stmt =
  let u = String.uppercase_ascii (pool_stem p) in
  String.concat "\n"
    (List.mapi
       (fun j a ->
         Printf.sprintf stmt
           (if j = 0 then "if" else "else if")
           (arm_test u a) (arm_slot p a))
       arms)

let word_at_definition p arms =
  let s = pool_stem p in
  String.concat ""
    [
      Printf.sprintf
        "jpl_ref jpl_%s_word_at(jpl_ref h, jpl_ref i) {\n  jpl_ref r = JPL_NIL;\n" s;
      Printf.sprintf
        "  /* §6.7 paragraph 5bis: one arm per word of %s, in the struct's own field order,\n\
        \     derived from the members the layout rule that emitted it registered.  Every member\n\
        \     is one uint32_t (or an array of them), so a word reads as a %s with no cast and no\n\
        \     pointer — reading a scalar word as a handle costs nothing, because the two are the\n\
        \     same type, and the scan only WRITES the words its table calls EDGE. */\n"
        p.p_elem p.p_handle;
      arm_chain p arms "  %s %s { r = %s; }";
      "\n  return r;\n}\n\n";
    ]

let word_put_definition p arms =
  let s = pool_stem p in
  String.concat ""
    [
      Printf.sprintf "void jpl_%s_word_put(jpl_ref h, jpl_ref i, jpl_ref v) {\n" s;
      Printf.sprintf
        "  /* The mirror of jpl_%s_word_at, over the same registered members: the scan's one\n\
        \     write, and the reason no cell in this tree is ever written through an address. */\n"
        s;
      arm_chain p arms "  %s %s { %s = v; }";
      "\n}\n\n";
    ]

(* evac, per pool: the from-region guard, the four comparisons that make an origin entry mean
   THIS round, and one structure assignment.  Note the order of the two writes at the end —
   origin[t] = h before origin[h] = t is not cosmetic: `t`'s entry is what the next evac's
   mutual arm reads, and `h`'s is what answers a second reference to the same cell. *)
let evac_definition p =
  let s = pool_stem p in
  let u = String.uppercase_ascii s in
  String.concat ""
    [
      Printf.sprintf "jpl_ref jpl_%s_evac(jpl_ref h) {\n" s;
      Printf.sprintf
        "  jpl_ref r = JPL_NIL;\n  jpl_ref o = JPL_NIL;\n  jpl_ref t = JPL_NIL;\n";
      Printf.sprintf
        "  /* §6.7 paragraph 5bis.  The domain test comes first: %s is the interval this\n\
        \     boundary reads FROM, so a handle inside it is the only thing an origin entry can\n\
        \     mean.  Anything else — an index of the to interval (a copy of a copy), a reserved\n\
        \     base, an index past the array — is refused and counted, never copied. */\n"
        ("JPL_" ^ u ^ "_OTHER_BASE");
      "  if (h == JPL_NIL) {\n    /* the empty list is not a cell: nothing is copied and no\n\
       \       counter moves, which is why JPL_NIL needs no reserved origin slot */\n";
      Printf.sprintf "  } else if ((h > %s_OTHER_BASE) && (h < %s_OTHER_TOP)) {\n" ("JPL_" ^ u)
        ("JPL_" ^ u);
      Printf.sprintf "    o = %s_origin[h];\n" ("jpl_" ^ s);
      Printf.sprintf
        "    /* Four arms, and the fourth is the one that makes the third true.  o below the\n\
        \       frontier means this round wrote o's entry — because alloc CLEARS the origin of\n\
        \       every cell it hands out — and a cell is evacuated at most once per round, so\n\
        \       o's entry names one source handle and equal-to-h is exactly \"this is h's\n\
        \       copy\".  Without the fourth arm a two-round trace reads a stale back-pointer as\n\
        \       a forwarding pointer and hands the parent a cell of the region being abandoned. */\n";
      Printf.sprintf
        "    if ((o != JPL_NIL) && (o > %s_CUR_BASE) && (o < jpl_%s_next) && (%s_origin[o] == h)) {\n"
        ("JPL_" ^ u) s ("jpl_" ^ s);
      Printf.sprintf
        "      if (jpl_%s_forwarded < JPL_REF_TOP) {\n        jpl_%s_forwarded = jpl_%s_forwarded + 1u;\n      }\n"
        s s s;
      Printf.sprintf "      r = o;\n";
      Printf.sprintf "    } else {\n      t = jpl_%s_alloc();\n" s;
      Printf.sprintf "      if (t != JPL_NIL) {\n";
      Printf.sprintf
        "        /* R7's cell is a struct of uint32_t members and %s_edge_covers_the_cell\n\
        \           pins NPOS * 4u == sizeof (%s), i.e. that no member is padded — which is what\n\
        \           makes this ONE statement the whole copy: C99 structure assignment, no pointer,\n\
        \           no cast, no aliasing question. */\n        %s[t] = %s[h];\n"
        ("jpl_check_" ^ s) p.p_elem p.p_arr p.p_arr;
      Printf.sprintf "        %s_origin[t] = h;\n        %s_origin[h] = t;\n" ("jpl_" ^ s)
        ("jpl_" ^ s);
      Printf.sprintf
        "        if (jpl_%s_copied < JPL_REF_TOP) {\n          jpl_%s_copied = jpl_%s_copied + 1u;\n        }\n"
        s s s;
      Printf.sprintf "        r = t;\n      }\n";
      Printf.sprintf "      /* t == JPL_NIL: the to interval is full.  jpl_%s_refused already\n\
        \         counts it (§6.6) and r stays the empty list, which is 5bis's answer for 2c —\n\
        \         2d is where an overflow becomes the model's BLimit. */\n" s;
      Printf.sprintf "    }\n  } else {\n";
      Printf.sprintf
        "    if (jpl_%s_badref < JPL_REF_TOP) {\n      jpl_%s_badref = jpl_%s_badref + 1u;\n    }\n"
        s s s;
      "  }\n  return r;\n}\n\n";
    ]

(* The queue: scan is the to interval's second pointer, and `queue_start` writes the same
   expression `reset` rewinds `next` to, so an empty queue and an empty region are one
   arithmetic fact rather than two that must agree. *)
let queue_start_definition p =
  let s = pool_stem p in
  String.concat ""
    [
      Printf.sprintf "void jpl_%s_queue_start(void) {\n" s;
      Printf.sprintf "  jpl_%s_scan = JPL_%s_CUR_BASE + 1u;\n}\n\n" s
        (String.uppercase_ascii s);
    ]

(* The scan's walk of one row, at indentation `ind`.  The classes come from the table and the
   words from the accessors derived from the same registered members, so the two halves of the
   scan are one reading of the cell — and `row * NPOS + i` is in bounds because `row` was
   guarded against NROWS above and `i` is bounded by NPOS here. *)
let scan_loop ind s u =
  String.concat ""
    [
      Printf.sprintf "%sfor (i = 0u; i < JPL_%s_NPOS; i = i + 1u) {\n" ind u;
      Printf.sprintf "%s  cls = jpl_%s_edge[(row * JPL_%s_NPOS) + i];\n" ind s u;
      Printf.sprintf
        "%s  /* SCALAR needs nothing (its value came with the copy) and UNUSED needs nothing\n\
         %s     (the word was never written), so only an EDGE word is rewritten — with the copy\n\
         %s     of the handle it holds, through the one runtime dispatch. */\n"
        ind ind ind;
      Printf.sprintf
        "%s  if ((cls != JPL_EDGE_SCALAR) && (cls != JPL_EDGE_UNUSED)) {\n\
         %s    jpl_%s_word_put(h, i, jpl_pools_evac_by_class(cls, jpl_%s_word_at(h, i)));\n\
         %s  }\n\
         %s}\n"
        ind ind s s ind ind;
    ]

let scan_one_definition p tagged =
  let s = pool_stem p in
  let u = String.uppercase_ascii s in
  String.concat ""
    [
      Printf.sprintf "void jpl_%s_scan_one(void) {\n" s;
      Printf.sprintf
        "  jpl_ref h = jpl_%s_scan;\n  jpl_ref i = 0u;\n  jpl_nat cls = 0u;\n" s;
      (if tagged then
         "  jpl_ref row = 0u;\n  jpl_bool walk = JPL_TRUE;\n\n\
          \  /* The row comes from the cell's own tag word, and a tag the table has no row for\n\
          \     stops the scan WITHOUT rewriting a word: a row this section does not have has no\n\
          \     classes to trust, and walking the slots as if they were scalar is the hard-coded\n\
          \     edge §6.7's derivation exists to forbid.  scan still advances below, so a bad tag\n\
          \     costs one cell and not the whole drain. */\n"
         ^ Printf.sprintf "  row = jpl_%s_word_at(h, 0u);\n" s
         ^ Printf.sprintf "  if (row >= JPL_%s_NROWS) {\n" u
         ^ Printf.sprintf
             "    if (jpl_%s_badtag < JPL_REF_TOP) {\n      jpl_%s_badtag = jpl_%s_badtag + 1u;\n    }\n"
             s s s
         ^ "    walk = JPL_FALSE;\n  }\n"
         ^ Printf.sprintf "  if (walk == JPL_TRUE) {\n%s  }\n" (scan_loop "    " s u)
       else
         "  /* An untagged cell is ONE row — the same conclusion edge_decl prints when it calls\n\
          \     this pool untagged, reached here without reading the table: the row index is 0u,\n\
          \     so the table's first NPOS classes ARE this cell's words.  No tag guard, because\n\
          \     there is no tag to be wrong. */\n"
         ^ Printf.sprintf "  const jpl_ref row = 0u;\n%s" (scan_loop "  " s u));
      Printf.sprintf "\n  jpl_%s_scan = h + 1u;\n}\n\n" s;
    ]

let drain_definition p =
  let s = pool_stem p in
  String.concat ""
    [
      Printf.sprintf "void jpl_%s_drain(void) {\n" s;
      Printf.sprintf
        "  /* R3's bound is the interval itself: scan advances one cell per step and only the\n\
        \     allocator moves next, so this is a fixpoint over %s's to region and every cell is\n\
        \     scanned at most once.  R4 holds because the call graph runs one way — drain,\n\
        \     scan_one, the dispatch, evac, alloc — and no evac reaches a scan. */\n"
        s;
      Printf.sprintf "  while (jpl_%s_scan < jpl_%s_next) {\n    jpl_%s_scan_one();\n  }\n}\n\n" s
        s s;
    ]

(* The dispatch's target set: the ids the edge tables can name, in the order the class macros
   are numbered.  An id whose pool has no evac is refused here rather than becoming a chain that
   silently covers a prefix of the domain. *)
let dispatch_targets () =
  let ids = edge_pool_ids () in
  let sized = sized_pools () in
  let stems =
    List.sort String.compare
      (List.map (fun (s, _) -> s) (Hashtbl.to_seq ids |> List.of_seq))
  in
  List.map
    (fun s ->
      match List.find_opt (fun p -> pool_stem p = s) sized with
      | Some _ -> (s, Hashtbl.find ids s)
      | None ->
          fail
            ("the edge class JPL_EDGE_TO_" ^ String.uppercase_ascii s
            ^ "_POOL names a pool with no evac: the table would point at a forwarding target\n\
               \   that cannot be copied into"))
    stems

let dispatch_definition () =
  let targets = dispatch_targets () in
  String.concat ""
    [
      "/* ── the one dispatch (JPL.md §6.7 paragraph 5bis): a class id is a number the edge\n\
      \   tables were built with, and every pool that can be an edge's target gets exactly one\n\
      \   arm here.  One function for the whole runtime rather than one per pool, because the\n\
      \   scan's word is a handle whose POOL the table says and not one the cell's own type\n\
      \   says — a per-pool dispatch would need a second table to name the target. */\n";
      "jpl_nat jpl_pools_unclassified = 0u;\n\n";
      "jpl_ref jpl_pools_evac_by_class(jpl_nat cls, jpl_ref h) {\n  jpl_ref r = h;\n";
      Printf.sprintf
        "  /* The final branch is impossible by construction — this chain and the tables are\n\
        \     the same edge_pool_ids () reading of the same registry, and the header's\n\
        \     jpl_check_dispatch_arms_cover_every_target pins the last arm's id against the size\n\
        \     of the target set — and it is emitted and counted anyway, because the alternative\n\
        \     to measuring an impossible case is trusting a sentence about it.  Returning the\n\
        \     handle unchanged is the least wrong action: the word then names a cell in the\n\
        \     abandoned interval, is_live rejects it, and the failure surfaces as a dead handle\n\
        \     instead of a cell that looks live. */\n";
      String.concat "\n"
        (List.mapi
           (fun j (s, _) ->
             Printf.sprintf "%s (cls == JPL_EDGE_TO_%s_POOL) { r = jpl_%s_evac(h); }"
               (if j = 0 then "  if" else "  else if")
               (String.uppercase_ascii s) s)
           targets);
      "\n  else {\n";
      "    if (jpl_pools_unclassified < JPL_REF_TOP) {\n      jpl_pools_unclassified = jpl_pools_unclassified + 1u;\n\
      \    }\n";
      "  }\n  return r;\n}\n";
    ]

let pool_definition p =
  let s = pool_stem p in
  let m = pool_macro p in
  let cap = Option.get p.p_cap in
  let sh = pool_shape p in
  let width = edge_cell_words p.p_elem in
  let arms = cell_arms p width in
  String.concat ""
    [
      Printf.sprintf "/* ── %s: %d cells per space x %d spaces = %s indices of %s, handled as\
                      \ %s ── */\n"
        s cap spaces m p.p_elem p.p_handle;
      Printf.sprintf "%s %s[%s];\n" p.p_elem p.p_arr m;
      Printf.sprintf
        "jpl_ref %s[%s];   /* §6.7's origin table: for a cell copied by a step boundary, the\n\
        \                        handle it was copied FROM, so the scan reads its children from\n\
        \                        the right place without a spare word in the cell.  One entry per\n\
        \                        INDEX — including the two reserved slots, which no handle names —\n\
        \                        because a handle is the only key the collector has.  No\n\
        \                        initialiser: zero is JPL_NIL, which already means \"not copied\n\
        \                        from anywhere\".  The one store this array gets outside a copy is\n\
        \                        in the allocator below: an entry for a cell of the current\n\
        \                        interval means THIS round because alloc cleared it, which is what\n\
        \                        evac's fourth arm reads (§6.7 paragraph 5bis — and it is charged\n\
        \                        per copy, so §6.6's no-clearing argument still holds) */\n"
        (origin_arr p) m;
      Printf.sprintf "jpl_ref jpl_%s_next = 1u;   /* the current interval's base + 1u at\n\
                      \                           start-up (space 0): index 0 is JPL_NIL and\n\
                      \                           stays reserved, per space */\n"
        s;
      Printf.sprintf "jpl_ref jpl_%s_peak = 0u;\n" s;
      Printf.sprintf "jpl_ref jpl_%s_taken = 0u;\n" s;
      Printf.sprintf "jpl_ref jpl_%s_refused = 0u;\n" s;
      Printf.sprintf
        "jpl_ref jpl_%s_scan = 1u;   /* §6.7 paragraph 5bis's second pointer: the to interval's\n\
        \                             queue, the lowest index not yet scanned.  1u because\n\
        \                             start-up is space 0, whose base is 0 — the same expression\n\
        \                             queue_start writes at run time, and no cell is scanned\n\
        \                             before a boundary has queued one */\n"
        s;
      Printf.sprintf
        "jpl_ref jpl_%s_copied = 0u;   /* fresh cells this pool evacuated */\n" s;
      Printf.sprintf
        "jpl_ref jpl_%s_forwarded = 0u;   /* evacuate calls answered by an existing copy: the\n\
        \                                    sharing hits, and the only quantity that separates a\n\
        \                                    copy from a duplicate */\n"
        s;
      Printf.sprintf
        "jpl_ref jpl_%s_badref = 0u;   /* a handle outside the region this boundary reads from */\n"
        s;
      (if sh.s_tagged then
         Printf.sprintf
           "jpl_ref jpl_%s_badtag = 0u;   /* a tag with no row in %s_edge */\n\n" s
           ("jpl_" ^ s)
       else "\n");
      Printf.sprintf "%s jpl_%s_alloc(void) {\n  %s h = JPL_NIL;\n" p.p_handle s p.p_handle;
      Printf.sprintf "  /* The pointer must sit INSIDE the current interval to allocate: after a\n\
                      \     swap and before the rewind, jpl_%s_next still names the interval just\n\
                      \     abandoned, and a test against the top alone would then serve this\n\
                      \     region's reserved nil index as if it were a cell.  Refusing instead is\n\
                      \     §4.2's saturate-to-error, and the refusal counter is what says a driver\n\
                      \     forgot to rewind. */\n"
        s;
      Printf.sprintf "  if ((jpl_%s_next > %s) && (jpl_%s_next < %s)) {\n    h = jpl_%s_next;\n" s
        (m_cur_base p) s (m_cur_top p) s;
      Printf.sprintf "    jpl_%s_next = jpl_%s_next + 1u;\n" s s;
      Printf.sprintf "    jpl_%s_origin[h] = JPL_NIL;\n" s;
      Printf.sprintf "    /* 5bis's one store per cell handed out: an index below the frontier\n\
                      \       then has an origin THIS round wrote — nil until a copy fills it —\n\
                      \       which is the fact evac's fourth arm turns into \"h is already\n\
                      \       copied\".  Without it a two-round trace reads last round's\n\
                      \       back-pointer as this round's forwarding pointer. */\n";
      Printf.sprintf "    /* peak is the most cells ONE region served — decision 4's quantity is\n\
                      \       cells, not positions in one big array — hence the region's base.\n\
                      \       next > CUR_BASE here, so the subtraction cannot wrap. */\n";
      Printf.sprintf "    if (jpl_%s_peak < (h - %s)) {\n      jpl_%s_peak = h - %s;\n    }\n" s
        (m_cur_base p) s (m_cur_base p);
      Printf.sprintf "    if (jpl_%s_taken < JPL_REF_TOP) {\n      jpl_%s_taken = jpl_%s_taken + 1u;\n    }\n" s s s;
      "  } else {\n";
      Printf.sprintf "    if (jpl_%s_refused < JPL_REF_TOP) {\n      jpl_%s_refused = jpl_%s_refused + 1u;\n    }\n" s s s;
      "  }\n  return h;\n}\n\n";
      Printf.sprintf "jpl_ref jpl_%s_reset(void) {\n" s;
      Printf.sprintf "  /* Rewind to the CURRENT interval's own base + 1u (§6.7 paragraph 4), not to\n\
                      \     1u: rewinding to 1u after a swap would free the cells the swap just made\n\
                      \     current.  The bounds test is not decoration — next may still name the\n\
                      \     interval just abandoned, and an unsigned subtraction there would wrap,\n\
                      \     so an abandoned region honestly reports zero cells returned. */\n";
      Printf.sprintf "  jpl_ref returned = 0u;\n";
      Printf.sprintf "  if ((jpl_%s_next > %s) && (jpl_%s_next <= %s)) {\n" s (m_cur_base p) s
        (m_cur_top p);
      Printf.sprintf "    returned = jpl_%s_next - %s - 1u;\n" s (m_cur_base p);
      "  }\n";
      Printf.sprintf "  jpl_%s_next = %s + 1u;\n" s (m_cur_base p);
      "  return returned;\n}\n\n";
      Printf.sprintf "jpl_bool jpl_%s_is_live(jpl_ref h) {\n  jpl_bool r = JPL_FALSE;\n" s;
      Printf.sprintf "  /* Three bounds, and the middle one is the whole point of ii-b-2b: at one\n\
                      \     interval `h < next` and `h below the array` said the same thing, so a\n\
                      \     handle from the PREVIOUS interval was live whenever the current region\n\
                      \     had grown past it — §6.6's aliasing debt, which this comparison now\n\
                      \     discharges.  h > CUR_BASE is strict because each region's base is its\n\
                      \     own reserved JPL_NIL, and h != JPL_NIL is exactly this test at space 0. */\n";
      Printf.sprintf "  if ((h > %s) && (h < %s) && (h < jpl_%s_next)) {\n    r = JPL_TRUE;\n"
        (m_cur_base p) (m_cur_top p) s;
      "  }\n  return r;\n}\n\n";
      word_at_definition p arms;
      word_put_definition p arms;
      evac_definition p;
      queue_start_definition p;
      scan_one_definition p sh.s_tagged;
      drain_definition p;
    ]

(* One global for the whole runtime (§6.7 paragraph 4), emitted once, after the pools whose
   bounds read it: eight indicators would be eight chances to disagree about which half of every
   array is current, and the swap is the only assignment the gate allows anywhere. *)
let space_definition =
  String.concat ""
    [
      "/* ── which interval is current: ONE value for the whole graph (JPL.md §6.7 paragraph 4)\n\
      \   — every pool moves together at a step boundary, so this is not per-pool state, and the\n\
      \   pools section of the header declares it beside the bounds that read it.  Start-up is\n\
      \   the low interval, whose base is 0, so every jpl_<stem>_next above is already its own\n\
      \   base + 1u. ── */\n";
      Printf.sprintf "jpl_nat %s = 0u;\n\n" space_global;
      Printf.sprintf "jpl_nat %s(void) {\n" swap_fn;
      "  /* THE one writer of the indicator: verify/c/jpl_emit.sh counts assignments to it in\n\
      \   this file and refuses a second one, because a flip nobody owns would make the\n\
      \   interval a handle was born in a question no code answers.  Modulo, not a conditional\n\
      \   on 0u/1u, so the cycle length is the header's own JPL_POOL_SPACES and the emitted\n\
      \   jpl_check_pools_flip_cycles_the_intervals is what says that length is two. */\n";
      Printf.sprintf "  %s = (%s + 1u) %% %s;\n" space_global space_global spaces_macro;
      Printf.sprintf "  return %s;\n}\n" space_global;
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
  if sized_pools () <> [] then begin
    emit b "\n";
    Buffer.add_string b space_definition;
    emit b "\n";
    Buffer.add_string b (dispatch_definition ());
    emit b "\n"
  end;
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
  section "STATIC POOLS (indices x cell size, from the caps above; indices = spaces x (cap+1))";
  Printf.printf "  %-26s %-24s %8s %6s %10s %12s  %s\n" "array" "element" "indices"
    "cap/sp" "bytes" "size" "sized from";
  let total = ref 0 and unsized = ref [] in
  List.iter
    (fun p ->
      let esz = size_of_name p.p_elem in
      match p.p_count with
      | Some n ->
          let b = n * esz in
          total := !total + b;
          Printf.printf "  %-26s %-24s %8d %6d %10d %12s  %s\n" p.p_arr p.p_elem n
            (Option.get p.p_cap) b (kb b) p.p_from
      | None ->
          unsized := p :: !unsized;
          Printf.printf "  %-26s %-24s %8s %6s %10d %12s  %s\n" p.p_arr p.p_elem "PENDING"
            "-" esz (kb esz ^ " per word") p.p_from)
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
    Printf.printf "  Cost of the decision, measured: the slab is %s, which is %d indices —\n"
      (kb (interval_indices caps.c_words * size_of_name "jpl_text"))
      (interval_indices caps.c_words);
    Printf.printf "  %d cells per space x %d spaces, each space reserving its own index 0 —\n"
      caps.c_words spaces;
    Printf.printf "  x %d bytes per cell, and it dominates every other pool.  The per-cell size is\n"
      (size_of_name "jpl_text");
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
  section "POOL RUNTIME (JPL.md §6.6, two intervals since §6.7's ii-b-2b): one bounded region per\
          \ SPACE per sized pool";
  let ps = sized_pools () in
  let unsized = List.filter (fun p -> p.p_count = None) (List.rev !pools) in
  Printf.printf "  %-22s %-26s %-30s %-26s %s\n" "stem" "capacity macro" "cells of"
    "handled as" "runtime names";
  List.iter
    (fun p ->
      Printf.printf "  %-22s %-26s %-30s %-26s _alloc, _reset, _is_live, _next, _peak,\
                    \ _taken, _refused, _origin\n"
        (pool_stem p) (pool_macro p) p.p_elem p.p_handle)
    ps;
  if unsized <> [] then
    Printf.printf "  NO RUNTIME for: %s — unsized pools can be neither defined nor handed\
                   \ out,\n   which is §6.6's rule cutting both ways.\n"
      (String.concat ", " (List.map (fun p -> p.p_arr) unsized));
  Printf.printf "\n  Each pool is ONE array of %d intervals, so 2f's declared-pool grep still\n\
    \  reads %d pools: the split is inside the index domain, not in the name count.  A space\n\
    \  reserves its own index 0, so a pool serves the artifact's cap cells PER SPACE, and\n\
    \  `%s()` — one global, one writer — says which space is current.  That\n\
    \  pointer is absolute and is read against the current interval, so `reset` rewinds to\n\
    \  the current base + 1u rather than to 1u, and `peak` counts a region's cells instead of\n\
    \  remembering a high-water index.\n\
    \  Reclamation is at REGION granularity: a reset returns every cell at once,\n\
    \  because a per-cell free needs the reachability rule §6.5's ii-b-2 owns before it is\n\
    \  safe, not a function.  A reset does not clear cells, and `is_live` is the guard rail\n\
    \  that makes a handle carried across one — or across a swap — observable (§6.7: after a\n\
    \  swap a handle from the previous interval reads dead while sitting BELOW the current\n\
    \  `next`, which is the case §6.6's `h < next` could not distinguish).  `peak` is the\n\
    \  quantity decision 4 said no walk over the artifact's text could produce — a run\n\
    \  measures it.  With no kernel that allocates yet, every peak in this tree is 0: this is\n\
    \  the instrument, not the number, and the gate prints that zero as one.\n"
    spaces (List.length !pools) swap_fn;
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
  let served =
    List.fold_left
      (fun a p -> match p.p_cap with Some v -> a + v | None -> a)
      0 (List.rev !pools)
  in
  (* The interval arithmetic the header's own typedefs pin, counted from the registry rather
     than from the emitted text: the emitter refused an array whose dimension is not SPACES x
     (cap + 1) before a file was written, so every pool that reaches this line has been
     checked twice — once by division here and once by the compiler. *)
  let intervals_ok =
    List.length
      (List.filter
         (fun p ->
           match (p.p_cap, p.p_count) with
           | (Some cap, Some n) -> n = interval_indices cap
           | _ -> false)
         ps)
  in
  (* §6.7 paragraph 5bis's census.  `tag_n` is the same `s_tagged` flag the declaration, the
     body and the scan's guard are emitted under, so the counters that exist only where a tag
     can be wrong are counted by the flag rather than by a number typed beside it — and the
     dispatch's arms come from `dispatch_targets ()`, which is the one list the chain and the
     refusal above both read. *)
  let tag_n = List.length (List.filter (fun p -> (pool_shape p).s_tagged) ps) in
  let dispatch_arms = List.length (dispatch_targets ()) in
  (* Every mutable global the runtime owns: the four counters §6.6 started with, the four
     §6.7 paragraph 5bis adds per pool, one badtag per tagged pool, the space indicator, and
     the dispatch's unclassified.  `scan` is in that count as a mutable static, not as a
     counter — it is a pointer, and `scan_pointers_emitted` says so. *)
  let globals = (8 * n) + tag_n + 2 in
  List.iter
    (fun (k, v, gloss) -> Printf.printf "  %-40s %8d   %s\n" k v gloss)
    [
      ("pools_declared", List.length !pools, "arrays the layout section declares");
      ("pools_with_capacity", n, "the ones sized from the cap table");
      ("pools_without_capacity", List.length unsized, "sized by nothing, so runtime-free");
      ("allocators_emitted", n, "one jpl_<stem>_alloc per sized pool");
      ("resets_emitted", n, "one jpl_<stem>_reset per sized pool");
      ("live_checks_emitted", n, "one jpl_<stem>_is_live per sized pool");
      ("counters_emitted", (7 * n) + tag_n + 1,
       "next, peak, taken, refused, copied, forwarded, badref per pool + badtag per tagged pool + unclassified");
      ("mutable_globals_emitted", globals,
       "every mutable static in the pools TU: the counters above, plus one scan pointer per pool, plus the space");
      ("mutable_globals_bytes", globals * w4, "4 B each — the price of a measured runtime");
      ("scan_pointers_emitted", n, "the to interval's second pointer, one per pool (§6.7 ¶5bis)");
      ("word_accessors_emitted", 2 * n,
       "jpl_<stem>_word_at and _word_put, from the members the layout rule registered");
      ("evac_functions_emitted", n, "one jpl_<stem>_evac per pool, copying ONE cell");
      ("evac_forward_arms_checked", n,
       "the four-arm test on origin — nil, in-interval, below the frontier, and mutual");
      ("origin_clears_emitted", n,
       "the store alloc does to origin[h] for the cell it hands out: 5bis's fourth arm reads it");
      ("queue_start_functions_emitted", n, "scan = CUR_BASE + 1u, per pool");
      ("scan_step_functions_emitted", n, "jpl_<stem>_scan_one, per pool");
      ("drain_functions_emitted", n, "the fixpoint loop over one pool's to region");
      ("tag_guards_emitted", tag_n,
       "the row bound + badtag arm, only where the cell HAS a tag word (§6.2)");
      ("dispatch_functions_emitted", 1, "jpl_pools_evac_by_class — one, not one per pool");
      ("dispatch_arms_emitted", dispatch_arms,
       "one per target the edge tables can name — must equal edge_target_pools");
      ("pool_arrays_defined", n, "arrays the generated translation unit defines");
      ("refusals_sum_terms", n, "terms in jpl_pools_refusals's saturating sum");
      ("allocator_handles_defined_in_layout", handles_ok, "an allocator's return type is a typedef the layout emitted");
      ("runtime_names_colliding_with_prototypes", List.length collide, "a runtime name that is also a closure symbol — must be 0");
      ("runtime_cells_total", cells, "indices across every sized pool, both intervals");
      ("runtime_bytes_total", bytes, "bytes of static storage the pools occupy");
      ("regions_per_pool", spaces, "§6.7 paragraph 4: the headroom factor read as intervals");
      ("space_cells_served_total", served, "cells ONE space serves, summed: the artifact's own caps");
      ("interval_arithmetics_checked", intervals_ok, "pools whose dimension is SPACES x (cap + 1) — must equal pools_with_capacity");
      ("interval_macros_emitted", (List.length interval_macros) * n + 1,
       "CAP, SPACE, LO/HI/CUR/OTHER x BASE/TOP per pool, plus JPL_POOL_SPACES");
      ("interval_typedefs_emitted", 4 * n, "two_regions, region_serves_the_cap, regions_tile_the_array, origin_is_the_index_domain");
      ("flip_typedefs_emitted", 1, "the swap's cycle length, checked against SPACES");
      ("origin_arrays_emitted", n, "one jpl_<stem>_origin per sized pool");
      ("origin_indices_total", cells, "the origin domain IS the index domain (§6.7)");
      ("origin_bytes_total", cells * w4, "4 B per index — §6.7 paragraph 4's predicted price");
      ("space_globals_emitted", 1, "ONE jpl_pools_space for the whole runtime, not per pool");
      ("swap_functions_emitted", 1, "its one writer; the gate counts assignments in the TU");
      ("static_bytes_total_with_origins", bytes + (cells * w4), "pools plus origins");
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
  if dispatch_arms <> List.length !pools then begin
    Printf.printf "RUNTIME REFUSED: jpl_pools_evac_by_class has %d arms but the edge tables' \
                   \target set names %d pools.\n"
      dispatch_arms (List.length !pools);
    Printf.printf "   A class no arm names is a table word whose target cannot be copied, i.e.\n\
      \   a live cell the scan leaves in the interval the boundary abandons — the failure §6.7\n\
      \   paragraph 5bis counts rather than describes.  The header's own\n\
      \   jpl_check_dispatch_arms_cover_every_target pins the last id against the count.\n";
    exit 1
  end;
  Printf.printf "\nRUNTIME EMITTED: %d pools, %d indices in total (%d spaces x (cap + 1) per\n\
    \  pool), one space serving %d cells summed over the pools: %s of pool storage plus\n\
    \  %s of origins = %s, with one %s and one %s().\n\
    \  ii-b-2c adds the copy itself: %d evac functions, each with the four-arm forwarding test\n\
    \  on origin and the %d origin clears that make its fourth arm mean THIS round, %d word\n\
    \  accessors derived from the members the layout registered, %d queue/scan/drain triplets\n\
    \  (%d tag guards, because %d cells have no tag to get wrong), and one dispatch whose %d\n\
    \  arms cover the whole target-id domain — %d mutable statics, %s of them.\n"
    n cells spaces served (kb bytes) (kb (cells * w4))
    (kb (bytes + (cells * w4))) space_global swap_fn
    n n (2 * n) n tag_n (n - tag_n) dispatch_arms globals (kb (globals * w4));
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
      | Some (cap_cells, macro, _) ->
          Printf.printf "                             %s -> jpl_%s_pool: %d cells per space x %d\
                        \ spaces, sized from %s\n"
            nm nm cap_cells headroom macro
      | None -> Printf.printf "                             %s -> NO CAPACITY\n" nm)
    pooled_types;
  Printf.printf "                             (the two halves are cross-checked: naming a type pooled without\n\
                \                             capping it is a refusal, not a silent fall-through to a by-value\n\
                \                             layout).  Every other vocabulary type is by value and needs no\n\
                \                             capacity\n";
  Printf.printf "  2. list pool sizing        pair(text,text) -> JPL_MAX_ENV, frame list -> JPL_MAX_STACK,\n";
  Printf.printf "                             every other list kind -> JPL_MAX_LIST\n";
  Printf.printf "  3. headroom factor         %d.  §6.7 paragraph 4 reads it as a NUMBER OF\n" headroom;
  Printf.printf "                             INTERVALS, not slack, so it is now the spaces of every\n";
  Printf.printf "                             pool's array: one holds the live set, one receives the\n";
  Printf.printf "                             copies a step boundary builds before releasing it.  That\n";
  Printf.printf "                             reading does not discharge the proof JPL.5-B.3 still\n";
  Printf.printf "                             owes — that the live set is bounded by the cap — it only\n";
  Printf.printf "                             says what a factor of 1 would mean (no to-space, so no\n";
  Printf.printf "                             copying collection at all).  Stated here so it is not\n";
  Printf.printf "                             silently absorbed into an array dimension.\n";
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
