(* sh_jpl.v

 * JPL-compliant bounded data layer (Phase 3d-C / JPL.2).
 *
 * The single source of truth for shell semantics is verify/models/sh_concrete.v,
 * which extracts to fuel-bounded recursion over heap lists (Peano nat, list-text,
 * cmd tree, higher-order obind).  A literal emit of that to C99 would need malloc,
 * recursion and boxed naturals, each of which breaks a mandatory canonical JPL
 * PowerPC C rule.  This file is the *bounded representation* the emitted C99 is
 * allowed to use, together with the *saturate-to-error* discipline that replaces
 * silent wraparound.  It is a companion to sh_concrete.v, not a replacement:
 *
 *   - every observable helper here agrees with the concrete model on in-budget
 *     inputs (see the behavioural-isomorphism Examples near the end), and
 *   - every operation that could exceed a compile-time capacity returns the
 *     defined BLimit outcome instead of wrapping or running past its budget.
 *
 * Scope of THIS file (JPL.2): the bounded data types, the saturate-to-error
 * result plumbing, and the primitive helpers built on top of them.  The
 * small-step machine that consumes these — the explicit bounded control stack
 * that makes `run` and the `expand`/`glob` scan loops fully iterative (no
 * non-tail recursion) — is authored in JPL.3 on top of this layer.  Until then
 * the scan-level helpers (b_expand, b_glob, b_match_any) are bounded *wrappers*
 * around the fuel-bounded concrete functions: they fix the observable bounded
 * contract and its saturation behaviour, which the JPL.3 machine must preserve.
 *
 * Design invariants (JPL.md):
 *   1. Axiom-free: coqchk -o -silent must report all four <none> lines.  No
 *      Axiom/Parameter/Admitted/admit anywhere below.
 *   2. Fixed-width unsigned naturals: a Coq nat here stands for a uint32_t in the
 *      emitted C.  Every value produced by this layer is provably <= MAX_FUEL,
 *      i.e. well inside 32-bit range, so the emit never wraps; when a computation
 *      would cross a capacity the bounded operation returns BLimit instead.
 *   3. No unbounded recursion in the representation: lists are wrapped in
 *      length-carrying records whose smart constructors refuse to build an
 *      over-long value.
 *
 * Build (Rocq >= 9.0):
 *   coqc sh_jpl.v
 *   coqchk -o -silent sh_jpl     # must report Axioms: <none>
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.
Import ListNotations.

(* sh_concrete.v is the single source of truth.  It is imported here only as the
   *reference semantics* the bounded layer must agree with — the concrete helper
   names (teqb, getv, setv, expand, glob, match_any, nat2text, nstat, cmd) are
   reused for the byte-level scans so nothing is re-implemented and re-derived,
   and the Examples at the bottom assert agreement, not duplication. *)
Require Import sh_concrete.

(* cmd has list-valued fields (a nested inductive); the register-all warning is
   about auto induction schemes we do not use. *)
Set Warnings "-register-all".

(* ═══════════════════════════════════════════════════════════════════
   §1  Capacity constants (LOCKED — JPL.md, user 2026-10-03; GLOB_FUEL and the
   raised MAX_FUEL added on the user's instruction of 2026-10-04)

   These are the compile-time budgets the emitted C allocates against.  They
   are written as Coq nats but become #define uint32_t constants at the emitter.
   None is a large literal: each is a small literal or a sum/product of them, and
   the largest (MAX_FUEL = 136 449) is three orders of magnitude below 2^31, so
   every one fits the fixed-width word — see cap_order and cap_fuel_order.
   ═══════════════════════════════════════════════════════════════════ *)

Definition MAX_WIDTH : nat := 32.      (* uint32 word bits *)
Definition MAX_WORD  : nat := 256.     (* expanded word / text length in bytes *)
Definition MAX_ARGV  : nat := 64.      (* argument words per simple command *)
Definition MAX_ENV   : nat := 128.     (* simultaneously live shell variables *)
Definition MAX_LIST  : nat := 1024.    (* any intermediate list length *)
Definition MAX_CMD   : nat := 4096.    (* node-pool capacity for one lowered cmd tree *)

(* GLOB_FUEL — the scan budget, added 2026-10-04 on the user's instruction to
   raise the fuel budget once sh_jpl_scan.v §4.3 proved glob's completeness.  That
   section shows the tail loop needs its OWN quadratic law, not the reference
   matcher's linear one:

     fuel_top pat str = (|pat|+|str|+1)*(|str|+1) + |pat| + |str|

   so on two full-width words it is (2*MAX_WORD+1)*(MAX_WORD+1) + 2*MAX_WORD, which
   is exactly the definition below (decimal 132 353; the value is DERIVED from
   MAX_WORD and never written as a literal, so it cannot drift if MAX_WORD changes).
   sh_jpl_scan.v §4.3.14 proves `fuel_top pat str <= GLOB_FUEL` from
   `length pat <= MAX_WORD /\ length str <= MAX_WORD`, and that is the only reason
   this constant exists: the old MAX_FUEL = 4096 could not carry it (the bound
   crosses 4096 at |pat| = |str| = 45, measured in §4.3.9), so a machine that globs
   at full word would have saturated rather than answered.  No slack is baked in —
   the margin lives in MAX_FUEL, which is this budget plus the machine's steps. *)
Definition GLOB_FUEL : nat :=
  S (MAX_WORD + MAX_WORD) * S MAX_WORD + MAX_WORD + MAX_WORD.

(* The machine hands ONE fuel number both to its step countdown and to the scans it
   calls, so the loop-iteration bound must cover the deepest scan it can be asked to
   run: GLOB_FUEL (one full-width glob) plus the 4096 steps this layer was originally
   budgeted for (decimal 136 449).  b_fuel below is the gate that refuses anything
   larger, and sh_jpl_scan.v §4.3.14's corollary shows the machine may therefore be
   handed exactly MAX_FUEL and still find every real match. *)
Definition MAX_FUEL  : nat := GLOB_FUEL + 4096.

Definition MAX_STACK : nat := 4096 + 4096.  (* explicit machine stack frames = 8192 *)

(* MAX_WORDS — the capacity of the WORD POOL, added 2026-10-05 because JPL.5-B.2's
   emitter could size every pool except the slab of `text` cells and had to declare
   `jpl_word_pool[]` with no dimension (JPL.md §6, §9.2's decision 3(a)).  It is a
   SUM of already-LOCKED caps, not a new choice, so each summand names the lemma (or
   the obligation) that pays for it:

     MAX_STACK   the words in a pool-fitting program TREE.  §7.1's cmd_words counts
                 word occurrences honestly (cmd_count under-counts them: an Assign
                 node holds two texts but is charged one node) and proves
                 cmd_words f c <= 2 * cmd_count f c with the same fuel, hence
                 cmd_fits_words: a tree the MAX_CMD node pool admits holds at most
                 2 * MAX_CMD = MAX_STACK word cells.  PROVED.
     MAX_STACK   the same occurrences again, as RUNTIME-EXPANDED copies.  An
                 FFor/FCase frame holds the expansion of a tree list, so while the
                 tree is alive its words exist twice in the slab.  This summand is
                 the OBLIGATION this constant names and does not yet discharge: it
                 needs the step-machine invariant "at most one live frame per source
                 node" (§7.2, still to be written).  It is charged at MAX_STACK — the
                 tree's own bound — rather than absorbed silently, so the debt is
                 visible in the number.
     2*MAX_ENV   every pair in a well-formed environment is a name cell plus a value
                 cell: §5's benv_words_le, from wf_benv's MAX_ENV cap.  PROVED.
     2           the per-step temporaries that live in neither tree nor environment:
                 the rendered `$?` status word and the word currently being
                 expanded.  Both are single cells by construction (b_nat2text and
                 b_expand refuse anything over MAX_WORD), so this is an allowance of
                 two CELLS, not of bytes.

   So MAX_WORDS = 8 192 + 8 192 + 256 + 2 = 16 642 cells, one uint32 length plus
   MAX_WORD uint32 codes each (measured: 1028 bytes per cell, so the slab is the
   dominant static allocation and JPL.md §9.2's decision 3 keeps it honest).  It sits
   ABOVE MAX_STACK and BELOW GLOB_FUEL (cap_words_order), which is why §1's
   total-order chain had to grow rather than absorb it.

   SPELLING.  Written with qualified Nat.add because a 16 642 Coq literal would
   extract as a 16 642-application Stdlib.Int.succ chain into a vendored artifact,
   and because the §1.1 driver hooks bind on the qualified names. *)
Definition MAX_WORDS : nat :=
  Nat.add (Nat.add MAX_STACK MAX_STACK)
          (Nat.add (Nat.add MAX_ENV MAX_ENV) (S (S O))).

(* The word pool is the one capacity that is not in the chain MAX_WIDTH … MAX_STACK,
   so its position in the order is proved separately: it dominates the frame pool it
   pays for and still fits under the scan budget, hence under MAX_FUEL, hence in the
   fixed-width word. *)
Lemma cap_words_order : MAX_STACK <= MAX_WORDS /\ MAX_WORDS <= GLOB_FUEL.
Proof.
  (* The left half is pure addition, so the kernel numbers decide it.  The right half
     compares against GLOB_FUEL, whose body is a PRODUCT: lia leaves the factors
     symbolic and cannot see the nonlinearity is closed, which is exactly why
     cap_fuel_order below decides the same comparison by computation. *)
  split.
  - unfold MAX_WORDS, MAX_STACK, MAX_ENV. lia.
  - unfold MAX_WORDS, MAX_STACK, MAX_ENV, GLOB_FUEL. apply Nat.leb_le. vm_compute.
    reflexivity.
Qed.

(* The word pool stays under the machine's own fuel budget, so it is below MAX_FUEL
   and therefore inside the fixed-width word by §1's remark on MAX_FUEL.  Stated as a
   comparison with MAX_FUEL rather than with 2^32-1 on purpose: a literal 4294967295
   as a Coq nat is four billion constructors, which no tactic here needs to touch. *)
Lemma MAX_WORDS_lt_fuel : MAX_WORDS < MAX_FUEL.
Proof.
  (* MAX_WORDS <= GLOB_FUEL (cap_words_order) and MAX_FUEL is GLOB_FUEL plus the
     step allowance, so the pool budget is strictly under the fuel budget.  GLOB_FUEL
     is deliberately left symbolic here — expanding it would expose the product. *)
  pose proof (proj2 cap_words_order) as Hw.
  unfold MAX_FUEL. lia.
Qed.

(* The caps are totally ordered and MAX_FUEL is now the largest — MAX_STACK sits
   under GLOB_FUEL, which underlies MAX_FUEL (cap_fuel_order below).  Since
   MAX_FUEL = 136 449 is three orders of magnitude below 2^31, every value this
   layer produces (bounded above by MAX_FUEL) fits the fixed-width uint32 word, so
   the emitted C never wraps. *)
Lemma cap_order :
  MAX_WIDTH <= MAX_WORD /\ MAX_ARGV <= MAX_ENV /\ MAX_ENV <= MAX_LIST /\
  MAX_LIST <= MAX_CMD /\ MAX_CMD <= MAX_STACK.
Proof. unfold MAX_WIDTH, MAX_WORD, MAX_ARGV, MAX_ENV, MAX_LIST, MAX_CMD, MAX_STACK. lia. Qed.

(* The two fuel links.  GLOB_FUEL <= MAX_FUEL is pure structure (MAX_FUEL is this
   budget plus a positive allowance).  MAX_STACK <= GLOB_FUEL is a closed decision
   on the two literals, checked by the VM rather than by building a 132 353-node
   Peano term by hand. *)
Lemma cap_fuel_order : MAX_STACK <= GLOB_FUEL /\ GLOB_FUEL <= MAX_FUEL.
Proof.
  split.
  - unfold MAX_STACK, GLOB_FUEL. apply Nat.leb_le. vm_compute. reflexivity.
  - unfold MAX_FUEL. lia.
Qed.

(* ═══════════════════════════════════════════════════════════════════
   §1.1  The cap table as DATA the extracted artifact carries (5-B.2a; the
   jpl_words field added 2026-10-05 so JPL.5-B.3 can link — see MAX_WORDS in §1)

   WHY THIS SECTION EXISTS.  JPL.md §6's C layout allocates against every constant
   above, but Coq's Extraction emits a constant only where the *code* mentions it:
   MAX_WORD, MAX_ENV, MAX_LIST, GLOB_FUEL and MAX_FUEL already reach sh_run_c.ml
   because a kernel guard compares with them, while MAX_WIDTH, MAX_ARGV, MAX_CMD,
   MAX_STACK and MAX_WORDS occur in proofs only and would simply be dropped.  The
   emitter must not keep its own copy of those five —
   that is a second, unchecked encoding of a LOCKED table, and this project has
   already retired a parallel encoding (sh_model.ml) for exactly that reason.
   So the table is exported as one value that the extraction driver names, and
   jpl_caps_are_locked below re-proves every field against the §1 literal: a
   cap that drifts breaks the model build rather than silently resizing a pool.

   WHY TWO FIELDS ARE DERIVED RATHER THAN COPIED.  Two independent reasons
   agree here.  (i) Size: ExtrOcamlNatInt renders a nat literal as one
   Stdlib.Int.succ per unit, so jpl_cmd := MAX_CMD would put a 4096-application
   chain (about a thousand lines) into a vendored artifact, and MAX_STACK would
   double it.  (ii) Provenance: the compact spellings are the *justifications*
   JPL.md §4.1 already gives, turned into definitions — the margin between the
   two fuel caps is exactly the node pool (max_fuel_margin_eq_MAX_CMD, proved in
   sh_jpl_run_c.v §5.4 and re-proved here locally), and the frame cap is
   documented as 2·MAX_CMD.  Nothing is re-chosen; the arithmetic identities are
   checked by lia against the literals, so a future change to MAX_FUEL's
   allowance would fail the pin rather than silently move the pool size.

   case_site_fuel is deliberately absent: it is a guard *threshold* the machine
   is handed at runtime, not a capacity something is allocated against.

   Nat.sub / Nat.add are written qualified, not as - / +, so the extraction
   driver's Extract Constant hooks (clamped subtraction, int addition) bind on
   these exact constants — the TOOLCHAIN GOTCHA recorded in sh_extract_jpl_c.v.
   ═══════════════════════════════════════════════════════════════════ *)

(* The node pool capacity, read off the two fuel caps the artifact already
   carries.  MAX_FUEL >= GLOB_FUEL (cap_fuel_order), so the clamped subtraction
   never clamps. *)
Definition max_cmd_from_margin : nat := Nat.sub MAX_FUEL GLOB_FUEL.

Lemma max_cmd_from_margin_is_MAX_CMD : max_cmd_from_margin = MAX_CMD.
Proof. unfold max_cmd_from_margin, MAX_FUEL, MAX_CMD. lia. Qed.

(* The frame capacity: one frame per live continuation of a pool-sized program,
   which is what "MAX_STACK = 2·MAX_CMD" in JPL.md §4.1 states. *)
Definition max_stack_from_margin : nat :=
  Nat.add max_cmd_from_margin max_cmd_from_margin.

Lemma max_stack_from_margin_is_MAX_STACK : max_stack_from_margin = MAX_STACK.
Proof.
  unfold max_stack_from_margin, max_cmd_from_margin, MAX_STACK, MAX_FUEL, MAX_CMD.
  lia.
Qed.

Record jpl_caps : Type := JplCaps
  { jpl_width      : nat   (* bits in the fixed-width word  = MAX_WIDTH  *)
  ; jpl_word       : nat   (* bytes per text               = MAX_WORD    *)
  ; jpl_argv       : nat   (* argument words per simple cmd= MAX_ARGV    *)
  ; jpl_env        : nat   (* live shell variables         = MAX_ENV     *)
  ; jpl_list       : nat   (* any intermediate list length = MAX_LIST    *)
  ; jpl_cmd        : nat   (* cmd node pool capacity       = MAX_CMD     *)
  ; jpl_stack      : nat   (* frame pool capacity          = MAX_STACK   *)
  ; jpl_words      : nat   (* word (text) pool capacity    = MAX_WORDS   *)
  ; jpl_glob_fuel  : nat   (* one scan's own budget        = GLOB_FUEL   *)
  ; jpl_fuel       : nat   (* steps the machine may be given= MAX_FUEL   *)
  }.

Definition jpl_caps_table : jpl_caps :=
  {| jpl_width     := MAX_WIDTH
   ; jpl_word      := MAX_WORD
   ; jpl_argv      := MAX_ARGV
   ; jpl_env       := MAX_ENV
   ; jpl_list      := MAX_LIST
   ; jpl_cmd       := max_cmd_from_margin
   ; jpl_stack     := max_stack_from_margin
   ; jpl_words     := MAX_WORDS
   ; jpl_glob_fuel := GLOB_FUEL
   ; jpl_fuel      := MAX_FUEL
  |}.

(* ANTI-DRIFT PIN.  jpl_caps_table is the emitter's ONLY source for the numbers
   it sizes arrays with, so the table has to be pinned against §1's LOCKED
   constants inside the model: every exported field must equal the constant it
   names, and the table must keep §1's ordering chain (MAX_WIDTH is the word the
   others fit in, MAX_FUEL stays the largest value in the system), because the
   emitted C's array dimensions inherit both facts.

   FORM OF THE PIN.  The pin is stated as one decidable boolean and closed by
   the VM, for the same reason cap_fuel_order above is: every quantity involved
   is a closed nat, and a Prop-level `reflexivity` would ask the conversion
   machine to normalise 132 353-node Peano terms — work the VM does in
   milliseconds and the kernel does not have to be shown.  A drift in any cap,
   or in the derived spellings below, makes THIS lemma fail to compile, so the
   model build breaks instead of a pool silently resizing.
   The two fields that are not copied verbatim also carry Prop-level identity
   lemmas (max_cmd_from_margin_is_MAX_CMD, max_stack_from_margin_is_MAX_STACK),
   which are the transportable facts a later proof can cite; the boolean pin is
   the machine check over the whole table. *)
Definition jpl_caps_okb : bool :=
  Nat.eqb (jpl_width     jpl_caps_table) MAX_WIDTH  &&
  Nat.eqb (jpl_word      jpl_caps_table) MAX_WORD   &&
  Nat.eqb (jpl_argv      jpl_caps_table) MAX_ARGV   &&
  Nat.eqb (jpl_env       jpl_caps_table) MAX_ENV    &&
  Nat.eqb (jpl_list      jpl_caps_table) MAX_LIST   &&
  Nat.eqb (jpl_cmd       jpl_caps_table) MAX_CMD    &&
  Nat.eqb (jpl_stack     jpl_caps_table) MAX_STACK  &&
  Nat.eqb (jpl_words     jpl_caps_table) MAX_WORDS  &&
  Nat.eqb (jpl_glob_fuel jpl_caps_table) GLOB_FUEL  &&
  Nat.eqb (jpl_fuel      jpl_caps_table) MAX_FUEL   &&
  Nat.leb (jpl_width     jpl_caps_table) (jpl_word jpl_caps_table) &&
  Nat.leb (jpl_argv      jpl_caps_table) (jpl_env jpl_caps_table) &&
  Nat.leb (jpl_env       jpl_caps_table) (jpl_list jpl_caps_table) &&
  Nat.leb (jpl_list      jpl_caps_table) (jpl_cmd jpl_caps_table) &&
  Nat.leb (jpl_cmd       jpl_caps_table) (jpl_stack jpl_caps_table) &&
  Nat.leb (jpl_stack     jpl_caps_table) (jpl_words jpl_caps_table) &&
  Nat.leb (jpl_words     jpl_caps_table) (jpl_glob_fuel jpl_caps_table) &&
  Nat.leb (jpl_glob_fuel jpl_caps_table) (jpl_fuel jpl_caps_table).

Lemma jpl_caps_are_locked : jpl_caps_okb = true.
Proof. vm_compute. reflexivity. Qed.

(* ═══════════════════════════════════════════════════════════════════
   §2  Saturate-to-error result plumbing

   BLimit is the defined LIMIT_EXHAUSTED outcome: an operation that would cross
   a capacity or divide by zero yields BLimit rather than wrapping, truncating
   silently, or exceeding its fuel budget.  bbind threads a chain of bounded
   steps, short-circuiting to BLimit on the first exhaustion — the shape the
   JPL.3 step machine will iterate.
   ═══════════════════════════════════════════════════════════════════ *)

Inductive bres (A : Type) : Type :=
  | BOk    : A -> bres A
  | BLimit : bres A.

(* Coq 9.2 does not infer the type parameter here, so mark it implicit explicitly
   (mirroring how the stdlib declares option's constructors). *)
Arguments BOk {A} _.
Arguments BLimit {A}.

Definition bbind {A B : Type} (x : bres A) (f : A -> bres B) : bres B :=
  match x with
  | BOk a => f a
  | BLimit => BLimit
  end.

Definition bmap {A B : Type} (f : A -> B) (x : bres A) : bres B :=
  match x with
  | BOk a => BOk (f a)
  | BLimit => BLimit
  end.

(* An over-budget fuel request is refused up front: the machine may never be
   handed a fuel argument larger than MAX_FUEL, which is what keeps the emitted
   loop counter inside the word and guarantees termination. *)
Definition b_fuel (f : nat) : bres nat :=
  if Nat.leb f MAX_FUEL then BOk f else BLimit.

(* ═══════════════════════════════════════════════════════════════════
   §3  Fixed-width unsigned arithmetic with a defined overflow policy

   A Coq nat in this layer denotes a uint32_t.  Each operation carries its own
   capacity and returns BLimit when the mathematical result would exceed it, so
   the emitted C never relies on wraparound.  Comparison is the total Nat
   primitive (never undefined here); division by zero is an explicit saturation,
   not the Coq Nat.div-0 = 0 convention leaking into the shell.
   ═══════════════════════════════════════════════════════════════════ *)

Definition b_add (cap a b : nat) : bres nat :=
  if Nat.leb (a + b) cap then BOk (a + b) else BLimit.

Definition b_sub (a b : nat) : bres nat :=
  if Nat.leb b a then BOk (a - b) else BLimit.

Definition b_mul (cap a b : nat) : bres nat :=
  if Nat.leb (a * b) cap then BOk (a * b) else BLimit.

Definition b_divmod (a b : nat) : bres (nat * nat) :=
  if Nat.eqb b 0 then BLimit else BOk (a / b, a mod b).

Lemma b_add_ok cap a b r : b_add cap a b = BOk r -> a + b = r /\ r <= cap.
Proof.
  unfold b_add; intros Hr.
  destruct (Nat.leb (a + b) cap) eqn:E; [| discriminate].
  apply Nat.leb_le in E. simpl in Hr. injection Hr as <-. lia.
Qed.

Lemma b_add_limit cap a b : b_add cap a b = BLimit -> cap < a + b.
Proof.
  unfold b_add; intros H.
  destruct (Nat.leb (a + b) cap) eqn:E; [| apply Nat.leb_gt in E; exact E].
  discriminate.
Qed.

Lemma b_sub_ok a b r : b_sub a b = BOk r -> b <= a /\ a - b = r.
Proof.
  unfold b_sub; intros Hr.
  destruct (Nat.leb b a) eqn:E; [| discriminate].
  apply Nat.leb_le in E. simpl in Hr. injection Hr as <-. lia.
Qed.

Lemma b_sub_limit a b : b_sub a b = BLimit -> a < b.
Proof.
  unfold b_sub; intros H.
  destruct (Nat.leb b a) eqn:E; [| apply Nat.leb_gt in E; exact E].
  discriminate.
Qed.

Lemma b_mul_ok cap a b r : b_mul cap a b = BOk r -> a * b = r /\ r <= cap.
Proof.
  unfold b_mul; intros Hr.
  destruct (Nat.leb (a * b) cap) eqn:E; [| discriminate].
  apply Nat.leb_le in E. simpl in Hr. injection Hr as <-. lia.
Qed.

Lemma b_divmod_ok a b q r : b_divmod a b = BOk (q, r) -> b <> 0 /\ q = a / b /\ r = a mod b.
Proof.
  unfold b_divmod; intros H.
  destruct (Nat.eqb b 0) eqn:E; [ discriminate | ].
  apply Nat.eqb_neq in E. simpl in H. injection H as <- <-. lia.
Qed.

Lemma b_divmod_limit a b : b_divmod a b = BLimit -> b = 0.
Proof.
  unfold b_divmod; intros H.
  destruct (Nat.eqb b 0) eqn:E; [ apply Nat.eqb_eq; exact E | discriminate ].
Qed.

Lemma b_fuel_ok f : b_fuel f = BOk f <-> f <= MAX_FUEL.
Proof.
  unfold b_fuel; split; intros H.
  - destruct (Nat.leb f MAX_FUEL) eqn:E; [ apply Nat.leb_le; exact E | discriminate H ].
  - destruct (Nat.leb f MAX_FUEL) eqn:E; [ reflexivity | apply Nat.leb_gt in E; lia ].
Qed.

(* The gate accepts exactly the scan budget §1 introduced: a machine handed
   GLOB_FUEL is not refused.  Without the raised MAX_FUEL this was BLimit — that
   is the whole content of the 2026-10-04 budget increase. *)
Lemma b_fuel_accepts_glob_fuel : b_fuel GLOB_FUEL = BOk GLOB_FUEL.
Proof. apply (proj2 (b_fuel_ok GLOB_FUEL)); apply (proj2 cap_fuel_order). Qed.

(* ═══════════════════════════════════════════════════════════════════
   §4  Bounded word: a byte array of capacity MAX_WORD carrying its length

   The record mirrors the emitted C encoding — a fixed-capacity array plus a
   length field.  Values are produced through smart constructors that refuse to
   exceed MAX_WORD (saturate-to-error).  raw_bword is the total injection used
   for already-in-budget literals; it is only ever shown well-formed for inputs
   already within the cap.
   ═══════════════════════════════════════════════════════════════════ *)

Record bword : Type := BW { bw_bytes : text; bw_len : nat }.

Definition wf_bword (w : bword) : Prop :=
  bw_len w = length (bw_bytes w) /\ bw_len w <= MAX_WORD.

Definition raw_bword (l : text) : bword := BW l (length l).

Definition mk_bword (l : text) : bres bword :=
  if Nat.leb (length l) MAX_WORD then BOk (raw_bword l) else BLimit.

(* Push one byte; saturates when the word is already at capacity. *)
Definition b_push (w : bword) (x : nat) : bres bword :=
  if Nat.leb (S (bw_len w)) MAX_WORD
  then BOk (BW (bw_bytes w ++ [x]) (S (bw_len w)))
  else BLimit.

(* Bounded append; saturates when the concatenation exceeds MAX_WORD. *)
Definition b_app (u v : bword) : bres bword :=
  if Nat.leb (bw_len u + bw_len v) MAX_WORD
  then BOk (BW (bw_bytes u ++ bw_bytes v) (bw_len u + bw_len v))
  else BLimit.

(* Word equality is the concrete byte test on the underlying arrays; reusing
   sh_concrete.teqb keeps a single definition of text equality. *)
Definition bword_eq (u v : bword) : bool := teqb (bw_bytes u) (bw_bytes v).

Lemma mk_bword_wf l :
  match mk_bword l with
  | BOk w => wf_bword w
  | BLimit => MAX_WORD < length l
  end.
Proof.
  unfold mk_bword, raw_bword; destruct (Nat.leb (length l) MAX_WORD) eqn:E.
  - unfold wf_bword; split; [ reflexivity | apply Nat.leb_le; exact E ].
  - apply Nat.leb_gt in E; exact E.
Qed.

Lemma raw_bword_wf l : length l <= MAX_WORD -> wf_bword (raw_bword l).
Proof. intros H. unfold wf_bword, raw_bword. split; [ reflexivity | exact H ]. Qed.

Lemma b_push_wf w x (Hw : wf_bword w) :
  match b_push w x with
  | BOk w' => wf_bword w'
  | BLimit => MAX_WORD <= bw_len w
  end.
Proof.
  unfold b_push; destruct (Nat.leb (S (bw_len w)) MAX_WORD) eqn:E.
  - apply Nat.leb_le in E. destruct Hw as [Hlen Hle].
    unfold wf_bword; cbn [bw_len bw_bytes]; rewrite length_app, <- Hlen; cbn [length]; lia.
  - apply Nat.leb_gt in E; lia.
Qed.

Lemma b_app_wf u v (Hu : wf_bword u) (Hv : wf_bword v) :
  match b_app u v with
  | BOk w => wf_bword w
  | BLimit => MAX_WORD < bw_len u + bw_len v
  end.
Proof.
  unfold b_app; destruct (Nat.leb (bw_len u + bw_len v) MAX_WORD) eqn:E.
  - apply Nat.leb_le in E. destruct Hu as [Hu1 Hu2]. destruct Hv as [Hv1 Hv2].
    unfold wf_bword; cbn [bw_len bw_bytes]; rewrite length_app, <- Hu1, <- Hv1; lia.
  - apply Nat.leb_gt in E; exact E.
Qed.

(* ═══════════════════════════════════════════════════════════════════
   §5  Bounded environment: an array of (name,value) word pairs up to MAX_ENV

   Lookup is the concrete getv: tail-recursive in its map argument and
   allocation-free, so it never saturates.  Update is bounded: setv either
   replaces in place (length unchanged) or appends the new binding at the end
   (length + 1); benv_setv refuses only when that result would exceed MAX_ENV,
   so a full map cannot grow past its capacity.

   Both carry `sh_concrete`'s `Fixpoint` shape, so Extraction emits `let rec`
   for them -- JPL Rule 6 recursion, and no fuel slot to report saturation in.
   The emitter-lowerable forms are the fuel-bounded tail loops `getv_it` /
   `setv_it` in `sh_jpl_scan.v` §5, which this file's `benv` API is proved to
   agree with; `be_getv` / `be_setv` are what extraction should consume.
   ═══════════════════════════════════════════════════════════════════ *)

Record benv : Type := BE { be_pairs : list (text * text); be_len : nat }.

Definition wf_benv (e : benv) : Prop :=
  be_len e = length (be_pairs e) /\ be_len e <= MAX_ENV.

Definition raw_benv (m : list (text * text)) : benv := BE m (length m).

Definition mk_benv (m : list (text * text)) : bres benv :=
  if Nat.leb (length m) MAX_ENV then BOk (raw_benv m) else BLimit.

Definition benv_getv (k : text) (e : benv) : option text := getv k (be_pairs e).

Definition benv_setv (k v : text) (e : benv) : bres benv :=
  if Nat.leb (length (setv k v (be_pairs e))) MAX_ENV
  then BOk (BE (setv k v (be_pairs e)) (length (setv k v (be_pairs e))))
  else BLimit.

Lemma mk_benv_wf m :
  match mk_benv m with
  | BOk e => wf_benv e
  | BLimit => MAX_ENV < length m
  end.
Proof.
  unfold mk_benv, raw_benv; destruct (Nat.leb (length m) MAX_ENV) eqn:E.
  - unfold wf_benv; split; [ reflexivity | apply Nat.leb_le; exact E ].
  - apply Nat.leb_gt in E; exact E.
Qed.

Lemma benv_getv_agree k e : benv_getv k e = getv k (be_pairs e).
Proof. reflexivity. Qed.

Lemma benv_setv_wf k v e :
  match benv_setv k v e with
  | BOk e' => wf_benv e'
  | BLimit => MAX_ENV < length (setv k v (be_pairs e))
  end.
Proof.
  unfold benv_setv; destruct (Nat.leb (length (setv k v (be_pairs e))) MAX_ENV) eqn:E.
  - unfold wf_benv; split; [ reflexivity | apply Nat.leb_le; exact E ].
  - apply Nat.leb_gt in E; exact E.
Qed.

(* setv never adds more than one cell, so a not-yet-full well-formed map always
   admits the update. *)
Lemma setv_length_le k v m : length (setv k v m) <= S (length m).
Proof.
  induction m as [ | [k' v'] m IH ].
  - cbn [setv length]; lia.
  - cbn [setv length]. destruct (teqb k k') eqn:E; cbn [length]; lia.
Qed.

Lemma benv_setv_fits k v e (Hw : wf_benv e) : be_len e < MAX_ENV -> { e' | benv_setv k v e = BOk e' }.
Proof.
  intros Hlt. destruct Hw as [Hlen Hcap].
  assert (Hle : length (setv k v (be_pairs e)) <= MAX_ENV).
  { pose proof (setv_length_le k v (be_pairs e)) as L. rewrite <- Hlen in L. lia. }
  unfold benv_setv.
  destruct (Nat.leb (length (setv k v (be_pairs e))) MAX_ENV) eqn:E.
  - exists (BE (setv k v (be_pairs e)) (length (setv k v (be_pairs e)))). reflexivity.
  - exfalso. apply Nat.leb_gt in E. lia.
Qed.

(* benv_words — the number of WORD CELLS a well-formed environment occupies in the
   slab: one cell per name plus one per value, so twice the pair count.  This is the
   summand MAX_WORDS pays for in §1, and it is the one summand proved outright rather
   than owed: wf_benv already caps be_pairs at MAX_ENV. *)
Definition benv_words (e : benv) : nat := Nat.add (be_len e) (be_len e).

Lemma benv_words_le e (Hw : wf_benv e) : benv_words e <= Nat.add MAX_ENV MAX_ENV.
Proof.
  destruct Hw as [_ Hcap].
  unfold benv_words. lia.
Qed.

(* ═══════════════════════════════════════════════════════════════════
   §6  Bounded machine state: an 8-bit status plus the bounded environment

   POSIX truncates the status to its low 8 bits, so it is always < 256 and never
   saturates the word.  The record pairs that bounded status with the bounded
   environment.
   ═══════════════════════════════════════════════════════════════════ *)

Record bcstate : Type := BCS { bc_status : nat; bc_env : benv }.

Definition wf_status (n : nat) : Prop := n < 256.

(* Reuses the concrete nstat; nstat_lt (from sh_concrete) shows it fits a byte. *)
Definition b_nstat (k : nat) : nat := nstat k.

Lemma b_nstat_lt : forall k, wf_status (b_nstat k).
Proof. intros k. unfold wf_status, b_nstat. apply nstat_lt. Qed.

(* ═══════════════════════════════════════════════════════════════════
   §7  Bounded command pool: a node-count upper bound for the lowered cmd tree

   The emitted C holds a program's `cmd` tree in a static pool of MAX_CMD nodes.
   cmd_count is a fuel-bounded size estimate (a node counts itself plus its
   children and argument/branch payloads); using fuel keeps it a safe fixpoint
   with no nested-recursion obligations, and it never under-counts, so a program
   whose cmd_count fits MAX_CMD is guaranteed to fit the pool.  cmd_fits is the
   lowering-time gate the bridge checks before handing a tree to the machine.
   ═══════════════════════════════════════════════════════════════════ *)

Fixpoint cmd_count_list (f : nat) (l : list cmd) : nat :=
  match f with
  | 0 => 0
  | S f' => match l with
            | [] => 0
            | c :: r => cmd_count f' c + cmd_count_list f' r
            end
  end

with cmd_count_pair (f : nat) (pb : list text * list cmd) : nat :=
  match f with
  | 0 => 0
  | S f' => length (fst pb) + cmd_count_list f' (snd pb)
  end

with cmd_count_pairs (f : nat) (l : list (list text * list cmd)) : nat :=
  match f with
  | 0 => 0
  | S f' => match l with
            | [] => 0
            | pb :: r => cmd_count_pair f' pb + cmd_count_pairs f' r
            end
  end

with cmd_count (f : nat) (c : cmd) : nat :=
  match f with
  | 0 => 0
  | S f' =>
      match c with
      | Skip => 1
      | Ext _ argv => S (length argv)
      | Assign _ _ => 1
      | Seq c1 c2 => S (cmd_count f' c1 + cmd_count f' c2)
      | And c1 c2 => S (cmd_count f' c1 + cmd_count f' c2)
      | Or c1 c2 => S (cmd_count f' c1 + cmd_count f' c2)
      | Bang c0 => S (cmd_count f' c0)
      | If cond t e => S (cmd_count f' cond + (cmd_count f' t + cmd_count f' e))
      | While cond body => S (cmd_count f' cond + cmd_count f' body)
      | For _ ws body => S (length ws + cmd_count_list f' body)
      | Case _ brs => S (cmd_count_pairs f' brs)
      end
  end.

(* A lowered program is pool-safe when its node estimate fits MAX_CMD under a
   depth bound large enough to reach every node (a tree of D nodes has depth
   <= D, so MAX_CMD is its own sufficient depth bound). *)
Definition cmd_fits (c : cmd) : bool := Nat.leb (cmd_count MAX_CMD c) MAX_CMD.

Example cmd_fits_skip : cmd_fits Skip = true.
Proof. unfold cmd_fits. reflexivity. Qed.

Example cmd_fits_seq_true_false :
  cmd_fits (Seq (Ext 0 [true_w]) (Ext 0 [false_w])) = true.
Proof. unfold cmd_fits. reflexivity. Qed.

(* ═══════════════════════════════════════════════════════════════════
   §7.1  Word OCCURRENCES in a tree: cmd_words, dominated by 2 * cmd_count

   §7's node estimate charges a COARSER price than the word slab pays, and the
   coarseness is not one-sided: an Assign node holds TWO texts (name and value)
   but is charged a single node, and a For node's loop variable and a Case node's
   scrutinee are each a word absorbed into the node's own "+1".  cmd_words counts
   words honestly — Ext's argv, Assign's two texts, For's variable plus its word
   list, Case's scrutinee plus every branch pattern — with the same fuel discipline
   as §7 so it is a safe fixpoint.

   This section's lemma is the domination §1's MAX_WORDS summand rests on: with the
   SAME fuel, cmd_words is at most TWICE cmd_count.  The factor 2 is exact, not
   slack: a leaf `Assign k v` has cmd_words = 2 and cmd_count = 1, so equality is
   attained and no smaller constant is provable from these definitions.

   WHAT THE LEMMA DOES NOT SAY.  It bounds the words in a tree the pool admits; it
   says nothing about the words a RUNNING program additionally materialises (the
   expanded list held by an FFor/FCase frame).  That is §1's second summand and it
   is still an obligation, named there, not discharged here.
   ═══════════════════════════════════════════════════════════════════ *)

Fixpoint cmd_words_list (f : nat) (l : list cmd) : nat :=
  match f with
  | 0 => 0
  | S f' => match l with
            | [] => 0
            | c :: r => cmd_words f' c + cmd_words_list f' r
            end
  end

with cmd_words_pair (f : nat) (pb : list text * list cmd) : nat :=
  match f with
  | 0 => 0
  | S f' => length (fst pb) + cmd_words_list f' (snd pb)
  end

with cmd_words_pairs (f : nat) (l : list (list text * list cmd)) : nat :=
  match f with
  | 0 => 0
  | S f' => match l with
            | [] => 0
            | pb :: r => cmd_words_pair f' pb + cmd_words_pairs f' r
            end
  end

with cmd_words (f : nat) (c : cmd) : nat :=
  match f with
  | 0 => 0
  | S f' =>
      match c with
      | Skip => 0
      | Ext _ argv => length argv
      | Assign _ _ => S (S O)
      | Seq c1 c2 => cmd_words f' c1 + cmd_words f' c2
      | And c1 c2 => cmd_words f' c1 + cmd_words f' c2
      | Or c1 c2 => cmd_words f' c1 + cmd_words f' c2
      | Bang c0 => cmd_words f' c0
      | If cond t e => cmd_words f' cond + (cmd_words f' t + cmd_words f' e)
      | While cond body => cmd_words f' cond + cmd_words f' body
      | For _ ws body => S (length ws) + cmd_words_list f' body
      | Case _ brs => S (cmd_words_pairs f' brs)
      end
  end.

(* One conjunction, so the induction hypothesis carries a bound for every child of
   every shape (command list, branch pair, branch-pair list, command) at the previous
   fuel.  The four statements are proved together because cmd_words_list calls
   cmd_words and vice versa. *)
Lemma cmd_words_le_count :
  forall (f : nat) (c : cmd) (l : list cmd)
         (pl : list (list text * list cmd)) (pb : list text * list cmd),
      cmd_words_list f l <= 2 * cmd_count_list f l
  /\  cmd_words_pairs f pl <= 2 * cmd_count_pairs f pl
  /\  cmd_words_pair f pb <= 2 * cmd_count_pair f pb
  /\  cmd_words f c <= 2 * cmd_count f c.
Proof.
  induction f as [| f' IHf]; intros c l pl pb.
  - cbn [cmd_words_list cmd_count_list cmd_words_pairs cmd_count_pairs
         cmd_words_pair cmd_count_pair cmd_words cmd_count]; lia.
  - split; [ | split; [ | split ] ].
    (* list of commands: the empty case is 0 <= 0; a cons is one command plus one list *)
    + destruct l as [| c0 lrest]; cbn [cmd_words_list cmd_count_list].
      * lia.
      * pose proof (IHf c0 lrest pl pb) as I.
        destruct I as [IL [_ [_ IC]]]. lia.
    (* list of branch pairs: one pair plus one list *)
    + destruct pl as [| pb0 plrest]; cbn [cmd_words_pairs cmd_count_pairs].
      * lia.
      * pose proof (IHf c l plrest pb0) as I.
        destruct I as [_ [B [C _]]]. lia.
    (* one branch pair: its pattern list plus its body list.  The pair's projections
        must be reduced too — destruct pb leaves fst (pats, body) in the goal, which
        would not match the induction hypothesis's shape. *)
    + destruct pb as [pats body]. cbn [cmd_words_pair cmd_count_pair fst snd].
      pose proof (IHf c body pl (nil, nil)) as I. destruct I as [A _]. lia.
    (* one command: the node's own words against the node's own charge *)
    + destruct c as [ | idx argv | k v | c1 c2 | c1 c2 | c1 c2 | c0
                      | cond t e | cond body | var ws body | scrut brs ];
        cbn [cmd_words cmd_count].
      * lia.                                       (* Skip: 0 words, 1 node *)
      * lia.                                       (* Ext: argv <= 2 * S argv *)
      * lia.                                       (* Assign: 2 = 2 * 1, equality *)
      * pose proof (IHf c1 l pl pb) as I1. destruct I1 as [_ [_ [_ D1]]].
        pose proof (IHf c2 l pl pb) as I2. destruct I2 as [_ [_ [_ D2]]]. lia.
      * pose proof (IHf c1 l pl pb) as I1. destruct I1 as [_ [_ [_ D1]]].
        pose proof (IHf c2 l pl pb) as I2. destruct I2 as [_ [_ [_ D2]]]. lia.
      * pose proof (IHf c1 l pl pb) as I1. destruct I1 as [_ [_ [_ D1]]].
        pose proof (IHf c2 l pl pb) as I2. destruct I2 as [_ [_ [_ D2]]]. lia.
      * pose proof (IHf c0 l pl pb) as I. destruct I as [_ [_ [_ D]]]. lia.
      * pose proof (IHf cond l pl pb) as I1. destruct I1 as [_ [_ [_ D1]]].
        pose proof (IHf t l pl pb) as I2. destruct I2 as [_ [_ [_ D2]]].
        pose proof (IHf e l pl pb) as I3. destruct I3 as [_ [_ [_ D3]]]. lia.
      * pose proof (IHf cond l pl pb) as I1. destruct I1 as [_ [_ [_ D1]]].
        pose proof (IHf body l pl pb) as I2. destruct I2 as [_ [_ [_ D2]]]. lia.
      * pose proof (IHf Skip body pl (nil, nil)) as I. destruct I as [IL _]. lia.
      * pose proof (IHf Skip l brs pb) as I. destruct I as [_ [B _]]. lia.
Qed.

(* The summand §1 pays for: a pool-admitting program holds at most MAX_STACK word
   cells — two per counted node, and the node budget is MAX_CMD, and
   MAX_STACK = 2 * MAX_CMD. *)

(* WHY THE BRIDGE IS WRITTEN AS A REWRITE RATHER THAN AN UNFOLD, with the numbers
   that decided it (measured 2026-10-05 on this file's §1..§7.1 prefix, which
   itself compiles in 5 s):

     unfold cmd_fits in Hf  +  Nat.leb_le      ->  >600 s, never finished
     exact Hf  at  (cmd_fits c = true) |- (cmd_count MAX_CMD c <=? MAX_CMD) = true
                                               ->  >45 s, and >45 s again with the
                                                  fuel written as 128 instead of 4096
     rewrite cmd_fits_unfold in Hf  (below)    ->  5.1 s
     the whole assembly, this file's shape     ->  5.2 s

   The cost is not the size of the fuel numeral (128 is as bad as 4096), it is the
   fuel-bounded fixpoint being REDUCED during a conversion.  `cmd_fits c` and
   `Nat.leb (cmd_count MAX_CMD c) MAX_CMD` sit on opposite sides of an `eq bool …
   true` whose parameter has to be made to match, so the kernel whnf's both sides:
   whnf of `Nat.leb x MAX_CMD` forces whnf of `cmd_count MAX_CMD c`, which unfolds
   the fixpoint into the eleven-way `match c with` whose branches each hold another
   `cmd_count f' …`.  Comparing those branch-by-branch re-enters the same reduction
   at every depth, so one definitional unfolding costs the whole unrolled recursion
   tree.  The two sides of `cmd_fits_unfold` are compared as TERMS (head `Nat.leb`
   on both after one delta, arguments then identical), which short-circuits before
   any of that — which is why `reflexivity` there is instant and the same equation
   reached through an `exact`/`unfold` cast is not.  Recorded here because the trap
   is invisible from the statement: the two spellings prove the same fact. *)
Lemma cmd_fits_unfold c : cmd_fits c = Nat.leb (cmd_count MAX_CMD c) MAX_CMD.
Proof. reflexivity. Qed.

Lemma cmd_fits_le c (Hf : cmd_fits c = true) : cmd_count MAX_CMD c <= MAX_CMD.
Proof.
  rewrite cmd_fits_unfold in Hf.
  apply Nat.leb_le.
  exact Hf.
Qed.

Corollary cmd_fits_words c (Hf : cmd_fits c = true) : cmd_words MAX_CMD c <= MAX_STACK.
Proof.
  pose proof (cmd_fits_le c Hf) as Hc.
  pose proof (cmd_words_le_count MAX_CMD c [] [] (nil, nil)) as I.
  destruct I as [_ [_ [_ D]]].
  (* The chain is cmd_words <= 2*cmd_count <= 2*MAX_CMD = MAX_STACK.  Every step is
     one stdlib lemma, not `lia`: a linear-arithmetic proof term over an atom that
     mentions the recursive `cmd_count` drags the same reduction storm into Qed.
     MAX_STACK stays symbolic for the same reason; the closed-numeral last step is
     decided by conversion against `Nat.le_refl`, whose argument is a numeral. *)
  apply Nat.le_trans with (m := 2 * cmd_count MAX_CMD c). { exact D. }
  apply Nat.le_trans with (m := 2 * MAX_CMD).
  - apply Nat.mul_le_mono_l. exact Hc.
  - exact (Nat.le_refl MAX_STACK).
Qed.

Example cmd_words_assign_is_two : cmd_words 1 (Assign true_w false_w) = 2.
Proof. reflexivity. Qed.

Example cmd_words_le_count_attained :
  cmd_words 1 (Assign true_w false_w) = 2 * cmd_count 1 (Assign true_w false_w).
Proof. reflexivity. Qed.

(* ═══════════════════════════════════════════════════════════════════
   §8  Bounded scan wrappers: expansion and glob matching

   These wrap the fuel-bounded concrete functions with the bounded contract the
   JPL.3 machine must preserve: reject over-budget fuel up front, and saturate
   when an expanded word would exceed MAX_WORD.  The concrete scan produces the
   bytes; the wrapper decides whether they fit.  Byte classification and the
   decimal renderer are the concrete total helpers (no allocation), reused as-is.
   ═══════════════════════════════════════════════════════════════════ *)

(* Decimal rendering of a status, checked to fit a word (statuses are <= 255 so
   this is always three digits, but the bound is stated, not assumed). *)
Definition b_nat2text (n : nat) : bres bword :=
  if Nat.leb (length (nat2text n)) MAX_WORD
  then BOk (raw_bword (nat2text n))
  else BLimit.

(* Bounded expansion of one word against a bounded environment at status st. *)
Definition b_expand (f : nat) (e : benv) (st : nat) (inp : text) : bres bword :=
  bbind (b_fuel f)
    (fun f' =>
       let w := expand f' (be_pairs e) st inp in
       if Nat.leb (length w) MAX_WORD then BOk (raw_bword w) else BLimit).

(* Glob matching and first-match are pure boolean scans (no allocation); only
   the fuel budget is checked, so they saturate to BLimit on over-budget fuel and
   otherwise return the concrete decision. *)
Definition b_glob (f : nat) (pat str : text) : bres bool :=
  bbind (b_fuel f) (fun f' => BOk (glob f' pat str)).

Definition b_match_any (f : nat) (pats : list text) (scrut : text) : bres bool :=
  bbind (b_fuel f) (fun f' => BOk (match_any f' pats scrut)).

(* ═══════════════════════════════════════════════════════════════════
   §9  Behavioural isomorphism with sh_concrete, and saturation, by computation

   Each bounded wrapper returns the concrete result wrapped in BOk for the §8
   corpus of sh_concrete.v, and refuses (BLimit) once a capacity is crossed —
   the same discipline the JPL.3 machine must keep.  All Examples are checked by
   pure computation (reflexivity), so no proof relies on an axiom.
   ═══════════════════════════════════════════════════════════════════ *)

Example iso_expand_var_present :
  b_expand 4 (raw_benv [([97], [98])]) 0 [36; 97] = BOk (raw_bword [98]).
Proof. reflexivity. Qed.

Example iso_expand_var_unset :
  b_expand 4 (raw_benv []) 0 [36; 97] = BOk (raw_bword []).
Proof. reflexivity. Qed.

Example iso_expand_var_brace :
  b_expand 6 (raw_benv [([97], [98])]) 0 [36; 123; 97; 125] = BOk (raw_bword [98]).
Proof. reflexivity. Qed.

Example iso_expand_status_zero :
  b_expand 2 (raw_benv []) 0 [36; 63] = BOk (raw_bword [48]).
Proof. reflexivity. Qed.

Example iso_expand_status_one :
  b_expand 2 (raw_benv []) 1 [36; 63] = BOk (raw_bword [49]).
Proof. reflexivity. Qed.

Example iso_expand_over_fuel_saturates :
  b_expand (MAX_FUEL + 1) (raw_benv []) 0 [36; 97] = BLimit.
Proof. unfold b_expand; reflexivity. Qed.

Example iso_glob_star : b_glob 6 [97; 42] [97; 99; 100] = BOk true.
Proof. unfold b_glob; reflexivity. Qed.

Example iso_glob_question : b_glob 3 [97; 63] [97; 99] = BOk true.
Proof. unfold b_glob; reflexivity. Qed.

Example iso_glob_mismatch : b_glob 4 [97; 98] [97; 99] = BOk false.
Proof. unfold b_glob; reflexivity. Qed.

Example iso_match_any : b_match_any 6 [[97]; [42]] [97] = BOk true.
Proof. unfold b_match_any; reflexivity. Qed.

Example iso_getv_present : benv_getv [97] (raw_benv [([97], [98])]) = Some [98].
Proof. reflexivity. Qed.

Example iso_setv_binds :
  benv_setv [97] [98] (raw_benv []) = BOk (raw_benv [([97], [98])]).
Proof. reflexivity. Qed.

(* Saturate-to-error on the fixed-width arithmetic and the div-by-zero seam. *)
Example iso_add_within : b_add MAX_WORD 200 50 = BOk 250.
Proof. reflexivity. Qed.

Example iso_add_saturates : b_add MAX_WORD 200 100 = BLimit.
Proof. reflexivity. Qed.

Example iso_divzero_saturates : b_divmod 5 0 = BLimit.
Proof. unfold b_divmod. reflexivity. Qed.
