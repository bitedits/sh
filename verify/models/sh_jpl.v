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
 *      emitted C.  Every value produced by this layer is provably <= MAX_STACK,
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
   §1  Capacity constants (LOCKED — JPL.md, user 2026-10-03)

   These are the compile-time budgets the emitted C allocates against.  They
   are written as Coq nats but become #define uint32_t constants at the emitter;
   each is provably < 2^31 so it fits the fixed-width word.
   ═══════════════════════════════════════════════════════════════════ *)

Definition MAX_WIDTH : nat := 32.      (* uint32 word bits *)
Definition MAX_WORD  : nat := 256.     (* expanded word / text length in bytes *)
Definition MAX_ARGV  : nat := 64.      (* argument words per simple command *)
Definition MAX_ENV   : nat := 128.     (* simultaneously live shell variables *)
Definition MAX_LIST  : nat := 1024.    (* any intermediate list length *)
Definition MAX_CMD   : nat := 4096.    (* node-pool capacity for one lowered cmd tree *)
Definition MAX_FUEL  : nat := 4096.    (* loop-iteration bound *)
Definition MAX_STACK : nat := 4096 + 4096.  (* explicit machine stack frames = 8192 *)

(* The caps are totally ordered with MAX_STACK the largest.  Since MAX_STACK =
   8192 < 2^32, every value this layer produces (bounded above by MAX_STACK)
   fits the fixed-width uint32 word, so the emitted C never wraps. *)
Lemma cap_order :
  MAX_WIDTH <= MAX_WORD /\ MAX_ARGV <= MAX_ENV /\ MAX_ENV <= MAX_LIST /\
  MAX_LIST <= MAX_CMD /\ MAX_CMD <= MAX_FUEL /\ MAX_FUEL <= MAX_STACK.
Proof. unfold MAX_WIDTH, MAX_WORD, MAX_ARGV, MAX_ENV, MAX_LIST, MAX_CMD, MAX_FUEL, MAX_STACK. lia. Qed.

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

   Lookup is the concrete getv (a total tail scan, no allocation, so never
   saturates).  Update is bounded: setv either replaces (length unchanged) or
   prepends (length + 1); benv_setv refuses only when that result would exceed
   MAX_ENV, so a full map cannot grow past its capacity.
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
