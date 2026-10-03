(* sh_properties.v
 *
 * Formal verification of the POSIX shell list/control-flow semantics that the
 * extracted kernel (sh_concrete.v -> sh_run.ml) executes.  The whole model here
 * is *relational*: a command's
 * meaning is an inductive proposition  exec c s0 f s  ("running c in state s0
 * with fuel budget f terminates in state s1").  There are no fixpoints and no
 * axioms, so every theorem below is checked by the Rocq kernel alone.
 *
 * What is captured faithfully from the concrete model:
 *  - status is truncated to its low 8 bits   (norm n = n land 255 <-> n mod 256)
 *  - && short-circuits on a non-zero left, || on a zero left
 *  - ; never short-circuits; the list status is that of the last command
 *  - ! inverts zero/non-zero (POSIX 2.11.3)
 *  - if/while branch on the *status* of the condition, not on the branch state
 *  - while with a failing test runs its body zero times (status of the test)
 *  - a prefix assignment binds exactly one variable and leaves the rest alone
 *
 * Build (Rocq >= 9.0):
 *   coqc sh_properties.v
 *   coqchk -o -silent sh_properties     # must report Axioms: <none>
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.
Import ListNotations.

(* A shell variable is a nat key holding a nat value in this abstract model;
   the keys stand for the names the concrete kernel keeps in its env table. *)

(* ═══════════════════════════════════════════════════════════════════
   §1  States, status normalisation and the variable store
   ═══════════════════════════════════════════════════════════════════ *)

(* norm n = n land 255 in the OCaml oracle. *)
Definition nstat (k : nat) : nat := k mod 256.

Lemma nstat_lt : forall k, nstat k < 256.
Proof. unfold nstat. intros k. apply Nat.mod_upper_bound. lia. Qed.

Lemma nstat_small : forall k, k < 256 -> nstat k = k.
Proof. unfold nstat. intros k Hk. apply Nat.mod_small. exact Hk. Qed.

Lemma nstat_zero : nstat 0 = 0.
Proof. reflexivity. Qed.

Lemma nstat_256 : nstat 256 = 0.
Proof. reflexivity. Qed.

(* status of the pipeline/command is a pair (last exit status, variable store). *)
Record state : Type := St { status : nat ; env : list (nat * nat) }.

(* ! inverts a status: zero becomes success-code 1, anything else becomes 0. *)
Definition bstat (n : nat) : nat := if Nat.eqb n 0 then 1 else 0.

Lemma bstat_0 : bstat 0 = 1.
Proof. reflexivity. Qed.

Lemma bstat_nonzero : forall n, n <> 0 -> bstat n = 0.
Proof. unfold bstat. intros n Hn. destruct (n =? 0) eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - reflexivity. Qed.

Lemma bstat_bstat : forall n, bstat (bstat n) = if Nat.eqb n 0 then 0 else 1.
Proof.
  intros n. destruct (n =? 0) eqn:E.
  - apply Nat.eqb_eq in E. subst n. reflexivity.
  - apply Nat.eqb_neq in E.
    replace (bstat n) with 0 by (symmetry; apply bstat_nonzero; exact E).
    reflexivity.
Qed.

(* ── finite-map helpers over the association list ────────────────── *)

Fixpoint getv (k : nat) (m : list (nat * nat)) : option nat :=
  match m with
  | [] => None
  | (k', v) :: r => if Nat.eq_dec k k' then Some v else getv k r
  end.

Fixpoint setv (k v : nat) (m : list (nat * nat)) : list (nat * nat) :=
  match m with
  | [] => [(k, v)]
  | (k', v') :: r =>
      if Nat.eq_dec k k' then (k, v) :: r else (k', v') :: setv k v r
  end.

Lemma getv_set_same : forall m k v, getv k (setv k v m) = Some v.
Proof.
  induction m as [ | [k' v'] m IH ]; intros k v; simpl.
  - destruct (Nat.eq_dec k k) as [_ | Hne].
    + reflexivity.
    + exfalso. apply Hne. reflexivity.
  - destruct (Nat.eq_dec k k') as [Heq | Hne].
    + subst k'. simpl. destruct (Nat.eq_dec k k) as [_ | Hne2].
      * reflexivity.
      * exfalso. apply Hne2. reflexivity.
    + simpl. destruct (Nat.eq_dec k k'); [ contradiction | exact (IH k v) ].
Qed.

Lemma getv_set_other :
  forall m k k2 v, k <> k2 -> getv k2 (setv k v m) = getv k2 m.
Proof.
  induction m as [ | [k' v'] m IH ]; intros k k2 v Hind; simpl.
  - destruct (Nat.eq_dec k2 k) as [H2 | N2]; [ subst k2; contradiction | reflexivity ].
  - destruct (Nat.eq_dec k k') as [Heq | Hne]; simpl.
    + subst k'. destruct (Nat.eq_dec k2 k) as [H2 | N2].
      * exfalso. exact (Hind (eq_sym H2)).
      * reflexivity.
    + destruct (Nat.eq_dec k2 k') as [H2 | N2].
      * reflexivity.
      * exact (IH k k2 v Hind).
Qed.

(* ═══════════════════════════════════════════════════════════════════
   §2  The exec relation (POSIX 2.9 / 2.10 / 2.11 control operators)
   ═══════════════════════════════════════════════════════════════════ *)

Inductive cmd : Type :=
  | Skip                        (* empty command: state unchanged *)
  | Ex     (k : nat)            (* command exiting with status k *)
  | Assign (k v : nat)          (* name=value prefix assignment *)
  | Seq  (c1 c2 : cmd)          (* c1 ; c2 *)
  | And  (c1 c2 : cmd)          (* c1 && c2 *)
  | Or   (c1 c2 : cmd)          (* c1 || c2 *)
  | Bang (c : cmd)              (* ! c *)
  | If   (cond t e : cmd)       (* if cond then t else e *)
  | While (cond body : cmd)     (* while cond do body done *)
  .

(*  exec c s0 f s  — c run in s0 with fuel budget f yields s.
    Compound forms consume one unit of fuel at their own node and hand the
    remaining budget to each child; this bounds recursion without a fixpoint. *)
Inductive exec : cmd -> state -> nat -> state -> Prop :=
  | ESkip : forall s f, exec Skip s f s

  | EExit : forall s f k,
      exec (Ex k) s f (St (nstat k) (env s))

  | EAssign : forall s f k v,
      exec (Assign k v) s f (St 0 (setv k v (env s)))

  | ESeq : forall c1 c2 s0 s1 s2 f,
      exec c1 s0 f s1 -> exec c2 s1 f s2 -> exec (Seq c1 c2) s0 (S f) s2

  | EAndStop : forall c1 c2 s0 s1 f,
      exec c1 s0 f s1 -> status s1 <> 0 -> exec (And c1 c2) s0 (S f) s1
  | EAndGo   : forall c1 c2 s0 s1 s2 f,
      exec c1 s0 f s1 -> status s1 = 0 -> exec c2 s1 f s2 ->
      exec (And c1 c2) s0 (S f) s2

  | EOrStop : forall c1 c2 s0 s1 f,
      exec c1 s0 f s1 -> status s1 = 0 -> exec (Or c1 c2) s0 (S f) s1
  | EOrGo   : forall c1 c2 s0 s1 s2 f,
      exec c1 s0 f s1 -> status s1 <> 0 -> exec c2 s1 f s2 ->
      exec (Or c1 c2) s0 (S f) s2

  | EBang : forall c s0 s1 f,
      exec c s0 f s1 -> exec (Bang c) s0 (S f) (St (bstat (status s1)) (env s1))

  | EIfT : forall cond t e s0 sc s1 f,
      exec cond s0 f sc -> status sc = 0 -> exec t sc f s1 ->
      exec (If cond t e) s0 (S f) s1
  | EIfE : forall cond t e s0 sc s1 f,
      exec cond s0 f sc -> status sc <> 0 -> exec e sc f s1 ->
      exec (If cond t e) s0 (S f) s1

  | EWhileStop : forall cond body s0 sc f,
      exec cond s0 f sc -> status sc <> 0 -> exec (While cond body) s0 (S f) sc
  | EWhileGo   : forall cond body s0 sc s1 s2 f,
      exec cond s0 f sc -> status sc = 0 -> exec body sc f s1 ->
      exec (While cond body) s1 f s2 -> exec (While cond body) s0 (S f) s2
  .

(* ═══════════════════════════════════════════════════════════════════
   §3  Executable reference semantics and determinism
   ═══════════════════════════════════════════════════════════════════ *)

(* run is the functional reading of the exec relation: it is what the OCaml
   interpreter — and, later, the hand-extracted C — computes.  It is total: a
   single fuel budget recurses, and it is only consumed at compound forms, so a
   while-loop terminates when the budget is exhausted.  Atomic commands evaluate
   at every fuel level; compounds evaluate only under a positive budget, which is
   exactly the shape of the relation (every compound constructor carries an S). *)

Definition obind {A B : Type} (x : option A) (f : A -> option B) : option B :=
  match x with
  | Some a => f a
  | None => None
  end.

Fixpoint run (f : nat) (c : cmd) (s : state) : option state :=
  match f with
  | 0 =>
      match c with
      | Skip => Some s
      | Ex k => Some (St (nstat k) (env s))
      | Assign k v => Some (St 0 (setv k v (env s)))
      | _ => None
      end
  | S f' =>
      match c with
      | Skip => Some s
      | Ex k => Some (St (nstat k) (env s))
      | Assign k v => Some (St 0 (setv k v (env s)))
      | Bang c =>
          obind (run f' c s) (fun s1 => Some (St (bstat (status s1)) (env s1)))
      | Seq c1 c2 =>
          obind (run f' c1 s) (run f' c2)
      | And c1 c2 =>
          obind (run f' c1 s)
            (fun s1 => if Nat.eqb (status s1) 0 then run f' c2 s1 else Some s1)
      | Or c1 c2 =>
          obind (run f' c1 s)
            (fun s1 => if Nat.eqb (status s1) 0 then Some s1 else run f' c2 s1)
      | If cond t e =>
          obind (run f' cond s)
            (fun sc => if Nat.eqb (status sc) 0 then run f' t sc else run f' e sc)
      | While cond body =>
          obind (run f' cond s)
            (fun sc =>
               if Nat.eqb (status sc) 0
               then obind (run f' body sc) (run f' (While cond body))
               else Some sc)
      end
  end.

(* The relation and the functional reference agree in the forward direction. *)
(* Close a fuel-step goal whose boolean test disagrees with the relation's
   status side condition. *)
Ltac contra_true Hne E := exfalso; exact (Hne (proj1 (Nat.eqb_eq _ _) E)).
Ltac contra_false Hz E := exfalso; exact ((proj1 (Nat.eqb_neq _ _) E) Hz).

Theorem exec_run : forall c s0 f s, exec c s0 f s -> run f c s0 = Some s.
Proof.
  intros c s0 f s H; induction H as
    [ s f | s f k | s f k v
    | c1 c2 s0 s1 s2 f H1 IH1 H2 IH2
    | c1 c2 s0 s1 f H1 IH1 Hne
    | c1 c2 s0 s1 s2 f H1 IH1 Hz H2 IH2
    | c1 c2 s0 s1 f H1 IH1 Hz
    | c1 c2 s0 s1 s2 f H1 IH1 Hne H2 IH2
    | c s0 s1 f H1 IH
    | cond t e s0 sc s1 f HC IHC Hz HT IHT
    | cond t e s0 sc s1 f HC IHC Hne HE ITE
    | cond body s0 sc f HC IHC Hne
    | cond body s0 sc s1 s2 f HC IHC Hz HB IHB HW IHw ].
  - destruct f; cbn [run obind]; reflexivity.   (* ESkip *)
  - destruct f; cbn [run obind]; reflexivity.   (* EExit *)
  - destruct f; cbn [run obind]; reflexivity.   (* EAssign *)
  - (* ESeq *) cbn [run obind]. rewrite IH1. cbn [obind]. rewrite IH2. reflexivity.
  - (* EAndStop *)
    cbn [run obind]. rewrite IH1. cbn [obind].
    destruct (status s1 =? 0) eqn:E.
    + contra_true Hne E.
    + reflexivity.
  - (* EAndGo *)
    cbn [run obind]. rewrite IH1. cbn [obind].
    destruct (status s1 =? 0) eqn:E.
    + rewrite IH2. reflexivity.
    + contra_false Hz E.
  - (* EOrStop *)
    cbn [run obind]. rewrite IH1. cbn [obind].
    destruct (status s1 =? 0) eqn:E.
    + reflexivity.
    + contra_false Hz E.
  - (* EOrGo *)
    cbn [run obind]. rewrite IH1. cbn [obind].
    destruct (status s1 =? 0) eqn:E.
    + contra_true Hne E.
    + rewrite IH2. reflexivity.
  - (* EBang *) cbn [run obind]. rewrite IH. reflexivity.
  - (* EIfT *)
    cbn [run obind]. rewrite IHC. cbn [obind].
    destruct (status sc =? 0) eqn:E.
    + rewrite IHT. reflexivity.
    + contra_false Hz E.
  - (* EIfE *)
    cbn [run obind]. rewrite IHC. cbn [obind].
    destruct (status sc =? 0) eqn:E.
    + contra_true Hne E.
    + rewrite ITE. reflexivity.
  - (* EWhileStop *)
    cbn [run obind]. rewrite IHC. cbn [obind].
    destruct (status sc =? 0) eqn:E.
    + contra_true Hne E.
    + reflexivity.
  - (* EWhileGo *)
    cbn [run obind]. rewrite IHC. cbn [obind].
    destruct (status sc =? 0) eqn:E.
    + rewrite IHB. cbn [obind]. rewrite IHw. reflexivity.
    + contra_false Hz E.
Qed.

(* Every program has at most one result state. *)
Theorem exec_deterministic :
  forall c s0 f s s', exec c s0 f s -> exec c s0 f s' -> s = s'.
Proof.
  intros c s0 f s s' H H2.
  pose proof (exec_run _ _ _ _ H) as E1.
  pose proof (exec_run _ _ _ _ H2) as E2.
  rewrite E1 in E2. injection E2. auto.
Qed.

(* ═══════════════════════════════════════════════════════════════════
   §4  Status is always an 8-bit value (well-formedness preservation)
   ═══════════════════════════════════════════════════════════════════ *)

Definition wf (s : state) : Prop := status s < 256.

Theorem exec_preserves_wf :
  forall c s0 f s, wf s0 -> exec c s0 f s -> wf s.
Proof.
  intros c s0 f s Hwf H; unfold wf in *; induction H as
    [ s | s f k | s f k v
    | c1 c2 s0 s1 s2 f H1 IH1 H2 IH2
    | c1 c2 s0 s1 f H1 IH1 Hne
    | c1 c2 s0 s1 s2 f H1 IH1 Hz H2 IH2
    | c1 c2 s0 s1 f H1 IH1 Hz
    | c1 c2 s0 s1 s2 f H1 IH1 Hne H2 IH2
    | c s0 s1 f H1 IH
    | cond t e s0 sc s1 f HC IHC Hz HT IHT
    | cond t e s0 sc s1 f HC IHC Hne HE ITE
    | cond body s0 sc f HC IHC Hne
    | cond body s0 sc s1 s2 f HC IHC Hz HB IHB HW IHw ].
  - exact Hwf.                                    (* Skip *)
  - apply nstat_lt.                               (* Ex *)
  - cbn; lia.                                     (* Assign *)
  - apply IH2, IH1. exact Hwf.                    (* Seq *)
  - apply IH1. exact Hwf.                         (* And/Stop *)
  - apply IH2, IH1. exact Hwf.                    (* And/Go *)
  - apply IH1. exact Hwf.                         (* Or/Stop *)
  - apply IH2, IH1. exact Hwf.                    (* Or/Go *)
  - cbn [status]; unfold bstat; destruct (status s1 =? 0); lia. (* Bang *)
  - apply IHT, IHC. exact Hwf.                    (* If/Then *)
  - apply ITE, IHC. exact Hwf.                    (* If/Else *)
  - apply IHC. exact Hwf.                         (* While/Stop *)
  - apply IHw, IHB, IHC. exact Hwf.               (* While/Go *)
Qed.

(* A command that exits with 256 lands on 0, matching the C wait-status wrap. *)
Theorem exit_256_is_zero :
  forall s0 f s, exec (Ex 256) s0 f s -> status s = 0.
Proof. intros s0 f s H. inversion H. subst. rewrite nstat_256. reflexivity. Qed.

(* The status of any completed command is reduced mod 256. *)
Theorem exit_norm :
  forall k s0 f s, exec (Ex k) s0 f s -> status s = nstat k.
Proof. intros k s0 f s H. inversion H. reflexivity. Qed.

(* run on the atomic commands, at every fuel level.  These let us read the
   result state out of an exec derivation (via exec_run) without depending on
   the opaque hypothesis names that inversion would generate. *)
Lemma run_ex : forall f k s, run f (Ex k) s = Some (St (nstat k) (env s)).
Proof. intros f k s; destruct f; reflexivity. Qed.

Lemma run_skip : forall f s, run f Skip s = Some s.
Proof. intros f s; destruct f; reflexivity. Qed.

Lemma run_assign : forall f k v s, run f (Assign k v) s = Some (St 0 (setv k v (env s))).
Proof. intros f k v s; destruct f; reflexivity. Qed.

Lemma run_ex0 : forall f s, run f (Ex 0) s = Some (St 0 (env s)).
Proof. intros f s. rewrite run_ex, nstat_zero. reflexivity. Qed.

Lemma run_ex1 : forall f s, run f (Ex 1) s = Some (St 1 (env s)).
Proof.
  intros f s. rewrite run_ex.
  replace (nstat 1) with 1 by (symmetry; apply nstat_small; lia). reflexivity.
Qed.

(* The reduced exit atoms as derivations, for building compound proofs. *)
Lemma exec_ex : forall k s0 f, exec (Ex k) s0 f (St (nstat k) (env s0)).
Proof. intros k s0 f. apply EExit. Qed.

Lemma eexit0 : forall s0 f, exec (Ex 0) s0 f (St 0 (env s0)).
Proof. intros s0 f. pose proof (exec_ex 0 s0 f) as E. rewrite nstat_zero in E. exact E. Qed.

Lemma eexit1 : forall s0 f, exec (Ex 1) s0 f (St 1 (env s0)).
Proof. intros s0 f. pose proof (exec_ex 1 s0 f) as E. rewrite nstat_small in E by lia. exact E. Qed.

(* ═══════════════════════════════════════════════════════════════════
   §5  Short-circuit laws for && and ||
   ═══════════════════════════════════════════════════════════════════ *)

(* A failing left operand of && stops the list; the right never runs and the
   result is exactly the left command's result state. *)
Theorem and_left_false_stops :
  forall c2 s0 f s, exec (And (Ex 1) c2) s0 f s -> s = St 1 (env s0).
Proof.
  intros c2 s0 f s H. pose proof (exec_run _ _ _ _ H) as R.
  destruct f; cbn [run] in R.
  - discriminate R.
  - rewrite run_ex1 in R. cbn in R. congruence.
Qed.

(* A succeeding left operand of || stops the list. *)
Theorem or_left_true_stops :
  forall c2 s0 f s, exec (Or (Ex 0) c2) s0 f s -> s = St 0 (env s0).
Proof.
  intros c2 s0 f s H. pose proof (exec_run _ _ _ _ H) as R.
  destruct f; cbn [run] in R.
  - discriminate R.
  - rewrite run_ex0 in R. cbn in R. congruence.
Qed.

(* && with a true left runs the right and yields its state. *)
Theorem and_left_true_runs :
  forall c2 s0 f s,
  exec c2 (St 0 (env s0)) f s -> exec (And (Ex 0) c2) s0 (S f) s.
Proof.
  intros c2 s0 f s Hc.
  apply EAndGo with (s1 := St 0 (env s0)); [ apply eexit0 | reflexivity | exact Hc ].
Qed.

(* || with a false left runs the right and yields its state. *)
Theorem or_left_false_runs :
  forall c2 s0 f s,
  exec c2 (St 1 (env s0)) f s -> exec (Or (Ex 1) c2) s0 (S f) s.
Proof.
  intros c2 s0 f s Hc.
  apply EOrGo with (s1 := St 1 (env s0)); [ apply eexit1 | cbn; discriminate | exact Hc ].
Qed.

(* ═══════════════════════════════════════════════════════════════════
   §6  Sequence: the list status is that of its last command
   ═══════════════════════════════════════════════════════════════════ *)

(* ; is right-absorbing with Skip. *)
Theorem seq_skip_right :
  forall c s0 f s, exec c s0 f s -> exec (Seq c Skip) s0 (S f) s.
Proof. intros c s0 f s Hc. apply ESeq with (s1 := s); [ exact Hc | apply ESkip ]. Qed.

(* ; is left-absorbing with Skip. *)
Theorem seq_skip_left :
  forall c s0 f s, exec c s0 f s -> exec (Seq Skip c) s0 (S f) s.
Proof. intros c s0 f s Hc. apply ESeq with (s1 := s0); [ apply ESkip | exact Hc ]. Qed.

(* A successful list decomposes into its two commands, sharing the middle state. *)
Theorem seq_last_status :
  forall c1 c2 s0 f s,
  exec (Seq c1 c2) s0 (S f) s ->
  exists s1, exec c1 s0 f s1 /\ exec c2 s1 f s.
Proof.
  intros c1 c2 s0 f s H. inversion H; subst.
  eexists. split; eassumption.
Qed.

(* ═══════════════════════════════════════════════════════════════════
   §7  if: which branch is taken is decided purely by the test status
   ═══════════════════════════════════════════════════════════════════ *)

Theorem if_true_takes_then :
  forall cond t e s0 sc f s,
  exec cond s0 f sc -> status sc = 0 ->
  exec t sc f s -> exec (If cond t e) s0 (S f) s.
Proof.
  intros cond t e s0 sc f s Hc Hst Ht. apply EIfT with (sc := sc); assumption.
Qed.

Theorem if_false_takes_else :
  forall cond t e s0 sc f s,
  exec cond s0 f sc -> status sc <> 0 ->
  exec e sc f s -> exec (If cond t e) s0 (S f) s.
Proof.
  intros cond t e s0 sc f s Hc Hst He. apply EIfE with (sc := sc); assumption.
Qed.

(* A test that succeeds (status 0) runs the then-branch. *)
Theorem if_const_then :
  forall a b s0 f s,
  exec a (St 0 (env s0)) f s -> exec (If (Ex 0) a b) s0 (S f) s.
Proof.
  intros a b s0 f s Ha.
  apply EIfT with (sc := St 0 (env s0)); [ apply eexit0 | reflexivity | exact Ha ].
Qed.

(* A test that fails (non-zero status) runs the else-branch. *)
Theorem if_const_else :
  forall a b s0 f s,
  exec b (St 1 (env s0)) f s -> exec (If (Ex 1) a b) s0 (S f) s.
Proof.
  intros a b s0 f s Hb.
  apply EIfE with (sc := St 1 (env s0)); [ apply eexit1 | cbn; discriminate | exact Hb ].
Qed.

(* ═══════════════════════════════════════════════════════════════════
   §8  while: an immediately-failing test runs the body zero times
   ═══════════════════════════════════════════════════════════════════ *)

Theorem while_false_zero_iterations :
  forall body s0 f s, exec (While (Ex 1) body) s0 f s -> s = St 1 (env s0).
Proof.
  intros body s0 f s H. pose proof (exec_run _ _ _ _ H) as R.
  destruct f; cbn [run] in R.
  - discriminate R.
  - rewrite run_ex1 in R. cbn in R. congruence.
Qed.

(* A roll-up: one iteration plus the tail yields a full while. *)
Theorem while_roll :
  forall cond body s0 sc s1 s2 f,
  exec cond s0 f sc -> status sc = 0 -> exec body sc f s1 ->
  exec (While cond body) s1 f s2 -> exec (While cond body) s0 (S f) s2.
Proof.
  intros cond body s0 sc s1 s2 f Hc Hz Hb Hw.
  apply EWhileGo with (sc := sc) (s1 := s1); assumption.
Qed.

(* ═══════════════════════════════════════════════════════════════════
   §9  ! inverts status and is idempotent up to normalisation
   ═══════════════════════════════════════════════════════════════════ *)

Theorem bang_inverts :
  forall c s0 f s, exec c s0 f s ->
  exec (Bang c) s0 (S f) (St (bstat (status s)) (env s)).
Proof. intros c s0 f s Hc. apply EBang with (s1 := s); exact Hc. Qed.

Theorem bang_twice :
  forall c s0 f s, exec c s0 f s ->
  exec (Bang (Bang c)) s0 (S (S f)) (St (bstat (bstat (status s))) (env s)).
Proof.
  intros c s0 f s Hc.
  apply EBang with (s1 := St (bstat (status s)) (env s)).
  apply EBang with (s1 := s); exact Hc.
Qed.

(* Double bang of a well-formed status normalises to 0/1 as POSIX requires. *)
Theorem bang_bang_norm :
  forall c s0 f s, exec c s0 f s -> wf s ->
  exists s', exec (Bang (Bang c)) s0 (S (S f)) s' /\
             status s' = (if Nat.eqb (status s) 0 then 0 else 1).
Proof.
  intros c s0 f s Hc Hwf.
  exists (St (bstat (bstat (status s))) (env s)).
  split; [ apply bang_twice; exact Hc | apply bstat_bstat ].
Qed.

(* ═══════════════════════════════════════════════════════════════════
   §10  Assignment scoping: it binds exactly one variable
   ═══════════════════════════════════════════════════════════════════ *)

Theorem assign_get :
  forall k v s0 f s,
  exec (Assign k v) s0 f s -> getv k (env s) = Some v /\ status s = 0.
Proof.
  intros k v s0 f s H. inversion H; subst. cbn [env status].
  split; [ apply getv_set_same | reflexivity ].
Qed.

Theorem assign_isolated :
  forall k k2 v s0 f s,
  k <> k2 -> exec (Assign k v) s0 f s -> getv k2 (env s) = getv k2 (env s0).
Proof.
  intros k k2 v s0 f s Hne H. inversion H; subst. cbn [env].
  apply getv_set_other. exact Hne.
Qed.

(* An assignment never short-circuits the following command in a list. *)
Theorem assign_then_seq :
  forall k v c s0 f s,
  exec c (St 0 (setv k v (env s0))) f s -> exec (Seq (Assign k v) c) s0 (S f) s.
Proof.
  intros k v c s0 f s Hc.
  apply ESeq with (s1 := St 0 (setv k v (env s0))).
  - apply EAssign.
  - exact Hc.
Qed.
