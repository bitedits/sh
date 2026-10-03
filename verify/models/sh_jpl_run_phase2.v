(* sh_jpl_run_phase2.v

 * JPL.3b — the liveness half of the machine equivalence (Phase 3d-C / JPL.3b).

 * sh_jpl_run.v delivers SOUNDNESS: `mrun_sound` proves that whenever the fuel
 * driver `mloop` answers BOk st, that st is exactly what the single source of
 * truth `run` computes (and `run_none_mloop_limit` its contrapositive).  What it
 * does NOT yet give is the converse — that every input `run` accepts is answered
 * by `mloop` under SOME step budget.  Without that half, `mloop`'s saturation
 * answer BLimit is only "not-yet-proven-safe", not "genuinely-out-of-budget",
 * so the extraction of the machine (JPL.4) would carry an unverified gap.

 * This file closes that gap.  It does not re-define or edit `run`, `step`,
 * `mloop`, or any of the soundness machinery — it imports them from
 * sh_jpl_run.v and adds ONLY a termination argument plus the completeness
 * theorems that follow from it.

 * Correctness contract (this file):
 *   - A well-founded step order on machine configurations.  `next g g'` says
 *     "g' is the config mloop continues from after one driver iteration started
 *     at g" — for an Onext step it is the successor, for an Oeffect step it is
 *     the phi-served re-entry `CFG 0 None k s'` that mloop builds after the
 *     seam.  `next_decrease` proves a single natural-number ranking
 *     (`cfg_budget g' < cfg_budget g`) on it, so its converse `prec g' g :=
 *     next g g'` is well-founded (`prec_wf`, via Wf_nat).  Because the order is
 *     well-founded, no phi-driven path can step forever under a succeeding run.
 *   - mrun_live : the LIVENESS half.  cfg_run phi g = Some st -> exists B,
 *     mloop phi B g = BOk st, by well-founded induction on prec.  Together with
 *     mrun_sound this is the two-sided agreement between the machine and run.
 *   - mloop_iff : the saturated two-sided statement for the initial config —
 *     past an existence witness budget, mloop equals b_of run exactly for EVERY
 *     larger budget (BOk when run succeeds, BLimit when it saturates).  This
 *     leans on mloop_ok_monotone (a reached BOk answer is stable under extra
 *     budget, since the driver is deterministic).
 *   - mrun_complete / mloop_sound_complete : the completeness direction and the
 *     iff phrased as two named directions, so the JPL.4 extraction gate has a
 *     single named lemma to consume.

 * Budget measure (used only to PROVE the order is well-founded — no closed-form
 * step budget is claimed):
 *     cfg_budget (CFG f co k s) = btask f (pending co) + bstack k
 * where btask mirrors run/step one dispatch per fuel decrement and bstack sums
 * bframe over the continuation stack.  A driver iteration either
 *   (a) decomposes the pending command, spending one dispatch charge and handing
 *       the child the predecessor fuel f' (mirroring run's fuel threading) while
 *       pushing only predecessor-fuel frames, or
 *   (b) pops the top frame via step_ret, consuming its bframe charge, or
 *   (c) reaches an atomic Ext leaf: its Oeffect seam is served by mloop into the
 *       re-entry CFG 0 None k s', which clears only the pending slot (constant
 *       budget), leaving the stack — and hence the ranking — strictly smaller.
 * In every case cfg_budget drops by at least one, which is what next_decrease
 * shows by `lia` over the born-canonical btask/bframe/bstack atoms.  The order
 * is the preimage of `<` on nat under cfg_budget, so it is well-founded — no
 * ad-hoc accessibility argument or lexicographic product is needed.

 * Build (Rocq >= 9.0):
 *   coqc sh_jpl_run_phase2.v
 *   coqchk -o -silent sh_jpl_run_phase2   # must report Axioms: <none>
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import Wf_nat.
Import ListNotations.

Require Import sh_concrete.
Require Import sh_jpl.
Require Import sh_jpl_run.   (* the machine + soundness; this file extends it *)

Set Warnings "-register-all".

(* ═══════════════════════════════════════════════════════════════════
   §1  A fuel-indexed step budget

   `btask f t` upper-bounds the number of driver iterations (`mloop` steps) the
   machine spends to finish the pending task `t` at fuel `f`, assuming the run
   succeeds.  It mirrors `run`/`step` line for line: every concrete helper
   (`run`, `run_seq`, `run_for`, `run_case`) and every `enter_*` in the machine
   descends the fuel by exactly one per recursion (one per command node, per
   loop iteration, per list element, per branch test), so fuel is the single
   well-founded measure and `btask` is an ordinary `Fixpoint` on it — and hence
   reduces by `cbn`/`simpl`, which is what the decrease proof in §3 leans on.

   `cfg_budget g = btask (pending) + sum of bframe over the stack` is then shown
   to STRICTLY DECREASE on every driver iteration (§3).  Since it lands in the
   well-founded naturals, the iteration relation is well-founded and the machine
   cannot step forever on any input `run` accepts — that is the liveness half.

   The construction is deliberately generous (it sums across both branches of
   If/And/Or/While).  We never claim a tight bound; a leading `+1` per dispatch
   is all that the decrease argument needs.

   `bframe` costs each frame at the fuel it stores; a frame is created by a
   parent command run at that fuel, and the machine pops it exactly as the
   budget account expects (the `1 +`/`2 +` dispatch charges line up one-for-one
   with `step_ret`).
   ═══════════════════════════════════════════════════════════════════ *)

(* The four pending shapes the machine can carry, without the fuel (which is the
   Fixpoint measure).  TCmd/TSeq/TCase/TFor correspond to run/run_seq/run_case/
   run_for respectively. *)
Inductive task : Type :=
  | TCmd  : cmd -> task
  | TSeq  : list cmd -> task
  | TCase : list (list text * list cmd) -> task
  | TFor  : list text -> list cmd -> task.

Fixpoint btask (f : nat) (t : task) : nat :=
  match f with
  | 0 =>
      match t with
      | TCmd c =>
          match c with
          | Skip => 1
          | Ext _ _ => 2
          | Assign _ _ => 2
          | _ => 1                   (* compound saturates in one Olimit step *)
          end
      | TSeq _ => 1
      | TCase _ => 1
      | TFor _ _ => 1
      end
  | S g =>
      match t with
      | TCmd c =>
          match c with
          | Skip => 1
          | Ext _ _ => 2
          | Assign _ _ => 2
          | Bang c0 => 2 + btask g (TCmd c0)
          | Seq c1 c2 => 2 + btask g (TCmd c1) + btask g (TCmd c2)
          | And c1 c2 => 2 + btask g (TCmd c1) + btask g (TCmd c2)
          | Or c1 c2 => 2 + btask g (TCmd c1) + btask g (TCmd c2)
          | If i t0 e => 2 + btask g (TCmd i) + btask g (TCmd t0) + btask g (TCmd e)
          | While i b => 3 + btask g (TCmd i) + btask g (TCmd b) + btask g (TCmd (While i b))
          | For _ ws body => 1 + btask g (TFor ws body)
          | Case _ brs => 1 + btask g (TCase brs)
          end
      | TSeq [] => 1
      | TSeq (c :: r) => 1 + btask g (TCmd c) + btask g (TSeq r)
      | TCase [] => 1
      | TCase (pb :: r) => 1 + btask g (TSeq (snd pb)) + btask g (TCase r)
      | TFor [] _ => 1
      | TFor (_ :: r) body => 1 + btask g (TSeq body) + btask g (TFor r body)
      end
  end.

(* Work owed by a continuation frame once its child has finished.  The constant
   charges are the `step_ret` dispatches that consume them.  NOTE: each arm is
   written in the canonical `btask f (T... )` form (no `btask f (TCmd c)`
   abbreviations), so that after `cbn` a frame's cost reduces to the EXACT same
   atom that `btask`'s own recursive arms produce (they too spell
   `btask g (TCmd c)` etc.).  Keeping both sides syntactically identical is what
   lets the ranking obligations below discharge by `lia` — otherwise one side
   would reduce to a wrapper like `bseq g l` and the other to `btask g (TSeq l)`,
   and `lia` would see two unrelated atoms. *)
Definition bframe (fr : frame) : nat :=
  match fr with
  | FSeq f c2 => 1 + btask f (TCmd c2)
  | FAnd f c2 => 1 + btask f (TCmd c2)
  | FOr f c2 => 1 + btask f (TCmd c2)
  | FBang => 1
  | FIf f t e => 1 + btask f (TCmd t) + btask f (TCmd e)
  | FWhile f c b => 2 + btask f (TCmd b) + btask f (TCmd (While c b))
  | FWhileBody f c b => 1 + btask f (TCmd (While c b))
  | FSeqList f l => btask f (TSeq l)
  | FForRest f _ ws body => btask f (TFor ws body)
  end.

Fixpoint bstack (k : stack) : nat :=
  match k with
  | [] => 0
  | fr :: r => bframe fr + bstack r
  end.

(* Total budget of a configuration: the pending task (0 when just finished) plus
   the whole stack. *)
Definition cfg_budget (g : cfg) : nat :=
  match cc g with
  | Some c => btask (cf g) (TCmd c) + bstack (ck g)
  | None => bstack (ck g)
  end.

(* Canonicalise budget terms to the single `btask f (T ... )` normal form, then
   discharge by `lia`.  `bframe`/`cfg_budget` are written so their unfolded atoms
   are identical to `btask`'s own recursive arms, and `lia` treats the remaining
   stuck `btask ... : nat` atoms as nonnegative.  Two reductions, keyed by whether
   the successor config is concrete or abstract:
     - `cbc` (concrete child): the successor `cfg_budget g'` is a real `CFG`, so
       unfold it together with the stack, then `lia`.  Used right after `injection`.
     - `cba` (abstract child): the successor came from a nested `enter_*`, so
       `cfg_budget g'` is an opaque atom shared verbatim with the ranking lemma —
       reduce only `btask`/`bstack`/`bframe` everywhere (the `cfg_budget` head is
       deliberately left alone, so the shared atom never splits) and `lia`. *)
Ltac cbc := cbn [cfg_budget cc cf ck btask bstack bframe snd fst]; lia.
Ltac cba := cbn [btask bstack bframe snd fst] in *; lia.


(* ═══════════════════════════════════════════════════════════════════
   §2  The driver-iteration relation and its ranking

   `next g g'` relates a config to the config `mloop` continues from after ONE
   driver iteration started at `g`: an Onext step's successor, or (past an
   Oeffect seam) the phi-served re-entry `CFG 0 None k s'` — the exact state
   mloop builds after servicing the effect.  `cfg_budget` is a strict ranking on
   it, so `next` is well-founded.  The ranking only has to make PROGRESS
   observable (a decreasing nat); it does not have to count real steps.
   ═══════════════════════════════════════════════════════════════════ *)

(* Budget delta for entering a command list (run_seq / a body list).  The
   conclusion is written in the canonical `btask h (TSeq l)` form so callers that
   thread an ABSTRACT successor can match it verbatim without unfolding `A`. *)
Lemma enter_seq_rank : forall h l s k g',
  enter_seq h l s k = Onext g' -> cfg_budget g' < btask h (TSeq l) + bstack k.
Proof.
  intros h l s k g' H. unfold enter_seq in H. destruct h as [|g]; [discriminate|].
  destruct l as [|c l']; cbn [enter_seq] in H.
  - injection H as <-. cbc.
  - destruct l' as [|c2 l'']; cbn [enter_seq] in H.
    + injection H as <-. cbc.
    + injection H as <-. cbc.
Qed.

(* Budget delta for entering a for-loop word list (run_for). *)
Lemma enter_for_rank : forall h var ws body s k g',
  enter_for h var ws body s k = Onext g' -> cfg_budget g' < btask h (TFor ws body) + bstack k.
Proof.
  intros h var ws body s k g' H. unfold enter_for in H. destruct h as [|g]; [discriminate|].
  destruct ws as [|w ws']; cbn [enter_for] in H.
  - (* no words: value produced, only the stack budget remains *)
    injection H as <-. cbc.
  - destruct ws' as [|w2 r]; cbn [enter_for] in H.
    + (* single word: enter_seq over the body, stack unchanged *)
      assert (A : cfg_budget g' < btask g (TSeq body) + bstack k)
        by (exact (enter_seq_rank _ _ _ _ _ H)).
      cba.
    + (* head word + rest: enter_seq over body, FForRest rest frame pushed *)
      assert (A : cfg_budget g' < btask g (TSeq body)
                       + bstack (FForRest g var (w2 :: r) body :: k))
        by (exact (enter_seq_rank _ _ _ _ _ H)).
      cba.
Qed.

(* Budget delta for a case scan.  enter_case is a Fixpoint over the branch list,
   so the ranking is proved by induction on that list. *)
Lemma enter_case_rank : forall brs h scrut s k g',
  enter_case h scrut brs s k = Onext g' -> cfg_budget g' < btask h (TCase brs) + bstack k.
Proof.
  induction brs as [|pb brs IH]; intros h scrut s k g' H.
  - (* brs = []: value produced, stack budget only *)
    destruct h as [|g]; cbn [enter_case] in H; [discriminate|].
    injection H as <-. cbc.
  - (* brs = pb :: brs; destruct the pair FIRST so enter_case can reduce *)
    destruct pb as [pats body].
    destruct h as [|g]; cbn [enter_case] in H; [discriminate|].
    destruct (match_any g pats (expand g (cenv s) (cstatus s) scrut)) eqn:Em.
    + (* branch matched: enter_seq over its body *)
      assert (A : cfg_budget g' < btask g (TSeq body) + bstack k)
        by (exact (enter_seq_rank _ _ _ _ _ H)).
      cba.
    + (* scan the rest: recursive enter_case at fuel g *)
      assert (A : cfg_budget g' < btask g (TCase brs) + bstack k)
        by (exact (IH g scrut s k g' H)).
      cba.
Qed.

(* One pending-command dispatch drops the ranking by at least one.  The two
   commands that hand off to enter_for/enter_case are recognised from the shape
   of the reduced step equation (abstract successor -> `cba`); every other
   successor is a plain CFG produced by step_cmd (concrete -> `cbc` after injection). *)
Lemma step_cmd_onext_rank : forall f c k s f2 c2 k2 s2,
  step_cmd f c k s = Onext (CFG f2 c2 k2 s2) ->
  cfg_budget (CFG f2 c2 k2 s2) < btask f (TCmd c) + bstack k.
Proof.
  intros f c k s f2 c2 k2 s2 H. unfold step_cmd in H.
  destruct f as [|f'];
  destruct c as [ |idx argv | nm v | bc | cA cB | cA cB | cA cB | ci ct ce | wi wb | var ws body | sc brs ];
  cbn [step_cmd] in H; try discriminate;
    match goal with
      | H0 : enter_for _ _ _ _ _ _ = Onext _ |- _ =>
          pose proof (enter_for_rank _ _ _ _ _ _ (CFG f2 c2 k2 s2) H0) as A; cba
      | H0 : enter_case _ _ _ _ _ = Onext _ |- _ =>
          pose proof (enter_case_rank _ _ _ _ _ (CFG f2 c2 k2 s2) H0) as A; cba
      | _ => inversion H; subst; cbc
    end.
Qed.

(* One stack-pop dispatch drops the ranking by at least one.  The frames whose
   successor depends on the status test are resolved by destructing `isz s`; the
   list/for frames hand off to enter_seq/enter_for (abstract -> `cba`). *)
Lemma step_ret_onext_rank : forall k s f2 c2 k2 s2,
  step_ret k s = Onext (CFG f2 c2 k2 s2) ->
  cfg_budget (CFG f2 c2 k2 s2) < bstack k.
Proof.
  intros k s f2 c2 k2 s2 H.
  destruct k as [|fr r]; cbn [step_ret] in H; [discriminate|].
  destruct fr as [ f1a c1a | f1b c1b | f1c c1c |  | f2a t2a e2a | f3a w3a b3a | f4a w4a b4a | f5a l5a | f6a v6a ws6a bd6a ];
  cbn [step_ret] in H;
  match goal with
    | H0 : enter_seq _ _ _ _ = Onext _ |- _ =>
        pose proof (enter_seq_rank _ _ _ _ (CFG f2 c2 k2 s2) H0) as A; cba
    | H0 : enter_for _ _ _ _ _ _ = Onext _ |- _ =>
        pose proof (enter_for_rank _ _ _ _ _ _ (CFG f2 c2 k2 s2) H0) as A; cba
    | _ => destruct (isz s); try discriminate; inversion H; subst; cbc
  end.
Qed.

Definition next (g g' : cfg) : Prop :=
  (step g = Onext g') \/
  (exists idx argv k s s', step g = Oeffect idx argv k s /\ g' = CFG 0 None k s').

(* A stack-pop (or the list/for entries it dispatches to) only ever yields
   Onext/Odone/Olimit, never the phi seam Oeffect. *)
Lemma enter_seq_ne_Oeffect : forall h l s k idx argv k' s',
  enter_seq h l s k <> Oeffect idx argv k' s'.
Proof.
  unfold enter_seq; intros h l s k idx argv k' s' H.
  destruct h as [|g]; [discriminate|].
  destruct l as [ | c l' ]; [ discriminate | ].
  destruct l' as [ | c2 l2 ]; cbn in H; discriminate.
Qed.

Lemma enter_for_ne_Oeffect : forall h var ws body s k idx argv k' s',
  enter_for h var ws body s k <> Oeffect idx argv k' s'.
Proof.
  unfold enter_for; intros h var ws body s k idx argv k' s' H.
  destruct h as [|g]; [discriminate|].
  destruct ws as [|w ws']; [discriminate|].
  destruct ws' as [ | w2 r ];
    [ apply (enter_seq_ne_Oeffect g body (bind_word g var w s) k idx argv k' s'); exact H
    | apply (enter_seq_ne_Oeffect g body (bind_word g var w s)
              (FForRest g var (w2 :: r) body :: k) idx argv k' s'); exact H ].
Qed.

Lemma enter_case_ne_Oeffect : forall brs h scrut s k idx argv k' s',
  enter_case h scrut brs s k <> Oeffect idx argv k' s'.
Proof.
  induction brs as [|pb brs IH]; intros h scrut s k idx argv k' s' H.
  unfold enter_case in H.
  - destruct h as [|g]; cbn [enter_case] in H; discriminate.
  - destruct h as [|g]; try (cbn [enter_case] in H; discriminate).
    destruct pb as [pats body]; cbn [enter_case] in H;
    destruct (match_any g pats (expand g (cenv s) (cstatus s) scrut));
    [ apply (enter_seq_ne_Oeffect g body s k idx argv k' s'); exact H
    | apply (IH g scrut s k idx argv k' s'); exact H ].
Qed.

Lemma step_ret_ne_Oeffect : forall k s idx argv k' s',
  step_ret k s <> Oeffect idx argv k' s'.
Proof.
  unfold step_ret; intros k s idx argv k' s' H.
  destruct k as [|fr r]; cbn in H; [discriminate|].
  destruct fr as [f1 c1|f2 c2|f3 c3| |f5 t5 e5|f6 c6 b6|f7 c7 b7|f8 l8|f9 v9 ws9 bd9];
  cbn in H;
  try (apply (enter_seq_ne_Oeffect f8 l8 s r idx argv k' s'); exact H);
  try (apply (enter_for_ne_Oeffect f9 v9 ws9 bd9 s r idx argv k' s'); exact H);
  try discriminate;
  destruct (isz s); discriminate.
Qed.

Lemma next_decrease : forall g g', next g g' -> cfg_budget g' < cfg_budget g.
Proof.
  intros g g' H. unfold next in H.
  destruct H as [H|[idx [argv [k [s [s' [He Hg']]]]]]].
  - (* Onext: the ranking lemmas give the drop; the parent config unfolds to the
       same `btask f (TCmd c) + bstack k` shape they conclude, so `exact` matches
       by conversion without touching the abstract LHS. *)
    destruct g as [f co k0 s0]; destruct g' as [f2 c2 k2 s2];
    destruct co as [|c]; cbn [step cc cf ck cs] in H.
    + exact (step_cmd_onext_rank f c k0 s0 f2 c2 k2 s2 H).
    + exact (step_ret_onext_rank k0 s0 f2 c2 k2 s2 H).
  - (* an Oeffect seam: only an Ext leaf reaches it, its budget is a constant 2,
       and the served re-entry clears the pending slot, so the stack is untouched. *)
    subst g'. destruct g as [f co k0 s0]. unfold step in He.
    destruct co as [|c]; cbn [cc cf ck cs] in He;
    [ (* Some c: unfold step_cmd, the only seam source is the Ext leaf *)
      destruct f; cbn [step_cmd] in He;
      destruct c as [|idx' argv'|nm v|bc|ca cb|ca cb|ca cb|ci ct ce|wi wb|var ws body|sc brs];
      cbn [step_cmd] in He; try discriminate;
      try (apply enter_for_ne_Oeffect in He; contradiction);
      try (apply enter_case_ne_Oeffect in He; contradiction);
      inversion He; subst; cbc
    | (* None: step_ret can never produce the seam *)
      apply (step_ret_ne_Oeffect _ _ _ _ _ _) in He; contradiction ].
Qed.

(* `prec g' g` holds when g' is the ONE-step successor of g, i.e. next g g'.
   Well-founded induction on `prec` therefore lets a property of g be derived
   from properties of its successors (each of which has a strictly smaller
   `cfg_budget`), which is exactly the recursion shape of the driver. *)
Definition prec (g' g : cfg) : Prop := next g g'.

Lemma prec_wf : well_founded prec.
Proof.
  apply (well_founded_lt_compat _ cfg_budget).
  intros x y H. (* H : prec x y = next y x *)
  exact (next_decrease y x H).
Qed.

(* ═══════════════════════════════════════════════════════════════════
   §3  Liveness (completeness): every input `run` accepts is answered

   mrun_live is the converse of mrun_sound.  A configuration whose meaning
   cfg_run phi g is Some st is answered BOk st by mloop under SOME step budget,
   so the driver never misses an input the reference run accepts.

   Proof shape (well-founded induction on `prec`, i.e. on the reverse of `next`):
     - destruct step g into its four outputs;
     - Onext g': next g g' gives prec g' g, so acc gives accessibility of g' and
       the induction hypothesis yields a budget B' for g'; return S B' and close
       the one driver step by computation (the case is only reachable while
       cfg_run phi g' = Some st, which step_preserves transfers from the parent).
     - Oeffect: fold phi's result into the re-entry CFG 0 None k s' (next-related
       to g), use the IH to get B', return S (S B') so the seam service plus one
       driver step both fit.  A seam phi rejects (phi .. = None) is impossible
       under cfg_run = Some st, since out_run then reduces to cont_run _ _ None,
       which cont_run_none collapses to None — contradiction.
     - Odone: return budget 1.
     - Olimit: contradicts cfg_run = Some st via step_preserves.
   No axiom, no Admitted: the well-founded principle is prec_wf, proved from
   next_decrease over the nat measure cfg_budget.
   ═══════════════════════════════════════════════════════════════════ *)

Theorem mrun_live : forall phi g st,
  cfg_run phi g = Some st -> exists B, mloop phi B g = BOk st.
Proof.
  intros phi g.
  induction (prec_wf g) as [g Hacc IH].
  intros st Hr.
  destruct (step g) as [g' | idx argv k s | sd | ] eqn:Es.
  - (* Onext g': next g g', so g' is a smaller successor and the IH applies.
       step_preserves transfers the parent's meaning to g'. *)
    assert (Aord : prec g' g) by (unfold prec, next; left; exact Es).
    assert (E : cfg_run phi g' = Some st).
    { assert (H : out_run phi (Onext g') = Some st)
        by (rewrite <- Es, step_preserves; exact Hr).
      cbn [out_run] in H. exact H. }
    destruct (IH g' Aord st E) as [B' Heq].
    exists (S B').
    cbn [mloop]. rewrite Es. exact Heq.
  - (* Oeffect seam *)
    destruct (phi idx argv s) as [s' | ] eqn:Ep; [|].
    + (* fold phi's result into the re-entry, which is next-related to g *)
      assert (Aord : prec (CFG 0 None k s') g) by
        (unfold prec, next; right; exists idx; exists argv; exists k; exists s; exists s';
         split; [exact Es | reflexivity]).
      assert (E : cfg_run phi (CFG 0 None k s') = Some st).
      { assert (H : out_run phi (Oeffect idx argv k s) = Some st)
          by (rewrite <- Es, step_preserves; exact Hr).
        cbn [out_run] in H. rewrite Ep in H. exact H. }
      destruct (IH (CFG 0 None k s') Aord st E) as [B' Heq].
      exists (S B').
      cbn [mloop]. rewrite Es, Ep. exact Heq.
    + (* phi rejects — unreachable when cfg_run succeeds *)
      rewrite <- step_preserves, Es in Hr.
      cbn [out_run] in Hr.
      rewrite Ep, cont_run_none in Hr. discriminate.
  - (* Odone sd: Hr pins st = sd, and budget 1 finishes in one step *)
    rewrite <- (step_preserves phi g), Es in Hr.
    cbn [out_run] in Hr.                 (* Hr : Some sd = Some st *)
    injection Hr as Hsd. subst sd.
    exists 1. simpl. rewrite Es. reflexivity.
  - (* Olimit *)
    rewrite <- step_preserves, Es in Hr. discriminate.
Qed.

(* ═══════════════════════════════════════════════════════════════════
   §4  Two-sided agreement between the machine and `run`

   With soundness (mrun_sound / mrun_correct / run_none_mloop_limit, from
   sh_jpl_run.v) and liveness (mrun_live, §3) both in hand, the machine's
   saturated answer IS `run`'s answer, not merely a safe over-approximation of
   it.  These are the named lemmas the JPL.4 extraction gate consumes.

   mloop_ok_monotone is the one extra structural fact: once the driver reaches a
   sound BOk answer at budget B, any larger budget follows the same deterministic
   path and returns the same BOk.  It lets the existential budget of mrun_live be
   upgraded to the "every budget >= the witness" form of mloop_iff.
   ═══════════════════════════════════════════════════════════════════ *)

Lemma mloop_ok_monotone : forall phi B' B g st,
  B <= B' -> mloop phi B g = BOk st -> mloop phi B' g = BOk st.
Proof.
  intros phi B'. induction B' as [| Bm IH]; intros B g st Hle Hm.
  - (* B' = 0 forces B = 0, where mloop is BLimit, never BOk *)
    replace B with 0 in Hm by lia. simpl in Hm. discriminate.
  - destruct B as [| Bp].
    + simpl in Hm. discriminate.
    + assert (Hle' : Bp <= Bm) by lia.
      destruct (step g) as [g2 | idx argv k s | sd | ] eqn:Es.
      * (* Onext: descend one step on both sides, then the IH at tail budgets *)
        cbn [mloop] in Hm; rewrite Es in Hm.
        cbn [mloop]; rewrite Es.
        exact (IH Bp g2 st Hle' Hm).
      * (* Oeffect seam *)
        destruct (phi idx argv s) as [s' | ] eqn:Ep.
        { cbn [mloop] in Hm; rewrite Es, Ep in Hm.
          cbn [mloop]; rewrite Es, Ep.
          exact (IH Bp (CFG 0 None k s') st Hle' Hm). }
        { cbn [mloop] in Hm; rewrite Es, Ep in Hm; discriminate. }
      * (* Odone: both sides compute to the same BOk sd = BOk st *)
        cbn [mloop] in Hm; rewrite Es in Hm.
        cbn [mloop]; rewrite Es.
        exact Hm.
      * (* Olimit: Hm says BLimit = BOk st *)
        cbn [mloop] in Hm; rewrite Es in Hm; discriminate.
Qed.

(* The meaning of the initial configuration is exactly `run`'s answer. *)
Lemma cfg_run_init : forall phi F c s,
  cfg_run phi (CFG F (Some c) [] s) = run phi F c s.
Proof.
  intros phi F c s. reflexivity.
Qed.

(* Completeness at the initial configuration: run accepts -> some budget answers. *)
Theorem mrun_complete : forall phi F c s st,
  run phi F c s = Some st -> exists B, mloop phi B (CFG F (Some c) [] s) = BOk st.
Proof.
  intros phi F c s st Hr.
  apply (mrun_live phi (CFG F (Some c) [] s) st).
  rewrite cfg_run_init. exact Hr.
Qed.

(* The saturated two-sided statement: past the witness budget the machine's
   answer equals b_of run, for EVERY larger budget. *)
Theorem mloop_iff : forall phi F c s,
  exists B0, forall B, B >= B0 ->
    mloop phi B (CFG F (Some c) [] s) = b_of (run phi F c s).
Proof.
  intros phi F c s.
  destruct (run phi F c s) as [st | ] eqn:Hr.
  - (* run succeeds: monotonicity lifts the witness budget to all larger ones *)
    destruct (mrun_complete phi F c s st Hr) as [B0 HB0].
    exists B0. intros B Hge.
    cbn [b_of].
    exact (mloop_ok_monotone phi B B0 (CFG F (Some c) [] s) st Hge HB0).
  - (* run saturates: mloop can never answer BOk, so its only answer is BLimit *)
    exists 0. intros B _.
    cbn [b_of].
    destruct (mloop phi B (CFG F (Some c) [] s)) as [st' | ] eqn:Hm.
    + destruct (run_none_mloop_limit phi B F c s Hr st' Hm).
    + reflexivity.
Qed.

(* The equivalence as two named directions, for the extraction gate. *)
Theorem mloop_sound_complete : forall phi F c s st,
  run phi F c s = Some st <-> exists B, mloop phi B (CFG F (Some c) [] s) = BOk st.
Proof.
  intros phi F c s st. split.
  - intro Hr. exact (mrun_complete phi F c s st Hr).
  - intros [B HB]. exact (mrun_correct phi B F c s st HB).
Qed.
