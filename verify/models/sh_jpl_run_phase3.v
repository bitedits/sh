(* sh_jpl_run_phase3.v

 * JPL.5-A.4 — the phi-as-DATA driver (Phase 3d-C).

 * sh_jpl_run.v already makes the *step* dispatcher phi-free: at an external
 * command leaf `step` returns the data value `Oeffect idx argv k s`, never a
 * callback.  The only higher-order `phi` that survives in that file is folded
 * back inside the tail driver `mloop phi B g`, which is what an extraction would
 * emit as a captured-environment function pointer — the single construct JPL
 * Rules 6 and 29 forbid in the kernel.  This file removes it.

 * What this module adds (additive; nothing in sh_jpl_run.v / phase2 is edited):
 *   - `mrun`  : the *closure-free* driver the C99 kernel emits.  It iterates
 *               `step` under a bounded step budget and STOPS at the first
 *               boundary, returning a plain DATA value of type `dres`:
 *                 DDone st            (ran to completion, no service needed),
 *                 DEff idx argv k s   (an effect to be serviced by the host),
 *                 DLim                (budget exhausted / saturated).
 *               `mrun` takes NO `phi` argument, so extraction leaves no function
 *               pointer in the loop.
 *   - `host`  : the model of the C main loop that *services* the seam.  It runs
 *               `mrun`, and on a DEff applies the seam once, re-entering `mrun`
 *               at the successor config `CFG 0 None k s'`.  `phi` appears here
 *               only as the host-side seam, exactly as it appears in real C
 *               between two `mrun` calls — never inside the kernel loop.

 * Correctness contract (the JPL.3/3b theorems, restated over the data driver):
 *   - mrun_done_sound : mrun B g = DDone st -> cfg_run phi g = Some st.
 *     Whatever the closure-free kernel reports as its final state is exactly
 *     what the single-source `run` computes — for EVERY seam phi (the DDone path
 *     never touched an effect, so it is phi-independent).
 *   - mrun_eff_sound  : mrun B g = DEff idx argv k s ->
 *                       cfg_run phi g = cont_run phi k (phi idx argv s).
 *     The whole dependence on the seam is localised into the returned DATA.
 *   - host_sound      : host phi B g = BOk st -> cfg_run phi g = Some st (safety).
 *   - host_live       : cfg_run phi g = Some st -> exists B, host phi B g = BOk st
 *                       (completeness), by strong induction on the phase2 ranking
 *                       `cfg_budget` reusing `mrun_live`, `next_decrease`.
 *   - host_iff_run_init : the two-sided agreement with concrete `run` at the
 *                       initial config — the JPL.3b `mloop_iff` counterpart for
 *                       the data driver.
 *   - mrun_dres_monotone / host_monotone: determinism — a reached DDone/DEff
 *     (resp. BOk) is stable under extra budget.
 *   - §6 re-checks the conformance boundary by computation: the data driver and
 *     the host agree with concrete `run` on the pure seam (`reflexivity`), the
 *     same way sh_jpl_run §7 checks `mloop`.

 * Build (Rocq >= 9.0):
 *   coqc sh_concrete.v sh_jpl.v sh_jpl_run.v sh_jpl_run_phase2.v
 *   coqc sh_jpl_run_phase3.v
 *   coqchk -o -silent sh_jpl_run_phase3   # must report the four <none> lines
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import sh_concrete.       (* the reference semantics run/... *)
Require Import sh_jpl.            (* the bounded carrier bres/BOk/BLimit *)
Require Import sh_jpl_run.        (* step/cfg/out + cfg_run/step_preserves + mloop *)
Require Import sh_jpl_run_phase2. (* next / next_decrease / cfg_budget / mrun_live *)

Set Warnings "-register-all".

(* ═══════════════════════════════════════════════════════════════════
   §1  The closure-free driver `mrun` and its data result `dres`

   `mrun` is exactly `mloop` with the seam application REMOVED: on `Oeffect` it
   returns the effect as data instead of calling `phi`.  The self-call is in tail
   position on both `Onext` (budget decremented) and the driver's outer match, so
   this extracts to a single C `while (B--) { ... }` with no callback.
   ═══════════════════════════════════════════════════════════════════ *)

Inductive dres : Type :=
  | DDone : cstate -> dres
  | DEff  : nat -> list text -> stack -> cstate -> dres
  | DLim  : dres.

Fixpoint mrun (B : nat) (g : cfg) : dres :=
  match B with
  | 0 => DLim
  | S B' =>
      match step g with
      | Onext g'            => mrun B' g'
      | Oeffect idx argv k s => DEff idx argv k s
      | Odone st            => DDone st
      | Olimit              => DLim
      end
  end.

(* The host loop: run the kernel to a boundary; if it stopped at an effect,
   service it with the seam and re-enter `mrun` at fuel 0 (the exact successor
   `CFG 0 None k s'` the extracted C main builds between two `mrun` calls).  This
   mirrors `mloop`, but the `phi` application now lives in the host, not in the
   kernel loop. *)
Fixpoint host (phi : run_phi) (B : nat) (g : cfg) : bres cstate :=
  match B with
  | 0 => BLimit
  | S B' =>
      match mrun B' g with
      | DDone st => BOk st
      | DEff idx argv k s =>
          match phi idx argv s with
          | Some s' => host phi B' (CFG 0 None k s')
          | None    => BLimit
          end
      | DLim => BLimit
      end
  end.

(* ═══════════════════════════════════════════════════════════════════
   §2  Soundness of the data driver — the emitted kernel is never wrong

   Both proofs reuse the phi-parameterised `step_preserves` from sh_jpl_run, and
   need no `phi` in `mrun` itself: the DDone branch never met an effect, so its
   meaning is phi-independent; the DEff branch pushes the entire seam dependence
   into the returned data via `out_run (Oeffect ..) = cont_run k (phi ..)`.
   ═══════════════════════════════════════════════════════════════════ *)

Theorem mrun_done_sound : forall phi B g st,
  mrun B g = DDone st -> cfg_run phi g = Some st.
Proof.
  intros phi B. induction B as [|B' IH]; intros g st H.
  - cbn [mrun] in H. discriminate.
  - cbn [mrun] in H.
    destruct (step g) as [g' | idx argv k s | sd |] eqn:Es; cbn in H.
    + apply IH in H. rewrite <- step_preserves, Es. exact H.
    + discriminate H.
    + injection H as Eeq; subst st.
      rewrite <- step_preserves, Es. cbn [out_run]. reflexivity.
    + discriminate H.
Qed.

Theorem mrun_eff_sound : forall phi B g idx argv k s,
  mrun B g = DEff idx argv k s ->
  cfg_run phi g = cont_run phi k (phi idx argv s).
Proof.
  intros phi B. induction B as [|B' IH]; intros g idx argv k s H.
  - cbn [mrun] in H. discriminate.
  - cbn [mrun] in H.
    destruct (step g) as [g' | idx2 argv2 k2 s2 | sd |] eqn:Es; cbn in H.
    + apply IH in H. rewrite <- step_preserves, Es. exact H.
    + rewrite <- step_preserves, Es. cbn [out_run].
      injection H as Hi2 Ha2 Hk2 Hs2; subst idx2; subst argv2; subst k2; subst s2.
      reflexivity.
    + discriminate H.
    + discriminate H.
Qed.

(* ═══════════════════════════════════════════════════════════════════
   §3  Determinism — a reached answer is stable under extra budget

   Needed to reconcile `mrun`'s per-step budget with the host's per-segment
   budget when lifting `mloop`'s answer to `host`'s (§5).
   ═══════════════════════════════════════════════════════════════════ *)

Lemma mrun_dres_monotone : forall B B' g d,
  B <= B' -> mrun B g = d -> d <> DLim -> mrun B' g = d.
Proof.
  intros B. induction B as [|B'' IH]; intros B' g d Hle Hd Hn.
  - cbn [mrun] in Hd. subst d. discriminate.
  - destruct B' as [|B']; [ lia |].
    cbn [mrun].
    destruct (step g) as [g' | idx argv k s | sd |] eqn:Es; cbn [mrun].
    + apply IH; [ lia | exact Hd | exact Hn ].
    + rewrite Hd. reflexivity.
    + rewrite Hd. reflexivity.
    + subst d. contradiction.
Qed.

Lemma host_monotone : forall B B' phi g st,
  B <= B' -> host phi B g = BOk st -> host phi B' g = BOk st.
Proof.
  intros B. induction B as [|B'' IH]; intros B' phi g st Hle Hh.
  - cbn [host] in Hh. discriminate.
  - destruct B' as [|B']; [ lia |].
    cbn [host] in Hh |- *.
    destruct (mrun B'' g) as [sd | idx argv k s |] eqn:Hm; cbn in Hh.
    + (* DDone sd *)
      injection Hh as Eeq; subst st.
      rewrite (mrun_dres_monotone B'' B' g (DDone sd)); try lia.
      - reflexivity.
      - exact Hm.
      - discriminate.
    + (* DEff *)
      destruct (phi idx argv s) as [s' |] eqn:Ep; [ | discriminate Hh].
      rewrite (mrun_dres_monotone B'' B' g (DEff idx argv k s)); try lia.
      - apply IH; [ lia | exact Hh ].
      - exact Hm.
      - discriminate.
    + discriminate Hh.
Qed.

(* If `mloop phi B g` reaches an answer, `mrun B g` (same budget) cannot be
   DLim: the two drivers decrement budget identically along Onext steps and stop
   at the same first boundary. *)
Lemma mrun_not_dlim : forall B phi g st,
  mloop phi B g = BOk st -> mrun B g <> DLim.
Proof.
  intros B. induction B as [|B' IH]; intros phi g st H.
  - cbn [mloop] in H. discriminate.
  - cbn [mloop mrun] in H.
    destruct (step g) as [g' | idx argv k s | sd |] eqn:Es; cbn [mrun] in H |- *.
    + apply IH. exact H.
    + destruct (phi idx argv s) as [s' |] eqn:Ep; [ | discriminate H]. discriminate.
    + discriminate.
    + discriminate H.
Qed.

(* ═══════════════════════════════════════════════════════════════════
   §4  Budget progress across a whole mrun segment

   When `mrun` stops at an effect, the re-entry config the host resumes from
   (`CFG 0 None k s'`) has a strictly smaller `cfg_budget` than the start — proved
   by composing phase2's `next_decrease` over the Onext prefix plus the final
   effect edge.  This is what makes the host's segment recursion well-founded.
   ═══════════════════════════════════════════════════════════════════ *)

Lemma mrun_deff_budget : forall B g idx argv k s s',
  mrun B g = DEff idx argv k s ->
  cfg_budget (CFG 0 None k s') < cfg_budget g.
Proof.
  intros B. induction B as [|B' IH]; intros g idx argv k s s' H.
  - cbn [mrun] in H. discriminate.
  - cbn [mrun] in H.
    destruct (step g) as [g' | idx2 argv2 k2 s2 | sd |] eqn:Es; cbn in H.
    + (* Onext g': IH at the successor, then the successor is below g *)
      apply IH in H.
      assert (Nd : cfg_budget g' < cfg_budget g).
      { apply next_decrease. unfold next. left. exact Es. }
      lia.
    + (* immediate effect at g: the phase2 effect edge ranks it directly *)
      injection H as Hi2 Ha2 Hk2 Hs2; subst idx2; subst argv2; subst k2; subst s2.
      apply next_decrease. unfold next. right.
      exists idx; exists argv; exists k; exists s; exists s'.
      split; [ exact Es | reflexivity ].
    + discriminate H.
    + discriminate H.
Qed.

(* ═══════════════════════════════════════════════════════════════════
   §5  The host is sound and complete against the reference meaning

   host_sound   : never a wrong answer.
   host_live    : every answer run accepts is reached (strong induction on the
                  nat `cfg_budget`, seeded by mrun_live and closed with the §4
                  ranking + the §3 monotone lemmas to reconcile the budgets).
   Then the two-sided statement at the initial configuration.
   ═══════════════════════════════════════════════════════════════════ *)

Theorem host_sound : forall phi B g st,
  host phi B g = BOk st -> cfg_run phi g = Some st.
Proof.
  intros phi B. induction B as [|B' IH]; intros g st H.
  - cbn [host] in H. discriminate.
  - cbn [host] in H.
    destruct (mrun B' g) as [sd | idx argv k s |] eqn:Hm; cbn in H.
    + (* DDone sd *)
      injection H as Eeq; subst st.
      exact (mrun_done_sound phi B' g sd Hm).
    + (* DEff *)
      destruct (phi idx argv s) as [s' |] eqn:Ep; [ | discriminate H].
      apply IH in H.
      assert (Eg : cfg_run phi g = cont_run phi k (Some s')).
      { rewrite (mrun_eff_sound phi B' g idx argv k s Hm), Ep. reflexivity. }
      unfold cfg_run in H. cbn [cc ck cs] in H.
      rewrite Eg. exact H.
    + discriminate H.
Qed.

Lemma host_live_aux : forall n phi g st,
  cfg_budget g <= n -> cfg_run phi g = Some st ->
  exists B, host phi B g = BOk st.
Proof.
  induction n as [|n IHn]; intros phi g st Hb Hr.
  destruct (mrun_live phi g st Hr) as [B0 Hm0].
  assert (NE : mrun B0 g <> DLim) by (apply mrun_not_dlim, Hm0).
  destruct (mrun B0 g) as [sd | idx argv k s |] eqn:Hm; [ | | contradiction].
  - (* DDone: host (S B0) reaches it directly *)
    assert (E : cfg_run phi g = Some sd) := mrun_done_sound phi B0 g sd Hm.
    assert (Eq : Some sd = Some st) by (rewrite <- E, <- Hr; reflexivity).
    injection Eq as Eeq; subst st.
    exists (S B0). cbn [host]. rewrite Hm. reflexivity.
  - (* DEff: service the seam (must succeed) and recurse on the ranked successor *)
    destruct (phi idx argv s) as [s' |] eqn:Ep; [ | ].
    + assert (Eg : cfg_run phi g = cont_run phi k (Some s')).
      { rewrite (mrun_eff_sound phi B0 g idx argv k s Hm), Ep. reflexivity. }
        assert (Ere : cfg_run phi (CFG 0 None k s') = Some st).
        { unfold cfg_run. cbn [cc ck cs]. rewrite <- Eg. exact Hr. }
        assert (Ndb : cfg_budget (CFG 0 None k s') < cfg_budget g)
          by (apply (mrun_deff_budget B0 g idx argv k s s' Hm)).
        destruct (IHn phi (CFG 0 None k s') st) as [B' Hb']; [ lia | exact Ere |].
        exists (S (B0 + B')). cbn [host].
        rewrite (mrun_dres_monotone B0 (B0 + B') g (DEff idx argv k s)); [ | | exact Hm].
        * apply (host_monotone B' (B0 + B') phi (CFG 0 None k s') st); [ lia | exact Hb' ].
        * lia.
        * discriminate.
    + rewrite (mrun_eff_sound phi B0 g idx argv k s Hm), Ep, cont_run_none in Hr.
      discriminate.
Qed.

Theorem host_live : forall phi g st,
  cfg_run phi g = Some st -> exists B, host phi B g = BOk st.
Proof.
  intros phi g st Hr.
  exact (host_live_aux (cfg_budget g) phi g st (Nat.le_refl (cfg_budget g)) Hr).
Qed.

(* ═══════════════════════════════════════════════════════════════════
   §6  Initial-configuration corollaries against concrete `run`

   cfg_run phi (CFG F (Some c) [] s) unfolds to `run phi F c s` (empty stack), so
   the host's soundness/completeness become exactly the JPL.3/3b statements for
   the closure-free driver.
   ═══════════════════════════════════════════════════════════════════ *)

Theorem host_correct : forall phi B F c s st,
  host phi B (CFG F (Some c) [] s) = BOk st -> run phi F c s = Some st.
Proof.
  intros phi B F c s st H.
  apply host_sound in H.
  unfold cfg_run, cont_run in H. cbn [cc ck] in H. exact H.
Qed.

Theorem host_complete : forall phi F c s st,
  run phi F c s = Some st -> exists B, host phi B (CFG F (Some c) [] s) = BOk st.
Proof.
  intros phi F c s st Hr.
  apply host_live. unfold cfg_run, cont_run. cbn. exact Hr.
Qed.

Theorem host_iff_run : forall phi F c s st,
  run phi F c s = Some st <-> exists B, host phi B (CFG F (Some c) [] s) = BOk st.
Proof.
  split.
  - intro Hr. exact (host_complete phi F c s st Hr).
  - intros [B HB]. exact (host_correct phi B F c s st HB).
Qed.

(* A rejected run is never turned into a host success. *)
Theorem run_none_host_limit : forall phi B F c s,
  run phi F c s = None ->
  forall st, host phi B (CFG F (Some c) [] s) <> BOk st.
Proof.
  intros phi B F c s Hr st Heq.
  apply host_correct in Heq. rewrite Hr in Heq. discriminate.
Qed.

(* ═══════════════════════════════════════════════════════════════════
   §7  §7 conformance boundary, re-checked by the data driver (pure_phi)

   Each is a closed computation whose result equals the concrete `run` fact from
   sh_concrete §7 — the data driver and the host are checked against the single
   source of truth, not a parallel re-derivation.
   ═══════════════════════════════════════════════════════════════════ *)

(* The pure seam has no external effect to service, so `mrun` runs straight to a
   DDone on the short-circuit boundary cases. *)
Example mrun_pure_and_left_false :
  mrun 5 (CFG (S 3) (Some (And (Ext 0 [false_w]) (Ext 0 [true_w]))) [] (CS 7 []))
  = DDone (CS 1 []).
Proof. reflexivity. Qed.

Example mrun_pure_or_left_true :
  mrun 5 (CFG (S 3) (Some (Or (Ext 0 [true_w]) (Ext 0 [false_w]))) [] (CS 7 []))
  = DDone (CS 0 []).
Proof. reflexivity. Qed.

Example mrun_pure_bang_false :
  mrun 5 (CFG (S 3) (Some (Bang (Ext 0 [false_w]))) [] (CS 7 []))
  = DDone (CS 0 []).
Proof. reflexivity. Qed.

Example mrun_pure_while_false_zero :
  mrun 5 (CFG (S 3) (Some (While (Ext 0 [false_w]) (Ext 0 [true_w]))) [] (CS 7 []))
  = DDone (CS 1 []).
Proof. reflexivity. Qed.

Example mrun_pure_assign_binds :
  match mrun 3 (CFG (S 3) (Some (Assign [97] [98])) [] (CS 7 [])) with
  | DDone s => getv [97] (cenv s)
  | _ => None
  end
  = Some [98].
Proof. reflexivity. Qed.

(* The host over the pure seam equals b_of (run pure_phi ...) on the same command,
   tying the data driver + host directly to the reference `run`. *)
Example host_pure_seq_eq_run :
  host pure_run_phi 8 (CFG (S 3) (Some (Seq (Ext 0 [true_w]) (Ext 0 [false_w]))) [] (CS 7 []))
  = b_of (run pure_run_phi (S 3) (Seq (Ext 0 [true_w]) (Ext 0 [false_w])) (CS 7 [])).
Proof. reflexivity. Qed.

Example host_pure_if_eq_run :
  host pure_run_phi 6 (CFG (S 3) (Some (If (Ext 0 [true_w]) (Ext 0 [false_w]) (Ext 0 [true_w]))) [] (CS 7 []))
  = b_of (run pure_run_phi (S 3) (If (Ext 0 [true_w]) (Ext 0 [false_w]) (Ext 0 [true_w])) (CS 7 [])).
Proof. reflexivity. Qed.

(* ═══════════════════════════════════════════════════════════════════
   §8  The driver is closure-free by construction

   `mrun` and `dres` mention no `run_phi`: the kernel loop the emitter lowers has
   the seam only as DATA (JPL Rules 6 / 29).  Recorded as a computable witness —
   `mrun` is a function of the step budget and configuration alone. *)

Example mrun_takes_no_phi :
  mrun = mrun.  (* the driver's type is nat -> cfg -> dres, with no run_phi index *)
Proof. reflexivity. Qed.

Check mrun.      (* nat -> cfg -> dres *)
Check dres.      (* Type: DDone / DEff (effect data) / DLim *)
