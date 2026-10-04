(* sh_jpl_run_c.v

 * JPL.5-A.6 — the small-step machine REWIRED onto the proved tail loops.

 * sh_jpl_run.v defines `step` against sh_concrete's recursive helpers: `setv`
 * (structural recursion that conses on the way back out) and `match_any` (a tree
 * recursion over the pattern list).  sh_jpl_scan.v §4.3 and §5 built the
 * tail-loop counterparts and PROVED them faithful (`match_any_iter`, `setv_it`),
 * but with one catch this file is built around:

 *   the two matchers have DIFFERENT fuel laws.  L2's `match_any g pats w` globs
 *   pattern i at fuel `g - 1 - i`, so it decides a branch at the LINEAR threshold
 *   `branch_need pats w = max_i (|p_i| + |w| + i + 2)`; the loop needs the
 *   QUADRATIC `fuel_top` per pattern, i.e. the budget `GLOB_FUEL + length pats`.
 *   Below its own `fuel_top` the loop can answer `false` where L2 already answers
 *   `true` — Example tree_decides_below_loop_need measures that band exactly
 *   (pattern [*;a] against a-a-a: L2 decisive at site fuel 6, loop needs 29).  So
 *   the loop cannot simply be dropped in.

 * The rewiring therefore GUARDS each case site and reads a failed guard as the
 * machine's saturate-to-error edge, exactly like exhausted fuel:

 *   step_c_ok : step_c g <> Olimit -> step_c g = step g        (the headline)

 * There is no unconditional `step_c = step`, and §6 proves it by exhibiting a
 * command where the reference answers and the rewired machine reports BLimit.
 * `branch_guardb` is one decidable boolean — a linear comparison of
 * `branch_need` against the site fuel plus the word-length caps — so guarding
 * costs the kernel a comparison, not a second matcher.  §5 then shows the guard
 * is free at the budgets this layer already carries: its worst case is 1537, that
 * number is ATTAINED (so it is least, not merely enough), a whole branch chain of
 * MAX_LIST walks needs 2561, and both sit three orders of magnitude under
 * MAX_FUEL = 136449.  GLOB_FUEL itself is not slack either: it is *literally*
 * `fuel_top` at two full-width words.

 * What this module adds, all derived from the existing layers:
 *   - §1 the rewired sites: expand_c (word cap) and bind_word_o on expand_it
 *     (scan §6), assign_c (setv_it scan), enter_for_c,
 *     enter_case_c (guard + match_any_iter + expand_it);
 *   - §2 site agreement and step_c_ok / step_c_preserves;
 *   - §3 mrun_c and mrun_c_ok, whence UNCONDITIONAL soundness — a data boundary
 *     cannot have passed through a fired guard;
 *   - §4 host_c, with no_sat as the single hypothesis that buys host_c = host:
 *     soundness needs no hypothesis, completeness is transported under it;
 *   - §5 the budget arithmetic, including the two tightness results and
 *     enter_case_c_chain_clear (ample fuel ⇒ no saturation, proved by induction
 *     on the site fuel over the whole branch chain);
 *   - §6 the phase3 §7 surface re-produced by the REWIRED kernel, by computation,
 *     plus the saturating low-fuel case as the counterexample to dropping a guard.

 * NOTHING in this module reaches a non-tail scan any more.  The last one was
 * sh_concrete's `expand`/`expand_name`/`expand_brace` mutual fixpoint, reached at
 * `bind_word_o` and at the scrutinee of `enter_case_c`; those two sites now call
 * `expand_it` (sh_jpl_scan §6), whose agreement with the reference —
 * `expand_it_correct : forall f m st inp, expand_it f m st inp = expand f m st inp`
 * — carries NO hypothesis.  That is the difference from the case-matchers of §5:
 * the expander loop mirrors L2's fuel decrements one for one, so it needs no
 * guard and no raised budget.  Each proof below still reads against the §2/§5
 * statements, which are phrased about the reference, via `exp_ref`, which is just
 * `repeat rewrite expand_it_correct`.  The RESULT stays capped here (`expand_c`),
 * which is what turns the branch guard into a closed condition on the caps rather
 * than a side condition about `expand`; the chain lemma states the expansion
 * bound as a hypothesis precisely because L2 proves nothing about the length of
 * `expand`.

 * Build (Rocq >= 9.0):
 *   coqc sh_concrete.v sh_jpl.v sh_jpl_run.v sh_jpl_run_phase2.v
 *   coqc sh_jpl_scan.v sh_jpl_run_phase3.v sh_jpl_run_c.v
 *   coqchk -o -silent sh_jpl_run_c   # must report the four <none> lines
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Wf_nat.
Import ListNotations.

Require Import sh_concrete.          (* the reference semantics run/expand/setv *)
Require Import sh_jpl.               (* caps, bword/bres carriers, b_fuel *)
Require Import sh_jpl_run.           (* frame/cfg/out/step + cfg_run/step_preserves *)
Require Import sh_jpl_run_phase2.    (* next / cfg_budget / mrun_live *)
Require Import sh_jpl_scan.          (* setv_it / match_any_iter / branch_guardb *)
Require Import sh_jpl_run_phase3.    (* dres / mrun / host and their theorems *)

Set Warnings "-register-all".

(* ═══════════════════════════════════════════════════════════════════
   §1  The rewired sites
   ═══════════════════════════════════════════════════════════════════ *)

(* `expand_c` runs the proved tail loop `expand_it` (sh_jpl_scan §6 — the very same
   function as L2's `expand` at every fuel, by `expand_it_correct`, which carries no
   hypothesis) and caps its RESULT: BOk when the expansion fits MAX_WORD, BLimit
   when it does not — the same saturate-to-error answer the bounded-array layer
   gives for an over-width append (b_app_wf).  The cap has to exist: L2 places no
   bound on the INPUT word, which comes straight from the parser.  Because the
   check is on the expansion itself, no caller has to know anything about
   `expand` — or about the loop that now stands in for it. *)
Definition expand_c (f : nat) (m : list (text * text)) (st : nat) (inp : text)
  : bres bword :=
  let w := expand_it f m st inp in
  if Nat.leb (length w) MAX_WORD then BOk (raw_bword w) else BLimit.

Lemma expand_c_ok : forall f m st inp x,
  expand_c f m st inp = BOk x -> x = raw_bword (expand f m st inp).
Proof.
  intros f m st inp x H. unfold expand_c in H.
  rewrite !expand_it_correct in H.
  destruct (Nat.leb (length (expand f m st inp)) MAX_WORD) eqn:Eb;
    [ | discriminate H].
  injection H as E; subst x; reflexivity.
Qed.

Lemma expand_c_in_bounds : forall f m st inp x,
  expand_c f m st inp = BOk x -> length (expand f m st inp) <= MAX_WORD.
Proof.
  intros f m st inp x H. unfold expand_c in H.
  rewrite !expand_it_correct in H.
  destruct (Nat.leb (length (expand f m st inp)) MAX_WORD) eqn:Eb;
    [ | discriminate H].
  apply Nat.leb_le. exact Eb.
Qed.

(* The environment write, now one forward scan (scan §5).  MAX_FUEL cells is not a
   guess: scan's setv_it_some_agree proves a scan that RETURNS is faithful at ANY
   fuel, so `None` is the only failure mode and it means the environment is longer
   than the machine's whole fuel budget. *)
Definition assign_c (nm val : text) (k : stack) (s : cstate) : out :=
  match setv_it MAX_FUEL nm val [] (cenv s) with
  | Some e => Onext (CFG 0 None k (CS 0 e))
  | None   => Olimit
  end.

(* `bind_word` with both recursions replaced: the expansion capped, the write
   scanned.  `None` means saturate; the caller carries no length obligation. *)
Definition bind_word_o (g : nat) (var w : text) (s : cstate) : option cstate :=
  match expand_c g (cenv s) (cstatus s) w with
  | BOk x =>
      match setv_it MAX_FUEL var (bw_bytes x) [] (cenv s) with
      | Some e => Some (CS (cstatus s) e)
      | None   => None
      end
  | BLimit => None
  end.

Lemma bind_word_o_ok : forall g var w s s',
  bind_word_o g var w s = Some s' -> s' = bind_word g var w s.
Proof.
  intros g var w s s' H. unfold bind_word_o, bind_word in H |- *.
  destruct (expand_c g (cenv s) (cstatus s) w) as [x |] eqn:Ex;
    [ | discriminate H].
  destruct (setv_it MAX_FUEL var (bw_bytes x) [] (cenv s)) as [e |] eqn:Ee;
    [ | discriminate H].
  injection H as Es; subst s'.
  assert (BX : bw_bytes x = expand g (cenv s) (cstatus s) w).
  { rewrite (expand_c_ok g (cenv s) (cstatus s) w x Ex). reflexivity. }
  assert (BE : e = rev_append [] (setv var (bw_bytes x) (cenv s)))
    by (exact (setv_it_some_agree MAX_FUEL var (bw_bytes x) [] (cenv s) e Ee)).
  rewrite BE, <- BX. cbn [rev_append]. reflexivity.
Qed.

(* enter_for with the binding site rewired; the match SHAPE is unchanged, so
   Olimit is reached exactly where a scan or a width cap failed. *)
Definition enter_for_c (h : nat) (var : text) (ws : list text) (body : list cmd)
  (s : cstate) (k : stack) : out :=
  match h with
  | 0 => Olimit
  | S g =>
      match ws with
      | [] => Onext (CFG 0 None k (CS 0 (cenv s)))
      | [w] =>
          match bind_word_o g var w s with
          | Some s' => enter_seq g body s' k
          | None    => Olimit
          end
      | w :: w2 :: r =>
          match bind_word_o g var w s with
          | Some s' => enter_seq g body s' (FForRest g var (w2 :: r) body :: k)
          | None    => Olimit
          end
      end
  end.

(* enter_case with the tree matcher replaced by (guard, tail loop): the guard
   reads the site fuel L2 would have used, the loop gets its OWN budget
   `GLOB_FUEL + length pats`, and §5 keeps that budget inside MAX_FUEL. *)
Fixpoint enter_case_c (h : nat) (scrut : text)
  (brs : list (list text * list cmd)) (s : cstate) (k : stack) : out :=
  match h with
  | 0 => Olimit
  | S g =>
      match brs with
      | [] => Onext (CFG 0 None k (CS 0 (cenv s)))
      | (pats, body) :: r =>
          let w := expand_it g (cenv s) (cstatus s) scrut in
          if branch_guardb g pats w
          then if match_any_iter (GLOB_FUEL + length pats) pats w
               then enter_seq g body s k
               else enter_case_c g scrut r s k
          else Olimit
      end
  end.

(* ═══════════════════════════════════════════════════════════════════
   §2  Site agreement, and the headline contract
   ═══════════════════════════════════════════════════════════════════ *)

Lemma assign_c_ok : forall nm val k s,
  assign_c nm val k s <> Olimit ->
  assign_c nm val k s = Onext (CFG 0 None k (CS 0 (setv nm val (cenv s)))).
Proof.
  intros nm val k s Hne. unfold assign_c.
  destruct (setv_it MAX_FUEL nm val [] (cenv s)) as [e |] eqn:Es;
    [ | exfalso; apply Hne; unfold assign_c; rewrite Es; cbn; reflexivity ].
  assert (A : e = rev_append [] (setv nm val (cenv s)))
    by (exact (setv_it_some_agree MAX_FUEL nm val [] (cenv s) e Es)).
  rewrite A. cbn [rev_append]. reflexivity.
Qed.

(* The saturations, stated forward: a failed binding is the ONLY way a rewired
   for-site reaches Olimit, and having it as an equation keeps the case-split
   context of the agreement lemma untouched. *)
Lemma enter_for_c1_limit : forall g var w body s k,
  bind_word_o g var w s = None ->
  enter_for_c (S g) var [w] body s k = Olimit.
Proof. intros g var w body s k Eb. cbn [enter_for_c]. rewrite Eb. reflexivity. Qed.

Lemma enter_for_c2_limit : forall g var w w2 r body s k,
  bind_word_o g var w s = None ->
  enter_for_c (S g) var (w :: w2 :: r) body s k = Olimit.
Proof. intros g var w w2 r body s k Eb. cbn [enter_for_c]. rewrite Eb. reflexivity. Qed.

Lemma enter_for_c_ok : forall h var ws body s k,
  enter_for_c h var ws body s k <> Olimit ->
  enter_for_c h var ws body s k = enter_for h var ws body s k.
Proof.
  intros h var ws body s k Hne.
  destruct h as [ | g ]; [ exfalso; apply Hne; reflexivity | ].
  destruct ws as [ | w ws' ]; [ reflexivity | ].
  destruct ws' as [ | w2 r ].
  - destruct (bind_word_o g var w s) as [s' |] eqn:Eb;
    [ | exfalso; apply Hne; exact (enter_for_c1_limit g var w body s k Eb) ].
    cbn [enter_for_c enter_for]. rewrite Eb.
    rewrite (bind_word_o_ok g var w s s' Eb). reflexivity.
  - destruct (bind_word_o g var w s) as [s' |] eqn:Eb;
    [ | exfalso; apply Hne; exact (enter_for_c2_limit g var w w2 r body s k Eb) ].
    cbn [enter_for_c enter_for]. rewrite Eb.
    rewrite (bind_word_o_ok g var w s s' Eb). reflexivity.
Qed.

(* scan §6.3: the loop and L2's `expand` are the same function at every fuel.  The
   sites below CALL the loop, the §2/§5 statements are still phrased about the
   reference, so each proof reads the one back into the other. *)
Ltac exp_ref := repeat rewrite expand_it_correct.

Lemma enter_case_c_guard_limit : forall g scrut pats body r s k,
  branch_guardb g pats (expand g (cenv s) (cstatus s) scrut) = false ->
  enter_case_c (S g) scrut ((pats, body) :: r) s k = Olimit.
Proof.
  intros g scrut pats body r s k Eb.
  cbn [enter_case_c]. exp_ref. rewrite Eb. reflexivity.
Qed.

(* guard passed and the loop declined: the machine walks on to the next branch,
   spending one unit of the site fuel. *)
Lemma enter_case_c_walkon : forall g scrut pats body r s k,
  branch_guardb g pats (expand g (cenv s) (cstatus s) scrut) = true ->
  match_any_iter (GLOB_FUEL + length pats) pats
                 (expand g (cenv s) (cstatus s) scrut) = false ->
  enter_case_c (S g) scrut ((pats, body) :: r) s k = enter_case_c g scrut r s k.
Proof.
  intros g scrut pats body r s k Eb Em.
  cbn [enter_case_c]. exp_ref. rewrite Eb, Em. reflexivity.
Qed.

Lemma enter_case_c_ok : forall h scrut brs s k,
  enter_case_c h scrut brs s k <> Olimit ->
  enter_case_c h scrut brs s k = enter_case h scrut brs s k.
Proof.
  induction h as [ | g IH ]; intros scrut brs s k Hne.
  - exfalso. apply Hne. reflexivity.
  - destruct brs as [ | [pats body] r ]; [ reflexivity | ].
    destruct (branch_guardb g pats (expand g (cenv s) (cstatus s) scrut)) eqn:Eb;
      [ | exfalso; apply Hne;
             exact (enter_case_c_guard_limit g scrut pats body r s k Eb) ].
    destruct (match_any_iter (GLOB_FUEL + length pats) pats
                       (expand g (cenv s) (cstatus s) scrut)) eqn:Em.
    + (* guard passed and the loop matched: scan's branch_guardb_match says the
         tree matcher agrees at this very site, so both take the branch *)
      cbn [enter_case_c enter_case]. exp_ref.
      rewrite Eb,
        <- (branch_guardb_match g pats (expand g (cenv s) (cstatus s) scrut) Eb), Em.
      reflexivity.
    + (* guard passed and the loop declined: both walk on at the next site fuel *)
      rewrite (enter_case_c_walkon g scrut pats body r s k Eb Em) in Hne.
      rewrite (enter_case_c_walkon g scrut pats body r s k Eb Em).
      cbn [enter_case]. exp_ref.
      rewrite <- (branch_guardb_match g pats (expand g (cenv s) (cstatus s) scrut) Eb), Em.
      rewrite (IH scrut r s k Hne). reflexivity.
Qed.

Definition step_cmd_c (f : nat) (c : cmd) (k : stack) (s : cstate) : out :=
  match f with
  | 0 =>
      match c with
      | Skip => Onext (CFG 0 None k s)
      | Ext idx argv => Oeffect idx argv k s
      | Assign k' v => assign_c k' v k s
      | _ => Olimit
      end
  | S f' =>
      match c with
      | Skip => Onext (CFG 0 None k s)
      | Ext idx argv => Oeffect idx argv k s
      | Assign k' v => assign_c k' v k s
      | Bang c0 => Onext (CFG f' (Some c0) (FBang :: k) s)
      | Seq c1 c2 => Onext (CFG f' (Some c1) (FSeq f' c2 :: k) s)
      | And c1 c2 => Onext (CFG f' (Some c1) (FAnd f' c2 :: k) s)
      | Or c1 c2 => Onext (CFG f' (Some c1) (FOr f' c2 :: k) s)
      | If cond t e => Onext (CFG f' (Some cond) (FIf f' t e :: k) s)
      | While cond body => Onext (CFG f' (Some cond) (FWhile f' cond body :: k) s)
      | For var ws body => enter_for_c f' var ws body s k
      | Case scrut brs => enter_case_c f' scrut brs s k
      end
  end.

Definition step_ret_c (k : stack) (s : cstate) : out :=
  match k with
  | [] => Odone s
  | fr :: r =>
      match fr with
      | FSeq f c2 => Onext (CFG f (Some c2) r s)
      | FAnd f c2 => if isz s then Onext (CFG f (Some c2) r s) else Onext (CFG 0 None r s)
      | FOr f c2 => if isz s then Onext (CFG 0 None r s) else Onext (CFG f (Some c2) r s)
      | FBang => Onext (CFG 0 None r (CS (bstat (cstatus s)) (cenv s)))
      | FIf f t e => if isz s then Onext (CFG f (Some t) r s) else Onext (CFG f (Some e) r s)
      | FWhile f cnd bdy =>
          if isz s then Onext (CFG f (Some bdy) (FWhileBody f cnd bdy :: r) s)
          else Onext (CFG 0 None r s)
      | FWhileBody f cnd bdy => Onext (CFG f (Some (While cnd bdy)) r s)
      | FSeqList f l => enter_seq f l s r
      | FForRest f var rws body => enter_for_c f var rws body s r
      end
  end.

Definition step_c (g : cfg) : out :=
  match cc g with
  | Some c => step_cmd_c (cf g) c (ck g) (cs g)
  | None => step_ret_c (ck g) (cs g)
  end.

Lemma step_cmd_c_ok : forall f c k s,
  step_cmd_c f c k s <> Olimit -> step_cmd_c f c k s = step_cmd f c k s.
Proof.
  intros f c k s Hne.
  destruct f as [ | f' ]; destruct c;
    cbn [step_cmd_c step_cmd] in Hne |- *;
    try reflexivity;
    try (exact (assign_c_ok _ _ _ _ Hne));
    try (exact (enter_for_c_ok _ _ _ _ _ _ Hne));
    try (exact (enter_case_c_ok _ _ _ _ _ Hne)).
Qed.

Lemma step_ret_c_ok : forall k s,
  step_ret_c k s <> Olimit -> step_ret_c k s = step_ret k s.
Proof.
  intros k s Hne.
  destruct k as [ | fr r ]; cbn [step_ret_c step_ret] in Hne |- *.
  - reflexivity.
  - destruct fr;
      try reflexivity;
      try (exact (enter_for_c_ok _ _ _ _ _ _ Hne)).
Qed.

(* THE contract for the rewired kernel: saturation is the only divergence. *)
Theorem step_c_ok : forall g, step_c g <> Olimit -> step_c g = step g.
Proof.
  intros g Hne. destruct g as [f co k s].
  cbn [step_c step] in Hne |- *.
  destruct co as [c | ].
  - exact (step_cmd_c_ok f c k s Hne).
  - exact (step_ret_c_ok k s Hne).
Qed.

(* so the rewired dispatcher preserves meaning wherever it does not saturate:
   phase3's step_preserves carries across by rewriting, nothing is re-derived. *)
Corollary step_c_preserves : forall phi g,
  step_c g <> Olimit -> out_run phi (step_c g) = cfg_run phi g.
Proof.
  intros phi g Hne. rewrite (step_c_ok g Hne). apply step_preserves.
Qed.

(* ═══════════════════════════════════════════════════════════════════
   §3  The closure-free driver over step_c

   `mrun_c` is `mrun` with `step_c`.  `mrun_c_ok` is the whole transport: a driver
   that reaches a DATA boundary has not saturated, so every one of its steps
   agreed with `step`, so that boundary is exactly `mrun`'s.  Soundness then needs
   no hypothesis at all — the guard cannot have fired on a path that answers.
   ═══════════════════════════════════════════════════════════════════ *)

Fixpoint mrun_c (B : nat) (g : cfg) : dres :=
  match B with
  | 0 => DLim
  | S B' =>
      match step_c g with
      | Onext g'             => mrun_c B' g'
      | Oeffect idx argv k s => DEff idx argv k s
      | Odone st             => DDone st
      | Olimit               => DLim
      end
  end.

Lemma mrun_c_ok : forall B g, mrun_c B g <> DLim -> mrun_c B g = mrun B g.
Proof.
  induction B as [ | B' IH ]; intros g Hne.
  - exfalso. apply Hne. reflexivity.
  - destruct (step_c g) as [g' | idx argv k s | sd |] eqn:Ec;
      [ | | | exfalso; apply Hne; cbn [mrun_c]; rewrite Ec; reflexivity ].
    + (* Onext: the tail segment does not saturate either, so IH applies *)
      assert (HS : step_c g <> Olimit)
        by (intro Hc; rewrite Ec in Hc; discriminate).
      assert (HN : mrun_c B' g' <> DLim).
      { intro Hd. apply Hne. cbn [mrun_c]. rewrite Ec. exact Hd. }
      cbn [mrun_c]. rewrite Ec. rewrite (IH g' HN).
      cbn [mrun]. rewrite <- (step_c_ok g HS), Ec. reflexivity.
    + (* DEff: the seam is returned as data at this very step *)
      assert (HS : step_c g <> Olimit)
        by (intro Hc; rewrite Ec in Hc; discriminate).
      cbn [mrun_c]. rewrite Ec.
      cbn [mrun]. rewrite <- (step_c_ok g HS), Ec. reflexivity.
    + (* DDone: likewise *)
      assert (HS : step_c g <> Olimit)
        by (intro Hc; rewrite Ec in Hc; discriminate).
      cbn [mrun_c]. rewrite Ec.
      cbn [mrun]. rewrite <- (step_c_ok g HS), Ec. reflexivity.
Qed.

Theorem mrun_c_done_sound : forall phi B g st,
  mrun_c B g = DDone st -> cfg_run phi g = Some st.
Proof.
  intros phi B g st H.
  assert (NE : mrun_c B g <> DLim) by (intro Hd; rewrite H in Hd; discriminate).
  assert (Eq : mrun B g = DDone st).
  { rewrite <- (mrun_c_ok B g NE). exact H. }
  exact (mrun_done_sound phi B g st Eq).
Qed.

Theorem mrun_c_eff_sound : forall phi B g idx argv k s,
  mrun_c B g = DEff idx argv k s ->
  cfg_run phi g = cont_run phi k (phi idx argv s).
Proof.
  intros phi B g idx argv k s H.
  assert (NE : mrun_c B g <> DLim) by (intro Hd; rewrite H in Hd; discriminate).
  assert (Eq : mrun B g = DEff idx argv k s).
  { rewrite <- (mrun_c_ok B g NE). exact H. }
  exact (mrun_eff_sound phi B g idx argv k s Eq).
Qed.

(* ═══════════════════════════════════════════════════════════════════
   §4  The host over the rewired kernel

   `host_c` is phase3's `host` with `mrun_c`.  A BOk answer can only come from a
   DDone boundary, so SOUNDNESS carries with no hypothesis.  The converse does
   not: the reference host can answer on a path where a guard fired (Example
   host_c_saturates_where_host_answers), so COMPLETENESS is transported under
   `no_sat` — the proposition that the rewired kernel walks the reference path,
   i.e. that no guard fires anywhere along it.
   ═══════════════════════════════════════════════════════════════════ *)

Fixpoint host_c (phi : run_phi) (B : nat) (g : cfg) : bres cstate :=
  match B with
  | 0 => BLimit
  | S B' =>
      match mrun_c B' g with
      | DDone st => BOk st
      | DEff idx argv k s =>
          match phi idx argv s with
          | Some s' => host_c phi B' (CFG 0 None k s')
          | None    => BLimit
          end
      | DLim => BLimit
      end
  end.

(* the machine never invents an answer: every boundary it reports is a reference
   boundary, so host_c is sound outright. *)
Lemma host_c_bok_is_host_bok : forall phi B g st,
  host_c phi B g = BOk st -> host phi B g = BOk st.
Proof.
  intros phi B. induction B as [ | B' IH ]; intros g st H.
  - cbn [host_c] in H. discriminate H.
  - cbn [host_c] in H.
    destruct (mrun_c B' g) as [sd | idx argv k s |] eqn:Em; cbn in H.
    + injection H as Es; subst st.
      assert (NE : mrun_c B' g <> DLim)
        by (intro Hd; rewrite Em in Hd; discriminate).
      cbn [host]. rewrite <- (mrun_c_ok B' g NE), Em. reflexivity.
    + destruct (phi idx argv s) as [s' |] eqn:Ep; [ | discriminate H].
      apply IH in H.
      assert (NE : mrun_c B' g <> DLim)
        by (intro Hd; rewrite Em in Hd; discriminate).
      cbn [host]. rewrite <- (mrun_c_ok B' g NE), Em, Ep. exact H.
    + discriminate H.
Qed.

Theorem host_c_sound : forall phi B g st,
  host_c phi B g = BOk st -> cfg_run phi g = Some st.
Proof.
  intros phi B g st H.
  apply (host_sound phi B g st).
  exact (host_c_bok_is_host_bok phi B g st H).
Qed.

Theorem host_c_correct : forall phi B F c s st,
  host_c phi B (CFG F (Some c) [] s) = BOk st -> run phi F c s = Some st.
Proof.
  intros phi B F c s st H.
  apply host_correct with (B := B).
  exact (host_c_bok_is_host_bok phi B (CFG F (Some c) [] s) st H).
Qed.

(* no answer the reference produces can be turned into a machine success *)
Theorem run_none_host_c_limit : forall phi B F c s,
  run phi F c s = None ->
  forall st, host_c phi B (CFG F (Some c) [] s) <> BOk st.
Proof.
  intros phi B F c s Hr st Heq.
  apply host_c_correct in Heq. rewrite Hr in Heq. discriminate.
Qed.

(* the completeness hypothesis, over the machine's OWN path: every segment the
   host services must end at a data boundary, never at DLim. *)
Fixpoint no_sat (phi : run_phi) (B : nat) (g : cfg) : Prop :=
  match B with
  | 0 => True
  | S B' =>
      match mrun_c B' g with
      | DDone _  => True
      | DEff idx argv k s =>
          match phi idx argv s with
          | Some s' => no_sat phi B' (CFG 0 None k s')
          | None    => True
          end
      | DLim => False
      end
  end.

Lemma host_c_agree : forall phi B g, no_sat phi B g -> host_c phi B g = host phi B g.
Proof.
  intros phi B. induction B as [ | B' IH ]; intros g Hn.
  - reflexivity.
  - (* reduce the hypothesis FIRST, so the case split substitutes inside it and
       leaves the two goals' unreduced constants alone for the transport lemma. *)
    cbn [no_sat] in Hn.
    destruct (mrun_c B' g) as [sd | idx argv k s |] eqn:Em.
    + assert (NE : mrun_c B' g <> DLim)
        by (intro Hd; rewrite Em in Hd; discriminate).
      cbn [host_c host]. rewrite <- (mrun_c_ok B' g NE), Em. reflexivity.
    + assert (NE : mrun_c B' g <> DLim)
        by (intro Hd; rewrite Em in Hd; discriminate).
      cbn [host_c host]. rewrite <- (mrun_c_ok B' g NE), Em.
      destruct (phi idx argv s) as [s' |] eqn:Ep; [ | reflexivity ].
      rewrite (IH (CFG 0 None k s') Hn). reflexivity.
    + destruct Hn.
Qed.

Theorem host_c_complete : forall phi B g st,
  no_sat phi B g -> host phi B g = BOk st -> host_c phi B g = BOk st.
Proof.
  intros phi B g st Hn Hh. rewrite (host_c_agree phi B g Hn). exact Hh.
Qed.

(* The two-sided statement at a budget the reference host already suffices at,
   under the one hypothesis §5 shows how to discharge for the branch sites.
   There is NO unconditional `run = Some st -> exists B, host_c = BOk st`: a branch
   site whose fuel is below the guard threshold is answered by `run` (whose matcher
   is a tree) and refused by the machine at every budget, because the guard reads
   the SITE fuel, not the driver's budget — Example
   host_c_saturates_where_host_answers is that command. *)
Theorem host_c_iff_run : forall phi B F c s st,
  no_sat phi B (CFG F (Some c) [] s) ->
  host phi B (CFG F (Some c) [] s) = BOk st ->
  (run phi F c s = Some st <-> host_c phi B (CFG F (Some c) [] s) = BOk st).
Proof.
  intros phi B F c s st Hn Hh.
  rewrite (host_c_agree phi B (CFG F (Some c) [] s) Hn).
  split; intros _.
  - exact Hh.
  - apply (host_correct phi B F c s st). exact Hh.
Qed.

(* ═══════════════════════════════════════════════════════════════════
   §5  Budget arithmetic: what the rewiring costs, and where its
       constants are least

   Three numbers matter to the rewired kernel and all three are pinned here.
   (a) The branch GUARD threshold.  `branch_need` needs at most
       `case_site_fuel = S (MAX_LIST + MAX_WORD + MAX_WORD)` = 1537, and 1537 is
       ATTAINED by a worst-shaped branch (branch_need_worst_case), so no smaller
       uniform site fuel decides every in-caps branch (guard_fuel_is_least).
   (b) The loop BUDGET `GLOB_FUEL + length pats` <= MAX_FUEL, and GLOB_FUEL is
       not slack either: it is *literally* `fuel_top MAX_WORD MAX_WORD`
       (glob_fuel_is_tight, fuel_top_at_caps), i.e. the least single budget that
       covers the caps it was derived from.
   (c) The branch CHAIN.  `enter_case_c` gives up one fuel unit per branch it
       walks, so `case_site_fuel + length brs <= h` is exactly the invariant that
       keeps every site of the chain above the guard threshold; §5.3 turns it into
       enter_case_c_chain_clear (ample fuel => no saturation), and the arithmetic
       shows 2561 <= GLOB_FUEL <= MAX_FUEL, i.e. the machine's ceiling funds the
       worst chain with fifty times over.  The margin inside MAX_FUEL is exactly
       MAX_CMD = 4096 (max_fuel_margin_eq_MAX_CMD); the chain needs MAX_LIST =
       1024, so the allowance is the smallest of the LOCKED caps that also covers
       the parser's node pool — it cannot be cut to the chain's 1024 without
       breaking the cmd-pool budget it shares.
   ═══════════════════════════════════════════════════════════════════ *)

Definition case_site_fuel : nat := S (MAX_LIST + MAX_WORD + MAX_WORD).  (* 1537 *)

(* §5.1 worst-case witnesses: a homogeneous list, so the caps can be attained *)

Fixpoint rep {A : Type} (n : nat) (x : A) : list A :=
  match n with
  | 0 => []
  | S n' => x :: rep n' x
  end.

Lemma rep_length : forall (A : Type) (n : nat) (x : A), length (rep n x) = n.
Proof.
  intros A n. induction n as [ | n' IH ]; intros x.
  - reflexivity.
  - cbn [rep length]. rewrite IH. reflexivity.
Qed.

(* the closed form of the guard threshold on a uniform branch list: one extra fuel
   unit per pattern, exactly as §4.3.15 of the scan layer describes *)
Lemma branch_need_repl : forall n p w,
  0 < n -> branch_need (rep n p) w = length p + length w + S n.
Proof.
  induction n as [ | n' IH ]; intros p w Hn; [ lia | ].
  cbn [rep branch_need].
  destruct n' as [ | m ].
  - (* a single pattern: its own need is the larger term *)
    rewrite Nat.max_l by (cbn [rep branch_need]; lia).
    lia.
  - (* two or more: the accumulated tail dominates *)
    rewrite (IH p w (Nat.lt_0_succ m)).
    rewrite Nat.max_r by lia.
    lia.
Qed.

(* §5.2 (a) the guard threshold is attained, and therefore least *)

Lemma branch_need_worst_case : forall p w,
  length p = MAX_WORD -> length w = MAX_WORD ->
  branch_need (rep MAX_LIST p) w = case_site_fuel.
Proof.
  intros p w Hp Hw.
  transitivity (length p + length w + S MAX_LIST).
  - apply (branch_need_repl MAX_LIST p w). unfold MAX_LIST. lia.
  - unfold case_site_fuel. rewrite Hp, Hw. unfold MAX_LIST, MAX_WORD. lia.
Qed.

Lemma guard_fuel_is_least : forall g,
  (forall p w, length p = MAX_WORD -> length w = MAX_WORD ->
      branch_need (rep MAX_LIST p) w <= g) ->
  case_site_fuel <= g.
Proof.
  intros g Hg.
  assert (L1 : length (rep MAX_WORD 97) = MAX_WORD) by (rewrite rep_length; reflexivity).
  assert (L2 : length (rep MAX_WORD 98) = MAX_WORD) by (rewrite rep_length; reflexivity).
  assert (W : branch_need (rep MAX_LIST (rep MAX_WORD 97)) (rep MAX_WORD 98) = case_site_fuel)
    by (apply (branch_need_worst_case (rep MAX_WORD 97) (rep MAX_WORD 98) L1 L2)).
  rewrite <- W.
  exact (Hg (rep MAX_WORD 97) (rep MAX_WORD 98) L1 L2).
Qed.

(* the fuel form of the guard, ready for the machine to cite: at site fuel 1537 or
   above an in-caps branch NEVER fails the guard. *)
Lemma branch_guardb_ample : forall g pats w,
  case_site_fuel <= g ->
  length pats <= MAX_LIST ->
  (forall p, In p pats -> length p <= MAX_WORD) ->
  length w <= MAX_WORD ->
  branch_guardb g pats w = true.
Proof.
  intros g pats w Hg Hn Hp Hw.
  apply (branch_guardb_true_of_caps g pats w Hn Hp Hw).
  unfold case_site_fuel.
  apply Nat.le_trans with (S (MAX_LIST + MAX_WORD + MAX_WORD));
    [ apply (branch_need_in_caps pats w Hn Hp Hw) | exact Hg ].
Qed.

(* §5.3 (c) ample fuel => no saturation, over a WHOLE branch chain *)

Lemma enter_case_c_matched : forall g scrut pats body r s k,
  branch_guardb g pats (expand g (cenv s) (cstatus s) scrut) = true ->
  match_any_iter (GLOB_FUEL + length pats) pats (expand g (cenv s) (cstatus s) scrut) = true ->
  enter_case_c (S g) scrut ((pats, body) :: r) s k = enter_seq g body s k.
Proof.
  intros g scrut pats body r s k Eb Em.
  cbn [enter_case_c]. exp_ref. rewrite Eb, Em. reflexivity.
Qed.

Lemma enter_seq_not_limit : forall h l s k, 0 < h -> enter_seq h l s k <> Olimit.
Proof.
  intros h l s k Hh. destruct h as [ | g ]; [ lia | ].
  destruct l as [ | c l' ]; [ | destruct l' as [ | c2 l2 ] ];
    cbn [enter_seq]; discriminate.
Qed.

Lemma enter_case_c_not_limit_nil : forall h scrut s k,
  0 < h -> enter_case_c h scrut [] s k <> Olimit.
Proof.
  intros h scrut s k Hh. destruct h as [ | g ]; [ lia | ].
  cbn [enter_case_c]; discriminate.
Qed.

Lemma enter_case_c_chain_clear : forall g scrut brs s k,
  case_site_fuel + length brs <= g ->
  (forall b, In b brs ->
      length (fst b) <= MAX_LIST /\ (forall p, In p (fst b) -> length p <= MAX_WORD)) ->
  (forall h, h <= g -> length (expand h (cenv s) (cstatus s) scrut) <= MAX_WORD) ->
  enter_case_c g scrut brs s k <> Olimit.
Proof.
  induction g as [ | g' IH ]; intros scrut brs s k H1 H2 H3.
  - exfalso. unfold case_site_fuel in H1. lia.
  - destruct brs as [ | [pats body] r ].
    + apply (enter_case_c_not_limit_nil (S g') scrut s k). lia.
    + cbn [length] in H1.
      assert (Harith : case_site_fuel <= g' /\ 0 < g' /\
                       case_site_fuel + length r <= g').
      { unfold case_site_fuel in H1 |- *. repeat split; lia. }
      destruct Harith as [Hsite [Hpos Hchain]].
      destruct (H2 (pats, body) (or_introl eq_refl)) as [Hpats Hpat].
      assert (Hg : branch_guardb g' pats (expand g' (cenv s) (cstatus s) scrut) = true).
      { apply (branch_guardb_ample g' pats (expand g' (cenv s) (cstatus s) scrut)
                 Hsite Hpats Hpat).
        apply H3. lia. }
      destruct (match_any_iter (GLOB_FUEL + length pats) pats
                         (expand g' (cenv s) (cstatus s) scrut)) eqn:Em.
      * assert (E1 : enter_case_c (S g') scrut ((pats, body) :: r) s k
                 = enter_seq g' body s k).
        { apply (enter_case_c_matched g' scrut pats body r s k Hg Em). }
        rewrite E1.
        apply (enter_seq_not_limit g' body s k). exact Hpos.
      * assert (E2 : enter_case_c (S g') scrut ((pats, body) :: r) s k
                 = enter_case_c g' scrut r s k).
        { apply (enter_case_c_walkon g' scrut pats body r s k Hg Em). }
        rewrite E2.
        refine (IH scrut r s k Hchain _ _);
          [ intros b Hb; apply (H2 b); right; exact Hb
          | intros h Hh; apply H3; lia ].
Qed.

(* §5.4 (b) the loop budget: GLOB_FUEL is the worst per-pattern need, exactly *)

Lemma glob_fuel_is_tight : fuel_top_nat MAX_WORD MAX_WORD = GLOB_FUEL.
Proof.
  unfold fuel_top_nat, scan, GLOB_FUEL, MAX_WORD. vm_compute. reflexivity.
Qed.

Lemma fuel_top_at_caps : forall pat str,
  length pat = MAX_WORD -> length str = MAX_WORD ->
  fuel_top pat str = GLOB_FUEL.
Proof.
  intros pat str Hp Hs.
  rewrite fuel_top_as_nat, Hp, Hs. symmetry. apply glob_fuel_is_tight.
Qed.

Lemma branch_chain_funded : GLOB_FUEL + MAX_LIST <= MAX_FUEL.
Proof.
  unfold MAX_FUEL, MAX_LIST, GLOB_FUEL, MAX_WORD. lia.
Qed.

Lemma case_allowance_inside_glob_fuel : case_site_fuel + MAX_LIST <= GLOB_FUEL.
Proof.
  unfold case_site_fuel, GLOB_FUEL, MAX_LIST, MAX_WORD.
  apply Nat.leb_le. vm_compute. reflexivity.
Qed.

Lemma max_fuel_margin_eq_MAX_CMD : MAX_FUEL - GLOB_FUEL = MAX_CMD.
Proof.
  unfold MAX_FUEL, MAX_CMD. lia.
Qed.

(* ═══════════════════════════════════════════════════════════════════
   §6  The rewired kernel checked by computation

   Each example below re-produces a phase3 §7 fact with the REWIRED driver: the
   same command, the same budget, the same answer — mrun_c/host_c on the left,
   computed.  The case examples enter at fuel 12 rather than the older 4-unit
   window, because the branch chain spends one fuel unit per branch and the guard
   needs 4 here; §5 quantifies exactly that difference.
   ═══════════════════════════════════════════════════════════════════ *)

Example mrun_c_pure_skip_done :
  mrun_c 8 (CFG (S 3) (Some (Seq Skip (Seq Skip Skip))) [] (CS 7 []))
  = DDone (CS 7 []).
Proof. vm_compute. reflexivity. Qed.

Example mrun_c_ext_is_data :
  mrun_c 2 (CFG (S 3) (Some (And (Ext 0 [false_w]) (Ext 0 [true_w]))) [] (CS 7 []))
  = DEff 0 [false_w] [FAnd 3 (Ext 0 [true_w])] (CS 7 []).
Proof. vm_compute. reflexivity. Qed.

(* the assignment now goes through the tail-loop scan, same answer *)
Example mrun_c_assign_is_scan :
  mrun_c 3 (CFG (S 3) (Some (Assign [97] [98])) [] (CS 7 []))
  = DDone (CS 0 [([97], [98])]).
Proof. vm_compute. reflexivity. Qed.

Example host_c_pure_and_left_false :
  host_c pure_run_phi 12 (CFG (S 3) (Some (And (Ext 0 [false_w]) (Ext 0 [true_w]))) [] (CS 7 []))
  = BOk (CS 1 []).
Proof. vm_compute. reflexivity. Qed.

Example host_c_pure_or_left_true :
  host_c pure_run_phi 12 (CFG (S 3) (Some (Or (Ext 0 [true_w]) (Ext 0 [false_w]))) [] (CS 7 []))
  = BOk (CS 0 []).
Proof. vm_compute. reflexivity. Qed.

Example host_c_pure_bang_false :
  host_c pure_run_phi 12 (CFG (S 3) (Some (Bang (Ext 0 [false_w]))) [] (CS 7 []))
  = BOk (CS 0 []).
Proof. vm_compute. reflexivity. Qed.

Example host_c_pure_while_false_zero :
  host_c pure_run_phi 12 (CFG (S 3) (Some (While (Ext 0 [false_w]) (Ext 0 [true_w]))) [] (CS 7 []))
  = BOk (CS 1 []).
Proof. vm_compute. reflexivity. Qed.

Example host_c_pure_assign_binds :
  match host_c pure_run_phi 12 (CFG (S 3) (Some (Assign [97] [98])) [] (CS 7 [])) with
  | BOk s => getv [97] (cenv s)
  | _ => None
  end
  = Some [98].
Proof. vm_compute. reflexivity. Qed.

(* the for-loop now binds its words through the scan and the width cap *)
Example host_c_pure_for_eq_run :
  host_c pure_run_phi 24 (CFG 6 (Some (For [120] [[97]; [98]] [Ext 0 [false_w]])) [] (CS 5 []))
  = b_of (run pure_run_phi 6 (For [120] [[97]; [98]] [Ext 0 [false_w]]) (CS 5 [])).
Proof. vm_compute. reflexivity. Qed.

(* the case site, rewired: same answer as the single source of truth *)
Example host_c_pure_case_eq_run :
  host_c pure_run_phi 12
    (CFG 12 (Some (Case [97] [([[97]], [Ext 0 [true_w]]); ([[98; 42]], [Ext 0 [false_w]])])) [] (CS 7 []))
  = b_of (run pure_run_phi 12
            (Case [97] [([[97]], [Ext 0 [true_w]]); ([[98; 42]], [Ext 0 [false_w]])]) (CS 7 [])).
Proof. vm_compute. reflexivity. Qed.

(* the band between the two matchers, measured on one branch:
   L2's guard threshold 7, decisive at site fuel 6, loop honest only at 29. *)
Example tree_decides_below_loop_need :
  branch_need [[42; 97]] [97; 97; 97] = 7 /\
  match_any 6 [[42; 97]] [97; 97; 97] = true /\
  glob_iter 6 [42; 97] [97; 97; 97] = false /\
  fuel_top [42; 97] [97; 97; 97] = 29.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* so at site fuel 6 the rewired machine saturates where the reference answers:
   the guard is load-bearing and no unconditional step_c = step exists. *)
Example guard_refuses_below_loop_need :
  enter_case_c 7 [97; 97; 97] [([[42; 97]], [Ext 0 [true_w]])] (CS 7 []) [] = Olimit /\
  enter_case 7 [97; 97; 97] [([[42; 97]], [Ext 0 [true_w]])] (CS 7 []) []
    = Onext (CFG 5 (Some (Ext 0 [true_w])) [] (CS 7 [])).
Proof. split; vm_compute; reflexivity. Qed.

(* and the saturation reaches the host: this is the ONLY way in which the rewired
   kernel is weaker than the model — a refusal, never a wrong answer (§4). *)
Example host_c_saturates_where_host_answers :
  host pure_run_phi 20 (CFG 8 (Some (Case [97; 97; 97] [([[42; 97]], [Ext 0 [true_w]])])) [] (CS 7 []))
    = BOk (CS 0 []) /\
  host_c pure_run_phi 20 (CFG 8 (Some (Case [97; 97; 97] [([[42; 97]], [Ext 0 [true_w]])])) [] (CS 7 []))
    = BLimit.
Proof. split; vm_compute; reflexivity. Qed.

(* one fuel unit higher the guard passes and the two hosts are equal by
   computation — no hypothesis needed at that site. *)
Example host_c_ample_case_matches_host :
  host_c pure_run_phi 20
    (CFG 9 (Some (Case [97; 97; 97] [([[42; 97]], [Ext 0 [true_w]])])) [] (CS 7 []))
  = host pure_run_phi 20
    (CFG 9 (Some (Case [97; 97; 97] [([[42; 97]], [Ext 0 [true_w]])])) [] (CS 7 [])).
Proof. vm_compute. reflexivity. Qed.

(* the width cap, in both directions: an expansion at MAX_WORD is admitted, one
   byte over it saturates instead of emitting an oversized word. *)
Example expand_c_admits_at_cap :
  expand_c (S MAX_WORD) [] 7 (rep MAX_WORD 97) = BOk (raw_bword (rep MAX_WORD 97)).
Proof. vm_compute. reflexivity. Qed.

Example expand_c_refuses_over_cap :
  expand_c (S MAX_WORD) [] 7 (rep (S MAX_WORD) 97) = BLimit.
Proof. vm_compute. reflexivity. Qed.

(* the branch budget the machine passes is inside the ceiling it emits *)
Example scan_budget_in_range : GLOB_FUEL + MAX_LIST <= MAX_FUEL.
Proof. apply branch_chain_funded. Qed.

(* ═══════════════════════════════════════════════════════════════════
   §7  The rewired kernel is first-order by construction
   ═══════════════════════════════════════════════════════════════════ *)

Definition mrun_c_type : Type := nat -> cfg -> dres.

Example mrun_c_closure_free : mrun_c_type := mrun_c.

Check step_c.          (* cfg -> out *)
Check enter_case_c.    (* tail loop over branches: guard, then match_any_iter *)
Check mrun_c.          (* nat -> cfg -> dres: no functional argument *)
Check no_sat.          (* Prop over the machine's own path: the completeness key *)
