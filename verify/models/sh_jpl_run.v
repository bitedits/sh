(* sh_jpl_run.v

 * JPL-compliant small-step machine (Phase 3d-C / JPL.3).

 * sh_concrete.v is the single source of truth, but its `run` is fuel-bounded
 * recursion over heap lists with a higher-order `obind`/`phi` callback.  A
 * literal emit of that to C99 needs recursion, malloc and captured-environment
 * function pointers, each of which breaks a mandatory canonical JPL PowerPC C
 * rule.  This file re-aims the SAME observable semantics to an iterative
 * control machine: a non-recursive `step` dispatcher over an explicit,
 * bounded continuation stack, driven by a fuel-bounded tail loop `mloop`.  The
 * machine is a companion to sh_concrete.v, not a replacement — it never edits
 * or duplicates `run`; instead it is PROVEN to agree with `run`.

 * Correctness contract (this file):
 *   - `cont_run` interprets the data stack as the concrete `run`/`run_seq`/
 *     `run_for`/`run_case` continuations it stands for (the specification).
 *   - `cfg_run phi g` is the meaning of a whole machine configuration.
 *   - `step_preserves`: one machine step never changes the configuration's
 *     meaning.  From this, `mloop` is SOUND: whenever it returns BOk st, that
 *     st is exactly what `run` computes for the starting configuration; and a
 *     configuration `run` rejects (None) can never be turned into BOk.
 *   - The extracted C is the `phi`-as-DATA shape: at an external-command leaf
 *     `step` returns `Oeffect idx argv k st` (a data value, not a callback),
 *     which the host services between steps.  `mloop` here folds `phi` back in
 *     at the effect sites purely so the equivalence to `run` can be stated.

 * Scope note (JPL.md): this file delivers the control-flow machine, the
 * specification, and FULL soundness over the entire control surface
 * (Skip/Ext/Assign/Seq/And/Or/Bang/If/While/For/Case).  The liveness half — a
 * well-founded step budget that makes mloop reach the sound answer for every
 * input run accepts, turning soundness into a two-sided iff — is proved in the
 * companion module sh_jpl_run_phase2.v (JPL.3b), which imports this file and
 * adds ONLY the termination argument plus mrun_live / mloop_iff /
 * mloop_sound_complete.  Making the scan helpers (expand/glob) themselves
 * iterative remains follow-on work for the extraction (JPL.4); the 26
 * extraction-parity checks and the /bin-sh conformance corpus are the empirical
 * net for that surface.

 * Build (Rocq >= 9.0):
 *   coqc sh_jpl_run.v
 *   coqchk -o -silent sh_jpl_run   # must report Axioms: <none>
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.
Import ListNotations.

Require Import sh_concrete.   (* the reference semantics run/... *)
Require Import sh_jpl.        (* the bounded layer: bres/BOk/BLimit *)

Set Warnings "-register-all".

(* ═══════════════════════════════════════════════════════════════════
   §1  Machine state: frames, stack, configuration, step output

   A frame is a *data* continuation: it carries the concrete-matching semantic
   fuel f (the f' that run used when it descended into the child that is now
   finishing) plus the sibling/payload the concrete node needs.  The stack is a
   plain list whose head is the innermost continuation.  No frame is a closure.
   ═══════════════════════════════════════════════════════════════════ *)

Inductive frame : Type :=
  | FSeq       : nat -> cmd -> frame                    (* after c1 of Seq c1 c2 *)
  | FAnd       : nat -> cmd -> frame                    (* after c1 of And c1 c2 *)
  | FOr        : nat -> cmd -> frame                    (* after c1 of Or c1 c2 *)
  | FBang      : frame                                  (* after inner of Bang c *)
  | FIf        : nat -> cmd -> cmd -> frame             (* after cond of If *)
  | FWhile     : nat -> cmd -> cmd -> frame             (* after the loop test *)
  | FWhileBody : nat -> cmd -> cmd -> frame             (* after the loop body *)
  | FSeqList   : nat -> list cmd -> frame               (* run_seq over a body list *)
  | FForRest   : nat -> text -> list text -> list cmd -> frame (* run_for over the rest words *)
  .

Definition stack := list frame.

(* A configuration is (fuel for the pending command, optional pending command,
   continuation stack, current state).  cc = Some c means "about to run c at
   fuel cf"; cc = None means "the command just finished, its result state is
   cs; now apply the stack." *)
Record cfg : Type := CFG { cf : nat ; cc : option cmd ; ck : stack ; cs : cstate }.

(* The step output.  Oeffect is the phi seam AS DATA (the JPL shape): the
   machine hands back (idx, argv, stack, state) and the host services it. *)
Inductive out : Type :=
  | Onext   : cfg -> out
  | Oeffect : nat -> list text -> stack -> cstate -> out
  | Odone   : cstate -> out
  | Olimit  : out.

(* status-is-zero test, shared by the machine and the specification so they are
   syntactically identical (lets step_preserves close by reflexivity). *)
Definition isz (s : cstate) : bool := Nat.eqb (cstatus s) 0.

(* ═══════════════════════════════════════════════════════════════════
   §2  Entering a list/for/case run (mirrors run_seq / run_for / run_case)

   Each is a single non-recursive dispatch: it consumes the fuel head, then
   either produces a value, hands off the first element, or (for case) re-enters
   via a re-dispatched pending Case node so the branch scan is one driver
   iteration per branch rather than step self-recursion.
   ═══════════════════════════════════════════════════════════════════ *)

(* enter_seq h l s k  ~  run_seq phi h l s, continuation k *)
Definition enter_seq (h : nat) (l : list cmd) (s : cstate) (k : stack) : out :=
  match h with
  | 0 => Olimit
  | S g =>
      match l with
      | [] => Onext (CFG 0 None k (CS 0 (cenv s)))
      | [c] => Onext (CFG g (Some c) k s)
      | c :: r => Onext (CFG g (Some c) (FSeqList g r :: k) s)
      end
  end.

(* binding a for-loop word to the variable, expanding at fuel g *)
Definition bind_word (g : nat) (var : text) (w : text) (s : cstate) : cstate :=
  CS (cstatus s) (setv var (expand g (cenv s) (cstatus s) w) (cenv s)).

(* enter_for h var ws body s k  ~  run_for phi h var ws body s, continuation k *)
Definition enter_for (h : nat) (var : text) (ws : list text) (body : list cmd) (s : cstate) (k : stack) : out :=
  match h with
  | 0 => Olimit
  | S g =>
      match ws with
      | [] => Onext (CFG 0 None k (CS 0 (cenv s)))
      | [w] => enter_seq g body (bind_word g var w s) k
      | w :: w2 :: r => enter_seq g body (bind_word g var w s) (FForRest g var (w2 :: r) body :: k)
      end
  end.

(* enter_case h scrut brs s k  ~  run_case phi h scrut brs s, continuation k.
   The no-match branch re-enters enter_case at fuel g in TAIL position, so the
   branch scan is a bounded loop (extracts to a C `while`), not step
   self-recursion and not a stack frame — there is no command to run between
   successive branch tests, so the driver has nothing to pop. *)
Fixpoint enter_case (h : nat) (scrut : text) (brs : list (list text * list cmd)) (s : cstate) (k : stack) : out :=
  match h with
  | 0 => Olimit
  | S g =>
      match brs with
      | [] => Onext (CFG 0 None k (CS 0 (cenv s)))
      | (pats, body) :: r =>
          if match_any g pats (expand g (cenv s) (cstatus s) scrut)
          then enter_seq g body s k
          else enter_case g scrut r s k
      end
  end.

(* ═══════════════════════════════════════════════════════════════════
   §3  The step dispatcher (non-recursive)

   step_cmd decomposes the pending command; step_ret feeds a finished value
   back through the top continuation frame.  step is the choice between them.
   Atomic commands (Skip/Ext/Assign) run at every fuel level; compound commands
   at fuel 0 saturate (Olimit), matching run's None.
   ═══════════════════════════════════════════════════════════════════ *)

Definition step_cmd (f : nat) (c : cmd) (k : stack) (s : cstate) : out :=
  match f with
  | 0 =>
      match c with
      | Skip => Onext (CFG 0 None k s)
      | Ext idx argv => Oeffect idx argv k s
      | Assign k' v => Onext (CFG 0 None k (CS 0 (setv k' v (cenv s))))
      | _ => Olimit
      end
  | S f' =>
      match c with
      | Skip => Onext (CFG 0 None k s)
      | Ext idx argv => Oeffect idx argv k s
      | Assign k' v => Onext (CFG 0 None k (CS 0 (setv k' v (cenv s))))
      | Bang c0 => Onext (CFG f' (Some c0) (FBang :: k) s)
      | Seq c1 c2 => Onext (CFG f' (Some c1) (FSeq f' c2 :: k) s)
      | And c1 c2 => Onext (CFG f' (Some c1) (FAnd f' c2 :: k) s)
      | Or c1 c2 => Onext (CFG f' (Some c1) (FOr f' c2 :: k) s)
      | If cond t e => Onext (CFG f' (Some cond) (FIf f' t e :: k) s)
      | While cond body => Onext (CFG f' (Some cond) (FWhile f' cond body :: k) s)
      | For var ws body => enter_for f' var ws body s k
      | Case scrut brs => enter_case f' scrut brs s k
      end
  end.

Definition step_ret (k : stack) (s : cstate) : out :=
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
      | FForRest f var rws body => enter_for f var rws body s r
      end
  end.

Definition step (g : cfg) : out :=
  match cc g with
  | Some c => step_cmd (cf g) c (ck g) (cs g)
  | None => step_ret (ck g) (cs g)
  end.

(* ═══════════════════════════════════════════════════════════════════
   §4  The fuel-bounded tail driver

   mloop iterates step, decrementing the independent step budget B.  On an
   Oeffect it services the seam with phi (the extraction-time host loop does
   this with the real fork/exec instead); on Odone it yields the final state; a
   budget or seam exhaustion yields the defined BLimit.  The recursive call is
   in tail position, so this extracts to a C `while (B--) { ... }`.
   ═══════════════════════════════════════════════════════════════════ *)

Fixpoint mloop (phi : run_phi) (B : nat) (g : cfg) : bres cstate :=
  match B with
  | 0 => BLimit
  | S B' =>
      match step g with
      | Onext g' => mloop phi B' g'
      | Oeffect idx argv k s =>
          match phi idx argv s with
          | Some s' => mloop phi B' (CFG 0 None k s')
          | None => BLimit
          end
      | Odone st => BOk st
      | Olimit => BLimit
      end
  end.

(* inject the concrete option-result into the bounded result carrier, so the
   equivalence can be phrased against run's own None (= saturate) outcome. *)
Definition b_of (o : option cstate) : bres cstate :=
  match o with
  | Some s => BOk s
  | None => BLimit
  end.

(* ═══════════════════════════════════════════════════════════════════
   §5  The specification: reading the data stack as concrete continuations

   frame_run applies one frame to the incoming result value; cont_run folds the
   whole stack; cfg_run is the meaning of a configuration.  These use the
   concrete run/run_seq/run_for/run_case directly, so the specification IS the
   single source of truth rather than a second encoding.
   ═══════════════════════════════════════════════════════════════════ *)

Definition frame_run (phi : run_phi) (fr : frame) (ov : option cstate) : option cstate :=
  match fr with
  | FSeq f c2 => obind ov (run phi f c2)
  | FAnd f c2 => obind ov (fun s1 => if isz s1 then run phi f c2 s1 else Some s1)
  | FOr f c2 => obind ov (fun s1 => if isz s1 then Some s1 else run phi f c2 s1)
  | FBang => obind ov (fun s1 => Some (CS (bstat (cstatus s1)) (cenv s1)))
  | FIf f t e => obind ov (fun sc => if isz sc then run phi f t sc else run phi f e sc)
  | FWhile f cnd bdy =>
      obind ov (fun sc => if isz sc then obind (run phi f bdy sc) (run phi f (While cnd bdy)) else Some sc)
  | FWhileBody f cnd bdy => obind ov (fun sbb => run phi f (While cnd bdy) sbb)
  | FSeqList f l => obind ov (run_seq phi f l)
  | FForRest f var rws body => obind ov (run_for phi f var rws body)
  end.

Fixpoint cont_run (phi : run_phi) (k : stack) (ov : option cstate) : option cstate :=
  match k with
  | [] => ov
  | fr :: r => cont_run phi r (frame_run phi fr ov)
  end.

Definition cfg_run (phi : run_phi) (g : cfg) : option cstate :=
  match cc g with
  | Some c => cont_run phi (ck g) (run phi (cf g) c (cs g))
  | None => cont_run phi (ck g) (Some (cs g))
  end.

(* meaning of a step output *)
Definition out_run (phi : run_phi) (o : out) : option cstate :=
  match o with
  | Onext g' => cfg_run phi g'
  | Oeffect idx argv k s => cont_run phi k (phi idx argv s)
  | Odone st => Some st
  | Olimit => None
  end.

(* ═══════════════════════════════════════════════════════════════════
   §6  Step preserves meaning — the soundness core

   Every frame_run wraps its input with obind, so None propagates to None; that
   is the one lemma the fuel-0 saturating cases need.  Everything else closes by
   computation because the machine and the specification are built from the same
   status test and the same fuel threading.
   ═══════════════════════════════════════════════════════════════════ *)

Lemma frame_run_none : forall phi fr, frame_run phi fr None = None.
Proof.
  intros phi fr. unfold frame_run. destruct fr; reflexivity.
Qed.

Lemma cont_run_none : forall phi k, cont_run phi k None = None.
Proof.
  intros phi k. induction k as [ | fr r IH ]; [ reflexivity | ].
  unfold cont_run. rewrite frame_run_none. exact IH.
Qed.

Lemma out_run_enter_seq : forall phi h l s r,
  out_run phi (enter_seq h l s r) = cont_run phi r (run_seq phi h l s).
Proof.
  intros phi h l s r. destruct h as [ | g ]; destruct l as [ | c l' ].
  - (* h = 0, l = [] *) simpl. rewrite cont_run_none. reflexivity.
  - (* h = 0, l = c :: _ *) simpl. rewrite cont_run_none. reflexivity.
  - (* h = S g, l = [] *) reflexivity.
  - (* h = S g, l = c :: l' *) destruct l' as [ | c2 l'']; reflexivity.
Qed.

Lemma out_run_enter_for : forall phi h var ws body s r,
  out_run phi (enter_for h var ws body s r) = cont_run phi r (run_for phi h var ws body s).
Proof.
  intros phi h var ws body s r. destruct h as [ | g ]; destruct ws as [ | w ws' ].
  - (* h = 0, ws = [] *) simpl. rewrite cont_run_none. reflexivity.
  - (* h = 0, ws = _ :: _ *) simpl. rewrite cont_run_none. reflexivity.
  - (* h = S g, ws = [] *) reflexivity.
  - (* h = S g, ws = w :: ws' *)
    destruct ws' as [ | w2 r' ]; cbn [enter_for].
    + rewrite out_run_enter_seq. reflexivity.
    + rewrite out_run_enter_seq. reflexivity.
Qed.

Lemma out_run_enter_case : forall phi h scrut brs s r,
  out_run phi (enter_case h scrut brs s r) = cont_run phi r (run_case phi h scrut brs s).
Proof.
  intros phi h. induction h as [ | g IH ]; intros scrut brs s r.
  - (* h = 0 *) simpl. rewrite cont_run_none. reflexivity.
  - (* h = S g *) destruct brs as [ | pb brs' ].
    + (* no branches *) reflexivity.
    + destruct pb as [pats body].
      cbn [enter_case run_case].
      destruct (match_any g pats (expand g (cenv s) (cstatus s) scrut)).
      * apply out_run_enter_seq.
      * apply IH.
Qed.

Lemma step_cmd_preserves : forall phi f c k s,
  out_run phi (step_cmd f c k s) = cont_run phi k (run phi f c s).
Proof.
  intros phi f c k s. destruct f as [ | f' ]; destruct c;
    cbn [step_cmd run out_run cfg_run cont_run frame_run obind];
    try (rewrite out_run_enter_for); try (rewrite out_run_enter_case);
    try (rewrite cont_run_none); reflexivity.
Qed.

Lemma step_ret_preserves : forall phi k s,
  out_run phi (step_ret k s) = cont_run phi k (Some s).
Proof.
  intros phi k s. destruct k as [ | fr r ].
  - cbn [step_ret out_run cfg_run cont_run]. reflexivity.
  - destruct fr;
      cbn [step_ret out_run cfg_run cont_run frame_run obind run];
      try (destruct (isz s));
      try (rewrite out_run_enter_seq); try (rewrite out_run_enter_for);
      reflexivity.
Qed.

Lemma step_preserves : forall phi g, out_run phi (step g) = cfg_run phi g.
Proof.
  intros phi g. destruct g as [f co k s]. cbn [step cfg_run].
  destruct co as [c | ].
  - apply step_cmd_preserves.
  - apply step_ret_preserves.
Qed.

(* mloop never computes a wrong answer: whatever it returns as BOk is exactly
   what cfg_run says the starting configuration means. *)
Theorem mrun_sound : forall phi B g st,
  mloop phi B g = BOk st -> cfg_run phi g = Some st.
Proof.
  intros phi B. induction B as [ | B' IH ]; intros g st H.
  - simpl in H. discriminate.
  - simpl in H.
    destruct (step g) as [g' | idx argv k s | st2 | ] eqn:Es; simpl in H.
    + (* Onext g' *) apply IH in H. rewrite <- step_preserves, Es. exact H.
    + (* Oeffect *) destruct (phi idx argv s) as [s' |] eqn:Ep; [| discriminate H].
      apply IH in H. unfold cfg_run in H. cbn in H.
      rewrite <- step_preserves, Es. unfold out_run. cbn. rewrite Ep. exact H.
    + (* Odone *) injection H as <-. rewrite <- step_preserves, Es. reflexivity.
    + (* Olimit *) discriminate H.
Qed.

(* Initial-configuration corollary, stated against concrete `run`. *)
Theorem mrun_correct : forall phi B F c s st,
  mloop phi B (CFG F (Some c) [] s) = BOk st -> run phi F c s = Some st.
Proof.
  intros phi B F c s st H.
  pose proof (mrun_sound phi B (CFG F (Some c) [] s) st H) as S.
  unfold cfg_run, cont_run in S. cbn in S. exact S.
Qed.

(* A configuration run rejects can never be turned into a success by the machine. *)
Theorem run_none_mloop_limit : forall phi B F c s,
  run phi F c s = None ->
  forall st, mloop phi B (CFG F (Some c) [] s) <> BOk st.
Proof.
  intros phi B F c s Hr st Heq.
  apply mrun_correct in Heq. rewrite Hr in Heq. discriminate.
Qed.

(* ═══════════════════════════════════════════════════════════════════
   §7  The §7 boundary facts, reproduced by the machine (pure_phi)

   Each machine run below is a closed computation whose result equals the
   concrete `run` fact already verified in sh_concrete §7 — so the machine is
   checked against the single source of truth on the conformance surface, not a
   parallel re-derivation of it.
   ═══════════════════════════════════════════════════════════════════ *)

Definition pure_run_phi : run_phi := pure_phi.

(* && with a failing left operand short-circuits: right never runs. *)
Example mach_and_left_false_stops :
  mloop pure_run_phi 5 (CFG (S 3) (Some (And (Ext 0 [false_w]) (Ext 0 [true_w]))) [] (CS 7 []))
  = BOk (CS 1 []).
Proof. reflexivity. Qed.

(* || with a succeeding left operand short-circuits. *)
Example mach_or_left_true_stops :
  mloop pure_run_phi 5 (CFG (S 3) (Some (Or (Ext 0 [true_w]) (Ext 0 [false_w]))) [] (CS 7 []))
  = BOk (CS 0 []).
Proof. reflexivity. Qed.

(* ; is right-sequential: the pair's status is the last command's. *)
Example mach_seq_right_status :
  mloop pure_run_phi 8 (CFG (S 3) (Some (Seq (Ext 0 [true_w]) (Ext 0 [false_w]))) [] (CS 7 []))
  = BOk (CS 1 []).
Proof. reflexivity. Qed.

(* ! inverts a failing status to zero. *)
Example mach_bang_false :
  mloop pure_run_phi 5 (CFG (S 3) (Some (Bang (Ext 0 [false_w]))) [] (CS 7 []))
  = BOk (CS 0 []).
Proof. reflexivity. Qed.

(* if runs the then-branch on a succeeding test. *)
Example mach_if_true :
  mloop pure_run_phi 6 (CFG (S 3) (Some (If (Ext 0 [true_w]) (Ext 0 [false_w]) (Ext 0 [true_w]))) [] (CS 7 []))
  = BOk (CS 1 []).
Proof. reflexivity. Qed.

(* while with an immediately-failing test runs its body zero times. *)
Example mach_while_false_zero :
  mloop pure_run_phi 5 (CFG (S 3) (Some (While (Ext 0 [false_w]) (Ext 0 [true_w]))) [] (CS 7 []))
  = BOk (CS 1 []).
Proof. reflexivity. Qed.

(* an assignment binds its value, and the machine reads it back like §7. *)
Example mach_assign_binds :
  match mloop pure_run_phi 3 (CFG (S 3) (Some (Assign [97] [98])) [] (CS 7 [])) with
  | BOk s => getv [97] (cenv s)
  | BLimit => None
  end
  = Some [98].
Proof. reflexivity. Qed.

(* the machine and concrete run agree on the §7 surface for the pure seam. *)
Example mach_eq_run_and :
  mloop pure_run_phi 5 (CFG (S 3) (Some (And (Ext 0 [false_w]) (Ext 0 [true_w]))) [] (CS 7 []))
  = b_of (run pure_run_phi (S 3) (And (Ext 0 [false_w]) (Ext 0 [true_w])) (CS 7 [])).
Proof.
  unfold b_of. reflexivity.
Qed.
