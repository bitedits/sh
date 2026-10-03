(* scratch: JPL.3b completeness development, to be appended to sh_jpl_run.v *)
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.
Import ListNotations.

Require Import sh_concrete.
Require Import sh_jpl.
Require Import sh_jpl_run.

Set Warnings "-register-all".

(* ── step-count bound over the concrete run group ───────────────── *)

Fixpoint step_cnt (f : nat) (c : cmd) : nat :=
  match f with
  | 0 =>
      match c with
      | Skip => 2 | Ext _ _ => 3 | Assign _ _ => 2 | _ => 1
      end
  | S g =>
      match c with
      | Skip => 2
      | Ext _ _ => 3
      | Assign _ _ => 2
      | Bang c0 => 3 + step_cnt g c0
      | Seq c1 c2 => 3 + step_cnt g c1 + step_cnt g c2
      | And c1 c2 => 3 + step_cnt g c1 + step_cnt g c2
      | Or c1 c2 => 3 + step_cnt g c1 + step_cnt g c2
      | If cond t e => 3 + step_cnt g cond + step_cnt g t + step_cnt g e
      | While cnd bdy => 4 + step_cnt g cnd + step_cnt g bdy + step_cnt g (While cnd bdy)
      | For var ws body => 3 + step_cnt_for g var ws body + step_cnt_seq g body
      | Case scrut brs => 3 + step_cnt_case g brs
      end
  end

with step_cnt_seq (f : nat) (l : list cmd) : nat :=
  match f with
  | 0 => 1
  | S g => match l with
           | [] => 1
           | [c] => 2 + step_cnt g c
           | c :: r => 3 + step_cnt g c + step_cnt_seq g r
           end
  end

with step_cnt_for (f : nat) (var : text) (ws : list text) (body : list cmd) : nat :=
  match f with
  | 0 => 1
  | S g => match ws with
           | [] => 1
           | [w] => 2 + step_cnt_seq g body
           | w :: w2 :: r => 3 + step_cnt_seq g body + step_cnt_for g var (w2 :: r) body
           end
  end

with step_cnt_case (f : nat) (brs : list (list text * list cmd)) : nat :=
  match f with
  | 0 => 1
  | S g => match brs with
           | [] => 1
           | (_pats, body) :: r => 3 + step_cnt_seq g body + step_cnt_case g r
           end
  end.

Definition frame_cnt (fr : frame) : nat :=
  match fr with
  | FSeq f c => 2 + step_cnt f c
  | FAnd f c => 2 + step_cnt f c
  | FOr f c => 2 + step_cnt f c
  | FBang => 2
  | FIf f t e => 2 + step_cnt f t + step_cnt f e
  | FWhile f cnd bdy => 3 + step_cnt f bdy + step_cnt f (While cnd bdy)
  | FWhileBody f cnd bdy => 2 + step_cnt f (While cnd bdy)
  | FSeqList f l => 2 + step_cnt_seq f l
  | FForRest f var ws body => 2 + step_cnt_for f var ws body
  end.

Fixpoint stack_cnt (k : stack) : nat :=
  match k with
  | [] => 2
  | fr :: r => frame_cnt fr + stack_cnt r
  end.

Definition budget (g : cfg) : nat :=
  match cc g with
  | Some c => S (step_cnt (cf g) c + stack_cnt (ck g))
  | None => S (stack_cnt (ck g))
  end.

(* budget of what a step output still owes: the Onext config's budget, or, for an
   Oeffect, the pop of the stack the host re-enters at (one extra step for the
   seam service).  Odone/Olimit owe nothing. *)
Definition out_budget (o : out) : nat :=
  match o with
  | Onext g => budget g
  | Oeffect _ _ k _ => S (stack_cnt k)
  | Odone _ => 0
  | Olimit => 0
  end.

Lemma budget_pos : forall g, 0 < budget g.
Proof.
  intros g. destruct g as [f co k s]. cbn [budget]. destruct co; lia.
Qed.

(* ── the enter_* dispatches stay within their charge ────────────── *)

Lemma budget_enter_seq : forall h l s k,
  S (out_budget (enter_seq h l s k)) <= S (step_cnt_seq h l + stack_cnt k).
Proof.
  intros h l s k. destruct h as [ | g ]; [ cbn [enter_seq out_budget]; lia | ].
  destruct l as [ | c l' ].
  - cbn [enter_seq out_budget budget cf cc ck cs stack_cnt frame_cnt step_cnt_seq step_cnt]. lia.
  - destruct l' as [ | c2 l'' ].
    + cbn [enter_seq out_budget budget cf cc ck cs stack_cnt frame_cnt step_cnt_seq step_cnt]. lia.
    + cbn [enter_seq out_budget budget cf cc ck cs stack_cnt frame_cnt
           step_cnt_seq step_cnt]. lia.
Qed.

Lemma budget_enter_for : forall h var ws body s k,
  S (out_budget (enter_for h var ws body s k))
  <= S (step_cnt_for h var ws body + stack_cnt k).
Proof.
  intros h var ws body s k. destruct h as [ | g ]; [ cbn [enter_for out_budget]; lia | ].
  destruct ws as [ | w ws' ].
  - cbn [enter_for out_budget budget cf cc ck cs stack_cnt frame_cnt step_cnt_for step_cnt_seq]. lia.
  - destruct ws' as [ | w2 r ].
    + assert (H := budget_enter_seq g body (bind_word g var w s) k).
      cbn [enter_for out_budget budget cf cc ck cs stack_cnt frame_cnt
           step_cnt_for step_cnt_seq]. lia.
    + assert (H := budget_enter_seq g body (bind_word g var w s)
                   (FForRest g var (w2 :: r) body :: k)).
      cbn [enter_for out_budget budget cf cc ck cs stack_cnt frame_cnt
           step_cnt_for step_cnt_seq]. lia.
Qed.

Lemma budget_enter_case : forall h scrut brs s k,
  S (out_budget (enter_case h scrut brs s k)) <= S (step_cnt_case h brs + stack_cnt k).
Proof.
  induction h as [ | g IH ]; intros scrut brs s k.
  - cbn [enter_case out_budget]. lia.
  - destruct brs as [ | pb brs' ].
    + cbn [enter_case out_budget budget cf cc ck cs stack_cnt frame_cnt
           step_cnt_case step_cnt_seq]. lia.
    + destruct pb as [pats body].
      destruct (match_any g pats (expand g (cenv s) (cstatus s) scrut)).
      * assert (H := budget_enter_seq g body s k).
        cbn [enter_case out_budget budget cf cc ck cs stack_cnt frame_cnt
             step_cnt_case step_cnt_seq]. lia.
      * assert (H := IH scrut brs' s k).
        cbn [enter_case out_budget budget cf cc ck cs stack_cnt frame_cnt
             step_cnt_case step_cnt_seq]. lia.
Qed.

(* ── one driver step costs at least one unit of budget ──────────── *)

Lemma budget_step_cmd : forall f c k s,
  S (out_budget (step_cmd f c k s)) <= budget (CFG f c k s).
Proof.
  intros f c k s. destruct f as [ | g ]; destruct c as
    [ | idx argv | k' v | c1 c2 | c1 c2 | c1 c2 | c0 | cond t e | cnd bdy | var ws body | scrut brs ];
    cbn [step_cmd out_budget budget cf cc ck cs stack_cnt frame_cnt
         step_cnt step_cnt_seq step_cnt_for step_cnt_case].
  - lia. lia. lia. lia. lia. lia. lia. lia. lia. lia. lia.
  - lia. lia. lia. lia. lia. lia. lia. lia. lia.
  - assert (H := budget_enter_for g var ws body s k). lia.
  - assert (H := budget_enter_case g scrut brs s k). lia.
Qed.

Lemma budget_step_ret : forall k s,
  S (out_budget (step_ret k s)) <= budget (CFG 0 None k s).
Proof.
  intros k s. destruct k as [ | fr r ].
  - cbn [step_ret out_budget budget cf cc ck cs stack_cnt]. lia.
  - destruct fr as [ f c | f c | f c | | f t e | f cnd bdy | f cnd bdy | f l | f var ws body ];
      cbn [step_ret out_budget budget cf cc ck cs stack_cnt frame_cnt
           step_cnt step_cnt_seq step_cnt_for step_cnt_case].
    + lia.
    + destruct (isz s); cbn; lia.
    + destruct (isz s); cbn; lia.
    + lia.
    + destruct (isz s); cbn; lia.
    + destruct (isz s); cbn; lia.
    + lia.
    + assert (H := budget_enter_seq f l s r). lia.
    + assert (H := budget_enter_for f var ws body s r). lia.
Qed.

Lemma budget_step : forall g,
  S (out_budget (step g)) <= budget g.
Proof.
  intros g. destruct g as [f co k s]. cbn [step].
  destruct co as [c | ].
  - apply budget_step_cmd.
  - apply budget_step_ret.
Qed.

(* ── completeness ──────────────────────────────────────────────── *)

Theorem mrun_complete : forall phi B g st,
  budget g <= B -> cfg_run phi g = Some st -> mloop phi B g = BOk st.
Proof.
  intros phi B. induction B as [ | B' IH ]; intros g st Hb Hrun.
  - assert (Hp : 0 < budget g) by apply budget_pos. lia.
  - assert (Hpre : out_run phi (step g) = Some st).
    { rewrite <- step_preserves. exact Hrun. }
    assert (Hbd : S (out_budget (step g)) <= budget g) by apply budget_step.
    cbn [mloop].
    destruct (step g) as [g' | idx argv k0 s0 | st2 | ] eqn:Es;
      cbn [out_run cfg_run cf cc ck cs] in Hpre; cbn [out_budget budget cf cc ck cs] in Hbd;
      simpl in Hb.
    + apply IH; lia.
    + destruct (phi idx argv s0) as [s1 | ] eqn:Ep; [ | discriminate].
      apply IH; [ lia | ].
      cbn [cfg_run cc cf ck cs] in Hpre. exact Hpre.
    + injection Hpre as Hst. subst st2. reflexivity.
    + discriminate.
Qed.

Theorem mrun_iff : forall phi B F c s st,
  budget (CFG F (Some c) [] s) <= B ->
  mloop phi B (CFG F (Some c) [] s) = BOk st <-> run phi F c s = Some st.
Proof.
  intros phi B F c s st Hb. split.
  - intros H. apply mrun_correct in H. exact H.
  - intros H. apply (mrun_complete phi B (CFG F (Some c) [] s) st); [ exact Hb | ].
    unfold cfg_run. cbn [cc ck cf cs]. exact H.
Qed.

Example budget_skip : budget (CFG 0 (Some Skip) [] (CS 0 [])) = 4.
Proof. reflexivity. Qed.

Example budget_seq_ext :
  budget (CFG 3 (Some (Seq (Ext 0 [true_w]) (Ext 0 [false_w]))) [] (CS 7 [])) = 14.
Proof. reflexivity. Qed.
