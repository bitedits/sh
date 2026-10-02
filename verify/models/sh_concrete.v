(* sh_concrete.v
 *
 * Concrete POSIX shell semantics: the Coq model that becomes the single source
 * of truth for the extracted C99 shell.  Where sh_properties.v abstracts a
 * command to a nat status and a nat-keyed environment, this file models the
 * things the real shell touches — words (text), a name->value environment, an
 * external-command status oracle, and the same control operators (; && || ! if
 * while).  It is still relational-free and axiom-free: every command has a
 * decidable, fuel-bounded functional reading `run`, so the whole file compiles
 * through the kernel with no Axiom and no Parameter.
 *
 * Design notes carried into the extraction (Phase 3c/3d):
 *  - text is list ascii, NOT Coq's string, because list extracts to an OCaml
 *    list and a C pointer array while Coq string drags in list_ofascii; the
 *    extraction maps this type to OCaml string / C char*.
 *  - the external-command status is modelled as DATA (a total function on the
 *    command name), not as an effectful oracle: "true"->0, "false"->1, anything
 *    else->127 (command-not-found).  This keeps the model pure; the C shim
 *    replaces the constant arms with the real fork/execvp status at the seam.
 *
 * Build (Rocq >= 9.0):
 *   coqc sh_concrete.v
 *   coqchk -o -silent sh_concrete    # must report Axioms: <none>
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Ascii.
Import ListNotations.

(* ═══════════════════════════════════════════════════════════════════
   §1  Text: shell words as lists of byte codes
   ═══════════════════════════════════════════════════════════════════ *)

(* A word is a list of byte codes (each intended to be < 256).  Using nat rather
   than Coq's ascii keeps decidable equality trivial to reason about; the
   extraction maps list nat to OCaml string / C char* in Phase 3c. *)
Definition text := list nat.

(* byte-ordered equality on text, decidable and computable *)
Fixpoint teqb (s1 s2 : text) : bool :=
  match s1, s2 with
  | [], [] => true
  | [], _ => false
  | _, [] => false
  | a1 :: r1, a2 :: r2 => if Nat.eqb a1 a2 then teqb r1 r2 else false
  end.

Lemma teqb_refl : forall s, teqb s s = true.
Proof.
  induction s as [ | a s IH ]; simpl.
  - reflexivity.
  - rewrite Nat.eqb_refl. exact IH.
Qed.

Lemma teqb_true_eq : forall s1 s2, teqb s1 s2 = true -> s1 = s2.
Proof.
  induction s1 as [ | a r1 IH ]; intros s2 H; simpl in H.
  - destruct s2; simpl in H; [ reflexivity | discriminate ].
  - destruct s2 as [ | b r2]; [ discriminate | ].
    simpl in H. destruct (Nat.eqb a b) eqn:Eb; [| discriminate H].
    apply Nat.eqb_eq in Eb. subst b.
    f_equal. exact (IH r2 H).
Qed.

Lemma teqb_false_neq : forall s1 s2, teqb s1 s2 = false -> s1 <> s2.
Proof.
  intros s1 s2 H Heq. subst s2.
  rewrite teqb_refl in H. discriminate.
Qed.

Lemma teqb_neq_false : forall s1 s2, s1 <> s2 -> teqb s1 s2 = false.
Proof.
  intros s1 s2 Hne.
  destruct (teqb s1 s2) eqn:E; [ | reflexivity ].
  exfalso. apply Hne. apply teqb_true_eq; exact E.
Qed.

(* ═══════════════════════════════════════════════════════════════════
   §2  State: an 8-bit status plus a name -> value environment
   ═══════════════════════════════════════════════════════════════════ *)

(* POSIX truncates exit status to the low 8 bits. *)
Definition nstat (k : nat) : nat := k mod 256.

Lemma nstat_lt : forall k, nstat k < 256.
Proof. unfold nstat. intros k. apply Nat.mod_upper_bound. lia. Qed.

Lemma nstat_small : forall k, k < 256 -> nstat k = k.
Proof. unfold nstat. intros k Hk. apply Nat.mod_small. exact Hk. Qed.

(* ! inverts a status: zero becomes 1, anything else becomes 0 (POSIX 2.11.3). *)
Definition bstat (n : nat) : nat := if Nat.eqb n 0 then 1 else 0.

Record cstate : Type := CS { cstatus : nat ; cenv : list (text * text) }.

(* environment lookup / update, keyed by text via teqb *)
Fixpoint getv (k : text) (m : list (text * text)) : option text :=
  match m with
  | [] => None
  | (k', v) :: r => if teqb k k' then Some v else getv k r
  end.

Fixpoint setv (k v : text) (m : list (text * text)) : list (text * text) :=
  match m with
  | [] => [(k, v)]
  | (k', v') :: r =>
      if teqb k k' then (k, v) :: r else (k', v') :: setv k v r
  end.

Lemma getv_set_same : forall m k v, getv k (setv k v m) = Some v.
Proof.
  induction m as [ | [k' v'] m IH ]; intros k v.
  - cbn [setv getv]. destruct (teqb k k) eqn:E; [ reflexivity | ].
    exfalso. apply (teqb_false_neq k k E). reflexivity.
  - destruct (teqb k k') eqn:E.
    + apply teqb_true_eq in E. subst k'.
      cbn [setv]. rewrite teqb_refl. cbn [getv]. rewrite teqb_refl. reflexivity.
    + cbn [setv]. rewrite E. cbn [getv]. rewrite E. apply IH.
Qed.

Lemma getv_set_other :
  forall m k k2 v, teqb k2 k = false -> getv k2 (setv k v m) = getv k2 m.
Proof.
  induction m as [ | [k' v'] m IH ]; intros k k2 v Hind.
  - cbn [setv getv]. destruct (teqb k2 k); [ discriminate | reflexivity ].
  - cbn [setv]. destruct (teqb k k') eqn:Ek.
    + apply teqb_true_eq in Ek. subst k'. cbn [getv]. rewrite Hind. reflexivity.
    + cbn [getv]. destruct (teqb k2 k'); [ reflexivity | apply IH; exact Hind ].
Qed.

(* ═══════════════════════════════════════════════════════════════════
   §3  External-command status as DATA (no effect, no axiom)
   ═══════════════════════════════════════════════════════════════════ *)

(* "true" and "false" as ASCII byte codes. *)
Definition true_w : text := [116; 114; 117; 101].
Definition false_w : text := [102; 97; 108; 115; 101].

(* The status a bare external command yields.  Verified model keeps this pure:
   recognised builtins map to their codes, an unknown command is 127.  The C
   extraction replaces these constant arms with the wait status of the real
   fork/execvp at the single command seam. *)
Definition ex_status (name : text) : nat :=
  if teqb name true_w then 0
  else if teqb name false_w then 1
  else 127.

Lemma ex_status_true : ex_status true_w = 0.
Proof. unfold ex_status. rewrite teqb_refl. reflexivity. Qed.

Lemma ex_status_false : ex_status false_w = 1.
Proof.
  unfold ex_status.
  assert (Ht : teqb false_w true_w = false).
  { simpl. destruct (Nat.eqb 102 116); reflexivity. }
  rewrite Ht. rewrite teqb_refl. reflexivity.
Qed.

Lemma ex_status_unknown : forall n, n <> true_w -> n <> false_w -> ex_status n = 127.
Proof.
  intros n H1 H2. unfold ex_status.
  destruct (teqb n true_w) eqn:E1; [ | idtac ].
  - exfalso. apply H1. apply teqb_true_eq; exact E1.
  - destruct (teqb n false_w) eqn:E2.
    + exfalso. apply H2. apply teqb_true_eq; exact E2.
    + reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════
   §4  Concrete commands and the fuel-bounded functional semantics
   ═══════════════════════════════════════════════════════════════════ *)

Inductive cmd : Type :=
  | Skip                          (* empty command: state unchanged *)
  | Ext  (name : text)            (* external command / builtin *)
  | Assign (k v : text)           (* name=value prefix assignment *)
  | Seq  (c1 c2 : cmd)            (* c1 ; c2 *)
  | And  (c1 c2 : cmd)            (* c1 && c2 *)
  | Or   (c1 c2 : cmd)            (* c1 || c2 *)
  | Bang (c : cmd)                (* ! c *)
  | If   (cond t e : cmd)         (* if cond then t else e *)
  | While (cond body : cmd)       (* while cond do body done *)
  .

Definition obind {A B : Type} (x : option A) (f : A -> option B) : option B :=
  match x with
  | Some a => f a
  | None => None
  end.

(* run f c s — the executable reading of a command.  Fuel is consumed only at
   compound nodes; atomic commands run at every fuel level. *)
Fixpoint run (f : nat) (c : cmd) (s : cstate) : option cstate :=
  match f with
  | 0 =>
      match c with
      | Skip => Some s
      | Ext n => Some (CS (nstat (ex_status n)) (cenv s))
      | Assign k v => Some (CS 0 (setv k v (cenv s)))
      | _ => None
      end
  | S f' =>
      match c with
      | Skip => Some s
      | Ext n => Some (CS (nstat (ex_status n)) (cenv s))
      | Assign k v => Some (CS 0 (setv k v (cenv s)))
      | Bang c =>
          obind (run f' c s) (fun s1 => Some (CS (bstat (cstatus s1)) (cenv s1)))
      | Seq c1 c2 =>
          obind (run f' c1 s) (run f' c2)
      | And c1 c2 =>
          obind (run f' c1 s)
            (fun s1 => if Nat.eqb (cstatus s1) 0 then run f' c2 s1 else Some s1)
      | Or c1 c2 =>
          obind (run f' c1 s)
            (fun s1 => if Nat.eqb (cstatus s1) 0 then Some s1 else run f' c2 s1)
      | If cond t e =>
          obind (run f' cond s)
            (fun sc => if Nat.eqb (cstatus sc) 0 then run f' t sc else run f' e sc)
      | While cond body =>
          obind (run f' cond s)
            (fun sc =>
               if Nat.eqb (cstatus sc) 0
               then obind (run f' body sc) (run f' (While cond body))
               else Some sc)
      end
  end.

(* ── atomic readings ─────────────────────────────────────────────── *)

Lemma run_skip : forall f s, run f Skip s = Some s.
Proof. intros f s; destruct f; reflexivity. Qed.

Lemma run_ext_true : forall f s, run f (Ext true_w) s = Some (CS 0 (cenv s)).
Proof.
  intros f s; destruct f; simpl; rewrite ex_status_true;
  replace (0 mod 256) with 0 by reflexivity; reflexivity.
Qed.

Lemma run_ext_false : forall f s, run f (Ext false_w) s = Some (CS 1 (cenv s)).
Proof.
  intros f s; destruct f; simpl; rewrite ex_status_false;
  replace (1 mod 256) with 1 by reflexivity; reflexivity.
Qed.

Lemma run_assign : forall f k v s,
  run f (Assign k v) s = Some (CS 0 (setv k v (cenv s))).
Proof. intros f k v s; destruct f; reflexivity. Qed.

(* ═══════════════════════════════════════════════════════════════════
   §5  Control-flow boundary laws (the src/ conformance surface)
   ═══════════════════════════════════════════════════════════════════ *)

(* && short-circuits: a failing left operand stops the list and the right never
   runs, so the state is exactly the left command's result. *)
Lemma and_left_false_stops :
  forall c2 s0 f, run (S f) (And (Ext false_w) c2) s0 = Some (CS 1 (cenv s0)).
Proof.
  intros c2 s0 f. cbn [run obind]. rewrite run_ext_false.
  cbn [obind cstatus]. reflexivity.
Qed.

(* || short-circuits: a succeeding left operand stops the list. *)
Lemma or_left_true_stops :
  forall c2 s0 f, run (S f) (Or (Ext true_w) c2) s0 = Some (CS 0 (cenv s0)).
Proof.
  intros c2 s0 f. cbn [run obind]. rewrite run_ext_true.
  cbn [obind]. reflexivity.
Qed.

(* ; is right-sequential: the list status is the last command's status. *)
Lemma seq_last_status_and :
  forall c1 c2 s0 f s1 s2,
  run f c1 s0 = Some s1 -> run f c2 s1 = Some s2 ->
  run (S f) (Seq c1 c2) s0 = Some s2.
Proof.
  intros c1 c2 s0 f s1 s2 H1 H2.
  cbn [run]. rewrite H1. cbn [obind]. rewrite H2. reflexivity.
Qed.

(* while with an immediately-failing test runs its body zero times and keeps the
   test's status. *)
Lemma while_false_zero :
  forall body s0 f, run (S f) (While (Ext false_w) body) s0 = Some (CS 1 (cenv s0)).
Proof.
  intros body s0 f. cbn [run obind]. rewrite run_ext_false.
  cbn [obind cstatus]. reflexivity.
Qed.

(* ! inverts a command's zero/non-zero status, leaving the environment alone. *)
Lemma bang_inverts_false :
  forall s0 f, run (S f) (Bang (Ext false_w)) s0 = Some (CS 0 (cenv s0)).
Proof.
  intros s0 f. cbn [run obind]. rewrite run_ext_false.
  cbn [obind]. unfold bstat. reflexivity.
Qed.

Lemma bang_inverts_true :
  forall s0 f, run (S f) (Bang (Ext true_w)) s0 = Some (CS 1 (cenv s0)).
Proof.
  intros s0 f. cbn [run obind]. rewrite run_ext_true.
  cbn [obind]. unfold bstat. reflexivity.
Qed.

(* if branches purely on the condition status: a succeeding test runs the
   then-branch, in the environment the test left behind (status 0). *)
Lemma if_true_takes_then :
  forall t e s0 f,
  run (S f) (If (Ext true_w) t e) s0 = run f t (CS 0 (cenv s0)).
Proof.
  intros t e s0 f. cbn [run obind]. rewrite run_ext_true.
  cbn [obind]. reflexivity.
Qed.

(* a failing test runs the else-branch. *)
Lemma if_false_takes_else :
  forall t e s0 f,
  run (S f) (If (Ext false_w) t e) s0 = run f e (CS 1 (cenv s0)).
Proof.
  intros t e s0 f. cbn [run obind]. rewrite run_ext_false.
  cbn [obind]. reflexivity.
Qed.

(* An assignment binds its value: reading the key back from the resulting
   environment yields v, at every fuel level. *)
Lemma assign_binds :
  forall k v s0 f,
  match run f (Assign k v) s0 with
  | Some s => getv k (cenv s) = Some v
  | None => True
  end.
Proof.
  intros k v s0 f; destruct f; cbn; apply getv_set_same.
Qed.

(* Assignments are isolated: binding one name leaves another distinct name's
   value unchanged. *)
Lemma assign_isolated :
  forall k k2 v s0,
  teqb k2 k = false ->
  match run 1 (Assign k v) s0 with
  | Some s => getv k2 (cenv s) = getv k2 (cenv s0)
  | None => True
  end.
Proof.
  intros k k2 v s0 Hne. cbn. apply getv_set_other. exact Hne.
Qed.
