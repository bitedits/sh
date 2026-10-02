(* sh_concrete.v
 *
 * Concrete POSIX shell semantics: the Coq model that becomes the single source
 * of truth for the extracted C99 shell.  Where sh_properties.v abstracts a
 * command to a nat status and a nat-keyed environment, this file models the
 * things the real shell touches — words (text), a name->value environment, an
 * external-command status oracle, word expansion, glob matching, and the full
 * control surface the parser produces (; && || ! if while for case).  It is
 * still relational-free and axiom-free: every command has a decidable,
 * fuel-bounded functional reading `run`, so the whole file compiles through the
 * kernel with no Axiom and no Parameter.
 *
 * Design notes carried into the extraction (Phase 3c/3d):
 *  - text is list nat (byte codes), not Coq's string, because a list extracts to
 *    an OCaml list and a C array while Coq string drags in list_ofascii; the
 *    extraction maps this type to OCaml string / C char* via Extract mappings.
 *  - the external-command status is modelled as DATA (a total function on the
 *    command name), not as an effectful oracle: "true"->0, "false"->1, anything
 *    else->127 (command-not-found).  This keeps the model pure; the C shim
 *    replaces the constant arms with the real fork/execvp status at the seam.
 *  - fuel is the single recursion measure: every fixpoint (run and its mutual
 *    helpers, expand, glob) decreases on a leading nat argument, so all of them
 *    are safe fixpoints and every Example below is closed by pure computation.
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
Import ListNotations.

(* cmd stores list-valued fields, so it is a nested inductive; the "register-all"
   warning only concerns auto-generated induction schemes we never use here. *)
Set Warnings "-register-all".

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
   §4  Word expansion: $name, ${name}, $?  (unset -> empty)
   ═══════════════════════════════════════════════════════════════════ *)

(* Byte codes used by the expander (POSIX/ASCII). *)
Definition b_dollar : nat := 36.   (* '$'  *)
Definition b_lbrace : nat := 123.  (* '{'  *)
Definition b_rbrace : nat := 125.  (* '}'  *)
Definition b_qmark  : nat := 63.   (* '?'  *)
Definition b_uscore : nat := 95.   (* '_'  *)
Definition b_0      : nat := 48.   (* '0'  *)

Definition is_digit (b : nat) : bool := Nat.leb b_0 b && Nat.leb b 57.
Definition is_alpha (b : nat) : bool :=
  (Nat.leb 65 b && Nat.leb b 90) || (Nat.leb 97 b && Nat.leb b 122).
Definition is_name (b : nat) : bool := is_alpha b || is_digit b || Nat.eqb b b_uscore.

(* decimal rendering of a status; statuses are small so ten digits is ample. *)
Fixpoint nat_digits (f n : nat) (acc : text) : text :=
  match f with
  | 0 => acc
  | S f' => if Nat.eqb n 0 then acc else nat_digits f' (n / 10) (((n mod 10) + b_0) :: acc)
  end.

Definition nat2text (n : nat) : text :=
  match n with
  | 0 => [b_0]
  | S _ => nat_digits 10 n []
  end.

(* substitute a looked-up name, or nothing when unset (model lookup_param). *)
Definition subst_var (m : list (text * text)) (nm rest : text) : text :=
  match getv nm m with
  | Some v => v ++ rest
  | None => rest
  end.

(* expand scans a word left to right; fuel is consumed once per input byte so a
   bare '$' never loops.  The leading fuel argument decreases in every recursive
   call across the whole mutual group, which keeps the guard checker happy. *)
Fixpoint expand (f : nat) (m : list (text * text)) (st : nat) (inp : text) : text :=
  match f with
  | 0 => []
  | S f' =>
      match inp with
      | [] => []
      | b :: bs =>
          if Nat.eqb b b_dollar then
            match bs with
            | [] => [b_dollar]
            | b2 :: bs2 =>
                if Nat.eqb b2 b_lbrace then expand_brace f' m st bs2 []
                else if is_name b2 then expand_name f' m st bs2 [b2]
                else if Nat.eqb b2 b_qmark then nat2text st ++ expand f' m st bs2
                else b_dollar :: expand f' m st bs
            end
          else b :: expand f' m st bs
      end
  end

with expand_name (f : nat) (m : list (text * text)) (st : nat) (inp acc : text) : text :=
  match f with
  | 0 => subst_var m acc []
  | S f' =>
      match inp with
      | [] => subst_var m acc []
      | b :: bs =>
          if is_name b then expand_name f' m st bs (acc ++ [b])
          else subst_var m acc (expand f' m st inp)
      end
  end

with expand_brace (f : nat) (m : list (text * text)) (st : nat) (inp acc : text) : text :=
  match f with
  | 0 => []
  | S f' =>
      match inp with
      | [] => []
      | b :: bs =>
          if Nat.eqb b b_rbrace then subst_var m acc (expand f' m st bs)
          else expand_brace f' m st bs (acc ++ [b])
      end
  end.

(* ═══════════════════════════════════════════════════════════════════
   §5  Glob matching for case patterns ('*' and '?')
   ═══════════════════════════════════════════════════════════════════ *)

Definition b_star : nat := 42.   (* '*'  *)

(* fuel-bounded glob: '*' matches any run of bytes, '?' matches one byte,
   anything else must match literally. *)
Fixpoint glob (f : nat) (pat str : text) : bool :=
  match f with
  | 0 => false
  | S f' =>
      match pat with
      | [] => match str with [] => true | _ => false end
      | p :: ps =>
          if Nat.eqb p b_star then
            match str with
            | [] => glob f' ps []
            | _ :: ss => glob f' ps str || glob f' pat ss
            end
          else
            match str with
            | [] => false
            | s :: ss =>
                if Nat.eqb p b_qmark then glob f' ps ss
                else if Nat.eqb p s then glob f' ps ss else false
            end
      end
  end.

(* first-match over a branch's alternative patterns; only glob is used here, so
   this is a standalone fixpoint rather than part of the run mutual group. *)
Fixpoint match_any (f : nat) (pats : list text) (scrut : text) : bool :=
  match f with
  | 0 => false
  | S f' =>
      match pats with
      | [] => false
      | p :: r => glob f' p scrut || match_any f' r scrut
      end
  end.

(* ═══════════════════════════════════════════════════════════════════
   §6  Concrete commands and the fuel-bounded functional semantics
   ═══════════════════════════════════════════════════════════════════ *)

Inductive cmd : Type :=
  | Skip                          (* empty command: state unchanged *)
  | Ext  (name : text)            (* external command / builtin (already expanded) *)
  | Assign (k v : text)           (* name=value prefix assignment (value already expanded) *)
  | Seq  (c1 c2 : cmd)            (* c1 ; c2 *)
  | And  (c1 c2 : cmd)            (* c1 && c2 *)
  | Or   (c1 c2 : cmd)            (* c1 || c2 *)
  | Bang (c : cmd)                (* ! c *)
  | If   (cond t e : cmd)         (* if cond then t else e *)
  | While (cond body : cmd)       (* while cond do body done *)
  | For (var : text) (ws : list text) (body : list cmd)   (* for var in ws; do body; done *)
  | Case (scrut : text) (brs : list (list text * list cmd)) (* case scrut in pats) body ;; ... esac *)
  .

Definition obind {A B : Type} (x : option A) (f : A -> option B) : option B :=
  match x with
  | Some a => f a
  | None => None
  end.

(* run f c s — the executable reading of a command.  Fuel is consumed only at
   compound nodes; atomic commands run at every fuel level.  run, run_seq,
   run_for, run_case and match_any form one mutual group, all decreasing on the
   leading fuel argument, so the kernel accepts them as safe fixpoints. *)
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
      | For var ws body =>
          run_for f' var ws body s
      | Case scrut brs =>
          run_case f' scrut brs s
      end
  end

with run_seq (f : nat) (cmds : list cmd) (s : cstate) : option cstate :=
  match f with
  | 0 => None
  | S f' =>
      match cmds with
      | [] => Some (CS 0 (cenv s))
      | [c] => run f' c s
      | c :: c2 :: r => obind (run f' c s) (run_seq f' (c2 :: r))
      end
  end

with run_for (f : nat) (var : text) (ws : list text) (body : list cmd) (s : cstate) : option cstate :=
  match f with
  | 0 => None
  | S f' =>
      match ws with
      | [] => Some (CS 0 (cenv s))
      | [w] =>
          let s1 := CS (cstatus s) (setv var (expand f' (cenv s) (cstatus s) w) (cenv s)) in
          run_seq f' body s1
      | w :: w2 :: r =>
          let s1 := CS (cstatus s) (setv var (expand f' (cenv s) (cstatus s) w) (cenv s)) in
          obind (run_seq f' body s1) (run_for f' var (w2 :: r) body)
      end
  end

with run_case (f : nat) (scrut : text) (brs : list (list text * list cmd)) (s : cstate) : option cstate :=
  match f with
  | 0 => None
  | S f' =>
      match brs with
      | [] => Some (CS 0 (cenv s))
      | (pats, body) :: r =>
          if match_any f' pats (expand f' (cenv s) (cstatus s) scrut)
          then run_seq f' body s
          else run_case f' scrut r s
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
   §7  Control-flow boundary laws (the src/ conformance surface)
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

(* ═══════════════════════════════════════════════════════════════════
   §8  Behaviour of the expander and the matcher, checked by computation.
   ═══════════════════════════════════════════════════════════════════ *)

Example expand_var_present : expand 4 [([97], [98])] 0 [36; 97] = [98].
Proof. reflexivity. Qed.

Example expand_var_unset : expand 4 [] 0 [36; 97] = [].
Proof. reflexivity. Qed.

Example expand_var_brace : expand 6 [([97], [98])] 0 [36; 123; 97; 125] = [98].
Proof. reflexivity. Qed.

Example expand_status_zero : expand 2 [] 0 [36; 63] = [48].
Proof. reflexivity. Qed.

Example expand_status_one : expand 2 [] 1 [36; 63] = [49].
Proof. reflexivity. Qed.

Example expand_lone_dollar : expand 3 [] 0 [36; 64; 65] = [36; 64; 65].
Proof. reflexivity. Qed.

Example glob_exact : glob 4 [97; 98] [97; 98] = true.
Proof. reflexivity. Qed.

Example glob_question : glob 3 [97; 63] [97; 99] = true.
Proof. reflexivity. Qed.

Example glob_star : glob 6 [97; 42] [97; 99; 100] = true.
Proof. reflexivity. Qed.

Example glob_mismatch : glob 4 [97; 98] [97; 99] = false.
Proof. reflexivity. Qed.

(* ═══════════════════════════════════════════════════════════════════
   §9  End-to-end: run binds the environment the expander reads, and the
       for/case forms run the expanded control surface.
   ═══════════════════════════════════════════════════════════════════ *)

(* A whole list: assign a=b, then expand "$a" in the produced environment gives
   "b".  The environment is exactly `run (Assign a b)`'s output. *)
Example assign_then_expand :
  expand 4 (setv [97] [98] []) 0 [36; 97] = [98].
Proof. reflexivity. Qed.

(* for x in a b: the loop leaves x bound to the last word, status 0. *)
Example for_binds_last :
  run 6 (For [120] [[97]; [98]] [Skip]) (CS 0 []) = Some (CS 0 [([120], [98])]).
Proof. reflexivity. Qed.

(* for over an empty word list runs the body zero times and returns 0. *)
Example for_empty :
  run 3 (For [120] [] [Ext false_w]) (CS 5 []) = Some (CS 0 []).
Proof. reflexivity. Qed.

(* case: the first matching pattern's body runs; 'a' matches pattern 'a'.
   Each branch carries a LIST of alternative glob patterns; here one each. *)
Example case_first_match :
  run 6 (Case [97] [([[97]], [Ext false_w]); ([[42]], [Ext true_w])]) (CS 0 [])
  = Some (CS 1 []).
Proof. reflexivity. Qed.

(* case: 'a' does not match 'b', so the '*' (match-all) branch runs. *)
Example case_star_fallback :
  run 6 (Case [97] [([[98]], [Ext false_w]); ([[42]], [Ext true_w])]) (CS 0 [])
  = Some (CS 0 []).
Proof. reflexivity. Qed.

(* case with no matching branch leaves status 0. *)
Example case_no_match :
  run 6 (Case [97] [([[98]], [Ext false_w])]) (CS 0 []) = Some (CS 0 []).
Proof. reflexivity. Qed.

(* for over one word expands that word against the live environment before
   binding the loop variable: with a=9 in scope, `for x in $a` binds x to 9.
   (Ext/Assign words are pre-expanded by the parser bridge, so the for-loop's
   own word-list expansion is the read-back demonstrated here.) *)
Example for_expands_word :
  run 6 (For [120] [[36; 97]] [Skip]) (CS 0 [([97], [57])])
  = Some (CS 0 [([97], [57]); ([120], [57])]).
Proof. reflexivity. Qed.
