(* sh_jpl_scan.v

 * JPL.5 path (A) — the bounded, ITERATIVE scan layer.  Sections 1-3 are step
 * 5-A.1 (bounded words), section 4 is step 5-A.3 (iterative glob/match_any) with
 * its two agreement halves — §4.2 soundness and §4.3 completeness, both proved
 * for arbitrary inputs, with §4.3.14 sizing L3's GLOB_FUEL from the loop's own
 * fuel law — section 5 is step 5-A.2 (iterative getv/setv over the benv array),
 * and section 6 is step 5-A.7 (the iterative word expander, which agrees with
 * sh_concrete's `expand` at EVERY fuel and so needs no guard).

 * Background (JPL.md): the machine authored in sh_jpl_run.v drove the
 * *concrete* sh_concrete scans (teqb/expand/glob/setv), which use non-tail
 * appends and, for glob, tree backtracking.  Extraction keeps that shape, so the
 * emitted OCaml was not yet in the "tail loops over a bounded store" subset the
 * JPL.5 emitter requires — which is what this file plus sh_jpl_run_c.v (L8, which
 * calls these loops) fix: after 5-A.7 the shipped kernel `mrun_c` reaches the OS
 * seam only through the loops proved here.  Path A fixes this in the SOURCE: this file rewrites
 * every byte-level scan as a fuel-bounded TAIL loop over a length-carrying
 * bounded word, and proves each one agrees with the sh_concrete original on
 * in-budget inputs, so the extraction that consumes this layer yields `while`
 * loops with no cons-walking recursion left to lower.

 * Invariants (JPL.md §Design):
 *   1. Axiom-free — coqchk -o -silent must report four <none>.  No Axiom /
 *      Parameter / Admitted / admit below.
 *   2. Behavioral isomorphism — every b_* / *_it scan equals the sh_concrete
 *      helper for well-formed, in-budget inputs (the lemmas + Examples below).
 *   3. Additive — sh_concrete.v is imported untouched as the reference
 *      semantics; sh_jpl.v's definitions are untouched too (only its §5 header
 *      comment now points here, where the emitter-lowerable forms live).
 *      Existing gates stay green.

 * The bounded word `bt` is the emitter's fixed array: a `text` payload plus its
 * length, with smart constructors that saturate (return BLimit) once MAX_WORD is
 * crossed, reusing sh_jpl's capacity constants and result carrier.

 * Build (Rocq >= 9.0):
 *   coqc sh_concrete.v; coqc sh_jpl.v; coqc sh_jpl_scan.v
 *   coqchk -o -silent sh_jpl_scan    # must report Axioms: <none>
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.
Import ListNotations.

Require Import sh_concrete.
Require Import sh_jpl.

Set Warnings "-register-all".

(* ═══════════════════════════════════════════════════════════════════
   §1  Bounded word `bt`: a byte payload + its length, capped at MAX_WORD

   This is deliberately the same shape as sh_jpl.bword (bytes ++ len); we reuse
   the concrete `text` payload so equality/lookup stay a single definition, and
   the saturation cap so there is exactly one MAX_WORD discipline in the tree.
   ═══════════════════════════════════════════════════════════════════ *)

Definition bt : Type := bword.          (* BW { bw_bytes : text; bw_len : nat } *)
Definition bt_bytes : bt -> text := bw_bytes.
Definition bt_len : bt -> nat := bw_len.
Definition wf_bt : bt -> Prop := wf_bword.

Definition bt_nil : bt := raw_bword [].

Definition bt_of (l : text) : bres bt := mk_bword l.

Lemma bt_nil_wf : wf_bt bt_nil.
Proof.
  unfold bt_nil, wf_bt, bt, wf_bword, raw_bword.
  cbn; split; [ reflexivity | unfold MAX_WORD; lia ].
Qed.

(* ═══════════════════════════════════════════════════════════════════
   §2  Bounded push — the write seam the tail loops accumulate into

   Push is the sh_jpl primitive (bytes ++ [x]); it carries the length invariant
   and saturates at MAX_WORD.  The loops below build their output one push at a
   time, so the only O(length) list work left is this guarded buffer write, which
   the emitter lowers to a fixed-array store at index len (never a malloc).
   ═══════════════════════════════════════════════════════════════════ *)

Definition bt_push (x : nat) (w : bt) : bres bt := b_push w x.

(* ═══════════════════════════════════════════════════════════════════
   §3  Scans that stay single-source: equality, bounded append, membership

   These reuse the concrete definitions verbatim rather than re-encoding them
   (design invariant: one hand-written truth).  `teqb` is already a fuel-free
   *tail* structural walk (its only recursive use is the tail of the else arm),
   and `b_app`/`b_push` are the saturating buffer writes.  What the JPL.5 emitter
   lowers — bounded `++`-style structural recursion — is exactly the shape these
   present, so they need no source rewrite; only glob's tree recursion (§later)
   and the phi closure do.  The Examples below pin the observable contract so the
   later re-extraction has a machine-checkable fidelity anchor.
   ═══════════════════════════════════════════════════════════════════ *)

(* byte-ordered equality on the payload: the concrete teqb, single source. *)
Definition bt_eq (u v : bt) : bool := teqb (bt_bytes u) (bt_bytes v).

Lemma bt_eq_refl : forall w, bt_eq w w = true.
Proof. intros w. unfold bt_eq. apply teqb_refl. Qed.

(* bounded append of two words; saturates to BLimit past MAX_WORD. *)
Definition bt_append (u v : bt) : bres bt := b_app u v.

(* a word plus one byte equals the push of that byte — the seam the loops use. *)
Example bt_push_one : bt_push 65 bt_nil = BOk (raw_bword [65]).
Proof. reflexivity. Qed.

Example bt_eq_agree : bt_eq (raw_bword [102;111]) (raw_bword [102;111]) = true.
Proof. reflexivity. Qed.

Example bt_eq_neq : bt_eq (raw_bword [97]) (raw_bword [98]) = false.
Proof. reflexivity. Qed.

(* saturation: appending a one-byte word to a full MAX_WORD word must refuse. *)
Lemma bt_append_full big (Hlen : bw_len big = MAX_WORD) :
  bt_append big (raw_bword [0]) = BLimit.
Proof.
  unfold bt_append, b_app.
  rewrite Hlen.
  unfold MAX_WORD; cbn [bw_len raw_bword length Nat.add Nat.leb]; reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════
   §4  Iterative glob — the mandatory Coq rewrite (5-A.3)

   sh_concrete.glob recurses as `glob f' ps str || glob f' pat ss` on a '*': a
   *tree* recursion the JPL.5 emitter cannot mechanically lower to a while-loop
   (the whole reason path A exists).  Here it is replaced by the classic forward
   two-scan with one saved backtracking point: `bk = Some (ps, str)` records the
   pattern just after the most recent '*' and the string where that '*' began.
   Every recursive call below is in TAIL position of a single fuel-bounded
   Fixpoint (one `S g` decrement per forward step OR per backtrack retry), so
   extraction yields one `let rec` -> one `while`.  The three fallback sites are
   deliberately the same inline block rather than a shared helper: a helper would
   be mutual recursion and defeat the guard checker.

   Agreement with sh_concrete.glob comes in two halves, both now proved for
   arbitrary inputs.  SOUNDNESS (a true answer is a real match) is §4.2, with no
   fuel hypothesis on the loop side.  COMPLETENESS (a real match is found) is
   §4.3, at the loop's own quadratic budget fuel_top — the statement cannot be
   carried at §4.2.2's linear budget, and §4.2.4 computes the difference.
   ═══════════════════════════════════════════════════════════════════ *)

Fixpoint glob_it (f : nat) (pat str : text) (bk : option (text * text)) : bool :=
  match f with
  | 0 => false
  | S g =>
    match pat with
    | [] =>
        match str with
        | [] => true
        | _ =>
            match bk with
            | None => false
            | Some (bps, bstr) =>
                match bstr with
                | [] => false
                | _ :: rstr => glob_it g bps rstr (Some (bps, rstr))
                end
            end
        end
    | p :: ps =>
        if Nat.eqb p b_star then
          glob_it g ps str (Some (ps, str))
        else
          match str with
          | [] =>
              match bk with
              | None => false
              | Some (bps, bstr) =>
                  match bstr with
                  | [] => false
                  | _ :: rstr => glob_it g bps rstr (Some (bps, rstr))
                  end
              end
          | s :: ss =>
              if Nat.eqb p b_qmark || Nat.eqb p s
              then glob_it g ps ss bk
              else
                match bk with
                | None => false
                | Some (bps, bstr) =>
                    match bstr with
                    | [] => false
                    | _ :: rstr => glob_it g bps rstr (Some (bps, rstr))
                    end
                end
          end
    end
  end.

(* closed form over an empty backtrack stack — the caller's entry point. *)
Definition glob_iter (f : nat) (pat str : text) : bool := glob_it f pat str None.

(* match_any as a fuel-bounded tail loop over the branch's patterns. *)
Fixpoint match_any_iter (f : nat) (pats : list text) (scrut : text) : bool :=
  match f with
  | 0 => false
  | S g =>
      match pats with
      | [] => false
      | p :: r => if glob_iter g p scrut then true else match_any_iter g r scrut
      end
  end.

(* ── §4.1 agreement with concrete glob on the parity + §8/§9 literals ── *)

(* byte mnemonics: 97 a, 98 b, 99 c, 100 d, 122 z; 42 '*', 63 '?'. *)
Example gi_exact    : glob_iter 8 [97;98] [97;98] = true.  Proof. reflexivity. Qed.
Example gi_qmark    : glob_iter 8 [97;63] [97;99] = true.  Proof. reflexivity. Qed.
Example gi_star     : glob_iter 8 [97;42] [97;99;100] = true. Proof. reflexivity. Qed.
Example gi_mismatch : glob_iter 8 [97;98] [97;99] = false. Proof. reflexivity. Qed.

(* backtracking: '*' must give a byte back so the trailing literal can match. *)
Example gi_star_b_ab   : glob_iter 32 [97;42;98] [97;98] = true.    Proof. reflexivity. Qed.
Example gi_star_b_abz  : glob_iter 32 [97;42;98] [97;98;122] = false. Proof. reflexivity. Qed.
Example gi_star_b_axb  : glob_iter 32 [97;42;98] [97;120;98] = true.  Proof. reflexivity. Qed.
Example gi_bare_star   : glob_iter 8 [42] [] = true.                 Proof. reflexivity. Qed.
Example gi_star_lit    : glob_iter 16 [42;98] [97;98] = true.        Proof. reflexivity. Qed.

Example gi_match_any_hit  : match_any_iter 16 [[97];[97;42]] [97;99] = true.  Proof. reflexivity. Qed.
Example gi_match_any_miss : match_any_iter 16 [[97];[98]] [99] = false.       Proof. reflexivity. Qed.

(* cross-check the iterative matcher reproduces the CONCRETE matcher exactly on
   each literal above (not just its own self-consistency). *)
Example gi_matches_concrete_star : glob_iter 8 [97;42] [97;99;100] = glob 8 [97;42] [97;99;100].
Proof. reflexivity. Qed.

Example gi_matches_concrete_abz : glob_iter 32 [97;42;98] [97;98;122] = glob 32 [97;42;98] [97;98;122].
Proof. reflexivity. Qed.

Example gi_matches_concrete_any : match_any_iter 16 [[97];[97;42]] [97;99] = match_any 16 [[97];[97;42]] [97;99].
Proof. reflexivity. Qed.

(* ═══════════════════════════════════════════════════════════════════
   §4.2  General agreement with concrete glob — task #34, soundness half
         (its mate, completeness, is §4.3)

   §4.1 samples the two matchers on the exact literals parity exercises.  This
   section replaces that sampling with theorems about ARBITRARY inputs.  The
   bridge is a declarative spec `gmatch` of what a glob means, written
   independently of either implementation:

     []       matches []
     p :: ps  matches p :: str        for a literal p
     ? :: ps  matches s :: str        ('?' eats exactly one byte)
     * :: ps  matches str             ('*' eats nothing here...)
     * :: ps  matches s :: str        (...or eats one byte and still matches)

   Everything below is proved for arbitrary pat/str/bk with NO fuel hypothesis on
   the loop side, so it holds at whatever fuel the machine actually uses:

     glob_it true          -> ok_it            (§4.2.3, the loop's own invariant)
     glob_iter true        -> gmatch           (§4.2.3)
     glob_iter true        -> glob (S(P+S)) true  (§4.2.3, agreement with L2)
     match_any_iter true   -> a branch really gmatches  (§4.2.3)

   NOT proved HERE (completeness, task #34's other half):
     gmatch pat str -> glob_iter f pat str = true  for f large enough.
   It cannot go through the disjunction `ok_it` alone: it needs a *linked*
   invariant tying the saved cell to the forward state (bstr = pre' ++ fws and
   bps = pre ++ pat for the same derivation of gmatch), plus the loop's measured
   quadratic fuel (P+1)(S+1) — concrete glob itself only needs the linear S(P+S)
   proved in §4.2.2, so the two bounds differ and the gap is real (§4.2.4 pins it
   by computation on '*a' / "aaa": glob decides it at 6, the loop needs 7).  That
   is exactly what §4.3 builds: `cinv` is the linked invariant, `fuel_top` is the
   quadratic bound.
   ═══════════════════════════════════════════════════════════════════ *)

(* ── §4.2.1  the declarative spec, and the retry machinery it needs ── *)

Inductive gmatch : text -> text -> Prop :=
| gm_end : gmatch [] []
| gm_lit : forall p ps str,
    Nat.eqb p b_star = false -> gmatch ps str -> gmatch (p :: ps) (p :: str)
| gm_q : forall ps s str,
    gmatch ps str -> gmatch (b_qmark :: ps) (s :: str)
| gm_star_here : forall ps str,
    gmatch ps str -> gmatch (b_star :: ps) str
| gm_star_take : forall ps s str,
    gmatch (b_star :: ps) str -> gmatch (b_star :: ps) (s :: str).

(* star absorbs any run of bytes in front of what it already matched *)
Lemma gmatch_star_app : forall h ps t,
  gmatch ps t -> gmatch (b_star :: ps) (h ++ t).
Proof.
  induction h as [| x h IH]; intros ps t Hm; cbn [app].
  - apply gm_star_here; exact Hm.
  - apply gm_star_take; apply IH; exact Hm.
Qed.

(* a match is a retry: dropping bytes off the front of the string keeps it
   matchable by the same pattern, because a leading '*' can eat them. *)
Definition gretry (bps bstr : text) : Prop :=
  exists h t, bstr = h ++ t /\ gmatch bps t.

Lemma gmatch_gretry : forall bps t, gmatch bps t -> gretry bps t.
Proof.
  intros bps t Hm. exists [], t. split; [ cbn [app]; reflexivity | exact Hm ].
Qed.

Lemma gretry_cons : forall bps x s, gretry bps s -> gretry bps (x :: s).
Proof.
  intros bps x s [h [t [Hs Hm]]]. exists (x :: h), t.
  rewrite Hs; split; [ cbn [app]; reflexivity | exact Hm ].
Qed.

Lemma gretry_gmatch_star : forall bps bstr,
  gretry bps bstr -> gmatch (b_star :: bps) bstr.
Proof.
  intros bps bstr [h [t [Hs Hm]]]. rewrite Hs.
  apply gmatch_star_app; exact Hm.
Qed.

(* the loop's invariant: either the forward scan still matches, or the saved
   backtrack cell can still be drained into a match *)
Inductive ok_it : text -> text -> option (text * text) -> Prop :=
| oi_match : forall pat str bk, gmatch pat str -> ok_it pat str bk
| oi_retry : forall pat str bps bstr, gretry bps bstr -> ok_it pat str (Some (bps, bstr)).

Lemma ok_it_drain_match : forall pat str bps x s,
  gmatch bps s -> ok_it pat str (Some (bps, x :: s)).
Proof.
  intros pat str bps x s Hm.
  apply oi_retry; apply gretry_cons; apply gmatch_gretry; exact Hm.
Qed.

Lemma ok_it_drain_retry : forall pat str bps x s,
  gretry bps s -> ok_it pat str (Some (bps, x :: s)).
Proof.
  intros pat str bps x s Hg. apply oi_retry; apply gretry_cons; exact Hg.
Qed.

(* ── §4.2.2  concrete glob decides gmatch, with linear fuel ── *)

Lemma glob_true_gmatch : forall f pat str, glob f pat str = true -> gmatch pat str.
Proof.
  induction f as [| f IH];
    [ intros pat str H; cbn in H; discriminate | ].
  intros pat str H; revert H; cbn; destruct pat as [| p ps]; cbn.
  - destruct str as [| s ss]; cbn; intros H; try discriminate; apply gm_end.
  - destruct (Nat.eqb p b_star) eqn:Ep; cbn.
    + apply Nat.eqb_eq in Ep; subst p.
      destruct str as [| s ss]; cbn; intros H.
      * apply gm_star_here; apply IH; exact H.
      * apply orb_true_iff in H; destruct H as [H1|H2];
          [ apply gm_star_here; apply IH; exact H1
          | apply gm_star_take; apply IH; exact H2 ].
    + destruct str as [| s ss]; cbn;
        [ intros H; discriminate
        | destruct (Nat.eqb p b_qmark) eqn:Eq; cbn;
            [ intros H; apply Nat.eqb_eq in Eq; subst p;
              apply gm_q; apply IH; exact H
            | destruct (Nat.eqb p s) eqn:Es; cbn;
                [ intros H; apply Nat.eqb_eq in Es; subst s;
                  apply gm_lit; [ exact Ep | apply IH; exact H ]
                | intros H; discriminate ] ] ].
Qed.

Lemma gmatch_glob : forall pat str, gmatch pat str ->
  forall f, S (length pat + length str) <= f -> glob f pat str = true.
Proof.
  intros pat str H; induction H as
    [ | p ps str Ep Hm IHg | ps s str Hm IHg | ps str Hm IHg | ps s str Hm IHg ];
    intros f Hle.
  - destruct f as [| f]; [ cbn; lia | cbn; reflexivity ].
  - destruct f as [| f]; [ cbn; lia | ]. cbn.
    rewrite Ep; cbn.
    destruct (Nat.eqb p b_qmark) eqn:Eq;
      [ apply IHg; cbn in Hle; lia
      | rewrite Nat.eqb_refl; cbn; apply IHg; cbn in Hle; lia ].
  - destruct f as [| f]; [ cbn; lia | ]. cbn.
    apply IHg; cbn in Hle; lia.
  - destruct f as [| f]; [ cbn; lia | ]. cbn.
    destruct str as [| y ss]; cbn;
      [ apply IHg; cbn in Hle; cbn; lia
      | apply orb_true_iff; left; apply IHg; cbn in Hle; cbn; lia ].
  - destruct f as [| f]; [ cbn; lia | ]. cbn.
    apply orb_true_iff; right; apply IHg; cbn in Hle; cbn; lia.
Qed.

(* the sizing fact #35 needs: length pat + length str drops by at least one per
   recursive glob call, so the reference matcher saturates at linear fuel. *)
Lemma glob_iff_gmatch : forall pat str f,
  S (length pat + length str) <= f -> (glob f pat str = true <-> gmatch pat str).
Proof.
  intros pat str f Hle; split; intro H.
  - exact (glob_true_gmatch f pat str H).
  - exact (gmatch_glob pat str H f Hle).
Qed.

Lemma glob_fuel_mono : forall f1 f2 pat str,
  S (length pat + length str) <= f1 -> f1 <= f2 ->
  glob f1 pat str = true -> glob f2 pat str = true.
Proof.
  intros f1 f2 pat str Hle1 Hle12 Hg.
  apply glob_true_gmatch in Hg.
  refine (gmatch_glob pat str Hg f2 _); lia.
Qed.

(* ── §4.2.3  the iterative loop is sound ── *)

Lemma glob_it_sound : forall f pat str bk,
  glob_it f pat str bk = true -> ok_it pat str bk.
Proof.
  induction f as [| f IH];
    [ intros pat str bk H; cbn in H; discriminate | ].
  intros pat str bk H; revert H; cbn; destruct pat as [| p ps]; cbn;
    [ destruct str as [| s ss]; cbn;
        [ intros H; apply oi_match; apply gm_end
        | destruct bk as [q |]; cbn;
            [ destruct q as [bps bstr]; cbn; destruct bstr as [| x rstr]; cbn;
                [ intros H; discriminate
                | intros H; specialize (IH bps rstr (Some (bps, rstr)) H); inversion IH; subst;
                    [ apply ok_it_drain_match; assumption | apply ok_it_drain_retry; assumption ] ]
            | intros H; discriminate ] ]
    | destruct (Nat.eqb p b_star) eqn:Ep; cbn;
        [ apply Nat.eqb_eq in Ep; subst p;
          intros H; specialize (IH ps str (Some (ps, str)) H); inversion IH; subst;
            [ apply oi_match; apply gm_star_here; assumption
            | apply oi_match; apply gretry_gmatch_star; assumption ]
        | destruct str as [| s ss]; cbn;
            [ destruct bk as [q |]; cbn;
                [ destruct q as [bps bstr]; cbn; destruct bstr as [| x rstr]; cbn;
                    [ intros H; discriminate
                    | intros H; specialize (IH bps rstr (Some (bps, rstr)) H); inversion IH; subst;
                        [ apply ok_it_drain_match; assumption | apply ok_it_drain_retry; assumption ] ]
                | intros H; discriminate ]
            | destruct (Nat.eqb p b_qmark) eqn:Eq; cbn;
                [ apply Nat.eqb_eq in Eq; subst p;
                  intros H; specialize (IH ps ss bk H); inversion IH; subst;
                    [ apply oi_match; apply gm_q; assumption | apply oi_retry; assumption ]
                | destruct (Nat.eqb p s) eqn:Es; cbn;
                    [ apply Nat.eqb_eq in Es; subst s;
                      intros H; specialize (IH ps ss bk H); inversion IH; subst;
                        [ apply oi_match; apply gm_lit; [ exact Ep | assumption ]
                        | apply oi_retry; assumption ]
                    | destruct bk as [q |]; cbn;
                        [ destruct q as [bps bstr]; cbn; destruct bstr as [| x rstr]; cbn;
                            [ intros H; discriminate
                            | intros H; specialize (IH bps rstr (Some (bps, rstr)) H);
                              inversion IH; subst;
                              [ apply ok_it_drain_match; assumption
                              | apply ok_it_drain_retry; assumption ] ]
                        | intros H; discriminate  ] ] ] ] ] ].
Qed.

Corollary glob_iter_sound : forall f pat str,
  glob_iter f pat str = true -> gmatch pat str.
Proof.
  intros f pat str H; unfold glob_iter in H.
  apply glob_it_sound in H; inversion H; assumption.
Qed.

(* the loop never contradicts the reference matcher: whatever it accepts, the
   concrete glob accepts at its own (linear) fuel. *)
Corollary glob_iter_accepts_glob : forall f pat str,
  glob_iter f pat str = true -> glob (S (length pat + length str)) pat str = true.
Proof.
  intros f pat str H.
  exact (gmatch_glob pat str (glob_iter_sound f pat str H)
                   (S (length pat + length str)) (Nat.le_refl _)).
Qed.

(* match_any's iterative form is sound too: an acceptance names a branch whose
   pattern really matches. *)
Corollary match_any_iter_sound : forall f pats scrut,
  match_any_iter f pats scrut = true ->
  exists p, In p pats /\ gmatch p scrut.
Proof.
  induction f as [| f IH];
    [ intros pats scrut H; cbn in H; discriminate | ].
  intros pats scrut H; revert H; cbn; destruct pats as [| p r]; cbn;
    [ intros H; discriminate
    | intros H; apply orb_true_iff in H; destruct H as [Hg|Hi];
        [ exists p; split; [ cbn [In]; left; reflexivity | apply glob_it_sound in Hg; inversion Hg; assumption ]
        | apply IH in Hi; destruct Hi as [q [Hiq Hgq]];
          exists q; split; [ right; exact Hiq | exact Hgq ] ] ].
Qed.

(* ── §4.2.4  the two fuel bounds genuinely differ, pinned by computation ──

   '*a' on "aaa": the reference matcher already decides it at its own linear
   budget S(P+S) = 6, while the loop needs 7.  This is why the scan's budget is
   sized from the loop's QUADRATIC law — which is what §4.3.9's `fuel_top` and
   §4.3.14's sizing of L3's GLOB_FUEL do — and not from §4.2.2's linear bound. *)

Example gf_glob_at_6 : glob 6 [42;97] [97;97;97] = true.
Proof. reflexivity. Qed.

Example gf_loop_at_6 : glob_iter 6 [42;97] [97;97;97] = false.
Proof. reflexivity. Qed.

Example gf_loop_at_7 : glob_iter 7 [42;97] [97;97;97] = true.
Proof. reflexivity. Qed.

(* ═══════════════════════════════════════════════════════════════════
   §4.3  Completeness — task #34's open half, now closed

   §4.2 proves the loop never accepts a non-match.  This section proves the
   converse at an explicit fuel: every real match IS found.  The headline is

     gmatch pat str -> glob_iter (fuel_top pat str) pat str = true

   with fuel_top pat str = (|pat|+|str|+1)*(|str|+1) + |pat| + |str| — the loop's
   own QUADRATIC law, not §4.2.2's linear S(|pat|+|str|).  The two genuinely
   differ (§4.2.4 computes '*a' / "aaa": glob decides it at 6, the loop needs 7),
   so no budget carried over from the reference matcher would do here.

   Why §4.2.3's `ok_it` cannot carry this direction: it is a bare disjunction
   (forward match OR saved cell drainable), so a cell that has nothing to do with
   the forward state satisfies it, and the install site then has no equation that
   forces the bound down.  The invariant used here, `cinv`, ANCHORS the cell: the
   saved pair (cp, cs) is the forward pair (fwd, fws) with one and the same
   star-free LOCKSTEP chunk (pre, pre') put back in front of it, and `fmatch` is
   what records that chunk.  The anchor is what makes every site of the loop
   strictly lower the bound, which is the only place induction can bite.

     §4.3.1-2   fmatch / nostar — what a star-free forward run consumes
     §4.3.3-6   elementary gmatch facts, prefix nesting, hanging, cancellation
     §4.3.7     a star-headed match is a drainable retry
     §4.3.8     cinv and its site lemmas (install, forward step, drain, empty
                cell, no cell)
     §4.3.9-10  the fuel law per site, and the three stuck sites
     §4.3.11    glob_it_complete — induction on fuel, one case per site
     §4.3.12    glob_iter complete, and  glob_iter (fuel_top) = true <->
                glob (S(P+S)) = true
     §4.3.13    match_any_iter <-> match_any at the shared branch budget
     §4.3.14    what the law costs the L3 budget: fuel_top <= GLOB_FUEL, and the
                machine-facing completeness corollaries at MAX_FUEL

   Strength of evidence: PROVED, axiom-free, for arbitrary pat/str/bk — not
   sampled.  §4.1's Examples stay as cheap regression samples only.  What this
   does NOT yet do: the machine still calls sh_concrete's recursive glob.  §4.3.14
   sizes L3's GLOB_FUEL from this layer's law (the constant is definitional, so it
   cannot drift), which removes the last missing ingredient; wiring the kernel's
   `step` onto these loops and transporting `step_c = step` is JPL.5-A.6 (#35).
   ═══════════════════════════════════════════════════════════════════ *)

(* ── §4.3.1 fmatch: what a FORWARD run of glob_it consumes — no star, pattern
      and string advance byte for byte. ── *)
Inductive fmatch : text -> text -> Prop :=
| fm_nil : fmatch [] []
| fm_q : forall ps ss s, fmatch ps ss -> fmatch (b_qmark :: ps) (s :: ss)
| fm_lit : forall p ps ss,
    Nat.eqb p b_star = false -> fmatch ps ss -> fmatch (p :: ps) (p :: ss).

Lemma fmatch_length : forall mid mid', fmatch mid mid' -> length mid = length mid'.
Proof.
  intros mid mid' H; induction H; cbn [length]; [ reflexivity | lia | lia ].
Qed.

Lemma fmatch_cons_inv : forall p ps s ss,
  fmatch (p :: ps) (s :: ss) -> fmatch ps ss.
Proof.
  intros p ps s ss H; inversion H; assumption.
Qed.

Lemma fmatch_take_cons : forall p ps ss s,
  fmatch ps ss ->
  Nat.eqb p b_star = false ->
  (Nat.eqb p b_qmark = true \/ Nat.eqb p s = true) ->
  fmatch (p :: ps) (s :: ss).
Proof.
  intros p ps ss s Hf Hst Hh.
  destruct Hh as [Hq|He].
  - apply Nat.eqb_eq in Hq; subst p; apply fm_q; exact Hf.
  - apply Nat.eqb_eq in He; subst p; apply fm_lit; [ assumption | exact Hf ].
Qed.

Lemma fmatch_app_cons : forall mid mid' p s,
  fmatch mid mid' ->
  Nat.eqb p b_star = false ->
  (Nat.eqb p b_qmark = true \/ Nat.eqb p s = true) ->
  fmatch (mid ++ [p]) (mid' ++ [s]).
Proof.
  intros mid mid' p s Hf Hp Hh; induction Hf as
    [ | ps ss x Hf' IH | q ps ss Hst Hf' IH ]; cbn [app].
  - apply fmatch_take_cons; [ constructor | exact Hp | exact Hh ].
  - apply fm_q; apply IH; assumption.
  - apply fm_lit; [ exact Hst | apply IH; assumption ].
Qed.

(* ── §4.3.2 no-star patterns: the shape every fmatch prefix has ── *)
Inductive nostar : text -> Prop :=
| ns_nil : nostar []
| ns_cons : forall p ps, Nat.eqb p b_star = false -> nostar ps -> nostar (p :: ps).

Lemma eqb_qmark_star : Nat.eqb b_qmark b_star = false.
Proof.
  apply Nat.eqb_neq; intro Heq; unfold b_qmark, b_star in Heq; discriminate.
Qed.

Lemma fmatch_nostar : forall mid mid', fmatch mid mid' -> nostar mid.
Proof.
  intros mid mid' H; induction H.
  - constructor.
  - constructor; [ exact eqb_qmark_star | assumption ].
  - constructor; assumption.
Qed.

Lemma nostar_cons_inv : forall p ps,
  nostar (p :: ps) -> Nat.eqb p b_star = false /\ nostar ps.
Proof.
  intros p ps H; inversion H; subst; split; assumption.
Qed.

(* ── §4.3.3 elementary gmatch facts ── *)
Lemma gmatch_nil_only : forall str, gmatch [] str -> str = [].
Proof.
  intros str H; inversion H; reflexivity.
Qed.

Lemma gmatch_nil_head_star : forall p ps, gmatch (p :: ps) [] -> Nat.eqb p b_star = true.
Proof.
  intros p ps Hm; inversion Hm; subst; apply Nat.eqb_eq; reflexivity.
Qed.

Lemma gmatch_lit_nil : forall p ps,
  Nat.eqb p b_star = false -> gmatch (p :: ps) [] -> False.
Proof.
  intros p ps Hst Hm; rewrite (gmatch_nil_head_star p ps Hm) in Hst; discriminate.
Qed.

(* a '*' head is impossible under a boolean test that says it is not one;
   this discharges the inversion cases that survive on that equation alone. *)
Ltac eqb_stars :=
  repeat match goal with
    | H : Nat.eqb b_star b_star = false |- _ =>
        rewrite Nat.eqb_refl in H; discriminate
    | H : Nat.eqb ?p b_star = false, He : ?p = b_star |- _ =>
        rewrite He in H; rewrite Nat.eqb_refl in H; discriminate
    | H : Nat.eqb ?p b_star = false, He : b_star = ?p |- _ =>
        rewrite <- He in H; rewrite Nat.eqb_refl in H; discriminate
  end.

Lemma gmatch_one_step : forall p ps s ss,
  Nat.eqb p b_star = false ->
  gmatch (p :: ps) (s :: ss) ->
  gmatch ps ss /\ (Nat.eqb p b_qmark = true \/ Nat.eqb p s = true).
Proof.
  intros p ps s ss Hst Hm; inversion Hm; subst; try eqb_stars.
  all: split; [ assumption | ].
  all: first [ right; apply Nat.eqb_eq; reflexivity | left; apply Nat.eqb_eq; reflexivity ].
Qed.

(* a leading '*' eats any run of bytes in front of what it already matched *)
Lemma gmatch_star_absorb : forall q k u,
  gmatch (b_star :: q) u -> gmatch (b_star :: q) (k ++ u).
Proof.
  intros q k u Hm; induction k as [| x xs IH]; [ cbn [app]; exact Hm | ].
  cbn [app]; apply gm_star_take; exact IH.
Qed.

(* ── §4.3.4 prefix nesting: equal appends nest their shorter prefix ── *)
Lemma app_prefix : forall (p q x y : text),
  p ++ x = q ++ y -> length p <= length q ->
  exists (k : text), q = p ++ k /\ x = k ++ y.
Proof.
  induction p as [| a bs IH]; intros q x y He Hle.
  - exists q; split; [ cbn [app]; reflexivity | cbn [app] in He; exact He ].
  - destruct q as [| c cs]; [ exfalso; cbn [length] in Hle; lia | ].
    cbn [app] in He; inversion He; subst.
    destruct (IH cs x y) as [k [Hq Hx]].
    + assumption.
    + cbn [length] in Hle; lia.
    + exists k; split; [ rewrite Hq; cbn [app]; reflexivity | exact Hx ].
Qed.

(* ── §4.3.5 hanging: a star-free leading chunk consumes exactly its own length ── *)
Lemma gmatch_hang : forall mid pat t,
  nostar mid -> gmatch (mid ++ pat) t ->
  exists j u, t = j ++ u /\ fmatch mid j /\ gmatch pat u /\ length j = length mid.
Proof.
  intros mid pat; induction mid as [| p ps IH]; intros t Hns Hm;
    cbn [app] in Hm |- *.
  - exists [], t.
    cbn [app length].
    split; [ reflexivity | split; [ constructor | split; [ assumption | reflexivity ] ] ].
  - apply nostar_cons_inv in Hns; destruct Hns as [Hst Hns].
    destruct t as [| s ss];
      [ exfalso; apply (gmatch_lit_nil p (ps ++ pat) Hst Hm) | ].
    assert (H1 := gmatch_one_step p (ps ++ pat) s ss Hst Hm);
      destruct H1 as [Hm' Hhead].
    destruct (IH ss Hns Hm') as [j [u [Ht [Hf [Hg Hj]]]]].
    exists (s :: j), u.
    split; [ rewrite Ht; cbn [app]; reflexivity |
      split; [ apply fmatch_take_cons; [ exact Hf | exact Hst | exact Hhead ] |
        split; [ exact Hg | cbn [length]; lia ] ] ].
Qed.

(* ── §4.3.6 cancellation: a lockstep prefix is consumed by the string as well ── *)
Lemma gmatch_canc : forall mid mid' pat str,
  fmatch mid mid' -> gmatch (mid ++ pat) (mid' ++ str) -> gmatch pat str.
Proof.
  intros mid mid' pat str Hf Hg.
  destruct (gmatch_hang mid pat (mid' ++ str) (fmatch_nostar mid mid' Hf) Hg)
    as [j [u [Ht [Hfj [Hg' Hj]]]]].
  assert (Hlen : length mid' <= length j).
  { rewrite Hj. rewrite (fmatch_length mid mid' Hf). apply Nat.le_refl. }
  destruct (app_prefix mid' j str u Ht Hlen) as [k [Hjk Hstr]].
  assert (HfL : length mid = length mid') by (apply fmatch_length; exact Hf).
  rewrite Hjk, length_app in Hj.
  assert (H0 : length k = 0) by lia.
  destruct k as [| ck]; [ | exfalso; cbn [length] in H0; discriminate ].
  cbn [app] in Hstr; subst u; exact Hg'.
Qed.

(* an anchored star: the older cell's match, hung on the same lockstep prefix,
   re-establishes the fresh cell's spec. *)
Lemma gmatch_anchored_star : forall mid mid' q str h t,
  fmatch mid mid' ->
  mid' ++ str = h ++ t ->
  gmatch (mid ++ b_star :: q) t ->
  gmatch (b_star :: q) str.
Proof.
  intros mid mid' q str h t Hf He Hm.
  destruct (gmatch_hang mid (b_star :: q) t (fmatch_nostar mid mid' Hf) Hm)
    as [j [u [Ht [Hfj [Hg Hj]]]]].
  rewrite Ht in He; rewrite app_assoc in He.
  destruct (app_prefix mid' (h ++ j) str u He) as [k [Hhj Hstr]].
  - assert (Hm2 : length mid = length mid') by (apply fmatch_length; exact Hf).
    rewrite length_app; lia.
  - rewrite Hstr; apply gmatch_star_absorb; exact Hg.
Qed.

(* ── §4.3.7 the retry form of a star-headed match ── *)
Lemma gmatch_gretry_star : forall ps str,
  gmatch (b_star :: ps) str -> gretry ps str.
Proof.
  intros ps str; induction str as [| s ss IH]; intros Hm.
  - inversion Hm; subst; try eqb_stars.
    all: apply gmatch_gretry; assumption.
  - inversion Hm; subst; try eqb_stars.
    all: first [ apply gmatch_gretry; assumption
               | apply gretry_cons; apply IH; assumption ].
Qed.

(* ── §4.3.8 the loop's invariant: the saved cell is anchored in the forward state
   A state (fwd, fws, bk) is one the forward scan can reach from a real match:
     ci_none — no star has been seen, so what is left really matches;
     ci_scan — a cell is saved, the forward scan still matches, and the cell is
               the anchor of the run that got here;
     ci_cell — a cell is saved and still drainable (the same anchor).
   The anchor says the saved pattern/string pair (cp, cs) is the forward pair
   with a LOCKSTEP (star-free) chunk pre/pre' put back in front of it.  This is
   strictly stronger than §4.2.3's `ok_it` disjunction, which a cell unrelated to
   the forward state also satisfies. *)
Inductive cinv : text -> text -> option (text * text) -> Prop :=
| ci_none : forall fwd fws, gmatch fwd fws -> cinv fwd fws None
| ci_scan : forall fwd fws cp cs pre pre',
    fmatch pre pre' -> cp = pre ++ fwd -> cs = pre' ++ fws ->
    gmatch fwd fws -> cinv fwd fws (Some (cp, cs))
| ci_cell : forall fwd fws pre pre' cp cs,
    fmatch pre pre' -> cp = pre ++ fwd -> cs = pre' ++ fws ->
    gretry cp cs -> cinv fwd fws (Some (cp, cs)).

Lemma cinv_none_inv : forall fwd fws, cinv fwd fws None -> gmatch fwd fws.
Proof.
  intros fwd fws H; inversion H; subst; assumption.
Qed.

(* a drain that leaves a byte in the cell's run keeps the cell drainable *)
Lemma drain_gretry : forall fwd fws pre pre' cp cs x rstr,
  cs = x :: rstr ->
  fmatch pre pre' -> cp = pre ++ fwd -> cs = pre' ++ fws ->
  gretry cp cs -> (gmatch fwd fws -> False) -> gretry cp rstr.
Proof.
  intros fwd fws pre pre' cp cs x rstr Hx Hf Hcp Hcs [h [t [Hht Hm]]] Hng.
  rewrite Hx in Hht; destruct h as [| y h2]; cbn [app] in Hht.
  - (* the cell had already swallowed nothing: its whole string is the forward
       string, so cancellation would unstick the forward state *)
    assert (Ht2 : t = pre' ++ fws)
      by (rewrite <- Hht, <- Hx, Hcs; reflexivity).
    rewrite Hcp, Ht2 in Hm.
    exfalso; apply Hng; exact (gmatch_canc pre pre' fwd fws Hf Hm).
  - (* the run the star had swallowed still has a byte to give back *)
    inversion Hht; subst.
    exists h2, t; split; [ reflexivity | exact Hm ].
Qed.

Lemma cinv_drain : forall fwd fws cp x rstr,
  cinv fwd fws (Some (cp, x :: rstr)) ->
  (gmatch fwd fws -> False) ->
  cinv cp rstr (Some (cp, rstr)).
Proof.
  intros fwd fws cp x rstr Hc Hng.
  inversion Hc; subst.
  - exfalso; apply Hng; assumption.
  - apply ci_cell with (pre := []) (pre' := []); try (cbn [app]; reflexivity).
    + constructor.
    + refine (drain_gretry fwd fws pre pre' (pre ++ fwd) (x :: rstr) x rstr
                      eq_refl _ eq_refl _ _ _); assumption.
Qed.

(* an empty cell string cannot coexist with a stuck forward state: the anchor
   forces the saved pattern to BE the forward pattern, so its retry is a match *)
Lemma anchored_empty_match : forall pre pre' fwd fws,
  fmatch pre pre' -> [] = pre' ++ fws -> gretry (pre ++ fwd) [] -> gmatch fwd fws.
Proof.
  intros pre pre' fwd fws Hf Hnil [h [t [Hht Hm]]].
  destruct pre' as [| a bs]; [ | exfalso; cbn [app] in Hnil; discriminate ].
  cbn [app] in Hnil; subst fws.
  inversion Hf; subst.
  destruct h as [| b hs]; [ | exfalso; cbn [app] in Hht; discriminate ].
  cbn [app] in Hht; subst t.
  exact Hm.
Qed.

Lemma cinv_nil_cell : forall fwd fws cp,
  cinv fwd fws (Some (cp, [])) ->
  (gmatch fwd fws -> False) ->
  False.
Proof.
  intros fwd fws cp Hc Hng.
  inversion Hc; subst.
  - apply Hng; assumption.
  - apply Hng, (anchored_empty_match pre pre' fwd fws); assumption.
Qed.

(* entering a new '*' installs the fresh cell, whatever the older one was *)
Lemma cinv_install : forall ps str bk,
  cinv (b_star :: ps) str bk -> cinv ps str (Some (ps, str)).
Proof.
  intros ps str bk Hc; inversion Hc; subst.
  - apply ci_cell with (pre := []) (pre' := []); try (cbn [app]; reflexivity).
    + constructor.
    + apply gmatch_gretry_star; exact H.
  - apply ci_cell with (pre := []) (pre' := []); try (cbn [app]; reflexivity).
    + constructor.
    + apply gmatch_gretry_star; exact H2.
  - apply ci_cell with (pre := []) (pre' := []); try (cbn [app]; reflexivity).
    + constructor.
    + destruct H2 as [h [t [Hht Hm]]].
      apply gmatch_gretry_star, (gmatch_anchored_star pre pre' ps str h t); assumption.
Qed.

(* a forward step keeps the invariant, extending the anchor by the byte pair *)
Lemma cinv_forward : forall p ps s ss bk,
  cinv (p :: ps) (s :: ss) bk ->
  Nat.eqb p b_star = false ->
  (Nat.eqb p b_qmark = true \/ Nat.eqb p s = true) ->
  cinv ps ss bk.
Proof.
  intros p ps s ss bk Hc Hst Hh; inversion Hc; subst.
  - apply ci_none; exact (proj1 (gmatch_one_step p ps s ss Hst H)).
  - apply ci_scan with (pre := pre ++ [p]) (pre' := pre' ++ [s]);
      [ apply fmatch_app_cons; [ exact H | exact Hst | exact Hh ]
      | rewrite <- app_assoc; reflexivity
      | rewrite <- app_assoc; reflexivity
      | exact (proj1 (gmatch_one_step p ps s ss Hst H2)) ].
  - apply ci_cell with (pre := pre ++ [p]) (pre' := pre' ++ [s]);
      [ apply fmatch_app_cons; [ exact H | exact Hst | exact Hh ]
      | rewrite <- app_assoc; reflexivity
      | rewrite <- app_assoc; reflexivity
      | exact H2 ].
Qed.

(* ── §4.3.9 the fuel bound ──
   scan a b = (a+b+1)(b+1) bounds the drain retries still available to a cell
   holding a pattern of length a and a string of length b; the forward state's
   own lengths are added on top, so every step of the loop — forward, install,
   drain — strictly lowers the bound. *)
Definition scan (a b : nat) : nat := S (a + b) * S b.

Definition state_bound (pat str : text) (bk : option (text * text)) : nat :=
  match bk with
  | None => scan (length pat) (length str) + length pat + length str
  | Some (bps, bstr) => scan (length bps) (length bstr) + length pat + length str
  end.

Definition fuel_top (pat str : text) : nat := state_bound pat str None.

(* Every site closes with the same normalisation: expose scan as a product. *)
Ltac fuel_norm := cbn [state_bound length] in *; unfold scan in *.

Lemma bound_pos_none : forall pat str, 0 < state_bound pat str None.
Proof. intros pat str; fuel_norm; nia. Qed.

Lemma bound_pos_cell : forall pat str bps bstr,
  0 < state_bound pat str (Some (bps, bstr)).
Proof. intros; fuel_norm; nia. Qed.

Lemma bound_pos : forall pat str bk, 0 < state_bound pat str bk.
Proof.
  intros pat str bk; destruct bk as [q|].
  - destruct q as [bps bstr]; apply bound_pos_cell.
  - apply bound_pos_none.
Qed.

Lemma bound_drain : forall pat str bps x rstr,
  state_bound bps rstr (Some (bps, rstr))
  < state_bound pat str (Some (bps, x :: rstr)).
Proof.
  intros pat str bps x rstr; fuel_norm; nia.
Qed.

Lemma bound_step_none : forall p ps s ss,
  state_bound ps ss None < state_bound (p :: ps) (s :: ss) None.
Proof.
  intros p ps s ss; fuel_norm; nia.
Qed.

Lemma bound_step_cell : forall p ps s ss bps bstr,
  state_bound ps ss (Some (bps, bstr))
  < state_bound (p :: ps) (s :: ss) (Some (bps, bstr)).
Proof.
  intros p ps s ss bps bstr; fuel_norm; nia.
Qed.

Lemma bound_step : forall p ps s ss bk,
  state_bound ps ss bk < state_bound (p :: ps) (s :: ss) bk.
Proof.
  intros p ps s ss bk; destruct bk as [q|].
  - destruct q as [bps bstr]; apply bound_step_cell.
  - apply bound_step_none.
Qed.

Lemma bound_install_none : forall ps str,
  state_bound ps str (Some (ps, str)) < state_bound (b_star :: ps) str None.
Proof.
  intros ps str; fuel_norm; nia.
Qed.

Lemma bound_install_cell : forall ps str cp cs,
  cinv (b_star :: ps) str (Some (cp, cs)) ->
  state_bound ps str (Some (ps, str))
  < state_bound (b_star :: ps) str (Some (cp, cs)).
Proof.
  intros ps str cp cs Hc; inversion Hc; subst.
  all:
    assert (Hle1 : length ps <= length (pre ++ b_star :: ps))
      by (rewrite length_app; cbn [length]; lia);
    assert (Hle2 : length str <= length (pre' ++ str))
      by (rewrite length_app; cbn [length]; lia);
    fuel_norm; nia.
Qed.

Lemma bound_install : forall ps str bk,
  cinv (b_star :: ps) str bk ->
  state_bound ps str (Some (ps, str)) < state_bound (b_star :: ps) str bk.
Proof.
  intros ps str bk Hc; destruct bk as [q|].
  - destruct q as [cp cs]; apply bound_install_cell; exact Hc.
  - apply bound_install_none.
Qed.

(* ── §4.3.10 the stuck sites ── *)
Lemma stuck_nil : forall s ss, ~(gmatch [] (s :: ss)).
Proof.
  intros s ss Hm.
  assert (Heq : s :: ss = []) by (apply (gmatch_nil_only _ Hm)).
  discriminate.
Qed.

Lemma stuck_lit_nil : forall p ps,
  Nat.eqb p b_star = false -> ~(gmatch (p :: ps) []).
Proof.
  intros p ps Hst Hm; exact (gmatch_lit_nil p ps Hst Hm).
Qed.

Lemma stuck_lit : forall p ps s ss,
  Nat.eqb p b_star = false ->
  Nat.eqb p b_qmark || Nat.eqb p s = false ->
  ~(gmatch (p :: ps) (s :: ss)).
Proof.
  intros p ps s ss Hst Ho Hm.
  destruct (gmatch_one_step p ps s ss Hst Hm) as [_ [Hq|Hl]].
  - destruct (orb_false_elim _ _ Ho) as [H1 _].
    apply Nat.eqb_eq in Hq; rewrite Hq in H1; rewrite Nat.eqb_refl in H1; discriminate.
  - destruct (orb_false_elim _ _ Ho) as [_ H2].
    apply Nat.eqb_eq in Hl; rewrite Hl in H2; rewrite Nat.eqb_refl in H2; discriminate.
Qed.

(* ── §4.3.11 completeness of the scan loop ── *)
Theorem glob_it_complete : forall f pat str bk,
  cinv pat str bk -> state_bound pat str bk <= f -> glob_it f pat str bk = true.
Proof.
  induction f as [| g IH]; intros pat str bk Hc Hb.
  { exfalso.
    assert (Hp : 0 < state_bound pat str bk) by apply bound_pos.
    lia. }
  { (* the loop's sites, taken in the order its code tests them *)
    revert Hc Hb; destruct pat as [| p ps]; cbn [glob_it]; intros Hc Hb.
    { (* pattern exhausted: accept outright, retry the cell, or fail *)
      revert Hc Hb; destruct str as [| s ss]; cbn [glob_it]; intros Hc Hb.
      { reflexivity. }
      { revert Hc Hb; destruct bk as [q|]; cbn [glob_it]; intros Hc Hb.
        { revert Hc Hb; destruct q as [bps bstr]; destruct bstr as [| x rstr];
            cbn [glob_it]; intros Hc Hb.
          { exfalso.
            apply (cinv_nil_cell [] (s :: ss) bps Hc (stuck_nil s ss)). }
          { apply IH.
            { apply (cinv_drain [] (s :: ss) bps x rstr Hc (stuck_nil s ss)). }
            assert (Hlt := bound_drain [] (s :: ss) bps x rstr); fuel_norm; nia. }
        }
        { exfalso.
          apply (stuck_nil s ss); exact (cinv_none_inv [] (s :: ss) Hc). }
      }
    }
    { revert Hc Hb; destruct (Nat.eqb p b_star) eqn:Ep;
        [ apply Nat.eqb_eq in Ep; subst p | ]; cbn [glob_it]; intros Hc Hb.
      { (* a new star: install the cell here and keep scanning *)
        apply IH.
        { exact (cinv_install ps str bk Hc). }
        assert (Hlt := bound_install ps str bk Hc); fuel_norm; nia. }
      { revert Hc Hb; destruct str as [| s ss]; cbn [glob_it]; intros Hc Hb.
        { (* literal against an exhausted string *)
          revert Hc Hb; destruct bk as [q|]; cbn [glob_it]; intros Hc Hb.
          { revert Hc Hb; destruct q as [bps bstr]; destruct bstr as [| x rstr];
              cbn [glob_it]; intros Hc Hb.
            { exfalso.
              apply (cinv_nil_cell (p :: ps) [] bps Hc (stuck_lit_nil p ps Ep)). }
            { apply IH.
              { apply (cinv_drain (p :: ps) [] bps x rstr Hc
                         (stuck_lit_nil p ps Ep)). }
              assert (Hlt := bound_drain (p :: ps) [] bps x rstr); fuel_norm; nia. }
          }
          { exfalso.
            apply (stuck_lit_nil p ps Ep); exact (cinv_none_inv (p :: ps) [] Hc). }
        }
        { revert Hc Hb; destruct (Nat.eqb p b_qmark || Nat.eqb p s) eqn:Eq;
            cbn [glob_it]; intros Hc Hb.
          { (* the byte is consumed: step forward, cell untouched *)
            apply IH.
            { apply (cinv_forward p ps s ss bk Hc Ep).
              apply (proj1 (orb_true_iff _ _)) in Eq. exact Eq. }
            assert (Hlt := bound_step p ps s ss bk); fuel_norm; nia. }
          { (* mismatch: hand the run one more byte to the star *)
            revert Hc Hb; destruct bk as [q|]; cbn [glob_it]; intros Hc Hb.
            { revert Hc Hb; destruct q as [bps bstr]; destruct bstr as [| x rstr];
                cbn [glob_it]; intros Hc Hb.
              { exfalso.
                apply (cinv_nil_cell (p :: ps) (s :: ss) bps Hc
                         (stuck_lit p ps s ss Ep Eq)). }
              { apply IH.
                { apply (cinv_drain (p :: ps) (s :: ss) bps x rstr Hc
                           (stuck_lit p ps s ss Ep Eq)). }
                assert (Hlt := bound_drain (p :: ps) (s :: ss) bps x rstr);
                fuel_norm; nia. }
            }
            { exfalso.
              apply (stuck_lit p ps s ss Ep Eq);
              exact (cinv_none_inv (p :: ps) (s :: ss) Hc). }
          }
        }
      }
    }
  }
Qed.

(* ── §4.3.12 top level, and the two-sided agreement with the reference matcher ── *)
(* The theorem is stated for every fuel at least the bound, so it already
   carries its own monotonicity: no separate fuel-lifting lemma is needed. *)
Corollary glob_iter_complete_at : forall f pat str,
  fuel_top pat str <= f -> gmatch pat str -> glob_iter f pat str = true.
Proof.
  intros f pat str Hle Hm; unfold glob_iter, fuel_top.
  apply glob_it_complete; [ apply ci_none; exact Hm | exact Hle ].
Qed.

Theorem glob_iter_complete : forall pat str,
  gmatch pat str -> glob_iter (fuel_top pat str) pat str = true.
Proof.
  intros pat str Hm; exact (glob_iter_complete_at _ pat str (Nat.le_refl _) Hm).
Qed.

Theorem glob_iter_iff_glob : forall pat str,
  glob_iter (fuel_top pat str) pat str = true
  <-> glob (S (length pat + length str)) pat str = true.
Proof.
  intros pat str; split; intro H.
  - exact (glob_iter_accepts_glob (fuel_top pat str) pat str H).
  - apply glob_true_gmatch in H.
    exact (glob_iter_complete pat str H).
Qed.

(* §7 match_any_iter completeness: written after the loop's own proof lands *)

(* the scan's product dominates the reference matcher's linear budget *)
Lemma prod_ge : forall n m, n <= n * S m.
Proof.
  intros n m; induction n as [| k IH]; [ cbn [Nat.mul]; lia | ].
  cbn [Nat.mul]; lia.
Qed.

(* ── §4.3.13 the branch matcher: the same two-sided agreement ── *)
Lemma fuel_top_dom : forall pat str, S (length pat + length str) <= fuel_top pat str.
Proof.
  intros pat str; unfold fuel_top; fuel_norm.
  apply (Nat.le_trans (S (length pat + length str))
                      (S (length pat + length str) * S (length str))).
  - apply prod_ge.
  - lia.
Qed.

Corollary match_any_sound : forall f pats scrut,
  match_any f pats scrut = true ->
  exists p, In p pats /\ gmatch p scrut.
Proof.
  induction f as [| g IH];
    [ intros pats scrut H; cbn [match_any] in H; discriminate | ].
  intros pats scrut H; revert H; cbn [match_any]; destruct pats as [| q rs]; cbn;
    [ intros H; discriminate
    | intros H; apply orb_true_iff in H; destruct H as [Hg|Hi];
        [ exists q; split; [ left; reflexivity | apply (glob_true_gmatch g); exact Hg ]
        | apply IH in Hi; destruct Hi as [p [Hin Hgm]];
          exists p; split; [ right; exact Hin | exact Hgm ] ] ].
Qed.

Lemma match_any_complete_at : forall f b pats scrut,
  f = b + length pats ->
  (forall p, In p pats -> fuel_top p scrut <= b) ->
  (exists p, In p pats /\ gmatch p scrut) ->
  match_any f pats scrut = true.
Proof.
  induction f as [| g IH]; intros b pats scrut Hf Htop Hex.
  - destruct pats as [| q rs];
      [ destruct Hex as [p [Hin _]]; exfalso; cbn [In] in Hin; exact Hin
      | exfalso; cbn [length] in Hf; lia ].
  - destruct pats as [| q rs];
      [ destruct Hex as [p [Hin _]]; exfalso; cbn [In] in Hin; exact Hin | ].
    cbn [match_any]; destruct Hex as [p [Hin Hgm]].
    cbn [In] in Hin; destruct Hin as [Heq|Hin'].
    + apply orb_true_iff; left; rewrite <- Heq in Hgm.
      cbn [length] in Hf.
      assert (Hb : fuel_top q scrut <= b) by (apply Htop; left; reflexivity).
      assert (Hd := fuel_top_dom q scrut).
      unfold fuel_top in Hb, Hd; fuel_norm.
      apply (gmatch_glob q scrut Hgm g); lia.
    + apply orb_true_iff; right.
      cbn [length] in Hf.
      apply (IH b rs scrut);
        [ lia
        | intros r Hinr; apply Htop; right; exact Hinr
        | exists p; split; [ exact Hin' | exact Hgm ] ].
Qed.

(* ── §4.3.13b the EXACT fuel window in which L2 `match_any` decides ──

   `match_any_complete_at` above is stated with the loop's budget (`fuel_top`), which
   is what `match_any_iter` needs; it is NOT what the tree recursion needs.  L2's tree
   is the *cheaper* of the two: pattern number i of a branch is globbed at fuel
   `f - 1 - i`, so the decisive threshold is the linear `S (len p + len w)` per pattern
   with one unit of fuel spent per pattern position.  The machine needs exactly this
   shape (it has `f`, not a chosen `b`), and the gap matters: at command fuel 4 a
   2-byte pattern is decisive for `match_any` while `fuel_top` demands 29 — so a
   rewiring that required `fuel_top <= f` would refuse almost every real `case`.
   `branch_decisive` spells the threading out; `match_any_complete_decisive` is the
   completeness half, and together with `match_any_sound` (no hypothesis) it says: at a
   `branch_decisive` fuel, `match_any f` decides the existential `gmatch` exactly. *)

(* The list comes FIRST so the guard checker recurses on it: with the fuel first Coq
   selects {struct f}, and then `branch_decisive f [] w` is stuck whenever `f` is a
   variable, which is exactly the shape the machine's proofs need to reduce. *)
Fixpoint branch_decisive (pats : list text) (f : nat) (w : text) : Prop :=
  match pats with
  | [] => True
  | p :: r =>
      match f with
      | 0 => False
      | S g => S (length p + length w) <= g /\ branch_decisive r g w
      end
  end.

Lemma match_any_complete_decisive : forall pats f w,
  branch_decisive pats f w ->
  (exists p, In p pats /\ gmatch p w) ->
  match_any f pats w = true.
Proof.
  induction pats as [ | p r IH ]; intros f w Hbd Hex.
  - cbn [In] in Hex. destruct Hex as [q [Hin Hgm]]; contradiction.
  - destruct f as [ | g ]; [ cbn [branch_decisive] in Hbd; contradiction | ].
    cbn [branch_decisive] in Hbd; destruct Hbd as [Hle Htl].
    cbn [match_any]. apply orb_true_iff.
    destruct Hex as [q [Hin Hgm]]; cbn [In] in Hin.
    destruct Hin as [Heq | Hin'].
    + left. subst q. exact (gmatch_glob p w Hgm g Hle).
    + right. apply IH; [ exact Htl | exists q; split; [ exact Hin' | exact Hgm ] ].
Qed.

Theorem match_any_iter_complete : forall f pats scrut b,
  (forall p, In p pats -> fuel_top p scrut <= b) ->
  b + length pats <= f ->
  (exists p, In p pats /\ gmatch p scrut) ->
  match_any_iter f pats scrut = true.
Proof.
  induction f as [| g IH].
  - intros pats scrut b Htop Hf Hex; cbn [match_any_iter].
    destruct pats as [| q rs];
      [ destruct Hex as [p [Hin _]]; exfalso; cbn [In] in Hin; exact Hin
      | exfalso; cbn [length] in Hf; lia ].
  - intros pats scrut b Htop Hf Hex; revert Hf Hex.
    destruct pats as [| q rs]; cbn [match_any_iter];
      [ cbn [length]; intros Hf [p [Hin _]]; exfalso; cbn [In] in Hin; exact Hin | ].
    intros Hf [p [Hin Hgm]]; destruct (glob_iter g q scrut) eqn:E.
    + reflexivity.
    + apply (IH rs scrut b).
      * intros r Hinr; apply Htop; right; exact Hinr.
      * cbn [length] in Hf; lia.
      * cbn [In] in Hin; destruct Hin as [Heq|Hin'].
        -- exfalso; rewrite <- Heq in Hgm; cbn [length] in Hf.
           assert (Hb : fuel_top q scrut <= b) by (apply Htop; left; reflexivity).
           assert (Hle : fuel_top q scrut <= g) by lia.
           assert (Ht : glob_iter g q scrut = true)
             by (apply (glob_iter_complete_at g q scrut Hle Hgm)).
           rewrite Ht in E; discriminate E.
        -- exists p; split; [ exact Hin' | exact Hgm ].
Qed.

Theorem match_any_iter_iff_match_any : forall b pats scrut,
  (forall p, In p pats -> fuel_top p scrut <= b) ->
  match_any_iter (b + length pats) pats scrut = true <->
  match_any (b + length pats) pats scrut = true.
Proof.
  intros b pats scrut Htop; split; intro H.
  - apply match_any_iter_sound in H; destruct H as [p [Hin Hgm]].
    apply (match_any_complete_at _ b pats scrut eq_refl Htop).
    exists p; split; [ exact Hin | exact Hgm ].
  - apply match_any_sound in H; destruct H as [p [Hin Hgm]].
    apply (match_any_iter_complete _ pats scrut b Htop (Nat.le_refl _)).
    exists p; split; [ exact Hin | exact Hgm ].
Qed.

(* ── §4.3.14 what the law costs the L3 budget — the sizing of GLOB_FUEL ──

   §4.3.11/12 give completeness AT fuel_top pat str, so the constant the machine has
   to carry is fuel_top's worst case over well-formed words.  Both words are capped
   at MAX_WORD by sh_jpl's `wf_bword`, which is exactly the hypothesis below.

   The bound is proved by MONOTONICITY of scan in each length plus the definitional
   identity `fuel_top MAX_WORD MAX_WORD = GLOB_FUEL`; no numeral is evaluated and no
   132 353-node Peano term is ever built, so the sizing stays valid if MAX_WORD
   changes.  sh_jpl.v §1 defines GLOB_FUEL to be this worst case, and the two
   corollaries at the bottom are what JPL.5-A.6 (#35) consumes: with the raised
   budget the machine can hand out MAX_FUEL and the loop is guaranteed to FIND every
   real match, not merely to reject the fake ones. *)

Definition fuel_top_nat (p s : nat) : nat := scan p s + p + s.

Lemma fuel_top_as_nat : forall pat str,
  fuel_top pat str = fuel_top_nat (length pat) (length str).
Proof. reflexivity. Qed.

Lemma scan_mono : forall a b c d, a <= c -> b <= d -> scan a b <= scan c d.
Proof.
  intros a b c d H1 H2; unfold scan; apply Nat.mul_le_mono; lia.
Qed.

Lemma fuel_top_nat_mono : forall p s p' s',
  p <= p' -> s <= s' -> fuel_top_nat p s <= fuel_top_nat p' s'.
Proof.
  intros p s p' s' H1 H2; unfold fuel_top_nat.
  apply Nat.add_le_mono.
  - apply Nat.add_le_mono.
    + apply scan_mono; assumption.
    + exact H1.
  - exact H2.
Qed.

(* GLOB_FUEL is defined in L3 as this very expression, so the top case is
   definitional — the constant cannot drift away from the law it is sized from. *)
Lemma fuel_top_nat_at_MAX_WORD : fuel_top_nat MAX_WORD MAX_WORD <= GLOB_FUEL.
Proof.
  unfold fuel_top_nat, scan, GLOB_FUEL; apply Nat.le_refl.
Qed.

Theorem fuel_top_le_glob_fuel : forall pat str,
  length pat <= MAX_WORD -> length str <= MAX_WORD ->
  fuel_top pat str <= GLOB_FUEL.
Proof.
  intros pat str Hp Hs; rewrite fuel_top_as_nat.
  apply (Nat.le_trans (fuel_top_nat (length pat) (length str))
                      (fuel_top_nat MAX_WORD MAX_WORD) GLOB_FUEL).
  - apply fuel_top_nat_mono; assumption.
  - apply fuel_top_nat_at_MAX_WORD.
Qed.

(* The machine's own budget covers it: MAX_FUEL = GLOB_FUEL + its step allowance. *)
Lemma glob_fuel_le_max_fuel : GLOB_FUEL <= MAX_FUEL.
Proof. exact (proj2 cap_fuel_order). Qed.

Corollary glob_iter_glob_fuel_complete : forall pat str,
  length pat <= MAX_WORD -> length str <= MAX_WORD -> gmatch pat str ->
  glob_iter GLOB_FUEL pat str = true.
Proof.
  intros pat str Hp Hs Hm.
  apply (glob_iter_complete_at GLOB_FUEL pat str).
  - apply fuel_top_le_glob_fuel; assumption.
  - exact Hm.
Qed.

Corollary glob_iter_max_fuel_complete : forall pat str,
  length pat <= MAX_WORD -> length str <= MAX_WORD -> gmatch pat str ->
  glob_iter MAX_FUEL pat str = true.
Proof.
  intros pat str Hp Hs Hm.
  apply (glob_iter_complete_at MAX_FUEL pat str).
  - apply (Nat.le_trans (fuel_top pat str) GLOB_FUEL MAX_FUEL);
      [ apply fuel_top_le_glob_fuel; assumption | apply glob_fuel_le_max_fuel ].
  - exact Hm.
Qed.

(* The branch matcher's call shape: one branch budget plus one step per branch. *)
Corollary match_any_iter_in_budget : forall pats scrut,
  length scrut <= MAX_WORD ->
  (forall p, In p pats -> length p <= MAX_WORD) ->
  (exists p, In p pats /\ gmatch p scrut) ->
  match_any_iter (GLOB_FUEL + length pats) pats scrut = true.
Proof.
  intros pats scrut Hs Hp Hex.
  apply (match_any_iter_complete _ pats scrut GLOB_FUEL).
  - intros p Hin; apply fuel_top_le_glob_fuel; [ apply (Hp p Hin) | exact Hs ].
  - apply Nat.le_refl.
  - exact Hex.
Qed.

(* ═══════════════════════════════════════════════════════════════════
   §4.3.15 the machine's branch guard: the LEAST fuel at which L2 decides,
   computed

   §4.3.13b says `match_any` decides a branch exactly at a `branch_decisive` fuel,
   and §4.3.14 says `match_any_iter` answers exactly at its own `fuel_top` budget.
   A machine that wants the answer of L2 while running the LOOP therefore needs one
   decidable predicate: is the site fuel decisive?  `branch_need pats w` is that
   predicate's exact threshold, and it is not an over-approximation:

     branch_decisive pats f w  ->  branch_need pats w <= f        (necessary)
     branch_need pats w <= f   ->  branch_decisive pats f w        (sufficient)

   so `f = branch_need pats w - 1` is genuinely too poor to decide the branch — the
   bound is minimal by the first half, not merely convenient.  Closed form: pattern
   number i is globbed at fuel `f - 1 - i`, so the branch needs
   `max_i (|p_i| + |w| + i + 2)`, which is what the forward scan computes.

   The two sizing facts the emitter needs are at the bottom: the threshold is linear
   in the caps (`<= S (MAX_LIST + 2*MAX_WORD)` = 1537), so the comparison itself can
   never overflow a uint32, and `branch_guardb` — the boolean the kernel evaluates —
   is exactly `decisive AND every word in budget`, which is what makes
   `match_any_iter (GLOB_FUEL + length pats)` agree with `match_any g` unconditionally
   at a passing guard (branch_guardb_match).  A failing guard is the machine's
   saturate-to-error edge, not a wrong answer.
   ═══════════════════════════════════════════════════════════════════ *)

(* The longest pattern of a branch, as a FORWARD loop rather than a fold_right: the
   emitter lowers exactly this shape, and as a Fixpoint its two computational laws
   reduce definitionally so the sizing proofs below can rewrite them. *)
Fixpoint max_pat_len (pats : list text) : nat :=
  match pats with
  | [] => 0
  | p :: r => Nat.max (length p) (max_pat_len r)
  end.

Lemma max_pat_len_cons : forall (p : text) (r : list text),
  max_pat_len (p :: r) = Nat.max (length p) (max_pat_len r).
Proof. reflexivity. Qed.

Lemma max_pat_len_le_all : forall pats m,
  (forall p, In p pats -> length p <= m) -> max_pat_len pats <= m.
Proof.
  induction pats as [ | q r IH ]; intros m Hle.
  - cbn [max_pat_len]; lia.
  - rewrite max_pat_len_cons. apply Nat.max_lub.
    + apply (Hle q); cbn [In]; left; reflexivity.
    + apply IH; intros p Hin; apply Hle; right; exact Hin.
Qed.

Fixpoint branch_need (pats : list text) (w : text) : nat :=
  match pats with
  | [] => 0
  | p :: r => Nat.max (S (S (length p + length w))) (S (branch_need r w))
  end.

Lemma branch_need_cons : forall (p : text) (r : list text) w,
  branch_need (p :: r) w = Nat.max (S (S (length p + length w))) (S (branch_need r w)).
Proof. reflexivity. Qed.

(* MINIMALITY: no fuel below `branch_need` decides the branch. *)
Lemma branch_decisive_need : forall pats w f,
  branch_decisive pats f w -> branch_need pats w <= f.
Proof.
  induction pats as [ | p r IH ]; intros w f Hbd; cbn [branch_decisive] in Hbd.
  - cbn [branch_need]; lia.
  - destruct f as [ | g ]; [ contradiction | ].
    destruct Hbd as [Hle Htl].
    rewrite branch_need_cons. apply Nat.max_lub.
    + lia.
    + specialize (IH w g Htl). lia.
Qed.

Lemma branch_need_decisive : forall pats w f,
  branch_need pats w <= f -> branch_decisive pats f w.
Proof.
  induction pats as [ | p r IH ]; intros w f Hn; cbn [branch_decisive].
  - exact I.
  - destruct f as [ | g ]; rewrite branch_need_cons in Hn.
    + assert (Ha : S (S (length p + length w)) <= Nat.max (S (S (length p + length w)))
                                                       (S (branch_need r w)))
      by apply Nat.le_max_l.
      lia.
    + assert (Ha : S (S (length p + length w)) <= Nat.max (S (S (length p + length w)))
                                                       (S (branch_need r w)))
      by apply Nat.le_max_l.
      assert (Hb : S (branch_need r w) <= Nat.max (S (S (length p + length w)))
                                              (S (branch_need r w)))
      by apply Nat.le_max_r.
      split; [ lia | apply IH; lia ].
Qed.

(* the threshold is linear in the three sizes it reads *)
Lemma branch_need_bound : forall pats w,
  branch_need pats w <= S (length pats + max_pat_len pats + length w).
Proof.
  induction pats as [ | p r IH ]; intros w.
  - cbn [branch_need max_pat_len length]. lia.
  - rewrite branch_need_cons, max_pat_len_cons. cbn [length]. apply Nat.max_lub.
    + assert (Hp : length p <= Nat.max (length p) (max_pat_len r)) by apply Nat.le_max_l.
      lia.
    + specialize (IH w).
      assert (Hm : max_pat_len r <= Nat.max (length p) (max_pat_len r)) by apply Nat.le_max_r.
      lia.
Qed.

(* So with the words in budget the guard's own arithmetic is bounded by a constant
   three orders of magnitude below 2^31: the emitted comparison cannot overflow. *)
Lemma branch_need_in_caps : forall pats w,
  length pats <= MAX_LIST ->
  (forall p, In p pats -> length p <= MAX_WORD) ->
  length w <= MAX_WORD ->
  branch_need pats w <= S (MAX_LIST + MAX_WORD + MAX_WORD).
Proof.
  intros pats w Hn Hp Hw.
  apply Nat.le_trans with (S (length pats + max_pat_len pats + length w)).
  - apply branch_need_bound.
  - pose proof (max_pat_len_le_all pats MAX_WORD Hp). lia.
Qed.

(* the guard threshold fits the machine's fuel ceiling: 1537 vs 136 449, checked by
   the VM rather than by building Peano numerals. *)
Lemma caps_under_max_fuel : S (MAX_LIST + MAX_WORD + MAX_WORD) <= MAX_FUEL.
Proof.
  unfold MAX_LIST, MAX_WORD, MAX_FUEL, GLOB_FUEL.
  apply Nat.leb_le. vm_compute. reflexivity.
Qed.

Lemma branch_need_le_max_fuel : forall pats w,
  length pats <= MAX_LIST ->
  (forall p, In p pats -> length p <= MAX_WORD) ->
  length w <= MAX_WORD ->
  branch_need pats w <= MAX_FUEL.
Proof.
  intros pats w Hn Hp Hw.
  assert (H1 := branch_need_in_caps pats w Hn Hp Hw).
  assert (H2 := caps_under_max_fuel). lia.
Qed.

(* the boolean the kernel evaluates: decisive AND everything in budget *)
Definition branch_guardb (g : nat) (pats : list text) (w : text) : bool :=
  andb (Nat.leb (branch_need pats w) g)
       (andb (Nat.leb (length w) MAX_WORD)
             (andb (Nat.leb (length pats) MAX_LIST)
                   (forallb (fun p => Nat.leb (length p) MAX_WORD) pats))).

Lemma branch_guardb_ok : forall g pats w, branch_guardb g pats w = true ->
  branch_decisive pats g w /\ length w <= MAX_WORD
                  /\ length pats <= MAX_LIST
                  /\ (forall p, In p pats -> length p <= MAX_WORD).
Proof.
  intros g pats w Hg; cbn [branch_guardb] in Hg.
  apply andb_true_iff in Hg. destruct Hg as [H1 H2].
  apply andb_true_iff in H2. destruct H2 as [Hw H3].
  apply andb_true_iff in H3. destruct H3 as [Hn Hfb].
  apply Nat.leb_le in H1. apply Nat.leb_le in Hw. apply Nat.leb_le in Hn.
  rewrite forallb_forall in Hfb.
  split; [ | split; [ | split ] ].
  - apply branch_need_decisive, H1.
  - exact Hw.
  - exact Hn.
  - intros p Hin. apply Nat.leb_le. exact (Hfb p Hin).
Qed.

(* THE point of the section: at a passing guard the loop and L2 answer identically,
   with no hypothesis on the shapes of the words beyond the caps. *)
Lemma branch_guardb_match : forall g pats w,
  branch_guardb g pats w = true ->
  match_any_iter (GLOB_FUEL + length pats) pats w = match_any g pats w.
Proof.
  intros g pats w Hg.
  assert (OK := branch_guardb_ok g pats w Hg).
  destruct OK as [Hdec [Hw [_ Hcaps]]].
  destruct (match_any g pats w) eqn:Em.
  - apply match_any_sound in Em; destruct Em as [p [Hin Hgm]].
    apply (match_any_iter_in_budget pats w Hw Hcaps).
    exists p; split; [ exact Hin | exact Hgm ].
  - destruct (match_any_iter (GLOB_FUEL + length pats) pats w) eqn:El; [ | reflexivity ].
    apply match_any_iter_sound in El; destruct El as [p [Hin Hgm]].
    assert (Htrue : match_any g pats w = true).
    { apply match_any_complete_decisive;
        [ exact Hdec | exists p; split; [ exact Hin | exact Hgm ] ]. }
    rewrite Htrue in Em. discriminate.
Qed.

(* the guard in the other direction: what the machine has to show to never saturate *)
Lemma branch_guardb_true_of_caps : forall g pats w,
  length pats <= MAX_LIST ->
  (forall p, In p pats -> length p <= MAX_WORD) ->
  length w <= MAX_WORD ->
  branch_need pats w <= g ->
  branch_guardb g pats w = true.
Proof.
  intros g pats w Hn Hp Hw Hneed.
  unfold branch_guardb; repeat (apply andb_true_iff; split).
  - apply Nat.leb_le, Hneed.
  - apply Nat.leb_le, Hw.
  - apply Nat.leb_le, Hn.
  - apply forallb_forall; intros p Hin. apply Nat.leb_le, (Hp p Hin).
Qed.

(* BUDGET ADEQUACY: the worst branch this layer can be asked to decide needs 1537
   fuel units, so a case site entered at MAX_FUEL always passes its guard.  The
   machine's ceiling is therefore ample for the scan by three orders of magnitude,
   and the guard fires only where L2's own answer is fuel-ambiguous. *)
Corollary branch_guardb_at_max_fuel : forall pats w,
  length pats <= MAX_LIST ->
  (forall p, In p pats -> length p <= MAX_WORD) ->
  length w <= MAX_WORD ->
  branch_guardb MAX_FUEL pats w = true.
Proof.
  intros pats w Hn Hp Hw.
  apply (branch_guardb_true_of_caps MAX_FUEL pats w Hn Hp Hw).
  apply (branch_need_le_max_fuel pats w Hn Hp Hw).
Qed.

(* the loop budget the rewired machine passes, checked against the ceiling: the
   4096-unit allowance inside MAX_FUEL covers the worst case MAX_LIST of the
   `+ length pats` term, so the scan budget the kernel computes is in range. *)
Lemma scan_budget_le_max_fuel : forall (pats : list text),
  length pats <= MAX_LIST -> GLOB_FUEL + length pats <= MAX_FUEL.
Proof.
  intros pats Hn. unfold MAX_LIST in Hn. unfold MAX_FUEL. lia.
Qed.

(* ═══════════════════════════════════════════════════════════════════
   §5  Iterative environment — the mandatory Coq rewrite (5-A.2)

   sh_concrete's `getv`/`setv` walk the association list with structural
   recursion, and `setv` conses on the way back out.  Neither is a loop, so the
   emitter would have to lower a recursion it cannot bound.  Over the bounded
   array representation of sh_jpl (`benv` = pairs + length, capacity MAX_ENV) both
   operations are a single FORWARD scan:

     getv  — compare the cursor's name, return its value or advance;
     setv  — compare, and either write at the cursor (replace) or, at the end,
             write one slot past it (append).

   `getv_it` is that scan.  `setv_it` is the same scan carrying the visited
   prefix in `acc` (reversed, exactly what an array holds implicitly); the splice
   uses `rev_append`, itself a tail loop, so no non-tail append survives.  `None`
   is the saturation marker: fuel exhausted before the scan finished, which the
   caller reads as BLimit.

   Agreement is proved, not sampled: `getv_it_agree` / `setv_it_agree` hold for
   EVERY input whose length fits the fuel, and `be_getv` / `be_setv` — the
   array-level API the kernel calls — are proved equal to sh_jpl's reference
   `benv_getv` / `benv_setv`.  The capacity law `be_setv_refuses_at_capacity`
   pins the saturate-to-error boundary at exactly MAX_ENV.
   ═══════════════════════════════════════════════════════════════════ *)

Fixpoint getv_it (f : nat) (k : text) (m : list (text * text)) : option text :=
  match f with
  | 0 => None
  | S f' =>
      match m with
      | [] => None
      | (k', v) :: r => if teqb k k' then Some v else getv_it f' k r
      end
  end.

Fixpoint setv_it (f : nat) (k v : text) (acc m : list (text * text))
  : option (list (text * text)) :=
  match f with
  | 0 => None
  | S f' =>
      match m with
      | [] => Some (rev_append acc [(k, v)])
      | (k', v') :: r =>
          if teqb k k' then Some (rev_append acc ((k, v) :: r))
          else setv_it f' k v ((k', v') :: acc) r
      end
  end.

(* Exhausted fuel reports "not found" / saturation — never a wrong value. *)
Lemma getv_it_exhaust : forall k m, getv_it 0 k m = None.
Proof. reflexivity. Qed.

Lemma setv_it_exhaust : forall k v acc m, setv_it 0 k v acc m = None.
Proof. reflexivity. Qed.

(* §5.1 agreement with the concrete reference scans *)

Lemma getv_it_agree : forall m f k, length m <= f -> getv_it f k m = getv k m.
Proof.
  induction m as [| [k' v'] m IH]; intros f k Hle.
  - cbn [length] in Hle. destruct f; reflexivity.
  - cbn [length] in Hle. destruct f as [| f']; [ lia |].
    cbn [getv_it getv].
    destruct (teqb k k') eqn:E; [ reflexivity | apply IH; lia ].
Qed.

(* one forward step of the accumulator: the cursor's pair moves to the splice *)
Lemma rev_append_cons_l : forall (p : text * text) acc xs,
  rev_append (p :: acc) xs = rev_append acc (p :: xs).
Proof. reflexivity. Qed.

Lemma setv_it_agree : forall m f k v acc,
  length m < f -> setv_it f k v acc m = Some (rev_append acc (setv k v m)).
Proof.
  induction m as [| [k' v'] m IH]; intros f k v acc Hlt.
  - cbn [length] in Hlt. destruct f as [| f']; [ lia |].
    cbn [setv_it setv]. reflexivity.
  - cbn [length] in Hlt. destruct f as [| f']; [ lia |].
    cbn [setv_it].
    destruct (teqb k k') eqn:E.
    + cbn [setv]. rewrite E. reflexivity.
    + rewrite (IH f' k v ((k', v') :: acc) ltac:(lia)).
      cbn [setv]. rewrite E, rev_append_cons_l. reflexivity.
Qed.

(* The converse reading, and the one the machine actually needs: a SUCCESSFUL scan
   is faithful whatever the fuel was.  No length hypothesis — the loop either
   reaches the cursor or it returns None, so `Some x` already carries the evidence
   that it walked the whole list.  This is what lets a rewired `step` site guard on
   nothing but the saturation marker. *)
Lemma setv_it_some_agree : forall f k v acc m x,
  setv_it f k v acc m = Some x -> x = rev_append acc (setv k v m).
Proof.
  intros f k v acc m; revert f k v acc.
  induction m as [ | [k' v'] m IH ]; intros f k v acc x H.
  - destruct f as [ | f']; cbn [setv_it] in H.
    + discriminate.
    + injection H as E; subst x; reflexivity.
  - destruct f as [ | f']; cbn [setv_it] in H.
    + discriminate.
    + destruct (teqb k k') eqn:E.
      * cbn [setv]. rewrite E. injection H as Ex; subst x; reflexivity.
      * specialize (IH f' k v ((k', v') :: acc) x H).
        cbn [setv]. rewrite E.
        rewrite <- rev_append_cons_l. exact IH.
Qed.

(* §5.2 the array-level API the extracted kernel calls *)

Definition be_getv (k : text) (e : benv) : option text :=
  getv_it (be_len e) k (be_pairs e).

Definition be_setv (k v : text) (e : benv) : bres benv :=
  match setv_it (S (be_len e)) k v [] (be_pairs e) with
  | Some m => if Nat.leb (length m) MAX_ENV then BOk (BE m (length m)) else BLimit
  | None    => BLimit
  end.

Lemma be_getv_agree : forall e k, wf_benv e -> be_getv k e = benv_getv k e.
Proof.
  intros e k [Hlen Hcap]. unfold be_getv, benv_getv.
  rewrite (getv_it_agree (be_pairs e) (be_len e) k ltac:(rewrite <- Hlen; lia)).
  reflexivity.
Qed.

Lemma be_setv_agree : forall e k v, wf_benv e -> be_setv k v e = benv_setv k v e.
Proof.
  intros e k v [Hlen Hcap]. unfold be_setv.
  rewrite (setv_it_agree (be_pairs e) (S (be_len e)) k v []
              ltac:(rewrite Hlen; lia)).
  cbn [rev_append]. unfold benv_setv. reflexivity.
Qed.

(* An accepted update is well-formed; a refused one leaves no partial state. *)
Lemma be_setv_wf : forall k v e,
  match be_setv k v e with
  | BOk e' => wf_benv e'
  | BLimit => True
  end.
Proof.
  intros k v e. unfold be_setv.
  destruct (setv_it (S (be_len e)) k v [] (be_pairs e)) as [m |].
  - destruct (Nat.leb (length m) MAX_ENV) eqn:L.
    + unfold wf_benv. split; [ reflexivity | apply Nat.leb_le; exact L ].
    + exact I.
  - exact I.
Qed.

(* A key that is absent really does add one cell, so at capacity the update is
   refused rather than silently dropped. *)
Lemma setv_length_absent : forall m k v, getv k m = None ->
  length (setv k v m) = S (length m).
Proof.
  induction m as [| [k' v'] m IH]; intros k v H.
  - cbn [setv length]. reflexivity.
  - destruct (teqb k k') eqn:E.
    + cbn [getv] in H. rewrite E in H. discriminate H.
    + cbn [getv] in H. rewrite E in H. specialize (IH k v H).
      cbn [setv]. rewrite E. cbn [length]. lia.
Qed.

Lemma be_setv_refuses_at_capacity : forall e k v, wf_benv e -> be_len e = MAX_ENV ->
  getv k (be_pairs e) = None -> be_setv k v e = BLimit.
Proof.
  intros e k v [Hlen Hcap] Hcap2 Hnone.
  unfold be_setv.
  rewrite (setv_it_agree (be_pairs e) (S (be_len e)) k v []
              ltac:(rewrite Hlen; lia)).
  cbn [rev_append].
  rewrite (setv_length_absent (be_pairs e) k v ltac:(exact Hnone)).
  rewrite <- Hlen, Hcap2.
  destruct (Nat.leb (S (S MAX_ENV)) MAX_ENV) eqn:L; [ | reflexivity ].
  apply Nat.leb_le in L. lia.
Qed.

(* Below capacity the scan always has enough fuel, so the update never saturates. *)
Lemma be_setv_admits : forall e k v, wf_benv e -> be_len e < MAX_ENV ->
  { e' | be_setv k v e = BOk e' }.
Proof.
  intros e k v Hw Hlt.
  rewrite (be_setv_agree e k v Hw).
  exact (benv_setv_fits k v e Hw Hlt).
Qed.

(* Write-then-read through the tail loops, entirely inside the bounded API. *)
Lemma be_getv_be_setv_same : forall e k v, wf_benv e -> be_len e < MAX_ENV ->
  match be_setv k v e with
  | BOk e' => be_getv k e'
  | BLimit => None
  end = Some v.
Proof.
  intros e k v [Hlen Hcap] Hlt.
  rewrite (be_setv_agree e k v (conj Hlen Hcap)).
  unfold benv_setv.
  destruct (Nat.leb (length (setv k v (be_pairs e))) MAX_ENV) eqn:L.
  - unfold be_getv. cbn [be_len be_pairs].
    rewrite (getv_it_agree (setv k v (be_pairs e))
                           (length (setv k v (be_pairs e))) k ltac:(lia)).
    apply getv_set_same.
  - exfalso. apply Nat.leb_gt in L.
    pose proof (setv_length_le k v (be_pairs e)) as SL.
    rewrite <- Hlen in SL. lia.
Qed.

(* ── §5.3 byte-level witnesses (mnemonics: 97 a, 98 b, 99 c, 100 d, 101 e) ── *)

Example getv_it_hit :
  getv_it 4 [97] [(([98], [99])); (([97], [100]))] = Some [100].
Proof. reflexivity. Qed.

Example getv_it_miss :
  getv_it 4 [97] [(([98], [99]))] = None.
Proof. reflexivity. Qed.

Example getv_it_no_fuel :
  getv_it 1 [98] [(([97], [100])); (([98], [99]))] = None.
Proof. reflexivity. Qed.

Example setv_it_replace_in_place :
  setv_it 4 [97] [100] [] [(([97], [98])); (([99], [101]))]
  = Some [(([97], [100])); (([99], [101]))].
Proof. reflexivity. Qed.

(* the middle slot: exercises the accumulator, i.e. the array's "leave the
   already-scanned prefix alone" behaviour *)
Example setv_it_middle_replace :
  setv_it 6 [99] [7] [] [(([97], [1])); (([99], [2])); (([101], [3]))]
  = Some [(([97], [1])); (([99], [7])); (([101], [3]))].
Proof. reflexivity. Qed.

Example setv_it_append_when_absent :
  setv_it 4 [97] [98] [] [(([99], [100]))] = Some [(([99], [100])); (([97], [98]))].
Proof. reflexivity. Qed.

Example setv_it_saturates :
  setv_it 1 [97] [98] [] [(([99], [100])); (([101], [102]))] = None.
Proof. reflexivity. Qed.

(* cross-check the tail loops reproduce the CONCRETE scans on the same inputs *)
Example getv_it_matches_concrete :
  getv_it 3 [97] [(([98], [99])); (([97], [100]))]
  = getv [97] [(([98], [99])); (([97], [100]))].
Proof. reflexivity. Qed.

Example setv_it_matches_concrete :
  setv_it 4 [99] [7] [] [(([97], [1])); (([99], [2])); (([101], [3]))]
  = Some (setv [99] [7] [(([97], [1])); (([99], [2])); (([101], [3]))]).
Proof. reflexivity. Qed.

Example be_getv_be_setv_roundtrip :
  match be_setv [97] [98] (raw_benv [(([99], [100]))]) with
  | BOk e => be_getv [97] e
  | BLimit => None
  end = Some [98].
Proof. reflexivity. Qed.

(* ═══════════════════════════════════════════════════════════════════
   §6  Iterative word expansion — the last scan the kernel recursed into
   before this section existed (5-A.7)

   `expand` / `expand_name` / `expand_brace` (sh_concrete §4) turn `$a`,
   `${a}` and `$?` into bytes.  After §4 drained glob/match_any and §5 drained
   the env writes, that mutual fixpoint was the ONLY construct in the extracted
   kernel that was neither a fixed-array layout nor a loop: every one of its
   recursive results is composed by a CONTINUATION — `b :: expand ..`,
   `nat2text st ++ expand ..`, `subst_var m acc (expand ..)` — so the answer is
   assembled on the way back out and the JPL.5 emitter would have to lower a
   recursion it cannot bound.

   `expand_go` is the same scan as ONE tail loop over an explicit state
     (mode, remaining input, REVERSED output, REVERSED name):
       EMain  — copy bytes; on '$' decide from the byte after it;
       EName  — collect name bytes, then substitute and hand the rest back to
                EMain (L2's `subst_var m acc (expand ..)`);
       EBrace — collect until '}'; without the '}' the name is dropped, exactly
                as L2's `expand_brace` returns [].
   The mode field replaces the call between the three fixpoints, and the
   reversed output accumulator replaces the `::`/`++` that L2 rebuilds on the
   way out — one `rev` per expansion instead of one per byte.

   THE DESIGN POINT that matters for L8 (sh_jpl_run_c.v): the fuel decrements
   mirror the reference ONE FOR ONE, so agreement is EXACT AT EVERY FUEL —
   `expand_it_correct` has no hypothesis, no guard and no raised budget, unlike
   §4.3.13b/§4.3.15, where `match_any`'s linear threshold and the loop's
   quadratic `fuel_top` differ and the case site has to test.  It is possible
   because the triple shares a single fuel counter and each of its steps
   consumes exactly one fuel and at most one input byte: L2's mode switch is a
   RETURN into another fixpoint at fuel `f'`, here it is a write of `ek_mode`
   with the same `f'`.

   The value lookup calls the concrete `getv`.  That is deliberate: `getv` is
   already a forward tail scan (§5's own census in JPL.md §9.1), so wiring
   `getv_it` in here would add a second encoding of the same scan rather than
   remove a recursion.

   Build note (measured, Rocq 9.2): `cbn [expand]` on a mutual fixpoint whose
   fuel argument is a constructor DOES step it and leaves the recursive calls at
   a variable fuel untouched, which is what makes the per-leaf rewriting line up
   with `expand_at`.  `cbn [expand_at]` is required AFTER `destruct mode`: cbn
   only unfolds a constant when the unfolding produces a redex, so with `mode`
   still a variable it leaves `expand_at ..` folded and the leaf mismatches.
   ═══════════════════════════════════════════════════════════════════ *)

Inductive exp_mode : Set := EMain | EName | EBrace.

(* one machine cell: what to scan, what has been produced (reversed), and the
   name being collected (reversed) *)
Record exp_k : Set := ExpK
  { ek_mode : exp_mode;
    ek_inp  : text;
    ek_out  : text;
    ek_name : text }.

(* the looked-up value of the collected name, or nothing when unset — the same
   reading `subst_var` gives, phrased so the loop's fuel-0 edge can use it *)
Definition ek_value (m : list (text * text)) (nm : text) : text :=
  match getv (rev nm) m with Some v => v | None => [] end.

Lemma ek_valuesubst : forall m nm rest,
  subst_var m (rev nm) rest = ek_value m nm ++ rest.
Proof.
  intros m nm rest. unfold subst_var, ek_value.
  destruct (getv (rev nm) m); reflexivity.
Qed.

(* the reference cell: the same three fixpoints, read back through the mode
   field.  `expand_at` is not a new semantics — it is `expand`/`expand_name`/
   `expand_brace` selected by `exp_mode`, and the agreement lemma below says the
   loop equals it. *)
Definition expand_at (m : list (text * text)) (st : nat) (f : nat)
           (mode : exp_mode) (inp nm : text) : text :=
  match mode with
  | EMain  => expand f m st inp
  | EName  => expand_name f m st inp (rev nm)
  | EBrace => expand_brace f m st inp (rev nm)
  end.

Fixpoint expand_go (f : nat) (m : list (text * text)) (st : nat) (k : exp_k)
  : text :=
  match f with
  | 0 =>
      match ek_mode k with
      | EName => rev (rev_append (ek_value m (ek_name k)) (ek_out k))
      | _     => rev (ek_out k)
      end
  | S f' =>
      let o := ek_out k in
      let nm := ek_name k in
      let i := ek_inp k in
      match ek_mode k with
      | EMain =>
          match i with
          | [] => rev o
          | b :: bs =>
              if Nat.eqb b b_dollar then
                match bs with
                | [] => rev (b_dollar :: o)
                | b2 :: bs2 =>
                    if Nat.eqb b2 b_lbrace then expand_go f' m st (ExpK EBrace bs2 o [])
                    else if is_name b2 then expand_go f' m st (ExpK EName bs2 o [b2])
                    else if Nat.eqb b2 b_qmark then
                           expand_go f' m st (ExpK EMain bs2 (rev_append (nat2text st) o) nm)
                         else expand_go f' m st (ExpK EMain bs (b_dollar :: o) nm)
                    end
              else expand_go f' m st (ExpK EMain bs (b :: o) nm)
          end
      | EName =>
          match i with
          | [] => rev (rev_append (ek_value m nm) o)
          | b :: bs =>
              if is_name b
              then expand_go f' m st (ExpK EName bs o (b :: nm))
              else expand_go f' m st (ExpK EMain i (rev_append (ek_value m nm) o) nm)
          end
      | EBrace =>
          match i with
          | [] => rev o
          | b :: bs =>
              if Nat.eqb b b_rbrace
              then expand_go f' m st (ExpK EMain bs (rev_append (ek_value m nm) o) nm)
              else expand_go f' m st (ExpK EBrace bs o (b :: nm))
          end
      end
  end.

Definition expand_it (f : nat) (m : list (text * text)) (st : nat) (inp : text)
  : text :=
  expand_go f m st (ExpK EMain inp [] []).

(* §6.1 the accumulator algebra.  `rev_append_rev` is stdlib's own spec for the
   reversed accumulator, so only the two derived faces are proved here. *)

Lemma rev_ra_spec : forall (l acc : text), rev (rev_append l acc) = rev acc ++ l.
Proof.
  intros l acc. rewrite rev_append_rev, rev_app_distr, rev_involutive. reflexivity.
Qed.

Lemma rev_cons_app : forall (a : nat) (l : text), rev (a :: l) = rev l ++ [a].
Proof.
  intros a l. change (a :: l) with ((a :: []) ++ l).
  rewrite rev_app_distr. reflexivity.
Qed.

(* Rocq's `app_assoc` reads left-associating, `l ++ (m ++ n) = (l ++ m) ++ n`;
   the accumulator goals want the other face, so the reassociation is `<-`. *)
Ltac exp_norm :=
  try rewrite !ek_valuesubst;
  try rewrite !rev_ra_spec;
  try rewrite !rev_cons_app;
  try rewrite !rev_append_rev;
  repeat rewrite <- app_assoc;
  try rewrite app_nil_r;
  try rewrite app_nil_l;
  reflexivity.

Lemma expand_nil : forall f m st, expand f m st [] = [].
Proof.
  intros f m st. destruct f.
  - reflexivity.
  - cbn [expand]. reflexivity.
Qed.

(* §6.2 the invariant: the loop's cell is the reference cell with the produced
   prefix in front of it.  Every transition is one fuel on both sides. *)

Lemma expand_go_correct : forall f m st mode inp o nm,
  expand_go f m st (ExpK mode inp o nm)
    = rev o ++ expand_at m st f mode inp nm.
Proof.
  induction f as [ | f IH ]; intros m st mode inp o nm;
    cbn [expand_go expand_at ek_mode ek_inp ek_out ek_name].
  - destruct mode; cbn [expand_at expand expand_name expand_brace]; exp_norm.
  - destruct mode as [ | | ]; destruct inp as [ | b bs ];
      cbn [expand_at expand expand_name expand_brace].
    + (* EMain, input consumed: both sides are rev o *) exp_norm.
    + (* EMain, b :: bs *) destruct (Nat.eqb b b_dollar) eqn:Eb; cbn [expand].
      * (* the '$' was seen: the byte after it decides *)
        destruct bs as [ | b2 bs2 ]; cbn [expand].
        -- (* lone '$' at the end of the word *) exp_norm.
        -- destruct (Nat.eqb b2 b_lbrace) eqn:E1; cbn [expand_name expand_brace].
           +++ rewrite (IH m st EBrace bs2 o []). exp_norm.
           +++ destruct (is_name b2) eqn:E2; cbn [expand_at expand].
               *** rewrite (IH m st EName bs2 o [b2]). exp_norm.
               *** destruct (Nat.eqb b2 b_qmark) eqn:E3; cbn [expand_at expand].
                   ---- rewrite (IH m st EMain bs2 (rev_append (nat2text st) o) nm).
                        exp_norm.
                   ---- rewrite (IH m st EMain (b2 :: bs2) (b_dollar :: o) nm). exp_norm.
      * rewrite (IH m st EMain bs (b :: o) nm). exp_norm.
    + (* EName, input consumed: substitute the name and stop *) exp_norm.
    + (* EName, b :: bs *) destruct (is_name b) eqn:E1; cbn [expand_at expand].
      * rewrite (IH m st EName bs o (b :: nm)). exp_norm.
      * rewrite (IH m st EMain (b :: bs) (rev_append (ek_value m nm) o) nm).
        exp_norm.
    + (* EBrace, input consumed: the unterminated name is dropped *) exp_norm.
    + (* EBrace, b :: bs *) destruct (Nat.eqb b b_rbrace) eqn:E1; cbn [expand_at expand].
      * rewrite (IH m st EMain bs (rev_append (ek_value m nm) o) nm). exp_norm.
      * rewrite (IH m st EBrace bs o (b :: nm)). exp_norm.
Qed.

(* §6.3 HYPOTHESIS-FREE agreement with the reference expander.  No fuel side
   condition, no length side condition, no guard: the loop is `expand`. *)

Theorem expand_it_correct : forall f m st inp,
  expand_it f m st inp = expand f m st inp.
Proof.
  intros f m st inp. unfold expand_it.
  rewrite (expand_go_correct f m st EMain inp []).
  reflexivity.
Qed.

(* §6.4 byte-level witnesses (mnemonics: 36 $, 63 ?, 64 @, 97 a, 98 b, 99 c,
   120 x, 122 z, 123 {, 125 }). *)

Example expand_it_name :
  expand_it 8 [([97], [98])] 0 [36; 97] = [98].
Proof. vm_compute. reflexivity. Qed.

Example expand_it_lone_dollar : expand_it 8 [] 0 [36] = [36].
Proof. vm_compute. reflexivity. Qed.

Example expand_it_brace :
  expand_it 8 [([97; 98; 99], [122])] 0 [36; 123; 97; 98; 99; 125; 120] = [122; 120].
Proof. vm_compute. reflexivity. Qed.

Example expand_it_qmark_status : expand_it 8 [] 1 [36; 63; 122] = [49; 122].
Proof. vm_compute. reflexivity. Qed.

(* the substituted value is NOT rescanned: with a -> "$x" the word `$a` stops at
   the literal `$` — the same single pass L2 makes *)
Example expand_it_no_recursion :
  expand_it 8 [([97], [36; 120]); ([120], [122])] 0 [36; 97] = [36; 120].
Proof. vm_compute. reflexivity. Qed.

Example expand_it_zero_fuel : expand_it 0 [] 0 [36; 97] = [].
Proof. vm_compute. reflexivity. Qed.

Example expand_it_name_then_literal :
  expand_it 8 [([97], [98])] 0 [36; 97; 64] = [98; 64].
Proof. vm_compute. reflexivity. Qed.

Example expand_it_brace_unset : expand_it 8 [] 0 [36; 123; 97; 125; 120] = [120].
Proof. vm_compute. reflexivity. Qed.

Example expand_it_brace_name :
  expand_it 8 [([97], [98])] 0 [36; 123; 97; 125] = [98].
Proof. vm_compute. reflexivity. Qed.

Example expand_it_status_127 : expand_it 8 [] 127 [36; 63] = [49; 50; 55].
Proof. vm_compute. reflexivity. Qed.

(* the low-fuel edge, where the two machines must still agree byte for byte *)
Example expand_it_vs_ref_qmark :
  expand_it 8 [] 127 [36; 63] = expand 8 [] 127 [36; 63].
Proof. vm_compute. reflexivity. Qed.

Example expand_it_vs_ref_brace :
  expand_it 8 [([97; 98; 99], [122])] 0 [36; 123; 97; 98; 99; 125; 120]
    = expand 8 [([97; 98; 99], [122])] 0 [36; 123; 97; 98; 99; 125; 120].
Proof. vm_compute. reflexivity. Qed.

Example expand_it_vs_ref_name_low_fuel :
  expand_it 3 [([97], [98])] 0 [36; 97; 64] = expand 3 [([97], [98])] 0 [36; 97; 64].
Proof. vm_compute. reflexivity. Qed.

(* an unterminated brace at low fuel: L2's `expand_brace` answers [] and the
   name it collected is dropped — the loop reproduces that edge, not a prettier
   version of it *)
Example expand_it_vs_ref_open_brace :
  expand_it 4 [] 0 [36; 123; 97; 98] = expand 4 [] 0 [36; 123; 97; 98].
Proof. vm_compute. reflexivity. Qed.
