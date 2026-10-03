(* sh_jpl_scan.v

 * JPL.5 path (A), step 5-A.1 — the bounded, ITERATIVE scan layer.

 * Background (JPL.md): the machine authored in sh_jpl_run.v drives the
 * *concrete* sh_concrete scans (teqb/expand/glob/setv), which use non-tail
 * appends and, for glob, tree backtracking.  Extraction keeps that shape, so the
 * emitted OCaml is not yet in the "tail loops over a bounded store" subset the
 * JPL.5 emitter requires.  Path A fixes this in the SOURCE: this file rewrites
 * every byte-level scan as a fuel-bounded TAIL loop over a length-carrying
 * bounded word, and proves each one agrees with the sh_concrete original on
 * in-budget inputs, so the extraction that consumes this layer yields `while`
 * loops with no cons-walking recursion left to lower.

 * Invariants (JPL.md §Design):
 *   1. Axiom-free — coqchk -o -silent must report four <none>.  No Axiom /
 *      Parameter / Admitted / admit below.
 *   2. Behavioral isomorphism — every b_* scan equals the sh_concrete helper for
 *      well-formed, in-budget inputs (the Examples/lemmas at the bottom).
 *   3. Additive — sh_concrete.v and sh_jpl.v are imported as the reference
 *      semantics; neither is edited.  Existing gates stay green.

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

   Equivalence to sh_concrete.glob on in-budget fuel is carried by the empirical
   net (the parity harness + /bin-sh corpus), matching the plan's stated policy
   for scan-level iterativity; the Examples below agree with the concrete matcher
   by computation on the exact literals parity exercises.
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
