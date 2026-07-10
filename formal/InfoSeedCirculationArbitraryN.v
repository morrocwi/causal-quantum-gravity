(*
   InfoSeedCirculationArbitraryN.v -- PROMOTED EXTRACT
   Provenance: elevated 2026-07-08/10 from research_universal_solver/formal/InfoSeedCirculationArbitraryN_attempt.v
   (renamed, "_attempt" dropped; Require targets adjusted to this repo's file names).
   Verified standalone at elevation (coqc -q -R . DQG; all Print Assumptions "Closed under
   the global context") and wired into COQFILES/make verify + CI on 2026-07-10, closing a
   review finding that elevation alone had left these outside the CI-guarded build.
   The original header below is kept verbatim from the audited source (including its
   "EXPLORATORY, single-attempt" self-description, which refers to its role in the source
   repo's exploratory arc, not to its verification status here).
*)
(******************************************************************************)
(* InfoSeedCirculationArbitraryN.v -- EXPLORATORY, single-attempt.       *)
(*   Requires InfoAsymmetricSeedTrifurcation (SkewOff, its antisymmetry)    *)
(*   and InfoSeedArbitraryNForcing (RowSum, fold_right_congruence,             *)
(*   RowSum_add/RowSum_scale, R0_general, Verts5/Wt5Root -- all reused, none re-           *)
(*   defined). No axiom, no Reals, no continuum. TIER = Th_coqc (Q-only).                    *)
(*                                                                            *)
(* THE FRONTIER DOC'S REMAINING PIECE OF ITEM 5: `InfoSeedArbitraryNForcing.v`         *)
(* closed the D-forcing/row-sum identity for ARBITRARY `NoDup` vertex lists, but explicitly      *)
(* left `circulation_sums_to_zero` (the 'asymmetric but balanced' principle,                       *)
(* `InfoSeedAsymmetricButBalanced_attempt.v`) at fixed n=3/n=4, flagging the needed argument           *)
(* as a 'double-fold antisymmetry-swap,' more involved than the row-sum proof. This file                 *)
(* closes that gap.                                                          *)
(*                                                                            *)
(* THE KEY TECHNICAL MOVE: a discrete FUBINI lemma for `fold_right` double sums --                          *)
(* swapping which of two (possibly different) lists is the outer vs. inner iteration doesn't                   *)
(* change the total. Applied with BOTH lists equal to the same vertex list, this gives: the                        *)
(* double sum of any antisymmetric function over `verts x verts` equals its own negation, hence                       *)
(* is exactly zero -- for ANY vertex list, not any fixed size.                                                             *)
(*                                                                            *)
(* WHAT IS PROVED (Th_coqc):                                                                                                *)
(*   fubini_double_sum       for possibly DIFFERENT lists L1, L2 and ANY f: swapping which is                                    *)
(*                        outer vs. inner in a `fold_right` double sum, with `f`'s two                                             *)
(*                        arguments swapped to match, leaves the total unchanged -- proved by                                        *)
(*                        induction on L1, using ONLY `RowSum_add`/`fold_right_congruence`                                              *)
(*                        (both reused from `InfoSeedArbitraryNForcing.v`, not                                                     *)
(*                        re-derived).                                                                                                        *)
(*   double_sum_swap         the SAME-list specialization: `fubini_double_sum L L f`.                                                            *)
(*   circulation_sums_to_zero_general   THE KEY RESULT: for ANY antisymmetric `f` (`f a b ==                                                        *)
(*                        -f b a`) and ANY vertex list `L`, the double sum of `f` over `L x L`                                                            *)
(*                        is EXACTLY zero -- unconditional, antisymmetry alone forces it.                                                                  *)
(*   circulation_general_sums_to_zero   applying the above to `SkewOff` specifically (via its                                                               *)
(*                        already-proven `skewoff_antisymmetric`, not re-derived): the seed's                                                                 *)
(*                        circulation genuinely sums to zero for an ARBITRARY vertex list -- the                                                               *)
(*                        'asymmetric but balanced' principle, now proved once for all n.                                                                          *)
(*   seed_n5_circulation_witness   a concrete check on THIS repo's own n=5 instance (`Verts5`,                                                                        *)
(*                        `Wt5Root`, from `InfoSeedArbitraryNForcing.v`): circulation                                                                             *)
(*                        genuinely sums to zero there too, applying the general theorem                                                                                    *)
(*                        directly, not re-checked by hand.                                                                                                                     *)
(*                                                                            *)
(* SCOPE / TIER HONESTY -- read before citing as more than it is:                                                                                                                  *)
(*   [Th_coqc] Every theorem above, exactly as stated. This CLOSES the specific gap flagged in                                                                                       *)
(*   `InfoSeedArbitraryNForcing.v`'s own header ('circulation_sums_to_zero... remain at                                                                                        *)
(*   fixed n'). Between this file and that one, BOTH halves of item 5's forcing-machinery                                                                                                *)
(*   generalization (row-sum/D-forcing AND circulation-balance) are now genuinely arbitrary-n.                                                                                             *)
(*   [Dr, stated openly]: `offdiag_le0_full` (the conditional small-skew hypothesis) and                                                                                                     *)
(*   everything built on TOP of the fixed-n seed this session (torsion, curvature, tau_rel floor,                                                                                                *)
(*   lambda_c crossover, the argmin_a first touch) STILL remain at fixed n -- this file does not                                                                                                     *)
(*   touch any of them. The continuum-limit connection (`InfoContinuumLimit_nD.v`) also remains                                                                                                        *)
(*   open.                                                                                                                                                                                                *)
(******************************************************************************)

Require InfoAsymmetricSeedTrifurcation.
Require InfoSeedArbitraryNForcing.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Open Scope Q_scope.

(* ========================================================================= *)
(* PART A -- the discrete Fubini lemma, for possibly different lists, ANY f.  *)
(* ========================================================================= *)

(* [Th_coqc] swapping outer/inner (with f's arguments swapped to match)         *)
(* leaves a fold_right double sum unchanged -- proved by induction on L1,        *)
(* reusing RowSum_add/fold_right_congruence, not re-deriving them. *)
Theorem fubini_double_sum :
  forall (L1 L2 : list nat) (f : nat -> nat -> Q),
    InfoSeedArbitraryNForcing.RowSum
      (fun i => InfoSeedArbitraryNForcing.RowSum (fun j => f i j) L2) L1
    == InfoSeedArbitraryNForcing.RowSum
         (fun j => InfoSeedArbitraryNForcing.RowSum (fun i => f i j) L1) L2.
Proof.
  induction L1 as [| x xs IH]; intros L2 f.
  - simpl.
    assert (Hz : InfoSeedArbitraryNForcing.RowSum
                   (fun j => InfoSeedArbitraryNForcing.RowSum (fun i => f i j) []) L2
                 == 0).
    { assert (Hpt : forall j, InfoSeedArbitraryNForcing.RowSum (fun i => f i j) [] == 0).
      { intro j. unfold InfoSeedArbitraryNForcing.RowSum. reflexivity. }
      rewrite (InfoSeedArbitraryNForcing.fold_right_congruence L2
                 (fun j => InfoSeedArbitraryNForcing.RowSum (fun i => f i j) [])
                 (fun _ => 0) (fun j _ => Hpt j)).
      clear.
      induction L2 as [| y ys IH];
        unfold InfoSeedArbitraryNForcing.RowSum in *; simpl;
        [reflexivity | rewrite IH; ring]. }
    unfold InfoSeedArbitraryNForcing.RowSum at 1. simpl.
    fold (InfoSeedArbitraryNForcing.RowSum
            (fun j => InfoSeedArbitraryNForcing.RowSum (fun i => f i j) []) L2).
    symmetry. exact Hz.
  - assert (Hunfold :
      InfoSeedArbitraryNForcing.RowSum
        (fun i => InfoSeedArbitraryNForcing.RowSum (fun j => f i j) L2) (x::xs)
      == InfoSeedArbitraryNForcing.RowSum (fun j => f x j) L2
         + InfoSeedArbitraryNForcing.RowSum
             (fun i => InfoSeedArbitraryNForcing.RowSum (fun j => f i j) L2) xs).
    { unfold InfoSeedArbitraryNForcing.RowSum. simpl. reflexivity. }
    rewrite Hunfold.
    rewrite (IH L2 f).
    rewrite <- (InfoSeedArbitraryNForcing.RowSum_add
                  (fun j => f x j)
                  (fun j => InfoSeedArbitraryNForcing.RowSum (fun i => f i j) xs) L2).
    apply InfoSeedArbitraryNForcing.fold_right_congruence.
    intros j _.
    unfold InfoSeedArbitraryNForcing.RowSum. simpl. reflexivity.
Qed.

Theorem double_sum_swap :
  forall (L : list nat) (f : nat -> nat -> Q),
    InfoSeedArbitraryNForcing.RowSum
      (fun i => InfoSeedArbitraryNForcing.RowSum (fun j => f i j) L) L
    == InfoSeedArbitraryNForcing.RowSum
         (fun i => InfoSeedArbitraryNForcing.RowSum (fun j => f j i) L) L.
Proof. intros L f. exact (fubini_double_sum L L f). Qed.

(* ========================================================================= *)
(* PART B -- THE KEY RESULT: antisymmetry alone forces the double sum to        *)
(* vanish, for ANY vertex list.                                                *)
(* ========================================================================= *)

Theorem circulation_sums_to_zero_general :
  forall (L : list nat) (f : nat -> nat -> Q),
    (forall a b, f a b == - f b a) ->
    InfoSeedArbitraryNForcing.RowSum
      (fun i => InfoSeedArbitraryNForcing.RowSum (fun j => f i j) L) L == 0.
Proof.
  intros L f Hanti.
  assert (Hswap := double_sum_swap L f).
  assert (Hflip :
    InfoSeedArbitraryNForcing.RowSum
      (fun i => InfoSeedArbitraryNForcing.RowSum (fun j => f j i) L) L
    == InfoSeedArbitraryNForcing.RowSum
         (fun i => InfoSeedArbitraryNForcing.RowSum (fun j => - f i j) L) L).
  { apply InfoSeedArbitraryNForcing.fold_right_congruence.
    intros i _.
    apply InfoSeedArbitraryNForcing.fold_right_congruence.
    intros j _. rewrite (Hanti j i). ring. }
  rewrite Hflip in Hswap.
  assert (Hneg :
    InfoSeedArbitraryNForcing.RowSum
      (fun i => InfoSeedArbitraryNForcing.RowSum (fun j => - f i j) L) L
    == - InfoSeedArbitraryNForcing.RowSum
           (fun i => InfoSeedArbitraryNForcing.RowSum (fun j => f i j) L) L).
  { rewrite <- (InfoSeedArbitraryNForcing.RowSum_scale (-1#1)
                  (fun i => InfoSeedArbitraryNForcing.RowSum (fun j => f i j) L) L).
    apply InfoSeedArbitraryNForcing.fold_right_congruence.
    intros i _.
    rewrite <- (InfoSeedArbitraryNForcing.RowSum_scale (-1#1) (fun j => f i j) L).
    apply InfoSeedArbitraryNForcing.fold_right_congruence.
    intros j _. ring. }
  rewrite Hneg in Hswap.
  lra.
Qed.

(* [Th_coqc] applying the above to SkewOff (via its already-proven                *)
(* skewoff_antisymmetric, not re-derived): circulation genuinely sums to zero      *)
(* for an ARBITRARY vertex list -- the 'asymmetric but balanced' principle,           *)
(* now proved once for all n. *)
Theorem circulation_general_sums_to_zero :
  forall (R : nat -> nat -> Q) (L : list nat),
    InfoSeedArbitraryNForcing.RowSum
      (fun i => InfoSeedArbitraryNForcing.RowSum
                  (fun j => InfoAsymmetricSeedTrifurcation.SkewOff R i j) L) L == 0.
Proof.
  intros R L.
  apply circulation_sums_to_zero_general.
  intros a b. exact (InfoAsymmetricSeedTrifurcation.skewoff_antisymmetric R a b).
Qed.

(* ========================================================================= *)
(* PART C -- concrete check on this repo's own n=5 instance, applying the        *)
(* general theorem directly.                                                  *)
(* ========================================================================= *)

Example seed_n5_circulation_witness :
  InfoSeedArbitraryNForcing.RowSum
    (fun i => InfoSeedArbitraryNForcing.RowSum
                (fun j => InfoAsymmetricSeedTrifurcation.SkewOff
                            (InfoSeedArbitraryNForcing.R0_general
                               InfoSeedArbitraryNForcing.Wt5Root (1#1)
                               InfoSeedArbitraryNForcing.Verts5) i j)
                InfoSeedArbitraryNForcing.Verts5)
    InfoSeedArbitraryNForcing.Verts5 == 0.
Proof.
  apply circulation_general_sums_to_zero.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions fubini_double_sum.
Print Assumptions double_sum_swap.
Print Assumptions circulation_sums_to_zero_general.
Print Assumptions circulation_general_sums_to_zero.
Print Assumptions seed_n5_circulation_witness.
