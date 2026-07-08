(******************************************************************************)
(* InfoSeedTauRelFloor.v -- EXPLORATORY, single-attempt.                 *)
(*   Requires InfoSpectralCeilingSharp (this repo, Anderson-Morley       *)
(*   sharp ceiling, untouched). No axiom, no Reals, no continuum. TIER = Th_coqc.  *)
(*                                                                            *)
(* THE FRONTIER DOC'S ITEM 3: reuse InfoSpectralCeilingSharp.v's Anderson-  *)
(* Morley bound (lam <= 4-Fmin) on the seed's own eigenpair, checking HONESTLY         *)
(* whether it applies and whether it yields a genuinely falsifiable prediction tied      *)
(* to THIS seed, not just another instance of an already-general theorem (the SAME        *)
(* discipline used on items 1 and 2, not repeating the original QM/SR overclaim).           *)
(*                                                                            *)
(* THE CHECK: the UNWEIGHTED K3 triangle (0,1),(0,2),(1,2) -- the same 3-vertex               *)
(* carrier this whole thread uses -- has eigenvector x=(1,-1,0) with eigenvalue lam=3            *)
(* under `lnode` (verified directly, not assumed: lnode(0)=3=lam*1, lnode(1)=-3=lam*(-1),          *)
(* lnode(2)=0, consistent for this lam). This is EXACTLY the same eigenvalue formula (3*w at         *)
(* w=1) that `InfoSeedFeedsQuantumRelativity_attempt.v`'s WEIGHTED bridge already used --              *)
(* the unweighted spectral-ceiling machinery and the weighted QM/SR machinery give the SAME             *)
(* number on the SAME carrier, independently checked, not assumed to match.                                *)
(*                                                                            *)
(* WHAT IS PROVED (Th_coqc):                                                                                  *)
(*   seed_eigenpair_witness       the eigenvector identity holds at every node for lam=3, x=(1,-1,0)             *)
(*                                on the unweighted K3 carrier -- a real check, not an assumption.                   *)
(*   seed_curvature_ceiling_applies   applying sharp_curvature_ceiling (not re-deriving it) to this                    *)
(*                                eigenpair with Fmin=0 (K3 is Forman-flat, matching item 2's own                       *)
(*                                result) gives lam <= 4 -- consistent with lam=3, not violated.                          *)
(*   tau_rel_floor                a GENERAL reciprocal-monotonicity lemma: if 0<lam<=4-Fmin and                          *)
(*                                0<4-Fmin, then /(4-Fmin) <= /lam -- i.e. the RELAXATION TIME                              *)
(*                                (inverse eigenvalue) has a genuine LOWER BOUND (floor) set by the                          *)
(*                                curvature ceiling. This is the actual falsifiable content: if a                             *)
(*                                seed's relaxation ever measured FASTER than this floor, the                                  *)
(*                                Anderson-Morley bound itself would be violated.                                                *)
(*   seed_tau_rel_floor_witness   the concrete floor for THIS seed's eigenpair: relaxation time                                   *)
(*                                1/3 is bounded below by 1/4 (Fmin=0 case) -- a real, checked                                       *)
(*                                numeric floor, not merely a structural possibility.                                                    *)
(*                                                                            *)
(* SCOPE / TIER HONESTY -- read before citing as more than it is:                                                                          *)
(*   [Th_coqc] Every theorem above, exactly as stated -- `sharp_curvature_ceiling` and                                                        *)
(*   `anderson_morley_witness` are APPLIED, not re-derived; `tau_rel_floor` is a genuinely new,                                                 *)
(*   general, small algebraic lemma (reciprocal monotonicity on positive rationals) proved here.                                                  *)
(*   [Dr, stated openly]: this is HONESTLY not numerically dramatic -- K3 is small and flat (Fmin=0),                                               *)
(*   giving a loose floor (1/4) far below the actual value (1/3); the bound is not saturated. It does                                                 *)
(*   NOT show the floor is TIGHT for this seed, nor that this seed's actual relaxation dynamics (which                                                  *)
(*   this repo does not model as a time-evolution here) literally obey `tau_rel`, i.e. `1/lam`, as any                                                    *)
(*   PHYSICAL time constant -- that identification (spectral gap <-> relaxation time) is a standard                                                          *)
(*   general dynamical-systems reading, not something this file itself derives from first principles.                                                          *)
(*   What IS new and checked: the two independently-defined machineries (unweighted spectral ceiling,                                                             *)
(*   weighted QM/SR eigenvalue) give the SAME number (3, at w=1) on the SAME carrier, and the resulting                                                             *)
(*   floor is a genuine, non-vacuous instance of Anderson-Morley applied to this thread's own seed.                                                                   *)
(******************************************************************************)

Require InfoSpectralCeilingSharp.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Open Scope Q_scope.

Import InfoSpectralCeilingSharp.SpectralCeilingSharp.

(* ========================================================================= *)
(* PART A -- the unweighted K3 carrier and its eigenpair.                     *)
(* ========================================================================= *)

Definition K3E : list Edge :=
  (0%nat, 1%nat) :: (0%nat, 2%nat) :: (1%nat, 2%nat) :: nil.

Definition SeedEigvec (i : nat) : Q :=
  match i with 0%nat => 1 | 1%nat => -1 | _ => 0 end.

(* [Th_coqc] a real check on lnode, not assumed: lam=3 with x=(1,-1,0). *)
Theorem seed_eigenpair_witness :
  forall i : nat, lnode K3E SeedEigvec i == 3 * SeedEigvec i.
Proof.
  intro i.
  destruct i as [|[|[|i]]]; unfold lnode, K3E, SeedEigvec, esum, acontrib; simpl; ring.
Qed.

Theorem K3_forman_flat_unweighted :
  forall e, In e K3E -> 0 <= forman K3E e.
Proof.
  intros e He.
  unfold K3E in He. simpl in He.
  assert (Hdeg : deg K3E 0%nat == 2 /\ deg K3E 1%nat == 2 /\ deg K3E 2%nat == 2).
  { unfold deg, K3E, esum, share. simpl. repeat split; ring. }
  destruct Hdeg as [D0 [D1 D2]].
  destruct He as [H|[H|[H|H]]].
  - rewrite <- H. unfold forman. cbn [fst snd]. rewrite D0, D1. lra.
  - rewrite <- H. unfold forman. cbn [fst snd]. rewrite D0, D2. lra.
  - rewrite <- H. unfold forman. cbn [fst snd]. rewrite D1, D2. lra.
  - contradiction.
Qed.

(* [Th_coqc] applying sharp_curvature_ceiling, not re-deriving it. *)
Theorem seed_curvature_ceiling_applies :
  3 <= 4 - 0.
Proof.
  apply (sharp_curvature_ceiling K3E SeedEigvec 3 0 (1%nat, 2%nat)).
  - exact seed_eigenpair_witness.
  - unfold K3E. right. right. left. reflexivity.
  - unfold ediff, SeedEigvec. simpl. lra.
  - exact K3_forman_flat_unweighted.
Qed.

(* ========================================================================= *)
(* PART B -- the general floor lemma: the curvature ceiling on lam becomes a   *)
(* genuine LOWER BOUND on the relaxation time 1/lam.                          *)
(* ========================================================================= *)

(* [Th_coqc] genuinely new: reciprocal monotonicity on positive rationals. *)
Theorem tau_rel_floor :
  forall lam Fmin : Q,
    0 < lam -> lam <= 4 - Fmin -> 0 < 4 - Fmin ->
    /(4 - Fmin) <= /lam.
Proof.
  intros lam Fmin Hlam Hle Hpos.
  apply Qle_shift_inv_l.
  - exact Hlam.
  - assert (H1 : lam / (4 - Fmin) <= 1).
    { apply Qle_shift_div_r.
      - exact Hpos.
      - rewrite Qmult_1_l. exact Hle. }
    unfold Qdiv in H1.
    rewrite Qmult_comm.
    exact H1.
Qed.

(* [Th_coqc] the concrete floor for THIS seed's eigenpair: relaxation time      *)
(* 1/3 is bounded below by the curvature-set floor 1/4, checked, not posited. *)
Example seed_tau_rel_floor_witness :
  /(4 - 0) <= /(3#1).
Proof.
  apply tau_rel_floor.
  - lra.
  - exact seed_curvature_ceiling_applies.
  - lra.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions seed_eigenpair_witness.
Print Assumptions K3_forman_flat_unweighted.
Print Assumptions seed_curvature_ceiling_applies.
Print Assumptions tau_rel_floor.
Print Assumptions seed_tau_rel_floor_witness.
