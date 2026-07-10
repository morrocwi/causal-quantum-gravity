(*
   InfoSeedTorsionGroupAndRankN.v -- PROMOTED EXTRACT
   Provenance: elevated 2026-07-08/10 from research_universal_solver/formal/InfoSeedTorsionGroupAndRankN_attempt.v
   (renamed, "_attempt" dropped; Require targets adjusted to this repo's file names).
   Verified standalone at elevation (coqc -q -R . DQG; all Print Assumptions "Closed under
   the global context") and wired into COQFILES/make verify + CI on 2026-07-10, closing a
   review finding that elevation alone had left these outside the CI-guarded build.
   The original header below is kept verbatim from the audited source (including its
   "EXPLORATORY, single-attempt" self-description, which refers to its role in the source
   repo's exploratory arc, not to its verification status here).
*)
(******************************************************************************)
(* InfoSeedTorsionGroupAndRankN.v -- EXPLORATORY, single-attempt.       *)
(*   Requires InfoAsymmetricSeedTrifurcation, InfoSeedTorsionIsSkewOff_  *)
(*   attempt, and InfoConnectionFromFrame_attempt (this repo, all untouched).    *)
(*   No axiom, no Reals, no continuum. TIER = Th_coqc (Q-only).                  *)
(*                                                                            *)
(* CONTINUES SEED_ASYMMETRY_FRONTIER_AND_CONTINUATION.md's torsion-connection      *)
(* item, parts (b) and (c) of 'what remains' after InfoSeedTorsionIsSkewOff_       *)
(* attempt.v's rank-1 identification.                                             *)
(*                                                                            *)
(* PART A (item c) -- does InfoConnectionFromFrame_attempt.v's OWN coboundary       *)
(* connection satisfy a torsion-free condition? Aedge's world is GROUP-valued        *)
(* (Heisenberg Hb), not Q-valued like R0 -- the rank-1 Torsion(R,i,j):=R(i,j)-R(j,i)   *)
(* definition does not typecheck there (no subtraction in a general group). The         *)
(* natural group-valued analogue replaces subtraction with the group operation that       *)
(* plays its role: torsion-free means the REVERSE reading is exactly the GROUP INVERSE     *)
(* of the forward reading (Omega(j,i) == hinv(Omega(i,j))) -- the same role 'R(j,i)==-R(i,j)'*)
(* plays for a symmetric (torsion-free) Q-valued connection. Aedge itself is only defined    *)
(* on CONSECUTIVE path indices (k, k+1); this file extends it to a full pairwise connection    *)
(* on ANY two nodes (CoboundaryConn f i j := hmul (f j) (hinv (f i)), which reduces to Aedge     *)
(* f k exactly at j = S k) and checks the group-torsion-free condition against THAT.              *)
(*                                                                            *)
(* WHAT IS PROVED (Part A, Th_coqc):                                                                *)
(*   coboundary_is_group_torsion_free   ANY coboundary connection satisfies                            *)
(*                                     Omega(j,i) == hinv(Omega(i,j)) EXACTLY -- the                      *)
(*                                     non-abelian analogue of 'a gradient/exact 1-form has                 *)
(*                                     zero antisymmetric part,' confirmed by direct group                    *)
(*                                     algebra (ring, no group-axiom lemmas needed beyond the                   *)
(*                                     concrete Hb component formulas already in this repo).                       *)
(*   omega_witness_has_torsion         a concrete NON-coboundary Hb-valued connection FAILS the                     *)
(*                                     group-torsion-free condition -- genuine group-valued                            *)
(*                                     torsion is possible, not vacuously absent for every                                *)
(*                                     connection.                                                                          *)
(* So: InfoConnectionFromFrame_attempt.v's own Aedge IS torsion-free by this (group-valued)                                   *)
(* notion, same as this repo's own R0-symmetric-connection case -- genuine (non-coboundary)                                     *)
(* HOLONOMY CURVATURE (already proven there, hz(commutator...)==6<>0) and genuine (non-zero-lam)                                  *)
(* TORSION (this repo's own seed) are two INDEPENDENT ways a discrete connection can be non-trivial:                                 *)
(* a coboundary can have EITHER, BOTH, or NEITHER kind of non-triviality depending on which object it is.                              *)
(*                                                                            *)
(* PART B (item b) -- a MODEST, HONEST rank-n extension. Genuine tensorial torsion needs an              *)
(* extra 'output' index k (T^k_ij = Gamma^k_ij - Gamma^k_ji, k ranging over the FIBER dimension,          *)
(* not just the base-space index pair i,j). The SIMPLEST honest extension: n INDEPENDENT rank-1              *)
(* seeds, one per output component k -- Gamma(k,i,j) := R0_k(i,j) for a family of seeds R0_0,...,R0_{n-1}.     *)
(* This is expressly the DIAGONAL / DECOUPLED special case (does not let different k's genuinely mix)          *)
(* -- NOT the fully general rank-n torsion of an arbitrary vector bundle connection, which stays [Open].         *)
(*                                                                            *)
(* WHAT IS PROVED (Part B, Th_coqc, a direct per-component instantiation of Part 1's rank-1 result,               *)
(* not a fresh construction):                                                                                        *)
(*   rankn_torsion_is_twice_skewoff   Torsion3(Gammas,k,i,j) == 2*SkewOff(Gammas(k),i,j) for i<>j,                     *)
(*                                   where Gammas : nat -> (nat->nat->Q) is the family of n seeds and                    *)
(*                                   Torsion3(Gammas,k,i,j) := Gammas(k)(i,j) - Gammas(k)(j,i) --                          *)
(*                                   literally Part 1's rank-1 theorem applied at each k independently.                       *)
(*   rankn_seed_torsion_is_lam_ord   for a family of R0_forced seeds sharing the SAME directional scalar               *)
(*                                   lam (one per-k weight Wt_k, one shared lam), Torsion3(k,i,j) ==                        *)
(*                                   2*lam*ord(i,j) for EVERY k -- the torsion-controlling parameter is                        *)
(*                                   the SAME lam across the whole rank-n family in this decoupled case.                          *)
(*                                                                            *)
(* SCOPE / TIER HONESTY:                                                                                                 *)
(*   [Th_coqc] Parts A and B exactly as stated above.                                                                       *)
(*   [Dr / explicitly Open, not hidden]: Part B is the DECOUPLED special case, not the fully general               *)
(*   rank-n torsion tensor of an arbitrary connection (which would let Gamma(k,i,j) mix different k's           *)
(*   in a way n independent seeds cannot represent) -- this remains open, as stated in the frontier doc.        *)
(*   Part A's group-valued torsion notion has not been connected back to the rank-1 Q-valued Torsion          *)
(*   of Part 1/InfoSeedTorsionIsSkewOff.v -- they are analogous constructions on different            *)
(*   algebraic structures (Q vs Hb), not shown to be instances of one common framework here.                *)
(******************************************************************************)

Require InfoAsymmetricSeedTrifurcation.
Require InfoSeedTorsionIsSkewOff.
Require InfoConnectionFromFrame_attempt.
Require InfoDiscreteRiemannCommutator_attempt.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Open Scope Q_scope.

Import InfoDiscreteRiemannCommutator_attempt.InfoDiscreteRiemannCommutator.
Import InfoConnectionFromFrame_attempt.InfoConnectionFromFrame.

(* ========================================================================= *)
(* PART A -- group-valued torsion, checked against InfoConnectionFromFrame's   *)
(* own coboundary connection.                                                 *)
(* ========================================================================= *)

Definition GroupTorsionFree (Omega : nat -> nat -> Hb) : Prop :=
  forall i j, Heq (Omega j i) (hinv (Omega i j)).

(* extends Aedge (defined only on consecutive path indices) to a full           *)
(* pairwise connection on ANY two nodes; reduces to Aedge f k exactly at         *)
(* j = S k. *)
Definition CoboundaryConn (f : nat -> Hb) (i j : nat) : Hb :=
  hmul (f j) (hinv (f i)).

(* [Th_coqc] ANY coboundary connection is group-torsion-free -- the non-        *)
(* abelian analogue of 'a gradient has zero antisymmetric part,' confirmed by     *)
(* direct component algebra (a polynomial identity in the six Hb components,       *)
(* closed by ring). *)
Theorem coboundary_is_group_torsion_free :
  forall (f : nat -> Hb) (i j : nat),
    Heq (CoboundaryConn f j i) (hinv (CoboundaryConn f i j)).
Proof.
  intros f i j.
  unfold CoboundaryConn, Heq, hinv, hmul. simpl.
  repeat split; ring.
Qed.

(* Non-vacuous: a concrete NON-coboundary Hb-valued connection FAILS the         *)
(* group-torsion-free condition -- genuine group-valued torsion is possible,      *)
(* not vacuously absent. *)
Definition OmegaWitness (i j : nat) : Hb :=
  match i, j with
  | 0%nat, 1%nat => mkH 1 0 0
  | 1%nat, 0%nat => mkH 1 0 0
  | _, _ => hid
  end.

Theorem omega_witness_has_torsion :
  ~ (Heq (OmegaWitness 1%nat 0%nat) (hinv (OmegaWitness 0%nat 1%nat))).
Proof.
  unfold OmegaWitness, Heq, hinv. simpl.
  intro H. destruct H as [Hx _]. lra.
Qed.

(* ========================================================================= *)
(* PART B -- a MODEST, honest rank-n extension: n independent rank-1 seeds,    *)
(* one per output component k. Explicitly the DECOUPLED special case, NOT the   *)
(* fully general rank-n torsion tensor (stated openly, not smuggled).           *)
(* ========================================================================= *)

Definition Torsion3 (Gammas : nat -> nat -> nat -> Q) (k i j : nat) : Q :=
  Gammas k i j - Gammas k j i.

(* [Th_coqc] Per-component instantiation of the rank-1 result: EVERY output       *)
(* component k independently gets Part 1's exact identity. *)
Theorem rankn_torsion_is_twice_skewoff :
  forall (Gammas : nat -> nat -> nat -> Q) (k i j : nat), i <> j ->
    Torsion3 Gammas k i j
      == (2#1) * InfoAsymmetricSeedTrifurcation.SkewOff (Gammas k) i j.
Proof.
  intros Gammas k i j Hij.
  unfold Torsion3.
  exact (InfoSeedTorsionIsSkewOff.torsion_is_twice_skewoff (Gammas k) i j Hij).
Qed.

(* a family of R0_forced seeds, one weight function Wt per output component k,   *)
(* sharing the SAME directional scalar lam. *)
Definition RankNSeed (Wts : nat -> nat -> nat -> Q) (lam : Q) (k i j : nat) : Q :=
  InfoAsymmetricSeedTrifurcation.R0_forced (Wts k) lam i j.

(* [Th_coqc] Torsion is EXACTLY 2*lam*ord for EVERY output component k, in this   *)
(* decoupled family -- lam remains the single torsion-controlling parameter        *)
(* across the whole rank-n family, not a per-k independent quantity. *)
Theorem rankn_seed_torsion_is_lam_ord :
  forall (Wts : nat -> nat -> nat -> Q),
    (forall k i j, Wts k i j == Wts k j i) ->
  forall (lam : Q) (k i j : nat), i <> j ->
    Torsion3 (RankNSeed Wts lam) k i j
      == (2#1) * lam * InfoAsymmetricSeedTrifurcation.ord i j.
Proof.
  intros Wts Wts_symmetric lam k i j Hij.
  unfold Torsion3, RankNSeed.
  fold (InfoAsymmetricSeedTrifurcation.R0_forced (Wts k) lam).
  pose proof (InfoSeedTorsionIsSkewOff.seed_torsion_is_lam_ord
                (Wts k) (Wts_symmetric k) lam i j Hij) as H.
  unfold InfoSeedTorsionIsSkewOff.Torsion in H.
  exact H.
Qed.

(* Non-vacuous concrete witness: a rank-3 family (k=0,1,2) all built from the     *)
(* SAME WtRoot/lamRoot seed (Part 7's own witness) -- every output component       *)
(* has torsion(0,1) = 2*1*1 = 2, identically, confirming the shared-lam reading. *)
Example rankn_witness :
  forall k : nat,
    Torsion3 (RankNSeed (fun _ => InfoAsymmetricSeedTrifurcation.WtRoot)
                InfoAsymmetricSeedTrifurcation.lamRoot)
      k 0%nat 1%nat == 2#1.
Proof.
  intro k.
  rewrite (rankn_seed_torsion_is_lam_ord
             (fun _ => InfoAsymmetricSeedTrifurcation.WtRoot)
             (fun k' i j => InfoAsymmetricSeedTrifurcation.WtRoot_symmetric i j)
             InfoAsymmetricSeedTrifurcation.lamRoot k 0%nat 1%nat
             (ltac:(discriminate))).
  unfold InfoAsymmetricSeedTrifurcation.ord,
    InfoAsymmetricSeedTrifurcation.lamRoot. simpl. ring.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions coboundary_is_group_torsion_free.
Print Assumptions omega_witness_has_torsion.
Print Assumptions rankn_torsion_is_twice_skewoff.
Print Assumptions rankn_seed_torsion_is_lam_ord.
Print Assumptions rankn_witness.
