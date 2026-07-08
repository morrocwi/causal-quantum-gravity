(******************************************************************************)
(* InfoSeedTorsionIsSkewOff.v -- EXPLORATORY, single-attempt.          *)
(*   Requires InfoAsymmetricSeedTrifurcation (this repo, R0/Parts 1-7).  *)
(*   No axiom, no Reals, no continuum. TIER = Th_coqc (Q-only).                  *)
(*                                                                            *)
(* THE FIRST BRICK OF THE TORSION-CONNECTION ITEM (see                            *)
(* docs/root/SEED_ASYMMETRY_FRONTIER_AND_CONTINUATION.md, 'the ONE next brick').    *)
(*                                                                            *)
(* THE STANDARD DEFINITION BEING SPECIALIZED (textbook differential geometry,      *)
(* not this project's invention): for an affine connection with coefficients        *)
(* Gamma^k_ij, the TORSION TENSOR is, by definition, the antisymmetrization in       *)
(* the LOWER two indices: T^k_ij := Gamma^k_ij - Gamma^k_ji. This file specializes    *)
(* that definition to the RANK-1 (scalar-bundle) case, where there is no separate      *)
(* 'output' index k at all -- the connection is a single matrix R : nat -> nat -> Q,    *)
(* R(i,j) read as 'the transport/connection coefficient from i to j,' and the           *)
(* torsion is exactly the antisymmetric part of THAT matrix. This is a genuine,          *)
(* not merely suggestive, instantiation of the general definition to a specific           *)
(* (simplified) bundle rank -- stated as such, not smuggled as the full tensorial          *)
(* torsion of a general vector bundle (which needs the k-index this file does not           *)
(* have).                                                                              *)
(*                                                                            *)
(* WHAT IS PROVED (Th_coqc, pure algebra, most of it a direct instantiation of              *)
(* InfoAsymmetricSeedTrifurcation's own SkewOff, not a fresh construction):           *)
(*   torsion_antisymmetric        Torsion(R,i,j) == -Torsion(R,j,i) -- the DEFINING             *)
(*                               property of a torsion tensor, confirmed for this               *)
(*                               specialization.                                                  *)
(*   torsion_is_twice_skewoff     Torsion(R,i,j) == 2 * SkewOff(R,i,j) EXACTLY, for                *)
(*                               i<>j -- THE BRIDGE THEOREM: this repo's already-proven             *)
(*                               antisymmetric decomposition piece (Part 1) IS (half of) the           *)
(*                               torsion of R read as a rank-1 connection, not merely analogous          *)
(*                               to it.                                                                   *)
(*   symmetric_connection_torsion_free   a symmetric connection (R(i,j)==R(j,i) for all i,j) has            *)
(*                               ZERO torsion everywhere -- the discrete analogue of 'a                      *)
(*                               symmetric (Levi-Civita-type) connection is torsion-free,' now                 *)
(*                               a genuine theorem about R, not an imported physics fact.                        *)
(*   seed_torsion_is_lam_ord      for THIS repo's own R0_forced(Wt,lam) (Part 7), torsion is                      *)
(*                               EXACTLY 2*lam*ord(i,j) -- the seed's directional scalar `lam`                      *)
(*                               and the trichotomy-forced sign `ord` are, literally, (half) the                     *)
(*                               seed's own torsion. Directionality is no longer merely an                            *)
(*                               algebraic curiosity of R0 -- it IS this rank-1 connection's                           *)
(*                               torsion, by direct substitution.                                                        *)
(*   seed_zero_lam_torsion_free   lam=0 collapses R0_forced to a torsion-free (symmetric)                                 *)
(*                               connection -- `lam` is EXACTLY the seed's own torsion-control                              *)
(*                               parameter, not an unrelated free knob.                                                       *)
(*                                                                            *)
(* SCOPE / TIER HONESTY -- read before citing this as more than it is:                                                        *)
(*   [Th_coqc] Every theorem above, exactly as stated: rank-1/scalar-bundle torsion, its                                        *)
(*   antisymmetry, its exact identity with 2*SkewOff, and the seed instantiation.                                                  *)
(*   [Dr, NOT proved here, stated openly]: that this rank-1 specialization is the CORRECT or                                        *)
(*   ONLY way to read torsion onto a graph -- the full tensorial torsion of a genuine rank->=2                                       *)
(*   vector bundle (with its own k-index, as `InfoTensorFrame_attempt.v`'s tensor-reconstruction                                       *)
(*   machinery would carry) is NOT built here; that is the natural next step (see the frontier                                          *)
(*   doc's item 2, curvature-chain integration) and remains open. This file also does NOT connect                                         *)
(*   to `InfoConnectionFromFrame_attempt.v`'s Heisenberg-holonomy curvature construction (that                                              *)
(*   file's `Aedge` connection is a PURE COBOUNDARY of a frame field, hence torsion-free by this                                              *)
(*   file's own `symmetric_connection_torsion_free`-style reasoning would need checking separately                                              *)
(*   -- not attempted here, flagged as the natural follow-up, not silently assumed either way).                                                    *)
(******************************************************************************)

Require InfoAsymmetricSeedTrifurcation.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Open Scope Q_scope.

(* ========================================================================= *)
(* THE DEFINITION: torsion of a rank-1 (scalar-bundle) connection R, read      *)
(* directly from R itself -- no new primitive, R IS the connection.            *)
(* ========================================================================= *)

Definition Torsion (R : nat -> nat -> Q) (i j : nat) : Q := R i j - R j i.

(* [Th_coqc] THE DEFINING PROPERTY: torsion is antisymmetric -- confirmed for   *)
(* this specialization, not assumed. *)
Theorem torsion_antisymmetric :
  forall (R : nat -> nat -> Q) (i j : nat), Torsion R i j == - Torsion R j i.
Proof. intros R i j. unfold Torsion. ring. Qed.

(* [Th_coqc] THE BRIDGE THEOREM: torsion is EXACTLY twice this repo's own       *)
(* SkewOff, for i<>j -- a direct instantiation, not a fresh construction.        *)
Theorem torsion_is_twice_skewoff :
  forall (R : nat -> nat -> Q) (i j : nat), i <> j ->
    Torsion R i j == (2#1) * InfoAsymmetricSeedTrifurcation.SkewOff R i j.
Proof.
  intros R i j Hij.
  unfold Torsion, InfoAsymmetricSeedTrifurcation.SkewOff.
  apply Nat.eqb_neq in Hij. rewrite Hij.
  unfold Qdiv, Qinv. simpl. ring.
Qed.

(* [Th_coqc] A symmetric connection is torsion-free EVERYWHERE -- the discrete   *)
(* analogue of 'a symmetric (Levi-Civita-type) connection is torsion-free,' now    *)
(* a genuine theorem about R, not an imported fact. *)
Theorem symmetric_connection_torsion_free :
  forall (R : nat -> nat -> Q), (forall i j, R i j == R j i) ->
    forall i j, Torsion R i j == 0.
Proof.
  intros R Hsym i j. unfold Torsion. rewrite (Hsym i j). ring.
Qed.

(* ========================================================================= *)
(* THE SEED INSTANTIATION: this repo's own R0_forced's torsion is EXACTLY        *)
(* 2*lam*ord -- directionality IS (half) the torsion, by direct substitution.      *)
(* ========================================================================= *)

(* [Th_coqc] THE KEY RESULT: torsion of the seed R0_forced(Wt,lam) at any         *)
(* off-diagonal pair is EXACTLY 2*lam*ord(i,j) -- reusing                          *)
(* skewoff_R0_forced_is_lam_ord + torsion_is_twice_skewoff directly. *)
Theorem seed_torsion_is_lam_ord :
  forall (Wt : nat -> nat -> Q), (forall i j, Wt i j == Wt j i) ->
  forall (lam : Q) (i j : nat), i <> j ->
    Torsion (InfoAsymmetricSeedTrifurcation.R0_forced Wt lam) i j
      == (2#1) * lam * InfoAsymmetricSeedTrifurcation.ord i j.
Proof.
  intros Wt Wt_symmetric lam i j Hij.
  rewrite (torsion_is_twice_skewoff
             (InfoAsymmetricSeedTrifurcation.R0_forced Wt lam) i j Hij).
  rewrite (InfoAsymmetricSeedTrifurcation.skewoff_R0_forced_is_lam_ord
             Wt Wt_symmetric lam i j Hij).
  ring.
Qed.

(* [Th_coqc] lam=0 collapses the seed to a torsion-free connection -- `lam` IS    *)
(* this seed's own torsion-control parameter, not an unrelated free knob. *)
Corollary seed_zero_lam_torsion_free :
  forall (Wt : nat -> nat -> Q), (forall i j, Wt i j == Wt j i) ->
  forall (i j : nat), i <> j ->
    Torsion (InfoAsymmetricSeedTrifurcation.R0_forced Wt 0) i j == 0.
Proof.
  intros Wt Wt_symmetric i j Hij.
  rewrite (seed_torsion_is_lam_ord Wt Wt_symmetric 0 i j Hij).
  ring.
Qed.

(* Non-vacuous concrete witness: the WtRoot/lamRoot seed (Part 7's own witness,      *)
(* lam=1) has torsion(0,1) = 2*1*ord(0,1) = 2*1*1 = 2 -- genuinely nonzero, a real     *)
(* directional/torsional reading, not a degenerate zero case. *)
Example seed_torsion_witness :
  Torsion (InfoAsymmetricSeedTrifurcation.R0_forced
             InfoAsymmetricSeedTrifurcation.WtRoot
             InfoAsymmetricSeedTrifurcation.lamRoot) 0%nat 1%nat == 2#1.
Proof.
  unfold Torsion, InfoAsymmetricSeedTrifurcation.R0_forced,
    InfoAsymmetricSeedTrifurcation.OffVal,
    InfoAsymmetricSeedTrifurcation.WtRoot,
    InfoAsymmetricSeedTrifurcation.lamRoot,
    InfoAsymmetricSeedTrifurcation.ord.
  simpl. ring.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions torsion_antisymmetric.
Print Assumptions torsion_is_twice_skewoff.
Print Assumptions symmetric_connection_torsion_free.
Print Assumptions seed_torsion_is_lam_ord.
Print Assumptions seed_zero_lam_torsion_free.
Print Assumptions seed_torsion_witness.
