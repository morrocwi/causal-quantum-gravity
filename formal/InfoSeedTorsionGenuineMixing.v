(******************************************************************************)
(* InfoSeedTorsionGenuineMixing.v -- EXPLORATORY, single-attempt.       *)
(*   Requires InfoAsymmetricSeedTrifurcation (this repo, R0/Parts 1-7).  *)
(*   No axiom, no Reals, no continuum. TIER = Th_coqc (Q-only).                   *)
(*                                                                            *)
(* THE REMAINING HARD PART of the torsion-connection item (see                    *)
(* SEED_ASYMMETRY_FRONTIER_AND_CONTINUATION.md, 'the ONE next brick'): Info         *)
(* SeedTorsionGroupAndRankN_attempt.v's Part B only built n INDEPENDENT (DECOUPLED)  *)
(* rank-1 seeds, one per output component k -- Gamma(k,i,j) := R0_k(i,j), where every   *)
(* k uses its OWN separate seed but the SAME 'shape' (ord's sign pattern) merely           *)
(* rescaled. This file builds a GENUINELY MIXED Gamma(k,i,j), where the output index k       *)
(* and the base-space pair (i,j) are entangled through a SHARED table T(k,i), not just         *)
(* n independent copies -- and PROVES (not just claims) that this mixing is genuine: no          *)
(* single per-k rescaling of one shared shape can reproduce it.                                     *)
(*                                                                            *)
(* THE CONSTRUCTION: Gamma(k,i,j) := T(k,i) * R(i,j), where T : nat->nat->Q is an                       *)
(* arbitrary table (the 'how much does output direction k align with base point i'                        *)
(* reading) and R is this thread's own asymmetric seed. Torsion is Gamma(k,i,j) -                            *)
(* Gamma(k,j,i) = T(k,i)*R(i,j) - T(k,j)*R(j,i), as always.                                                    *)
(*                                                                            *)
(* WHAT IS PROVED (Th_coqc):                                                                                    *)
(*   mixed_torsion_formula          the definitional unfolding, stated once for reuse.                              *)
(*   separable_T_collapses_to_shared_shape   IF T is SEPARABLE (T(k,i) == g(k)*h(i) for some                          *)
(*                                          g,h), the mixed torsion collapses to a SINGLE               *)
(*                                          k-independent SHAPE (h(i)*R(i,j)-h(j)*R(j,i))               *)
(*                                          rescaled by g(k) -- i.e. separable T reduces to               *)
(*                                          (a rescaled version of) the DECOUPLED case, honestly           *)
(*                                          showing what 'decoupled' actually meant algebraically.           *)
(*   genuine_mixing_witness         a CONCRETE non-separable T (the Kronecker delta) on THIS                  *)
(*                                 thread's own WtRoot/lamRoot seed, computed directly: at k=0                    *)
(*                                 the torsion is NONZERO at pair (0,1) but EXACTLY ZERO at pair                     *)
(*                                 (1,2); at k=1 it is the reverse pattern (zero pattern differs           *)
(*                                 with k) -- a real, checked, non-vacuous witness.                            *)
(*   no_shared_shape_decoupling     THE KEY THEOREM: no single scalar c makes k=0's torsion at                     *)
(*                                 BOTH pairs simultaneously equal c times k=1's -- a rigorous,                       *)
(*                                 not just illustrative, proof that this Gamma is NOT reducible                        *)
(*                                 to any single shared shape scaled per k. Genuine mixing, proved.                       *)
(*                                                                            *)
(* SCOPE / TIER HONESTY:                                                                                                  *)
(*   [Th_coqc] All four theorems above, exactly as stated.                                                                   *)
(*   [Dr, stated openly, NOT claimed as done here]: this file does NOT invoke                                                   *)
(*   InfoTensorFrame_attempt.v's actual polarization/reconstruction machinery -- it uses a single,                                 *)
(*   hand-picked concrete non-separable T (the Kronecker delta) to DEMONSTRATE that genuine mixing                                    *)
(*   is possible and checkable, not to derive T from some prior quadratic-form data the way that file                                    *)
(*   reconstructs symmetric 2-tensors. Building T FROM InfoTensorFrame's reconstruction (rather than                                        *)
(*   positing it directly, as here) remains the natural, still-open follow-up. This file also does NOT                                       *)
(*   claim the Kronecker-delta choice is the UNIQUE or most natural non-separable T -- only that it is A                                       *)
(*   genuine, checkable one.                                                                                                                       *)
(******************************************************************************)

Require InfoAsymmetricSeedTrifurcation.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Open Scope Q_scope.

(* ========================================================================= *)
(* PART A -- the mixed connection and its torsion.                            *)
(* ========================================================================= *)

Definition MixedGamma (T R : nat -> nat -> Q) (k i j : nat) : Q := T k i * R i j.

Definition MixedTorsion (T R : nat -> nat -> Q) (k i j : nat) : Q :=
  MixedGamma T R k i j - MixedGamma T R k j i.

Theorem mixed_torsion_formula :
  forall (T R : nat -> nat -> Q) (k i j : nat),
    MixedTorsion T R k i j == T k i * R i j - T k j * R j i.
Proof. intros T R k i j. unfold MixedTorsion, MixedGamma. ring. Qed.

(* ========================================================================= *)
(* PART B -- separable T collapses to a single shared shape, rescaled: this   *)
(* is what 'decoupled' (InfoSeedTorsionGroupAndRankN_attempt.v Part B) meant     *)
(* algebraically, made explicit here.                                            *)
(* ========================================================================= *)

Theorem separable_T_collapses_to_shared_shape :
  forall (R : nat -> nat -> Q) (g h : nat -> Q) (k i j : nat),
    MixedTorsion (fun a b => g a * h b) R k i j
      == g k * (h i * R i j - h j * R j i).
Proof.
  intros R g h k i j.
  unfold MixedTorsion, MixedGamma.
  ring.
Qed.

(* ========================================================================= *)
(* PART C -- a CONCRETE non-separable T (the Kronecker delta) on this thread's *)
(* own seed: genuine mixing, checked, not just claimed.                          *)
(* ========================================================================= *)

Definition KroneckerT (k i : nat) : Q := if Nat.eqb k i then 1 else 0.

Definition SeedR : nat -> nat -> Q :=
  InfoAsymmetricSeedTrifurcation.R0_forced
    InfoAsymmetricSeedTrifurcation.WtRoot
    InfoAsymmetricSeedTrifurcation.lamRoot.

(* [Th_coqc] non-vacuous: k=0's torsion is NONZERO at (0,1) but EXACTLY ZERO    *)
(* at (1,2); the SUPPORT (which pairs are nonzero) genuinely depends on k --      *)
(* impossible for a decoupled family, where every k follows the SAME ord-sign      *)
(* pattern at every pair, merely rescaled. *)
Example genuine_mixing_witness :
  MixedTorsion KroneckerT SeedR 0%nat 0%nat 1%nat == -3#1
  /\ MixedTorsion KroneckerT SeedR 0%nat 1%nat 2%nat == 0
  /\ MixedTorsion KroneckerT SeedR 1%nat 1%nat 2%nat == -4#1
  /\ MixedTorsion KroneckerT SeedR 1%nat 0%nat 1%nat == 5#1.
Proof.
  unfold MixedTorsion, MixedGamma, KroneckerT, SeedR,
    InfoAsymmetricSeedTrifurcation.R0_forced,
    InfoAsymmetricSeedTrifurcation.OffVal,
    InfoAsymmetricSeedTrifurcation.WtRoot,
    InfoAsymmetricSeedTrifurcation.lamRoot,
    InfoAsymmetricSeedTrifurcation.ord.
  simpl.
  repeat split; ring.
Qed.

(* [Th_coqc] THE KEY THEOREM: no single scalar c reproduces k=0's torsion as c        *)
(* times k=1's torsion at BOTH pairs simultaneously -- a rigorous refutation of          *)
(* 'this is secretly one shared shape scaled per k,' not merely illustrative. *)
Theorem no_shared_shape_decoupling :
  ~ (exists c : Q,
       MixedTorsion KroneckerT SeedR 0%nat 1%nat 2%nat
         == c * MixedTorsion KroneckerT SeedR 1%nat 1%nat 2%nat
       /\ MixedTorsion KroneckerT SeedR 0%nat 0%nat 1%nat
            == c * MixedTorsion KroneckerT SeedR 1%nat 0%nat 1%nat).
Proof.
  intros [c [H12 H01]].
  destruct genuine_mixing_witness as [E01 [E12 [F12 F01]]].
  rewrite E12, F12 in H12.
  rewrite E01, F01 in H01.
  assert (Hc0 : c == 0) by lra.
  rewrite Hc0 in H01.
  lra.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions mixed_torsion_formula.
Print Assumptions separable_T_collapses_to_shared_shape.
Print Assumptions genuine_mixing_witness.
Print Assumptions no_shared_shape_decoupling.
