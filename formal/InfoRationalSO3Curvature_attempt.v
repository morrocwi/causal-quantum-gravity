(******************************************************************************)
(* InfoRationalSO3Curvature_attempt.v -- EXPLORATORY, single-attempt.           *)
(*   Requires InfoMetricCompatibleCurvature_attempt (REUSES Mat3/mmul/mtrans/    *)
(*   Meq) + Coq.QArith + Lqa. No Reals, no axiom. TIER = Th_coqc (Q-only).      *)
(*   Compile: coqc -q -R . RDL <this>.                                          *)
(*                                                                            *)
(* CAPSTONE: a GENUINE metric-compatible rational Riemann curvature over Q --    *)
(* two rational SO(3) ROTATIONS whose parallel-transport HOLONOMY is a nonzero   *)
(* rational curvature, all division-free.                                       *)
(*                                                                            *)
(* This closes the loop across the curvature chain:                             *)
(*  - InfoRationalIsometry: rational isometries exist over Q (SO(2), Cayley).    *)
(*  - InfoMetricCompatibleCurvature: so(3)-valued curvature is antisymmetric     *)
(*    (ij-antisymmetry) and satisfies Bianchi, at the Lie-algebra level.         *)
(*  - InfoDiscreteRiemannCommutator: curvature = the transport holonomy /        *)
(*    commutator.                                                               *)
(* Here all three meet in ONE concrete object: two GROUP-level rational SO(3)     *)
(* rotations (built from the (3,4,5) Pythagorean triple, so every entry is a      *)
(* rational and each matrix is EXACTLY orthogonal), whose holonomy               *)
(* Rz Rx Rz^{-1} Rx^{-1} (inverse = transpose, since orthogonal) is NOT the       *)
(* identity -- a genuine nonzero rational curvature. Metric-compatible (the       *)
(* transports are real isometries), non-abelian (SO(3)), division-free, over Q.  *)
(*                                                                            *)
(* Rz = rotation about z, Rx = rotation about x, both by the (3/5,4/5) angle.    *)
(*                                                                            *)
(* WHAT IS PROVED (Th_coqc, axiom-free over Q; Compute-checked witness):        *)
(*   Rz_orthogonal / Rx_orthogonal : (Rz)^T Rz == I and (Rx)^T Rx == I -- each    *)
(*       is an EXACT rational isometry (the (3,4,5) Pythagorean identity).       *)
(*   holonomy_a13 : the (1,3) entry of the holonomy == 336/625.                  *)
(*   curvature_nonzero : the holonomy is NOT the identity (its (1,3) entry is     *)
(*       336/625 <> 0, whereas the identity's is 0) -- genuine nonzero rational   *)
(*       metric-compatible curvature.                                           *)
(*                                                                            *)
(* HONEST FENCE. CLOSED: a concrete pair of rational SO(3) isometries with a      *)
(* nonzero rational holonomy/curvature, division-free over Q -- the group-level   *)
(* metric-compatible curvature EXISTS and is genuinely non-abelian, no continuum, *)
(* no irrationals. [Open], NOT smuggled: the GENERAL SO(n) rotation family (this  *)
(* is a specific pair, not a parametrized theorem for all rational rotations),     *)
(* the tie to an actual finite-metric field g and its Levi-Civita connection      *)
(* (these rotations are posited, not derived from a metric), pair symmetry        *)
(* R_ijkl=R_klij, the differential (second) Bianchi identity, and the full        *)
(* R^i_jkl array. The continuum Riemann tensor is refused. All entries plain Q;    *)
(* no Reals, no irrational, no division, no constant.                            *)
(******************************************************************************)

Require InfoMetricCompatibleCurvature_attempt.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.

Module InfoRationalSO3Curvature.
Import InfoMetricCompatibleCurvature_attempt.InfoMetricCompatibleCurvature.
Open Scope Q_scope.

Definition I3 : Mat3 := mkM 1 0 0  0 1 0  0 0 1.

(* rational rotations by the (3/5, 4/5) angle, about z and about x *)
Definition Rz : Mat3 := mkM (3#5) (-(4#5)) 0  (4#5) (3#5) 0  0 0 1.
Definition Rx : Mat3 := mkM 1 0 0  0 (3#5) (-(4#5))  0 (4#5) (3#5).

(* ------------------------------------------------------------------ *)
(* (1) each is an EXACT rational isometry (Pythagorean orthogonality). *)
(* ------------------------------------------------------------------ *)
Theorem Rz_orthogonal : Meq (mmul (mtrans Rz) Rz) I3.
Proof. unfold Meq; simpl. repeat split; ring. Qed.

Theorem Rx_orthogonal : Meq (mmul (mtrans Rx) Rx) I3.
Proof. unfold Meq; simpl. repeat split; ring. Qed.

(* holonomy = Rz Rx Rz^{-1} Rx^{-1}, inverse = transpose (orthogonal) *)
Definition HOL : Mat3 :=
  mmul (mmul (mmul Rz Rx) (mtrans Rz)) (mtrans Rx).

(* ------------------------------------------------------------------ *)
(* (2) the holonomy's (1,3) entry is 336/625 -- concrete, exact.       *)
(* ------------------------------------------------------------------ *)
Theorem holonomy_a13 : a13 HOL == 336 # 625.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* (3) hence the holonomy is NOT the identity: genuine nonzero          *)
(*     rational metric-compatible curvature.                           *)
(* ------------------------------------------------------------------ *)
Theorem curvature_nonzero : ~ (a13 HOL == a13 I3).
Proof.
  rewrite holonomy_a13. unfold I3; simpl. intro C. lra.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions Rz_orthogonal.
Print Assumptions Rx_orthogonal.
Print Assumptions holonomy_a13.
Print Assumptions curvature_nonzero.

End InfoRationalSO3Curvature.
