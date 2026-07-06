(******************************************************************************)
(* InfoMetricCompatibleCurvature_attempt.v -- EXPLORATORY, single-attempt.      *)
(*   Standalone. Requires ONLY Coq.QArith + Lqa: no arc file, no Reals, no      *)
(*   axiom. TIER = Th_coqc (Q-only, axiom-free). Compile: coqc -q -R . RDL.     *)
(*                                                                            *)
(* METRIC-COMPATIBLE CURVATURE: ij-ANTISYMMETRY and the algebraic BIANCHI       *)
(* identity, at the Lie-algebra level, DIVISION-FREE.                          *)
(*                                                                            *)
(* InfoDiscreteRiemannCommutator gave 2-index curvature = the group commutator; *)
(* InfoConnectionFromFrame tied the connection to a frame field (pure-gauge =   *)
(* flat). The standing [Open]: for the commutator to be a genuine RIEMANN       *)
(* curvature (not an arbitrary Yang-Mills field), the connection must be        *)
(* METRIC-COMPATIBLE -- the transport an isometry, so the connection generator  *)
(* lives in so(g) (g-antisymmetric). The GROUP-level rational isometry SO(n)     *)
(* needs det<>0 / division (still [Open]). But the LIE-ALGEBRA level is          *)
(* division-free: so(n) is just the antisymmetric matrices, all rational. We     *)
(* work the minimal non-abelian case so(3), realized exactly as so(3) ~ (Q^3, x) *)
(* (axial vector <-> antisymmetric 3x3 matrix; bracket = cross product).        *)
(*                                                                            *)
(* WHAT IS PROVED (Th_coqc, axiom-free over Q; Compute-checked witness):        *)
(*   asym_is_antisymmetric : (asym u)^T == -(asym u) -- the connection generator *)
(*       is genuinely so(3)-valued (metric-compatible generator).              *)
(*   commutator_is_asym_cross : the MATRIX commutator [asym u, asym v] ==        *)
(*       asym (cross u v). The curvature commutator of two metric-compatible     *)
(*       generators is again an antisymmetric matrix -- so(3) is CLOSED under    *)
(*       the bracket, and the bracket IS the cross product. (This is the anchor  *)
(*       that makes the cross-product picture the genuine matrix commutator.)    *)
(*   curvature_ij_antisymmetric : hence the curvature [asym u, asym v] is        *)
(*       antisymmetric, ( [.,.] )^T == -( [.,.] ) -- the Riemann ij-plane index  *)
(*       antisymmetry R_ijkl = -R_jikl, exact.                                  *)
(*   bianchi_jacobi : cross u (cross v w) + cross v (cross w u)                  *)
(*       + cross w (cross u v) == 0 -- the Jacobi identity of the bracket = the  *)
(*       FIRST (algebraic) BIANCHI identity for so(3)-valued curvature, exact.   *)
(*   curvature_nonzero_witness : cross e1 e2 == e3 (<> 0) -- genuine nonzero      *)
(*       metric-compatible curvature (so(3) is non-abelian).                    *)
(*                                                                            *)
(* HONEST FENCE. CLOSED: the metric-compatible (so(3)-valued) curvature's        *)
(* ij-antisymmetry and the algebraic Bianchi/Jacobi identity, division-free      *)
(* over Q, with the matrix-commutator = cross-product anchor and a nonzero        *)
(* witness. [Open], NOT smuggled: (i) the GROUP-level rational isometry SO(n)     *)
(* (actual orthogonal transport, det<>0) -- this file is the Lie ALGEBRA, not    *)
(* the group; (ii) so(n) for n>3 (here n=3 via the cross-product realization);   *)
(* (iii) the tie to an actual finite-metric field g and its Levi-Civita          *)
(* connection; (iv) pair symmetry R_ijkl = R_klij and the differential (second)  *)
(* Bianchi identity; (v) the full R^i_jkl array. The continuum is refused. All    *)
(* quantities plain Q; no Reals, no division, no constant.                       *)
(******************************************************************************)

Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.

Module InfoMetricCompatibleCurvature.
Open Scope Q_scope.

(* 3-vectors and the cross product = the so(3) Lie bracket *)
Record V3 : Type := mkV { v1 : Q ; v2 : Q ; v3 : Q }.
Definition Veq (a b : V3) : Prop :=
  v1 a == v1 b /\ v2 a == v2 b /\ v3 a == v3 b.
Definition cross (u w : V3) : V3 :=
  mkV (v2 u * v3 w - v3 u * v2 w)
      (v3 u * v1 w - v1 u * v3 w)
      (v1 u * v2 w - v2 u * v1 w).

(* 3x3 matrices, product, transpose, negation, subtraction *)
Record Mat3 : Type := mkM {
  a11:Q;a12:Q;a13:Q; a21:Q;a22:Q;a23:Q; a31:Q;a32:Q;a33:Q }.
Definition Meq (A B : Mat3) : Prop :=
  a11 A==a11 B /\ a12 A==a12 B /\ a13 A==a13 B /\
  a21 A==a21 B /\ a22 A==a22 B /\ a23 A==a23 B /\
  a31 A==a31 B /\ a32 A==a32 B /\ a33 A==a33 B.
Definition mmul (A B : Mat3) : Mat3 := mkM
  (a11 A*a11 B + a12 A*a21 B + a13 A*a31 B)
  (a11 A*a12 B + a12 A*a22 B + a13 A*a32 B)
  (a11 A*a13 B + a12 A*a23 B + a13 A*a33 B)
  (a21 A*a11 B + a22 A*a21 B + a23 A*a31 B)
  (a21 A*a12 B + a22 A*a22 B + a23 A*a32 B)
  (a21 A*a13 B + a22 A*a23 B + a23 A*a33 B)
  (a31 A*a11 B + a32 A*a21 B + a33 A*a31 B)
  (a31 A*a12 B + a32 A*a22 B + a33 A*a32 B)
  (a31 A*a13 B + a32 A*a23 B + a33 A*a33 B).
Definition mtrans (A : Mat3) : Mat3 := mkM
  (a11 A) (a21 A) (a31 A) (a12 A) (a22 A) (a32 A) (a13 A) (a23 A) (a33 A).
Definition mneg (A : Mat3) : Mat3 := mkM
  (- a11 A) (- a12 A) (- a13 A) (- a21 A) (- a22 A) (- a23 A)
  (- a31 A) (- a32 A) (- a33 A).
Definition msub (A B : Mat3) : Mat3 := mkM
  (a11 A - a11 B) (a12 A - a12 B) (a13 A - a13 B)
  (a21 A - a21 B) (a22 A - a22 B) (a23 A - a23 B)
  (a31 A - a31 B) (a32 A - a32 B) (a33 A - a33 B).
Definition mcomm (A B : Mat3) : Mat3 := msub (mmul A B) (mmul B A).

(* the so(3) generator of an axial vector *)
Definition asym (u : V3) : Mat3 := mkM
  0        (- v3 u) (v2 u)
  (v3 u)   0        (- v1 u)
  (- v2 u) (v1 u)   0.

(* ------------------------------------------------------------------ *)
(* (1) the generator is genuinely antisymmetric (metric-compatible).   *)
(* ------------------------------------------------------------------ *)
Theorem asym_is_antisymmetric : forall u : V3,
  Meq (mtrans (asym u)) (mneg (asym u)).
Proof. intro u. unfold Meq; simpl. repeat split; ring. Qed.

(* ------------------------------------------------------------------ *)
(* (2) ANCHOR: the matrix commutator is asym of the cross product --   *)
(*     so(3) closed under bracket, bracket = cross.                    *)
(* ------------------------------------------------------------------ *)
Theorem commutator_is_asym_cross : forall u w : V3,
  Meq (mcomm (asym u) (asym w)) (asym (cross u w)).
Proof. intros u w. unfold Meq; simpl. repeat split; ring. Qed.

(* ------------------------------------------------------------------ *)
(* (3) hence the curvature is ij-antisymmetric.                        *)
(* ------------------------------------------------------------------ *)
Theorem curvature_ij_antisymmetric : forall u w : V3,
  Meq (mtrans (mcomm (asym u) (asym w))) (mneg (mcomm (asym u) (asym w))).
Proof. intros u w. unfold Meq; simpl. repeat split; ring. Qed.

(* ------------------------------------------------------------------ *)
(* (4) algebraic BIANCHI = Jacobi identity of the bracket.             *)
(* ------------------------------------------------------------------ *)
Theorem bianchi_jacobi : forall u w t : V3,
  Veq (mkV
        (v1 (cross u (cross w t)) + v1 (cross w (cross t u)) + v1 (cross t (cross u w)))
        (v2 (cross u (cross w t)) + v2 (cross w (cross t u)) + v2 (cross t (cross u w)))
        (v3 (cross u (cross w t)) + v3 (cross w (cross t u)) + v3 (cross t (cross u w))))
      (mkV 0 0 0).
Proof. intros u w t. unfold Veq; simpl. repeat split; ring. Qed.

(* ------------------------------------------------------------------ *)
(* (5) NON-VACUOUS witness: e1 x e2 = e3 -- nonzero so(3) curvature.    *)
(* ------------------------------------------------------------------ *)
Example curvature_nonzero_witness :
  Veq (cross (mkV 1 0 0) (mkV 0 1 0)) (mkV 0 0 1).
Proof. unfold Veq; simpl. repeat split; ring. Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions commutator_is_asym_cross.
Print Assumptions curvature_ij_antisymmetric.
Print Assumptions bianchi_jacobi.
Print Assumptions asym_is_antisymmetric.

End InfoMetricCompatibleCurvature.
