(******************************************************************************)
(* InfoRationalIsometry_attempt.v -- EXPLORATORY, single-attempt.               *)
(*   Standalone. Requires ONLY Coq.QArith + Lqa: no arc file, no Reals, no      *)
(*   axiom. TIER = Th_coqc (Q-only, axiom-free). Compile: coqc -q -R . RDL.     *)
(*                                                                            *)
(* RATIONAL ISOMETRY EXISTS OVER Q, DIVISION-FREE (the SO(n) group-level gap).  *)
(*                                                                            *)
(* InfoMetricCompatibleCurvature closed the LIE-ALGEBRA level (so(3) ~ cross,   *)
(* division-free). The standing [Open] was the GROUP level: does a genuine       *)
(* rational ISOMETRY (orthogonal transport, M^T M = I) exist over Q at all, or   *)
(* does SO(n) force irrational entries / division by a determinant? This closes  *)
(* the existence question for SO(2) via the CAYLEY transform of a rational skew  *)
(* generator -- the tangent-half-angle / Pythagorean parametrization -- and the  *)
(* key orthogonality is a DIVISION-FREE ring identity.                          *)
(*                                                                            *)
(* Skew generator A(t) = [[0,-t],[t,0]] (the so(2) element). Its Cayley          *)
(* transform is (I-A)(I+A)^{-1}. Rather than divide, keep the UNNORMALIZED       *)
(*   N(t) := (I-A) * adj(I+A) = [[1-t^2, 2t],[-2t, 1-t^2]],                       *)
(* where adj(I+A) = [[1,t],[-t,1]] is the adjugate and (I+A)*adj(I+A) =           *)
(* (1+t^2) I. Then N(t)^T N(t) = (1+t^2)^2 I EXACTLY (ring) -- so the rational     *)
(* rotation M(t) = N(t)/(1+t^2) is orthogonal, and 1+t^2 > 0 for every rational  *)
(* t (never zero), so M(t) is a well-defined RATIONAL isometry with no           *)
(* irrationals and no risky division.                                          *)
(*                                                                            *)
(* WHAT IS PROVED (Th_coqc, axiom-free over Q; Compute-checked witness):        *)
(*   cayley_inverse_relation : (I+A(t)) * adj(I+A(t)) == (1+t^2) I -- the         *)
(*       adjugate is the inverse up to the scalar 1+t^2 (division-free).         *)
(*   N_is_cayley_numerator : (I - A(t)) * adj(I+A(t)) == N(t).                    *)
(*   cayley_orthogonal : N(t)^T N(t) == (1+t^2)^2 I -- the Pythagorean            *)
(*       orthogonality; so M(t)=N(t)/(1+t^2) satisfies M^T M = I exactly.        *)
(*   cayley_det : det N(t) == (1+t^2)^2 > 0 -- a PROPER rotation (det M = +1),    *)
(*       and 1+t^2 is never zero, so M(t) is a genuine rational SO(2) element.   *)
(*   denom_positive : 0 < 1 + t^2 -- the normaliser never vanishes over Q.       *)
(*   witness : t=1 -> N = [[0,2],[-2,0]], N^T N == 4 I = (1+1)^2 I (a rational    *)
(*       90-degree rotation).                                                   *)
(*                                                                            *)
(* HONEST FENCE. CLOSED: a genuine rational ISOMETRY (SO(2)) exists over Q,       *)
(* exactly orthogonal via a division-free ring identity (Cayley/Pythagorean) --  *)
(* so the SO(n) 'needs irrationals / risky division' objection is defused for     *)
(* n=2. [Open], NOT smuggled: SO(2) is ABELIAN, so it carries NO curvature -- the *)
(* non-abelian SO(3) rational rotation (Cayley of an so(3) generator, giving      *)
(* genuine curvature that ties back to InfoMetricCompatibleCurvature's cross-     *)
(* product commutator), general SO(n), the tie to an actual finite-metric field  *)
(* g, and det-based inversion for n>=3 all remain [Open]. The continuum is        *)
(* refused. t and all entries plain Q; no Reals, no irrational, no unguarded      *)
(* division, no constant.                                                       *)
(******************************************************************************)

Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.

Module InfoRationalIsometry.
Open Scope Q_scope.

Record Mat2 : Type := mkM2 { b11:Q; b12:Q; b21:Q; b22:Q }.
Definition Meq2 (A B : Mat2) : Prop :=
  b11 A==b11 B /\ b12 A==b12 B /\ b21 A==b21 B /\ b22 A==b22 B.
Definition mmul2 (A B : Mat2) : Mat2 := mkM2
  (b11 A*b11 B + b12 A*b21 B) (b11 A*b12 B + b12 A*b22 B)
  (b21 A*b11 B + b22 A*b21 B) (b21 A*b12 B + b22 A*b22 B).
Definition mtrans2 (A : Mat2) : Mat2 := mkM2 (b11 A) (b21 A) (b12 A) (b22 A).
Definition scaleI (s : Q) : Mat2 := mkM2 s 0 0 s.
Definition det2 (A : Mat2) : Q := b11 A * b22 A - b12 A * b21 A.

(* I + A(t), I - A(t), adjugate of I+A, and the Cayley numerator N *)
Definition IpA (t : Q) : Mat2 := mkM2 1 (- t) t 1.
Definition ImA (t : Q) : Mat2 := mkM2 1 t (- t) 1.
Definition adjIpA (t : Q) : Mat2 := mkM2 1 t (- t) 1.
Definition Ncay (t : Q) : Mat2 := mkM2 (1 - t*t) (2*t) (- (2*t)) (1 - t*t).

(* ------------------------------------------------------------------ *)
(* (1) adjugate is the inverse up to the scalar (1+t^2) -- no division. *)
(* ------------------------------------------------------------------ *)
Theorem cayley_inverse_relation : forall t : Q,
  Meq2 (mmul2 (IpA t) (adjIpA t)) (scaleI (1 + t*t)).
Proof. intro t. unfold Meq2; simpl. repeat split; ring. Qed.

(* ------------------------------------------------------------------ *)
(* (2) N is the Cayley numerator (I - A) * adj(I + A).                  *)
(* ------------------------------------------------------------------ *)
Theorem N_is_cayley_numerator : forall t : Q,
  Meq2 (mmul2 (ImA t) (adjIpA t)) (Ncay t).
Proof. intro t. unfold Meq2; simpl. repeat split; ring. Qed.

(* ------------------------------------------------------------------ *)
(* (3) PYTHAGOREAN ORTHOGONALITY: N^T N == (1+t^2)^2 I (division-free). *)
(*     => M = N/(1+t^2) is exactly orthogonal, M^T M = I.              *)
(* ------------------------------------------------------------------ *)
Theorem cayley_orthogonal : forall t : Q,
  Meq2 (mmul2 (mtrans2 (Ncay t)) (Ncay t)) (scaleI ((1 + t*t) * (1 + t*t))).
Proof. intro t. unfold Meq2; simpl. repeat split; ring. Qed.

(* ------------------------------------------------------------------ *)
(* (4) proper rotation: det N == (1+t^2)^2 > 0, normaliser never zero. *)
(* ------------------------------------------------------------------ *)
Theorem cayley_det : forall t : Q,
  det2 (Ncay t) == (1 + t*t) * (1 + t*t).
Proof. intro t. unfold det2; simpl. ring. Qed.

Theorem denom_positive : forall t : Q, 0 < 1 + t*t.
Proof. intro t. nra. Qed.

(* ------------------------------------------------------------------ *)
(* (5) witness: t=1 -> a rational 90-degree rotation.                  *)
(* ------------------------------------------------------------------ *)
Example cayley_witness_t1 :
  Meq2 (mmul2 (mtrans2 (Ncay 1)) (Ncay 1)) (scaleI 4).
Proof. unfold Meq2; simpl. repeat split; ring. Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions cayley_orthogonal.
Print Assumptions cayley_inverse_relation.
Print Assumptions cayley_det.
Print Assumptions denom_positive.

End InfoRationalIsometry.
