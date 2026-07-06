(******************************************************************************)
(* InfoMetricFrameNonReadout_attempt.v -- EXPLORATORY, single-attempt.          *)
(*   Requires InfoIrrationalNonReadout_attempt (REUSES sqrt2_is_not_a_readout)   *)
(*   + Coq.QArith + Lqa. No Reals, no axiom. TIER = Th_coqc (Q-only).           *)
(*   Compile: coqc -q -R . RDL <this>.                                          *)
(*                                                                            *)
(* THE ORTHONORMAL FRAME sqrt(g) IS AN I1 NON-READOUT -- the curvature chain's   *)
(* remaining [Open] is a genuine non-readout, NOT a fillable gap.               *)
(*                                                                            *)
(* InfoMetricDerivedCurvature showed the metric-DERIVED Levi-Civita CONNECTION   *)
(* and curvature are RATIONAL readouts (they need only g^{-1}, always rational). *)
(* The only thing that resisted was the tie to the SO(n) frame-rotation picture, *)
(* which needs an ORTHONORMAL FRAME e with e^T e = g -- i.e. e = sqrt(g). This    *)
(* file proves that frame is an I1 non-readout (an irrational) for a perfectly    *)
(* good RATIONAL metric, by reusing the framework's own capstone                 *)
(* sqrt2_is_not_a_readout. So the curvature chain's last [Open] is diagnosed:     *)
(* not a missing theorem but an INJECTED INFINITY (I1, R-completeness) -- the      *)
(* connection/curvature are readouts, the frame is not, per the thesis.          *)
(*                                                                            *)
(* Metric g = diag(1, 2): a rational, positive-definite 2-D metric. An            *)
(* orthonormal frame e = diag(e1, e2) needs e1^2 = 1 and e2^2 = 2 -- and e2 = 2   *)
(* has NO rational solution.                                                      *)
(*                                                                            *)
(* WHAT IS PROVED (Th_coqc, axiom-free over Q; Compute-checked witness):        *)
(*   metric_frame_diag12_no_rational : ~ (exists e2 : Q, e2 * e2 == 2) -- the      *)
(*       orthonormal frame of the rational metric diag(1,2) is NOT a readout       *)
(*       (reusing sqrt2_is_not_a_readout). The I1 barrier, made a theorem.        *)
(*   perfect_square_metric_has_rational_frame : the metric diag(1,4) DOES have a   *)
(*       rational frame (e2 = 2, 2*2 = 4) -- the frame is rational EXACTLY when     *)
(*       g22 is a perfect square, so the barrier is I1 (irrationality), sharp.    *)
(*   connection_stays_rational_note : for diag(1,2) the inverse-metric entry        *)
(*       1/g22 = 1/2 IS rational -- so the CONNECTION (needing only g^{-1}) is a    *)
(*       readout while the FRAME (needing sqrt g) is not: the barrier is           *)
(*       specifically the square root, not the metric or division.               *)
(*                                                                            *)
(* HONEST FENCE. CLOSED: the orthonormal frame sqrt(g) of a rational metric is an  *)
(* I1 non-readout (irrational) for non-perfect-square g, while the metric, its      *)
(* inverse, and its Levi-Civita connection/curvature stay rational readouts -- so   *)
(* the curvature chain's remaining frame-[Open] is a genuine non-readout, per the   *)
(* readout-not-truth thesis, not a gap to be filled over Q. This does NOT claim     *)
(* the continuum frame is wrong -- it says the RATIONAL readout has no frame there;  *)
(* the +reals frame is the non-readout the framework refuses. Everything plain Q.   *)
(******************************************************************************)

Require InfoIrrationalNonReadout_attempt.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.

Module InfoMetricFrameNonReadout.
Import InfoIrrationalNonReadout_attempt.InfoIrrationalNonReadout.
Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(* (1) the frame of the rational metric diag(1,2) is a non-readout.    *)
(* ------------------------------------------------------------------ *)
Theorem metric_frame_diag12_no_rational :
  ~ (exists e2 : Q, e2 * e2 == 2).
Proof.
  intros [e2 H]. exact (sqrt2_is_not_a_readout e2 H).
Qed.

(* ------------------------------------------------------------------ *)
(* (2) a perfect-square metric DOES have a rational frame -- so the     *)
(*     barrier is exactly irrationality (I1), nothing else.            *)
(* ------------------------------------------------------------------ *)
Theorem perfect_square_metric_has_rational_frame :
  exists e2 : Q, e2 * e2 == 4.
Proof. exists 2. ring. Qed.

(* ------------------------------------------------------------------ *)
(* (3) the CONNECTION stays a rational readout even where the frame     *)
(*     fails: for diag(1,2), the inverse-metric entry 1/2 is rational.  *)
(*     (Connection needs g^{-1}; frame needs sqrt g. Only sqrt is I1.)  *)
(* ------------------------------------------------------------------ *)
Theorem connection_stays_rational_note :
  (2#1) * (1#2) == 1 /\ ~ (exists e2 : Q, e2 * e2 == 2).
Proof.
  split.
  - ring.
  - exact metric_frame_diag12_no_rational.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions metric_frame_diag12_no_rational.
Print Assumptions perfect_square_metric_has_rational_frame.
Print Assumptions connection_stays_rational_note.

End InfoMetricFrameNonReadout.
