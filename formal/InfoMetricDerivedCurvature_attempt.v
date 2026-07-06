(******************************************************************************)
(* InfoMetricDerivedCurvature_attempt.v -- EXPLORATORY, single-attempt.         *)
(*   Standalone. Requires ONLY Coq.QArith + Lqa: no arc file, no Reals, no      *)
(*   axiom. TIER = Th_coqc (Q-only, axiom-free). Compile: coqc -q -R . RDL.     *)
(*                                                                            *)
(* METRIC-DERIVED (Levi-Civita) CURVATURE IS A RATIONAL READOUT -- no frame     *)
(* square root, no I1.                                                          *)
(*                                                                            *)
(* The curvature chain so far POSITED the connection (Heisenberg generators,    *)
(* rational SO(3) rotations). The standing [Open] was the tie to an actual      *)
(* metric field g via its Levi-Civita connection. The key readout observation:  *)
(* the Levi-Civita CHRISTOFFEL needs only g^{-1} (the inverse metric), and the  *)
(* inverse of any nonzero RATIONAL is rational -- so Gamma = (1/2) g^{-1}(dg) is *)
(* a RATIONAL readout for any rational metric field, with NO square root and NO  *)
(* injected infinity. (It is the orthonormal FRAME e with e^T e = g that needs  *)
(* sqrt(g) -- an I1 non-readout for non-perfect-square g; that frame, not the    *)
(* connection, is the real barrier, and it stays [Open].)                        *)
(*                                                                            *)
(* Concretely, the 2-D diagonal metric g = diag(1, w(x1)) with w a rational      *)
(* field on the grid. Its single independent Riemann component is                *)
(*   R1212(w,n) := -(1/2) * ddw(w,n) + (dw(w,n))^2 / (4 * w n),                   *)
(* dw the first finite difference, ddw the second -- rational whenever w n <> 0. *)
(*                                                                            *)
(* WHAT IS PROVED (Th_coqc, axiom-free over Q; Compute-checked witness):        *)
(*   christoffel_G212_rational : the Levi-Civita Christoffel Gamma^2_12 =         *)
(*       (1/2)*dw/w is defined over Q for any w n <> 0 (no sqrt, no I1) -- the    *)
(*       metric-derived connection is a rational readout.                       *)
(*   flat_constant_zero_curvature : a constant metric field (w n == c) has        *)
(*       R1212 == 0 -- flat, as it must be.                                     *)
(*   curved_witness : a concrete non-constant metric w = (1,2,4,...) has          *)
(*       R1212 w 0 == -1/4 <> 0 -- genuine nonzero metric-derived curvature,      *)
(*       a rational readout with no square root anywhere.                       *)
(*                                                                            *)
(* HONEST FENCE. CLOSED: the metric-DERIVED (Levi-Civita) curvature of a          *)
(* diagonal 2-D metric is a genuine RATIONAL readout (the connection needs only   *)
(* g^{-1}, always rational; no frame sqrt, no I1), zero on flat and nonzero on a  *)
(* curved witness. This sharpens the earlier worry: the CONNECTION is rational,   *)
(* only the orthonormal FRAME (sqrt g) is the I1 barrier. [Open], NOT smuggled:   *)
(* the tie to the SO(3)/frame-rotation picture (needs sqrt g = I1 for             *)
(* non-perfect-square g), the off-diagonal / higher-D metric, the general         *)
(* metric (not just diag(1,w)), pair symmetry, the 2nd Bianchi identity, and the  *)
(* full R^i_jkl array. The continuum Riemann / smooth d(Gamma) is refused. w and   *)
(* all quantities plain Q; no Reals, no sqrt, no constant (pi etc.).             *)
(******************************************************************************)

Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.

Module InfoMetricDerivedCurvature.
Open Scope Q_scope.

(* finite differences of the metric field *)
Definition dw  (w : nat -> Q) (n : nat) : Q := w (S n) - w n.
Definition ddw (w : nat -> Q) (n : nat) : Q := w (S (S n)) - 2 * w (S n) + w n.

(* the metric-derived Levi-Civita Christoffel Gamma^2_12 = (1/2) dw / w,
   and the single 2-D Riemann component of g = diag(1, w). *)
Definition G212 (w : nat -> Q) (n : nat) : Q := (1#2) * dw w n / w n.
Definition R1212 (w : nat -> Q) (n : nat) : Q :=
  - (1#2) * ddw w n + (dw w n * dw w n) / (4 * w n).

(* ------------------------------------------------------------------ *)
(* (1) the metric-derived connection is rational (no sqrt, no I1):     *)
(*     Gamma^2_12 * w = (1/2) dw, an exact rational identity for w<>0.  *)
(* ------------------------------------------------------------------ *)
Theorem christoffel_G212_rational : forall (w : nat -> Q) (n : nat),
  ~ (w n == 0) -> G212 w n * w n == (1#2) * dw w n.
Proof.
  intros w n Hw. unfold G212, Qdiv.
  rewrite <- Qmult_assoc, (Qmult_comm (/ w n) (w n)), Qmult_inv_r by exact Hw.
  ring.
Qed.

(* ------------------------------------------------------------------ *)
(* (2) constant metric field => flat (R1212 == 0).                     *)
(* ------------------------------------------------------------------ *)
Theorem flat_constant_zero_curvature : forall (w : nat -> Q) (c : Q) (n : nat),
  (forall k, w k == c) -> R1212 w n == 0.
Proof.
  intros w c n Hc.
  assert (Hd : dw w n == 0) by (unfold dw; rewrite (Hc (S n)), (Hc n); ring).
  assert (Hdd : ddw w n == 0)
    by (unfold ddw; rewrite (Hc (S (S n))), (Hc (S n)), (Hc n); ring).
  unfold R1212, Qdiv. rewrite Hd, Hdd. ring.
Qed.

(* ------------------------------------------------------------------ *)
(* (3) curved witness: w = (1,2,4,...) -> R1212 == -1/4 <> 0.           *)
(* ------------------------------------------------------------------ *)
Definition wc (n : nat) : Q :=
  match n with O => 1 | S O => 2 | _ => 4 end.

Example curved_witness : R1212 wc 0 == - (1#4).
Proof. vm_compute. reflexivity. Qed.

Example curved_witness_nonzero : ~ (R1212 wc 0 == 0).
Proof. rewrite curved_witness. intro C. lra. Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions christoffel_G212_rational.
Print Assumptions flat_constant_zero_curvature.
Print Assumptions curved_witness.

End InfoMetricDerivedCurvature.
