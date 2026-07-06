(******************************************************************************)
(* InfoDiscreteGaussBonnet_attempt.v -- EXPLORATORY, single-attempt.            *)
(*   Requires InfoDiscreteRiemannCurvature_attempt (REUSES christoffel_fd /      *)
(*   riemann_fd, never redefines) + Coq.QArith + Lqa. No Reals, no axiom.       *)
(*   TIER = Th_coqc (Q-only, axiom-free). Compile: coqc -q -R . RDL <this>.     *)
(*                                                                            *)
(* DISCRETE GAUSS-BONNET: total curvature telescopes to a boundary term.        *)
(*                                                                            *)
(* InfoDiscreteRiemannCurvature gave curvature as the metric's finite SECOND    *)
(* difference riemann_fd w j = christoffel_fd w (S j) - christoffel_fd w j.      *)
(* Summing a second difference over a range TELESCOPES: the total curvature      *)
(* over [0,N) equals the boundary first-difference (Christoffel) -- the exact,   *)
(* finite, readout-level analogue of Gauss-Bonnet (integral of curvature =       *)
(* boundary holonomy). No continuum integral, no limit.                        *)
(*                                                                            *)
(* WHAT IS PROVED (Th_coqc, axiom-free over Q; Compute-checked witness):        *)
(*   total_curvature_telescopes : sum_{j<N} riemann_fd w j                       *)
(*       == christoffel_fd w N - christoffel_fd w 0.  Total discrete curvature   *)
(*       = the boundary Christoffel (holonomy) -- discrete Gauss-Bonnet, exact.  *)
(*   closed_loop_zero_total_curvature : if the boundary Christoffels match        *)
(*       (christoffel_fd w N == christoffel_fd w 0, a 'closed loop' / matched     *)
(*       boundary), the total curvature is ZERO -- a global flatness constraint  *)
(*       from local curvatures cancelling around the loop.                      *)
(*   affine_total_curvature_zero : an affine metric has zero total curvature      *)
(*       (each riemann_fd is 0) -- consistent with affine = flat.               *)
(*   witness : the non-affine w n = (qn n)^2 over [0,N): total curvature ==       *)
(*       christoffel_fd wsq N - christoffel_fd wsq 0, and for N=2 it is 4 (= the  *)
(*       accumulated second differences 2+2), matching the boundary term.       *)
(*                                                                            *)
(* HONEST FENCE. CLOSED: the scalar (one-index) discrete Gauss-Bonnet /          *)
(* total-curvature-telescoping and the closed-loop zero-total-curvature          *)
(* constraint -- exact finite readouts. [Open]: the full 2-D surface             *)
(* Gauss-Bonnet (integral of Gaussian curvature = 2*pi*Euler char), which needs  *)
(* the genuine 2-index curvature and a topological Euler characteristic, and the *)
(* continuum theorem (a non-readout). This is the 1-D telescoping face only.     *)
(* No Reals, no continuum, no constant, no pi.                                  *)
(******************************************************************************)

Require InfoDiscreteRiemannCurvature_attempt.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.

Module InfoDiscreteGaussBonnet.
Import InfoDiscreteRiemannCurvature_attempt.InfoDiscreteRiemannCurvature.
Open Scope Q_scope.

(* total curvature = sum of the local second differences over [0,N) *)
Fixpoint total_curv (w : nat -> Q) (N : nat) : Q :=
  match N with O => 0 | S n => total_curv w n + riemann_fd w n end.

(* ------------------------------------------------------------------ *)
(* (1) DISCRETE GAUSS-BONNET: the sum telescopes to the boundary       *)
(*     Christoffel (holonomy).                                         *)
(* ------------------------------------------------------------------ *)
Theorem total_curvature_telescopes :
  forall (w : nat -> Q) (N : nat),
    total_curv w N == christoffel_fd w N - christoffel_fd w 0.
Proof.
  intros w N. induction N as [| n IH]; simpl.
  - unfold christoffel_fd. ring.
  - rewrite IH. unfold riemann_fd. ring.
Qed.

(* ------------------------------------------------------------------ *)
(* (2) closed loop (matched boundary Christoffels) => zero total curv. *)
(* ------------------------------------------------------------------ *)
Theorem closed_loop_zero_total_curvature :
  forall (w : nat -> Q) (N : nat),
    christoffel_fd w N == christoffel_fd w 0 ->
    total_curv w N == 0.
Proof.
  intros w N H. rewrite total_curvature_telescopes. lra.
Qed.

(* ------------------------------------------------------------------ *)
(* (3) affine metric => zero total curvature (consistent with flat).   *)
(* ------------------------------------------------------------------ *)
Theorem affine_total_curvature_zero :
  forall (a b : Q) (w : nat -> Q) (N : nat),
    (forall n, w n == a + b * qn n) ->
    total_curv w N == 0.
Proof.
  intros a b w N Hw. induction N as [| n IH]; simpl.
  - reflexivity.
  - rewrite IH. assert (Hr := affine_is_flat a b w n Hw). lra.
Qed.

(* ------------------------------------------------------------------ *)
(* (4) witness: non-affine w = (qn n)^2, N=2 -> total curv = 4 =        *)
(*     christoffel_fd wsq 2 - christoffel_fd wsq 0 (boundary), and      *)
(*     also the accumulated second differences 2 + 2.                  *)
(* ------------------------------------------------------------------ *)
Example total_curv_wsq_2 : total_curv wsq 2 == 4.
Proof.
  rewrite total_curvature_telescopes. unfold christoffel_fd, wsq.
  assert (H0 : qn 0 == 0) by reflexivity.
  assert (H1 : qn 1 == 1) by (vm_compute; reflexivity).
  assert (H2 : qn 2 == 2) by (vm_compute; reflexivity).
  assert (H3 : qn 3 == 3) by (vm_compute; reflexivity).
  rewrite H0, H1, H2, H3. ring.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions total_curvature_telescopes.
Print Assumptions closed_loop_zero_total_curvature.
Print Assumptions affine_total_curvature_zero.

End InfoDiscreteGaussBonnet.
