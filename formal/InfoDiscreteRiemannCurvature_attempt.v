(******************************************************************************)
(* InfoDiscreteRiemannCurvature_attempt.v -- EXPLORATORY, single-attempt.       *)
(*   Standalone. Requires ONLY Coq.QArith + Lqa: no arc file, no Reals, no      *)
(*   axiom. TIER = Th_coqc (Q-only, axiom-free). Compile: coqc -q -R . RDL.     *)
(*                                                                            *)
(* DISCRETE RIEMANN CURVATURE -- and the secret it exposes about the geodesic   *)
(* bricks.                                                                     *)
(*                                                                            *)
(* SELF-SCRUTINY (human_pi: 'find what continuum it smuggled'). The scalar and  *)
(* tensor geodesic bricks (InfoGeodesicActionStationarity / TensorStationarity) *)
(* proved exact ring identities -- Th_coqc -- BUT their PHYSICAL reading         *)
(* interpreted gamma / c as the GRADIENT of a smooth metric field over a         *)
(* CONTINUOUS position (c = dw/dx1). That derivative is an I2 non-readout        *)
(* (smooth field + infinitely divisible position). The honest readout: the       *)
(* metric lives at DISCRETE NODES w : nat -> Q, and the 'gradient' is a FINITE   *)
(* forward difference between adjacent nodes -- a readout, no limit.            *)
(*                                                                            *)
(* THE SECRET this exposes: an AFFINE metric has ZERO discrete Riemann          *)
(* curvature. The tensor brick's cross-Christoffel Gamma^1_22 = 1/2*c was        *)
(* nonzero, but with w AFFINE the space is FLAT -- so that 'bending' was a       *)
(* COORDINATE / gauge effect (removable by a change of coordinates), NOT         *)
(* intrinsic curvature. Genuine spatial bending needs the metric's SECOND        *)
(* finite difference to be nonzero (a NON-affine metric). Curvature is a         *)
(* second-difference readout, not a first-difference (Christoffel) one.         *)
(*                                                                            *)
(* Discrete objects (metric field w : nat -> Q at nodes; no continuum):         *)
(*   christoffel_fd w j := w (S j) - w j          (finite forward difference)    *)
(*   riemann_fd     w j := christoffel_fd w (S j) - christoffel_fd w j           *)
(*                       == w (S (S j)) - 2 * w (S j) + w j   (2nd difference)    *)
(*                                                                            *)
(* WHAT IS PROVED (Th_coqc, axiom-free over Q; Compute-checked witness):        *)
(*   riemann_is_second_difference : riemann_fd w j == w(S(S j)) - 2*w(S j)+w j.  *)
(*       Discrete curvature IS the finite second difference of the metric --     *)
(*       exact, no continuum d^2g.                                              *)
(*   affine_is_flat : if w is affine (w n == a + b * qn n) then                 *)
(*       riemann_fd w j == 0 for all j. THE SECRET: the geodesic bricks'         *)
(*       affine metric has ZERO curvature -- their cross-Christoffel bending is  *)
(*       gauge, not curvature.                                                  *)
(*   christoffel_can_be_nonzero_while_flat : the SAME affine w has a nonzero     *)
(*       Christoffel (christoffel_fd w j == b) yet zero Riemann -- Christoffel   *)
(*       != curvature, made exact.                                             *)
(*   curvature_nonzero_witness : a NON-affine metric w n = (qn n)^2 has          *)
(*       riemann_fd w 0 == 2 <> 0 -- genuine discrete curvature, FINITE, a       *)
(*       readout (no h->0, no d^2g).                                            *)
(*   flat_iff_second_diff_zero : riemann_fd w j == 0 <-> the three-node metric   *)
(*       values are in arithmetic progression (locally affine) -- the exact      *)
(*       discrete flat<->affine equivalence.                                    *)
(*                                                                            *)
(* HONEST FENCE. CLOSED: the scalar (one-index) discrete Riemann curvature as    *)
(* the metric's finite second difference, the exact flat<->affine equivalence,   *)
(* and the Christoffel!=curvature separation -- all finite readouts. [Open]:     *)
(* the full multi-index Riemann tensor R^i_jkl in >=2 dimensions with the        *)
(* nonlinear Gamma*Gamma terms and index antisymmetries; the continuum Riemann   *)
(* tensor (smooth d(Gamma)) is a non-readout, correctly refused. This brick      *)
(* corrects the geodesic bricks' honest tier (their affine bending is flat/gauge) *)
(* and grounds curvature as a second-difference readout. w,a,b plain Q; no        *)
(* Reals, no continuum, no constant.                                           *)
(******************************************************************************)

Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.

Module InfoDiscreteRiemannCurvature.
Open Scope Q_scope.

Definition qn (n : nat) : Q := inject_Z (Z.of_nat n).
Lemma qn_S : forall n, qn (S n) == qn n + 1.
Proof. intro n. unfold qn. rewrite Nat2Z.inj_succ. unfold Z.succ.
       rewrite inject_Z_plus. reflexivity. Qed.

(* metric field at discrete nodes -> the finite-difference geometry *)
Definition christoffel_fd (w : nat -> Q) (j : nat) : Q := w (S j) - w j.
Definition riemann_fd (w : nat -> Q) (j : nat) : Q :=
  christoffel_fd w (S j) - christoffel_fd w j.

(* ------------------------------------------------------------------ *)
(* (1) discrete curvature IS the second finite difference.             *)
(* ------------------------------------------------------------------ *)
Theorem riemann_is_second_difference :
  forall (w : nat -> Q) (j : nat),
    riemann_fd w j == w (S (S j)) - 2 * w (S j) + w j.
Proof. intros w j. unfold riemann_fd, christoffel_fd. ring. Qed.

(* ------------------------------------------------------------------ *)
(* (2) THE SECRET: an affine metric is FLAT (zero Riemann), even        *)
(*     though its Christoffel is nonzero.                               *)
(* ------------------------------------------------------------------ *)
Theorem affine_is_flat :
  forall (a b : Q) (w : nat -> Q) (j : nat),
    (forall n, w n == a + b * qn n) ->
    riemann_fd w j == 0.
Proof.
  intros a b w j Hw.
  rewrite riemann_is_second_difference.
  rewrite (Hw (S (S j))), (Hw (S j)), (Hw j).
  rewrite !qn_S. ring.
Qed.

Theorem christoffel_can_be_nonzero_while_flat :
  forall (a b : Q) (w : nat -> Q) (j : nat),
    (forall n, w n == a + b * qn n) ->
    christoffel_fd w j == b /\ riemann_fd w j == 0.
Proof.
  intros a b w j Hw. split.
  - unfold christoffel_fd. rewrite (Hw (S j)), (Hw j), qn_S. ring.
  - apply (affine_is_flat a b); exact Hw.
Qed.

(* ------------------------------------------------------------------ *)
(* (3) genuine curvature: a NON-affine metric has nonzero Riemann.     *)
(*     w n = (qn n)^2 : second difference of a square is 2.            *)
(* ------------------------------------------------------------------ *)
Definition wsq (n : nat) : Q := qn n * qn n.

Theorem curvature_nonzero_witness : riemann_fd wsq 0 == 2.
Proof.
  rewrite riemann_is_second_difference. unfold wsq.
  assert (H0 : qn 0 == 0) by reflexivity.
  assert (H1 : qn 1 == 1) by (vm_compute; reflexivity).
  assert (H2 : qn 2 == 2) by (vm_compute; reflexivity).
  rewrite H0, H1, H2. ring.
Qed.

(* ------------------------------------------------------------------ *)
(* (4) exact flat <-> locally-affine (arithmetic-progression) equiv.    *)
(* ------------------------------------------------------------------ *)
Theorem flat_iff_second_diff_zero :
  forall (w : nat -> Q) (j : nat),
    riemann_fd w j == 0 <->
    w (S (S j)) - w (S j) == w (S j) - w j.
Proof.
  intros w j. rewrite riemann_is_second_difference. split; intro H; lra.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions riemann_is_second_difference.
Print Assumptions affine_is_flat.
Print Assumptions christoffel_can_be_nonzero_while_flat.
Print Assumptions curvature_nonzero_witness.
Print Assumptions flat_iff_second_diff_zero.

End InfoDiscreteRiemannCurvature.
