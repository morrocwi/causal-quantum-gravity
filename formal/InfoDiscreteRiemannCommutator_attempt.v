(******************************************************************************)
(* InfoDiscreteRiemannCommutator_attempt.v -- EXPLORATORY, single-attempt.      *)
(*   Standalone. Requires ONLY Coq.QArith + Lqa: no arc file, no Reals, no      *)
(*   axiom. TIER = Th_coqc (Q-only, axiom-free). Compile: coqc -q -R . RDL.     *)
(*                                                                            *)
(* GENUINE 2-INDEX DISCRETE RIEMANN CURVATURE = the parallel-transport          *)
(* HOLONOMY / group COMMUTATOR (the Gamma*Gamma non-commutativity).             *)
(*                                                                            *)
(* Synthesized from THREE different-model pre-imaginations. Two of them         *)
(* (holonomy lens and commutator lens) INDEPENDENTLY derived the same object:   *)
(* discrete Riemann curvature is the failure of a finite parallel-transport      *)
(* loop to close = the COMMUTATOR of the two directional transports. The         *)
(* scalar/one-index brick (InfoDiscreteRiemannCurvature) provably cannot reach   *)
(* this -- scalars commute, so its curvature is the flat/abelian second          *)
(* difference. The genuinely 2-index content IS matrix non-commutativity.       *)
(*                                                                            *)
(* To stay axiom-free over Q, we refuse matrix inverse / division (a non-       *)
(* readout risk) and use the MINIMAL NON-ABELIAN RATIONAL group: the            *)
(* Heisenberg / upper-unipotent group, whose inverse is POLYNOMIAL:             *)
(*   element g = (x,y,z);  id = (0,0,0)                                          *)
(*   mul g1 g2 = (x1+x2, y1+y2, z1+z2 + x1*y2)                                   *)
(*   inv g     = (-x, -y, -z + x*y)          -- no division                     *)
(* Exactly one commutator direction (the center z), which turns out to BE the   *)
(* curvature. Parallel transport around a plaquette with an x-increment a and a *)
(* y-increment b is the group commutator [X,Y], whose center is a*b = "area x    *)
(* field strength", exact over Q. The continuum R = dGamma-dGamma+Gamma*Gamma is *)
(* the first-order expansion of this exact product; we refuse that expansion     *)
(* (refuse I2) and keep the finite product.                                     *)
(*                                                                            *)
(* WHAT IS PROVED (Th_coqc, axiom-free over Q; Compute-checked witness):        *)
(*   hinv_ok : mul g (inv g) == id (componentwise) -- polynomial inverse works.  *)
(*   curvature_is_central : the commutator's x,y components are 0 -- curvature   *)
(*       lives ONLY in the center (the one 2-index direction).                  *)
(*   plaquette_curvature_z : the center of [X,Y] (X = x-increment a, Y = y-      *)
(*       increment b) == a*b -- the exact discrete Riemann curvature R_xy.       *)
(*   reverse_antisymmetric : the center of [Y,X] == -(a*b) -- kl-plane index     *)
(*       antisymmetry R_xy = -R_yx, EXACT (in the nilpotent center), not just    *)
(*       first order.                                                           *)
(*   abelian_flat_x / abelian_flat_y / same_direction_flat : if a=0, or b=0, or  *)
(*       both increments are in the same (abelian) direction, R == 0 -- the      *)
(*       curvature is impossible in any scalar/abelian/relabeled-1D reduction,   *)
(*       so this brick STRICTLY exceeds InfoDiscreteRiemannCurvature.            *)
(*   nonvacuous_witness : a=2, b=3 -> R_xy == 6 <> 0 -- genuine 2-index          *)
(*       non-abelian curvature.                                                 *)
(*                                                                            *)
(* HONEST FENCE. CLOSED: the exact 2-index discrete curvature as the transport   *)
(* holonomy / group commutator = the Gamma*Gamma non-commutativity, with the     *)
(* abelian/scalar-flat fences and the kl-antisymmetry (exact in the center).     *)
(* [Open], NOT smuggled (the three lenses agreed): (i) METRIC-COMPATIBILITY /    *)
(* ij-antisymmetry -- the transport being an ISOMETRY (M^T g M = g) so the       *)
(* generator is so(g)-valued; Heisenberg is not orthogonal, so this is NOT free  *)
(* and needs SO(n) (rational orthogonal, reintroducing det<>0) -- a harder later *)
(* brick; (ii) deriving the connection from an actual finite-metric second       *)
(* difference (Levi-Civita/Christoffel from riemann_fd, checked against qform) -- *)
(* the tie to geometry; (iii) pair symmetry R_ijkl=R_klij and the Bianchi        *)
(* identities; (iv) the full R^i_jkl array over all planes in n>=3. The continuum *)
(* Riemann tensor is a refused non-readout. x,y,z,a,b plain Q; no Reals, no       *)
(* division, no constant.                                                       *)
(******************************************************************************)

Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.

Module InfoDiscreteRiemannCommutator.
Open Scope Q_scope.

(* Heisenberg / upper-unipotent group element (x,y,z) *)
Record Hb : Type := mkH { hx : Q ; hy : Q ; hz : Q }.

Definition hmul (g1 g2 : Hb) : Hb :=
  mkH (hx g1 + hx g2) (hy g1 + hy g2) (hz g1 + hz g2 + hx g1 * hy g2).
Definition hinv (g : Hb) : Hb :=
  mkH (- hx g) (- hy g) (- hz g + hx g * hy g).
Definition hid : Hb := mkH 0 0 0.

(* group commutator [g1,g2] = g1 g2 g1^-1 g2^-1 *)
Definition commutator (g1 g2 : Hb) : Hb :=
  hmul (hmul (hmul g1 g2) (hinv g1)) (hinv g2).

(* ------------------------------------------------------------------ *)
(* (0) the polynomial inverse actually works (all three components).   *)
(* ------------------------------------------------------------------ *)
Theorem hinv_ok : forall g : Hb,
  hx (hmul g (hinv g)) == hx hid /\
  hy (hmul g (hinv g)) == hy hid /\
  hz (hmul g (hinv g)) == hz hid.
Proof. intro g. simpl. repeat split; ring. Qed.

(* ------------------------------------------------------------------ *)
(* (1) curvature lives ONLY in the center: [X,Y] has x,y components 0. *)
(* ------------------------------------------------------------------ *)
Theorem curvature_is_central : forall a b : Q,
  hx (commutator (mkH a 0 0) (mkH 0 b 0)) == 0 /\
  hy (commutator (mkH a 0 0) (mkH 0 b 0)) == 0.
Proof. intros a b. simpl. split; ring. Qed.

(* ------------------------------------------------------------------ *)
(* (2) THE CURVATURE: R_xy = the center of [X,Y] == a*b.               *)
(* ------------------------------------------------------------------ *)
Theorem plaquette_curvature_z : forall a b : Q,
  hz (commutator (mkH a 0 0) (mkH 0 b 0)) == a * b.
Proof. intros a b. simpl. ring. Qed.

(* ------------------------------------------------------------------ *)
(* (3) kl-antisymmetry, EXACT: reversing the loop negates the center.  *)
(* ------------------------------------------------------------------ *)
Theorem reverse_antisymmetric : forall a b : Q,
  hz (commutator (mkH 0 b 0) (mkH a 0 0)) == - (a * b).
Proof. intros a b. simpl. ring. Qed.

(* ------------------------------------------------------------------ *)
(* (4) FLAT fences: scalar/abelian/same-direction reductions => R = 0. *)
(*     (beats the scalar one-index brick: those cases are all it has.) *)
(* ------------------------------------------------------------------ *)
Theorem abelian_flat_x : forall b : Q,
  hz (commutator (mkH 0 0 0) (mkH 0 b 0)) == 0.
Proof. intros b. simpl. ring. Qed.

Theorem abelian_flat_y : forall a : Q,
  hz (commutator (mkH a 0 0) (mkH 0 0 0)) == 0.
Proof. intros a. simpl. ring. Qed.

Theorem same_direction_flat : forall a a' : Q,
  hz (commutator (mkH a 0 0) (mkH a' 0 0)) == 0.
Proof. intros a a'. simpl. ring. Qed.

(* ------------------------------------------------------------------ *)
(* (5) NON-VACUOUS witness: genuinely 2-index non-abelian curvature.   *)
(* ------------------------------------------------------------------ *)
Example nonvacuous_witness :
  hz (commutator (mkH 2 0 0) (mkH 0 3 0)) == 6.
Proof. simpl. ring. Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions plaquette_curvature_z.
Print Assumptions curvature_is_central.
Print Assumptions reverse_antisymmetric.
Print Assumptions same_direction_flat.
Print Assumptions hinv_ok.

End InfoDiscreteRiemannCommutator.
