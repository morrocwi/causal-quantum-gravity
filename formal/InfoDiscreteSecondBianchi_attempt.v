(******************************************************************************)
(* InfoDiscreteSecondBianchi_attempt.v -- EXPLORATORY, single-attempt.          *)
(*   Standalone. Requires ONLY Coq.QArith + Lqa: no arc file, no Reals, no      *)
(*   axiom. TIER = Th_coqc (Q-only, axiom-free). Compile: coqc -q -R . RDL.     *)
(*                                                                            *)
(* THE DIFFERENTIAL (SECOND) BIANCHI IDENTITY, discrete and exact: dF = 0.      *)
(*                                                                            *)
(* InfoMetricCompatibleCurvature closed the FIRST (algebraic) Bianchi = Jacobi. *)
(* The SECOND (differential) Bianchi says the curvature 2-form is covariantly    *)
(* closed: dF = 0. For an ABELIAN connection (the curvature living in the        *)
(* Heisenberg center R_xy = a*b, an abelian direction) the covariant d is the    *)
(* plain exterior derivative, and dF = ddA = 0 is a FINITE-difference identity:   *)
(* mixed finite differences on the lattice commute, so the cyclic sum of the      *)
(* transverse differences of the curvature components cancels exactly.          *)
(*                                                                            *)
(* Abelian connection components A_x, A_y, A_z : Z^3 -> Q on the 3-D lattice.    *)
(* Forward differences dx, dy, dz. Curvature 2-form (discrete curl):             *)
(*   Fxy = dx A_y - dy A_x,  Fyz = dy A_z - dz A_y,  Fzx = dz A_x - dx A_z.       *)
(*                                                                            *)
(* WHAT IS PROVED (Th_coqc, axiom-free over Q; Compute-checked witness):        *)
(*   mixed_differences_commute : dx (dy f) == dy (dx f) -- the lattice fact that  *)
(*       makes it all work (finite differences in different directions commute). *)
(*   second_bianchi : dz Fxy + dx Fyz + dy Fzx == 0 -- the discrete differential  *)
(*       (second) Bianchi identity dF = 0, exact, for any abelian connection.    *)
(*   curvature_can_be_nonzero : a concrete connection with Fxy <> 0 somewhere --  *)
(*       so dF = 0 is a genuine cancellation, not a vacuous 'everything is zero'. *)
(*                                                                            *)
(* HONEST FENCE. CLOSED: the discrete differential (second) Bianchi identity      *)
(* dF = 0 for an ABELIAN lattice curvature (F = dA), exact over Q, with the       *)
(* mixed-difference-commutation lemma and a nonzero-curvature witness. [Open],    *)
(* NOT smuggled: the NON-ABELIAN covariant Bianchi dF + [A,F] = 0 (the full       *)
(* so(3)/matrix curvature, where the bracket term is genuinely needed), the tie   *)
(* to a metric's Levi-Civita curvature, pair symmetry R_ijkl=R_klij, and the      *)
(* full R^i_jkl array. The continuum dF is a refused non-readout. A_x,A_y,A_z and  *)
(* all quantities plain Q; no Reals, no continuum, no constant.                  *)
(******************************************************************************)

Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.

Module InfoDiscreteSecondBianchi.
Open Scope Q_scope.

Definition F3 := nat -> nat -> nat -> Q.
Definition dx (f : F3) (i j k : nat) : Q := f (S i) j k - f i j k.
Definition dy (f : F3) (i j k : nat) : Q := f i (S j) k - f i j k.
Definition dz (f : F3) (i j k : nat) : Q := f i j (S k) - f i j k.

(* curvature 2-form (discrete curl) of an abelian connection (Ax,Ay,Az) *)
Definition Fxy (Ax Ay : F3) : F3 := fun i j k => dx Ay i j k - dy Ax i j k.
Definition Fyz (Ay Az : F3) : F3 := fun i j k => dy Az i j k - dz Ay i j k.
Definition Fzx (Az Ax : F3) : F3 := fun i j k => dz Ax i j k - dx Az i j k.

(* ------------------------------------------------------------------ *)
(* (1) mixed finite differences commute (the lattice fact).            *)
(* ------------------------------------------------------------------ *)
Theorem mixed_differences_commute : forall (f : F3) (i j k : nat),
  dx (dy f) i j k == dy (dx f) i j k.
Proof. intros f i j k. unfold dx, dy. ring. Qed.

(* ------------------------------------------------------------------ *)
(* (2) the discrete SECOND (differential) Bianchi identity: dF = 0.    *)
(* ------------------------------------------------------------------ *)
Theorem second_bianchi :
  forall (Ax Ay Az : F3) (i j k : nat),
    dz (Fxy Ax Ay) i j k + dx (Fyz Ay Az) i j k + dy (Fzx Az Ax) i j k == 0.
Proof.
  intros Ax Ay Az i j k.
  unfold dz, dx, dy, Fxy, Fyz, Fzx, dx, dy, dz. ring.
Qed.

(* ------------------------------------------------------------------ *)
(* (3) NON-VACUOUS: a concrete connection with nonzero curvature.      *)
(*     Ay(i,j,k) = i (linear in x) -> Fxy = dx Ay - dy Ax = 1 <> 0.    *)
(* ------------------------------------------------------------------ *)
Definition Ay_lin : F3 := fun i _ _ => inject_Z (Z.of_nat i).
Definition Azero : F3 := fun _ _ _ => 0.

Example curvature_can_be_nonzero : Fxy Azero Ay_lin O O O == 1.
Proof. unfold Fxy, dx, dy, Ay_lin, Azero. vm_compute. reflexivity. Qed.

(* and the second Bianchi still holds on this nonzero-curvature connection *)
Example bianchi_on_witness :
  dz (Fxy Azero Ay_lin) O O O + dx (Fyz Ay_lin Azero) O O O
  + dy (Fzx Azero Azero) O O O == 0.
Proof. apply second_bianchi. Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions mixed_differences_commute.
Print Assumptions second_bianchi.
Print Assumptions curvature_can_be_nonzero.

End InfoDiscreteSecondBianchi.
