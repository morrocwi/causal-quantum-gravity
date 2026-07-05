(* ===================================================================
   InfoModeRotation_attempt.v

   Bridges the mother equation's own CFL/leapfrog stepper (C41/C42,
   the recurrence x_{n+1} = (2-a)x_n - x_{n-1} on the stability window
   a in [0,4]) to the imaginary-unit/roots-of-unity track
   (InfoImaginaryOrder_attempt.v: i^4=1 on Q x Q pairs) -- NOT by
   analogy, but by showing the stepper matrix AT a=2 is literally the
   same object as the standard i-rotation matrix acting on Q x Q pairs.

   THE CLAIM, verified by hand before writing a line of Coq: the
   stepper S_a := [[2-a,-1],[1,0]] in SL_2(Q) (det = (2-a)*0-(-1)*1 = 1
   for every a) has S_2 = [[0,-1],[1,0]], which is exactly the matrix
   representation of multiplication by i on R^2 = C. Consequently
   S_2^2 = -I and S_2^4 = I follow from the SAME component algebra
   InfoImaginaryOrder_attempt.v already proved for i -- this file does
   not reuse that file's Coq definitions (Q x Q under cmul is a
   different formalization than a 2x2 matrix acting on Q x Q by
   left-multiplication), but proves the same numerical fact about the
   same numerical object from the mother-equation side.

   FURTHER: hand-verified periods at the window's other integer points:
   S_1^3 = -I (hence period 6), S_3^3 = I (period 3). These three
   points (a=1,2,3) are exactly the crystallographic-restriction values
   (trace = 2-a = 2*cos(2*pi*k/n) in Q forces n in {1,2,3,4,6} -- the
   theorem that also forbids 5-fold and 7-fold rotational symmetry in
   periodic crystals). The forward direction (a=1,2,3 give finite
   period, exactly) is what this file mechanizes. The GENERAL
   crystallographic restriction theorem (no other rational a in [0,4]
   gives a finite-order stepper) is a real, nontrivial, well-established
   result in the literature (Coxeter groups / the crystallographic
   restriction theorem) -- it is CITED here, not mechanized: PT(lit),
   not Th_coqc. Likewise the period-5 non-example (a = (5-sqrt5)/2,
   verified by hand to satisfy 2-a = 2*cos(2*pi/5) = (sqrt5-1)/2, hence
   irrational, hence unreachable by any a in Q) is stated in prose only
   -- it requires Coq.Reals to even express sqrt5, not attempted here.

   TIER: every theorem below is Tier-0, Q-only, axiom-free (ring/lra).
   All pair "equalities" are stated componentwise via Q's setoid
   equality (==), never Leibniz (=), to keep every proof ring/lra-
   reachable (Leibniz equality between symbolic-component pairs is not
   a ring goal and is not what this file needs to claim).
   =================================================================== *)

Require Coq.QArith.QArith.
Require Coq.micromega.Lqa.

Import Coq.QArith.QArith.
Import Coq.micromega.Lqa.
Open Scope Q_scope.

Module ModeRotation.

Definition step (a : Q) (p : Q * Q) : Q * Q :=
  let '(x, y) := p in ((2 - a) * x - y, x).

Fixpoint iter_step (a : Q) (n : nat) (p : Q * Q) : Q * Q :=
  match n with
  | O => p
  | S k => step a (iter_step a k p)
  end.

Definition Qpair_eq (p q : Q * Q) : Prop := fst p == fst q /\ snd p == snd q.
Infix "=p=" := Qpair_eq (at level 70).

(* ------------------------------------------------------------------ *)
(*  BRIDGE: at a=2, the stepper IS the i-rotation matrix action        *)
(*  (x,y) |-> (-y,x), matching InfoImaginaryOrder's i := (0,1) acting  *)
(*  by complex multiplication (x,y)*i = (-y,x).                        *)
(* ------------------------------------------------------------------ *)

Theorem step2_is_rotation : forall x y : Q, step 2 (x, y) =p= (-y, x).
Proof. intros x y. unfold step, Qpair_eq. simpl. split; ring. Qed.

Theorem step2_squares_to_negation : forall x y : Q,
  iter_step 2 2 (x, y) =p= (-x, -y).
Proof. intros x y. simpl. unfold step, Qpair_eq. simpl. split; ring. Qed.

Theorem step2_period4 : forall x y : Q, iter_step 2 4 (x, y) =p= (x, y).
Proof. intros x y. simpl. unfold step, Qpair_eq. simpl. split; ring. Qed.

(* minimality on a concrete nonzero witness, mirroring how
   InfoImaginaryOrder checks i, i^2, i^3 are each <> 1 on components *)
Theorem step2_not_fixed_at_1 : fst (iter_step 2 1 (1, 0)) == 0
                             /\ snd (iter_step 2 1 (1, 0)) == 1.
Proof. simpl. unfold step. split; ring. Qed.

Theorem step2_not_fixed_at_2 : fst (iter_step 2 2 (1, 0)) == -1
                             /\ snd (iter_step 2 2 (1, 0)) == 0.
Proof. simpl. unfold step. split; ring. Qed.

(* ------------------------------------------------------------------ *)
(*  THE OTHER CRYSTALLOGRAPHIC WINDOW POINTS: a=1 (period 6),          *)
(*  a=3 (period 3). Hand-verified before writing, both confirmed via   *)
(*  direct matrix power computation.                                   *)
(* ------------------------------------------------------------------ *)

Theorem step1_cubes_to_negation : forall x y : Q,
  iter_step 1 3 (x, y) =p= (-x, -y).
Proof. intros x y. simpl. unfold step, Qpair_eq. simpl. split; ring. Qed.

Theorem step1_period6 : forall x y : Q, iter_step 1 6 (x, y) =p= (x, y).
Proof. intros x y. simpl. unfold step, Qpair_eq. simpl. split; ring. Qed.

Theorem step3_cubes_to_identity : forall x y : Q,
  iter_step 3 3 (x, y) =p= (x, y).
Proof. intros x y. simpl. unfold step, Qpair_eq. simpl. split; ring. Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions step2_is_rotation.
Print Assumptions step2_squares_to_negation.
Print Assumptions step2_period4.
Print Assumptions step2_not_fixed_at_1.
Print Assumptions step2_not_fixed_at_2.
Print Assumptions step1_cubes_to_negation.
Print Assumptions step1_period6.
Print Assumptions step3_cubes_to_identity.

End ModeRotation.
