(* ===================================================================== *)
(*  InfoShiftAverage.v                                                    *)
(*  EXACT HOMOGENIZATION AT THE WINDOW CENTER: THE ORBIT AVERAGE OF THE   *)
(*  COEFFICIENT SHIFT IS A CONSTANT, WITH NO LIMIT TAKEN.                 *)
(*                                                                        *)
(*  At the stability-window center the one-step mode map is the exact     *)
(*  i-rotation on Q^2 (period four).  Along that orbit the pointwise      *)
(*  coefficient shift 3*g*c^2 of the cubic linearization therefore has    *)
(*  an EXACT rational average:                                            *)
(*                                                                        *)
(*      (1/4) * sum over one period of 3*g*c(t)^2                         *)
(*         ==  (3*g/2) * (x^2 + y^2)                                      *)
(*                                                                        *)
(*  --- a homogenization statement that is pure algebra, because the      *)
(*  crystallographic period is exact.  Results: rot_period4 (local,       *)
(*  self-contained), orbit_shift_sum_exact, homogenized_shift_exact,      *)
(*  homogenized_nonneg, homogenized_pos.                                  *)
(*                                                                        *)
(*  SCOPE, STATED EXACTLY: this closes OB-HOMOGENIZATION at the           *)
(*  exact-period instance (window center; the same route covers the       *)
(*  other crystallographic periods).  The general statement --- an        *)
(*  effective coefficient for APERIODIC backgrounds, and the passage      *)
(*  from the averaged coefficient to an effective inertia in the          *)
(*  propagation problem --- remains Open.  One joint is instanced,        *)
(*  not the loop closed.                                                  *)
(*  Expected: Print Assumptions => Closed under the global context.       *)
(* ===================================================================== *)

Require Coq.QArith.QArith.
Require Coq.micromega.Lqa.

Module ShiftAverage.

Import Coq.QArith.QArith.
Import Coq.micromega.Lqa.
Local Open Scope Q_scope.

(* the exact i-rotation on Q^2 *)
Definition rot (p : Q * Q) : Q * Q := (snd p, - fst p).

Theorem rot_period4 : forall p : Q * Q,
  fst (rot (rot (rot (rot p)))) == fst p
  /\ snd (rot (rot (rot (rot p)))) == snd p.
Proof. intros [x y]. simpl. split; ring. Qed.

(* pointwise coefficient shift carried by amplitude c *)
Definition qsh (g c : Q) : Q := 3 * g * (c * c).

(* one full period of the first component: x, y, -x, -y *)
Theorem orbit_shift_sum_exact : forall (g x y : Q),
  qsh g (fst (x, y)) + qsh g (fst (rot (x, y)))
  + qsh g (fst (rot (rot (x, y)))) + qsh g (fst (rot (rot (rot (x, y)))))
  == 6 * g * (x * x + y * y).
Proof. intros g x y. unfold qsh. simpl. ring. Qed.

Theorem homogenized_shift_exact : forall (g x y : Q),
  (1 # 4) *
  ( qsh g (fst (x, y)) + qsh g (fst (rot (x, y)))
    + qsh g (fst (rot (rot (x, y)))) + qsh g (fst (rot (rot (rot (x, y))))) )
  == (3 # 2) * g * (x * x + y * y).
Proof. intros g x y. unfold qsh. simpl. ring. Qed.

Theorem homogenized_nonneg : forall (g x y : Q),
  0 <= g -> 0 <= (3 # 2) * g * (x * x + y * y).
Proof. intros g x y Hg. nra. Qed.

Theorem homogenized_pos : forall (g x y : Q),
  0 < g -> ~ (x == 0) -> 0 < (3 # 2) * g * (x * x + y * y).
Proof.
  intros g x y Hg Hx.
  assert (Hxx : 0 < x * x).
  { destruct (Q_dec 0 x) as [[Hl | Hr] | He]; [nra | nra |].
    exfalso. apply Hx. symmetry. exact He. }
  nra.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions rot_period4.
Print Assumptions orbit_shift_sum_exact.
Print Assumptions homogenized_shift_exact.
Print Assumptions homogenized_nonneg.
Print Assumptions homogenized_pos.

End ShiftAverage.
