(* ===================================================================== *)
(*  InfoTensorEvolution.v                                                 *)
(*  GAP-2 OPENER: THE EXACT COMPONENTWISE UPDATE LAW OF THE FIELD TENSOR. *)
(*                                                                        *)
(*  For the rank-one tensor built from a field, tens x i j := x i * x j,  *)
(*  one update step x |-> x + d obeys an EXACT componentwise law:         *)
(*                                                                        *)
(*    tens(x+d) - tens(x)  ==  x (X) d  +  d (X) x  +  d (X) d            *)
(*                                                                        *)
(*  (all three terms explicit, nothing dropped), the tensor is exactly    *)
(*  symmetric, the diagonal (trace density) obeys the same law with       *)
(*  2 x_i d_i + d_i^2, and subtracting the symmetric-linear part leaves   *)
(*  EXACTLY the second-order term d (X) d.                                *)
(*                                                                        *)
(*  HONESTLY NOT CLAIMED: any field equation for a continuum readout of   *)
(*  this tensor (the remaining content of the gap), any covariance        *)
(*  statement, and any conservation law; those are separate targets.      *)
(*  This file supplies the exact algebra every such attempt must use.     *)
(*  Expected: Print Assumptions => Closed under the global context.       *)
(* ===================================================================== *)

Require Coq.QArith.QArith.

Module TensorEvolution.

Import Coq.QArith.QArith.
Local Open Scope Q_scope.

Definition tens (x : nat -> Q) (i j : nat) : Q := x i * x j.

Theorem tensor_sym : forall (x : nat -> Q) (i j : nat),
  tens x i j == tens x j i.
Proof. intros x i j. unfold tens. ring. Qed.

Theorem tensor_step_exact : forall (x d : nat -> Q) (i j : nat),
  tens (fun k => x k + d k) i j - tens x i j
  == x i * d j + d i * x j + d i * d j.
Proof. intros x d i j. unfold tens. ring. Qed.

Theorem trace_step_exact : forall (x d : nat -> Q) (i : nat),
  tens (fun k => x k + d k) i i - tens x i i
  == 2 * (x i * d i) + d i * d i.
Proof. intros x d i. unfold tens. ring. Qed.

Theorem second_order_residual : forall (x d : nat -> Q) (i j : nat),
  (tens (fun k => x k + d k) i j - tens x i j)
  - (x i * d j + d i * x j)
  == d i * d j.
Proof. intros x d i j. unfold tens. ring. Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions tensor_sym.
Print Assumptions tensor_step_exact.
Print Assumptions trace_step_exact.
Print Assumptions second_order_residual.

End TensorEvolution.
