(* ===================================================================== *)
(*  InfoOperatorLosesPropertyAtEndpoints_attempt.v                          *)
(*  AN OPERATOR LOSES A DEFINING PROPERTY AT EACH REFUSED ENDPOINT 0 AND    *)
(*  INFINITY.  The canonical operator here is MULTIPLICATION over Q         *)
(*  (QArith).  On the finite interior (factor c <> 0) multiplication keeps  *)
(*  its defining properties -- cancellation and invertibility -- but each   *)
(*  is LOST exactly at the endpoint 0 (multiplication by 0 is non-injective *)
(*  and has no un-erase / inverse), and Q itself has NO maximal / infinity  *)
(*  element, so there is no infinity target to operate on -- closure at     *)
(*  infinity fails: Q is unbounded.  Nothing is admitted; every claim is     *)
(*  an elementary field / Archimedean fact, machine-checked over Q.         *)
(*                                                                          *)
(*  ------------------------- SCOPE (read me) --------------------------    *)
(*  [Th_coqc]  (actually machine-checked below, coqc, axiom-free) --        *)
(*    FOR MULTIPLICATION specifically: cancellation + invertibility hold    *)
(*    on the finite interior (c <> 0) and are LOST at 0 (non-injective,     *)
(*    no inverse); and Q has no maximal / infinity element (unbounded), so  *)
(*    there is no infinity to operate on.  BE HONEST: these are elementary  *)
(*    field / Archimedean facts -- a thin anchor, not a deep theorem.       *)
(*      cancellation_holds_offzero  a*c==b*c, c<>0  =>  a==b                 *)
(*      cancellation_fails_at_zero  exists a b, ~(a==b) /\ a*0==b*0          *)
(*      inverse_exists_offzero      c<>0  =>  exists q, c*q==1               *)
(*      no_inverse_at_zero          forall q, ~(0*q==1)                      *)
(*      no_maximal_element          forall B, exists q, B<q  (q=B+1)         *)
(*      operator_breaks_at_both_endpoints  the bundled honest core          *)
(*                                                                          *)
(*  [Dr]  (NOT proved by Coq -- the universal reading):                     *)
(*    EVERY well-behaved (finite-property-preserving) operator loses a      *)
(*    defining property (inverse / cancellation / closure / totality) at    *)
(*    each refused endpoint 0 and infinity; touching an endpoint always     *)
(*    costs a property (paradox or amputation).  Mathematics' consistent    *)
(*    infinities each PAY this price -- limits never touch infinity,        *)
(*    cardinals drop cancellation, extended reals drop totality, ZFC drops  *)
(*    unrestricted comprehension -- which is the evidence.  The operator    *)
(*    lives only in the finite interior between the two refused endpoints.  *)
(*    0-side anchor: InfoErasureArrowOfTime (x*0 has no inverse).           *)
(*    inf-side anchor: InfoZeroInfinityReciprocal (unbounded reciprocal).   *)
(*    This file unifies them as -- property lost at each endpoint.          *)
(* ===================================================================== *)

Require Import QArith.
Require Import Qcanon.

Local Open Scope Q_scope.

(* --------------------------------------------------------------------- *)
(*  AT ZERO -- multiplication loses cancellation and invertibility.       *)
(* --------------------------------------------------------------------- *)

(* (1) Cancellation is valid in the finite interior (nonzero factor). *)
Theorem cancellation_holds_offzero :
  forall a b c : Q, ~ (c == 0) -> a * c == b * c -> a == b.
Proof.
  intros a b c Hc Heq.
  apply (Qmult_inj_r a b c Hc).
  exact Heq.
Qed.

(* (2) Cancellation BREAKS exactly at 0: distinct 3 and 5 collide. *)
Theorem cancellation_fails_at_zero :
  exists a b : Q, ~ (a == b) /\ a * 0 == b * 0.
Proof.
  exists (3 # 1), (5 # 1).
  split.
  - discriminate.
  - reflexivity.
Qed.

(* (3) Every nonzero c has a multiplicative inverse q = /c. *)
Theorem inverse_exists_offzero :
  forall c : Q, ~ (c == 0) -> exists q : Q, c * q == 1.
Proof.
  intros c Hc.
  exists (/ c).
  apply Qmult_inv_r.
  exact Hc.
Qed.

(* (4) 0 has NO multiplicative inverse: x*0 has no un-erase. *)
Theorem no_inverse_at_zero :
  forall q : Q, ~ (0 * q == 1).
Proof.
  intros q H.
  rewrite Qmult_0_l in H.
  discriminate.
Qed.

(* --------------------------------------------------------------------- *)
(*  AT INFINITY -- Q has no infinity element (unbounded, not closed up).  *)
(* --------------------------------------------------------------------- *)

(* (5) There is no largest Q: infinity is not an element (q = B+1). *)
Theorem no_maximal_element :
  forall B : Q, exists q : Q, B < q.
Proof.
  intros B.
  exists (B + 1).
  rewrite <- (Qplus_0_r B) at 1.
  apply Qplus_lt_r.
  reflexivity.
Qed.

(* --------------------------------------------------------------------- *)
(*  (6) Concrete numeric witnesses (vm_compute / reflexivity).            *)
(* --------------------------------------------------------------------- *)

(* cancellation collision at 0: 3*0 == 5*0 (yet 3 <> 5). *)
Theorem witness_cancellation_collision : (3 # 1) * 0 == (5 # 1) * 0.
Proof. reflexivity. Qed.

Theorem witness_three_neq_five : ~ ((3 # 1) == (5 # 1)).
Proof. discriminate. Qed.

(* interior inverse: (2#1)*(1#2) == 1. *)
Theorem witness_inverse_two : (2 # 1) * (1 # 2) == 1.
Proof. reflexivity. Qed.

(* no-inverse instance at 0: 0*(5#1) is 0, not 1. *)
Theorem witness_no_inverse_at_zero : ~ (0 * (5 # 1) == 1).
Proof. discriminate. Qed.

(* unbounded: 100 < 101 (a concrete step past any given bound). *)
Theorem witness_unbounded_step : (100 # 1) < (101 # 1).
Proof. reflexivity. Qed.

(* --------------------------------------------------------------------- *)
(*  BUNDLE -- the honest core, machine-checked in one conjunction.        *)
(* --------------------------------------------------------------------- *)

Theorem operator_breaks_at_both_endpoints :
  (* interior: cancellation + invertibility hold off-zero *)
  (forall a b c : Q, ~ (c == 0) -> a * c == b * c -> a == b) /\
  (forall c : Q, ~ (c == 0) -> exists q : Q, c * q == 1) /\
  (* endpoint 0: non-injective (cancellation fails) and no inverse *)
  (exists a b : Q, ~ (a == b) /\ a * 0 == b * 0) /\
  (forall q : Q, ~ (0 * q == 1)) /\
  (* endpoint infinity: no maximal element (Q unbounded, not closed up) *)
  (forall B : Q, exists q : Q, B < q).
Proof.
  repeat split.
  - exact cancellation_holds_offzero.
  - exact inverse_exists_offzero.
  - exact cancellation_fails_at_zero.
  - exact no_inverse_at_zero.
  - exact no_maximal_element.
Qed.

(* --------------------------------------------------------------------- *)
(*  AXIOM AUDIT -- every core theorem closed under the global context.    *)
(* --------------------------------------------------------------------- *)

Print Assumptions cancellation_holds_offzero.
Print Assumptions cancellation_fails_at_zero.
Print Assumptions inverse_exists_offzero.
Print Assumptions no_inverse_at_zero.
Print Assumptions no_maximal_element.
Print Assumptions witness_cancellation_collision.
Print Assumptions witness_inverse_two.
Print Assumptions witness_no_inverse_at_zero.
Print Assumptions witness_unbounded_step.
Print Assumptions operator_breaks_at_both_endpoints.
