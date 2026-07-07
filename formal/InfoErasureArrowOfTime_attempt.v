(******************************************************************************)
(* InfoErasureArrowOfTime_attempt.v                                           *)
(*                                                                            *)
(* Erasure, un-erasure, and the arithmetic arrow of time, over Q (QArith).    *)
(*                                                                            *)
(* CLAIM (what the Coq actually PROVES, machine-checked over Q):               *)
(*   1. x0 is a TOTAL map on Q: forall a, a*0 == 0.                            *)
(*   2. x0 is NON-INJECTIVE (erasure): two DISTINCT inputs (3#1 and 5#1),      *)
(*      3#1 <> 5#1, both map to the single output 0. Two distinctions are      *)
(*      collapsed into one indistinguishable value: information is destroyed.  *)
(*   3. No un-erase for a real distinction: for A <> 0 there is NO q with      *)
(*      q*0 == A. "A/0" has no answer (no readout).                           *)
(*   4. 0/0 is non-unique: EVERY q satisfies q*0 == 0, and two distinct        *)
(*      q (0#1 and 7#1) both "solve" it, so 0/0 cannot pick out one q.         *)
(*   5. The ASYMMETRY: x0 is total (step 1) yet non-injective (step 2) and     *)
(*      has no preimage for nonzero targets (step 3), hence no two-sided       *)
(*      inverse. That is the machine-checked irreversibility core.             *)
(*                                                                            *)
(* SCOPE / TIER HONESTY (a skeptic should read this):                         *)
(*   [Th_coqc]  Steps 1-5 are the Coq content. They are ELEMENTARY, in fact    *)
(*              near-definitional in any field: a*0==0 is a ring axiom's        *)
(*              consequence, and everything else is bookkeeping on top of it.  *)
(*              The Coq here is a THIN, honest anchor - it certifies the        *)
(*              injectivity-failure and the no-preimage fact, nothing deeper.   *)
(*                                                                            *)
(*   [Dr]       The INTERPRETATION is the point, and it is Dr (readout-not-     *)
(*              truth), NOT proved by the Coq:                                 *)
(*                - x0 = erasure of a distinction into indistinguishability;    *)
(*                  irreversible; carries a Landauer thermodynamic cost.        *)
(*                - div-by-0 = trying to read a distinction back OUT of         *)
(*                  indistinguishability = a non-readout (undefined for A<>0,    *)
(*                  indeterminate for A=0).                                     *)
(*                - 1/0 -> infinity is an I4 injected-infinity that this        *)
(*                  project REFUSES; there is no such element of Q here.        *)
(*                - the many-to-one(x0) / no-inverse(div0) ASYMMETRY read AS    *)
(*                  the irreversibility of erasure = the ARROW OF TIME at the    *)
(*                  arithmetic level.  <-- this arrow-of-time reading is [Dr].   *)
(*              The Coq only anchors the injectivity-failure / no-inverse that   *)
(*              this reading rests ON; it does not prove the reading.           *)
(******************************************************************************)

From Coq Require Import QArith.

Open Scope Q_scope.

(* ------------------------------------------------------------------------- *)
(* Step 1. x0 is a TOTAL map on Q: every input has an output, and it is 0.    *)
(* ------------------------------------------------------------------------- *)

Theorem mul0_total : forall a : Q, a * 0 == 0.
Proof.
  intro a. ring.
Qed.

(* ------------------------------------------------------------------------- *)
(* Step 2. x0 is NON-INJECTIVE (erasure): a concrete collision of DISTINCT    *)
(*         inputs onto the single output 0.                                    *)
(* ------------------------------------------------------------------------- *)

Theorem three_times_zero : (3#1) * 0 == 0.
Proof. reflexivity. Qed.

Theorem five_times_zero : (5#1) * 0 == 0.
Proof. reflexivity. Qed.

Theorem three_neq_five : ~ ((3#1) == (5#1)).
Proof. intro H. discriminate H. Qed.

(* The collision, packaged: two distinct inputs, equal outputs.               *)
Theorem mul0_not_injective :
  exists a b : Q, ~ (a == b) /\ (a * 0 == b * 0).
Proof.
  exists (3#1), (5#1). split.
  - exact three_neq_five.
  - rewrite three_times_zero, five_times_zero. reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* Step 3a. No un-erase for a real distinction: for A <> 0 there is NO q       *)
(*          with q*0 == A. "A/0" has no answer.                                *)
(* ------------------------------------------------------------------------- *)

Theorem div0_no_inverse_nonzero :
  forall (q A : Q), ~ (A == 0) -> ~ (q * 0 == A).
Proof.
  intros q A HA Hq.
  apply HA.
  rewrite <- Hq.
  apply mul0_total.
Qed.

(* Concrete instance: nothing times 0 gives 1.                                 *)
Theorem no_q_gives_one : forall q : Q, ~ (q * 0 == 1).
Proof.
  intro q. apply div0_no_inverse_nonzero.
  intro H. discriminate H.
Qed.

(* ------------------------------------------------------------------------- *)
(* Step 3b. 0/0 is non-unique (indeterminate): EVERY q solves q*0==0, and two  *)
(*          DISTINCT q both solve it, so 0/0 cannot pick out a single answer.   *)
(* ------------------------------------------------------------------------- *)

Theorem all_q_solve_zero_over_zero : forall q : Q, q * 0 == 0.
Proof. exact mul0_total. Qed.

Theorem div0_no_unique_inverse :
  exists q1 q2 : Q,
    ~ (q1 == q2) /\ (q1 * 0 == 0) /\ (q2 * 0 == 0).
Proof.
  exists (0#1), (7#1). split; [| split].
  - intro H. discriminate H.
  - apply mul0_total.
  - apply mul0_total.
Qed.

(* ------------------------------------------------------------------------- *)
(* Step 5. The ASYMMETRY / irreversibility core, bundled into one statement:   *)
(*   x0 is TOTAL (every a has an output) AND non-injective (a distinct         *)
(*   collision exists) AND has no preimage for a nonzero target - hence no      *)
(*   two-sided inverse. This conjunction is the machine-checked irreversibility.*)
(* ------------------------------------------------------------------------- *)

Theorem erasure_asymmetry :
  (* total: every input has the output 0 *)
  (forall a : Q, a * 0 == 0)
  /\
  (* non-injective: distinct inputs, one output (erasure) *)
  (exists a b : Q, ~ (a == b) /\ (a * 0 == b * 0))
  /\
  (* no un-erase of a real distinction: nothing maps to a nonzero target *)
  (forall (q A : Q), ~ (A == 0) -> ~ (q * 0 == A)).
Proof.
  split; [| split].
  - apply mul0_total.
  - exact mul0_not_injective.
  - exact div0_no_inverse_nonzero.
Qed.

(* ------------------------------------------------------------------------- *)
(* Assumption audit: every theorem must be closed under the global context.    *)
(* ------------------------------------------------------------------------- *)

Print Assumptions mul0_total.
Print Assumptions mul0_not_injective.
Print Assumptions div0_no_inverse_nonzero.
Print Assumptions no_q_gives_one.
Print Assumptions div0_no_unique_inverse.
Print Assumptions erasure_asymmetry.
