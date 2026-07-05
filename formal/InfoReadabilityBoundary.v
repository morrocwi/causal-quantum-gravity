(* ===================================================================
   InfoReadabilityBoundary_attempt.v

   ONE MORE INSTANCE toward this repo's own crystallographic-restriction-
   adjacent story, alongside InfoModeRotation_attempt.v's rational
   period-4/6/3 witnesses (a=2,1,3 in the stepper
   S_a := [[2-a,-1],[1,0]] on the window a in [0,4]).

   InfoModeRotation_attempt.v mechanized the FORWARD direction (a=1,2,3
   give an exactly-periodic stepper) and stated the period-5 non-example
   ONLY in prose (a = (5-sqrt5)/2 is irrational, hence unreachable by any
   a in Q), because expressing sqrt5 needs Coq.Reals and that file
   deliberately stays Q-only.

   THIS FILE closes that prose gap with an actual Coq proof, entirely in
   Q -- no Coq.Reals needed -- by working with the ALGEBRAIC CONDITION
   for period 5 instead of sqrt5 itself.

   THE ALGEBRA (independently verified by two reviewers via sympy against
   the real `step` definition below, both confirming the same polynomial
   identity by `expand()`): the off-diagonal entry of the 5th iterate of
   `step`, as a polynomial in `a`, is

       poly5(a) := -a^4 + 8a^3 - 21a^2 + 20a - 5

   and this factors EXACTLY as

       poly5(a) == -(a^2 - 5a + 5) * (a^2 - 3a + 1)                [star]

   Roots of `a^2-5a+5` are `(5+-sqrt5)/2` -- these are the genuine
   period-5 witnesses (M^5 = I). Roots of `a^2-3a+1` are `(3+-sqrt5)/2`
   -- these give M^5 = -I, i.e. period 10, NOT period 5. IMPORTANT: only
   the FIRST quadratic's roots are period-5 witnesses; the second
   quadratic is algebraically entangled with the same off-diagonal
   vanishing condition (poly5(a)==0) but is a different dynamical fact.
   Both quadratics share discriminant 5, and that shared discriminant is
   ALL the theorem below actually needs: it never distinguishes which
   quadratic a root of poly5 solves, only that EITHER way, some rational
   value would have to square to 5.

   RESULT (three self-contained Q/Z facts, all closed under the global
   context, no admits):
     (1) no_rational_sqrt5 : no q:Q has q*q==5 -- the same
         readout-not-truth shape as InfoIrrationalNonReadout_attempt.v's
         sqrt2 result, proved from scratch here for 5 (mod-5 divisibility
         descent rather than parity descent, since 5 is odd).
     (2) poly5_factors : the factorization identity [star] above, a `ring`
         check once poly5 is given as its own Definition (matching the
         confirmed sympy expansion).
     (3) no_rational_period5 : no a:Q makes poly5(a)==0. Proved by: the
         factorization forces one of the two quadratic factors to vanish
         (Q has no zero divisors, Qmult_integral); completing the square
         on whichever one vanishes produces a rational value squaring to
         5 in EITHER case ((2a-5)^2==5 or (2a-3)^2==5); no_rational_sqrt5
         forbids both. Hence NO rational a makes the 5th-iterate's
         off-diagonal entry vanish -- period 5 is unreachable by any
         rational stepper parameter.

   HONEST SCOPE -- read before citing this as more than it is:
     - This is a NECESSARY-condition non-existence result about ONE
       polynomial condition (the 5th-iterate off-diagonal vanishing),
       not a general classification of all periods reachable by rational
       a. It does NOT claim, and this file does not attempt, that
       {1,2,3,4,6} is the COMPLETE set of periods reachable in [0,4] --
       that is exactly the GENERAL crystallographic restriction theorem
       (trace = 2cos(2*pi*k/n) in Q forces n in {1,2,3,4,6}), which is
       real, well-established literature (Coxeter groups / crystallography)
       and is CITED here, registered in `docs/root/EQUATION_REGISTRY.md`,
       NOT mechanized: PT(lit), not Th_coqc. Proving it in general would
       require handling every n, not just n=5, and is out of scope for
       this file.
     - The one small composing remark below (period4_and_period5_are_
       distinct) is a trivial rationality/irrationality distinction, not
       a claim that the period set is complete.

   TIER: every theorem below is Tier-0, Q-only (with an internal Z-level
   descent lemma for the number theory), axiom-free (ring/lia/nia/lra).
   =================================================================== *)

Require Import Coq.ZArith.ZArith.
Require Coq.QArith.QArith.
Require Import Coq.micromega.Lia.
Require Coq.micromega.Lqa.

Import Coq.QArith.QArith.
Import Coq.micromega.Lqa.

Module ReadabilityBoundary.

(* ------------------------------------------------------------------ *)
(*  PART 1: no rational number squares to 5 (the sqrt5-is-a-non-       *)
(*  readout fact), proved from scratch via a mod-5 divisibility        *)
(*  descent on Z (the odd-prime analogue of the classical even-        *)
(*  descent proof of sqrt2's irrationality).                            *)
(* ------------------------------------------------------------------ *)

Open Scope Z_scope.

(* If 5 divides a*a then 5 divides a: proved directly by writing
   a = 5*q + r with 0<=r<5 (Euclidean division) and observing r*r must
   itself be a multiple of 5, which forces r=0 by exhaustive case check
   on the five possible remainders. *)
Lemma five_dvd_sq : forall a k : Z, a * a = 5 * k -> (5 | a)%Z.
Proof.
  intros a k Heq.
  assert (Hdm : a = 5 * (a / 5) + a mod 5) by (apply Z.div_mod; lia).
  assert (Hb : 0 <= a mod 5 < 5) by (apply Z.mod_pos_bound; lia).
  set (q := a / 5) in *.
  set (r := a mod 5) in *.
  rewrite Hdm in Heq.
  set (m := k - 5 * q * q - 2 * q * r) in *.
  assert (Hr2 : r * r = 5 * m) by (unfold m; nia).
  assert (Hcase : r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4) by lia.
  destruct Hcase as [H0 | [H1 | [H2 | [H3 | H4]]]]; subst r.
  - exists q. lia.
  - lia.
  - lia.
  - lia.
  - lia.
Qed.

(* NO positive-plus-nonneg integer solution to a^2 = 5*b^2 -- infinite
   descent via divisibility by 5, mirroring
   InfoIrrationalNonReadout_attempt.v's even-descent for sqrt2 but using
   mod-5 case analysis (five_dvd_sq) in place of parity. *)
Lemma no_int_sqrt5 : forall b, 0 < b -> forall a, 0 <= a -> a * a = 5 * (b * b) -> False.
Proof.
  intro b0. remember (Z.to_nat b0) as m0 eqn:Hm0.
  revert b0 Hm0.
  induction m0 as [m0 IH] using lt_wf_ind.
  intros b Hm0 Hb a Ha Heq.
  assert (Hda : (5 | a)%Z) by (apply (five_dvd_sq a (b * b)); exact Heq).
  destruct Hda as [c Hc].
  assert (Hb2 : b * b = 5 * (c * c)) by nia.
  assert (Hdb : (5 | b)%Z) by (apply (five_dvd_sq b (c * c)); exact Hb2).
  destruct Hdb as [d Hd].
  assert (Hd_pos : 0 < d) by nia.
  assert (Hc2 : c * c = 5 * (d * d)) by nia.
  apply (IH (Z.to_nat d)) with (b0 := d) (a := Z.abs c).
  - assert (Z.to_nat d < Z.to_nat b)%nat by (apply Z2Nat.inj_lt; lia). lia.
  - reflexivity.
  - exact Hd_pos.
  - apply Z.abs_nonneg.
  - assert (Z.abs c * Z.abs c = c * c) by (rewrite <- Z.abs_mul; apply Z.abs_eq; apply Z.square_nonneg).
    rewrite H. exact Hc2.
Qed.

Open Scope Q_scope.

(* THE READOUT-NOT-TRUTH BOUNDARY, NUMERICAL, FOR 5: no rational readout
   q has q^2 == 5. Same shape as InfoIrrationalNonReadout_attempt.v's
   sqrt2_is_not_a_readout, proved independently here for 5. *)
Theorem no_rational_sqrt5 : forall q : Q, ~ (q * q == 5).
Proof.
  intros q Hq.
  destruct q as [a b].
  unfold Qmult, Qeq in Hq. simpl in Hq.
  assert (Hint : (a * a = 5 * (Z.pos b * Z.pos b))%Z) by (simpl in Hq; lia).
  destruct (Z.le_gt_cases 0 a) as [Hpos | Hneg].
  - apply (no_int_sqrt5 (Z.pos b)) with (a := a); [lia | exact Hpos | exact Hint].
  - apply (no_int_sqrt5 (Z.pos b)) with (a := (-a)%Z); [lia | lia |].
    assert (((-a) * (-a) = a * a)%Z) by ring. rewrite H. exact Hint.
Qed.

Print Assumptions no_rational_sqrt5.

(* ------------------------------------------------------------------ *)
(*  PART 2: the confirmed 5th-iterate off-diagonal polynomial and its  *)
(*  exact factorization (sympy-confirmed by two independent reviewers  *)
(*  against the real iterated `step` matrix; taken here as the given,  *)
(*  already-verified starting polynomial per the task's exact facts).   *)
(* ------------------------------------------------------------------ *)

(* The stepper from InfoModeRotation_attempt.v, reproduced here so this
   file is self-contained (matches that file's exact definition). *)
Definition step (a : Q) (p : Q * Q) : Q * Q :=
  let '(x, y) := p in ((2 - a) * x - y, x).

Fixpoint iter_step (a : Q) (n : nat) (p : Q * Q) : Q * Q :=
  match n with
  | O => p
  | S k => step a (iter_step a k p)
  end.

(* The 5th-iterate off-diagonal polynomial, as its own Definition
   (confirmed equal, by sympy expand() against the real iterated matrix,
   to -a^4+8a^3-21a^2+20a-5). *)
Definition poly5 (a : Q) : Q := -a * a * a * a + 8 * a * a * a - 21 * a * a + 20 * a - 5.

(* Sanity check tying poly5 to the actual stepper: starting the recursion
   at (x,y)=(0,1), the x-component after 5 steps is exactly the M^5[0,1]
   matrix entry -- i.e. exactly the polynomial poly5 -- for every a, not
   just a sampled point. This is a live cross-check that poly5 is not an
   unmoored polynomial but the actual off-diagonal quantity this file
   reasons about. *)
Example poly5_matches_iterate :
  forall a : Q, fst (iter_step a 5 (0, 1)) == poly5 a.
Proof. intro a. simpl. unfold step. simpl. unfold poly5. ring. Qed.

(* THE FACTORIZATION IDENTITY: a `ring` check of the confirmed algebra. *)
Theorem poly5_factors : forall a : Q,
  poly5 a == -(a * a - 5 * a + 5) * (a * a - 3 * a + 1).
Proof. intro a. unfold poly5. ring. Qed.

Print Assumptions poly5_factors.

(* ------------------------------------------------------------------ *)
(*  PART 3: NO rational a makes the 5th-iterate's off-diagonal entry    *)
(*  vanish. Precise, honestly-scoped statement -- see header SCOPE:    *)
(*  this is a necessary-condition non-existence result about ONE        *)
(*  polynomial condition, not a classification of all reachable         *)
(*  periods.                                                            *)
(* ------------------------------------------------------------------ *)

Theorem no_rational_period5 : forall a : Q, ~ (poly5 a == 0).
Proof.
  intros a Ha.
  rewrite poly5_factors in Ha.
  assert (Hz : (a * a - 5 * a + 5) * (a * a - 3 * a + 1) == 0) by lra.
  destruct (Qmult_integral _ _ Hz) as [H1 | H2].
  - apply (no_rational_sqrt5 (2 * a - 5)).
    assert ((2 * a - 5) * (2 * a - 5) == 4 * (a * a - 5 * a + 5) + 5) by ring.
    rewrite H. rewrite H1. ring.
  - apply (no_rational_sqrt5 (2 * a - 3)).
    assert ((2 * a - 3) * (2 * a - 3) == 4 * (a * a - 3 * a + 1) + 5) by ring.
    rewrite H. rewrite H2. ring.
Qed.

Print Assumptions no_rational_period5.

(* ------------------------------------------------------------------ *)
(*  ONE small, honestly-scoped composing remark: the a=2 witness        *)
(*  (InfoModeRotation_attempt.v's period-4 point) is rational, and is    *)
(*  therefore automatically distinct from any root of poly5 (which, by   *)
(*  no_rational_period5, no rational number can be). This is NOT a       *)
(*  claim that {1,2,3,4,6} is the complete period set -- see header      *)
(*  SCOPE -- just the trivial observation that the period-4 witness      *)
(*  and "a solving the period-5 polynomial" can never coincide.          *)
(* ------------------------------------------------------------------ *)

Remark period4_and_period5_are_distinct :
  (exists a : Q, a == 2) /\ (forall a : Q, poly5 a == 0 -> False).
Proof. split; [exists 2; ring | exact no_rational_period5]. Qed.

Print Assumptions period4_and_period5_are_distinct.

End ReadabilityBoundary.

(* PRIMARY TARGETS: ReadabilityBoundary.no_rational_period5 (no rational  *)
(* stepper parameter a makes the 5th-iterate's off-diagonal entry poly5(a) *)
(* vanish -- the algebraic, Q-only face of period-5-is-unreachable-by-a     *)
(* rational-a, closing in actual Coq the gap InfoModeRotation_attempt.v      *)
(* left as prose) and .no_rational_sqrt5 (sqrt5 is a non-readout, the        *)
(* number-theoretic engine behind it, proved from scratch via mod-5          *)
(* divisibility descent). Backed by .poly5_factors (the sympy-confirmed       *)
(* factorization, closed by `ring`) and .no_int_sqrt5 (the Z-level infinite   *)
(* descent). As documented in the header SCOPE block: this is a necessary-    *)
(* condition non-existence result about ONE polynomial condition, NOT a       *)
(* mechanization of the general crystallographic restriction theorem (cited,  *)
(* registered in docs/root/EQUATION_REGISTRY.md, not proved here) and NOT a   *)
(* claim that {1,2,3,4,6} is the complete set of periods reachable in [0,4]. *)
