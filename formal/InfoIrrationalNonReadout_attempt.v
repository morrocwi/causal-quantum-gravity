(******************************************************************************)
(* InfoIrrationalNonReadout_attempt.v -- EXPLORATORY, single-attempt file      *)
(*  (not part of the build, not wired into any aggregate). Standalone; needs   *)
(*  only ZArith/QArith/Lia/Lqa (no repo file Required -- this is the           *)
(*  framework's OWN foundational question, answered from first principles).    *)
(*                                                                            *)
(* MOTIVATION -- the user asked, after the spectral-gap work: what IS an        *)
(*  irrational number in THIS framework's information terms? The Fiedler        *)
(*  value being irrational was named repeatedly as 'the wall.' This file        *)
(*  answers the question precisely, both conceptually and by proof.           *)
(*                                                                            *)
(* THE ANSWER: in a framework where information is delta_R (retained            *)
(*  difference) and every value is a finite rational READOUT, an IRRATIONAL     *)
(*  is precisely a NON-READOUT -- a value that no finite delta_R captures.      *)
(*  It is the readout-not-truth gap made numerical: a 'truth' that the           *)
(*  rational readouts approach to ANY tolerance yet NONE ever equals. This       *)
(*  is not a defect to be removed but the exact shape of the wall this           *)
(*  session kept meeting: a graph whose Fiedler value (spectral gap) is           *)
(*  irrational has an exact spectral gap that is a NON-READOUT -- boundable       *)
(*  by rational Poincare inequalities (readouts, which is why                    *)
(*  InfoCompleteGraphSpectralGap could cross it for K_n where the gap IS          *)
(*  rational) but never attained by any rational value, which is exactly          *)
(*  why the exact-eigenvalue route is closed in Q.                           *)
(*                                                                            *)
(* RESULT (self-checked numerically in Python with exact fractions before    *)
(*  any Coq was written -- no small a,b with a^2=2b^2; rational squeeze of      *)
(*  2 to any tolerance; Newton iterate approaching sqrt 2 with rational          *)
(*  terms):                                                                  *)
(*   (1) no_int_sqrt2: NO positive integers satisfy a^2 = 2*b^2 -- the           *)
(*       classical infinite even-descent, machine-checked from scratch          *)
(*       (a^2 even => a even; a=2c => b even; recurse on a strictly smaller       *)
(*       denominator via well-founded induction).                            *)
(*   (2) sqrt2_is_not_a_readout: NO rational q has q*q == 2 -- 'sqrt 2' is a      *)
(*       NON-READOUT, the numerical face of readout-not-truth. THIS IS THE        *)
(*       DEFINITION of irrational in the framework: a value the readouts          *)
(*       never attain.                                                       *)
(*   (3) sqrt2_squeezed_tightly: yet rational readouts squeeze it to any          *)
(*       tolerance (1.414^2 < 2 < 1.415^2, gap < 1/100) -- attainable-to-any-      *)
(*       tolerance, never attained: the precise structure of a non-readout        *)
(*       truth.                                                              *)
(*   (4) newton2_fixed_point_iff_sqrt2: the Newton map f(x)=(x+2/x)/2 has         *)
(*       f(q)==q IFF q*q==2 -- so its fixed point is exactly the                  *)
(*       non-readout sqrt 2.                                                  *)
(*   (5) newton2_has_no_rational_fixed_point: hence this CONTRACTION has NO        *)
(*       rational fixed point. This is the framework-native statement of the      *)
(*       wall: InfoContractionConvergence's convergence theorem needs a           *)
(*       RATIONAL fixed point to name; a contraction whose fixed point is          *)
(*       irrational produces a Cauchy readout sequence with NO readout limit       *)
(*       -- convergence in tolerance, never convergence to a point. Irrational      *)
(*       = a convergent readout sequence whose limit is not a readout.       *)
(*                                                                            *)
(* SCOPE -- read before trusting this as more than it is: this makes            *)
(*  'irrational = non-readout' PRECISE for the concrete witness sqrt 2, and       *)
(*  ties it exactly to the contraction framework's 'needs a rational fixed        *)
(*  point' hypothesis and thereby to the irrational-Fiedler spectral-gap wall.    *)
(*  It does NOT build a general theory of irrationals or of Dedekind cuts /        *)
(*  Cauchy-sequence reals (that IS the +reals machinery this repo               *)
(*  deliberately avoids); sqrt 2 stands as the canonical, fully-machine-           *)
(*  checked exemplar of the phenomenon. The reachability side (3) is             *)
(*  witnessed concretely (a single tight squeeze), not by a general               *)
(*  any-tolerance bisection induction -- the STRUCTURE (attainable-to-            *)
(*  tolerance yet unattained) is what the exemplar exhibits, and the             *)
(*  any-tolerance version is exactly InfoContractionConvergence's                 *)
(*  Archimedean machinery pointed at a non-rational limit. Does not modify         *)
(*  any repo file; says nothing about real particle mass ratios;                  *)
(*  engine.lexicon.stance_for('mass') remains [Open].                        *)
(******************************************************************************)

Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lqa.

Module InfoIrrationalNonReadout.
  Open Scope Z_scope.

  (* a^2 even => a even *)
  Lemma even_sq : forall a, Z.even (a*a) = true -> Z.even a = true.
  Proof.
    intros a H. rewrite Z.even_mul in H.
    destruct (Z.even a); [reflexivity | simpl in H; discriminate].
  Qed.

  (* NO positive integer solution to a^2 = 2 b^2 -- infinite even-descent,
     the number-theoretic heart of "sqrt 2 is not a readout". *)
  Lemma no_int_sqrt2 : forall b, 0 < b -> forall a, 0 <= a -> a*a = 2*(b*b) -> False.
  Proof.
    intro b0. remember (Z.to_nat b0) as m eqn:Hm.
    revert b0 Hm.
    induction m as [m IH] using lt_wf_ind.
    intros b Hm Hb a Ha Heq.
    (* a is even *)
    assert (Haev : Z.even a = true).
    { apply even_sq. assert (Z.even (a*a) = Z.even (2*(b*b))) by (rewrite Heq; reflexivity).
      rewrite H. rewrite Z.even_mul. reflexivity. }
    destruct (Z.even a) eqn:E; [| discriminate].
    apply Z.even_spec in E. destruct E as [c Hc].
    (* a = 2c, so 4c^2 = 2 b^2, b^2 = 2 c^2 *)
    assert (Hb2 : b*b = 2*(c*c)) by (subst a; lia).
    (* b even *)
    assert (Hbev : Z.even b = true).
    { apply even_sq. assert (Z.even (b*b) = Z.even (2*(c*c))) by (rewrite Hb2; reflexivity).
      rewrite H, Z.even_mul. reflexivity. }
    destruct (Z.even b) eqn:Eb; [| discriminate].
    apply Z.even_spec in Eb. destruct Eb as [d Hd].
    (* b = 2d, 0 < d < b, and c^2 = 2 d^2 *)
    assert (Hd_pos : 0 < d) by lia.
    assert (Hc2 : c*c = 2*(d*d)) by (subst b; lia).
    apply (IH (Z.to_nat d)) with (b0 := d) (a := Z.abs c).
    - assert (Z.to_nat d < Z.to_nat b)%nat by (apply Z2Nat.inj_lt; lia). lia.
    - reflexivity.
    - exact Hd_pos.
    - apply Z.abs_nonneg.
    - assert (Z.abs c * Z.abs c = c * c) by (rewrite <- Z.abs_mul; apply Z.abs_eq; apply Z.square_nonneg).
      rewrite H. exact Hc2.
  Qed.

  Print Assumptions no_int_sqrt2.

  Open Scope Q_scope.

  (* THE READOUT-NOT-TRUTH BOUNDARY, NUMERICAL: no rational readout q has
     q^2 == 2. "sqrt 2" names a truth that no finite information (no q:Q)
     captures -- it is a NON-READOUT. This is what "irrational" MEANS in this
     framework: a value the readouts never attain. *)
  Theorem sqrt2_is_not_a_readout : forall q : Q, ~ (q * q == 2).
  Proof.
    intros q Hq.
    (* q = a # b; q*q == 2 means (a*a) = 2*(b*b) as Z *)
    destruct q as [a b].
    unfold Qmult, Qeq in Hq. simpl in Hq.
    (* Hq : (a*a) * 1 = 2 * (Z.pos b * Z.pos b) after Qeq unfolding *)
    assert (Hint : (a*a = 2*(Z.pos b * Z.pos b))%Z).
    { simpl in Hq. lia. }
    destruct (Z.le_gt_cases 0 a) as [Hpos | Hneg].
    - apply (no_int_sqrt2 (Z.pos b)) with (a := a); [lia | exact Hpos | exact Hint].
    - apply (no_int_sqrt2 (Z.pos b)) with (a := (-a)%Z); [lia | lia |].
      assert (((-a)*(-a) = a*a)%Z) by ring. rewrite H. exact Hint.
  Qed.

  Print Assumptions sqrt2_is_not_a_readout.

  (* ...YET the truth is REACHABLE to any tolerance by rational readouts:
     for any eps > 0 there are readouts q_lo, q_hi with q_lo^2 < 2 < q_hi^2
     and the gap q_hi^2 - q_lo^2 below eps. The readouts squeeze the
     non-readout truth arbitrarily tightly -- they just never land on it.
     (Witnessed concretely rather than by a general bisection induction:
     the point is the STRUCTURE -- attainable-to-any-tolerance yet never
     attained -- which the concrete squeeze already exhibits.) *)
  Example sqrt2_squeezed_tightly :
    (1414#1000) * (1414#1000) < 2 /\ 2 < (1415#1000) * (1415#1000)
    /\ (1415#1000)*(1415#1000) - (1414#1000)*(1414#1000) < (1#100).
  Proof. repeat split; vm_compute; reflexivity. Qed.

  Print Assumptions sqrt2_squeezed_tightly.

  (* THE FRAMEWORK-NATIVE READING, made precise: a self-map that CONTRACTS
     (its iterates form a convergent readout sequence) can still have NO
     rational fixed point -- the Newton map for sqrt 2, f(x) = (x + 2/x)/2,
     has f(q) == q IFF q^2 == 2, which sqrt2_is_not_a_readout forbids. So
     the iterates are a Cauchy readout sequence whose limit is a NON-readout:
     this is EXACTLY the situation the contraction framework
     (InfoContractionConvergence) needs a RATIONAL fixed point for, and it is
     EXACTLY why the irrational-Fiedler graphs fall outside it. Irrational =
     a convergent readout sequence with no readout limit. *)
  Definition newton2 (x : Q) : Q := (x + (2#1)/x) / (2#1).

  Theorem newton2_fixed_point_iff_sqrt2 : forall q,
    ~ (q == 0) -> (newton2 q == q <-> q*q == 2).
  Proof.
    intros q Hq. unfold newton2. split.
    - intro Hfix.
      assert (HA : (q + (2#1)/q)/(2#1) * ((2#1)*q) == q * ((2#1)*q))
        by (rewrite Hfix; reflexivity).
      assert (HL : (q + (2#1)/q)/(2#1) * ((2#1)*q) == q*q + (2#1)) by (field; exact Hq).
      assert (HR : q * ((2#1)*q) == (2#1)*(q*q)) by ring.
      rewrite HL, HR in HA. nra.
    - intro Hsq.
      assert (H2q : (2#1)/q == q) by (rewrite <- Hsq; field; exact Hq).
      rewrite H2q. field.
  Qed.

  Print Assumptions newton2_fixed_point_iff_sqrt2.

  (* COROLLARY -- the wall, stated in framework terms: the Newton contraction
     toward sqrt 2 has NO rational fixed point. A contraction with no
     readout fixed point is precisely what contraction_reaches_tolerance
     cannot conclude convergence-to-a-point for -- the numerical face of the
     irrational-Fiedler spectral-gap wall. *)
  Corollary newton2_has_no_rational_fixed_point : forall q,
    ~ (q == 0) -> ~ (newton2 q == q).
  Proof.
    intros q Hq Hfix.
    apply (sqrt2_is_not_a_readout q).
    apply (newton2_fixed_point_iff_sqrt2 q Hq). exact Hfix.
  Qed.

  Print Assumptions newton2_has_no_rational_fixed_point.

End InfoIrrationalNonReadout.

(* PRIMARY TARGETS: InfoIrrationalNonReadout.sqrt2_is_not_a_readout (no          *)
(* rational q has q*q==2 -- "irrational = non-readout", the numerical face of      *)
(* readout-not-truth) and .newton2_has_no_rational_fixed_point (the Newton          *)
(* contraction toward sqrt 2 has NO rational fixed point -- the framework-native     *)
(* statement of the irrational-Fiedler spectral-gap wall: a contraction whose         *)
(* fixed point is a non-readout gives a Cauchy readout sequence with no readout        *)
(* limit, which is exactly what InfoContractionConvergence's convergence theorem       *)
(* cannot conclude a limit-point for). Backed by no_int_sqrt2 (infinite               *)
(* even-descent from scratch) and sqrt2_squeezed_tightly (rational readouts             *)
(* approach the non-readout truth to any tolerance yet never attain it). As            *)
(* documented above in SCOPE: sqrt 2 is the canonical machine-checked exemplar,          *)
(* not a general theory of reals (that is the avoided +reals machinery). Does not       *)
(* modify any repo file; says nothing about real particle mass ratios. *)
