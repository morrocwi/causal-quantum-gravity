(* CI-ATTEMPTS: +reals *)
(* ===================================================================== *)
(*  RDL_ContinuumLimit_nD.v  —  the MULTI-AXIS second-derivative readout.  *)
(*                                                                        *)
(*  HONEST AXIOM STATUS: over Coq's classical reals (NOT axiom-free),      *)
(*  exactly like RDL_ContinuumLimit.v whose 1-D core is reproduced         *)
(*  verbatim below so this file coqc-checks standalone; the Print          *)
(*  Assumptions at the bottom discloses the reals axioms used.  (A         *)
(*  Q-pure Qabs variant of the same epsilon-delta contents is portable     *)
(*  future work; alignment with the kernel file comes first.)              *)
(*                                                                        *)
(*  CONTENT.  The 1-D theorem says: a Peano second-order expansion at a    *)
(*  point makes the symmetric second-difference quotient converge to       *)
(*  twice the quadratic coefficient.  This file adds the LIMIT CALCULUS    *)
(*  (tends0_ext / tends0_plus / tends0_scale) and closes the multi-axis    *)
(*  step of the readout ladder in ONE theorem:                             *)
(*                                                                        *)
(*    weighted_two_axis_readout:                                          *)
(*      [ w1*D2sym(F1,x1,h) + w2*D2sym(F2,x2,h) ] / h^2                   *)
(*          --->  w1*(2*a2_1) + w2*(2*a2_2)                                *)
(*                                                                        *)
(*  whose instances are, by choice of weights alone:                       *)
(*    laplacian_2d_readout   (w =  1, 1) : the flat 2-D Laplacian          *)
(*    box_2d_readout         (w = -1, 1) : the d'Alembert operator —       *)
(*                           reproducing the kernel's lorentz_box shape    *)
(*                           as an instance                                *)
(*    (any constant w)                   : constant-diagonal-metric        *)
(*                           operators — the flat slice of rung 3          *)
(*    laplacian_3d_readout   : a third axis by the same additivity —       *)
(*                           the n-axis case iterates identically.         *)
(*                                                                        *)
(*  LADDER STATUS after this file: rung 1 (RDL_ProductSpectrum.v, Q,       *)
(*  axiom-free) supplies the discrete n-D spectral structure from the      *)
(*  1-D factors; this rung supplies the per-axis readout and its           *)
(*  weighted composition; together the FLAT n-D readout row of the         *)
(*  crosswalk closes at this file's tier.  NOT claimed: variable           *)
(*  coefficients a(x) (rung 3 proper), off-diagonal stencils (rung 4,      *)
(*  dominance-conditional), and any general-metric convergence (open       *)
(*  remainder, imported literature at its own tier).                       *)
(*  coqc 8.18.0.                                                           *)
(* ===================================================================== *)

Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Open Scope R_scope.

(* ---- 1-D core, reproduced verbatim from RDL_ContinuumLimit.v ---- *)

Definition tends0 (g : R -> R) (L : R) : Prop :=
  forall eps, eps > 0 -> exists del, del > 0 /\
    forall h, h <> 0 -> Rabs h < del -> Rabs (g h - L) < eps.

Definition D2sym (f:R->R) (x h:R) : R := f (x + h) - 2 * f x + f (x - h).

Lemma sq_neq0 : forall h, h <> 0 -> h * h <> 0.
Proof. intros h Hh Hc. destruct (Rmult_integral _ _ Hc); contradiction. Qed.

Lemma D2sym_expand :
  forall (f : R -> R) (x a1 a2 : R) (r : R -> R),
  (forall h, f (x + h) = f x + a1 * h + a2 * (h * h) + r h) ->
  forall h, D2sym f x h = 2 * a2 * (h * h) + (r h + r (- h)).
Proof.
  intros f x a1 a2 r Hexp h. unfold D2sym. rewrite (Hexp h).
  assert (Hm : f (x - h) = f x + a1 * (- h) + a2 * ((- h) * (- h)) + r (- h)).
  { replace (x - h) with (x + - h) by ring. apply (Hexp (- h)). }
  rewrite Hm. ring.
Qed.

Theorem symmetric_second_difference_limit :
  forall (f : R -> R) (x a1 a2 : R) (r : R -> R),
  (forall h, f (x + h) = f x + a1 * h + a2 * (h * h) + r h) ->
  tends0 (fun h => r h / (h * h)) 0 ->
  tends0 (fun h => D2sym f x h / (h * h)) (2 * a2).
Proof.
  intros f x a1 a2 r Hexp Hrem eps Heps.
  assert (Hhalf : eps / 2 > 0) by lra.
  destruct (Hrem (eps / 2) Hhalf) as [del [Hdel Hb]].
  exists del. split; [exact Hdel|].
  intros h Hh Hhd.
  assert (Hq : D2sym f x h / (h * h) - 2 * a2
               = r h / (h * h) + r (- h) / (h * h)).
  { rewrite (D2sym_expand f x a1 a2 r Hexp h). field. exact Hh. }
  cbn beta. rewrite Hq.
  assert (Hh'  : - h <> 0) by (intro Hc; apply Hh; lra).
  assert (Hhd' : Rabs (- h) < del) by (rewrite Rabs_Ropp; exact Hhd).
  pose proof (Hb h Hh Hhd) as B1.
  pose proof (Hb (- h) Hh' Hhd') as B2.
  replace ((- h) * (- h)) with (h * h) in B2 by ring.
  replace (r h / (h * h) - 0) with (r h / (h * h)) in B1 by ring.
  replace (r (- h) / (h * h) - 0) with (r (- h) / (h * h)) in B2 by ring.
  apply Rle_lt_trans with (Rabs (r h / (h * h)) + Rabs (r (- h) / (h * h))).
  - apply Rabs_triang.
  - lra.
Qed.

(* ---- THE LIMIT CALCULUS ---- *)

(* limits only see the punctured values *)
Lemma tends0_ext : forall (g g' : R -> R) (L : R),
  (forall h, h <> 0 -> g h = g' h) ->
  tends0 g L -> tends0 g' L.
Proof.
  intros g g' L Hgg Hg eps Heps.
  destruct (Hg eps Heps) as [del [Hdel Hb]].
  exists del. split; [exact Hdel|].
  intros h Hh Hhd.
  rewrite <- (Hgg h Hh). apply Hb; assumption.
Qed.

(* limits add *)
Lemma tends0_plus : forall (g g' : R -> R) (L L' : R),
  tends0 g L -> tends0 g' L' ->
  tends0 (fun h => g h + g' h) (L + L').
Proof.
  intros g g' L L' Hg Hg' eps Heps.
  assert (Hhalf : eps / 2 > 0) by lra.
  destruct (Hg  (eps / 2) Hhalf) as [d1 [Hd1 Hb1]].
  destruct (Hg' (eps / 2) Hhalf) as [d2 [Hd2 Hb2]].
  exists (Rmin d1 d2). split.
  - apply Rmin_glb_lt; assumption.
  - intros h Hh Hhd.
    assert (Hm1 : Rmin d1 d2 <= d1) by apply Rmin_l.
    assert (Hm2 : Rmin d1 d2 <= d2) by apply Rmin_r.
    assert (B1 := Hb1 h Hh (Rlt_le_trans _ _ _ Hhd Hm1)).
    assert (B2 := Hb2 h Hh (Rlt_le_trans _ _ _ Hhd Hm2)).
    replace (g h + g' h - (L + L')) with ((g h - L) + (g' h - L')) by ring.
    apply Rle_lt_trans with (Rabs (g h - L) + Rabs (g' h - L')).
    + apply Rabs_triang.
    + lra.
Qed.

(* limits scale *)
Lemma tends0_scale : forall (c : R) (g : R -> R) (L : R),
  tends0 g L -> tends0 (fun h => c * g h) (c * L).
Proof.
  intros c g L Hg.
  destruct (Req_dec c 0) as [-> | Hc].
  - intros eps Heps. exists 1. split; [lra|].
    intros h _ _.
    replace (0 * g h - 0 * L) with 0 by ring.
    rewrite Rabs_R0. exact Heps.
  - intros eps Heps.
    assert (Hac : 0 < Rabs c) by (apply Rabs_pos_lt; exact Hc).
    assert (Heac : eps / Rabs c > 0)
      by (apply Rdiv_lt_0_compat; assumption).
    destruct (Hg (eps / Rabs c) Heac) as [del [Hdel Hb]].
    exists del. split; [exact Hdel|].
    intros h Hh Hhd.
    replace (c * g h - c * L) with (c * (g h - L)) by ring.
    rewrite Rabs_mult.
    assert (B := Hb h Hh Hhd).
    assert (Hm : Rabs c * Rabs (g h - L) < Rabs c * (eps / Rabs c))
      by (apply Rmult_lt_compat_l; assumption).
    assert (Heq : Rabs c * (eps / Rabs c) = eps)
      by (field; apply Rgt_not_eq; exact Hac).
    lra.
Qed.

(* ---- THE MULTI-AXIS READOUT ---- *)

(* one theorem; the flat Laplacian, the box operator, and every         *)
(* constant-diagonal-metric operator are instances by weight choice     *)
Theorem weighted_two_axis_readout :
  forall (F1 F2 : R -> R) (x1 x2 a11 a21 a12 a22 : R) (r1 r2 : R -> R)
         (w1 w2 : R),
  (forall h, F1 (x1 + h) = F1 x1 + a11 * h + a21 * (h * h) + r1 h) ->
  tends0 (fun h => r1 h / (h * h)) 0 ->
  (forall h, F2 (x2 + h) = F2 x2 + a12 * h + a22 * (h * h) + r2 h) ->
  tends0 (fun h => r2 h / (h * h)) 0 ->
  tends0 (fun h => (w1 * D2sym F1 x1 h + w2 * D2sym F2 x2 h) / (h * h))
         (w1 * (2 * a21) + w2 * (2 * a22)).
Proof.
  intros F1 F2 x1 x2 a11 a21 a12 a22 r1 r2 w1 w2 He1 Hr1 He2 Hr2.
  assert (H1 := symmetric_second_difference_limit F1 x1 a11 a21 r1 He1 Hr1).
  assert (H2 := symmetric_second_difference_limit F2 x2 a12 a22 r2 He2 Hr2).
  assert (S1 := tends0_scale w1 _ _ H1).
  assert (S2 := tends0_scale w2 _ _ H2).
  assert (P := tends0_plus _ _ _ _ S1 S2).
  apply (tends0_ext
    (fun h => w1 * (D2sym F1 x1 h / (h * h))
            + w2 * (D2sym F2 x2 h / (h * h)))
    (fun h => (w1 * D2sym F1 x1 h + w2 * D2sym F2 x2 h) / (h * h)));
    [| exact P].
  intros h Hh. field. apply Hh.
Qed.

(* the flat 2-D Laplacian *)
Corollary laplacian_2d_readout :
  forall (F1 F2 : R -> R) (x1 x2 a11 a21 a12 a22 : R) (r1 r2 : R -> R),
  (forall h, F1 (x1 + h) = F1 x1 + a11 * h + a21 * (h * h) + r1 h) ->
  tends0 (fun h => r1 h / (h * h)) 0 ->
  (forall h, F2 (x2 + h) = F2 x2 + a12 * h + a22 * (h * h) + r2 h) ->
  tends0 (fun h => r2 h / (h * h)) 0 ->
  tends0 (fun h => (D2sym F1 x1 h + D2sym F2 x2 h) / (h * h))
         (2 * a21 + 2 * a22).
Proof.
  intros F1 F2 x1 x2 a11 a21 a12 a22 r1 r2 He1 Hr1 He2 Hr2.
  assert (HW := weighted_two_axis_readout F1 F2 x1 x2 a11 a21 a12 a22
                  r1 r2 1 1 He1 Hr1 He2 Hr2).
  apply (tends0_ext
    (fun h => (1 * D2sym F1 x1 h + 1 * D2sym F2 x2 h) / (h * h)));
    [intros h _; f_equal; ring |].
  replace (2 * a21 + 2 * a22) with (1 * (2 * a21) + 1 * (2 * a22)) by ring.
  exact HW.
Qed.

(* the box operator: weights (-1, 1) — the kernel's lorentz_box shape   *)
(* recovered as an instance                                             *)
Corollary box_2d_readout :
  forall (Ft Fx : R -> R) (t x a1t a2t a1x a2x : R) (rt rx : R -> R),
  (forall h, Ft (t + h) = Ft t + a1t * h + a2t * (h * h) + rt h) ->
  tends0 (fun h => rt h / (h * h)) 0 ->
  (forall h, Fx (x + h) = Fx x + a1x * h + a2x * (h * h) + rx h) ->
  tends0 (fun h => rx h / (h * h)) 0 ->
  tends0 (fun h => (- D2sym Ft t h + D2sym Fx x h) / (h * h))
         (- (2 * a2t) + 2 * a2x).
Proof.
  intros Ft Fx t x a1t a2t a1x a2x rt rx He1 Hr1 He2 Hr2.
  assert (HW := weighted_two_axis_readout Ft Fx t x a1t a2t a1x a2x
                  rt rx (- 1) 1 He1 Hr1 He2 Hr2).
  apply (tends0_ext
    (fun h => (- 1 * D2sym Ft t h + 1 * D2sym Fx x h) / (h * h)));
    [intros h _; f_equal; ring |].
  replace (- (2 * a2t) + 2 * a2x)
    with (- 1 * (2 * a2t) + 1 * (2 * a2x)) by ring.
  exact HW.
Qed.

(* a third axis by the same additivity; n axes iterate identically *)
Corollary laplacian_3d_readout :
  forall (F1 F2 F3 : R -> R) (x1 x2 x3 a11 a21 a12 a22 a13 a23 : R)
         (r1 r2 r3 : R -> R),
  (forall h, F1 (x1 + h) = F1 x1 + a11 * h + a21 * (h * h) + r1 h) ->
  tends0 (fun h => r1 h / (h * h)) 0 ->
  (forall h, F2 (x2 + h) = F2 x2 + a12 * h + a22 * (h * h) + r2 h) ->
  tends0 (fun h => r2 h / (h * h)) 0 ->
  (forall h, F3 (x3 + h) = F3 x3 + a13 * h + a23 * (h * h) + r3 h) ->
  tends0 (fun h => r3 h / (h * h)) 0 ->
  tends0 (fun h => (D2sym F1 x1 h + D2sym F2 x2 h + D2sym F3 x3 h)
                   / (h * h))
         (2 * a21 + 2 * a22 + 2 * a23).
Proof.
  intros F1 F2 F3 x1 x2 x3 a11 a21 a12 a22 a13 a23 r1 r2 r3
         He1 Hr1 He2 Hr2 He3 Hr3.
  assert (H12 := laplacian_2d_readout F1 F2 x1 x2 a11 a21 a12 a22
                   r1 r2 He1 Hr1 He2 Hr2).
  assert (H3 := symmetric_second_difference_limit F3 x3 a13 a23 r3 He3 Hr3).
  assert (P := tends0_plus _ _ _ _ H12 H3).
  apply (tends0_ext
    (fun h => (D2sym F1 x1 h + D2sym F2 x2 h) / (h * h)
            + D2sym F3 x3 h / (h * h)));
    [| exact P].
  intros h Hh. field. apply Hh.
Qed.

(* --- HONEST DISCLOSURE: which reals axioms do these rest on? --- *)
Print Assumptions weighted_two_axis_readout.
Print Assumptions laplacian_2d_readout.
Print Assumptions box_2d_readout.
Print Assumptions laplacian_3d_readout.
