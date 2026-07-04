(* CI-ATTEMPTS: +reals *)
(* ===================================================================== *)
(*  RDL_WeightedReadout.v  —  the VARIABLE-COEFFICIENT readout:            *)
(*  the flux-form weighted second difference converges to the             *)
(*  divergence-form operator (a u')' = a u'' + a' u'.                     *)
(*                                                                        *)
(*  HONEST AXIOM STATUS: over Coq's classical reals, same tier as          *)
(*  RDL_ContinuumLimit.v / RDL_ContinuumLimit_nD.v (the disclosure at      *)
(*  the bottom is the authority; the nD file landed on                     *)
(*  sig_forall_dec + funext only, and this file targets the same           *)
(*  profile).                                                              *)
(*                                                                        *)
(*  CONTENT.  Both the coefficient a and the field f are given             *)
(*  second-order Peano expansions at x:                                    *)
(*     a(x+k) = a0 + b1 k + b2 k^2 + s(k),   s(k)/k^2 -> 0                 *)
(*     f(x+k) = f(x) + a1 k + a2 k^2 + r(k), r(k)/k^2 -> 0                 *)
(*  The flux-form stencil                                                  *)
(*     D2w(h) = a(x+h/2) (f(x+h)-f(x)) - a(x-h/2) (f(x)-f(x-h))            *)
(*  then satisfies EXACTLY (a pure ring identity after substitution)       *)
(*     D2w(h) = (2 a0 a2 + b1 a1) h^2 + R2(h)                              *)
(*  with an explicit remainder R2, and R2(h)/h^2 -> 0 by an extended       *)
(*  limit calculus.  Hence                                                 *)
(*     D2w(h)/h^2  --->  2 a0 a2 + b1 a1  =  a(x) f''(x) + a'(x) f'(x),    *)
(*  the divergence-form (a u')' operator: the product rule is a READOUT    *)
(*  of the flux stencil, not an input.                                     *)
(*                                                                        *)
(*  LADDER STATUS: with RDL_ProductSpectrum.v (rung 1, Q, axiom-free)      *)
(*  and RDL_ContinuumLimit_nD.v (rung 2, weighted multi-axis), this        *)
(*  closes the variable-coefficient PER-AXIS readout — the diagonal-       *)
(*  metric rung.  NOT claimed: off-diagonal stencils (dominance-           *)
(*  conditional, rung 4) and general-metric spectral convergence           *)
(*  (imported literature at its own tier; the open remainder).             *)
(*                                                                        *)
(*  The two load-bearing algebraic identities (master and quotient) were   *)
(*  pre-verified symbolically before authoring.  coqc 8.18.0.              *)
(* ===================================================================== *)

Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Open Scope R_scope.

(* ---- shared 1-D notions (as in RDL_ContinuumLimit.v) ---- *)

Definition tends0 (g : R -> R) (L : R) : Prop :=
  forall eps, eps > 0 -> exists del, del > 0 /\
    forall h, h <> 0 -> Rabs h < del -> Rabs (g h - L) < eps.

Lemma sq_neq0 : forall h, h <> 0 -> h * h <> 0.
Proof. intros h Hh Hc. destruct (Rmult_integral _ _ Hc); contradiction. Qed.

(* ---- THE EXTENDED LIMIT CALCULUS ---- *)

Lemma tends0_ext : forall (g g' : R -> R) (L : R),
  (forall h, h <> 0 -> g h = g' h) ->
  tends0 g L -> tends0 g' L.
Proof.
  intros g g' L Hgg Hg eps Heps.
  destruct (Hg eps Heps) as [del [Hdel Hb]].
  exists del. split; [exact Hdel|].
  intros h Hh Hhd. rewrite <- (Hgg h Hh). apply Hb; assumption.
Qed.

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

Lemma tends0_id : tends0 (fun h => h) 0.
Proof.
  intros eps Heps. exists eps. split; [exact Heps|].
  intros h _ Hhd. replace (h - 0) with h by ring. exact Hhd.
Qed.

(* the product of two vanishing limits vanishes *)
Lemma tends0_mult0 : forall (g g' : R -> R),
  tends0 g 0 -> tends0 g' 0 ->
  tends0 (fun h => g h * g' h) 0.
Proof.
  intros g g' Hg Hg' eps Heps.
  destruct (Hg eps Heps) as [d1 [Hd1 Hb1]].
  destruct (Hg' 1 Rlt_0_1) as [d2 [Hd2 Hb2]].
  exists (Rmin d1 d2). split.
  - apply Rmin_glb_lt; assumption.
  - intros h Hh Hhd.
    assert (Hm1 : Rmin d1 d2 <= d1) by apply Rmin_l.
    assert (Hm2 : Rmin d1 d2 <= d2) by apply Rmin_r.
    assert (B1 := Hb1 h Hh (Rlt_le_trans _ _ _ Hhd Hm1)).
    assert (B2 := Hb2 h Hh (Rlt_le_trans _ _ _ Hhd Hm2)).
    replace (g h - 0) with (g h) in B1 by ring.
    replace (g' h - 0) with (g' h) in B2 by ring.
    replace (g h * g' h - 0) with (g h * g' h) by ring.
    rewrite Rabs_mult.
    assert (Hp1 := Rabs_pos (g h)).
    assert (Hp2 := Rabs_pos (g' h)).
    assert (Hle : Rabs (g h) * Rabs (g' h) <= Rabs (g h) * 1)
      by (apply Rmult_le_compat_l; lra).
    lra.
Qed.

(* reparametrizing the approach h |-> c*h (c <> 0) preserves the limit *)
Lemma tends0_comp_scale : forall (c : R) (g : R -> R) (L : R),
  c <> 0 ->
  tends0 g L -> tends0 (fun h => g (c * h)) L.
Proof.
  intros c g L Hc Hg eps Heps.
  assert (Hac : 0 < Rabs c) by (apply Rabs_pos_lt; exact Hc).
  destruct (Hg eps Heps) as [del [Hdel Hb]].
  assert (Hdc : del / Rabs c > 0)
    by (apply Rdiv_lt_0_compat; assumption).
  exists (del / Rabs c). split; [exact Hdc|].
  intros h Hh Hhd.
  assert (Hch : c * h <> 0)
    by (intro Hc0; destruct (Rmult_integral _ _ Hc0); contradiction).
  assert (Habs : Rabs (c * h) < del).
  { rewrite Rabs_mult.
    assert (Hm : Rabs c * Rabs h < Rabs c * (del / Rabs c))
      by (apply Rmult_lt_compat_l; assumption).
    assert (Heq : Rabs c * (del / Rabs c) = del)
      by (field; apply Rgt_not_eq; exact Hac).
    lra. }
  exact (Hb (c * h) Hch Habs).
Qed.

(* an o(h^2) remainder itself vanishes *)
Lemma tends0_val : forall (g : R -> R),
  tends0 (fun h => g h / (h * h)) 0 ->
  tends0 g 0.
Proof.
  intros g Hg eps Heps.
  destruct (Hg eps Heps) as [del [Hdel Hb]].
  exists (Rmin del 1). split.
  - apply Rmin_glb_lt; lra.
  - intros h Hh Hhd.
    assert (Hm1 : Rmin del 1 <= del) by apply Rmin_l.
    assert (Hm2 : Rmin del 1 <= 1) by apply Rmin_r.
    assert (B := Hb h Hh (Rlt_le_trans _ _ _ Hhd Hm1)).
    replace (g h / (h * h) - 0) with (g h / (h * h)) in B by ring.
    assert (Hgh : g h = g h / (h * h) * (h * h))
      by (field; exact Hh).
    replace (g h - 0) with (g h) by ring.
    rewrite Hgh. rewrite Rabs_mult.
    assert (Hh1 : Rabs h < 1) by lra.
    assert (Hp := Rabs_pos h).
    assert (Hsq : Rabs (h * h) < 1).
    { rewrite Rabs_mult.
      replace 1 with (1 * 1) by ring.
      apply Rmult_le_0_lt_compat; lra. }
    assert (Hq := Rabs_pos (g h / (h * h))).
    assert (Hle : Rabs (g h / (h * h)) * Rabs (h * h)
                  <= Rabs (g h / (h * h)) * 1)
      by (apply Rmult_le_compat_l; lra).
    lra.
Qed.

(* an o(h^2) remainder is also o(h) *)
Lemma tends0_small1 : forall (g : R -> R),
  tends0 (fun h => g h / (h * h)) 0 ->
  tends0 (fun h => g h / h) 0.
Proof.
  intros g Hg eps Heps.
  destruct (Hg eps Heps) as [del [Hdel Hb]].
  exists (Rmin del 1). split.
  - apply Rmin_glb_lt; lra.
  - intros h Hh Hhd.
    assert (Hm1 : Rmin del 1 <= del) by apply Rmin_l.
    assert (Hm2 : Rmin del 1 <= 1) by apply Rmin_r.
    assert (B := Hb h Hh (Rlt_le_trans _ _ _ Hhd Hm1)).
    replace (g h / (h * h) - 0) with (g h / (h * h)) in B by ring.
    assert (Hgh : g h / h = g h / (h * h) * h)
      by (field; exact Hh).
    replace (g h / h - 0) with (g h / h) by ring.
    rewrite Hgh. rewrite Rabs_mult.
    assert (Hh1 : Rabs h < 1) by lra.
    assert (Hq := Rabs_pos (g h / (h * h))).
    assert (Hle : Rabs (g h / (h * h)) * Rabs h
                  <= Rabs (g h / (h * h)) * 1)
      by (apply Rmult_le_compat_l; lra).
    lra.
Qed.

(* readout through the squared-step quotient, given an exact remainder *)
Lemma quotient_readout : forall (D R2 : R -> R) (L : R),
  (forall h, h <> 0 -> D h = L * (h * h) + R2 h) ->
  tends0 (fun h => R2 h / (h * h)) 0 ->
  tends0 (fun h => D h / (h * h)) L.
Proof.
  intros D R2 L HD HR eps Heps.
  destruct (HR eps Heps) as [del [Hdel Hb]].
  exists del. split; [exact Hdel|].
  intros h Hh Hhd.
  assert (B := Hb h Hh Hhd).
  replace (R2 h / (h * h) - 0) with (R2 h / (h * h)) in B by ring.
  assert (Hq : D h / (h * h) - L = R2 h / (h * h)).
  { rewrite (HD h Hh). field. exact Hh. }
  rewrite Hq. exact B.
Qed.

(* ---- THE WEIGHTED (FLUX-FORM) SECOND DIFFERENCE ---- *)

Definition D2w (a f : R -> R) (x : R) (h : R) : R :=
  a (x + h / 2) * (f (x + h) - f x) - a (x - h / 2) * (f x - f (x - h)).

(* the explicit remainder (pre-verified symbolically) *)
Definition R2 (a0 b1 b2 a1 a2 : R) (s r : R -> R) (h : R) : R :=
  a0 * (r h + r (- h))
  + (b1 * (h / 2)) * (r h - r (- h))
  + (b2 * ((h / 2) * (h / 2))) * (2 * a2 * (h * h) + (r h + r (- h)))
  + s (h / 2) * (a1 * h + a2 * (h * h) + r h)
  - s (- (h / 2)) * (a1 * h - a2 * (h * h) - r (- h)).

(* THE MASTER IDENTITY: exact, for every h *)
Lemma D2w_expand :
  forall (a f : R -> R) (x a0 b1 b2 a1 a2 : R) (s r : R -> R),
  (forall k, a (x + k) = a0 + b1 * k + b2 * (k * k) + s k) ->
  (forall k, f (x + k) = f x + a1 * k + a2 * (k * k) + r k) ->
  forall h,
  D2w a f x h = (2 * a0 * a2 + b1 * a1) * (h * h) + R2 a0 b1 b2 a1 a2 s r h.
Proof.
  intros a f x a0 b1 b2 a1 a2 s r Ha Hf h. unfold D2w, R2.
  rewrite (Ha (h / 2)).
  replace (x - h / 2) with (x + - (h / 2)) by ring.
  rewrite (Ha (- (h / 2))).
  rewrite (Hf h).
  replace (x - h) with (x + - h) by ring.
  rewrite (Hf (- h)).
  field.
Qed.

(* the remainder is o(h^2): assembled from the extended calculus *)
Lemma R2_small :
  forall (a0 b1 b2 a1 a2 : R) (s r : R -> R),
  tends0 (fun k => s k / (k * k)) 0 ->
  tends0 (fun k => r k / (k * k)) 0 ->
  tends0 (fun h => R2 a0 b1 b2 a1 a2 s r h / (h * h)) 0.
Proof.
  intros a0 b1 b2 a1 a2 s r Hs Hr.
    (* component limits *)
    assert (Hrq  : tends0 (fun h => r h / (h * h)) 0) by exact Hr.
    assert (Hrmq : tends0 (fun h => r (- h) / (h * h)) 0).
    { apply (tends0_ext (fun h => r (- (1) * h) / ((- (1) * h) * (- (1) * h)))).
      - intros h _.
        replace (- (1) * h) with (- h) by ring.
        replace (- h * - h) with (h * h) by ring.
        reflexivity.
      - apply (tends0_comp_scale (- (1)) (fun k => r k / (k * k)) 0);
          [lra | exact Hr]. }
    assert (Hrv  : tends0 (fun h => r h) 0) by (apply tends0_val; exact Hr).
    assert (Hrmv : tends0 (fun h => r (- h)) 0).
    { apply (tends0_ext (fun h => r (- (1) * h))).
      - intros h _. replace (- (1) * h) with (- h) by ring. reflexivity.
      - apply (tends0_comp_scale (- (1)) (fun k => r k) 0);
          [lra | exact Hrv]. }
    assert (Hr1  : tends0 (fun h => r h / h) 0)
      by (apply tends0_small1; exact Hr).
    assert (Hrm1 : tends0 (fun h => r (- h) / h) 0).
    { assert (Hpre : tends0 (fun h => r (- (1) * h) / (- (1) * h)) 0)
        by (apply (tends0_comp_scale (- (1)) (fun k => r k / k) 0);
            [lra | exact Hr1]).
      assert (Hneg := tends0_scale (- (1)) _ _ Hpre).
      replace (- (1) * 0) with 0 in Hneg by ring.
      apply (tends0_ext
        (fun h => - (1) * (r (- (1) * h) / (- (1) * h)))); [| exact Hneg].
      intros h Hh.
      replace (- (1) * h) with (- h) by ring.
      field. exact Hh. }
    assert (Hsv : tends0 (fun h => s (h / 2)) 0).
    { apply (tends0_ext (fun h => s (/ 2 * h))).
      - intros h _. replace (/ 2 * h) with (h / 2) by field. reflexivity.
      - apply (tends0_comp_scale (/ 2) (fun k => s k) 0); [lra |].
        apply tends0_val; exact Hs. }
    assert (Hsmv : tends0 (fun h => s (- (h / 2))) 0).
    { apply (tends0_ext (fun h => s (- / 2 * h))).
      - intros h _. replace (- / 2 * h) with (- (h / 2)) by field. reflexivity.
      - apply (tends0_comp_scale (- / 2) (fun k => s k) 0); [lra |].
        apply tends0_val; exact Hs. }
    assert (Hs1 : tends0 (fun h => s (h / 2) / h) 0).
    { assert (Hpre : tends0 (fun h => s (/ 2 * h) / (/ 2 * h)) 0)
        by (apply (tends0_comp_scale (/ 2) (fun k => s k / k) 0);
            [lra | apply tends0_small1; exact Hs]).
      assert (Hhalf := tends0_scale (/ 2) _ _ Hpre).
      replace (/ 2 * 0) with 0 in Hhalf by ring.
      apply (tends0_ext
        (fun h => / 2 * (s (/ 2 * h) / (/ 2 * h)))); [| exact Hhalf].
      intros h Hh.
      replace (/ 2 * h) with (h / 2) by field.
      field. exact Hh. }
    assert (Hsm1 : tends0 (fun h => s (- (h / 2)) / h) 0).
    { assert (Hpre : tends0 (fun h => s (- / 2 * h) / (- / 2 * h)) 0)
        by (apply (tends0_comp_scale (- / 2) (fun k => s k / k) 0);
            [lra | apply tends0_small1; exact Hs]).
      assert (Hhalf := tends0_scale (- / 2) _ _ Hpre).
      replace (- / 2 * 0) with 0 in Hhalf by ring.
      apply (tends0_ext
        (fun h => - / 2 * (s (- / 2 * h) / (- / 2 * h)))); [| exact Hhalf].
      intros h Hh.
      replace (- / 2 * h) with (- (h / 2)) by field.
      field. exact Hh. }
    assert (Hhh : tends0 (fun h => h * h) 0)
      by (apply tends0_mult0; apply tends0_id).
    (* the five groups *)
    assert (G1 : tends0 (fun h => a0 * (r h / (h * h)) + a0 * (r (- h) / (h * h))) 0).
    { replace 0 with (a0 * 0 + a0 * 0) at 1 by ring.
      apply tends0_plus; apply tends0_scale; assumption. }
    assert (G2 : tends0 (fun h => b1 / 2 * (r h / h) + - (b1 / 2) * (r (- h) / h)) 0).
    { replace 0 with (b1 / 2 * 0 + - (b1 / 2) * 0) at 1 by ring.
      apply tends0_plus; apply tends0_scale; assumption. }
    assert (G3 : tends0 (fun h => b2 / 4 * (2 * a2 * (h * h))
                                + (b2 / 4 * (r h) + b2 / 4 * (r (- h)))) 0).
    { replace 0 with (b2 / 4 * (2 * a2 * 0) + (b2 / 4 * 0 + b2 / 4 * 0)) at 1 by ring.
      apply tends0_plus.
      - apply tends0_scale. apply tends0_scale. exact Hhh.
      - apply tends0_plus; apply tends0_scale; assumption. }
    assert (G4 : tends0 (fun h => a1 * (s (h / 2) / h)
                                + (a2 * (s (h / 2))
                                   + s (h / 2) * (r h / (h * h)))) 0).
    { replace 0 with (a1 * 0 + (a2 * 0 + 0)) at 1 by ring.
      apply tends0_plus; [apply tends0_scale; exact Hs1 |].
      apply tends0_plus; [apply tends0_scale; exact Hsv |].
      apply tends0_mult0; assumption. }
    assert (G5 : tends0 (fun h => - a1 * (s (- (h / 2)) / h)
                                + (a2 * (s (- (h / 2)))
                                   + s (- (h / 2)) * (r (- h) / (h * h)))) 0).
    { replace 0 with (- a1 * 0 + (a2 * 0 + 0)) at 1 by ring.
      apply tends0_plus; [apply tends0_scale; exact Hsm1 |].
      apply tends0_plus; [apply tends0_scale; exact Hsmv |].
      apply tends0_mult0; assumption. }
    (* assemble *)
    assert (HG := tends0_plus _ _ _ _ G1
                    (tends0_plus _ _ _ _ G2
                       (tends0_plus _ _ _ _ G3
                          (tends0_plus _ _ _ _ G4 G5)))).
    replace (0 + (0 + (0 + (0 + 0)))) with 0 in HG by ring.
    eapply tends0_ext; [ | exact HG ].
    intros h Hh. cbn beta. unfold R2. field. exact Hh.
  Qed.

(* THE VARIABLE-COEFFICIENT READOUT *)
Theorem weighted_second_difference_limit :
  forall (a f : R -> R) (x a0 b1 b2 a1 a2 : R) (s r : R -> R),
  (forall k, a (x + k) = a0 + b1 * k + b2 * (k * k) + s k) ->
  tends0 (fun k => s k / (k * k)) 0 ->
  (forall k, f (x + k) = f x + a1 * k + a2 * (k * k) + r k) ->
  tends0 (fun k => r k / (k * k)) 0 ->
  tends0 (fun h => D2w a f x h / (h * h)) (2 * a0 * a2 + b1 * a1).
Proof.
  intros a f x a0 b1 b2 a1 a2 s r Ha Hs Hf Hr.
  apply (quotient_readout (D2w a f x) (R2 a0 b1 b2 a1 a2 s r)).
  - intros h _. apply (D2w_expand a f x a0 b1 b2 a1 a2 s r Ha Hf).
  - apply (R2_small a0 b1 b2 a1 a2 s r Hs Hr).
Qed.

(* constant coefficient recovers c times the unweighted limit — the     *)
(* consistency instance joining this file to RDL_ContinuumLimit_nD.v    *)
Corollary constant_coefficient_instance :
  forall (f : R -> R) (c x a1 a2 : R) (r : R -> R),
  (forall k, f (x + k) = f x + a1 * k + a2 * (k * k) + r k) ->
  tends0 (fun k => r k / (k * k)) 0 ->
  tends0 (fun h => D2w (fun _ => c) f x h / (h * h)) (c * (2 * a2)).
Proof.
  intros f c x a1 a2 r Hf Hr.
  replace (c * (2 * a2)) with (2 * c * a2 + 0 * a1) by ring.
  apply (weighted_second_difference_limit (fun _ => c) f x c 0 0 a1 a2
           (fun _ => 0) r).
  - intro k. ring.
  - intros eps Heps. exists 1. split; [lra|]. intros h _ _.
    replace (0 / (h * h) - 0) with 0
      by (unfold Rdiv; rewrite Rmult_0_l; ring).
    rewrite Rabs_R0. exact Heps.
  - exact Hf.
  - exact Hr.
Qed.

(* --- HONEST DISCLOSURE: which reals axioms do these rest on? --- *)
Print Assumptions weighted_second_difference_limit.
Print Assumptions constant_coefficient_instance.
