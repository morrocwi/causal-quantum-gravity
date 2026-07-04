(* ===================================================================== *)
(*  InfoLorentzContinuum.v                                                *)
(*                                                                         *)
(*  PURPOSE                                                                *)
(*  The discrete Lorentzian d'Alembertian on an information-readout        *)
(*  lattice (signed sum of a time second-difference and a space            *)
(*  second-difference) has a continuum limit: as the lattice spacing       *)
(*  h -> 0, the signed second-difference quotient tends to                 *)
(*    Box F = - d2F/dt2 + d2F/dx2.                                         *)
(*  The MINUS sign on the time term is exactly the causal signature        *)
(*  carried by the discrete order relation "<" in the parent InfoLorentz   *)
(*  development (URCF_RD_All.v, Module InfoLorentz); it is NOT re-derived  *)
(*  here because this file is a standalone extraction of the continuum     *)
(*  limit step only -- it does not reference Edge/info_form/InfoLorentz.   *)
(*                                                                         *)
(*  CLAIM TIER: +reals (Open/continuum tier in the readout-not-truth       *)
(*  stance). This file trades in the actual continuum (h -> 0, an          *)
(*  epsilon-delta limit over R) and therefore, unlike the axiom-free       *)
(*  discrete/Q-valued readout theorems elsewhere in this arc, it is NOT    *)
(*  "Closed" under `Print Assumptions`. It rests on Coq's standard Reals   *)
(*  axiomatization. Do not present this theorem's conclusion as a          *)
(*  discrete/finite-diagnostic readout: it is the continuum idealisation   *)
(*  that the discrete theorems are compared against, one tier up.         *)
(*                                                                         *)
(*  EXPECTED AXIOM DISCLOSURE (`Print Assumptions lorentz_box_continuum`): *)
(*    ClassicalDedekindReals.sig_forall_dec                                *)
(*    FunctionalExtensionality.functional_extensionality_dep               *)
(*  (the two axioms Coq's stdlib Reals library itself is built on --       *)
(*  "TIER 1" in the parent file's disclosure, i.e. the bare reals, with    *)
(*  NO additional classical excluded-middle axiom pulled in: this file     *)
(*  never invokes MVT/derivable_pt_lim, only the readout-native Peano-     *)
(*  expansion definition of "has a 2nd-order readout", so it stays one     *)
(*  rung below the parent file's classical TIER 2.)                       *)
(*                                                                         *)
(*  PROVENANCE                                                             *)
(*  Extracted verbatim (module body unmodified) from:                     *)
(*    research_universal_solver/formal/URCF_RD_All.v                      *)
(*      Module ContLimit             lines 6105-6182                      *)
(*      Module Capstone              lines 6600-6681 (TIER 1 slice only)  *)
(*      Module InfoLorentzContinuum  lines 7037-7078                      *)
(*  as read on 2026-06-27.                                                 *)
(*  This file inlines the minimal pieces of ContLimit/Capstone that        *)
(*  lorentz_box_continuum actually depends on (tends0, D2sym,              *)
(*  has_second_readout, continuum_gate_readout_native and their proof      *)
(*  lemmas) so it compiles standalone, with no Require of the giant        *)
(*  parent file and no dependency on InfoLorentz's Edge/info_form graph    *)
(*  machinery.                                                             *)
(* ===================================================================== *)

From Coq Require Import Reals.
From Coq Require Import Lra.

(* ===================================================================== *)
(*  Module ContLimit  (minimal slice: tends0, D2sym, and the symmetric    *)
(*  second-difference limit theorem that has_second_readout is built on)  *)
(* ===================================================================== *)
Module ContLimit.
  Import Reals.
  Import Lra.
  Local Open Scope R_scope.

  (* self-contained "g(h) -> L as h->0 through h<>0" (epsilon-delta) *)
  Definition tends0 (g : R -> R) (L : R) : Prop :=
    forall eps, eps > 0 -> exists del, del > 0 /\
      forall h, h <> 0 -> Rabs h < del -> Rabs (g h - L) < eps.

  Definition D2sym (f:R->R) (x h:R) : R := f (x + h) - 2 * f x + f (x - h).

  Lemma sq_neq0 : forall h, h <> 0 -> h * h <> 0.
  Proof. intros h Hh Hc. destruct (Rmult_integral _ _ Hc); contradiction. Qed.

  Section SSD.
    Variable f : R -> R.
    Variable x a1 a2 : R.
    Variable r : R -> R.
    Hypothesis Hexp : forall h, f (x + h) = f x + a1 * h + a2 * (h * h) + r h.
    Hypothesis Hrem : tends0 (fun h => r h / (h * h)) 0.

    (* symmetric difference cancels the odd term *)
    Lemma D2sym_expand :
      forall h, D2sym f x h = 2 * a2 * (h * h) + (r h + r (- h)).
    Proof.
      intro h. unfold D2sym. rewrite (Hexp h).
      assert (Hm : f (x - h) = f x + a1 * (- h) + a2 * ((- h) * (- h)) + r (- h)).
      { replace (x - h) with (x + - h) by ring. apply (Hexp (- h)). }
      rewrite Hm. ring.
    Qed.

    Theorem symmetric_second_difference_limit :
      tends0 (fun h => D2sym f x h / (h * h)) (2 * a2).
    Proof.
      intros eps Heps.
      assert (Hhalf : eps / 2 > 0) by lra.
      destruct (Hrem (eps / 2) Hhalf) as [del [Hdel Hb]].
      exists del. split; [exact Hdel|].
      intros h Hh Hhd.
      assert (Hq : D2sym f x h / (h * h) - 2 * a2
                   = r h / (h * h) + r (- h) / (h * h)).
      { rewrite D2sym_expand. field. exact Hh. }
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
  End SSD.
End ContLimit.

(* ===================================================================== *)
(*  Module Capstone  (minimal slice: TIER 1 readout-native continuum gate *)
(*  only -- the classical/MVT-based TIER 2 cap is NOT needed and is       *)
(*  omitted, which is why this file's axiom load stays at bare reals.)    *)
(* ===================================================================== *)
Module Capstone.
  Import Reals.
  Import Lra.
  Import ContLimit.
  Local Open Scope R_scope.

  (* --------------------------------------------------------------------- *)
  (*  TIER 1.  Readout-native continuum gate (classic-FREE).                *)
  (*  'f has a 2nd-order retained readout at x' = a Peano expansion whose    *)
  (*  remainder is o(h^2): the ontology's differentiability primitive.       *)
  (* --------------------------------------------------------------------- *)

  Definition has_second_readout (f:R->R) (x a1 a2:R) (r:R->R) : Prop :=
    (forall h, f (x + h) = f x + a1 * h + a2 * (h * h) + r h)
    /\ tends0 (fun h => r h / (h * h)) 0.

  Theorem continuum_gate_readout_native :
    forall f x a1 a2 r,
    has_second_readout f x a1 a2 r ->
    tends0 (fun h => D2sym f x h / (h * h)) (2 * a2).
  Proof.
    intros f x a1 a2 r [Hexp Hrem].
    exact (symmetric_second_difference_limit f x a1 a2 r Hexp Hrem).
  Qed.
End Capstone.

(* ===================================================================== *)
(*  Module InfoLorentzContinuum  —  TIER 1 (+reals): the continuum readout  *)
(*  of the discrete Lorentzian operator. The signed sum of the time/space    *)
(*  second-difference quotients tends to  □ = −∂tt + ∂xx.  The MINUS on time  *)
(*  is exactly the InfoLorentz causal sign (signature carried by ≺).         *)
(*  Builds on Capstone TIER 1; carries the standard real-analysis axioms.    *)
(*  (Module body verbatim from URCF_RD_All.v lines 7037-7078.)              *)
(* ===================================================================== *)
Module InfoLorentzContinuum.
  Import Reals. Import Lra. Import ContLimit. Import Capstone.
  Local Open Scope R_scope.

  Lemma tends0_opp : forall g L, tends0 g L -> tends0 (fun h => - g h) (- L).
  Proof.
    intros g L H eps Heps. destruct (H eps Heps) as [del [Hd Hb]].
    exists del. split;[exact Hd|]. intros h Hh Hlt. specialize (Hb h Hh Hlt).
    replace (- g h - - L) with (- (g h - L)) by ring. rewrite Rabs_Ropp. exact Hb.
  Qed.

  Lemma tends0_plus : forall g1 g2 L1 L2,
    tends0 g1 L1 -> tends0 g2 L2 -> tends0 (fun h => g1 h + g2 h) (L1+L2).
  Proof.
    intros g1 g2 L1 L2 H1 H2 eps Heps.
    destruct (H1 (eps/2) ltac:(lra)) as [d1 [Hd1 Hb1]].
    destruct (H2 (eps/2) ltac:(lra)) as [d2 [Hd2 Hb2]].
    exists (Rmin d1 d2). split. apply Rmin_pos; assumption.
    intros h Hh Hlt.
    assert (Rabs h < d1) by (eapply Rlt_le_trans;[exact Hlt|apply Rmin_l]).
    assert (Rabs h < d2) by (eapply Rlt_le_trans;[exact Hlt|apply Rmin_r]).
    specialize (Hb1 h Hh ltac:(assumption)). specialize (Hb2 h Hh ltac:(assumption)).
    replace (g1 h + g2 h - (L1+L2)) with ((g1 h - L1)+(g2 h - L2)) by ring.
    eapply Rle_lt_trans. apply Rabs_triang. lra.
  Qed.

  (* the d'Alembertian as the signed-second-difference readout limit *)
  Theorem lorentz_box_continuum :
    forall (Ft Fx:R->R) (t x a1t a2t a1x a2x:R) (rt rx:R->R),
      has_second_readout Ft t a1t a2t rt ->
      has_second_readout Fx x a1x a2x rx ->
      tends0 (fun h => - (D2sym Ft t h / (h*h)) + (D2sym Fx x h / (h*h)))
             (- (2*a2t) + 2*a2x).
  Proof.
    intros Ft Fx t x a1t a2t a1x a2x rt rx HFt HFx.
    apply (tends0_plus (fun h => - (D2sym Ft t h / (h*h)))
                       (fun h => D2sym Fx x h / (h*h))
                       (- (2*a2t)) (2*a2x)).
    - apply tends0_opp. exact (continuum_gate_readout_native Ft t a1t a2t rt HFt).
    - exact (continuum_gate_readout_native Fx x a1x a2x rx HFx).
  Qed.
End InfoLorentzContinuum.

Print Assumptions InfoLorentzContinuum.lorentz_box_continuum.
