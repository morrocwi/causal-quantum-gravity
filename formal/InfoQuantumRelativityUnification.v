(******************************************************************************)
(* InfoQuantumRelativityUnification.v -- axiom-free, Q-only. Requires but      *)
(*  does not modify InfoLorentzInvariance.v and InfoSchrodinger.v.            *)
(*                                                                            *)
(*  Proves that this repository's quantum dispersion relation (Branch 1,     *)
(*  InfoSchrodinger.spine_mode_dispersion) and its special-relativistic       *)
(*  wave operator (Branch 2, InfoLorentzInvariance.box_quad, already proven   *)
(*  boost-invariant) are literally the same equation under an exact linear    *)
(*  reparametrization -- pure ring algebra, no continuum limit, no new        *)
(*  axiom. See PAPER.md Sec. 6 for the full derivation and interpretation.    *)
(******************************************************************************)

Require InfoLorentzInvariance.
Require InfoSchrodinger.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Open Scope Q_scope.

Module InfoQuantumRelativityUnification.
  Import InfoLorentzInvariance.InfoLorentzInvariance.
  Import InfoSchrodinger.InfoSchrodinger.

  Theorem box_quad_is_spine_residual : forall M K omsq lam : Q,
    box_quad (M*omsq*(1#2)) (K*lam*(1#2)) == spine_residual M K omsq lam.
  Proof.
    intros M K omsq lam. unfold box_quad, spine_residual. ring.
  Qed.

  Theorem spine_dispersion_iff_box_quad_vanishes : forall M K omsq lam : Q,
    M*omsq == K*lam <-> box_quad (M*omsq*(1#2)) (K*lam*(1#2)) == 0.
  Proof.
    intros M K omsq lam.
    rewrite (box_quad_is_spine_residual M K omsq lam).
    symmetry. exact (spine_mode_dispersion M K omsq lam).
  Qed.

  Corollary spine_dispersion_preserved_under_boost : forall M K omsq lam g v atx : Q,
    g*g*(1 - v*v) == 1 ->
    M*omsq == K*lam ->
    box_quad (catt g v (M*omsq*(1#2)) atx (K*lam*(1#2)))
             (caxx g v (M*omsq*(1#2)) atx (K*lam*(1#2))) == 0.
  Proof.
    intros M K omsq lam g v atx Hg Hdisp.
    rewrite (box_quad_boost_invariant g v (M*omsq*(1#2)) atx (K*lam*(1#2)) Hg).
    apply (spine_dispersion_iff_box_quad_vanishes M K omsq lam).
    exact Hdisp.
  Qed.

  Print Assumptions box_quad_is_spine_residual.
  Print Assumptions spine_dispersion_iff_box_quad_vanishes.
  Print Assumptions spine_dispersion_preserved_under_boost.

End InfoQuantumRelativityUnification.
