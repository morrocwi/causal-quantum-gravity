(* ================================================================================================
   InfoSchrodinger — the Schrödinger readout FROM OUR SPINE M∂²Φ + K·L_R Φ (conservative part), not
   imported. A temporal mode exp(−iωt) has ∂²→−ω², so on an L_R-eigenmode (eigenvalue λ) the spine residual
   is K·λ − M·ω²; it vanishes iff Mω²=Kλ (the quantum DISPERSION). With E=ℏω (Planck–Einstein, ℏ from
   InfoActionQuantum) the energy spectrum E²M=ℏ²Kλ is the Hamiltonian H=K·L_R spectrum read off the graph
   Laplacian spectrum λ; PSD of L_R (R1) makes the energy real (E²≥0). The time-dependent unitary group
   exp(−iHt/ℏ) and the i∂_t generator are InfoEvolution/InfoQuantum (complex); here is the real spectral core.

   Tier: Th_coqc (axiom-free Coq structure over Q; verified below via `Print Assumptions` = Closed
   under the global context).

   Provenance: extracted verbatim from a private research repo, no content changed.
   Source: research_universal_solver/formal/URCF_RD_All.v, Module InfoSchrodinger, lines 9125-9150.
   ================================================================================================ *)
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.

Module InfoSchrodinger.
  Import Coq.QArith.QArith. Import Coq.micromega.Lqa. Open Scope Q_scope.
  Definition spine_residual (M K omsq lam : Q) : Q := K*lam - M*omsq.

  (* (1) DISPERSION: the conservative spine mode condition Mω² = Kλ *)
  Theorem spine_mode_dispersion : forall M K omsq lam : Q,
    spine_residual M K omsq lam == 0 <-> M*omsq == K*lam.
  Proof. intros. unfold spine_residual. split; intro H; lra. Qed.

  (* (2) ENERGY SPECTRUM from the graph Laplacian spectrum: E=ℏω + dispersion ⇒ E²·M = ℏ²·K·λ *)
  Theorem energy_spectrum_from_laplacian : forall hbar M K lam omsq Esq : Q,
    ~ (M == 0) -> M*omsq == K*lam -> Esq == hbar*hbar*omsq -> Esq*M == hbar*hbar*K*lam.
  Proof. intros hbar M K lam omsq Esq HM Hd HE. rewrite HE.
    transitivity (hbar*hbar*(K*lam)); [ rewrite <- Hd; ring | ring ]. Qed.

  (* (3) ENERGY IS REAL from PSD (R1): with K≥0, λ≥0 (L_R positive semidefinite) and M>0, E² ≥ 0 *)
  Theorem energy_nonneg_from_psd : forall hbar M K lam omsq Esq : Q,
    0 < M -> 0 <= K -> 0 <= lam -> M*omsq == K*lam -> Esq == hbar*hbar*omsq -> 0 <= Esq.
  Proof. intros hbar M K lam omsq Esq HM HK Hl Hd HE.
    assert (HEM : Esq*M == hbar*hbar*(K*lam)) by
      (rewrite HE; transitivity (hbar*hbar*(K*lam)); [ rewrite <- Hd; ring | ring ]).
    assert (Hh : 0 <= hbar*hbar) by nra.
    assert (HKl : 0 <= K*lam) by nra.
    assert (0 <= hbar*hbar*(K*lam)) by nra.
    nra. Qed.

  Print Assumptions spine_mode_dispersion.
  Print Assumptions energy_spectrum_from_laplacian.
  Print Assumptions energy_nonneg_from_psd.
End InfoSchrodinger.
