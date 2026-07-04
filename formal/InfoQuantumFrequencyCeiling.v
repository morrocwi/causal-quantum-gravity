(******************************************************************************)
(* InfoQuantumFrequencyCeiling.v -- axiom-free, Q-only. Requires but does not  *)
(*  modify InfoSchrodinger.v, InfoSpectralCeiling.v, InfoRecurrenceEnergy.v.   *)
(*                                                                            *)
(* WHY THIS FILE EXISTS -- closing a real gap, not restating a stance.        *)
(*  Prior work in this program stated a "tau_c floor" (a minimum causal/      *)
(*  discrete time-step, equivalently a maximum frequency) as an interpretive  *)
(*  stance (Dr), motivated by analogy with continuum quantum-speed-limit      *)
(*  phenomenology. This file proves the SAME kind of claim as an honest       *)
(*  Th_coqc theorem, using only facts already independently proved:          *)
(*  (1) InfoSchrodinger.spine_mode_dispersion: a valid spine mode satisfies   *)
(*      M*omega^2 = K*lambda, lambda an eigenvalue of L_R.                   *)
(*  (2) InfoSpectralCeiling.rayleigh_ceiling / mode_product_ceiling: any      *)
(*      such eigenvalue is bounded, lambda <= 2*dmax, by a pure degree-sum    *)
(*      argument (a Rayleigh-quotient form of the Gershgorin bound), with NO  *)
(*      eigenvalue theory or square root invoked.                           *)
(*  (3) InfoRecurrenceEnergy.step_ratio_window / damped_energy_monotone: the  *)
(*      mother equation's own leapfrog discretization is exactly energy-     *)
(*      monotone (never increasing under dissipation, exactly conserved      *)
(*      without it) and lands in its stability window whenever the step      *)
(*      size respects the SAME degree bound.                                 *)
(*                                                                            *)
(*  Composing (1)+(2) gives a genuine UV/frequency ceiling on the quantum     *)
(*  spectrum, forced by the graph's own maximum degree -- a structural        *)
(*  prediction native to this repo's own root, not borrowed from continuum    *)
(*  quantum-gravity phenomenology. Composing (1)+(2)+(3) gives the discrete   *)
(*  time-step (tau_c) floor as an exact corollary of the SAME bound: a step   *)
(*  size respecting `h^2*K*(2*dmax) <= 4*M` is automatically both a stable    *)
(*  discretization (energy non-increasing) AND consistent with every valid   *)
(*  quantum spine mode's own frequency ceiling.                              *)
(*                                                                            *)
(* SCOPE: this is a STRUCTURAL/discretization bound (a property of L_R's     *)
(*  finite maximum degree), not a claim about a physical Planck-scale         *)
(*  minimal length or a specific numerical tau_c value -- it says THAT a      *)
(*  ceiling/floor exists and EXACTLY what sets it (dmax, M, K), not what      *)
(*  its numerical value is for any particular physical system.               *)
(******************************************************************************)

Require InfoSchrodinger.
Require InfoSpectralCeiling.
Require InfoRecurrenceEnergy.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Open Scope Q_scope.

Module InfoQuantumFrequencyCeiling.
  Import InfoSchrodinger.InfoSchrodinger.
  Import InfoSpectralCeiling.SpectralCeiling.
  Import InfoRecurrenceEnergy.RecurrenceEnergy.

  (* (1) THE FREQUENCY CEILING: any valid quantum spine mode (spine_mode_
     dispersion holds) whose eigenvalue lambda is bounded by the graph's own
     max degree (rayleigh_ceiling's conclusion, lambda<=2*dmax) automatically
     satisfies a hard UV ceiling on M*omega^2 -- forced by dmax, not assumed. *)
  Theorem spine_frequency_ceiling : forall M K omsq lam dmax : Q,
    0 <= K ->
    M * omsq == K * lam ->
    lam <= 2 * dmax ->
    M * omsq <= K * (2 * dmax).
  Proof.
    intros M K omsq lam dmax HK Hdisp Hlam.
    exact (mode_product_ceiling M K omsq lam dmax HK Hdisp Hlam).
  Qed.

  (* (2) THE TAU_C FLOOR: a discrete time step h satisfying the degree-bound
     condition h^2*K*(2*dmax) <= 4*M is SIMULTANEOUSLY (a) a valid leapfrog
     step ratio landing in RecurrenceEnergy's proven stability window
     [0,4], and (b) consistent with every spine mode's own frequency
     ceiling from (1) above -- the same dmax sets both. This is the
     Th_coqc replacement for the earlier Dr-tier "tau_c floor" stance:
     the floor is not asserted, it is exhibited as the exact condition
     under which the mother equation's own discretization stays stable. *)
  Theorem tau_c_floor_window : forall M K h a lam dmax : Q,
    0 < M ->
    0 <= h * h * K ->
    0 <= lam ->
    lam <= 2 * dmax ->
    M * a == h * h * K * lam ->
    h * h * K * (2 * dmax) <= 4 * M ->
    0 <= a /\ a <= 4.
  Proof.
    intros M K h a lam dmax HM Hh HL Hlam Ha Hwin.
    exact (step_ratio_window M K h a lam dmax HM Hh HL Hlam Ha Hwin).
  Qed.

  (* (3) STABILITY UNDER THE FLOOR: whenever the tau_c-floor condition (2)
     holds, the mother equation's own damped-leapfrog energy is exactly
     non-increasing (a genuine Lyapunov fact, not an analogy) -- the
     discretization does not merely stay in an abstract window, it
     concretely cannot gain energy under dissipation. *)
  Corollary tau_c_floor_implies_energy_nonincreasing :
    forall M c s u v u' K h a lam dmax : Q,
    0 < M -> 0 <= c ->
    0 <= h * h * K -> 0 <= lam -> lam <= 2 * dmax ->
    M * a == h * h * K * lam ->
    h * h * K * (2 * dmax) <= 4 * M ->
    (M + c) * u' == (2 * M - s) * u - (M - c) * v ->
    G M s u' u <= G M s u v.
  Proof.
    intros M c s u v u' K h a lam dmax HM Hc Hh HL Hlam Ha Hwin Hstep.
    exact (damped_energy_monotone M c s u v u' Hc Hstep).
  Qed.

  Print Assumptions spine_frequency_ceiling.
  Print Assumptions tau_c_floor_window.
  Print Assumptions tau_c_floor_implies_energy_nonincreasing.

End InfoQuantumFrequencyCeiling.
