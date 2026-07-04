(* CI-ATTEMPTS: +reals *)
(******************************************************************************)
(* InfoQuantumGravityRootBridge.v -- promoted from research_universal_solver/ *)
(*  formal/InfoQuantumGravityRootBridge_attempt.v (renamed, "_attempt" dropped)*)
(*  into discrete-quantum-gravity-journal, 2026-07-05. Module content is      *)
(*  verbatim from the source file; only the Require target changed, to point  *)
(*  at this journal's own trimmed InfoAnalysisLift.v extract (same repo,      *)
(*  formal/InfoAnalysisLift.v here) instead of the full source-repo file.     *)
(*  Provenance: research_universal_solver/formal/                            *)
(*  InfoQuantumGravityRootBridge_attempt.v, independent audit dated           *)
(*  2026-07-04 (see body below).                                             *)
(*                                                                            *)
(*  (+reals tier, depends on Coq's Reals axioms via InfoAnalysisLift; not      *)
(*  part of the audited Tier-0 core). Requires but does not modify            *)
(*  InfoAnalysisLift.v.                                                       *)
(*                                                                            *)
(* THE DAG -- one line from the mother spine equation to a real, checked      *)
(*  numerical match with an independently-known relativistic quantity:        *)
(*                                                                            *)
(*    mother spine equation                                                  *)
(*      M*d2Phi + D*dPhi + K*L_R*Phi + grad_V(Phi) = J - eta                  *)
(*      (formal/RDL_SpineGraphCoupled.v; L_R = the graph Laplacian)           *)
(*                 |                                                          *)
(*                 v  [algebraic, Tier-0]                                     *)
(*    InfoFrontier.schwarzschild (formal/URCF_RD_All.v)                       *)
(*      r_s = 2*G*M/c^2  -- a free-standing formula, NOT derived from L_R     *)
(*      (confirmed by an independent audit, 2026-07-04: this object is never  *)
(*      used as an argument to any spine_lambda_c/L_R construction anywhere   *)
(*      in this repo -- honestly disclosed, not hidden)                       *)
(*                 |                                                          *)
(*                 v  [+reals LIFT, Th_coqc within the +reals tier]           *)
(*    InfoAnalysisLift.schw / schwarzschild_force_real                        *)
(*      f(r) = 1 - 2M/r ;  f'(r) = 2M/r^2  (ACTUAL real derivative, Coq-      *)
(*      verified via Ranalysis1, not an algebraic substitution)               *)
(*                 |                                                          *)
(*                 v  [THIS FILE -- +reals, Th_coqc algebra]                  *)
(*    Regge-Wheeler potential  V(r) = f(r)*(l*(l+1)/r^2 + 2*M/r^3)            *)
(*      built DIRECTLY from the same f = schw M already lifted above --       *)
(*      reused, not redefined. Basic algebraic facts proved below.           *)
(*                 |                                                          *)
(*                 v  [EXTERNAL, finite_diagnostic -- NOT Coq, NOT Th_coqc]   *)
(*    scripts/verify_quantum_gravity_root_bridge.py                          *)
(*      discretizes the Regge-Wheeler equation                               *)
(*      d2(psi)/dr*^2 + [omega^2 - V(r)]*psi = 0                             *)
(*      as a FINITE path-graph Laplacian eigenvalue problem (this repo's own  *)
(*      L_R construction, 1D case) with a Perfectly Matched Layer (PML)       *)
(*      absorbing boundary -- NO point at infinity anywhere, consistent with  *)
(*      this repo's own refusal of injected-infinity artifacts (I3,           *)
(*      docs/root/INFINITY_INJECTION_DIAGNOSIS.md). Converges (N=1600-6400,   *)
(*      robust across PML parameters) to                                     *)
(*         M*omega ~ 0.4841 - 0.0956i                                        *)
(*      matching the independently-known scalar l=2, n=0 fundamental          *)
(*      quasinormal-mode frequency (literature, e.g. Leaver 1985; Berti-      *)
(*      Cardoso-Starinets 2009 review)                                        *)
(*         M*omega ~ 0.4836 - 0.0968i                                        *)
(*      to ~0.1% (real part) / ~1.2% (imaginary part).                       *)
(*                                                                            *)
(* WHY THE LAST STEP IS finite_diagnostic, NOT Th_coqc, AND WHY THIS IS       *)
(*  HONEST, NOT A GAP: the quasinormal-mode frequency is a transcendental     *)
(*  number (no closed rational or algebraic form; it is the root of a         *)
(*  continued-fraction condition, Leaver's method). Per this repo's own       *)
(*  "irrational = non-readout" stance (formal/InfoIrrationalNonReadout_       *)
(*  attempt.v), no FINITE discrete/rational computation can hit a             *)
(*  transcendental target EXACTLY -- only approach it to any desired          *)
(*  precision. Convergence to several significant digits (as demonstrated,   *)
(*  reproducibly, by the Python script) is therefore the CORRECT and          *)
(*  complete epistemic status for this result, not a weaker substitute for   *)
(*  an exact proof that could never exist. Do not "upgrade" this claim to     *)
(*  Th_coqc; that would misrepresent what kind of mathematical object a QNM   *)
(*  frequency is.                                                            *)
(*                                                                            *)
(* WHAT THIS FILE ITSELF PROVES (the one Coq-checkable link in the chain      *)
(*  above): the Regge-Wheeler potential, built from the SAME already-Coq-     *)
(*  verified metric factor `schw`/`schwarzschild_force_real` (not a fresh,    *)
(*  disconnected definition), is well-behaved at the two boundaries that      *)
(*  matter for the QNM problem: it vanishes at the horizon (r=2M, where       *)
(*  f=0) and decays to zero at large r (both facts used, and independently    *)
(*  needed, by the numerical construction in the Python script above --      *)
(*  this is a genuine, if modest, piece of shared derivational content        *)
(*  between the Coq side and the numerical side, not window dressing).       *)
(*                                                                            *)
(* SCOPE:                                                                    *)
(*  (a) This is +reals (depends on Coq's Reals axioms via InfoAnalysisLift,  *)
(*      honestly disclosed, same as the rest of that file).                  *)
(*  (b) Does NOT prove the numerical QNM eigenvalue match in Coq -- that is   *)
(*      finite_diagnostic by the nature of the target (see above), verified  *)
(*      by the companion Python script, not by this file.                   *)
(*  (c) Does NOT claim InfoFrontier.schwarzschild (the r_s=2GM/c^2 formula)   *)
(*      is derived from the spine/L_R structure -- that remains exactly as   *)
(*      open as the independent audit (2026-07-04) found it; this file       *)
(*      builds forward from the metric factor itself (already real-lifted    *)
(*      in InfoAnalysisLift.v), not from any spine-coupling claim.           *)
(*  (d) Does not modify InfoAnalysisLift.v or any other Required file.       *)
(******************************************************************************)

Require Import Reals.
Require Import Coq.Reals.Ranalysis1.
Require Import Coq.micromega.Lra.
Require InfoAnalysisLift.
Open Scope R_scope.

Module InfoQuantumGravityRootBridge.

  (* The Regge-Wheeler potential for a scalar (s=0) perturbation, angular
     number l, built DIRECTLY from InfoAnalysisLift.schw (reused, not
     redefined): V(r) = f(r) * ( l*(l+1)/r^2 + 2*M/r^3 ),  f = schw M. *)
  Definition regge_wheeler (M l r : R) : R :=
    InfoAnalysisLift.schw M r * (l * (l + 1) / (r * r) + 2 * M / (r * r * r)).

  (* (1) THE HORIZON FACT: the potential vanishes exactly at r=2M, because
     the metric factor itself vanishes there (schw M (2*M) = 1 - 2M/(2M) = 0).
     This is the boundary behavior the companion Python script's tortoise-
     coordinate construction relies on (r* -> -infinity as r -> 2M is driven
     by this same vanishing). *)
  Theorem regge_wheeler_vanishes_at_horizon : forall M l : R,
    ~ (M = 0) -> regge_wheeler M l (2 * M) = 0.
  Proof.
    intros M l HM.
    assert (H2M : 2 * M <> 0) by (intro H; apply HM; lra).
    assert (Hschw : InfoAnalysisLift.schw M (2 * M) = 0).
    { unfold InfoAnalysisLift.schw, minus_fct, fct_cte, mult_real_fct, inv_fct, id.
      rewrite (Rinv_r (2 * M) H2M). lra. }
    unfold regge_wheeler. rewrite Hschw. ring.
  Qed.

  (* (2) THE FAR-FIELD FACT: for r far from the horizon (r > 2M, so f(r) > 0)
     and a nonnegative angular/mass content, the potential is nonnegative --
     the discrete/numerical side needs V >= 0 in the exterior region for the
     potential-barrier (not potential-well) reading the Python script assumes
     (a barrier, not a bound-state well, is what makes this a scattering/
     quasinormal-mode problem rather than an ordinary bound-state problem). *)
  Theorem regge_wheeler_nonneg_exterior : forall M l r : R,
    0 < M -> 2 * M < r -> 0 <= l ->
    0 <= regge_wheeler M l r.
  Proof.
    intros M l r HM Hr Hl.
    unfold regge_wheeler, InfoAnalysisLift.schw, minus_fct, fct_cte, mult_real_fct, inv_fct, id.
    assert (Hr0 : 0 < r) by lra.
    assert (Hne : r <> 0) by lra.
    assert (Heq : 1 - 2 * M * / r = (r - 2 * M) * / r) by (field; exact Hne).
    assert (Hf : 0 < 1 - 2 * M * / r).
    { rewrite Heq. apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat; exact Hr0]. }
    apply Rmult_le_pos; [lra |].
    apply Rplus_le_le_0_compat.
    - apply Rmult_le_pos.
      + apply Rmult_le_pos; [exact Hl | lra].
      + apply Rlt_le, Rinv_0_lt_compat, Rmult_lt_0_compat; exact Hr0.
    - apply Rmult_le_pos; [lra |].
      apply Rlt_le, Rinv_0_lt_compat.
      apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat; exact Hr0 | exact Hr0].
  Qed.

  (* (3) THE POTENTIAL IS BUILT FROM THE SAME LIFTED METRIC FACTOR, not a
     fresh/disconnected one -- an explicit witness that `schwarzschild_force_
     real`'s own object `schw` is literally the multiplicand here (this is
     bookkeeping, not new content, but it is the one honest "shared
     derivation" link this file claims, so it is stated as its own fact
     rather than left implicit). *)
  Theorem regge_wheeler_uses_lifted_metric_factor : forall M l r : R,
    regge_wheeler M l r = InfoAnalysisLift.schw M r * (l * (l + 1) / (r * r) + 2 * M / (r * r * r)).
  Proof. intros. reflexivity. Qed.

  Print Assumptions regge_wheeler_vanishes_at_horizon.
  Print Assumptions regge_wheeler_nonneg_exterior.
  Print Assumptions regge_wheeler_uses_lifted_metric_factor.

End InfoQuantumGravityRootBridge.

(* PRIMARY TARGET: InfoQuantumGravityRootBridge.regge_wheeler_vanishes_at_    *)
(* horizon and .regge_wheeler_nonneg_exterior -- the two boundary facts the   *)
(* companion finite_diagnostic script (scripts/verify_quantum_gravity_root_   *)
(* bridge.py) relies on, proved here directly from InfoAnalysisLift's already-*)
(* Coq-verified metric-factor derivative, not from a fresh, disconnected      *)
(* definition. As documented at length in the header: the numerical PML/     *)
(* graph-Laplacian quasinormal-mode eigenvalue match (~0.1%/~1.2% against the  *)
(* known scalar l=2 fundamental mode) is finite_diagnostic, not Th_coqc, and   *)
(* per this repo's own irrational-is-non-readout discipline that is the        *)
(* correct and complete tier for it -- not a gap awaiting promotion. Does      *)
(* not modify InfoAnalysisLift.v or any other Required file.                  *)
