(******************************************************************************)
(* InfoAnalysisLift.v — TRIMMED EXTRACT for discrete-quantum-gravity-journal. *)
(*                                                                            *)
(* This is NOT the full file. The original, full InfoAnalysisLift.v lives at *)
(* research_universal_solver/formal/InfoAnalysisLift.v and contains many     *)
(* unrelated +reals lift theorems (relaxation ODE, harmonic oscillator,      *)
(* unitary norm conservation, multivariable partials, etc). This extract     *)
(* keeps ONLY the piece needed by InfoQuantumGravityRootBridge.v: the        *)
(* Schwarzschild metric factor `schw` and the theorem                        *)
(* `schwarzschild_force_real` establishing its real radial derivative,       *)
(* verbatim from the source file, dated 2026-07-05.                         *)
(*                                                                            *)
(* TIER: +reals — this DEPENDS on the Coq Reals axioms (ClassicalDedekindReals*)
(* + FunctionalExtensionality-adjacent stdlib construction), exactly as in    *)
(* the source file. It is NOT axiom-free; the dependency is disclosed.       *)
(******************************************************************************)

Require Import Reals.
Require Import Coq.Reals.Ranalysis1.
Require Import Coq.micromega.Lra.
Open Scope R_scope.

(* GR radial lift: the Schwarzschild metric factor f(r)=1−2M/r ; its REAL radial derivative f'(r)=2M/r² is
   the gravitational "force" / radial Christoffel source — lifting InfoFrontier.schwarzschild (algebraic) to
   the actual derivative of the metric. Single-variable (radial), so stdlib derive_pt suffices. NOTE: the
   full multi-index Christoffel ½(∂_μ g_νσ+∂_ν g_μσ−∂_σ g_μν) needs MULTI-variable partial derivatives, which
   the stdlib single-variable Ranalysis does not provide — that remains the honest analysis [Open]. *)
Definition schw (M : R) : R -> R := minus_fct (fct_cte 1) (mult_real_fct (2*M) (inv_fct id)).
Theorem schwarzschild_force_real : forall (M r : R) (pr : derivable_pt (schw M) r),
  r <> 0 -> derive_pt (schw M) r pr = (2*M) / (r*r).
Proof.
  intros M r pr Hr. unfold schw in pr |- *.
  assert (Hid : id r <> 0) by (unfold id; exact Hr).
  rewrite (pr_nu (minus_fct (fct_cte 1) (mult_real_fct (2*M) (inv_fct id))) r pr
    (derivable_pt_minus (fct_cte 1) (mult_real_fct (2*M) (inv_fct id)) r
       (derivable_pt_const 1 r)
       (derivable_pt_scal (inv_fct id) (2*M) r
          (derivable_pt_inv id r Hid (derivable_pt_id r))))).
  rewrite derive_pt_minus, derive_pt_const, derive_pt_scal, derive_pt_inv, derive_pt_id.
  unfold id, Rsqr. field. exact Hr.
Qed.

Print Assumptions schwarzschild_force_real.
