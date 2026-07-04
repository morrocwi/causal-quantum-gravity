(******************************************************************************)
(* InfoCoercivityBoundedClosure.v -- TRIMMED EXTRACT (dropped "_attempt")     *)
(*  Provenance: extracted 2026-07-05 from research_universal_solver/formal/  *)
(*  InfoCoercivityBoundedClosure_attempt.v (axiom-free, Th_coqc arc; that    *)
(*  file's own header documents the full "small-data" coercivity-closure    *)
(*  result, C*=1.10781... calibration, and SCOPE caveats in detail -- see   *)
(*  it for the complete story).                                             *)
(*                                                                            *)
(*  This extract keeps ONLY: the Csafe constant, and the wshare/wdeg         *)
(*  (weighted-degree) definitions -- the minimal pieces that                 *)
(*  InfoDiscreteGraphCurvature.v's wdeg_uniform_weight and                   *)
(*  coercivity_threshold_via_degree theorems actually reference (checked     *)
(*  against that file's proof scripts: both proofs `unfold`/reference only   *)
(*  these three definitions, never any lemma or theorem from the source      *)
(*  file). The source file's per-edge/per-node coercivity LEMMAS and         *)
(*  THEOREMS (core_ineq, edge_energy_nonneg_if_coercive_bounded,             *)
(*  wdeg_redistribution, dissip_fold_split,                                  *)
(*  dissip_plus_cubic_fold_nonneg, cubic_energy_bounded_below_by_            *)
(*  dissipation, nonlinear_energy_nonincreasing_if_coercive_bounded, and     *)
(*  the worked Example) are NOT needed by the curvature file and are         *)
(*  intentionally dropped here -- see the source file in                     *)
(*  research_universal_solver for the full, untrimmed content and its       *)
(*  many other Requires (RDL_MetricReadout, InfoMetricIsEnergyReadout_      *)
(*  attempt, InfoMultiAgentCoupling_attempt, InfoAdvectionFromRoot_attempt,  *)
(*  InfoCubicFormTheory_attempt, InfoNonlinearRootClosure_attempt), none of  *)
(*  which this trimmed extract requires.                                    *)
(******************************************************************************)

Require RDL_GammaSpectral.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.QArith.QArith.
Open Scope Q_scope.

Module InfoCoercivityBoundedClosure.
  Import RDL_GammaSpectral.

  (* THE SAFE RATIONAL CONSTANT: chosen with ~80% margin above the sharp
     numeric ratio C*=1.10781... (calibration detail in the source file's
     header) -- Csafe=2 is the smallest clean rational the source file's
     `nra` closes directly. *)
  Definition Csafe : Q := 2#1.

  (* WEIGHTED DEGREE: total incident-edge weight at node i. *)
  Definition wshare (e : Edge) (i : nat) : Q :=
    (if Nat.eqb (u_of e) i then w_of e else 0) + (if Nat.eqb (v_of e) i then w_of e else 0).

  Definition wdeg (edges : list Edge) (i : nat) : Q :=
    fold_right (fun e acc => wshare e i + acc) 0 edges.

End InfoCoercivityBoundedClosure.
