(* ===================================================================== *)
(*  RDL_GammaSpectral.v -- TRIMMED EXTRACT                                *)
(*  Provenance: extracted 2026-07-05 from                                 *)
(*  research_universal_solver/formal/RDL_GammaSpectral.v (axiom-free,     *)
(*  Th_coqc arc). This extract keeps ONLY the Edge type and the           *)
(*  w_of/u_of/v_of projections -- the minimal shared vocabulary that      *)
(*  InfoDiscreteGraphCurvature.v and InfoCoercivityBoundedClosure.v both  *)
(*  build on. The source file's Dirichlet-energy (Γ) theorems             *)
(*  (energy_nonneg, energy_edge_gauge, energy_zero_edges) and the         *)
(*  discrete-Laplacian-stencil theorems (laplacian_stencil,               *)
(*  secondDiff_quadratic, secondDiff_readout_invariant) are NOT needed by *)
(*  either downstream file's proof scripts and are intentionally dropped  *)
(*  here -- see the source file in research_universal_solver for the      *)
(*  full, untrimmed content.                                              *)
(* ===================================================================== *)

Require Import Coq.QArith.QArith.
Open Scope Q_scope.

(* ===== Γ (graph) primitive: a weighted edge over ℚ ===== *)
Definition Edge := (nat * nat * Q)%type.
Definition w_of (e:Edge) : Q   := snd e.
Definition u_of (e:Edge) : nat := fst (fst e).
Definition v_of (e:Edge) : nat := snd (fst e).
