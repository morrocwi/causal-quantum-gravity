(*
   InfoSeedCurvatureIntegration.v -- PROMOTED EXTRACT
   Provenance: elevated 2026-07-08/10 from research_universal_solver/formal/InfoSeedCurvatureIntegration_attempt.v
   (renamed, "_attempt" dropped; Require targets adjusted to this repo's file names).
   Verified standalone at elevation (coqc -q -R . DQG; all Print Assumptions "Closed under
   the global context") and wired into COQFILES/make verify + CI on 2026-07-10, closing a
   review finding that elevation alone had left these outside the CI-guarded build.
   The original header below is kept verbatim from the audited source (including its
   "EXPLORATORY, single-attempt" self-description, which refers to its role in the source
   repo's exploratory arc, not to its verification status here).
*)
(******************************************************************************)
(* InfoSeedCurvatureIntegration.v -- EXPLORATORY, single-attempt.       *)
(*   Requires InfoAsymmetricSeedTrifurcation, InfoDiscreteGraphCurvature_  *)
(*   attempt, InfoCoercivityBoundedClosure, RDL_GammaSpectral (all this    *)
(*   repo, all untouched). No axiom, no Reals, no continuum. TIER = Th_coqc.        *)
(*                                                                            *)
(* THE FRONTIER DOC'S ITEM 2: build the discrete curvature this repo already        *)
(* has proven (Forman-Ricci, InfoDiscreteGraphCurvature.v) FROM                *)
(* SymOff(R0_forced) -- i.e. show the curvature machinery already proven elsewhere       *)
(* in this repo is genuinely compatible with an R0-derived L_R, not merely sitting          *)
(* alongside it. Following InfoSeedFeedsQuantumRelativity_attempt.v's own audit-               *)
(* corrected discipline: check HONESTLY whether this application adds anything beyond            *)
(* a concrete instance before framing it as a 'connection,' and say so plainly either              *)
(* way -- do not repeat that file's original overclaim pattern.                                      *)
(*                                                                            *)
(* THE CONSTRUCTION: a uniform-weight K3 (complete 3-vertex) edge list, matching                       *)
(* EXACTLY the seed instantiation InfoSeedFeedsQuantumRelativity_attempt.v already                       *)
(* used for the QM/SR eigenvalue bridge (weight w on every edge). This is the SAME seed                    *)
(* family, now read through the curvature lens instead of the spectral lens.                                 *)
(*                                                                            *)
(* WHAT IS PROVED (Th_coqc):                                                                                   *)
(*   K3_deg_two                every node of K3Edges(w) has UNWEIGHTED degree exactly 2                          *)
(*                            (each node connects to the other two) -- direct computation.                          *)
(*   K3_forman_flat            consequently, EVERY edge of K3Edges(w) has Forman curvature                            *)
(*                            EXACTLY ZERO -- applying InfoDiscreteGraphCurvature's own                                *)
(*                            forman_flat_if_both_degree_two, not re-deriving it. K3 (=the                              *)
(*                            3-cycle) is Forman-flat, matching this repo's own documented                                 *)
(*                            2-regular-graph pattern (C6 is flat for the same reason) -- an                                 *)
(*                            HONEST, expected result, not a numerically striking one.                                        *)
(*   K3_wdeg_is_2w             the WEIGHTED degree (wdeg, InfoCoercivityBoundedClosure's own,                                    *)
(*                            reused) of every node is EXACTLY 2*w -- via wdeg_uniform_weight,                                     *)
(*                            applied, not re-derived.                                                                                *)
(*   wdeg_matches_seed_degree_term   THE LINK: 2*w -- the SAME weighted-degree number that sets                                        *)
(*                            Forman-adjacent curvature/coercivity thresholds via wdeg -- is                                              *)
(*                            EXACTLY the degree term appearing in Part 7's forced-D formula                                                *)
(*                            for this uniform seed. Proved by direct computation on both sides,                                            *)
(*                            not posited to match.                                                                                              *)
(*   seed_D_ties_wdeg_and_forman_together   THE SYNTHESIS: for THIS uniform K3 seed, in ONE                                                        *)
(*                            package -- (i) every edge is Forman-flat, (ii) the forced D value                                                       *)
(*                            at every node is EXACTLY wdeg(that node) minus lam times the FIXED                                                        *)
(*                            circulation constant -- i.e. Forman curvature (via wdeg) and the                                                            *)
(*                            forced D formula are both honest functions of the SAME underlying                                                             *)
(*                            weighted-degree data for this seed family.                                                                                       *)
(*                                                                            *)
(* SCOPE / TIER HONESTY -- read this before citing as more than it is:                                                                                            *)
(*   [Th_coqc] Every theorem above, exactly as stated -- all direct computation or direct                                                                            *)
(*   application of already-proven theorems (forman_flat_if_both_degree_two,                                                                                          *)
(*   wdeg_uniform_weight, diagpart_R0_forced_is_degree_minus_circulation), not fresh derivations.                                                                        *)
(*   [Dr, stated openly, matching InfoSeedFeedsQuantumRelativity_attempt.v's own audit-corrected               *)
(*   discipline]: NONE of the underlying theorems (forman_flat_if_both_degree_two,                                                                                          *)
(*   wdeg_uniform_weight) become tighter, more general, or newly true because of this file --                                                                                *)
(*   they were already proven for arbitrary edge lists/weights before this file existed. What IS                                                                              *)
(*   genuinely new here is the CONCRETE COMPUTATION tying the seed's own degree term to wdeg                                                                                    *)
(*   (a real, checked equality on two independently-defined quantities, not assumed) and the                                                                                      *)
(*   packaging of Forman-flatness + forced-D into one honest statement about the SAME seed. This                                                                                    *)
(*   does NOT show curvature is NON-flat or numerically interesting for this seed (K3 is flat, an                                                                                     *)
(*   honest, unglamorous fact) -- a non-uniform-weight or larger (n>3) seed would be needed for a                                                                                       *)
(*   genuinely non-flat curvature reading, and is not attempted here.                                                                                                                      *)
(******************************************************************************)

Require RDL_GammaSpectral.
Require InfoDiscreteGraphCurvature.
Require InfoCoercivityBoundedClosure.
Require InfoAsymmetricSeedTrifurcation.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Open Scope Q_scope.

Import InfoDiscreteGraphCurvature.InfoDiscreteGraphCurvature.
Import InfoCoercivityBoundedClosure.InfoCoercivityBoundedClosure.

(* ========================================================================= *)
(* PART A -- the uniform-weight K3 edge list, matching InfoSeedFeedsQuantum-    *)
(* Relativity_attempt.v's own seed instantiation (weight w on every edge).      *)
(* ========================================================================= *)

Definition K3Edges (w : Q) : list RDL_GammaSpectral.Edge :=
  [(0%nat, 1%nat, w); (0%nat, 2%nat, w); (1%nat, 2%nat, w)].

Theorem K3_deg_two :
  forall w : Q,
    deg (K3Edges w) 0%nat == 2
    /\ deg (K3Edges w) 1%nat == 2
    /\ deg (K3Edges w) 2%nat == 2.
Proof.
  intro w. unfold deg, share, K3Edges. simpl. repeat split; ring.
Qed.

(* [Th_coqc] Applying forman_flat_if_both_degree_two, not re-deriving it:        *)
(* EVERY edge of K3Edges(w) is Forman-flat -- K3 (= the 3-cycle) matches this      *)
(* repo's own documented 2-regular-graph pattern (C6 is flat for the same reason). *)
Theorem K3_forman_flat :
  forall w : Q,
    forman (K3Edges w) (0%nat, 1%nat, w) == 0
    /\ forman (K3Edges w) (0%nat, 2%nat, w) == 0
    /\ forman (K3Edges w) (1%nat, 2%nat, w) == 0.
Proof.
  intro w.
  destruct (K3_deg_two w) as [D0 [D1 D2]].
  repeat split;
    apply forman_flat_if_both_degree_two;
    unfold RDL_GammaSpectral.u_of, RDL_GammaSpectral.v_of; simpl; assumption.
Qed.

(* [Th_coqc] Applying wdeg_uniform_weight, not re-deriving it. *)
Theorem K3_wdeg_is_2w :
  forall w : Q,
    wdeg (K3Edges w) 0%nat == (2#1) * w
    /\ wdeg (K3Edges w) 1%nat == (2#1) * w
    /\ wdeg (K3Edges w) 2%nat == (2#1) * w.
Proof.
  intro w.
  assert (Hw : forall e, In e (K3Edges w) -> RDL_GammaSpectral.w_of e == w).
  { intros e He. unfold K3Edges in He. simpl in He.
    destruct He as [H|[H|[H|H]]]; try (rewrite <- H; unfold RDL_GammaSpectral.w_of; simpl; reflexivity).
    contradiction. }
  destruct (K3_deg_two w) as [D0 [D1 D2]].
  split.
  { rewrite (wdeg_uniform_weight (K3Edges w) 0%nat w Hw). rewrite D0. ring. }
  split.
  { rewrite (wdeg_uniform_weight (K3Edges w) 1%nat w Hw). rewrite D1. ring. }
  rewrite (wdeg_uniform_weight (K3Edges w) 2%nat w Hw). rewrite D2. ring.
Qed.

(* ========================================================================= *)
(* PART B -- THE LINK: wdeg matches the degree term in Part 7's forced-D        *)
(* formula for a uniform-weight seed, exactly.                                *)
(* ========================================================================= *)

Definition WtUniform (w : Q) (i j : nat) : Q :=
  match i, j with
  | 0%nat, 0%nat | 1%nat, 1%nat | 2%nat, 2%nat => 0
  | _, _ => w
  end.

Theorem WtUniform_symmetric : forall w i j, WtUniform w i j == WtUniform w j i.
Proof.
  intros w i j.
  destruct i as [|[|[|i]]]; destruct j as [|[|[|j]]]; unfold WtUniform; try reflexivity.
Qed.

(* [Th_coqc] THE LINK: computed on both sides, not assumed to match. *)
Theorem wdeg_matches_seed_degree_term :
  forall w : Q,
    wdeg (K3Edges w) 0%nat == WtUniform w 0%nat 1%nat + WtUniform w 0%nat 2%nat
    /\ wdeg (K3Edges w) 1%nat == WtUniform w 1%nat 0%nat + WtUniform w 1%nat 2%nat
    /\ wdeg (K3Edges w) 2%nat == WtUniform w 2%nat 0%nat + WtUniform w 2%nat 1%nat.
Proof.
  intro w.
  destruct (K3_wdeg_is_2w w) as [W0 [W1 W2]].
  unfold WtUniform. simpl.
  split.
  { rewrite W0. ring. }
  split.
  { rewrite W1. ring. }
  rewrite W2. ring.
Qed.

(* ========================================================================= *)
(* PART C -- THE SYNTHESIS: Forman-flatness and the forced-D formula, in ONE    *)
(* package, for the SAME uniform K3 seed.                                     *)
(* ========================================================================= *)

Theorem seed_D_ties_wdeg_and_forman_together :
  forall w lam : Q,
    (* Forman curvature is flat at every edge *)
    (forman (K3Edges w) (0%nat, 1%nat, w) == 0
     /\ forman (K3Edges w) (0%nat, 2%nat, w) == 0
     /\ forman (K3Edges w) (1%nat, 2%nat, w) == 0)
    /\
    (* the forced D at every node is EXACTLY wdeg minus lam times the fixed circulation *)
    (InfoAsymmetricSeedTrifurcation.DiagPart
       (InfoAsymmetricSeedTrifurcation.R0_forced (WtUniform w) lam) 0%nat 0%nat
       == wdeg (K3Edges w) 0%nat - lam * (2#1)
     /\ InfoAsymmetricSeedTrifurcation.DiagPart
          (InfoAsymmetricSeedTrifurcation.R0_forced (WtUniform w) lam) 1%nat 1%nat
          == wdeg (K3Edges w) 1%nat
     /\ InfoAsymmetricSeedTrifurcation.DiagPart
          (InfoAsymmetricSeedTrifurcation.R0_forced (WtUniform w) lam) 2%nat 2%nat
          == wdeg (K3Edges w) 2%nat + lam * (2#1)).
Proof.
  intros w lam.
  split.
  { exact (K3_forman_flat w). }
  pose proof (InfoAsymmetricSeedTrifurcation.diagpart_R0_forced_is_degree_minus_circulation
                (WtUniform w) (WtUniform_symmetric w) lam) as [D0 [D1 D2]].
  destruct (wdeg_matches_seed_degree_term w) as [WM0 [WM1 WM2]].
  split.
  { rewrite D0, WM0. ring. }
  split.
  { rewrite D1, WM1. ring. }
  rewrite D2, WM2. ring.
Qed.

(* Non-vacuous concrete witness: w=5, lam=1 -- Forman-flat at every edge, D        *)
(* forced to (8, 10, 12) (wdeg=10 at every node, shifted by +-2*lam). *)
Example seed_curvature_witness :
  wdeg (K3Edges (5#1)) 0%nat == 10#1
  /\ InfoAsymmetricSeedTrifurcation.DiagPart
       (InfoAsymmetricSeedTrifurcation.R0_forced (WtUniform (5#1)) (1#1)) 0%nat 0%nat
     == 8#1
  /\ InfoAsymmetricSeedTrifurcation.DiagPart
       (InfoAsymmetricSeedTrifurcation.R0_forced (WtUniform (5#1)) (1#1)) 2%nat 2%nat
     == 12#1.
Proof.
  pose proof (seed_D_ties_wdeg_and_forman_together (5#1) (1#1)) as [_ [E0 [_ E2]]].
  destruct (K3_wdeg_is_2w (5#1)) as [W0 [_ W2]].
  split.
  { exact W0. }
  split.
  { rewrite E0, W0. ring. }
  rewrite E2, W2. ring.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions K3_deg_two.
Print Assumptions K3_forman_flat.
Print Assumptions K3_wdeg_is_2w.
Print Assumptions WtUniform_symmetric.
Print Assumptions wdeg_matches_seed_degree_term.
Print Assumptions seed_D_ties_wdeg_and_forman_together.
Print Assumptions seed_curvature_witness.
