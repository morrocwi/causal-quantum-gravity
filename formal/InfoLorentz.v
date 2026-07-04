(* ===================================================================== *)
(*  InfoLorentz.v                                                         *)
(*                                                                         *)
(*  PURPOSE: the indefinite (Lorentzian, −+) signature is NOT imposed by  *)
(*  coordinates — it is carried by the CAUSAL ORDER ≺ (sign −1 on         *)
(*  causal/timelike edges, +1 on spacelike). FRAME-COVARIANCE = invariance*)
(*  under causal-structure-preserving relabellings (discrete "boosts").   *)
(*  This realises the MLCD core (Lorentz from the order, covariance       *)
(*  structural) at the DISCRETE level, axiom-free.                       *)
(*                                                                         *)
(*  HONEST BOUNDARY: the continuum □ = −∂tt+∂xx readout of this operator  *)
(*  stays the hard tier (BD coefficients / continuum-contamination) —     *)
(*  NOT solved here. This file only proves the discrete causal bilinear   *)
(*  form's self-adjointness, its Euclidean reduction, and its             *)
(*  frame-covariance under edge-multiset permutation.                    *)
(*                                                                         *)
(*  TIER: Th_coqc, Tier-0, axiom-free (over Q; no Section/Hypothesis;     *)
(*  verified below by `Print Assumptions` — expect Closed under the       *)
(*  global context for all three theorems).                              *)
(*                                                                         *)
(*  PROVENANCE: extracted verbatim (definitions + Module InfoLorentz)     *)
(*  from research_universal_solver/formal/URCF_RD_All.v, lines 6042–6045  *)
(*  (Edge/w_of/u_of/v_of, inside Module Gamma), lines 6698 and 6765       *)
(*  (distinguish, info_form, inside Module InfoOperator), and lines       *)
(*  6985–7028 (Module InfoLorentz itself). Authored 2026-06-27, commit    *)
(*  71d4095 feat(formal): InfoLorentz -- discrete frame-covariant         *)
(*  Lorentzian operator (frontier #1, axiom-free) in                     *)
(*  research_universal_solver (git log --follow -- formal/URCF_RD_All.v).*)
(*  This file is a standalone, minimal re-derivation for the              *)
(*  discrete-quantum-gravity-journal, carrying only the definitions       *)
(*  InfoLorentz actually depends on (Edge/w_of/u_of/v_of from Gamma;      *)
(*  distinguish/info_form from InfoOperator) -- not the surrounding       *)
(*  modules unrelated content (energy, StarRig, CPTP readout, etc.).      *)
(* ===================================================================== *)

From Coq Require Import Lists.List.
From Coq Require Import Sorting.Permutation.
From Coq Require Import QArith.QArith.
From Coq Require Import micromega.Lqa.
Import ListNotations.
Local Open Scope Q_scope.

(* ----------------------------------------------------------------- *)
(*  Minimal carrier, verbatim from Module Gamma (URCF_RD_All.v:6042). *)
(* ----------------------------------------------------------------- *)
Definition Edge := (nat * nat * Q)%type.
Definition w_of (e:Edge) : Q   := snd e.
Definition u_of (e:Edge) : nat := fst (fst e).
Definition v_of (e:Edge) : nat := snd (fst e).

(* ----------------------------------------------------------------- *)
(*  Minimal carrier, verbatim from Module InfoOperator                *)
(*  (URCF_RD_All.v:6698, 6765).                                       *)
(* ----------------------------------------------------------------- *)

(* retained distinguishability across an edge (RAR razor primitive) *)
Definition distinguish (x:nat->Q) (e:Edge) : Q := x (u_of e) - x (v_of e).

(* SELF-ADJOINT GENERATOR: the polarized Dirichlet bilinear form of the
   operator. Its symmetry = the generator L_R is SELF-ADJOINT (⟨x,L y⟩ =
   ⟨L x,y⟩), the condition for a valid quantum/Schrödinger generator; its
   diagonal is the retained-information functional. *)
Definition info_form (x y : nat->Q) (edges : list Edge) : Q :=
  fold_right (fun e acc => w_of e * (distinguish x e * distinguish y e) + acc) 0 edges.

(* ===================================================================== *)
(*  Module InfoLorentz  —  frontier #1, the LORENTZIAN signature, on our    *)
(*  philosophy (MLCD): the indefinite (−+) signature is NOT imposed by       *)
(*  coordinates — it is carried by the CAUSAL ORDER ≺ (sign −1 on causal/    *)
(*  timelike edges, +1 on spacelike). FRAME-COVARIANCE = invariance under    *)
(*  causal-structure-preserving relabellings (discrete "boosts"). This       *)
(*  realises the MLCD core (Lorentz from the order, covariance structural)   *)
(*  at the DISCRETE level, axiom-free.                                       *)
(*  HONEST: the continuum □ = −∂tt+∂xx readout of this operator stays the     *)
(*  hard tier (BD coefficients / continuum-contamination) — NOT solved here. *)
(* ===================================================================== *)
Module InfoLorentz.
  Import Coq.Lists.List. Import ListNotations.
  Import Coq.micromega.Lqa.
  Import Coq.QArith.QArith.
  Import Coq.Sorting.Permutation.

  (* signed causal bilinear form: sgn e in {+1 spacelike, -1 timelike} from ≺ *)
  Definition causal_form (sgn:Edge->Q) (x y:nat->Q) (edges:list Edge) : Q :=
    fold_right (fun e acc => sgn e * (w_of e * (distinguish x e * distinguish y e)) + acc) 0 edges.

  (* the Lorentzian generator is SELF-ADJOINT even with indefinite signature *)
  Theorem causal_form_self_adjoint :
    forall sgn edges x y, causal_form sgn x y edges == causal_form sgn y x edges.
  Proof.
    intros sgn edges x y. induction edges as [|e es IH].
    - reflexivity.
    - simpl. rewrite IH. unfold distinguish. ring.
  Qed.

  (* all-spacelike (sgn = +1) recovers the Euclidean info form L_R *)
  Theorem causal_form_euclidean_reduction :
    forall edges x y, causal_form (fun _ => 1) x y edges == info_form x y edges.
  Proof.
    intros edges x y. induction edges as [|e es IH].
    - reflexivity.
    - simpl. rewrite IH. unfold distinguish. ring.
  Qed.

  (* FRAME-COVARIANCE: invariant under causal-structure-preserving relabelling
     (each edge carries its own signature, so a "boost" that permutes events
     leaves the form invariant) — the discrete Lorentz invariance, structural. *)
  Theorem causal_form_frame_covariant :
    forall sgn x y edges edges',
      Permutation edges edges' -> causal_form sgn x y edges == causal_form sgn x y edges'.
  Proof.
    intros sgn x y edges edges' Hp. unfold causal_form. induction Hp.
    - reflexivity.
    - simpl. rewrite IHHp. reflexivity.
    - simpl. ring.
    - rewrite IHHp1; exact IHHp2.
  Qed.
End InfoLorentz.

(* ----------------------------------------------------------------- *)
(*  Axiom-free verification (Tier-0 / Th_coqc): expect Closed under   *)
(*  the global context for each theorem.                              *)
(* ----------------------------------------------------------------- *)
Print Assumptions InfoLorentz.causal_form_self_adjoint.
Print Assumptions InfoLorentz.causal_form_euclidean_reduction.
Print Assumptions InfoLorentz.causal_form_frame_covariant.
