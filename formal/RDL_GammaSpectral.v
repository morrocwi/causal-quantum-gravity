(*
   RDL_GammaSpectral.v -- FULL EXTRACT (un-trimmed on 2026-07-06)
   Provenance: extracted from research_universal_solver/formal/RDL_GammaSpectral.v
   (axiom-free Th_coqc). Previously a trimmed extract (Edge + u_of/v_of/w_of
   only); RESTORED to full because the promoted InfoMetricIsEnergyReadout.v
   uses term/energy and their supporting lemmas. Superset of the prior trim,
   so all earlier downstream files still compile. stdlib-only; Th_coqc.
*)

(* ===================================================================== *)
(*  RDL_GammaSpectral.v                                                    *)
(*  SPOKE Γ (graph) of R^◇, + the AXIOM-FREE discrete core of the          *)
(*  continuum readout — all over ℚ, no analysis, no axioms.                *)
(*                                                                        *)
(*  (1) Γ : Dirichlet energy of a weighted graph (edge list) over ℚ        *)
(*      - energy_nonneg : nonneg weights ⇒ energy ≥ 0   (L_R PSD, Fiedler) *)
(*      - energy_edge_gauge : energy is INVARIANT under permuting/relabel- *)
(*        ing the edge multiset = the PGFT graph-gauge (Table 10:          *)
(*        relabel nodes must not change invariant graph readouts)          *)
(*  (2) discrete continuum precursor (the AXIOM-FREE half of L_R→−Δ_g):    *)
(*      - laplacian_stencil : the [1,−2,1] second difference IS the        *)
(*        discrete (negative) Laplacian                                    *)
(*      - secondDiff_quadratic : 2nd difference of a quadratic = 2a·h²      *)
(*        EXACTLY, every location x, every resolution h                    *)
(*      - secondDiff_readout_invariant : the scaled reading is the SAME at *)
(*        every resolution/location = the value 2a (=q'') disclosed at all *)
(*        resolutions — a READOUT-INVARIANT in the canon's exact sense     *)
(*        (like π across polygon resolutions), proven with NO division.    *)
(*  The TRUE limit h→0 for general smooth f is the readout-LIMIT — it      *)
(*  lives over the (axiomatic) reals, deliberately OUTSIDE this axiom-free *)
(*  core (see RDL_ContinuumReadout.v).   coqc 8.18.0.                      *)
(* ===================================================================== *)

Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Sorting.Permutation.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Open Scope Q_scope.

(* --- ℚ nonnegativity helpers --- *)
Lemma Qplus_nonneg : forall a b, 0 <= a -> 0 <= b -> 0 <= a + b.
Proof. intros; lra. Qed.
Lemma Qsq_nonneg : forall d, 0 <= d * d.
Proof. intro d; nra. Qed.
Lemma Qmul_nonneg : forall a b, 0 <= a -> 0 <= b -> 0 <= a * b.
Proof. intros; nra. Qed.

(* ===== (1) Γ : weighted-graph Dirichlet energy ===== *)
Definition Edge := (nat * nat * Q)%type.
Definition w_of (e:Edge) : Q   := snd e.
Definition u_of (e:Edge) : nat := fst (fst e).
Definition v_of (e:Edge) : nat := snd (fst e).

Definition term (x:nat->Q) (e:Edge) : Q :=
  w_of e * ((x (u_of e) - x (v_of e)) * (x (u_of e) - x (v_of e))).

Definition energy (edges:list Edge) (x:nat->Q) : Q :=
  fold_right (fun e acc => term x e + acc) 0 edges.

(* PSD : nonneg edge weights ⇒ Dirichlet energy ≥ 0  (the L_R ≽ 0 core) *)
Theorem energy_nonneg : forall edges x,
  (forall e, In e edges -> 0 <= w_of e) -> 0 <= energy edges x.
Proof.
  induction edges as [|e es IH]; intros x Hw.
  - simpl; lra.
  - simpl. apply Qplus_nonneg.
    + apply Qmul_nonneg.
      * apply Hw; left; reflexivity.
      * apply Qsq_nonneg.
    + apply IH. intros e' He'. apply Hw; right; exact He'.
Qed.

(* GRAPH-GAUGE (PGFT Table 10): permuting/relabeling the edge multiset     *)
(* leaves the invariant graph readout (energy) unchanged.                  *)
Theorem energy_edge_gauge : forall x edges edges',
  Permutation edges edges' -> energy edges x == energy edges' x.
Proof.
  intros x edges edges' Hp. unfold energy. induction Hp.
  - reflexivity.
  - simpl. rewrite IHHp. reflexivity.
  - simpl. ring.
  - rewrite IHHp1; exact IHHp2.
Qed.

Theorem energy_zero_edges : forall x, energy [] x == 0.
Proof. intro x; reflexivity. Qed.

(* ===== (2) discrete continuum precursor (axiom-free half of L_R→−Δ_g) ==== *)
Definition D2 (f:Q->Q) (x h:Q) : Q := f (x + h) - (2#1) * f x + f (x - h).
Definition quad (a b c:Q) : Q -> Q := fun t => a*t*t + b*t + c.

(* the [1,−2,1] stencil IS the discrete (negative) Laplacian *)
Theorem laplacian_stencil : forall f x h,
  D2 f x h == f (x - h) - (2#1) * f x + f (x + h).
Proof. intros; unfold D2; ring. Qed.

(* 2nd difference of a quadratic = 2a·h²  EXACTLY (all x, all h) *)
Theorem secondDiff_quadratic : forall a b c x h,
  D2 (quad a b c) x h == (2#1) * a * (h * h).
Proof. intros; unfold D2, quad; ring. Qed.

(* READOUT-INVARIANT : the scaled 2nd-difference reading is identical at    *)
(* every resolution h and location x — value 2a disclosed at ALL            *)
(* resolutions (NO division), exactly the π/φ readout-invariant pattern.    *)
Theorem secondDiff_readout_invariant : forall a b c x x' h h',
  D2 (quad a b c) x h * (h' * h') == D2 (quad a b c) x' h' * (h * h).
Proof. intros; unfold D2, quad; ring. Qed.

(* --------------------------------------------------------------------- *)
Print Assumptions energy_nonneg.
Print Assumptions energy_edge_gauge.
Print Assumptions laplacian_stencil.
Print Assumptions secondDiff_quadratic.
Print Assumptions secondDiff_readout_invariant.
