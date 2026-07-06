(*
   InfoMetricIsEnergyReadout.v -- PROMOTED EXTRACT
   Provenance: extracted 2026-07-06 from research_universal_solver/formal/InfoMetricIsEnergyReadout_attempt.v
   axiom-free Th_coqc arc; passed the sibling ci_attempts_audit (ALL PASS:
   compile + axiom-free) and re-verified here by make verify + Print
   Assumptions = "Closed under the global context".
   MAIN: the graph metric IS an energy readout -- the same L_R data, read as curvature/metric, equals the mother equation energy form.
   Deps: RDL_MetricReadout, RDL_GammaSpectral (trimmed extract). Coq code below is byte-identical to the audited source;
   only this provenance banner is prepended on promotion.
*)

(******************************************************************************)
(* InfoMetricIsEnergyReadout_attempt.v -- EXPLORATORY, single-attempt file    *)
(*  (not part of the build, not wired into any aggregate). Standalone (no -R  *)
(*  flag needed, matching the other _attempt.v files), but genuinely BRIDGES *)
(*  two pre-existing, independently-verified 'islands' of this repo rather    *)
(*  than adding new isolated math.                                          *)
(*                                                                            *)
(* MOTIVATION: docs/root/math/INFO_OPERATOR_PLAN.md explicitly flags          *)
(*  formal/RDL_MetricReadout.v, formal/RDL_GammaSpectral.v, formal/RDL_DtN.v, *)
(*  formal/RDL_LaplaceBeltrami.v as ISOLATED ISLANDS -- 'none imports the     *)
(*  others or connects to the unified... operator' -- and names the missing  *)
(*  'MetricReadout is a readout of the information operator I' theorem as    *)
(*  the specific still-unwritten Phase-1 bridge. This file writes exactly    *)
(*  that bridge for the two most directly connectable islands:                *)
(*   - RDL_GammaSpectral.energy: the WEIGHTED-GRAPH Dirichlet form, built     *)
(*     from an edge list (u,v,w) -> w*(x_u-x_v)^2, summed -- this repo's      *)
(*     existing 'energy = information' readout (InfoOperator.                *)
(*     info_is_operator_energy elsewhere in the aggregate uses the same       *)
(*     shape).                                                               *)
(*   - RDL_MetricReadout.qform: the MATRIX-QUADRATIC-FORM metric/Hessian      *)
(*     readout v |-> v^T H v, proven to be exactly what the discrete          *)
(*     directional second-difference D2dir reads off (metric_form_readout).  *)
(*  The classical graph-theory fact connecting them -- that the WEIGHTED      *)
(*  GRAPH LAPLACIAN's quadratic form equals the Dirichlet energy EXACTLY,     *)
(*  x^T L x = sum_edges w(x_u-x_v)^2 -- has NOT, before this file, been       *)
(*  stated or proved anywhere in this repo's Coq. Once proved, it says:       *)
(*  the 'metric' (qform, hence the Hessian/curvature reading via              *)
(*  metric_form_readout) IS, for the graph-Laplacian case, literally the same *)
(*  quantity as the Dirichlet energy readout -- i.e. GEOMETRY IS A READOUT    *)
(*  OF RETAINED INFORMATION (energy), not a separately-postulated structure.  *)
(*                                                                            *)
(* RESULT (self-checked numerically in Python with exact fractions across 10  *)
(*  random (n, edge-list, x) instances, including zero-edge and multi-edge/   *)
(*  parallel-edge cases, before this proof was attempted -- confirmed        *)
(*  qform(L,x) == energy(edges,x) EXACTLY, no factor-of-2 discrepancy):       *)
(*   qform n (L edges) x == energy edges x                                   *)
(*  for L edges built as the standard graph Laplacian matrix (diagonal =      *)
(*  weighted degree, off-diagonal = -w for each edge), given every edge's     *)
(*  endpoints are < n and distinct (no self-loops -- a self-loop contributes  *)
(*  0 to energy trivially, so excluding it costs nothing).                   *)
(*                                                                            *)
(* SCOPE -- read before trusting this as more than it is: (1) this connects   *)
(*  two EXISTING, already-proven, axiom-free discrete modules -- it does NOT  *)
(*  touch or extend the continuum/+reals gaps (RDL_MetricReadoutLimit.v,      *)
(*  RDL_MetricReadoutRate.v, InfoAnalysisLift.v) or the still-genuinely-open  *)
(*  items (full DtN interior invertibility, the real Bianchi-identity proof,  *)
(*  Raychaudhuri, Friedmann -- all untouched, all still [Open] exactly as     *)
(*  before). (2) does not modify RDL_MetricReadout.v or RDL_GammaSpectral.v   *)
(*  themselves (both Required, neither edited -- no axiom-profile drift on    *)
(*  either). (3) says nothing about real particle mass ratios; engine.       *)
(*  lexicon.stance_for('mass') remains [Open].                               *)
(******************************************************************************)

Require RDL_MetricReadout.
Require RDL_GammaSpectral.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Require Import Lia.
Open Scope Q_scope.

Module InfoMetricIsEnergyReadout.
  Import RDL_MetricReadout.
  Import RDL_GammaSpectral.

  (* ---- a finite-sum "extract two nonzero terms" toolkit, needed to reduce
     the matrix-quadratic-form Sum down to just the two indices an edge
     touches. Not present in either island file, so built here. ---- *)
  Lemma Sum_peel_zero_tail : forall n m f,
    (m <= n)%nat -> (forall i, (m <= i)%nat -> (i < n)%nat -> f i == 0) ->
    Sum n f == Sum m f.
  Proof.
    induction n as [|n IH]; intros m f Hmn Hz.
    - assert (m = 0)%nat by lia. subst. reflexivity.
    - destruct (Nat.eq_dec m (S n)) as [Heq|Hne].
      + subst. reflexivity.
      + assert (Hmn' : (m <= n)%nat) by lia.
        simpl. rewrite (IH m f Hmn') by (intros i Hi1 Hi2; apply Hz; lia).
        rewrite (Hz n) by lia. ring.
  Qed.

  Lemma Sum_one_term : forall n a f,
    (a < n)%nat -> (forall i, (i < n)%nat -> i <> a -> f i == 0) -> Sum n f == f a.
  Proof.
    intros n a f Ha Hz.
    rewrite (Sum_peel_zero_tail n (S a) f) by (try lia; intros i Hi1 Hi2; apply Hz; lia).
    simpl. rewrite (Sum_peel_zero_tail a 0 f) by (try lia; intros i Hi1 Hi2; apply Hz; lia).
    simpl. ring.
  Qed.

  Lemma Sum_two_terms_ordered : forall n a b f,
    (a < b)%nat -> (b < n)%nat ->
    (forall i, (i < n)%nat -> i <> a -> i <> b -> f i == 0) -> Sum n f == f a + f b.
  Proof.
    intros n a b f Hab Hbn Hz.
    rewrite (Sum_peel_zero_tail n (S b) f) by (try lia; intros i Hi1 Hi2; apply Hz; lia).
    simpl. rewrite (Sum_one_term b a f) by (try lia; intros i Hi1 Hi2; apply Hz; lia).
    ring.
  Qed.

  Lemma Sum_two_terms : forall n f a b,
    (a < n)%nat -> (b < n)%nat -> a <> b ->
    (forall i, (i < n)%nat -> i <> a -> i <> b -> f i == 0) -> Sum n f == f a + f b.
  Proof.
    intros n f a b Ha Hb Hab Hz.
    destruct (lt_eq_lt_dec a b) as [[Hlt|Heq]|Hgt].
    - apply Sum_two_terms_ordered; assumption.
    - contradiction.
    - rewrite (Sum_two_terms_ordered n b a f Hgt Ha) by (intros i Hi1 Hi2 Hi3; apply Hz; lia). ring.
  Qed.

  (* ---- the graph Laplacian, built from RDL_GammaSpectral's own Edge type ---- *)
  Definition Ledge (e : Edge) (i j : nat) : Q :=
    if andb (Nat.eqb i (u_of e)) (Nat.eqb j (u_of e)) then w_of e
    else if andb (Nat.eqb i (v_of e)) (Nat.eqb j (v_of e)) then w_of e
    else if andb (Nat.eqb i (u_of e)) (Nat.eqb j (v_of e)) then - w_of e
    else if andb (Nat.eqb i (v_of e)) (Nat.eqb j (u_of e)) then - w_of e
    else 0.

  Definition L (edges : list Edge) : Sym :=
    fun i j => fold_right (fun e acc => Ledge e i j + acc) 0 edges.

  Lemma Ledge_uu : forall e, Ledge e (u_of e) (u_of e) == w_of e.
  Proof. intro e. unfold Ledge. rewrite !Nat.eqb_refl. reflexivity. Qed.

  Lemma Ledge_uv : forall e, u_of e <> v_of e -> Ledge e (u_of e) (v_of e) == - w_of e.
  Proof.
    intros e Hne. unfold Ledge.
    rewrite Nat.eqb_refl.
    rewrite (proj2 (Nat.eqb_neq (v_of e) (u_of e)) (not_eq_sym Hne)). simpl.
    rewrite (proj2 (Nat.eqb_neq (u_of e) (v_of e)) Hne). simpl.
    rewrite Nat.eqb_refl. reflexivity.
  Qed.

  Lemma Ledge_vu : forall e, u_of e <> v_of e -> Ledge e (v_of e) (u_of e) == - w_of e.
  Proof.
    intros e Hne. unfold Ledge.
    rewrite (proj2 (Nat.eqb_neq (v_of e) (u_of e)) (not_eq_sym Hne)). simpl.
    rewrite Nat.eqb_refl.
    rewrite (proj2 (Nat.eqb_neq (u_of e) (v_of e)) Hne). simpl.
    rewrite Nat.eqb_refl. reflexivity.
  Qed.

  Lemma Ledge_vv : forall e, u_of e <> v_of e -> Ledge e (v_of e) (v_of e) == w_of e.
  Proof.
    intros e Hne. unfold Ledge.
    rewrite (proj2 (Nat.eqb_neq (v_of e) (u_of e)) (not_eq_sym Hne)). simpl.
    rewrite Nat.eqb_refl. reflexivity.
  Qed.

  Lemma Ledge_zero_col : forall e k i, i <> u_of e -> i <> v_of e -> Ledge e k i == 0.
  Proof.
    intros e k i Hiu Hiv. unfold Ledge.
    rewrite (proj2 (Nat.eqb_neq i (u_of e)) Hiu).
    rewrite (proj2 (Nat.eqb_neq i (v_of e)) Hiv).
    rewrite !Bool.andb_false_r. reflexivity.
  Qed.

  Lemma row_u : forall n e x, (u_of e < n)%nat -> (v_of e < n)%nat -> u_of e <> v_of e ->
    row n (Ledge e) x (u_of e) == w_of e * (x (u_of e) - x (v_of e)).
  Proof.
    intros n e x Hu Hv Hne. unfold row.
    rewrite (Sum_two_terms n (fun j => Ledge e (u_of e) j * x j) (u_of e) (v_of e) Hu Hv Hne).
    - rewrite Ledge_uu, (Ledge_uv e Hne). ring.
    - intros i Hi Hia Hib. rewrite (Ledge_zero_col e (u_of e) i Hia Hib). ring.
  Qed.

  Lemma row_v : forall n e x, (u_of e < n)%nat -> (v_of e < n)%nat -> u_of e <> v_of e ->
    row n (Ledge e) x (v_of e) == - w_of e * (x (u_of e) - x (v_of e)).
  Proof.
    intros n e x Hu Hv Hne. unfold row.
    rewrite (Sum_two_terms n (fun j => Ledge e (v_of e) j * x j) (u_of e) (v_of e) Hu Hv Hne).
    - rewrite (Ledge_vu e Hne), (Ledge_vv e Hne). ring.
    - intros i Hi Hia Hib. rewrite (Ledge_zero_col e (v_of e) i Hia Hib). ring.
  Qed.

  Lemma row_other : forall n e x i,
    (forall k, Ledge e i k == 0) -> row n (Ledge e) x i == 0.
  Proof.
    intros n e x i Hz. unfold row.
    rewrite (Sum_ext n (fun j => Ledge e i j * x j) (fun j => 0)) by (intro j; rewrite Hz; ring).
    induction n as [|n IH]; simpl; [reflexivity | rewrite IH; ring].
  Qed.

  Lemma Ledge_zero_row : forall e i, i <> u_of e -> i <> v_of e -> forall k, Ledge e i k == 0.
  Proof.
    intros e i Hiu Hiv k. unfold Ledge.
    rewrite (proj2 (Nat.eqb_neq i (u_of e)) Hiu).
    rewrite (proj2 (Nat.eqb_neq i (v_of e)) Hiv).
    reflexivity.
  Qed.

  (* single-edge case: qform of the single-edge Laplacian equals that edge's
     Dirichlet term EXACTLY (no factor of 2 -- verified numerically first). *)
  Lemma qform_single_edge : forall n e x,
    (u_of e < n)%nat -> (v_of e < n)%nat -> u_of e <> v_of e ->
    qform n (Ledge e) x == term x e.
  Proof.
    intros n e x Hu Hv Hne.
    unfold qform, bil.
    rewrite (Sum_two_terms n (fun i => x i * row n (Ledge e) x i) (u_of e) (v_of e) Hu Hv Hne).
    - rewrite (row_u n e x Hu Hv Hne), (row_v n e x Hu Hv Hne).
      unfold term. ring.
    - intros i Hi Hia Hib.
      rewrite (row_other n e x i (Ledge_zero_row e i Hia Hib)). ring.
  Qed.

  (* additivity of qform under pointwise addition of the matrix argument *)
  Lemma row_pointwise_add : forall n H1 H2 v i,
    row n (fun a b => H1 a b + H2 a b) v i == row n H1 v i + row n H2 v i.
  Proof. intros. unfold row. rewrite <- Sum_plus. apply Sum_ext. intro j. ring. Qed.

  Lemma qform_pointwise_add : forall n H1 H2 x,
    qform n (fun a b => H1 a b + H2 a b) x == qform n H1 x + qform n H2 x.
  Proof.
    intros. unfold qform, bil. rewrite <- Sum_plus. apply Sum_ext. intro i.
    rewrite row_pointwise_add. ring.
  Qed.

  (* MAIN THEOREM: the graph-Laplacian quadratic form IS the Dirichlet
     energy, exactly -- by induction on the edge list, mirroring `energy`'s
     own fold_right structure. This is the "MetricReadout is a readout of
     the information operator" bridge INFO_OPERATOR_PLAN.md names as
     missing: the metric/Hessian form (qform, hence D2dir via
     metric_form_readout) and the energy readout (energy, hence
     InfoOperator.info_is_operator_energy's info(x)=<x,L_R x> elsewhere in
     the aggregate) are the SAME quantity for the graph-Laplacian case. *)
  Lemma Sum_zero_const : forall n, Sum n (fun _ => 0) == 0.
  Proof. induction n; simpl; [reflexivity | rewrite IHn; ring]. Qed.

  Theorem metric_form_is_energy_readout : forall n edges x,
    (forall e, In e edges -> (u_of e < n)%nat /\ (v_of e < n)%nat /\ u_of e <> v_of e) ->
    qform n (L edges) x == energy edges x.
  Proof.
    intros n edges x.
    induction edges as [| e edges IH]; intro Hwf.
    - unfold qform, bil, row, L. simpl.
      rewrite (Sum_ext n (fun i => x i * Sum n (fun j => 0 * x j)) (fun i => 0)).
      + apply Sum_zero_const.
      + intro i.
        rewrite (Sum_ext n (fun j => 0 * x j) (fun j => 0)) by (intro j; ring).
        rewrite Sum_zero_const. ring.
    - assert (He : (u_of e < n)%nat /\ (v_of e < n)%nat /\ u_of e <> v_of e)
        by (apply Hwf; left; reflexivity).
      destruct He as [Hu [Hv Hne]].
      assert (Hwf' : forall e', In e' edges -> (u_of e' < n)%nat /\ (v_of e' < n)%nat /\ u_of e' <> v_of e')
        by (intros e' He'; apply Hwf; right; exact He').
      assert (HL : forall i j, L (e :: edges) i j == Ledge e i j + L edges i j)
        by (intros i j; unfold L; reflexivity).
      assert (Hqext : qform n (L (e :: edges)) x == qform n (fun i j => Ledge e i j + L edges i j) x).
      { unfold qform, bil. apply Sum_ext. intro i. unfold row.
        rewrite (Sum_ext n (fun j => L (e::edges) i j * x j) (fun j => (Ledge e i j + L edges i j) * x j))
          by (intro j; rewrite HL; ring).
        reflexivity. }
      assert (Hqadd : qform n (L (e :: edges)) x == qform n (Ledge e) x + qform n (L edges) x)
        by (rewrite Hqext; apply qform_pointwise_add).
      rewrite Hqadd.
      rewrite (qform_single_edge n e x Hu Hv Hne).
      rewrite (IH Hwf').
      simpl. reflexivity.
  Qed.

  Print Assumptions metric_form_is_energy_readout.

End InfoMetricIsEnergyReadout.

(* PRIMARY TARGET: InfoMetricIsEnergyReadout.metric_form_is_energy_readout --
   proves the graph-Laplacian quadratic form (RDL_MetricReadout.qform) equals
   the Dirichlet-energy readout (RDL_GammaSpectral.energy) exactly, bridging
   two previously-isolated repo modules exactly as
   docs/root/math/INFO_OPERATOR_PLAN.md's still-unwritten "MetricReadout is a
   readout of I" Phase-1 theorem names. As documented above: does not touch
   the +reals-tier limit/rate files, does not close the genuinely open GR
   items (Bianchi proof, Raychaudhuri, Friedmann, DtN interior
   invertibility); says nothing about real particle mass ratios. *)
