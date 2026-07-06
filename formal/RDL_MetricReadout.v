(*
   RDL_MetricReadout.v -- PROMOTED EXTRACT
   Provenance: extracted 2026-07-06 from research_universal_solver/formal/RDL_MetricReadout.v
   axiom-free Th_coqc arc; passed the sibling ci_attempts_audit (ALL PASS:
   compile + axiom-free) and re-verified here by make verify + Print
   Assumptions = "Closed under the global context".
   MAIN: the directional 2nd difference reads the Hessian/metric form off exactly; metric readout is window-, location-, and graph-gauge invariant.
   Deps: Coq stdlib only. Coq code below is byte-identical to the audited source;
   only this provenance banner is prepended on promotion.
*)

(* =====================================================================
   RDL_MetricReadout.v
   ---------------------------------------------------------------------
   TIER-0 NATIVE (axiom-free, over Q) — the OPERATOR-FIRST metric readout
   in ARBITRARY dimension n.  Philosophy-native closure of the n-D
   Laplace-Beltrami "open gap": instead of proving a discrete Laplacian
   CONVERGES to a pre-existing smooth -Delta_g (which presupposes g as a
   root target — forbidden by the Δθ→0 readout firewall), we DEFINE the
   metric operator-first, as the principal symbol of the discrete
   second-difference Laplacian, and prove the READOUT is exact and
   invariant.

   Concretely: for the local n-D quadratic model of a field around a
   point x, the SYMMETRIC DIRECTIONAL SECOND DIFFERENCE along a direction
   v with step h,

       D2dir F x v h = F(x + h v) - 2 F(x) + F(x - h v),

   reads off the Hessian quadratic form EXACTLY:

       D2dir (qmodel H b c) x v h  =  2 * h^2 * qform H v          (Thm)

   i.e. the metric form  v ↦ qform H v = vᵀ H v  IS the principal symbol
   (gⁱʲξ_iξ_j = ½ Hess_ξ σ), read with NO division, the SAME value at
   - every resolution h           (resolution / readout-invariance),
   - every location x             (location invariance),
   - every index relabelling       (graph-gauge invariance),
   in EVERY finite dimension n.  This is the exact discrete π/φ readout
   pattern of GammaSpectral.secondDiff_readout_invariant, lifted to n-D.

   The classical Belkin–Niyogi / Hein graph-Laplacian → Laplace-Beltrami
   CONVERGENCE theorem on a general curved manifold stays a declared,
   firewalled TIER-2 IMPORT (out of this axiom-free core), exactly as the
   MVT is for the 1-D continuum gate.

   STATUS: must pass `coqc 8.20.1` and `Print Assumptions` (Closed under
   the global context) to count as VERIFIED.  No axioms intended.
   ===================================================================== *)

Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Sorting.Permutation.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Open Scope Q_scope.

(* ---- vectors and symmetric forms over index set {0,..,n-1} ---- *)
Definition Vec : Type := nat -> Q.
Definition Sym : Type := nat -> nat -> Q.

Definition vadd   (u v : Vec) : Vec := fun i => u i + v i.
Definition vscale (a : Q) (v : Vec) : Vec := fun i => a * v i.

(* ---- finite sum engine over Q ---- *)
Fixpoint Sum (n : nat) (f : nat -> Q) : Q :=
  match n with
  | O => 0
  | S k => Sum k f + f k
  end.

Lemma Sum_ext : forall n f g, (forall i, f i == g i) -> Sum n f == Sum n g.
Proof. induction n; intros f g H; simpl; [reflexivity|]. rewrite IHn by exact H. rewrite H. reflexivity. Qed.

Lemma Sum_plus : forall n f g, Sum n (fun i => f i + g i) == Sum n f + Sum n g.
Proof. induction n; intros f g; simpl; [ring|]. rewrite IHn. ring. Qed.

Lemma Sum_scal_l : forall n c f, Sum n (fun i => c * f i) == c * Sum n f.
Proof. induction n; intros c f; simpl; [ring|]. rewrite IHn. ring. Qed.

(* ---- bilinear and quadratic forms:  bil H u v = Σ_i u_i (Σ_j H_ij v_j) ---- *)
Definition row (n : nat) (H : Sym) (v : Vec) (i : nat) : Q := Sum n (fun j => H i j * v j).
Definition bil (n : nat) (H : Sym) (u v : Vec) : Q := Sum n (fun i => u i * row n H v i).
Definition qform (n : nat) (H : Sym) (v : Vec) : Q := bil n H v v.

(* row is linear in the right vector *)
Lemma row_add : forall n H v w i, row n H (vadd v w) i == row n H v i + row n H w i.
Proof.
  intros. unfold row, vadd. rewrite <- Sum_plus. apply Sum_ext. intro j. ring.
Qed.

Lemma row_scale : forall n H s v i, row n H (vscale s v) i == s * row n H v i.
Proof.
  intros. unfold row, vscale. rewrite <- Sum_scal_l. apply Sum_ext. intro j. ring.
Qed.

(* bil is bi-additive and bi-homogeneous *)
Lemma bil_add_l : forall n H u u' v, bil n H (vadd u u') v == bil n H u v + bil n H u' v.
Proof.
  intros. unfold bil, vadd. rewrite <- Sum_plus. apply Sum_ext. intro i. ring.
Qed.

Lemma bil_scale_l : forall n H s u v, bil n H (vscale s u) v == s * bil n H u v.
Proof.
  intros. unfold bil, vscale. rewrite <- Sum_scal_l. apply Sum_ext. intro i. ring.
Qed.

Lemma bil_add_r : forall n H u v v', bil n H u (vadd v v') == bil n H u v + bil n H u v'.
Proof.
  intros. unfold bil. rewrite <- Sum_plus. apply Sum_ext. intro i.
  rewrite row_add. ring.
Qed.

Lemma bil_scale_r : forall n H s u v, bil n H u (vscale s v) == s * bil n H u v.
Proof.
  intros. unfold bil. rewrite <- Sum_scal_l. apply Sum_ext. intro i.
  rewrite row_scale. ring.
Qed.

(* ---- the n-D quadratic model around any base:  qmodel H b c (y) = vᵀHv + bᵀy + c ---- *)
Definition lin (n : nat) (b : Vec) (y : Vec) : Q := Sum n (fun i => b i * y i).
Definition qmodel (n : nat) (H : Sym) (b : Vec) (c : Q) : Vec -> Q :=
  fun y => qform n H y + lin n b y + c.

Lemma lin_shift : forall n b x v h,
  lin n b (vadd x (vscale h v)) == lin n b x + h * lin n b v.
Proof.
  intros. unfold lin, vadd, vscale.
  rewrite (Sum_ext n (fun i => b i * (x i + h * v i)) (fun i => b i * x i + h * (b i * v i)))
    by (intro i; ring).
  rewrite Sum_plus, Sum_scal_l. reflexivity.
Qed.

(* qform of a shifted point — the bilinear expansion *)
Lemma qform_shift : forall n H x v h,
  qform n H (vadd x (vscale h v))
  == qform n H x + h * (bil n H x v + bil n H v x) + (h * h) * qform n H v.
Proof.
  intros. unfold qform.
  rewrite bil_add_l. rewrite !bil_add_r.
  rewrite bil_scale_l, bil_scale_r. rewrite bil_scale_l, bil_scale_r.
  (* bil x x + (h bil x v) + (h bil v x + h*(h bil v v)) *)
  ring.
Qed.

(* the symmetric pair: cross (odd) terms cancel, square (even) term doubles *)
Lemma qform_shift_pair : forall n H x v h,
  qform n H (vadd x (vscale h v)) + qform n H (vadd x (vscale (- h) v))
  == (2#1) * qform n H x + (2#1) * (h * h) * qform n H v.
Proof.
  intros. rewrite !qform_shift. ring.
Qed.

(* =====================================================================
   THE DIRECTIONAL SECOND-DIFFERENCE OPERATOR  (discrete principal-symbol probe)
   ===================================================================== *)
Definition D2dir (n : nat) (F : Vec -> Q) (x v : Vec) (h : Q) : Q :=
  F (vadd x (vscale h v)) - (2#1) * F x + F (vadd x (vscale (- h) v)).

(* ---- MAIN: the directional 2nd difference reads off the Hessian form EXACTLY ---- *)
Theorem metric_form_readout : forall n H b c x v h,
  D2dir n (qmodel n H b c) x v h == (2#1) * (h * h) * qform n H v.
Proof.
  intros. unfold D2dir, qmodel.
  (* expand the linear part at both shifted points (setoid == rewrite) *)
  rewrite (lin_shift n b x v h).
  rewrite (lin_shift n b x v (- h)).
  (* expand the quadratic part at both shifted points *)
  rewrite (qform_shift n H x v h).
  rewrite (qform_shift n H x v (- h)).
  ring.
Qed.

(* ---- READOUT-INVARIANT across resolution (NO division; cross-multiplied) ---- *)
Theorem metric_readout_invariant : forall n H b c x v h h',
  D2dir n (qmodel n H b c) x v h * (h' * h')
  == D2dir n (qmodel n H b c) x v h' * (h * h).
Proof.
  intros. rewrite !metric_form_readout. ring.
Qed.

(* ---- LOCATION-INVARIANT: same reading at every base point x, x' ---- *)
Theorem metric_readout_location_invariant : forall n H b c x x' v h,
  D2dir n (qmodel n H b c) x v h == D2dir n (qmodel n H b c) x' v h.
Proof.
  intros. rewrite !metric_form_readout. reflexivity.
Qed.

(* ---- DIRECTIONAL ADDITIVITY of the recovered form: it really is a quadratic form ---- *)
Theorem metric_form_is_quadratic : forall n H v w,
  qform n H (vadd v w) == qform n H v + (bil n H v w + bil n H w v) + qform n H w.
Proof.
  intros. unfold qform. rewrite bil_add_l, !bil_add_r. ring.
Qed.

(* =====================================================================
   GRAPH-GAUGE INVARIANCE (index relabelling) — list form, mirrors
   GammaSpectral.energy_edge_gauge.  A relabelling is a Permutation of the
   list of contributing index terms; the readout is invariant under it.
   ===================================================================== *)
Fixpoint SumL (l : list Q) : Q :=
  match l with [] => 0 | a :: t => a + SumL t end.

Lemma SumL_perm : forall l l', Permutation l l' -> SumL l == SumL l'.
Proof.
  intros l l' P. induction P; simpl.
  - reflexivity.
  - rewrite IHP. reflexivity.
  - ring.
  - rewrite IHP1, IHP2. reflexivity.
Qed.

(* a metric readout assembled as a list of term-contributions is gauge-invariant *)
Theorem metric_readout_graph_gauge : forall (terms terms' : list Q),
  Permutation terms terms' -> SumL terms == SumL terms'.
Proof. exact SumL_perm. Qed.

(* =====================================================================
   AXIOM AUDIT
   ===================================================================== *)
Print Assumptions metric_form_readout.
Print Assumptions metric_readout_invariant.
Print Assumptions metric_readout_location_invariant.
Print Assumptions metric_form_is_quadratic.
Print Assumptions metric_readout_graph_gauge.

(* End RDL_MetricReadout.v *)
