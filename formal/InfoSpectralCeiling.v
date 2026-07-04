(* ===================================================================== *)
(*  RDL_SpectralCeiling.v                                                  *)
(*  SPECTRAL CEILING of the graph quadratic form from the DEGREE BOUND,    *)
(*  entirely over Q (no reals, no square roots, no eigenvalue theory).     *)
(*                                                                         *)
(*  CLAIMED HERE (candidate for coqc 8.18.0, axiom-free target):           *)
(*    deg_node_swap        sum over edges of endpoint squares              *)
(*                         = sum over nodes of deg(i) * x_i^2              *)
(*                         (the exact double-counting identity)            *)
(*    form_degree_bound    x^T L x  <=  2 * dmax * ||x||^2                 *)
(*                         (Rayleigh-quotient form of the Gershgorin       *)
(*                          bound lam_max <= 2*deg_max, WITHOUT invoking   *)
(*                          any eigen-theory: pure sum manipulation)       *)
(*    rayleigh_nonneg      any exact Rayleigh pair has  0 <= lam           *)
(*    rayleigh_ceiling     any exact Rayleigh pair has  lam <= 2*dmax      *)
(*    mode_product_ceiling M*omsq == K*lam  ==>  M*omsq <= K*(2*dmax)      *)
(*                         (product form; division-free ceiling on the    *)
(*                          squared spectral parameter)                    *)
(*    step_ratio_window    M*a == h*h*K*lam  and  h*h*K*(2*dmax) <= 4*M    *)
(*                         ==>  0 <= a <= 4                                *)
(*                         (the dimensionless step ratio lands in the     *)
(*                          boundedness window of RDL_RecurrenceEnergy.v)  *)
(*                                                                         *)
(*  An eigenpair is taken EXTENSIONALLY as a hypothesis                    *)
(*      form E x == lam * norm2 n x ,  0 < norm2 n x                       *)
(*  so no spectral theorem is needed or smuggled in.                       *)
(*                                                                         *)
(*  Pre-verified numerically (exact rationals, 200 random graphs) before   *)
(*  authoring.  Expected: Print Assumptions => Closed under the global     *)
(*  context (no funext / no classical / no admit).                         *)
(* ===================================================================== *)

Require Coq.Arith.PeanoNat.
Require Coq.Lists.List.
Require Coq.QArith.QArith.
Require Coq.micromega.Lia.
Require Coq.micromega.Lqa.

Module SpectralCeiling.

Import Coq.Lists.List. Import ListNotations.
Import Coq.Arith.PeanoNat.
Import Coq.QArith.QArith.
Import Coq.micromega.Lia.
Import Coq.micromega.Lqa.
Local Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(* Graph data: an edge is an ordered pair of node indices.             *)
(* ------------------------------------------------------------------ *)

Definition Edge : Type := (nat * nat)%type.

(* indicator:  ind u i = 1 if u = i else 0 *)
Definition ind (u i : nat) : Q := if Nat.eqb u i then 1 else 0.

(* how many endpoints of edge e touch node i (0, 1, or 2) *)
Definition share (e : Edge) (i : nat) : Q := ind (fst e) i + ind (snd e) i.

(* unweighted degree of node i *)
Definition deg (E : list Edge) (i : nat) : Q :=
  fold_right (fun e acc => share e i + acc) 0 E.

(* finite sums *)
Fixpoint qsum (n : nat) (f : nat -> Q) : Q :=
  match n with
  | O => 0
  | S m => qsum m f + f m
  end.

Definition esum (E : list Edge) (g : Edge -> Q) : Q :=
  fold_right (fun e acc => g e + acc) 0 E.

(* edge difference, quadratic form of the graph Laplacian, squared norm *)
Definition ediff (x : nat -> Q) (e : Edge) : Q := x (fst e) - x (snd e).

Definition form (E : list Edge) (x : nat -> Q) : Q :=
  esum E (fun e => ediff x e * ediff x e).

Definition norm2 (n : nat) (x : nat -> Q) : Q :=
  qsum n (fun i => x i * x i).

(* all edge endpoints live below n *)
Definition nodes_ok (n : nat) (E : list Edge) : Prop :=
  forall e, In e E -> (fst e < n)%nat /\ (snd e < n)%nat.

(* ------------------------------------------------------------------ *)
(* Elementary facts                                                    *)
(* ------------------------------------------------------------------ *)

Lemma sq_nonneg : forall q : Q, 0 <= q * q.
Proof.
  intro q. destruct (Qlt_le_dec q 0) as [Hneg | Hpos].
  - setoid_replace (q * q) with ((- q) * (- q)) by ring.
    apply Qmult_le_0_compat; lra.
  - apply Qmult_le_0_compat; lra.
Qed.

Lemma edge_sq_bound : forall A B : Q,
  (A - B) * (A - B) <= 2 * (A * A) + 2 * (B * B).
Proof.
  intros A B.
  assert (H : 2 * (A * A) + 2 * (B * B) - (A - B) * (A - B)
              == (A + B) * (A + B)) by ring.
  assert (H0 := sq_nonneg (A + B)). lra.
Qed.

(* ------------------------------------------------------------------ *)
(* qsum toolbox                                                        *)
(* ------------------------------------------------------------------ *)

Lemma qsum_ext : forall n (f g : nat -> Q),
  (forall i, (i < n)%nat -> f i == g i) ->
  qsum n f == qsum n g.
Proof.
  induction n as [| m IH]; intros f g H; simpl.
  - reflexivity.
  - rewrite (IH f g); [| intros i Hi; apply H; lia].
    rewrite (H m); [reflexivity | lia].
Qed.

Lemma qsum_zero : forall n, qsum n (fun _ => 0) == 0.
Proof.
  induction n as [| m IH]; simpl; [reflexivity | rewrite IH; ring].
Qed.

Lemma qsum_plus : forall n (f g : nat -> Q),
  qsum n (fun i => f i + g i) == qsum n f + qsum n g.
Proof.
  induction n as [| m IH]; intros f g; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

Lemma qsum_scale : forall n (c : Q) (f : nat -> Q),
  qsum n (fun i => c * f i) == c * qsum n f.
Proof.
  induction n as [| m IH]; intros c f; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

Lemma qsum_le : forall n (f g : nat -> Q),
  (forall i, (i < n)%nat -> f i <= g i) ->
  qsum n f <= qsum n g.
Proof.
  induction n as [| m IH]; intros f g H; simpl.
  - lra.
  - apply Qplus_le_compat.
    + apply IH. intros i Hi. apply H. lia.
    + apply H. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* esum toolbox                                                        *)
(* ------------------------------------------------------------------ *)

Lemma esum_ext : forall E (f g : Edge -> Q),
  (forall e, In e E -> f e == g e) ->
  esum E f == esum E g.
Proof.
  induction E as [| e r IH]; intros f g H; simpl.
  - reflexivity.
  - rewrite (H e); [| left; reflexivity].
    rewrite (IH f g); [reflexivity | intros e' He'; apply H; right; exact He'].
Qed.

Lemma esum_scale : forall E (c : Q) (g : Edge -> Q),
  esum E (fun e => c * g e) == c * esum E g.
Proof.
  induction E as [| e r IH]; intros c g; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

Lemma esum_le : forall E (f g : Edge -> Q),
  (forall e, In e E -> f e <= g e) ->
  esum E f <= esum E g.
Proof.
  induction E as [| e r IH]; intros f g H; simpl.
  - lra.
  - apply Qplus_le_compat.
    + apply H. left. reflexivity.
    + apply IH. intros e' He'. apply H. right. exact He'.
Qed.

Lemma esum_nonneg : forall E (g : Edge -> Q),
  (forall e, In e E -> 0 <= g e) ->
  0 <= esum E g.
Proof.
  induction E as [| e r IH]; intros g H; simpl.
  - lra.
  - assert (H1 : 0 <= g e) by (apply H; left; reflexivity).
    assert (H2 : 0 <= esum r g)
      by (apply IH; intros e' He'; apply H; right; exact He').
    lra.
Qed.

(* ------------------------------------------------------------------ *)
(* Indicator sums                                                      *)
(* ------------------------------------------------------------------ *)

Lemma isum_out : forall n u (g : nat -> Q),
  (n <= u)%nat ->
  qsum n (fun i => ind u i * g i) == 0.
Proof.
  induction n as [| m IH]; intros u g H; simpl.
  - reflexivity.
  - assert (Eq : Nat.eqb u m = false) by (apply Nat.eqb_neq; lia).
    unfold ind at 2. rewrite Eq.
    rewrite (IH u g); [ring | lia].
Qed.

Lemma isum_in : forall n u (g : nat -> Q),
  (u < n)%nat ->
  qsum n (fun i => ind u i * g i) == g u.
Proof.
  induction n as [| m IH]; intros u g H; simpl.
  - lia.
  - destruct (Nat.eq_dec u m) as [-> | Hne].
    + rewrite (isum_out m m g); [| lia].
      unfold ind at 1. rewrite Nat.eqb_refl. ring.
    + assert (Eq : Nat.eqb u m = false) by (apply Nat.eqb_neq; lia).
      unfold ind at 2. rewrite Eq.
      rewrite (IH u g); [ring | lia].
Qed.

Lemma share_sum : forall n (e : Edge) (g : nat -> Q),
  (fst e < n)%nat -> (snd e < n)%nat ->
  qsum n (fun i => share e i * g i) == g (fst e) + g (snd e).
Proof.
  intros n e g Hu Hv.
  rewrite (qsum_ext n (fun i => share e i * g i)
                      (fun i => ind (fst e) i * g i + ind (snd e) i * g i));
    [| intros i _; unfold share; ring].
  rewrite qsum_plus.
  rewrite (isum_in n (fst e) g Hu).
  rewrite (isum_in n (snd e) g Hv).
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* THE DOUBLE-COUNTING IDENTITY                                        *)
(*   sum_{e in E} ( x_{u(e)}^2 + x_{v(e)}^2 )                          *)
(*     = sum_{i < n}  deg(i) * x_i^2                                   *)
(* ------------------------------------------------------------------ *)

Lemma deg_node_swap : forall E n (x : nat -> Q),
  nodes_ok n E ->
  esum E (fun e => x (fst e) * x (fst e) + x (snd e) * x (snd e))
    == qsum n (fun i => deg E i * (x i * x i)).
Proof.
  induction E as [| e r IH]; intros n x Hok; simpl.
  - rewrite (qsum_ext n (fun i => deg [] i * (x i * x i)) (fun _ => 0));
      [rewrite qsum_zero; reflexivity |].
    intros i _. unfold deg. simpl. ring.
  - destruct (Hok e (or_introl eq_refl)) as [Hu Hv].
    rewrite (qsum_ext n (fun i => deg (e :: r) i * (x i * x i))
             (fun i => share e i * (x i * x i) + deg r i * (x i * x i)));
      [| intros i _; unfold deg; simpl; ring].
    rewrite qsum_plus.
    rewrite (share_sum n e (fun i => x i * x i) Hu Hv).
    rewrite <- (IH n x); [reflexivity |].
    intros e' He'. apply Hok. right. exact He'.
Qed.

(* ------------------------------------------------------------------ *)
(* Nonnegativity of the form and the norm                              *)
(* ------------------------------------------------------------------ *)

Theorem form_nonneg : forall E x, 0 <= form E x.
Proof.
  intros E x. unfold form.
  apply esum_nonneg. intros e _. apply sq_nonneg.
Qed.

Theorem norm2_nonneg : forall n x, 0 <= norm2 n x.
Proof.
  intros n x. unfold norm2.
  induction n as [| m IH]; simpl.
  - lra.
  - assert (H := sq_nonneg (x m)). lra.
Qed.

(* ------------------------------------------------------------------ *)
(* THE CEILING:  form E x <= (2*dmax) * norm2 n x                      *)
(* ------------------------------------------------------------------ *)

Theorem form_degree_bound : forall E n (x : nat -> Q) (dmax : Q),
  nodes_ok n E ->
  (forall i, (i < n)%nat -> deg E i <= dmax) ->
  form E x <= (2 * dmax) * norm2 n x.
Proof.
  intros E n x dmax Hok Hdeg.
  (* Step 1: per-edge bound  (xu - xv)^2 <= 2*xu^2 + 2*xv^2 *)
  assert (H1 : form E x
               <= esum E (fun e => 2 * (x (fst e) * x (fst e))
                                 + 2 * (x (snd e) * x (snd e)))).
  { unfold form. apply esum_le. intros e _. unfold ediff.
    apply edge_sq_bound. }
  (* Step 2: pull the 2 out *)
  assert (H2 : esum E (fun e => 2 * (x (fst e) * x (fst e))
                              + 2 * (x (snd e) * x (snd e)))
               == 2 * esum E (fun e => x (fst e) * x (fst e)
                                     + x (snd e) * x (snd e))).
  { rewrite <- esum_scale. apply esum_ext. intros e _. ring. }
  (* Step 3: double counting *)
  assert (H3 := deg_node_swap E n x Hok).
  (* Step 4: bound degrees by dmax *)
  assert (H4 : qsum n (fun i => deg E i * (x i * x i))
               <= qsum n (fun i => dmax * (x i * x i))).
  { apply qsum_le. intros i Hi.
    apply Qmult_le_compat_r; [apply Hdeg; exact Hi | apply sq_nonneg]. }
  (* Step 5: pull dmax out *)
  assert (H5 : qsum n (fun i => dmax * (x i * x i)) == dmax * norm2 n x).
  { unfold norm2. apply qsum_scale. }
  lra.
Qed.

(* ------------------------------------------------------------------ *)
(* Exact Rayleigh pairs land in [0, 2*dmax]                            *)
(* (an eigenpair of the Laplacian is a special case:                   *)
(*  L x = lam x  ==>  form = lam * norm2)                              *)
(* ------------------------------------------------------------------ *)

Theorem rayleigh_nonneg : forall E n x lam,
  form E x == lam * norm2 n x ->
  0 < norm2 n x ->
  0 <= lam.
Proof.
  intros E n x lam Heig HN.
  apply (proj1 (Qmult_le_r 0 lam (norm2 n x) HN)).
  assert (H := form_nonneg E x). lra.
Qed.

Theorem rayleigh_ceiling : forall E n x lam dmax,
  nodes_ok n E ->
  (forall i, (i < n)%nat -> deg E i <= dmax) ->
  form E x == lam * norm2 n x ->
  0 < norm2 n x ->
  lam <= 2 * dmax.
Proof.
  intros E n x lam dmax Hok Hdeg Heig HN.
  apply (proj1 (Qmult_le_r lam (2 * dmax) (norm2 n x) HN)).
  assert (Hb := form_degree_bound E n x dmax Hok Hdeg).
  lra.
Qed.

(* ------------------------------------------------------------------ *)
(* Product-form ceiling on the squared spectral parameter:             *)
(*   the relation M*omsq == K*lam plus lam <= 2*dmax yields a          *)
(*   division-free CEILING  M*omsq <= K*(2*dmax).                      *)
(*   (For M, K fixed this bounds omsq by a constant that depends       *)
(*    ONLY on the maximum degree of the graph — the spectrum of the    *)
(*    second-difference relation has a finite top.)                    *)
(* ------------------------------------------------------------------ *)

Theorem mode_product_ceiling : forall M K omsq lam dmax,
  0 <= K ->
  M * omsq == K * lam ->
  lam <= 2 * dmax ->
  M * omsq <= K * (2 * dmax).
Proof.
  intros M K omsq lam dmax HK Hd Hlam.
  assert (Hkl : lam * K <= (2 * dmax) * K)
    by (apply Qmult_le_compat_r; assumption).
  lra.
Qed.

(* ------------------------------------------------------------------ *)
(* Step-ratio window:                                                  *)
(*   if the dimensionless ratio a satisfies  M*a == h*h*K*lam  and     *)
(*   the degree-only condition  h*h*K*(2*dmax) <= 4*M  holds, then     *)
(*   0 <= a <= 4  — exactly the boundedness window of the two-step     *)
(*   recurrence in RDL_RecurrenceEnergy.v.  No spectrum needs to be    *)
(*   computed: max degree alone suffices.                              *)
(* ------------------------------------------------------------------ *)

Theorem step_ratio_window : forall M K h a lam dmax,
  0 < M ->
  0 <= h * h * K ->
  0 <= lam ->
  lam <= 2 * dmax ->
  M * a == h * h * K * lam ->
  h * h * K * (2 * dmax) <= 4 * M ->
  0 <= a /\ a <= 4.
Proof.
  intros M K h a lam dmax HM HhK Hlam0 Hlam Heq Hcfl.
  split.
  - apply (proj1 (Qmult_le_r 0 a M HM)).
    assert (H0 : 0 <= h * h * K * lam)
      by (apply Qmult_le_0_compat; assumption).
    lra.
  - apply (proj1 (Qmult_le_r a 4 M HM)).
    assert (Hstep : lam * (h * h * K) <= (2 * dmax) * (h * h * K))
      by (apply Qmult_le_compat_r; assumption).
    lra.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions deg_node_swap.
Print Assumptions form_degree_bound.
Print Assumptions rayleigh_nonneg.
Print Assumptions rayleigh_ceiling.
Print Assumptions mode_product_ceiling.
Print Assumptions step_ratio_window.

End SpectralCeiling.
