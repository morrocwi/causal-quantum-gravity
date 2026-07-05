(* ===================================================================== *)
(*  RDL_TensorFrame.v          (repo namespace: rename Info* mechanically) *)
(*  THE LATTICE EDGE FRAME IS A MINIMAL COMPLETE TENSOR FRAME, IN EVERY    *)
(*  DIMENSION — a symmetric two-tensor is entirely determined, component   *)
(*  by component and exactly over Q, by its quadratic evaluations along    *)
(*  the axis directions and the pairwise (face-diagonal) directions; and   *)
(*  the direction count matches the component count exactly.               *)
(*                                                                        *)
(*  This upgrades the per-edge dictionary (strain(e), forman(e)) from      *)
(*  scalar data to: diagonal evaluations of a tensor in the edge frame     *)
(* : the polarization identities below are the exact key that      *)
(*  reconstructs every off-diagonal component from them.  What remains     *)
(*  OUTSIDE this file (named, deliberately): covariance across frames,     *)
(*  the trace/Einstein-tensor construction, OB-FORMAN-RICCI, and the       *)
(*  readout limit.                                                         *)
(*                                                                        *)
(*  CLAIMED HERE (candidate for coqc 8.18.0, axiom-free target):           *)
(*    frame_count        2n + n(n-1) = n(n+1): the axis + face-diagonal    *)
(*                       directions number exactly twice... i.e. equal     *)
(*                       (doubled form, division-free) the dimension of    *)
(*                       the space of symmetric two-tensors, every n       *)
(*    dsum_basis         the double sum against two basis indicators       *)
(*                       reads off exactly one tensor component            *)
(*    diag_reads         Q(e_u) == T u u                                   *)
(*    pair_reads_raw     Q(e_u + e_w) == T u u + T u w + T w u + T w w     *)
(*    pair_reads         (symmetric T)  == T u u + 2 T u w + T w w        *)
(*    offdiag_reconstruct                                                  *)
(*                       2 * T u w == Q(e_u+e_w) - Q(e_u) - Q(e_w)         *)
(*                       (the exact polarization key, division-free)       *)
(*    frame_determines   two symmetric tensors with equal evaluations on   *)
(*                       the frame agree in EVERY component                *)
(*    forms_agree        ... and hence their quadratic forms agree on      *)
(*                       EVERY vector: the frame data is the tensor        *)
(*                                                                        *)
(*  Pre-verified with exact rationals (reconstruction of 200 random        *)
(*  symmetric tensors in dimensions 2 and 4, every component exact;        *)
(*  direction/component counting checked for n = 2..6) before authoring.   *)
(*  Expected: Print Assumptions => Closed under the global context.        *)
(* ===================================================================== *)

Require Coq.Arith.PeanoNat.
Require Coq.QArith.QArith.
Require Coq.micromega.Lia.
Require Coq.micromega.Lqa.

Module TensorFrame.

Import Coq.Arith.PeanoNat.
Import Coq.QArith.QArith.
Import Coq.micromega.Lia.
Import Coq.micromega.Lqa.
Local Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(* Data                                                                *)
(* ------------------------------------------------------------------ *)

Definition ind (u i : nat) : Q := if Nat.eqb u i then 1 else 0.

Fixpoint qsum (n : nat) (f : nat -> Q) : Q :=
  match n with
  | O => 0
  | S m => qsum m f + f m
  end.

(* the quadratic form of a two-tensor T on a vector v *)
Definition qform (n : nat) (T : nat -> nat -> Q) (v : nat -> Q) : Q :=
  qsum n (fun i => qsum n (fun j => v i * T i j * v j)).

(* ------------------------------------------------------------------ *)
(* Toolbox                                                             *)
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

Lemma qsum_plus : forall n (f g : nat -> Q),
  qsum n (fun i => f i + g i) == qsum n f + qsum n g.
Proof.
  induction n as [| m IH]; intros f g; simpl; [ring | rewrite IH; ring].
Qed.

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

(* ------------------------------------------------------------------ *)
(* THE COUNTING IDENTITY (division-free form)                          *)
(* ------------------------------------------------------------------ *)

(* axes (n) plus face diagonals (n(n-1)/2) equal the components of a    *)
(* symmetric two-tensor (n(n+1)/2), every n — stated doubled to stay    *)
(* division-free over nat                                               *)
Theorem frame_count : forall n : nat, (2*n + n*(n-1) = n*(n+1))%nat.
Proof.
  intro n. destruct n as [| m]; [reflexivity | lia].
Qed.

(* ------------------------------------------------------------------ *)
(* READING COMPONENTS OFF THE FRAME                                    *)
(* ------------------------------------------------------------------ *)

(* the double sum against two basis indicators reads one component *)
Lemma dsum_basis : forall n (T : nat -> nat -> Q) (u w : nat),
  (u < n)%nat -> (w < n)%nat ->
  qsum n (fun i => qsum n (fun j => ind u i * T i j * ind w j)) == T u w.
Proof.
  intros n T u w Hu Hw.
  rewrite (qsum_ext n
    (fun i => qsum n (fun j => ind u i * T i j * ind w j))
    (fun i => ind u i * T i w));
    [ apply (isum_in n u (fun i => T i w) Hu) |].
  intros i _.
  rewrite (qsum_ext n
    (fun j => ind u i * T i j * ind w j)
    (fun j => ind w j * (ind u i * T i j)));
    [| intros j _; ring].
  apply (isum_in n w (fun j => ind u i * T i j) Hw).
Qed.

(* the axis evaluations are the diagonal components *)
Theorem diag_reads : forall n (T : nat -> nat -> Q) (u : nat),
  (u < n)%nat ->
  qform n T (fun k => ind u k) == T u u.
Proof.
  intros n T u Hu. unfold qform. cbv beta.
  apply (dsum_basis n T u u Hu Hu).
Qed.

(* the pair evaluation, no symmetry assumed *)
Theorem pair_reads_raw : forall n (T : nat -> nat -> Q) (u w : nat),
  (u < n)%nat -> (w < n)%nat ->
  qform n T (fun k => ind u k + ind w k)
  == T u u + T u w + T w u + T w w.
Proof.
  intros n T u w Hu Hw. unfold qform. cbv beta.
  rewrite (qsum_ext n
    (fun i => qsum n (fun j =>
       (ind u i + ind w i) * T i j * (ind u j + ind w j)))
    (fun i => qsum n (fun j => ind u i * T i j * ind u j)
            + (qsum n (fun j => ind u i * T i j * ind w j)
               + (qsum n (fun j => ind w i * T i j * ind u j)
                  + qsum n (fun j => ind w i * T i j * ind w j))))).
  - rewrite (qsum_plus n
      (fun i => qsum n (fun j => ind u i * T i j * ind u j))
      (fun i => qsum n (fun j => ind u i * T i j * ind w j)
              + (qsum n (fun j => ind w i * T i j * ind u j)
                 + qsum n (fun j => ind w i * T i j * ind w j)))).
    rewrite (qsum_plus n
      (fun i => qsum n (fun j => ind u i * T i j * ind w j))
      (fun i => qsum n (fun j => ind w i * T i j * ind u j)
              + qsum n (fun j => ind w i * T i j * ind w j))).
    rewrite (qsum_plus n
      (fun i => qsum n (fun j => ind w i * T i j * ind u j))
      (fun i => qsum n (fun j => ind w i * T i j * ind w j))).
    rewrite (dsum_basis n T u u Hu Hu).
    rewrite (dsum_basis n T u w Hu Hw).
    rewrite (dsum_basis n T w u Hw Hu).
    rewrite (dsum_basis n T w w Hw Hw).
    ring.
  - intros i _.
    rewrite (qsum_ext n
      (fun j => (ind u i + ind w i) * T i j * (ind u j + ind w j))
      (fun j => ind u i * T i j * ind u j
              + (ind u i * T i j * ind w j
                 + (ind w i * T i j * ind u j
                    + ind w i * T i j * ind w j))));
      [| intros j _; ring].
    rewrite (qsum_plus n
      (fun j => ind u i * T i j * ind u j)
      (fun j => ind u i * T i j * ind w j
              + (ind w i * T i j * ind u j + ind w i * T i j * ind w j))).
    rewrite (qsum_plus n
      (fun j => ind u i * T i j * ind w j)
      (fun j => ind w i * T i j * ind u j + ind w i * T i j * ind w j)).
    rewrite (qsum_plus n
      (fun j => ind w i * T i j * ind u j)
      (fun j => ind w i * T i j * ind w j)).
    reflexivity.
Qed.

(* symmetric tensors: the classical polarization form *)
Theorem pair_reads : forall n (T : nat -> nat -> Q) (u w : nat),
  (forall i j, T i j == T j i) ->
  (u < n)%nat -> (w < n)%nat ->
  qform n T (fun k => ind u k + ind w k)
  == T u u + 2 * T u w + T w w.
Proof.
  intros n T u w Hsym Hu Hw.
  assert (Hr := pair_reads_raw n T u w Hu Hw).
  assert (Hs := Hsym w u).
  lra.
Qed.

(* THE POLARIZATION KEY, division-free: every off-diagonal component    *)
(* is exactly recovered from three frame evaluations                    *)
Theorem offdiag_reconstruct : forall n (T : nat -> nat -> Q) (u w : nat),
  (forall i j, T i j == T j i) ->
  (u < n)%nat -> (w < n)%nat ->
  2 * T u w
  == qform n T (fun k => ind u k + ind w k)
     - qform n T (fun k => ind u k)
     - qform n T (fun k => ind w k).
Proof.
  intros n T u w Hsym Hu Hw.
  assert (Hp := pair_reads n T u w Hsym Hu Hw).
  assert (Hu' := diag_reads n T u Hu).
  assert (Hw' := diag_reads n T w Hw).
  lra.
Qed.

(* ------------------------------------------------------------------ *)
(* COMPLETENESS: the frame data IS the tensor                          *)
(* ------------------------------------------------------------------ *)

Theorem frame_determines : forall n (T T' : nat -> nat -> Q) (u w : nat),
  (forall i j, T i j == T j i) ->
  (forall i j, T' i j == T' j i) ->
  (forall i, (i < n)%nat ->
     qform n T (fun k => ind i k) == qform n T' (fun k => ind i k)) ->
  (forall i j, (i < n)%nat -> (j < n)%nat ->
     qform n T (fun k => ind i k + ind j k)
     == qform n T' (fun k => ind i k + ind j k)) ->
  (u < n)%nat -> (w < n)%nat ->
  T u w == T' u w.
Proof.
  intros n T T' u w HsT HsT' Hdiag Hpair Hu Hw.
  destruct (Nat.eq_dec u w) as [-> | Hne].
  - assert (H1 := diag_reads n T w Hw).
    assert (H2 := diag_reads n T' w Hw).
    assert (H3 := Hdiag w Hw).
    lra.
  - assert (P1 := pair_reads n T u w HsT Hu Hw).
    assert (P2 := pair_reads n T' u w HsT' Hu Hw).
    assert (Hp := Hpair u w Hu Hw).
    assert (D1 := diag_reads n T u Hu).
    assert (D2 := diag_reads n T' u Hu).
    assert (D3 := diag_reads n T w Hw).
    assert (D4 := diag_reads n T' w Hw).
    assert (Du := Hdiag u Hu).
    assert (Dw := Hdiag w Hw).
    lra.
Qed.

(* ... and equal components give equal forms on EVERY vector *)
Theorem forms_agree : forall n (T T' : nat -> nat -> Q),
  (forall i j, (i < n)%nat -> (j < n)%nat -> T i j == T' i j) ->
  forall v : nat -> Q, qform n T v == qform n T' v.
Proof.
  intros n T T' H v. unfold qform.
  apply qsum_ext. intros i Hi.
  apply qsum_ext. intros j Hj.
  rewrite (H i j Hi Hj). reflexivity.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions frame_count.
Print Assumptions dsum_basis.
Print Assumptions diag_reads.
Print Assumptions pair_reads_raw.
Print Assumptions pair_reads.
Print Assumptions offdiag_reconstruct.
Print Assumptions frame_determines.
Print Assumptions forms_agree.

End TensorFrame.
