(* ===================================================================== *)
(*  RDL_GraphNoether.v                                                     *)
(*  SYMMETRY ==> CONSERVED QUANTITY for the graph second-difference        *)
(*  recurrence, entirely over Q (no reals, no limits, no groups            *)
(*  imported).                                                             *)
(*                                                                         *)
(*  A symmetry is a node map  sg : nat -> nat  with three properties,      *)
(*  each stated in checkable finite form:                                  *)
(*    (i)   sg is injective;                                               *)
(*    (ii)  sg maps the stored edge list to a permutation of itself        *)
(*          (orientation-preserving automorphism);                         *)
(*    (iii) sg maps the node range 0..n-1 to a permutation of itself.     *)
(*                                                                         *)
(*  CLAIMED HERE (candidate for coqc 8.18.0, axiom-free target):           *)
(*    lap_equivariant     (L (x o sg)) i == (L x) (sg i)                   *)
(*                        — the operator commutes with the symmetry        *)
(*    gform_invariant     gform(x o sg, y o sg) == gform(x, y)             *)
(*    vdot_invariant      <v o sg, w o sg>     == <v, w>                   *)
(*    energy_invariant    Evec(p o sg, q o sg) == Evec(p, q)               *)
(*    W_antisym           the pairing W is antisymmetric                   *)
(*    noether_conserved   for the CONSERVATIVE step                        *)
(*                          M p'_i == 2M p_i - M q_i - h^2 K (L p)_i ,     *)
(*                        the quantity                                     *)
(*                          W(p,q) := sum_i ( p(sg i) q_i - p_i q(sg i) )  *)
(*                        satisfies  M * W(p',p) == M * W(p,q)  EXACTLY:   *)
(*                        one conserved quantity PER symmetry.             *)
(*                        The proof has exactly Noether's shape: the       *)
(*                        inertial terms cancel pointwise; the coupling    *)
(*                        term dies by equivariance + summation-by-parts   *)
(*                        (the symmetry of the coupling is precisely what  *)
(*                        kills the force contribution).                   *)
(*    c6_* / noether_c6   a CONCRETE instance: the 6-cycle with its        *)
(*                        rotation; all three hypotheses are proved for    *)
(*                        it, so the theorem set is non-vacuous.           *)
(*                                                                         *)
(*  HONESTLY NOT CLAIMED: the dissipative correction law for W (the       *)
(*  exact identity W picks up under c <> 0 — numerically W is NOT          *)
(*  conserved with dissipation, as expected), and orientation-REVERSING    *)
(*  automorphisms (hypothesis (ii) fixes the stored orientation; the       *)
(*  flip-invariance needed to relax this lives in                          *)
(*  RDL_CausalSignature.term_orientation_invariant style lemmas).          *)
(*                                                                         *)
(*  Pre-verified with exact rational arithmetic: conservation over         *)
(*  60-step orbits on the 6-cycle rotation and a star leaf-swap;           *)
(*  equivariance and both invariances on 200 random states; dissipation    *)
(*  confirmed to break conservation (so the hypothesis is sharp).          *)
(*  Expected: Print Assumptions => Closed under the global context.        *)
(* ===================================================================== *)

Require Coq.Arith.PeanoNat.
Require Coq.Bool.Bool.
Require Coq.Lists.List.
Require Coq.QArith.QArith.
Require Coq.Sorting.Permutation.
Require Coq.micromega.Lia.
Require Coq.micromega.Lqa.

Module GraphNoether.

Import Coq.Lists.List. Import ListNotations.
Import Coq.Arith.PeanoNat.
Import Coq.Bool.Bool.
Import Coq.QArith.QArith.
Import Coq.Sorting.Permutation.
Import Coq.micromega.Lia.
Import Coq.micromega.Lqa.
Local Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(* Graph data (shared conventions; self-contained for standalone coqc) *)
(* ------------------------------------------------------------------ *)

Definition Edge : Type := (nat * nat)%type.

Definition ind (u i : nat) : Q := if Nat.eqb u i then 1 else 0.

Fixpoint qsum (n : nat) (f : nat -> Q) : Q :=
  match n with
  | O => 0
  | S m => qsum m f + f m
  end.

Definition esum (E : list Edge) (g : Edge -> Q) : Q :=
  fold_right (fun e acc => g e + acc) 0 E.

Definition nsum (l : list nat) (f : nat -> Q) : Q :=
  fold_right (fun i acc => f i + acc) 0 l.

Definition ediff (x : nat -> Q) (e : Edge) : Q := x (fst e) - x (snd e).

(* named integrands so all rewriting stays first-order *)
Definition lint (x : nat -> Q) (i : nat) (e : Edge) : Q :=
  (ind (fst e) i - ind (snd e) i) * ediff x e.

Definition gint (x y : nat -> Q) (e : Edge) : Q := ediff x e * ediff y e.

Definition lap (E : list Edge) (x : nat -> Q) (i : nat) : Q :=
  esum E (lint x i).

Definition gform (E : list Edge) (x y : nat -> Q) : Q :=
  esum E (gint x y).

Definition vdot (n : nat) (v w : nat -> Q) : Q :=
  qsum n (fun i => v i * w i).

Definition nodes_ok (n : nat) (E : list Edge) : Prop :=
  forall e, In e E -> (fst e < n)%nat /\ (snd e < n)%nat.

(* image of an edge under a node map *)
Definition emap (sg : nat -> nat) (e : Edge) : Edge :=
  (sg (fst e), sg (snd e)).

(* ------------------------------------------------------------------ *)
(* qsum / esum toolbox                                                 *)
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
  induction n as [| m IH]; intros f g; simpl; [ring | rewrite IH; ring].
Qed.

Lemma qsum_sub : forall n (f g : nat -> Q),
  qsum n (fun i => f i - g i) == qsum n f - qsum n g.
Proof.
  induction n as [| m IH]; intros f g; simpl; [ring | rewrite IH; ring].
Qed.

Lemma qsum_scale : forall n (c : Q) (f : nat -> Q),
  qsum n (fun i => c * f i) == c * qsum n f.
Proof.
  induction n as [| m IH]; intros c f; simpl; [ring | rewrite IH; ring].
Qed.

Lemma esum_ext : forall E (f g : Edge -> Q),
  (forall e, In e E -> f e == g e) ->
  esum E f == esum E g.
Proof.
  induction E as [| e r IH]; intros f g H; simpl.
  - reflexivity.
  - rewrite (H e); [| left; reflexivity].
    rewrite (IH f g); [reflexivity | intros e' He'; apply H; right; exact He'].
Qed.

Lemma esum_precompose : forall E (t : Edge -> Edge) (g : Edge -> Q),
  esum E (fun e => g (t e)) == esum (map t E) g.
Proof.
  induction E as [| e r IH]; intros t g; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma esum_perm : forall (l l' : list Edge) (g : Edge -> Q),
  Permutation l l' -> esum l g == esum l' g.
Proof.
  intros l l' g HP. induction HP; simpl.
  - reflexivity.
  - rewrite IHHP. reflexivity.
  - ring.
  - rewrite IHHP1. exact IHHP2.
Qed.

Lemma nsum_precompose : forall (l : list nat) (t : nat -> nat) (f : nat -> Q),
  nsum l (fun i => f (t i)) == nsum (map t l) f.
Proof.
  induction l as [| a r IH]; intros t f; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma nsum_perm : forall (l l' : list nat) (f : nat -> Q),
  Permutation l l' -> nsum l f == nsum l' f.
Proof.
  intros l l' f HP. induction HP; simpl.
  - reflexivity.
  - rewrite IHHP. reflexivity.
  - ring.
  - rewrite IHHP1. exact IHHP2.
Qed.

Lemma nsum_app : forall (l1 l2 : list nat) (f : nat -> Q),
  nsum (l1 ++ l2) f == nsum l1 f + nsum l2 f.
Proof.
  induction l1 as [| a r IH]; intros l2 f; simpl; [ring | rewrite IH; ring].
Qed.

(* bridge: the range sum is the list sum over seq 0 n *)
Lemma nsum_single : forall a (f : nat -> Q), nsum (a :: nil) f == f a.
Proof. intros. simpl. ring. Qed.

Lemma qsum_nsum : forall n (f : nat -> Q),
  qsum n f == nsum (seq 0 n) f.
Proof.
  induction n as [| m IH]; intros f.
  - simpl. reflexivity.
  - rewrite seq_S. rewrite nsum_app.
    rewrite Nat.add_0_l. rewrite nsum_single.
    cbn [qsum]. rewrite IH. ring.
Qed.

(* reindexing a range sum along a map that permutes the range *)
Lemma qsum_reindex : forall n (sg : nat -> nat) (f : nat -> Q),
  Permutation (map sg (seq 0 n)) (seq 0 n) ->
  qsum n (fun i => f (sg i)) == qsum n f.
Proof.
  intros n sg f HP.
  rewrite (qsum_nsum n (fun i => f (sg i))).
  rewrite (qsum_nsum n f).
  rewrite (nsum_precompose (seq 0 n) sg f).
  apply nsum_perm. exact HP.
Qed.

(* the node map sends the range into the range *)
Lemma sigma_bound : forall n (sg : nat -> nat),
  Permutation (map sg (seq 0 n)) (seq 0 n) ->
  forall i, (i < n)%nat -> (sg i < n)%nat.
Proof.
  intros n sg HP i Hi.
  assert (Hin : In (sg i) (seq 0 n)).
  { apply (Permutation_in _ HP). apply in_map. apply in_seq. lia. }
  apply in_seq in Hin. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* isum + summation by parts (as in RDL_GraphFluxBalance.v)            *)
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

Lemma green_identity : forall E n (x y : nat -> Q),
  nodes_ok n E ->
  qsum n (fun i => y i * lap E x i) == gform E x y.
Proof.
  induction E as [| e r IH]; intros n x y Hok.
  - rewrite (qsum_ext n (fun i => y i * lap [] x i) (fun _ => 0));
      [rewrite qsum_zero |].
    + unfold gform. simpl. reflexivity.
    + intros i _. unfold lap. simpl. ring.
  - destruct (Hok e (or_introl eq_refl)) as [Hu Hv].
    rewrite (qsum_ext n (fun i => y i * lap (e :: r) x i)
             (fun i => (ind (fst e) i * (y i * ediff x e)
                        - ind (snd e) i * (y i * ediff x e))
                       + y i * lap r x i));
      [| intros i _; unfold lap, lint; simpl; ring].
    rewrite qsum_plus.
    rewrite qsum_sub.
    rewrite (isum_in n (fst e) (fun i => y i * ediff x e) Hu).
    rewrite (isum_in n (snd e) (fun i => y i * ediff x e) Hv).
    rewrite (IH n x y);
      [| intros e' He'; apply Hok; right; exact He'].
    unfold gform, gint. simpl. unfold ediff. ring.
Qed.

Lemma gform_sym : forall E x y, gform E x y == gform E y x.
Proof.
  intros E x y. unfold gform. apply esum_ext.
  intros e _. unfold gint. ring.
Qed.

(* ------------------------------------------------------------------ *)
(* EQUIVARIANCE:  L (x o sg) i  ==  (L x) (sg i)                       *)
(* ------------------------------------------------------------------ *)

Lemma ind_inj : forall (sg : nat -> nat),
  (forall a b : nat, sg a = sg b -> a = b) ->
  forall u i, ind (sg u) (sg i) == ind u i.
Proof.
  intros sg Hinj u i. unfold ind.
  destruct (Nat.eqb (sg u) (sg i)) eqn:H1;
  destruct (Nat.eqb u i) eqn:H2; try reflexivity.
  - apply Nat.eqb_eq in H1. apply Nat.eqb_neq in H2.
    exfalso. apply H2. apply Hinj. exact H1.
  - apply Nat.eqb_neq in H1. apply Nat.eqb_eq in H2.
    exfalso. apply H1. rewrite H2. reflexivity.
Qed.

Theorem lap_equivariant : forall E (sg : nat -> nat) (x : nat -> Q) (i : nat),
  (forall a b : nat, sg a = sg b -> a = b) ->
  Permutation (map (emap sg) E) E ->
  lap E (fun j => x (sg j)) i == lap E x (sg i).
Proof.
  intros E sg x i Hinj HPE.
  unfold lap.
  rewrite (esum_ext E (lint (fun j => x (sg j)) i)
                      (fun e => lint x (sg i) (emap sg e)));
    [| intros e _; unfold lint, emap, ediff; simpl;
       rewrite (ind_inj sg Hinj (fst e) i);
       rewrite (ind_inj sg Hinj (snd e) i);
       reflexivity].
  rewrite (esum_precompose E (emap sg) (lint x (sg i))).
  apply esum_perm. exact HPE.
Qed.

(* ------------------------------------------------------------------ *)
(* INVARIANCE of the quadratic structures                              *)
(* ------------------------------------------------------------------ *)

Theorem gform_invariant : forall E (sg : nat -> nat) (x y : nat -> Q),
  Permutation (map (emap sg) E) E ->
  gform E (fun j => x (sg j)) (fun j => y (sg j)) == gform E x y.
Proof.
  intros E sg x y HPE.
  unfold gform.
  rewrite (esum_ext E (gint (fun j => x (sg j)) (fun j => y (sg j)))
                      (fun e => gint x y (emap sg e)));
    [| intros e _; unfold gint, emap, ediff; simpl; reflexivity].
  rewrite (esum_precompose E (emap sg) (gint x y)).
  apply esum_perm. exact HPE.
Qed.

Theorem vdot_invariant : forall n (sg : nat -> nat) (v w : nat -> Q),
  Permutation (map sg (seq 0 n)) (seq 0 n) ->
  vdot n (fun j => v (sg j)) (fun j => w (sg j)) == vdot n v w.
Proof.
  intros n sg v w HPn.
  unfold vdot.
  exact (qsum_reindex n sg (fun i => v i * w i) HPn).
Qed.

Definition Evec (M h K : Q) (E : list Edge) (n : nat) (p q : nat -> Q) : Q :=
  M * qsum n (fun i => (p i - q i) * (p i - q i)) + (h * h * K) * gform E p q.

Theorem energy_invariant : forall E n (sg : nat -> nat) (p q : nat -> Q) (M h K : Q),
  Permutation (map (emap sg) E) E ->
  Permutation (map sg (seq 0 n)) (seq 0 n) ->
  Evec M h K E n (fun j => p (sg j)) (fun j => q (sg j)) == Evec M h K E n p q.
Proof.
  intros E n sg p q M h K HPE HPn.
  unfold Evec.
  assert (K1 : qsum n (fun i => (p (sg i) - q (sg i)) * (p (sg i) - q (sg i)))
             == qsum n (fun i => (p i - q i) * (p i - q i)))
    by (exact (qsum_reindex n sg (fun i => (p i - q i) * (p i - q i)) HPn)).
  assert (K2 := gform_invariant E sg p q HPE).
  rewrite K1, K2. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* THE CONSERVED PAIRING                                               *)
(* ------------------------------------------------------------------ *)

Definition Wq (n : nat) (sg : nat -> nat) (p q : nat -> Q) : Q :=
  qsum n (fun i => p (sg i) * q i - p i * q (sg i)).

Theorem W_antisym : forall n sg (p q : nat -> Q),
  Wq n sg p q + Wq n sg q p == 0.
Proof.
  intros n sg p q. unfold Wq.
  rewrite <- (qsum_plus n (fun i => p (sg i) * q i - p i * q (sg i))
                          (fun i => q (sg i) * p i - q i * p (sg i))).
  rewrite (qsum_ext n (fun i => (p (sg i) * q i - p i * q (sg i))
                              + (q (sg i) * p i - q i * p (sg i)))
                      (fun _ => 0));
    [apply qsum_zero | intros i _; ring].
Qed.

(* ------------------------------------------------------------------ *)
(* THE NOETHER THEOREM: one conserved quantity per symmetry.           *)
(*   step:  M p'_i == 2M p_i - M q_i - h^2 K (L p)_i   (conservative)  *)
(*   then:  M * Wq(p', p) == M * Wq(p, q)              (exact)         *)
(* ------------------------------------------------------------------ *)

Theorem noether_conserved :
  forall E n (sg : nat -> nat) (p q p' : nat -> Q) (M h K : Q),
  (forall a b : nat, sg a = sg b -> a = b) ->
  Permutation (map (emap sg) E) E ->
  Permutation (map sg (seq 0 n)) (seq 0 n) ->
  nodes_ok n E ->
  (forall i, (i < n)%nat ->
     M * p' i == 2 * M * p i - M * q i - (h * h * K) * lap E p i) ->
  M * Wq n sg p' p == M * Wq n sg p q.
Proof.
  intros E n sg p q p' M h K Hinj HPE HPn Hok Hstep.
  (* A: pull M inside the sum *)
  assert (HA : M * Wq n sg p' p
             == qsum n (fun i => (M * p' (sg i)) * p i
                                - (M * p' i) * p (sg i))).
  { unfold Wq.
    rewrite <- (qsum_scale n M
      (fun i => p' (sg i) * p i - p' i * p (sg i))).
    apply qsum_ext. intros i _. ring. }
  (* B: substitute the step at i and at sg i; move lap through sg *)
  assert (HB : qsum n (fun i => (M * p' (sg i)) * p i
                              - (M * p' i) * p (sg i))
             == qsum n (fun i =>
      (2 * M * p (sg i) - M * q (sg i)
         - (h * h * K) * lap E (fun j => p (sg j)) i) * p i
    - (2 * M * p i - M * q i - (h * h * K) * lap E p i) * p (sg i))).
  { apply qsum_ext. intros i Hi.
    assert (Hsb : (sg i < n)%nat) by (apply (sigma_bound n sg HPn); exact Hi).
    assert (E1 : M * p' (sg i)
               == 2 * M * p (sg i) - M * q (sg i)
                  - (h * h * K) * lap E p (sg i))
      by (apply Hstep; exact Hsb).
    assert (E2 : M * p' i
               == 2 * M * p i - M * q i - (h * h * K) * lap E p i)
      by (apply Hstep; exact Hi).
    assert (Heq : lap E (fun j => p (sg j)) i == lap E p (sg i))
      by (apply lap_equivariant; assumption).
    rewrite E1, E2, Heq. reflexivity. }
  (* C: split into inertial + Noether + coupling pieces *)
  assert (HC : qsum n (fun i =>
      (2 * M * p (sg i) - M * q (sg i)
         - (h * h * K) * lap E (fun j => p (sg j)) i) * p i
    - (2 * M * p i - M * q i - (h * h * K) * lap E p i) * p (sg i))
    == qsum n (fun i => 2 * M * (p (sg i) * p i - p i * p (sg i)))
     + (qsum n (fun i => (- M) * (q (sg i) * p i - q i * p (sg i)))
        + qsum n (fun i => (- (h * h * K))
            * (p i * lap E (fun j => p (sg j)) i
               - p (sg i) * lap E p i)))).
  { rewrite <- (qsum_plus n
      (fun i => (- M) * (q (sg i) * p i - q i * p (sg i)))
      (fun i => (- (h * h * K))
          * (p i * lap E (fun j => p (sg j)) i - p (sg i) * lap E p i))).
    rewrite <- (qsum_plus n
      (fun i => 2 * M * (p (sg i) * p i - p i * p (sg i)))
      (fun i => (- M) * (q (sg i) * p i - q i * p (sg i))
              + (- (h * h * K))
                * (p i * lap E (fun j => p (sg j)) i
                   - p (sg i) * lap E p i))).
    apply qsum_ext. intros i _. ring. }
  (* D1: the inertial piece vanishes pointwise *)
  assert (HD1 : qsum n (fun i => 2 * M * (p (sg i) * p i - p i * p (sg i)))
              == 0).
  { rewrite (qsum_ext n
      (fun i => 2 * M * (p (sg i) * p i - p i * p (sg i)))
      (fun _ => 0)); [apply qsum_zero | intros i _; ring]. }
  (* D2: the Noether piece *)
  assert (HD2 : qsum n (fun i => (- M) * (q (sg i) * p i - q i * p (sg i)))
              == (- M) * Wq n sg q p).
  { unfold Wq. apply qsum_scale. }
  (* D3: the coupling piece dies by equivariance + summation by parts *)
  assert (HD3 : qsum n (fun i => (- (h * h * K))
                  * (p i * lap E (fun j => p (sg j)) i
                     - p (sg i) * lap E p i)) == 0).
  { rewrite (qsum_scale n (- (h * h * K))
      (fun i => p i * lap E (fun j => p (sg j)) i - p (sg i) * lap E p i)).
    assert (Hin : qsum n (fun i => p i * lap E (fun j => p (sg j)) i
                                 - p (sg i) * lap E p i) == 0).
    { rewrite (qsum_sub n
        (fun i => p i * lap E (fun j => p (sg j)) i)
        (fun i => p (sg i) * lap E p i)).
      rewrite (green_identity E n (fun j => p (sg j)) p Hok).
      rewrite (qsum_ext n (fun i => p (sg i) * lap E p i)
                          (fun i => (fun j => p (sg j)) i * lap E p i));
        [| intros i _; reflexivity].
      rewrite (green_identity E n p (fun j => p (sg j)) Hok).
      rewrite (gform_sym E p (fun j => p (sg j))).
      ring. }
    rewrite Hin. ring. }
  (* E: assemble, then close with antisymmetry *)
  assert (Hqp : Wq n sg q p == - Wq n sg p q).
  { assert (Ha := W_antisym n sg p q). lra. }
  assert (Hm : (- M) * Wq n sg q p == (- M) * (- Wq n sg p q))
    by (rewrite Hqp; reflexivity).
  lra.
Qed.

(* ------------------------------------------------------------------ *)
(* CONCRETE INSTANCE: the 6-cycle with its rotation.  All three        *)
(* hypotheses are PROVED (injectivity, edge permutation, node          *)
(* permutation), so the Noether theorem above is non-vacuous.          *)
(* ------------------------------------------------------------------ *)

(* rotation of 0..5, identity elsewhere: globally injective *)
Definition rot6 (i : nat) : nat :=
  if (i <? 5)%nat then S i else if (i =? 5)%nat then 0%nat else i.

Definition C6 : list Edge :=
  (0%nat, 1%nat) :: (1%nat, 2%nat) :: (2%nat, 3%nat)
  :: (3%nat, 4%nat) :: (4%nat, 5%nat) :: (5%nat, 0%nat) :: nil.

Lemma rot6_inj : forall a b : nat, rot6 a = rot6 b -> a = b.
Proof.
  intros a b H. unfold rot6 in H.
  destruct (a <? 5)%nat eqn:Ha1; destruct (b <? 5)%nat eqn:Hb1;
  destruct (a =? 5)%nat eqn:Ha2; destruct (b =? 5)%nat eqn:Hb2;
  repeat match goal with
  | Hx : (_ <? _)%nat = true  |- _ => apply Nat.ltb_lt in Hx
  | Hx : (_ <? _)%nat = false |- _ => apply Nat.ltb_ge in Hx
  | Hx : (_ =? _)%nat = true  |- _ => apply Nat.eqb_eq in Hx
  | Hx : (_ =? _)%nat = false |- _ => apply Nat.eqb_neq in Hx
  end; lia.
Qed.

Lemma c6_edge_perm : Permutation (map (emap rot6) C6) C6.
Proof.
  simpl.
  change (Permutation
    (((1%nat,2%nat) :: (2%nat,3%nat) :: (3%nat,4%nat)
      :: (4%nat,5%nat) :: (5%nat,0%nat) :: nil) ++ ((0%nat,1%nat) :: nil))
    (((0%nat,1%nat) :: nil) ++ ((1%nat,2%nat) :: (2%nat,3%nat)
      :: (3%nat,4%nat) :: (4%nat,5%nat) :: (5%nat,0%nat) :: nil))).
  apply Permutation_app_comm.
Qed.

Lemma c6_node_perm : Permutation (map rot6 (seq 0 6)) (seq 0 6).
Proof.
  simpl.
  change (Permutation
    ((1 :: 2 :: 3 :: 4 :: 5 :: nil)%nat ++ (0 :: nil)%nat)
    ((0 :: nil)%nat ++ (1 :: 2 :: 3 :: 4 :: 5 :: nil)%nat)).
  apply Permutation_app_comm.
Qed.

Lemma c6_nodes_ok : nodes_ok 6 C6.
Proof.
  intros e He. unfold C6 in He. simpl in He.
  repeat (destruct He as [He | He]; [subst; simpl; split; lia |]).
  contradiction.
Qed.

(* the rotation's conserved quantity on the 6-cycle *)
Corollary noether_c6 :
  forall (p q p' : nat -> Q) (M h K : Q),
  (forall i, (i < 6)%nat ->
     M * p' i == 2 * M * p i - M * q i - (h * h * K) * lap C6 p i) ->
  M * Wq 6 rot6 p' p == M * Wq 6 rot6 p q.
Proof.
  intros p q p' M h K Hstep.
  apply (noether_conserved C6 6 rot6 p q p' M h K
           rot6_inj c6_edge_perm c6_node_perm c6_nodes_ok Hstep).
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions lap_equivariant.
Print Assumptions gform_invariant.
Print Assumptions vdot_invariant.
Print Assumptions energy_invariant.
Print Assumptions W_antisym.
Print Assumptions noether_conserved.
Print Assumptions noether_c6.

End GraphNoether.
