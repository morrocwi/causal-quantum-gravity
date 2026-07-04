(* ===================================================================== *)
(*  RDL_CompanionSkew.v                                                    *)
(*  FIRST-ORDER COMPANION STRUCTURE of the graph second-difference         *)
(*  relation, entirely over Q (no reals, no division, no complex           *)
(*  numbers, no limits).                                                   *)
(*                                                                         *)
(*  The pair (x, v) carries the second-order relation as a first-order     *)
(*  system.  The M-SCALED generator                                        *)
(*      B (x, v)  :=  ( M*v ,  - K * (L x) )                               *)
(*  avoids all division (scaling a generator by a scalar preserves         *)
(*  skewness).  The energy pairing is                                      *)
(*      <(x,v),(y,w)>_E  :=  K * gform(x,y)  +  M * <v,w> .                *)
(*                                                                         *)
(*  CLAIMED HERE (candidate for coqc 8.18.0, axiom-free target):           *)
(*    Einner_sym          the energy pairing is symmetric                  *)
(*    Einner_nonneg       0 <= K, 0 <= M  ==>  the pairing is positive     *)
(*                        semidefinite on the diagonal                     *)
(*    companion_skew      <B(x,v),(y,w)>_E == - <(x,v),B(y,w)>_E           *)
(*                        (the generator is SKEW-ADJOINT for the energy    *)
(*                         pairing; the proof runs through the             *)
(*                         summation-by-parts identity, re-proved here     *)
(*                         so the file checks standalone)                  *)
(*    companion_energy_orthogonal                                          *)
(*                        <B(x,v),(x,v)>_E == 0                            *)
(*                        (the generator moves every state ORTHOGONALLY    *)
(*                         to the energy level set — the division-free,    *)
(*                         limit-free algebraic core of norm-preserving    *)
(*                         first-order evolution.  The discrete-time       *)
(*                         counterpart is RDL_GraphFluxBalance.            *)
(*                         flux_balance_conserved; the modal counterpart   *)
(*                         is RDL_RecurrenceEnergy.Qf_step_invariant.)     *)
(*                                                                         *)
(*  Pre-verified with exact rational arithmetic on 300 random graphs       *)
(*  and signed random M, K (skewness and orthogonality hold with NO        *)
(*  sign conditions; only the semidefiniteness needs 0 <= M, 0 <= K).      *)
(*  Expected: Print Assumptions => Closed under the global context.        *)
(* ===================================================================== *)

Require Coq.Arith.PeanoNat.
Require Coq.Lists.List.
Require Coq.QArith.QArith.
Require Coq.micromega.Lia.
Require Coq.micromega.Lqa.

Module CompanionSkew.

Import Coq.Lists.List. Import ListNotations.
Import Coq.Arith.PeanoNat.
Import Coq.QArith.QArith.
Import Coq.micromega.Lia.
Import Coq.micromega.Lqa.
Local Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(* Graph data (conventions of RDL_SpectralCeiling.v /                  *)
(* RDL_GraphFluxBalance.v; self-contained for standalone coqc).        *)
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

Definition ediff (x : nat -> Q) (e : Edge) : Q := x (fst e) - x (snd e).

Definition divg (E : list Edge) (g : Edge -> Q) (i : nat) : Q :=
  esum E (fun e => (ind (fst e) i - ind (snd e) i) * g e).

Definition lap (E : list Edge) (x : nat -> Q) (i : nat) : Q :=
  divg E (ediff x) i.

Definition gform (E : list Edge) (x y : nat -> Q) : Q :=
  esum E (fun e => ediff x e * ediff y e).

Definition vdot (n : nat) (v w : nat -> Q) : Q :=
  qsum n (fun i => v i * w i).

Definition nodes_ok (n : nat) (E : list Edge) : Prop :=
  forall e, In e E -> (fst e < n)%nat /\ (snd e < n)%nat.

(* ------------------------------------------------------------------ *)
(* Toolbox                                                             *)
(* ------------------------------------------------------------------ *)

Lemma sq_nonneg : forall q : Q, 0 <= q * q.
Proof.
  intro q. destruct (Qlt_le_dec q 0) as [Hneg | Hpos].
  - setoid_replace (q * q) with ((- q) * (- q)) by ring.
    apply Qmult_le_0_compat; lra.
  - apply Qmult_le_0_compat; lra.
Qed.

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

Lemma qsum_nonneg : forall n (f : nat -> Q),
  (forall i, (i < n)%nat -> 0 <= f i) ->
  0 <= qsum n f.
Proof.
  induction n as [| m IH]; intros f H; simpl.
  - lra.
  - assert (H1 : 0 <= qsum m f) by (apply IH; intros i Hi; apply H; lia).
    assert (H2 : 0 <= f m) by (apply H; lia).
    lra.
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

Lemma esum_scale : forall E (c : Q) (g : Edge -> Q),
  esum E (fun e => c * g e) == c * esum E g.
Proof.
  induction E as [| e r IH]; intros c g; simpl; [ring | rewrite IH; ring].
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

(* summation by parts (as in RDL_GraphFluxBalance.v) *)
Lemma green_identity : forall E n (x y : nat -> Q),
  nodes_ok n E ->
  qsum n (fun i => y i * lap E x i) == gform E x y.
Proof.
  induction E as [| e r IH]; intros n x y Hok.
  - rewrite (qsum_ext n (fun i => y i * lap [] x i) (fun _ => 0));
      [rewrite qsum_zero |].
    + unfold gform. simpl. reflexivity.
    + intros i _. unfold lap, divg. simpl. ring.
  - destruct (Hok e (or_introl eq_refl)) as [Hu Hv].
    rewrite (qsum_ext n (fun i => y i * lap (e :: r) x i)
             (fun i => (ind (fst e) i * (y i * ediff x e)
                        - ind (snd e) i * (y i * ediff x e))
                       + y i * lap r x i));
      [| intros i _; unfold lap, divg; simpl; ring].
    rewrite qsum_plus.
    rewrite qsum_sub.
    rewrite (isum_in n (fst e) (fun i => y i * ediff x e) Hu).
    rewrite (isum_in n (snd e) (fun i => y i * ediff x e) Hv).
    rewrite (IH n x y);
      [| intros e' He'; apply Hok; right; exact He'].
    unfold gform. simpl. unfold ediff. ring.
Qed.

Lemma gform_sym : forall E x y, gform E x y == gform E y x.
Proof.
  intros E x y. unfold gform. apply esum_ext. intros e _. ring.
Qed.

Lemma gform_scale_l : forall E (c : Q) (x y : nat -> Q),
  gform E (fun i => c * x i) y == c * gform E x y.
Proof.
  intros E c x y. unfold gform.
  rewrite (esum_ext E (fun e => ediff (fun i => c * x i) e * ediff y e)
                      (fun e => c * (ediff x e * ediff y e)));
    [apply esum_scale |].
  intros e _. unfold ediff. ring.
Qed.

Lemma gform_scale_r : forall E (c : Q) (x y : nat -> Q),
  gform E x (fun i => c * y i) == c * gform E x y.
Proof.
  intros E c x y.
  rewrite (gform_sym E x (fun i => c * y i)).
  rewrite (gform_scale_l E c y x).
  rewrite (gform_sym E y x).
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The energy pairing and the M-scaled generator                       *)
(* ------------------------------------------------------------------ *)

Definition Einner (E : list Edge) (n : nat) (M K : Q)
                  (x v y w : nat -> Q) : Q :=
  K * gform E x y + M * vdot n v w.

(* B (x,v) = (Bpos v , Bvel x):  the two components of the generator *)
Definition Bpos (M : Q) (v : nat -> Q) : nat -> Q :=
  fun i => M * v i.

Definition Bvel (K : Q) (E : list Edge) (x : nat -> Q) : nat -> Q :=
  fun i => - (K * lap E x i).

(* ------------------------------------------------------------------ *)
(* Structure of the pairing                                            *)
(* ------------------------------------------------------------------ *)

Theorem Einner_sym : forall E n M K (x v y w : nat -> Q),
  Einner E n M K x v y w == Einner E n M K y w x v.
Proof.
  intros E n M K x v y w. unfold Einner, vdot.
  rewrite (gform_sym E x y).
  rewrite (qsum_ext n (fun i => v i * w i) (fun i => w i * v i));
    [reflexivity | intros i _; ring].
Qed.

Theorem Einner_nonneg : forall E n M K (x v : nat -> Q),
  0 <= K -> 0 <= M ->
  0 <= Einner E n M K x v x v.
Proof.
  intros E n M K x v HK HM. unfold Einner.
  assert (Hg : 0 <= gform E x x).
  { unfold gform. apply esum_nonneg. intros e _. apply sq_nonneg. }
  assert (Hv : 0 <= vdot n v v).
  { unfold vdot. apply qsum_nonneg. intros i _. apply sq_nonneg. }
  assert (H1 : 0 <= K * gform E x x) by (apply Qmult_le_0_compat; assumption).
  assert (H2 : 0 <= M * vdot n v v) by (apply Qmult_le_0_compat; assumption).
  lra.
Qed.

(* ------------------------------------------------------------------ *)
(* SKEW-ADJOINTNESS of the generator for the energy pairing:           *)
(*   <B(x,v),(y,w)>_E  ==  - <(x,v),B(y,w)>_E                          *)
(* No sign conditions on M or K are needed.                            *)
(* ------------------------------------------------------------------ *)

Theorem companion_skew : forall E n (x v y w : nat -> Q) (M K : Q),
  nodes_ok n E ->
  Einner E n M K (Bpos M v) (Bvel K E x) y w
    == - Einner E n M K x v (Bpos M w) (Bvel K E y).
Proof.
  intros E n x v y w M K Hok.
  unfold Einner, Bpos, Bvel.
  assert (A1 : gform E (fun i => M * v i) y == M * gform E v y)
    by (apply gform_scale_l).
  assert (A2 : vdot n (fun i => - (K * lap E x i)) w == - (K * gform E x w)).
  { unfold vdot.
    rewrite (qsum_ext n (fun i => - (K * lap E x i) * w i)
                        (fun i => (- K) * (w i * lap E x i)));
      [| intros i _; ring].
    rewrite (qsum_scale n (- K) (fun i => w i * lap E x i)).
    rewrite (green_identity E n x w Hok). ring. }
  assert (A3 : gform E x (fun i => M * w i) == M * gform E x w)
    by (apply gform_scale_r).
  assert (A4 : vdot n v (fun i => - (K * lap E y i)) == - (K * gform E y v)).
  { unfold vdot.
    rewrite (qsum_ext n (fun i => v i * - (K * lap E y i))
                        (fun i => (- K) * (v i * lap E y i)));
      [| intros i _; ring].
    rewrite (qsum_scale n (- K) (fun i => v i * lap E y i)).
    rewrite (green_identity E n y v Hok). ring. }
  assert (A5 : gform E v y == gform E y v) by (apply gform_sym).
  rewrite A1, A2, A3, A4, A5. ring.
Qed.

(* ------------------------------------------------------------------ *)
(* ENERGY ORTHOGONALITY:  the generator moves every state              *)
(* orthogonally to its own energy level set — exactly, over Q,         *)
(* with no limit taken anywhere.                                       *)
(* ------------------------------------------------------------------ *)

Theorem companion_energy_orthogonal : forall E n (x v : nat -> Q) (M K : Q),
  nodes_ok n E ->
  Einner E n M K (Bpos M v) (Bvel K E x) x v == 0.
Proof.
  intros E n x v M K Hok.
  assert (Hskew := companion_skew E n x v x v M K Hok).
  assert (Hsym : Einner E n M K x v (Bpos M v) (Bvel K E x)
              == Einner E n M K (Bpos M v) (Bvel K E x) x v)
    by (apply Einner_sym).
  lra.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions green_identity.
Print Assumptions Einner_sym.
Print Assumptions Einner_nonneg.
Print Assumptions companion_skew.
Print Assumptions companion_energy_orthogonal.

End CompanionSkew.
