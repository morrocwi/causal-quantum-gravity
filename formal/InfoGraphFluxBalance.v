(* ===================================================================== *)
(*  RDL_GraphFluxBalance.v                                                 *)
(*  TRANSPORT-ONLY STRUCTURE of the graph second-difference operator:      *)
(*  the discrete divergence theorem, the summation-by-parts (Green)        *)
(*  identity, self-adjointness, and the EXACT balance law of the full      *)
(*  vector two-step recurrence with dissipation and a source term —        *)
(*  entirely over Q (no reals, no limits, no square roots).                *)
(*                                                                         *)
(*  CLAIMED HERE (candidate for coqc 8.18.0, axiom-free target):           *)
(*    div_total_zero      the total divergence of ANY edge field is 0      *)
(*                        (the discrete divergence theorem: edge fields    *)
(*                         TRANSPORT, they never create)                   *)
(*    lap_total_zero      sum over nodes of (L x)_i is 0                   *)
(*    green_identity      <y, L x> == sum_e ediff(x,e)*ediff(y,e)          *)
(*                        (summation by parts / discrete Green identity)   *)
(*    lap_self_adjoint    <y, L x> == <x, L y>                             *)
(*    green_diag          <x, L x> == the edge quadratic form              *)
(*                        (joint with RDL_SpectralCeiling.form)            *)
(*    flux_balance        for the vector recurrence, per step, EXACTLY:    *)
(*                          Evec(p',p) - Evec(p,q)                         *)
(*                            == - c * sum_i (p'_i - q_i)^2                *)
(*                               + h^2 * sum_i J_i * (p'_i - q_i)          *)
(*                        i.e. the energy change decomposes EXACTLY into   *)
(*                        a nonpositive dissipation term and the work of   *)
(*                        the source; the coupling term contributes ZERO   *)
(*                        net energy (it only transports through edges,    *)
(*                        by green_identity + div_total_zero).             *)
(*    flux_balance_monotone   c >= 0, source == 0  ==>  Evec nonincreasing *)
(*    flux_balance_conserved  c == 0, source == 0  ==>  Evec conserved     *)
(*                                                                         *)
(*  The step is taken as a per-node hypothesis (division-free):            *)
(*    (M+c) p'_i == 2M p_i - (M-c) q_i - h^2 K (L p)_i + h^2 J_i           *)
(*  and the energy is                                                      *)
(*    Evec(p,q) := M * sum_i (p_i - q_i)^2 + h^2 K * gform(p,q),           *)
(*  the vector version of RDL_RecurrenceEnergy.G (modal reduction:         *)
(*  on an exact Rayleigh pair gform contracts to lam * (p.q) and this      *)
(*  file's balance law contracts to that file's decrement identity).       *)
(*                                                                         *)
(*  Pre-verified with exact rational arithmetic on 300 random graphs       *)
(*  (all four structural identities and the full balance law, exact        *)
(*  equality) before authoring.                                            *)
(*  Expected: Print Assumptions => Closed under the global context.        *)
(* ===================================================================== *)

Require Coq.Arith.PeanoNat.
Require Coq.Lists.List.
Require Coq.QArith.QArith.
Require Coq.micromega.Lia.
Require Coq.micromega.Lqa.

Module GraphFluxBalance.

Import Coq.Lists.List. Import ListNotations.
Import Coq.Arith.PeanoNat.
Import Coq.QArith.QArith.
Import Coq.micromega.Lia.
Import Coq.micromega.Lqa.
Local Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(* Graph data (same conventions as RDL_SpectralCeiling.v; the file is  *)
(* self-contained so it coqc-checks standalone).                       *)
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

(* signed divergence at node i of an edge field g *)
Definition divg (E : list Edge) (g : Edge -> Q) (i : nat) : Q :=
  esum E (fun e => (ind (fst e) i - ind (snd e) i) * g e).

(* the graph second-difference operator at node i:                     *)
(*   (L x)_i  =  divergence of the edge-difference field of x          *)
Definition lap (E : list Edge) (x : nat -> Q) (i : nat) : Q :=
  divg E (ediff x) i.

(* bilinear edge form; gform E x x is RDL_SpectralCeiling.form *)
Definition gform (E : list Edge) (x y : nat -> Q) : Q :=
  esum E (fun e => ediff x e * ediff y e).

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

Lemma esum_sub : forall E (f g : Edge -> Q),
  esum E (fun e => f e - g e) == esum E f - esum E g.
Proof.
  induction E as [| e r IH]; intros f g; simpl; [ring | rewrite IH; ring].
Qed.

(* indicator sums (as in RDL_SpectralCeiling.v) *)
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
(* THE DISCRETE DIVERGENCE THEOREM:                                    *)
(* the total divergence of ANY edge field vanishes — an edge field     *)
(* moves quantity between its two endpoints and does nothing else.     *)
(* ------------------------------------------------------------------ *)

Theorem div_total_zero : forall E n (g : Edge -> Q),
  nodes_ok n E ->
  qsum n (fun i => divg E g i) == 0.
Proof.
  induction E as [| e r IH]; intros n g Hok.
  - rewrite (qsum_ext n (fun i => divg [] g i) (fun _ => 0));
      [apply qsum_zero |].
    intros i _. unfold divg. simpl. reflexivity.
  - destruct (Hok e (or_introl eq_refl)) as [Hu Hv].
    rewrite (qsum_ext n (fun i => divg (e :: r) g i)
             (fun i => (ind (fst e) i * g e - ind (snd e) i * g e)
                       + divg r g i));
      [| intros i _; unfold divg; simpl; ring].
    rewrite qsum_plus.
    rewrite qsum_sub.
    rewrite (isum_in n (fst e) (fun _ => g e) Hu).
    rewrite (isum_in n (snd e) (fun _ => g e) Hv).
    rewrite (IH n g); [ring |].
    intros e' He'. apply Hok. right. exact He'.
Qed.

Corollary lap_total_zero : forall E n (x : nat -> Q),
  nodes_ok n E ->
  qsum n (fun i => lap E x i) == 0.
Proof.
  intros E n x Hok. unfold lap. apply div_total_zero. exact Hok.
Qed.

(* ------------------------------------------------------------------ *)
(* SUMMATION BY PARTS (discrete Green identity):                       *)
(*   <y, L x>  ==  sum_e  ediff(x,e) * ediff(y,e)                      *)
(* ------------------------------------------------------------------ *)

Theorem green_identity : forall E n (x y : nat -> Q),
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

Theorem lap_self_adjoint : forall E n (x y : nat -> Q),
  nodes_ok n E ->
  qsum n (fun i => y i * lap E x i) == qsum n (fun i => x i * lap E y i).
Proof.
  intros E n x y Hok.
  rewrite (green_identity E n x y Hok).
  rewrite (green_identity E n y x Hok).
  unfold gform. apply esum_ext. intros e _. ring.
Qed.

Corollary green_diag : forall E n (x : nat -> Q),
  nodes_ok n E ->
  qsum n (fun i => x i * lap E x i) == gform E x x.
Proof.
  intros E n x Hok. apply green_identity. exact Hok.
Qed.

(* gform is symmetric and additive in its first slot *)
Lemma gform_sym : forall E x y, gform E x y == gform E y x.
Proof.
  intros E x y. unfold gform. apply esum_ext. intros e _. ring.
Qed.

Lemma gform_sub_l : forall E (p q y : nat -> Q),
  gform E (fun i => p i - q i) y == gform E p y - gform E q y.
Proof.
  intros E p q y. unfold gform.
  rewrite (esum_ext E (fun e => ediff (fun i => p i - q i) e * ediff y e)
                      (fun e => ediff p e * ediff y e
                                - ediff q e * ediff y e));
    [apply esum_sub |].
  intros e _. unfold ediff. ring.
Qed.

(* ------------------------------------------------------------------ *)
(* THE EXACT BALANCE LAW of the vector two-step recurrence.            *)
(*                                                                     *)
(* Energy of a state pair:                                             *)
(*   Evec(p,q) := M * sum_i (p_i - q_i)^2 + h^2 K * gform(p,q)         *)
(* Step (per node, division-free hypothesis):                          *)
(*   (M+c) p'_i == 2M p_i - (M-c) q_i - h^2 K (L p)_i + h^2 J_i        *)
(* Then EXACTLY:                                                       *)
(*   Evec(p',p) - Evec(p,q)                                            *)
(*     == - c * sum_i (p'_i - q_i)^2  +  h^2 * sum_i J_i (p'_i - q_i)  *)
(*                                                                     *)
(* The coupling operator L drops out of the balance ENTIRELY: by       *)
(* green_identity its contribution telescopes over edges, so it can    *)
(* only transport between nodes — never create or destroy.             *)
(* ------------------------------------------------------------------ *)

Definition Evec (M h K : Q) (E : list Edge) (n : nat) (p q : nat -> Q) : Q :=
  M * qsum n (fun i => (p i - q i) * (p i - q i)) + (h * h * K) * gform E p q.

Theorem flux_balance :
  forall E n (p q p' J : nat -> Q) (M c h K : Q),
  nodes_ok n E ->
  (forall i, (i < n)%nat ->
     (M + c) * p' i ==
     2 * M * p i - (M - c) * q i - (h * h * K) * lap E p i + (h * h) * J i) ->
  Evec M h K E n p' p - Evec M h K E n p q ==
    - (c * qsum n (fun i => (p' i - q i) * (p' i - q i)))
    + (h * h) * qsum n (fun i => J i * (p' i - q i)).
Proof.
  intros E n p q p' J M c h K Hok Hstep.
  unfold Evec.
  (* kinetic part:  sum (p'-p)^2 - sum (p-q)^2 == sum (p'-q)(p'-2p+q) *)
  assert (HS : qsum n (fun i => (p' i - p i) * (p' i - p i))
             - qsum n (fun i => (p i - q i) * (p i - q i))
             == qsum n (fun i => (p' i - q i) * (p' i - 2 * p i + q i))).
  { rewrite <- qsum_sub. apply qsum_ext. intros i _. ring. }
  (* coupling part:  gform(p',p) - gform(p,q) == sum (p'-q)_i (L p)_i *)
  assert (HT : gform E p' p - gform E p q
             == qsum n (fun i => (p' i - q i) * lap E p i)).
  { rewrite (gform_sym E p q).
    rewrite <- (gform_sub_l E p' q p).
    rewrite (gform_sym E (fun i => p' i - q i) p).
    rewrite <- (green_identity E n p (fun i => p' i - q i) Hok).
    reflexivity. }
  (* merge into a single node sum *)
  assert (Hmerge :
    M * qsum n (fun i => (p' i - q i) * (p' i - 2 * p i + q i))
    + (h * h * K) * qsum n (fun i => (p' i - q i) * lap E p i)
    == qsum n (fun i =>
         M * ((p' i - q i) * (p' i - 2 * p i + q i))
         + (h * h * K) * ((p' i - q i) * lap E p i))).
  { rewrite qsum_plus.
    rewrite (qsum_scale n M (fun i => (p' i - q i) * (p' i - 2 * p i + q i))).
    rewrite (qsum_scale n (h * h * K) (fun i => (p' i - q i) * lap E p i)).
    reflexivity. }
  (* apply the step hypothesis pointwise *)
  assert (Hpoint : qsum n (fun i =>
         M * ((p' i - q i) * (p' i - 2 * p i + q i))
         + (h * h * K) * ((p' i - q i) * lap E p i))
    == qsum n (fun i =>
         (p' i - q i) * (- (c * (p' i - q i)) + (h * h) * J i))).
  { apply qsum_ext. intros i Hi.
    assert (Hb : M * (p' i - 2 * p i + q i) + (h * h * K) * lap E p i
                 == - (c * (p' i - q i)) + (h * h) * J i)
      by (specialize (Hstep i Hi); lra).
    rewrite <- Hb. ring. }
  (* split the right-hand side into dissipation + work *)
  assert (Hsplit : qsum n (fun i =>
         (p' i - q i) * (- (c * (p' i - q i)) + (h * h) * J i))
    == - (c * qsum n (fun i => (p' i - q i) * (p' i - q i)))
       + (h * h) * qsum n (fun i => J i * (p' i - q i))).
  { rewrite (qsum_ext n
      (fun i => (p' i - q i) * (- (c * (p' i - q i)) + (h * h) * J i))
      (fun i => (- c) * ((p' i - q i) * (p' i - q i))
                + (h * h) * (J i * (p' i - q i))));
      [| intros i _; ring].
    rewrite qsum_plus.
    rewrite (qsum_scale n (- c) (fun i => (p' i - q i) * (p' i - q i))).
    rewrite (qsum_scale n (h * h) (fun i => J i * (p' i - q i))).
    ring. }
  (* pre-multiplied versions so the final step is linear in monomials *)
  assert (HS2 : M * (qsum n (fun i => (p' i - p i) * (p' i - p i))
                   - qsum n (fun i => (p i - q i) * (p i - q i)))
              == M * qsum n (fun i => (p' i - q i) * (p' i - 2 * p i + q i)))
    by (rewrite HS; reflexivity).
  assert (HT2 : (h * h * K) * (gform E p' p - gform E p q)
              == (h * h * K) * qsum n (fun i => (p' i - q i) * lap E p i))
    by (rewrite HT; reflexivity).
  lra.
Qed.

(* with no source and nonnegative dissipation the energy never grows *)
Theorem flux_balance_monotone :
  forall E n (p q p' J : nat -> Q) (M c h K : Q),
  nodes_ok n E ->
  0 <= c ->
  (forall i, (i < n)%nat -> J i == 0) ->
  (forall i, (i < n)%nat ->
     (M + c) * p' i ==
     2 * M * p i - (M - c) * q i - (h * h * K) * lap E p i + (h * h) * J i) ->
  Evec M h K E n p' p <= Evec M h K E n p q.
Proof.
  intros E n p q p' J M c h K Hok Hc HJ Hstep.
  assert (Hbal := flux_balance E n p q p' J M c h K Hok Hstep).
  assert (HW : qsum n (fun i => J i * (p' i - q i)) == 0).
  { rewrite (qsum_ext n (fun i => J i * (p' i - q i)) (fun _ => 0));
      [apply qsum_zero |].
    intros i Hi. rewrite (HJ i Hi). ring. }
  assert (HW2 : (h * h) * qsum n (fun i => J i * (p' i - q i)) == 0)
    by (rewrite HW; ring).
  assert (HD : 0 <= qsum n (fun i => (p' i - q i) * (p' i - q i)))
    by (apply qsum_nonneg; intros i _; apply sq_nonneg).
  assert (HcD : 0 <= c * qsum n (fun i => (p' i - q i) * (p' i - q i)))
    by (apply Qmult_le_0_compat; assumption).
  lra.
Qed.

(* with no source and no dissipation the energy is EXACTLY conserved *)
Theorem flux_balance_conserved :
  forall E n (p q p' J : nat -> Q) (M c h K : Q),
  nodes_ok n E ->
  c == 0 ->
  (forall i, (i < n)%nat -> J i == 0) ->
  (forall i, (i < n)%nat ->
     (M + c) * p' i ==
     2 * M * p i - (M - c) * q i - (h * h * K) * lap E p i + (h * h) * J i) ->
  Evec M h K E n p' p == Evec M h K E n p q.
Proof.
  intros E n p q p' J M c h K Hok Hc HJ Hstep.
  assert (Hbal := flux_balance E n p q p' J M c h K Hok Hstep).
  assert (HW : qsum n (fun i => J i * (p' i - q i)) == 0).
  { rewrite (qsum_ext n (fun i => J i * (p' i - q i)) (fun _ => 0));
      [apply qsum_zero |].
    intros i Hi. rewrite (HJ i Hi). ring. }
  assert (HW2 : (h * h) * qsum n (fun i => J i * (p' i - q i)) == 0)
    by (rewrite HW; ring).
  assert (HZ : c * qsum n (fun i => (p' i - q i) * (p' i - q i)) == 0)
    by (rewrite Hc; ring).
  lra.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions div_total_zero.
Print Assumptions lap_total_zero.
Print Assumptions green_identity.
Print Assumptions lap_self_adjoint.
Print Assumptions green_diag.
Print Assumptions flux_balance.
Print Assumptions flux_balance_monotone.
Print Assumptions flux_balance_conserved.

End GraphFluxBalance.
