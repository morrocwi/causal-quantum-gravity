(* ===================================================================== *)
(*  RDL_ActionStationarity.v                                               *)
(*  THE RECURRENCE AS A STATIONARITY READOUT — the second-difference       *)
(*  step is EXACTLY the vanishing of the first variation of a discrete     *)
(*  quadratic action, at every node; and the same functional, varied       *)
(*  over the GRAPH instead of the field, yields an exact per-edge          *)
(*  balance law.  Entirely over Q (no reals, no limits, no calculus:       *)
(*  "first variation" is the LINEAR COEFFICIENT of an exact quadratic      *)
(*  polarization identity).                                                *)
(*                                                                         *)
(*  The window action, for a three-slice field history (p, m, q):          *)
(*    Awin := M*|q - m|^2 + M*|m - p|^2 - h^2 K * gform(m, m)              *)
(*  (kinetic minus potential; overall constants absorbed).                 *)
(*                                                                         *)
(*  CLAIMED HERE (candidate for coqc 8.18.0, axiom-free target):           *)
(*    action_polarization                                                  *)
(*        perturbing the middle slice at one node i by s changes Awin      *)
(*        by EXACTLY                                                       *)
(*          -2s * [ M(q_i - 2m_i + p_i) + h^2 K (L m)_i ]  +  s^2 * C_i    *)
(*        with C_i := 2M - h^2 K * gdeg(i).  The linear coefficient IS     *)
(*        the step residual: the recurrence is the readout of the          *)
(*        selection principle, node by node.                               *)
(*    mother_step_stationary                                               *)
(*        on the conservative step the first variation VANISHES at every   *)
(*        node: the change is purely second order.                         *)
(*    damped_step_balance                                                  *)
(*        on the dissipative step the first variation equals EXACTLY the   *)
(*        work of the dissipative force against the variation,             *)
(*          2 s c (q_i - p_i)                                              *)
(*        (the discrete Rayleigh/Onsager balance: dissipation is the       *)
(*        only obstruction to stationarity).                               *)
(*    strict_descent                                                       *)
(*        wherever the residual is nonzero and C_i > 0, an explicit        *)
(*        variation strictly LOWERS the action (witness s = R/C, value     *)
(*        -R^2/C): a non-solution is never selected — the argmin           *)
(*        content of the readout, made exact.                              *)
(*    addition_variation / retention_balance_add / retention_balance_rem   *)
(*        varying the GRAPH: for the geometric functional                  *)
(*          Sgeo := h^2 K * gform(m,m) - sum_e benefit(e),                 *)
(*        adding an edge changes Sgeo by EXACTLY                           *)
(*          h^2 K * (ediff m e)^2 - benefit(e),                            *)
(*        and hence (both directions, exact iff):                          *)
(*          an absent edge stays absent  iff  benefit <= quadratic strain, *)
(*          a retained edge stays        iff  quadratic strain <= benefit. *)
(*        This per-edge balance between field strain and retention         *)
(*        benefit is the geometry-variation slot of the same selection     *)
(*        principle (the conservation slot is RDL_GraphFluxBalance.        *)
(*        div_total_zero; the curvature response to the same edge move     *)
(*        is RDL_GraphGrowth.forman_growth_shift).                         *)
(*                                                                         *)
(*  HONESTLY NOT CLAIMED: any continuum variational principle, any         *)
(*  metric, and any readout-limit of the coupled (field + graph)           *)
(*  stationarity — those remain the open remainder, deliberately.          *)
(*                                                                         *)
(*  Pre-verified with exact rational arithmetic (300 random                *)
(*  graph/field/parameter draws; every identity and both iff directions    *)
(*  checked exactly) before authoring.                                     *)
(*  Expected: Print Assumptions => Closed under the global context.        *)
(* ===================================================================== *)

Require Coq.Arith.PeanoNat.
Require Coq.Lists.List.
Require Coq.QArith.QArith.
Require Coq.micromega.Lia.
Require Coq.micromega.Lqa.

Module ActionStationarity.

Import Coq.Lists.List. Import ListNotations.
Import Coq.Arith.PeanoNat.
Import Coq.QArith.QArith.
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

Definition ediff (x : nat -> Q) (e : Edge) : Q := x (fst e) - x (snd e).

Definition lint (x : nat -> Q) (i : nat) (e : Edge) : Q :=
  (ind (fst e) i - ind (snd e) i) * ediff x e.

Definition lap (E : list Edge) (x : nat -> Q) (i : nat) : Q :=
  esum E (lint x i).

Definition gform (E : list Edge) (x y : nat -> Q) : Q :=
  esum E (fun e => ediff x e * ediff y e).

(* the quadratic weight of a single-node variation in the potential *)
Definition gdeg (E : list Edge) (i : nat) : Q :=
  esum E (fun e => (ind (fst e) i - ind (snd e) i)
                 * (ind (fst e) i - ind (snd e) i)).

(* ------------------------------------------------------------------ *)
(* Toolbox                                                             *)
(* ------------------------------------------------------------------ *)

Lemma sq_nonneg : forall x : Q, 0 <= x * x.
Proof.
  intro x. destruct (Qlt_le_dec x 0) as [Hneg | Hpos].
  - setoid_replace (x * x) with ((- x) * (- x)) by ring.
    apply Qmult_le_0_compat; lra.
  - apply Qmult_le_0_compat; lra.
Qed.

Lemma sq_pos : forall x : Q, ~ x == 0 -> 0 < x * x.
Proof.
  intros x Hx.
  destruct (Qlt_le_dec x 0) as [Hneg | Hpos].
  - setoid_replace (x * x) with ((- x) * (- x)) by ring.
    assert (H0 : 0 < - x) by lra.
    assert (Hm : 0 * (- x) < (- x) * (- x))
      by (apply Qmult_lt_compat_r; lra).
    lra.
  - assert (H0 : 0 < x) by lra.
    assert (Hm : 0 * x < x * x)
      by (apply Qmult_lt_compat_r; lra).
    lra.
Qed.

Lemma ind_sym : forall a b : nat, ind a b == ind b a.
Proof.
  intros a b. unfold ind. rewrite Nat.eqb_sym. reflexivity.
Qed.

Lemma ind_sq : forall a b : nat, ind a b * ind a b == ind a b.
Proof.
  intros a b. unfold ind. destruct (Nat.eqb a b); ring.
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

Lemma qsum_plus : forall n (f g : nat -> Q),
  qsum n (fun i => f i + g i) == qsum n f + qsum n g.
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

Lemma esum_plus : forall E (f g : Edge -> Q),
  esum E (fun e => f e + g e) == esum E f + esum E g.
Proof.
  induction E as [| e r IH]; intros f g; simpl; [ring | rewrite IH; ring].
Qed.

Lemma esum_scale : forall E (c : Q) (g : Edge -> Q),
  esum E (fun e => c * g e) == c * esum E g.
Proof.
  induction E as [| e r IH]; intros c g; simpl; [ring | rewrite IH; ring].
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
(* Single-node perturbation expansions (exact quadratic polarization)  *)
(* ------------------------------------------------------------------ *)

(* right slot of a squared difference: a - (m + s * delta_i) *)
Lemma norm2_shift_r : forall n (a m : nat -> Q) (i : nat) (s : Q),
  (i < n)%nat ->
  qsum n (fun j => (a j - (m j + s * ind i j)) * (a j - (m j + s * ind i j)))
  == qsum n (fun j => (a j - m j) * (a j - m j))
     - (2 * s) * (a i - m i) + s * s.
Proof.
  intros n a m i s Hi.
  rewrite (qsum_ext n
    (fun j => (a j - (m j + s * ind i j)) * (a j - (m j + s * ind i j)))
    (fun j => (a j - m j) * (a j - m j)
              + ((- (2 * s)) * (ind i j * (a j - m j))
                 + (s * s) * (ind i j * ind i j))));
    [| intros j _; ring].
  rewrite (qsum_plus n
    (fun j => (a j - m j) * (a j - m j))
    (fun j => (- (2 * s)) * (ind i j * (a j - m j))
              + (s * s) * (ind i j * ind i j))).
  rewrite (qsum_plus n
    (fun j => (- (2 * s)) * (ind i j * (a j - m j)))
    (fun j => (s * s) * (ind i j * ind i j))).
  rewrite (qsum_scale n (- (2 * s)) (fun j => ind i j * (a j - m j))).
  rewrite (qsum_scale n (s * s) (fun j => ind i j * ind i j)).
  rewrite (isum_in n i (fun j => a j - m j) Hi).
  rewrite (isum_in n i (fun j => ind i j) Hi).
  assert (Hii : ind i i == 1)
    by (unfold ind; rewrite Nat.eqb_refl; reflexivity).
  rewrite Hii. ring.
Qed.

(* left slot: (m + s * delta_i) - p *)
Lemma norm2_shift_l : forall n (p m : nat -> Q) (i : nat) (s : Q),
  (i < n)%nat ->
  qsum n (fun j => ((m j + s * ind i j) - p j) * ((m j + s * ind i j) - p j))
  == qsum n (fun j => (m j - p j) * (m j - p j))
     + (2 * s) * (m i - p i) + s * s.
Proof.
  intros n p m i s Hi.
  rewrite (qsum_ext n
    (fun j => ((m j + s * ind i j) - p j) * ((m j + s * ind i j) - p j))
    (fun j => (m j - p j) * (m j - p j)
              + ((2 * s) * (ind i j * (m j - p j))
                 + (s * s) * (ind i j * ind i j))));
    [| intros j _; ring].
  rewrite (qsum_plus n
    (fun j => (m j - p j) * (m j - p j))
    (fun j => (2 * s) * (ind i j * (m j - p j))
              + (s * s) * (ind i j * ind i j))).
  rewrite (qsum_plus n
    (fun j => (2 * s) * (ind i j * (m j - p j)))
    (fun j => (s * s) * (ind i j * ind i j))).
  rewrite (qsum_scale n (2 * s) (fun j => ind i j * (m j - p j))).
  rewrite (qsum_scale n (s * s) (fun j => ind i j * ind i j)).
  rewrite (isum_in n i (fun j => m j - p j) Hi).
  rewrite (isum_in n i (fun j => ind i j) Hi).
  assert (Hii : ind i i == 1)
    by (unfold ind; rewrite Nat.eqb_refl; reflexivity).
  rewrite Hii. ring.
Qed.

(* the potential slot: exact quadratic expansion of gform under a       *)
(* single-node variation; the LINEAR coefficient is 2 * (L m)_i         *)
Lemma gform_shift : forall E (m : nat -> Q) (i : nat) (s : Q),
  gform E (fun j => m j + s * ind i j) (fun j => m j + s * ind i j)
  == gform E m m + (2 * s) * lap E m i + (s * s) * gdeg E i.
Proof.
  intros E m i s.
  unfold gform, lap, gdeg.
  rewrite (esum_ext E
    (fun e => ediff (fun j => m j + s * ind i j) e
            * ediff (fun j => m j + s * ind i j) e)
    (fun e => ediff m e * ediff m e
              + ((2 * s) * lint m i e
                 + (s * s) * ((ind (fst e) i - ind (snd e) i)
                              * (ind (fst e) i - ind (snd e) i)))));
    [| intros e _;
       unfold ediff, lint;
       rewrite (ind_sym i (fst e)); rewrite (ind_sym i (snd e));
       unfold ediff; ring].
  rewrite (esum_plus E
    (fun e => ediff m e * ediff m e)
    (fun e => (2 * s) * lint m i e
              + (s * s) * ((ind (fst e) i - ind (snd e) i)
                           * (ind (fst e) i - ind (snd e) i)))).
  rewrite (esum_plus E
    (fun e => (2 * s) * lint m i e)
    (fun e => (s * s) * ((ind (fst e) i - ind (snd e) i)
                         * (ind (fst e) i - ind (snd e) i)))).
  rewrite (esum_scale E (2 * s) (lint m i)).
  rewrite (esum_scale E (s * s)
    (fun e => (ind (fst e) i - ind (snd e) i)
            * (ind (fst e) i - ind (snd e) i))).
  ring.
Qed.

(* ------------------------------------------------------------------ *)
(* THE WINDOW ACTION and its exact polarization                        *)
(* ------------------------------------------------------------------ *)

Definition Awin (E : list Edge) (n : nat) (M h K : Q)
                (p m q : nat -> Q) : Q :=
  M * qsum n (fun j => (q j - m j) * (q j - m j))
  + M * qsum n (fun j => (m j - p j) * (m j - p j))
  - (h * h * K) * gform E m m.

(* THE POLARIZATION IDENTITY: the first variation of the action at      *)
(* node i is minus twice the STEP RESIDUAL; the equation of motion is    *)
(* the stationarity readout of the action, node by node, exactly.        *)
Theorem action_polarization :
  forall E n (p m q : nat -> Q) (M h K : Q) (i : nat) (s : Q),
  (i < n)%nat ->
  Awin E n M h K p (fun j => m j + s * ind i j) q - Awin E n M h K p m q
  == - (2 * s) * (M * (q i - 2 * m i + p i) + (h * h * K) * lap E m i)
     + (s * s) * (2 * M - (h * h * K) * gdeg E i).
Proof.
  intros E n p m q M h K i s Hi.
  unfold Awin.
  rewrite (norm2_shift_r n q m i s Hi).
  rewrite (norm2_shift_l n p m i s Hi).
  rewrite (gform_shift E m i s).
  ring.
Qed.

(* on the conservative step the first variation vanishes: the change    *)
(* of the action is PURELY second order at every node                    *)
Theorem mother_step_stationary :
  forall E n (p m q : nat -> Q) (M h K : Q) (i : nat) (s : Q),
  (i < n)%nat ->
  M * q i == 2 * M * m i - M * p i - (h * h * K) * lap E m i ->
  Awin E n M h K p (fun j => m j + s * ind i j) q - Awin E n M h K p m q
  == (s * s) * (2 * M - (h * h * K) * gdeg E i).
Proof.
  intros E n p m q M h K i s Hi Hstep.
  assert (Hpol := action_polarization E n p m q M h K i s Hi).
  assert (HR : M * (q i - 2 * m i + p i) + (h * h * K) * lap E m i == 0)
    by lra.
  assert (Hz : - (2 * s)
               * (M * (q i - 2 * m i + p i) + (h * h * K) * lap E m i)
               == 0)
    by (rewrite HR; ring).
  lra.
Qed.

(* on the dissipative step the first variation equals EXACTLY the work  *)
(* of the dissipative force against the variation (discrete Rayleigh /  *)
(* Onsager balance): dissipation is the sole obstruction to             *)
(* stationarity                                                          *)
Theorem damped_step_balance :
  forall E n (p m q : nat -> Q) (M c h K : Q) (i : nat) (s : Q),
  (i < n)%nat ->
  (M + c) * q i == 2 * M * m i - (M - c) * p i - (h * h * K) * lap E m i ->
  Awin E n M h K p (fun j => m j + s * ind i j) q - Awin E n M h K p m q
  == (2 * s) * (c * (q i - p i))
     + (s * s) * (2 * M - (h * h * K) * gdeg E i).
Proof.
  intros E n p m q M c h K i s Hi Hstep.
  assert (Hpol := action_polarization E n p m q M h K i s Hi).
  assert (HR : M * (q i - 2 * m i + p i) + (h * h * K) * lap E m i
             == - (c * (q i - p i)))
    by lra.
  assert (Hz : - (2 * s)
               * (M * (q i - 2 * m i + p i) + (h * h * K) * lap E m i)
               == - (2 * s) * (- (c * (q i - p i))))
    by (rewrite HR; reflexivity).
  lra.
Qed.

(* wherever the residual is nonzero (and the quadratic weight is        *)
(* positive), an explicit variation strictly LOWERS the action:         *)
(* non-solutions are never selected — the argmin content, exact          *)
Theorem strict_descent :
  forall E n (p m q : nat -> Q) (M h K : Q) (i : nat),
  (i < n)%nat ->
  0 < 2 * M - (h * h * K) * gdeg E i ->
  ~ (M * (q i - 2 * m i + p i) + (h * h * K) * lap E m i == 0) ->
  exists s : Q,
    Awin E n M h K p (fun j => m j + s * ind i j) q
    < Awin E n M h K p m q.
Proof.
  intros E n p m q M h K i Hi HC HR.
  set (R := M * (q i - 2 * m i + p i) + (h * h * K) * lap E m i) in *.
  set (C := 2 * M - (h * h * K) * gdeg E i) in *.
  exists (R / C).
  assert (Hpol := action_polarization E n p m q M h K i (R / C) Hi).
  fold R C in Hpol.
  assert (HCnz : ~ C == 0) by (intro Hc0; lra).
  assert (Hval : - (2 * (R / C)) * R + (R / C) * (R / C) * C
               == - ((R * R) / C))
    by (field; exact HCnz).
  assert (HRR : 0 < R * R) by (apply sq_pos; exact HR).
  assert (HinvC : 0 < / C) by (apply Qinv_lt_0_compat; exact HC).
  assert (Hprod : 0 * / C < (R * R) * / C)
    by (apply Qmult_lt_compat_r; [exact HinvC | exact HRR]).
  assert (Hpos : 0 < (R * R) / C)
    by (unfold Qdiv; lra).
  lra.
Qed.

(* ------------------------------------------------------------------ *)
(* VARYING THE GRAPH: the geometric functional and its exact per-edge  *)
(* balance law (the geometry-variation slot of the same principle)     *)
(* ------------------------------------------------------------------ *)

(* field strain stored in the geometry, minus the total retention       *)
(* benefit of the edges (one admissible lens; benefit b : Edge -> Q)    *)
Definition Sgeo (E : list Edge) (m : nat -> Q) (b : Edge -> Q)
                (h K : Q) : Q :=
  (h * h * K) * gform E m m - esum E b.

(* the EXACT variation of the functional under adding one edge *)
Theorem addition_variation :
  forall E (m : nat -> Q) (b : Edge -> Q) (h K : Q) (estar : Edge),
  Sgeo (estar :: E) m b h K - Sgeo E m b h K
  == (h * h * K) * (ediff m estar * ediff m estar) - b estar.
Proof.
  intros E m b h K estar.
  unfold Sgeo, gform. simpl. ring.
Qed.

(* an absent edge stays absent  iff  its benefit does not exceed the    *)
(* quadratic strain it would carry                                       *)
Theorem retention_balance_add :
  forall E (m : nat -> Q) (b : Edge -> Q) (h K : Q) (estar : Edge),
  Sgeo E m b h K <= Sgeo (estar :: E) m b h K
  <-> b estar <= (h * h * K) * (ediff m estar * ediff m estar).
Proof.
  intros E m b h K estar.
  assert (Hv := addition_variation E m b h K estar).
  split; intro H; lra.
Qed.

(* a retained edge stays retained  iff  its strain does not exceed its  *)
(* benefit                                                               *)
Theorem retention_balance_rem :
  forall E (m : nat -> Q) (b : Edge -> Q) (h K : Q) (e : Edge),
  Sgeo (e :: E) m b h K <= Sgeo E m b h K
  <-> (h * h * K) * (ediff m e * ediff m e) <= b e.
Proof.
  intros E m b h K e.
  assert (Hv := addition_variation E m b h K e).
  split; intro H; lra.
Qed.

(* with no benefit anywhere, growth is never selected: the functional   *)
(* never decreases under edge addition                                   *)
Corollary no_free_growth :
  forall E (m : nat -> Q) (b : Edge -> Q) (h K : Q) (estar : Edge),
  0 <= h * h * K ->
  b estar <= 0 ->
  Sgeo E m b h K <= Sgeo (estar :: E) m b h K.
Proof.
  intros E m b h K estar HhK Hb.
  apply retention_balance_add.
  assert (Hs := sq_nonneg (ediff m estar)).
  assert (Hp : 0 <= (h * h * K) * (ediff m estar * ediff m estar))
    by (apply Qmult_le_0_compat; assumption).
  lra.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions action_polarization.
Print Assumptions mother_step_stationary.
Print Assumptions damped_step_balance.
Print Assumptions strict_descent.
Print Assumptions addition_variation.
Print Assumptions retention_balance_add.
Print Assumptions retention_balance_rem.
Print Assumptions no_free_growth.

End ActionStationarity.
