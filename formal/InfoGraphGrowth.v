(* ===================================================================== *)
(*  RDL_GraphGrowth.v                                                      *)
(*  EXACT LAWS OF GRAPH GROWTH — what adding an edge does to curvature,    *)
(*  to energy, and what a growing graph does to its slowest modes.         *)
(*  Entirely over Q (no reals, no limits, no eigenvalue theory).           *)
(*                                                                         *)
(*  CLAIMED HERE (candidate for coqc 8.18.0, axiom-free target):           *)
(*                                                                         *)
(*  I.  GROWTH vs CURVATURE (Forman, as in the C40 line):                  *)
(*    forman_growth_shift     F_{estar::E}(e) == F_E(e)                       *)
(*                              - share(estar,u(e)) - share(estar,v(e))        *)
(*                            — the EXACT law: adding one edge shifts      *)
(*                            every edge's curvature by minus the          *)
(*                            incidence count of the new edge              *)
(*    forman_growth_monotone  adding an edge NEVER increases curvature     *)
(*    forman_growth_strict    ... and strictly decreases it (by >= 1) on   *)
(*                            every edge sharing an endpoint with estar       *)
(*                                                                         *)
(*  II. GROWTH vs ENERGY:                                                  *)
(*    growth_energy_shift     Evec(estar::E) - Evec(E)                        *)
(*                              == h^2 K * ediff(p,estar) * ediff(q,estar)       *)
(*                            — the EXACT energy cost/release of adding    *)
(*                            one edge                                     *)
(*    growth_energy_adiabatic if the field is continuous across the new    *)
(*                            edge (ediff p estar == 0) the energy is         *)
(*                            EXACTLY unchanged                            *)
(*                                                                         *)
(*  III. ORDER COLLAPSE (recording the #4 obstruction as theorems,         *)
(*       conventions of RDL_CausalSignature.v):                            *)
(*    total_order_collapse    if EVERY edge is comparable (a total order   *)
(*                            makes all of them so) then                   *)
(*                            cform == - gdiag <= 0: the signature         *)
(*                            degenerates to (0,n) — NO spacelike cone.    *)
(*                            Incomparability IS what space is made of;    *)
(*                            a total order has no space.                  *)
(*    incomparable_collapse   dually, no comparable edge gives             *)
(*                            cform == gdiag (the honest, order-derived    *)
(*                            replacement of the imported Euclidean       *)
(*                            reduction)                                  *)
(*                                                                         *)
(*  IV. GROWTH vs SLOW MODES (dilution on the growing path):               *)
(*    ramp_mean_zero          the ramp state  x_i = 2 i - m  on the path   *)
(*                            with m+1 nodes sums to zero                  *)
(*    ramp_form / ramp_norm2  its edge form is exactly 4m; three times     *)
(*                            its squared norm is exactly n(n^2-1),        *)
(*                            n := m+1  (division-free closed forms)       *)
(*    ramp_dilution           n(n+1) * form == 12 * norm2   EXACTLY —      *)
(*                            i.e. the Rayleigh quotient of this           *)
(*                            mean-zero state is exactly 12/(n(n+1)):      *)
(*                            the growing path supports states of          *)
(*                            arbitrarily small quotient.  Composed with   *)
(*                            RDL_SpectralCeiling.mode_product_ceiling     *)
(*                            this brackets the spectrum from BOTH sides   *)
(*                            as the graph grows: the top is pinned by     *)
(*                            degree, the bottom sinks like 1/n^2.         *)
(*    ramp_norm2_pos          the witness is nondegenerate (norm2 > 0      *)
(*                            for m >= 1), so the quotient statement is    *)
(*                            not vacuous                                  *)
(*                                                                         *)
(*  HONESTLY NOT CLAIMED: any exponential (de Sitter-like) dilution — a    *)
(*  finite diagnostic over growth rules (path / binary tree / star) finds  *)
(*  power laws n^-2 / ~n^-1.1 and NO dilution at all for star growth: the  *)
(*  dilution LAW is a property of the growth topology, not of growth       *)
(*  itself.  That comparison is measurement, not theorem, and lives in     *)
(*  the journal at finite_diagnostic tier.                                 *)
(*                                                                         *)
(*  Pre-verified with exact rational arithmetic: the two growth laws on    *)
(*  300 random graphs each; the ramp Rayleigh identity exactly for         *)
(*  n = 2..59.  Expected: Print Assumptions => Closed.                     *)
(* ===================================================================== *)

Require Coq.Arith.PeanoNat.
Require Coq.Bool.Bool.
Require Coq.Lists.List.
Require Coq.QArith.QArith.
Require Coq.ZArith.ZArith.
Require Coq.micromega.Lia.
Require Coq.micromega.Lqa.

Module GraphGrowth.

Import Coq.Lists.List. Import ListNotations.
Import Coq.Arith.PeanoNat.
Import Coq.Bool.Bool.
Import Coq.ZArith.ZArith.
Import Coq.QArith.QArith.
Import Coq.micromega.Lia.
Import Coq.micromega.Lqa.
Local Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(* Graph data (shared conventions; self-contained for standalone coqc) *)
(* ------------------------------------------------------------------ *)

Definition Edge : Type := (nat * nat)%type.

Fixpoint qsum (n : nat) (f : nat -> Q) : Q :=
  match n with
  | O => 0
  | S m => qsum m f + f m
  end.

Definition esum (E : list Edge) (g : Edge -> Q) : Q :=
  fold_right (fun e acc => g e + acc) 0 E.

Definition ediff (x : nat -> Q) (e : Edge) : Q := x (fst e) - x (snd e).

Definition gform (E : list Edge) (x y : nat -> Q) : Q :=
  esum E (fun e => ediff x e * ediff y e).

Definition gdiag (E : list Edge) (x : nat -> Q) : Q :=
  esum E (fun e => ediff x e * ediff x e).

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

Lemma gdiag_cons : forall e E x,
  gdiag (e :: E) x == ediff x e * ediff x e + gdiag E x.
Proof. intros. unfold gdiag. simpl. reflexivity. Qed.

Theorem gdiag_nonneg : forall E x, 0 <= gdiag E x.
Proof.
  intros E x. unfold gdiag.
  apply esum_nonneg. intros e _. apply sq_nonneg.
Qed.

(* ------------------------------------------------------------------ *)
(* PART I — GROWTH vs CURVATURE (Forman, C40 conventions)              *)
(* ------------------------------------------------------------------ *)

Definition share (e : Edge) (i : nat) : Q :=
  (if Nat.eqb (fst e) i then 1 else 0) + (if Nat.eqb (snd e) i then 1 else 0).

Definition deg (E : list Edge) (i : nat) : Q := esum E (fun e => share e i).

Definition forman (E : list Edge) (e : Edge) : Q :=
  4 - deg E (fst e) - deg E (snd e).

Lemma share_nonneg : forall e i, 0 <= share e i.
Proof.
  intros e i. unfold share.
  destruct (Nat.eqb (fst e) i); destruct (Nat.eqb (snd e) i); lra.
Qed.

Lemma share_hit : forall e i, fst e = i \/ snd e = i -> 1 <= share e i.
Proof.
  intros e i [He | He]; unfold share; rewrite He, Nat.eqb_refl.
  - destruct (Nat.eqb (snd e) i); lra.
  - destruct (Nat.eqb (fst e) i); lra.
Qed.

(* THE EXACT LAW: one new edge shifts every curvature by minus its    *)
(* incidence count at the edge's two endpoints.                        *)
Theorem forman_growth_shift : forall E (estar e : Edge),
  forman (estar :: E) e
  == forman E e - share estar (fst e) - share estar (snd e).
Proof.
  intros E estar e. unfold forman, deg. simpl. ring.
Qed.

(* growth NEVER increases curvature *)
Theorem forman_growth_monotone : forall E (estar e : Edge),
  forman (estar :: E) e <= forman E e.
Proof.
  intros E estar e.
  assert (Hs := forman_growth_shift E estar e).
  assert (H1 := share_nonneg estar (fst e)).
  assert (H2 := share_nonneg estar (snd e)).
  lra.
Qed.

(* ... and strictly decreases it wherever the new edge touches *)
Theorem forman_growth_strict : forall E (estar e : Edge),
  (fst estar = fst e \/ snd estar = fst e) \/
  (fst estar = snd e \/ snd estar = snd e) ->
  forman (estar :: E) e <= forman E e - 1.
Proof.
  intros E estar e Hinc.
  assert (Hs := forman_growth_shift E estar e).
  assert (H1 := share_nonneg estar (fst e)).
  assert (H2 := share_nonneg estar (snd e)).
  destruct Hinc as [Hhit | Hhit].
  - assert (Hg := share_hit estar (fst e) Hhit). lra.
  - assert (Hg := share_hit estar (snd e) Hhit). lra.
Qed.

(* ------------------------------------------------------------------ *)
(* PART II — GROWTH vs ENERGY                                          *)
(* ------------------------------------------------------------------ *)

Definition Evec (M h K : Q) (E : list Edge) (n : nat) (p q : nat -> Q) : Q :=
  M * qsum n (fun i => (p i - q i) * (p i - q i)) + (h * h * K) * gform E p q.

(* the EXACT energy cost/release of adding one edge *)
Theorem growth_energy_shift :
  forall E n (p q : nat -> Q) (M h K : Q) (estar : Edge),
  Evec M h K (estar :: E) n p q - Evec M h K E n p q
  == (h * h * K) * (ediff p estar * ediff q estar).
Proof.
  intros E n p q M h K estar.
  unfold Evec, gform. simpl. ring.
Qed.

(* adding an edge across which the field is continuous is free *)
Corollary growth_energy_adiabatic :
  forall E n (p q : nat -> Q) (M h K : Q) (estar : Edge),
  ediff p estar == 0 ->
  Evec M h K (estar :: E) n p q == Evec M h K E n p q.
Proof.
  intros E n p q M h K estar Hd.
  assert (Hs := growth_energy_shift E n p q M h K estar).
  rewrite Hd in Hs.
  assert (Hz : (h * h * K) * (0 * ediff q estar) == 0) by ring.
  lra.
Qed.

(* ------------------------------------------------------------------ *)
(* PART III — ORDER COLLAPSE (RDL_CausalSignature.v conventions)       *)
(* ------------------------------------------------------------------ *)

Definition cmpb (prec : nat -> nat -> bool) (e : Edge) : bool :=
  (prec (fst e) (snd e) || prec (snd e) (fst e))%bool.

Definition csgn (prec : nat -> nat -> bool) (e : Edge) : Q :=
  if cmpb prec e then - (1) else 1.

Definition cform (E : list Edge) (prec : nat -> nat -> bool)
                 (x : nat -> Q) : Q :=
  esum E (fun e => csgn prec e * (ediff x e * ediff x e)).

(* a total order makes every edge comparable: the signed form          *)
(* degenerates to MINUS the positive form — no spacelike cone exists.  *)
(* Incomparability is what space is made of.                           *)
Theorem total_order_collapse : forall E prec (x : nat -> Q),
  (forall e, In e E -> cmpb prec e = true) ->
  cform E prec x == - gdiag E x.
Proof.
  intros E prec x Htot.
  unfold cform, gdiag.
  rewrite (esum_ext E (fun e => csgn prec e * (ediff x e * ediff x e))
                      (fun e => - (1) * (ediff x e * ediff x e)));
    [| intros e He; unfold csgn; rewrite (Htot e He); reflexivity].
  rewrite (esum_scale E (- (1)) (fun e => ediff x e * ediff x e)).
  ring.
Qed.

Corollary total_order_nonpos : forall E prec (x : nat -> Q),
  (forall e, In e E -> cmpb prec e = true) ->
  cform E prec x <= 0.
Proof.
  intros E prec x Htot.
  assert (Hc := total_order_collapse E prec x Htot).
  assert (Hg := gdiag_nonneg E x).
  lra.
Qed.

(* dually: no comparable edge at all recovers the plain positive form  *)
(* — the order-derived version of the "Euclidean reduction".           *)
Theorem incomparable_collapse : forall E prec (x : nat -> Q),
  (forall e, In e E -> cmpb prec e = false) ->
  cform E prec x == gdiag E x.
Proof.
  intros E prec x Hinc.
  unfold cform, gdiag.
  apply esum_ext. intros e He.
  unfold csgn. rewrite (Hinc e He). ring.
Qed.

(* ------------------------------------------------------------------ *)
(* PART IV — GROWTH vs SLOW MODES: the exact dilution identity         *)
(* ------------------------------------------------------------------ *)

(* natural numbers injected into Q *)
Definition qn (k : nat) : Q := inject_Z (Z.of_nat k).

Lemma qn_0 : qn 0 == 0.
Proof. reflexivity. Qed.

Lemma qn_S : forall k, qn (S k) = qn k + 1.
Proof.
  intro k. unfold qn.
  rewrite Nat2Z.inj_succ. rewrite <- Z.add_1_r.
  apply inject_Z_plus.
Qed.

Lemma qn_nonneg : forall k, 0 <= qn k.
Proof.
  induction k as [| j IH].
  - rewrite qn_0. lra.
  - rewrite qn_S. lra.
Qed.

Lemma qn_ge1 : forall k, (1 <= k)%nat -> 1 <= qn k.
Proof.
  intros k Hk. destruct k as [| j]; [lia |].
  rewrite qn_S. assert (H := qn_nonneg j). lra.
Qed.

(* constant sums and the two classical power sums, division-free *)
Lemma qsum_const : forall n (c : Q), qsum n (fun _ => c) == qn n * c.
Proof.
  induction n as [| m IH]; intro c; simpl.
  - rewrite qn_0. ring.
  - rewrite IH. rewrite qn_S. ring.
Qed.

Lemma sum_qn : forall n, 2 * qsum n qn == qn n * (qn n - 1).
Proof.
  induction n as [| m IH]; cbn [qsum].
  - rewrite qn_0. ring.
  - rewrite qn_S. lra.
Qed.

Lemma sum_qn2 : forall n,
  6 * qsum n (fun i => qn i * qn i) == qn n * (qn n - 1) * (2 * qn n - 1).
Proof.
  induction n as [| m IH]; cbn [qsum].
  - rewrite qn_0. ring.
  - rewrite qn_S.
    assert (IHt : qn m * (6 * qsum m (fun i => qn i * qn i))
                == qn m * (qn m * (qn m - 1) * (2 * qn m - 1)))
      by (rewrite IH; reflexivity).
    lra.
Qed.

(* the path graph on m+1 nodes: edges (k, k+1) for k < m *)
Fixpoint pathE (m : nat) : list Edge :=
  match m with
  | O => nil
  | S k => (k, S k) :: pathE k
  end.

(* any state with constant step -2 has edge form exactly 4m on pathE m *)
Lemma pathE_gdiag_const : forall m (x : nat -> Q),
  (forall k : nat, x k - x (S k) == - (2)) ->
  gdiag (pathE m) x == 4 * qn m.
Proof.
  induction m as [| k IH]; intros x H.
  - cbn [pathE]. unfold gdiag. simpl. rewrite qn_0. ring.
  - cbn [pathE]. rewrite gdiag_cons.
    assert (Hd : ediff x (k, S k) == - (2))
      by (unfold ediff; simpl; apply H).
    rewrite Hd. rewrite (IH x H). rewrite qn_S. ring.
Qed.

(* the mean-zero ramp on the m+1 nodes of pathE m *)
(* x_i := 2 i - m *)

Theorem ramp_mean_zero : forall m,
  qsum (S m) (fun i => 2 * qn i - qn m) == 0.
Proof.
  intro m.
  rewrite (qsum_sub (S m) (fun i => 2 * qn i) (fun _ => qn m)).
  rewrite (qsum_scale (S m) 2 qn).
  rewrite (qsum_const (S m) (qn m)).
  assert (H2 := sum_qn (S m)).
  rewrite qn_S in *.
  lra.
Qed.

Theorem ramp_form : forall m,
  gdiag (pathE m) (fun i => 2 * qn i - qn m) == 4 * qn m.
Proof.
  intro m.
  apply pathE_gdiag_const.
  intro k. rewrite qn_S. ring.
Qed.

Theorem ramp_norm2 : forall m,
  3 * qsum (S m) (fun i => (2 * qn i - qn m) * (2 * qn i - qn m))
  == qn (S m) * (qn (S m) * qn (S m) - 1).
Proof.
  intro m.
  assert (Hsplit : qsum (S m) (fun i => (2 * qn i - qn m) * (2 * qn i - qn m))
    == qsum (S m) (fun i => 4 * (qn i * qn i))
     + (qsum (S m) (fun i => (- (4 * qn m)) * qn i)
        + qsum (S m) (fun _ => qn m * qn m))).
  { rewrite <- (qsum_plus (S m) (fun i => (- (4 * qn m)) * qn i)
                            (fun _ => qn m * qn m)).
    rewrite <- (qsum_plus (S m) (fun i => 4 * (qn i * qn i))
                            (fun i => (- (4 * qn m)) * qn i + qn m * qn m)).
    apply qsum_ext. intros i _. ring. }
  rewrite Hsplit.
  rewrite (qsum_scale (S m) 4 (fun i => qn i * qn i)).
  rewrite (qsum_scale (S m) (- (4 * qn m)) qn).
  rewrite (qsum_const (S m) (qn m * qn m)).
  assert (H6 := sum_qn2 (S m)).
  assert (H2 := sum_qn (S m)).
  assert (H2t : qn m * (2 * qsum (S m) qn)
              == qn m * (qn (S m) * (qn (S m) - 1)))
    by (rewrite H2; reflexivity).
  rewrite qn_S in *.
  lra.
Qed.

(* THE DILUTION IDENTITY, division-free:                               *)
(*   n(n+1) * form == 12 * norm2 ,  n = m+1                            *)
(* i.e. the mean-zero ramp has Rayleigh quotient EXACTLY 12/(n(n+1)):  *)
(* the growing path supports states of arbitrarily small quotient.     *)
Theorem ramp_dilution : forall m,
  qn (S m) * (qn (S m) + 1)
    * gdiag (pathE m) (fun i => 2 * qn i - qn m)
  == 12 * qsum (S m) (fun i => (2 * qn i - qn m) * (2 * qn i - qn m)).
Proof.
  intro m.
  rewrite ramp_form.
  assert (H3 := ramp_norm2 m).
  assert (H12 : 4 * (3 * qsum (S m)
                  (fun i => (2 * qn i - qn m) * (2 * qn i - qn m)))
              == 4 * (qn (S m) * (qn (S m) * qn (S m) - 1)))
    by (rewrite H3; reflexivity).
  rewrite qn_S in *.
  lra.
Qed.

(* the witness is nondegenerate for every m >= 1 *)
Theorem ramp_norm2_pos : forall m,
  (1 <= m)%nat ->
  0 < qsum (S m) (fun i => (2 * qn i - qn m) * (2 * qn i - qn m)).
Proof.
  intros m Hm. cbn [qsum].
  assert (Hfm : (2 * qn m - qn m) * (2 * qn m - qn m) == qn m * qn m)
    by ring.
  assert (Hrest : 0 <= qsum m (fun i => (2 * qn i - qn m) * (2 * qn i - qn m)))
    by (apply qsum_nonneg; intros i _; apply sq_nonneg).
  assert (Hq1 : 1 <= qn m) by (apply qn_ge1; exact Hm).
  assert (Hqq : 1 * qn m <= qn m * qn m)
    by (apply Qmult_le_compat_r; lra).
  lra.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions forman_growth_shift.
Print Assumptions forman_growth_monotone.
Print Assumptions forman_growth_strict.
Print Assumptions growth_energy_shift.
Print Assumptions growth_energy_adiabatic.
Print Assumptions total_order_collapse.
Print Assumptions total_order_nonpos.
Print Assumptions incomparable_collapse.
Print Assumptions ramp_mean_zero.
Print Assumptions ramp_form.
Print Assumptions ramp_norm2.
Print Assumptions ramp_dilution.
Print Assumptions ramp_norm2_pos.

End GraphGrowth.
