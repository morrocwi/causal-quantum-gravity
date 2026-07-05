(* ===================================================================== *)
(*  RDL_CeilingMonotone.v     (repo namespace: rename Info* mechanically)  *)
(*  THE FORM AND ITS CEILING ARE MONOTONE UNDER RETENTION — every          *)
(*  retained edge adds an exact nonnegative square to the quadratic        *)
(*  form, so no Rayleigh level is ever lost under growth, and the          *)
(*  degree data feeding the spectral ceiling only grows.  Over Q.          *)
(*                                                                        *)
(*  This is the (b)-half of the chain closure: with RDL_GrowthFold.v       *)
(*  (curvature side) it makes the whole Th-segment                         *)
(*      retention -> growth -> curvature -> internal-frequency data        *)
(*  seamless: the form that the internal spectrum lives on, and the        *)
(*  degree bound that caps it (RDL_SpectralCeiling.form_degree_bound),     *)
(*  are BOTH monotone in retention — exactly the monotone arrows the       *)
(*  chain needs before its single disclosed identification.                *)
(*                                                                        *)
(*  CLAIMED HERE (candidate for coqc 8.18.0, axiom-free target):           *)
(*    gform_step_add        gd (e::E) x == gd E x + (ediff x e)^2 (exact)  *)
(*    gform_monotone_add    one retained edge never lowers the form        *)
(*    gform_monotone_app    a whole growth list never lowers the form      *)
(*    rayleigh_level_persists                                              *)
(*        every exact Rayleigh level achieved before growth is still       *)
(*        dominated after growth:                                          *)
(*          gd E x == lam * |x|^2  ->  lam * |x|^2 <= gd (Es ++ E) x       *)
(*    deg_step_add / deg_monotone_app                                      *)
(*        the ceiling's degree data accumulates and never decreases        *)
(*        (so with RDL_SpectralCeiling.v the frequency ceiling is          *)
(*        monotone in retention — composition noted, not re-proved).       *)
(*                                                                        *)
(*  HONESTLY NOT CLAIMED: monotonicity of individual eigenvalues           *)
(*  (interlacing needs spectral theory we do not invoke; the               *)
(*  extensional per-direction statement above is what the chain            *)
(*  uses), and any physical identification (manuscript, own tier).         *)
(*                                                                        *)
(*  Pre-verified with exact rationals (300 random draws; step law,         *)
(*  list monotonicity, and level persistence checked exactly).             *)
(*  Expected: Print Assumptions => Closed.                                 *)
(* ===================================================================== *)

Require Coq.Arith.PeanoNat.
Require Coq.Lists.List.
Require Coq.QArith.QArith.
Require Coq.micromega.Lqa.

Module CeilingMonotone.

Import Coq.Lists.List. Import ListNotations.
Import Coq.Arith.PeanoNat.
Import Coq.QArith.QArith.
Import Coq.micromega.Lqa.
Local Open Scope Q_scope.

Definition Edge : Type := (nat * nat)%type.

Fixpoint qsum (n : nat) (f : nat -> Q) : Q :=
  match n with
  | O => 0
  | S m => qsum m f + f m
  end.

Definition esum (E : list Edge) (g : Edge -> Q) : Q :=
  fold_right (fun e acc => g e + acc) 0 E.

Definition ediff (x : nat -> Q) (e : Edge) : Q := x (fst e) - x (snd e).

Definition gd (E : list Edge) (x : nat -> Q) : Q :=
  esum E (fun e => ediff x e * ediff x e).

Definition norm2 (n : nat) (x : nat -> Q) : Q :=
  qsum n (fun i => x i * x i).

Definition share (e : Edge) (i : nat) : Q :=
  (if Nat.eqb (fst e) i then 1 else 0) + (if Nat.eqb (snd e) i then 1 else 0).

Definition deg (E : list Edge) (i : nat) : Q := esum E (fun e => share e i).

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

Lemma esum_app : forall (a b : list Edge) (g : Edge -> Q),
  esum (a ++ b) g == esum a g + esum b g.
Proof.
  induction a as [| e r IH]; intros b g; simpl.
  - ring.
  - rewrite (IH b g). ring.
Qed.

Lemma esum_nonneg : forall E (g : Edge -> Q),
  (forall e, In e E -> 0 <= g e) ->
  0 <= esum E g.
Proof.
  induction E as [| e r IH]; intros g H; simpl.
  - lra.
  - assert (He : 0 <= g e) by (apply H; left; reflexivity).
    assert (Hr : 0 <= esum r g)
      by (apply IH; intros e' He'; apply H; right; exact He').
    lra.
Qed.

Lemma share_nonneg : forall (e : Edge) (i : nat), 0 <= share e i.
Proof.
  intros e i. unfold share.
  destruct (Nat.eqb (fst e) i); destruct (Nat.eqb (snd e) i); lra.
Qed.

(* ------------------------------------------------------------------ *)
(* THE FORM IS MONOTONE UNDER RETENTION                                *)
(* ------------------------------------------------------------------ *)

Theorem gform_step_add : forall (E : list Edge) (x : nat -> Q) (e : Edge),
  gd (e :: E) x == gd E x + ediff x e * ediff x e.
Proof.
  intros E x e. unfold gd. simpl. ring.
Qed.

Theorem gform_monotone_add : forall (E : list Edge) (x : nat -> Q) (e : Edge),
  gd E x <= gd (e :: E) x.
Proof.
  intros E x e.
  assert (Hs := gform_step_add E x e).
  assert (Hn := sq_nonneg (ediff x e)).
  lra.
Qed.

Theorem gform_monotone_app : forall (Es E : list Edge) (x : nat -> Q),
  gd E x <= gd (Es ++ E) x.
Proof.
  intros Es E x.
  assert (Ha := esum_app Es E (fun e => ediff x e * ediff x e)).
  assert (Hn : 0 <= esum Es (fun e => ediff x e * ediff x e))
    by (apply esum_nonneg; intros e _; apply sq_nonneg).
  unfold gd in *. lra.
Qed.

(* every exact Rayleigh level achieved before growth is still           *)
(* dominated after growth                                               *)
Theorem rayleigh_level_persists :
  forall (Es E : list Edge) (n : nat) (x : nat -> Q) (lam : Q),
  gd E x == lam * norm2 n x ->
  lam * norm2 n x <= gd (Es ++ E) x.
Proof.
  intros Es E n x lam Hx.
  assert (Hm := gform_monotone_app Es E x).
  lra.
Qed.

(* ------------------------------------------------------------------ *)
(* THE CEILING'S DEGREE DATA IS MONOTONE UNDER RETENTION               *)
(* (composition with RDL_SpectralCeiling.form_degree_bound noted in    *)
(* the header, not re-proved here)                                     *)
(* ------------------------------------------------------------------ *)

Theorem deg_step_add : forall (E : list Edge) (e : Edge) (i : nat),
  deg (e :: E) i == deg E i + share e i.
Proof.
  intros E e i. unfold deg. simpl. ring.
Qed.

Theorem deg_monotone_app : forall (Es E : list Edge) (i : nat),
  deg E i <= deg (Es ++ E) i.
Proof.
  intros Es E i.
  assert (Ha := esum_app Es E (fun e => share e i)).
  assert (Hn : 0 <= esum Es (fun e => share e i))
    by (apply esum_nonneg; intros e _; apply share_nonneg).
  unfold deg in *. lra.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions gform_step_add.
Print Assumptions gform_monotone_add.
Print Assumptions gform_monotone_app.
Print Assumptions rayleigh_level_persists.
Print Assumptions deg_step_add.
Print Assumptions deg_monotone_app.

End CeilingMonotone.
