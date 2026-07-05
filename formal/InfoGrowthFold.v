(* ===================================================================== *)
(*  RDL_GrowthFold.v          (repo namespace: rename Info* mechanically)  *)
(*  THE CUMULATIVE LAW OF CURVATURE UNDER A RETENTION SEQUENCE —           *)
(*  adding ANY list of edges shifts every edge's curvature by EXACTLY      *)
(*  the accumulated share sum, and never upward.  Entirely over Q.         *)
(*                                                                        *)
(*  This is the missing fold of RDL_GraphGrowth.forman_growth_shift:       *)
(*  the single-step law iterates to an exact closed form over an           *)
(*  arbitrary growth sequence Es (order-independent, since the shift       *)
(*  is a sum).  Together with the retention criterion                      *)
(*  (RDL_ActionStationarity / RDL_CurvatureBalance) this closes the        *)
(*  Th-side of the chain                                                   *)
(*      retention -> growth -> curvature                                   *)
(*  with no seams: which edges are retained is the balance law; what       *)
(*  retention does to curvature is THIS file; both exact.                  *)
(*                                                                        *)
(*  CLAIMED HERE (candidate for coqc 8.18.0, axiom-free target):           *)
(*    deg_app                   degree accumulates additively over the     *)
(*                              retained list (exact)                      *)
(*    deg_monotone_app          degree never decreases under retention     *)
(*    forman_fold               forman (Es ++ E) e                         *)
(*                                == forman E e - ssum Es e     (exact),   *)
(*                              ssum = the accumulated share sum           *)
(*    ssum_nonneg               the accumulated shift is nonnegative       *)
(*    curvature_antitone_growth retention only bends curvature DOWNWARD:   *)
(*                              forman (Es ++ E) e <= forman E e, for      *)
(*                              every edge, every growth list              *)
(*                                                                        *)
(*  HONESTLY NOT CLAIMED: anything about WHICH edges get retained          *)
(*  (that is the balance law's job), and any physical reading of the       *)
(*  monotone descent (that lives in the manuscript at its own tier).       *)
(*                                                                        *)
(*  Pre-verified with exact rationals (300 random graph/growth-list        *)
(*  draws; fold, antitonicity, and degree accumulation checked             *)
(*  exactly).  Expected: Print Assumptions => Closed.                      *)
(* ===================================================================== *)

Require Coq.Arith.PeanoNat.
Require Coq.Lists.List.
Require Coq.QArith.QArith.
Require Coq.micromega.Lqa.

Module GrowthFold.

Import Coq.Lists.List. Import ListNotations.
Import Coq.Arith.PeanoNat.
Import Coq.QArith.QArith.
Import Coq.micromega.Lqa.
Local Open Scope Q_scope.

Definition Edge : Type := (nat * nat)%type.

Definition esum (E : list Edge) (g : Edge -> Q) : Q :=
  fold_right (fun e acc => g e + acc) 0 E.

Definition share (e : Edge) (i : nat) : Q :=
  (if Nat.eqb (fst e) i then 1 else 0) + (if Nat.eqb (snd e) i then 1 else 0).

Definition deg (E : list Edge) (i : nat) : Q := esum E (fun e => share e i).

Definition forman (E : list Edge) (e : Edge) : Q :=
  4 - deg E (fst e) - deg E (snd e).

(* the accumulated shift of one edge's curvature over a growth list *)
Definition ssum (Es : list Edge) (e : Edge) : Q :=
  esum Es (fun estar => share estar (fst e) + share estar (snd e)).

(* ------------------------------------------------------------------ *)
(* Toolbox                                                             *)
(* ------------------------------------------------------------------ *)

Lemma esum_app : forall (a b : list Edge) (g : Edge -> Q),
  esum (a ++ b) g == esum a g + esum b g.
Proof.
  induction a as [| e r IH]; intros b g; simpl.
  - ring.
  - rewrite (IH b g). ring.
Qed.

Lemma esum_plus : forall E (f g : Edge -> Q),
  esum E (fun e => f e + g e) == esum E f + esum E g.
Proof.
  induction E as [| e r IH]; intros f g; simpl; [ring | rewrite IH; ring].
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
(* DEGREE ACCUMULATION                                                 *)
(* ------------------------------------------------------------------ *)

Theorem deg_app : forall (Es E : list Edge) (i : nat),
  deg (Es ++ E) i == esum Es (fun e => share e i) + deg E i.
Proof.
  intros Es E i. unfold deg. apply esum_app.
Qed.

Theorem deg_monotone_app : forall (Es E : list Edge) (i : nat),
  deg E i <= deg (Es ++ E) i.
Proof.
  intros Es E i.
  assert (Ha := deg_app Es E i).
  assert (Hn : 0 <= esum Es (fun e => share e i))
    by (apply esum_nonneg; intros e _; apply share_nonneg).
  lra.
Qed.

(* ------------------------------------------------------------------ *)
(* THE FOLD                                                            *)
(* ------------------------------------------------------------------ *)

Theorem forman_fold : forall (Es E : list Edge) (e : Edge),
  forman (Es ++ E) e == forman E e - ssum Es e.
Proof.
  intros Es E e. unfold forman, ssum.
  assert (H1 := deg_app Es E (fst e)).
  assert (H2 := deg_app Es E (snd e)).
  assert (Hp := esum_plus Es (fun estar => share estar (fst e))
                             (fun estar => share estar (snd e))).
  cbv beta in Hp.
  lra.
Qed.

Theorem ssum_nonneg : forall (Es : list Edge) (e : Edge),
  0 <= ssum Es e.
Proof.
  intros Es e. unfold ssum.
  apply esum_nonneg. intros estar _.
  assert (H1 := share_nonneg estar (fst e)).
  assert (H2 := share_nonneg estar (snd e)).
  lra.
Qed.

(* retention only bends curvature downward *)
Theorem curvature_antitone_growth : forall (Es E : list Edge) (e : Edge),
  forman (Es ++ E) e <= forman E e.
Proof.
  intros Es E e.
  assert (Hf := forman_fold Es E e).
  assert (Hn := ssum_nonneg Es e).
  lra.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions deg_app.
Print Assumptions deg_monotone_app.
Print Assumptions forman_fold.
Print Assumptions ssum_nonneg.
Print Assumptions curvature_antitone_growth.

End GrowthFold.
