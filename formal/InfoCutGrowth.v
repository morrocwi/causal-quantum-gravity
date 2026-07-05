(* ===================================================================== *)
(*  InfoCutGrowth.v                                                       *)
(*  THE SCREEN-GROWTH LEDGER: EXACT CUT BOOKKEEPING AND ITS PRICE.        *)
(*                                                                        *)
(*  For a region given by a node list A, the cut count of an edge list    *)
(*  is an exact sum of crossing indicators.  Theorems:                    *)
(*                                                                        *)
(*    cut_append_exact    one retention step changes the cut by exactly   *)
(*                        its crossing indicator (0 or 1)                 *)
(*    cut_concat_exact    a whole retention history adds exactly its own  *)
(*                        crossing count (order-free, telescoped)         *)
(*    cut_monotone        appended history never shrinks the cut          *)
(*    priced_screen_growth  if every retained edge satisfies the balance  *)
(*                        (strain <= benefit), then the TOTAL STRAIN      *)
(*                        ADMITTED ACROSS THE SCREEN by the new edges is  *)
(*                        bounded by the TOTAL BENEFIT GRANTED THERE ---  *)
(*                        screen growth is priced, edge by edge.          *)
(*                                                                        *)
(*  This is the static half of the discrete Raychaudhuri slot (the        *)
(*  named continuum engine inside horizon thermodynamics; registered).    *)
(*  HONESTLY NOT CLAIMED: any rate law for the cut under the dynamics,    *)
(*  and any focusing statement; those remain open.                        *)
(*  Expected: Print Assumptions => Closed under the global context.       *)
(* ===================================================================== *)

Require Coq.Arith.PeanoNat.
Require Coq.Lists.List.
Require Coq.QArith.QArith.
Require Coq.micromega.Lqa.

Module CutGrowth.

Import Coq.Lists.List. Import ListNotations.
Import Coq.Arith.PeanoNat.
Import Coq.QArith.QArith.
Import Coq.micromega.Lqa.
Local Open Scope Q_scope.

Definition Edge : Type := (nat * nat)%type.

Definition esum (E : list Edge) (h : Edge -> Q) : Q :=
  fold_right (fun e acc => h e + acc) 0 E.

Fixpoint inb (i : nat) (A : list nat) : bool :=
  match A with
  | [] => false
  | a :: r => orb (Nat.eqb a i) (inb i r)
  end.

Definition crossb (A : list nat) (e : Edge) : bool :=
  xorb (inb (fst e) A) (inb (snd e) A).

Definition cutQ (A : list nat) (E : list Edge) : Q :=
  esum E (fun e => if crossb A e then 1 else 0).

(* ------------------------------------------------------------------ *)
(* Toolbox                                                             *)
(* ------------------------------------------------------------------ *)

Lemma esum_app : forall (E1 E2 : list Edge) (h : Edge -> Q),
  esum (E1 ++ E2) h == esum E1 h + esum E2 h.
Proof.
  induction E1 as [| e r IH]; intros E2 h; simpl; [ring | rewrite IH; ring].
Qed.

Lemma esum_nonneg : forall (E : list Edge) (h : Edge -> Q),
  (forall e, In e E -> 0 <= h e) ->
  0 <= esum E h.
Proof.
  induction E as [| e r IH]; intros h H; simpl.
  - lra.
  - assert (H1 : 0 <= h e) by (apply H; left; reflexivity).
    assert (H2 : 0 <= esum r h)
      by (apply IH; intros e' He'; apply H; right; exact He').
    lra.
Qed.

Lemma esum_le : forall (E : list Edge) (f h : Edge -> Q),
  (forall e, In e E -> f e <= h e) ->
  esum E f <= esum E h.
Proof.
  induction E as [| e r IH]; intros f h H; simpl.
  - lra.
  - assert (H1 : f e <= h e) by (apply H; left; reflexivity).
    assert (H2 : esum r f <= esum r h)
      by (apply IH; intros e' He'; apply H; right; exact He').
    lra.
Qed.

(* ------------------------------------------------------------------ *)
(* Exact bookkeeping                                                   *)
(* ------------------------------------------------------------------ *)

Theorem cut_append_exact : forall (A : list nat) (E : list Edge) (e : Edge),
  cutQ A (e :: E) == (if crossb A e then 1 else 0) + cutQ A E.
Proof. intros A E e. unfold cutQ. simpl. reflexivity. Qed.

Theorem cut_concat_exact : forall (A : list nat) (Es E : list Edge),
  cutQ A (Es ++ E) == cutQ A Es + cutQ A E.
Proof. intros A Es E. unfold cutQ. apply esum_app. Qed.

Theorem cut_monotone : forall (A : list nat) (Es E : list Edge),
  cutQ A E <= cutQ A (Es ++ E).
Proof.
  intros A Es E. rewrite (cut_concat_exact A Es E).
  assert (H : 0 <= cutQ A Es).
  { unfold cutQ. apply esum_nonneg. intros e _.
    destruct (crossb A e); lra. }
  lra.
Qed.

(* ------------------------------------------------------------------ *)
(* THE PRICE OF SCREEN GROWTH                                          *)
(* ------------------------------------------------------------------ *)

Theorem priced_screen_growth :
  forall (A : list nat) (Es : list Edge) (strain bene : Edge -> Q),
  (forall e, In e Es -> strain e <= bene e) ->
  (forall e, In e Es -> 0 <= strain e) ->
  esum Es (fun e => if crossb A e then strain e else 0)
  <= esum Es (fun e => if crossb A e then bene e else 0).
Proof.
  intros A Es strain bene Hbal Hnn.
  apply esum_le. intros e He.
  destruct (crossb A e).
  - apply Hbal; exact He.
  - lra.
Qed.

(* benefit granted at the screen also dominates nothing-from-nothing:  *)
(* the admitted strain across the screen is itself nonnegative          *)
Theorem screen_strain_nonneg :
  forall (A : list nat) (Es : list Edge) (strain : Edge -> Q),
  (forall e, In e Es -> 0 <= strain e) ->
  0 <= esum Es (fun e => if crossb A e then strain e else 0).
Proof.
  intros A Es strain Hnn.
  apply esum_nonneg. intros e He.
  destruct (crossb A e); [apply Hnn; exact He | lra].
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions cut_append_exact.
Print Assumptions cut_concat_exact.
Print Assumptions cut_monotone.
Print Assumptions priced_screen_growth.
Print Assumptions screen_strain_nonneg.

End CutGrowth.
