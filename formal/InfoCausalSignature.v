(* ===================================================================== *)
(*  RDL_CausalSignature.v                                                  *)
(*  SIGNED QUADRATIC STRUCTURE induced on a graph BY a binary order        *)
(*  relation — the sign of every edge is CONSTRUCTED from the relation's   *)
(*  comparability, never taken as a free parameter.  Entirely over Q.      *)
(*                                                                         *)
(*  Construction:  given  prec : nat -> nat -> bool  (intended reading:    *)
(*  a strict causal order), an edge is COMPARABLE when prec holds in       *)
(*  either direction; comparable edges receive sign -1, incomparable       *)
(*  edges sign +1.  The signed form is                                     *)
(*      cform E prec x  :=  sum_e  csgn(e) * (ediff x e)^2 .               *)
(*                                                                         *)
(*  CLAIMED HERE (candidate for coqc 8.18.0, axiom-free target):           *)
(*    csgn_flip / term_orientation_invariant                               *)
(*        the sign and every form term are invariant under reversing an    *)
(*        edge's stored orientation: the form depends only on the          *)
(*        UNDERLYING graph and the relation (this is the correct           *)
(*        invariance statement; list-permutation invariance is weaker)     *)
(*    cform_split                                                          *)
(*        for EVERY graph and EVERY relation:                              *)
(*          cform == gdiag(incomparable edges) - gdiag(comparable edges),  *)
(*        an exact decomposition into a DIFFERENCE OF TWO POSITIVE         *)
(*        SEMIDEFINITE forms, with the split dictated by the relation      *)
(*    timelike_nonpos / spacelike_nonneg                                   *)
(*        the two cone inequalities: states whose incomparable-edge        *)
(*        differences vanish have cform <= 0; states whose comparable-     *)
(*        edge differences vanish have cform >= 0                          *)
(*    minkowski_cell                                                       *)
(*        concrete star cell (center 0; one comparable edge 0-1; three     *)
(*        incomparable edges 0-2, 0-3, 0-4):  the form diagonalizes        *)
(*        EXACTLY over Q as                                                *)
(*          - (x1-x0)^2 + (x2-x0)^2 + (x3-x0)^2 + (x4-x0)^2               *)
(*        — a rational congruence witness of type (1,3)                    *)
(*    cell_indefinite                                                      *)
(*        explicit witnesses: the cell form takes the value -1 on a        *)
(*        comparable-direction bump and +1 on an incomparable-direction    *)
(*        bump — genuinely indefinite, with the negative direction being   *)
(*        exactly the comparable (causal) one                              *)
(*    lightcone_factor                                                     *)
(*        - a^2 + b^2 == (b - a) * (b + a):  the 1+1 normal form factors   *)
(*        through null coordinates (pure ring identity)                    *)
(*                                                                         *)
(*  HONESTLY NOT CLAIMED (remain open):  global uniqueness / maximal       *)
(*  dimension of the negative part for a general relation (i.e. WHY        *)
(*  exactly one independent comparable direction — that is genuine         *)
(*  physical content, not closed here), and any boost-type transformation  *)
(*  group (imported wherever it is used, as before).                       *)
(*                                                                         *)
(*  Pre-verified with exact rational arithmetic (300 random               *)
(*  graph/relation/state triples for the split; constructed cone states;   *)
(*  200 random states on the star cell) before authoring.                  *)
(*  Expected: Print Assumptions => Closed under the global context.        *)
(* ===================================================================== *)

Require Coq.Arith.PeanoNat.
Require Coq.Bool.Bool.
Require Coq.Lists.List.
Require Coq.QArith.QArith.
Require Coq.micromega.Lia.
Require Coq.micromega.Lqa.

Module CausalSignature.

Import Coq.Lists.List. Import ListNotations.
Import Coq.Arith.PeanoNat.
Import Coq.Bool.Bool.
Import Coq.QArith.QArith.
Import Coq.micromega.Lia.
Import Coq.micromega.Lqa.
Local Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(* Graph data (shared conventions; self-contained for standalone coqc) *)
(* ------------------------------------------------------------------ *)

Definition Edge : Type := (nat * nat)%type.

Definition esum (E : list Edge) (g : Edge -> Q) : Q :=
  fold_right (fun e acc => g e + acc) 0 E.

Definition ediff (x : nat -> Q) (e : Edge) : Q := x (fst e) - x (snd e).

(* comparability of an edge under the relation *)
Definition cmpb (prec : nat -> nat -> bool) (e : Edge) : bool :=
  (prec (fst e) (snd e) || prec (snd e) (fst e))%bool.

(* the sign CONSTRUCTED from the relation: comparable -> -1, else +1 *)
Definition csgn (prec : nat -> nat -> bool) (e : Edge) : Q :=
  if cmpb prec e then - (1) else 1.

Definition cform (E : list Edge) (prec : nat -> nat -> bool)
                 (x : nat -> Q) : Q :=
  esum E (fun e => csgn prec e * (ediff x e * ediff x e)).

(* the plain (positive semidefinite) edge form *)
Definition gdiag (E : list Edge) (x : nat -> Q) : Q :=
  esum E (fun e => ediff x e * ediff x e).

Definition timeE (prec : nat -> nat -> bool) (E : list Edge) : list Edge :=
  filter (cmpb prec) E.

Definition spaceE (prec : nat -> nat -> bool) (E : list Edge) : list Edge :=
  filter (fun e => negb (cmpb prec e)) E.

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

Lemma esum_ext : forall E (f g : Edge -> Q),
  (forall e, In e E -> f e == g e) ->
  esum E f == esum E g.
Proof.
  induction E as [| e r IH]; intros f g H; simpl.
  - reflexivity.
  - rewrite (H e); [| left; reflexivity].
    rewrite (IH f g); [reflexivity | intros e' He'; apply H; right; exact He'].
Qed.

Lemma esum_zero : forall E, esum E (fun _ => 0) == 0.
Proof.
  induction E as [| e r IH]; simpl; [reflexivity | rewrite IH; ring].
Qed.

Lemma esum_sub : forall E (f g : Edge -> Q),
  esum E (fun e => f e - g e) == esum E f - esum E g.
Proof.
  induction E as [| e r IH]; intros f g; simpl; [ring | rewrite IH; ring].
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

(* esum over a filtered list = esum with an indicator *)
Lemma esum_filter : forall E (f : Edge -> bool) (g : Edge -> Q),
  esum (filter f E) g == esum E (fun e => if f e then g e else 0).
Proof.
  induction E as [| e r IH]; intros f g; simpl.
  - reflexivity.
  - destruct (f e); simpl; rewrite IH; ring.
Qed.

(* ------------------------------------------------------------------ *)
(* Orientation invariance: the sign and every form term depend only    *)
(* on the UNDERLYING edge, not on its stored orientation.              *)
(* ------------------------------------------------------------------ *)

Lemma csgn_flip : forall prec (u v : nat),
  csgn prec (u, v) == csgn prec (v, u).
Proof.
  intros prec u v. unfold csgn, cmpb. simpl.
  rewrite orb_comm. reflexivity.
Qed.

Theorem term_orientation_invariant : forall prec (x : nat -> Q) (u v : nat),
  csgn prec (u, v) * (ediff x (u, v) * ediff x (u, v))
  == csgn prec (v, u) * (ediff x (v, u) * ediff x (v, u)).
Proof.
  intros prec x u v.
  rewrite (csgn_flip prec u v).
  unfold ediff. simpl. ring.
Qed.

(* ------------------------------------------------------------------ *)
(* THE SPLIT THEOREM: for EVERY graph and EVERY relation, the signed   *)
(* form is EXACTLY the difference of two positive semidefinite forms,  *)
(* the split dictated by comparability.                                *)
(* ------------------------------------------------------------------ *)

Theorem cform_split : forall E prec (x : nat -> Q),
  cform E prec x == gdiag (spaceE prec E) x - gdiag (timeE prec E) x.
Proof.
  intros E prec x.
  unfold cform, gdiag, spaceE, timeE.
  rewrite (esum_filter E (fun e => negb (cmpb prec e))
                         (fun e => ediff x e * ediff x e)).
  rewrite (esum_filter E (cmpb prec)
                         (fun e => ediff x e * ediff x e)).
  rewrite <- esum_sub.
  apply esum_ext. intros e _.
  unfold csgn. destruct (cmpb prec e); simpl; ring.
Qed.

Theorem gdiag_nonneg : forall E x, 0 <= gdiag E x.
Proof.
  intros E x. unfold gdiag.
  apply esum_nonneg. intros e _. apply sq_nonneg.
Qed.

(* ------------------------------------------------------------------ *)
(* THE TWO CONES.                                                      *)
(* ------------------------------------------------------------------ *)

(* states with vanishing incomparable-edge differences: cform <= 0 *)
Theorem timelike_nonpos : forall E prec (x : nat -> Q),
  (forall e, In e E -> cmpb prec e = false -> ediff x e == 0) ->
  cform E prec x <= 0.
Proof.
  intros E prec x Hsp.
  assert (Hsplit := cform_split E prec x).
  assert (Hzero : gdiag (spaceE prec E) x == 0).
  { unfold gdiag, spaceE.
    rewrite (esum_ext (filter (fun e => negb (cmpb prec e)) E)
              (fun e => ediff x e * ediff x e) (fun _ => 0));
      [apply esum_zero |].
    intros e He.
    apply filter_In in He. destruct He as [HinE Hneg].
    apply negb_true_iff in Hneg.
    rewrite (Hsp e HinE Hneg). ring. }
  assert (Hpos := gdiag_nonneg (timeE prec E) x).
  lra.
Qed.

(* states with vanishing comparable-edge differences: cform >= 0 *)
Theorem spacelike_nonneg : forall E prec (x : nat -> Q),
  (forall e, In e E -> cmpb prec e = true -> ediff x e == 0) ->
  0 <= cform E prec x.
Proof.
  intros E prec x Hti.
  assert (Hsplit := cform_split E prec x).
  assert (Hzero : gdiag (timeE prec E) x == 0).
  { unfold gdiag, timeE.
    rewrite (esum_ext (filter (cmpb prec) E)
              (fun e => ediff x e * ediff x e) (fun _ => 0));
      [apply esum_zero |].
    intros e He.
    apply filter_In in He. destruct He as [HinE Hcmp].
    rewrite (Hti e HinE Hcmp). ring. }
  assert (Hpos := gdiag_nonneg (spaceE prec E) x).
  lra.
Qed.

(* ------------------------------------------------------------------ *)
(* THE CONCRETE (1,3) CELL: center 0; the relation holds ONLY on the   *)
(* pair (0,1); edges to 2, 3, 4 are incomparable.  The form            *)
(* diagonalizes EXACTLY over Q with signature pattern (-,+,+,+).       *)
(* ------------------------------------------------------------------ *)

Definition prec14 (u v : nat) : bool :=
  (Nat.eqb u 0 && Nat.eqb v 1)%bool.

Definition E14 : list Edge :=
  (0%nat, 1%nat) :: (0%nat, 2%nat) :: (0%nat, 3%nat) :: (0%nat, 4%nat) :: nil.

Theorem minkowski_cell : forall x : nat -> Q,
  cform E14 prec14 x
  == - ((x 1%nat - x 0%nat) * (x 1%nat - x 0%nat))
     + (x 2%nat - x 0%nat) * (x 2%nat - x 0%nat)
     + (x 3%nat - x 0%nat) * (x 3%nat - x 0%nat)
     + (x 4%nat - x 0%nat) * (x 4%nat - x 0%nat).
Proof.
  intro x.
  unfold cform, E14, csgn, cmpb, prec14, ediff. simpl. ring.
Qed.

(* explicit indefiniteness witnesses: a comparable-direction bump and  *)
(* an incomparable-direction bump                                      *)
Definition bump1 (i : nat) : Q := if Nat.eqb i 1 then 1 else 0.
Definition bump2 (i : nat) : Q := if Nat.eqb i 2 then 1 else 0.

Theorem cell_indefinite :
  cform E14 prec14 bump1 < 0 /\ 0 < cform E14 prec14 bump2.
Proof.
  assert (H1 : cform E14 prec14 bump1 == - (1)).
  { unfold cform, E14, csgn, cmpb, prec14, ediff, bump1. simpl. ring. }
  assert (H2 : cform E14 prec14 bump2 == 1).
  { unfold cform, E14, csgn, cmpb, prec14, ediff, bump2. simpl. ring. }
  split; lra.
Qed.

(* the 1+1 normal form factors through null coordinates *)
Theorem lightcone_factor : forall a b : Q,
  - (a * a) + b * b == (b - a) * (b + a).
Proof. intros. ring. Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions term_orientation_invariant.
Print Assumptions cform_split.
Print Assumptions timelike_nonpos.
Print Assumptions spacelike_nonneg.
Print Assumptions minkowski_cell.
Print Assumptions cell_indefinite.
Print Assumptions lightcone_factor.

End CausalSignature.
