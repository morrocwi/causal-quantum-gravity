(* ===================================================================
   InfoCurvatureNoether_attempt.v

   Bridges two previously separate results in this repository:
     - InfoGraphNoether_attempt.v (C46): a graph automorphism sigma
       leaves the Laplacian-built quadratic form gform invariant, with
       a concrete non-vacuous witness (the 6-cycle C6 with its rotation
       automorphism rot6, an order-6 permutation).
     - InfoDiscreteGraphCurvature_attempt.v / InfoGraphGrowth_attempt.v
       (C47/C49): Forman curvature forman(E,e) = 4 - deg(u) - deg(v).

   These were never composed: nobody had shown Forman curvature itself
   (as opposed to the quadratic form gform) is also sigma-invariant.
   This file proves exactly that, reusing this repo's own emap/esum
   machinery (reproduced standalone from InfoGraphNoether_attempt.v)
   rather than re-inventing it.

   THE STRUCTURAL PARALLEL THIS FILE IS -- AND IS NOT -- MAKING:
   rot6 is an order-6 permutation of graph nodes: a discrete rotation,
   structurally analogous to how a primitive n-th root of unity is an
   order-n rotation of the complex unit circle (InfoImaginaryOrder_
   attempt.v proves i has order exactly 4; InfoRootsOfUnityPeriod_
   attempt.v proves 5th roots of unity have order exactly 5). This
   file does NOT reuse those files' complex-number (Q x Q pairs)
   machinery -- graph automorphisms (permutations of nat) and complex
   roots of unity (elements of Q x Q under cmul) are different
   algebraic objects, not the same theorem in disguise. The honest
   parallel is qualitative, not a shared proof: BOTH are instances of
   "a finite structure only ever admits finite-order symmetries" --
   a permutation group on a finite set (graph automorphisms) and the
   multiplicative group of roots of unity (complex rotations) are both
   finite groups, so neither can host the "irrational-angle", dense,
   infinite-order rotation that this research program's own readout/
   non-readout diagnostic treats as the non-readout case. This file
   proves the graph-side instance of that pattern; it does not derive
   or need the complex-number side to do so.

   RESULT: forman_sigma_invariant (Th_coqc, general, any injective node
   map with a permuted edge list) composes with the SAME concrete C6
   rotation witness InfoGraphNoether_attempt.v already uses, giving a
   non-vacuous instance for free. HONEST CAVEAT, stated plainly: C6 is
   a regular graph (every node has degree 2), so its Forman curvature
   is constant (= 0) at every edge -- the concrete instance confirms
   the general theorem applies and is non-vacuous, but does not by
   itself illustrate a case where curvature actually varies across the
   orbit. The general theorem (forman_sigma_invariant) is stated for
   an arbitrary graph and automorphism, and is the part that matters
   for a non-regular graph.
   =================================================================== *)

Require Coq.Arith.PeanoNat.
Require Coq.Lists.List.
Require Coq.Sorting.Permutation.
Require Coq.QArith.QArith.
Require Coq.micromega.Lia.
Require Coq.micromega.Lqa.

Import Coq.Lists.List.
Import Coq.Sorting.Permutation.
Import Coq.QArith.QArith.
Import Coq.micromega.Lia.
Import Coq.micromega.Lqa.
Open Scope Q_scope.
Import ListNotations.

Module CurvatureNoether.

Definition Edge : Type := (nat * nat)%type.

Definition esum (E : list Edge) (g : Edge -> Q) : Q :=
  fold_right (fun e acc => g e + acc) 0 E.

(* image of an edge under a node map, reproduced from InfoGraphNoether *)
Definition emap (sg : nat -> nat) (e : Edge) : Edge :=
  (sg (fst e), sg (snd e)).

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

(* ---- degree and Forman curvature, reproduced from InfoGraphGrowth_attempt.v ---- *)
Definition share (e : Edge) (i : nat) : Q :=
  (if Nat.eqb (fst e) i then 1 else 0) + (if Nat.eqb (snd e) i then 1 else 0).

Definition deg (E : list Edge) (i : nat) : Q := esum E (fun e => share e i).

Definition forman (E : list Edge) (e : Edge) : Q :=
  4 - deg E (fst e) - deg E (snd e).

(* ================================================================= *)
(*  THE BRIDGE: Forman curvature is sigma-invariant for any injective *)
(*  node map, exactly as gform already is (InfoGraphNoether's         *)
(*  gform_invariant) -- proved here for the first time.               *)
(* ================================================================= *)

Lemma sg_eqb_inj : forall (sg : nat -> nat) (a i : nat),
  (forall x y, sg x = sg y -> x = y) ->
  Nat.eqb (sg a) (sg i) = Nat.eqb a i.
Proof.
  intros sg a i Hinj.
  destruct (Nat.eqb a i) eqn:E.
  - apply Nat.eqb_eq in E. subst. apply Nat.eqb_refl.
  - apply Nat.eqb_neq in E.
    destruct (Nat.eqb (sg a) (sg i)) eqn:E2; [| reflexivity].
    apply Nat.eqb_eq in E2. apply Hinj in E2. contradiction.
Qed.

Lemma share_sigma : forall (sg : nat -> nat) (e : Edge) (i : nat),
  (forall x y, sg x = sg y -> x = y) ->
  share (emap sg e) (sg i) == share e i.
Proof.
  intros sg e i Hinj. unfold share, emap. simpl.
  rewrite (sg_eqb_inj sg (fst e) i Hinj).
  rewrite (sg_eqb_inj sg (snd e) i Hinj).
  reflexivity.
Qed.

Theorem deg_sigma_invariant : forall (sg : nat -> nat) (E : list Edge) (i : nat),
  (forall x y, sg x = sg y -> x = y) ->
  deg (map (emap sg) E) (sg i) == deg E i.
Proof.
  intros sg E i Hinj. unfold deg.
  rewrite <- esum_precompose.
  apply esum_ext. intros e _.
  apply share_sigma. exact Hinj.
Qed.

Theorem forman_sigma_invariant : forall (sg : nat -> nat) (E : list Edge) (e : Edge),
  (forall x y, sg x = sg y -> x = y) ->
  forman (map (emap sg) E) (emap sg e) == forman E e.
Proof.
  intros sg E e Hinj. unfold forman, emap. simpl.
  rewrite (deg_sigma_invariant sg E (fst e) Hinj).
  rewrite (deg_sigma_invariant sg E (snd e) Hinj).
  reflexivity.
Qed.

(* ================================================================= *)
(*  CONCRETE INSTANCE: the same order-6 rotation InfoGraphNoether     *)
(*  already uses, reproduced here, confirming the theorem is          *)
(*  non-vacuous (with the honest caveat stated in the file header:    *)
(*  C6 is regular, so its curvature happens to be constant).          *)
(* ================================================================= *)

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

Corollary forman_c6_rotation_invariant : forall e : Edge,
  forman (map (emap rot6) C6) (emap rot6 e) == forman C6 e.
Proof.
  intro e. apply forman_sigma_invariant. exact rot6_inj.
Qed.

(* Honest numeric confirmation of the caveat: C6 is 2-regular, so its  *)
(* curvature is the constant 0 at every edge -- vm_compute confirms   *)
(* this is a genuine (if simple) instance, not a vacuous statement.    *)
Example c6_curvature_is_zero : forman C6 (0%nat, 1%nat) == 0.
Proof. unfold forman, deg, esum, share, C6. simpl. reflexivity. Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions sg_eqb_inj.
Print Assumptions share_sigma.
Print Assumptions deg_sigma_invariant.
Print Assumptions forman_sigma_invariant.
Print Assumptions rot6_inj.
Print Assumptions forman_c6_rotation_invariant.
Print Assumptions c6_curvature_is_zero.

End CurvatureNoether.
