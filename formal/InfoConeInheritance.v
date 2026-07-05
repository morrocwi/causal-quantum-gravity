(* ===================================================================== *)
(*  InfoConeInheritance.v                                                 *)
(*  THE CAUSALITY CURRENCY OF A BRIDGE: A GENERIC LEAPFROG STEP, OVER     *)
(*  ANY PER-NODE COEFFICIENT FIELD, IS BLIND TO NON-NEIGHBORS.            *)
(*                                                                        *)
(*  A single leapfrog step of the mother equation's own linear/quadratic  *)
(*  sector, `step E m dt prev curr i`, is defined for an ARBITRARY list   *)
(*  of edges E and an ARBITRARY per-node coefficient field m : nat -> Q   *)
(*  (no sign or shape assumed).  Because m is universally quantified,     *)
(*  ANY nonnegative field -- including a Regge-Wheeler-shaped potential   *)
(*  V(r_i) built elsewhere at the +reals tier and merely EVALUATED into   *)
(*  this Q-valued slot -- is automatically an instance of this same       *)
(*  step, and automatically inherits every theorem proved here.  This is  *)
(*  a definitional weld, not new physics: nothing about Schwarzschild is  *)
(*  used or assumed inside this file.                                     *)
(*                                                                        *)
(*  Results (all exact over Q, no reals, no limits):                      *)
(*    shift_blind_step        the step's value at node i is a function    *)
(*                            PURELY of prev i and of curr at i's own      *)
(*                            edge-endpoints -- two fields agreeing there  *)
(*                            give the same next value at i, regardless   *)
(*                            of how they differ anywhere else            *)
(*    step_domain_of_dependence   the complementary statement: perturbing *)
(*                            curr ONLY at a node k that shares no edge    *)
(*                            with i (and k<>i) cannot change step(...)(i)*)
(*    step_path_local_stencil     specialized to a PATH graph (the        *)
(*                            radial/1D case a Regge-Wheeler-style        *)
(*                            equation actually needs): the step at an    *)
(*                            interior node i depends only on             *)
(*                            prev(i), curr(i-1), curr(i), curr(i+1)      *)
(*                                                                        *)
(*  HONESTLY NOT CLAIMED: any multi-step / iterated causal-cone growth     *)
(*  bound (this is the ONE-STEP fact only); any statement about           *)
(*  Schwarzschild, Regge-Wheeler, or any physical potential (those live   *)
(*  at the +reals tier elsewhere and are not referenced here); any        *)
(*  stability, energy, or sign property of the field m.                   *)
(*  Expected: Print Assumptions => Closed under the global context.       *)
(* ===================================================================== *)

Require Coq.Arith.PeanoNat.
Require Coq.Lists.List.
Require Coq.QArith.QArith.
Require Coq.micromega.Lqa.
Require Coq.micromega.Lia.

Module ConeInheritance.

Import Coq.Lists.List. Import ListNotations.
Import Coq.Arith.PeanoNat.
Import Coq.QArith.QArith.
Import Coq.micromega.Lqa.
Import Coq.micromega.Lia.
Local Open Scope Q_scope.

Definition Edge : Type := (nat * nat)%type.

Definition esum (E : list Edge) (h : Edge -> Q) : Q :=
  fold_right (fun e acc => h e + acc) 0 E.

Definition touches (e : Edge) (i : nat) : bool :=
  orb (Nat.eqb (fst e) i) (Nat.eqb (snd e) i).

Definition other_end (e : Edge) (i : nat) : nat :=
  if Nat.eqb (fst e) i then snd e else fst e.

(* per-node contribution of one edge to the graph-Laplacian action at i *)
Definition acontrib (x : nat -> Q) (i : nat) (e : Edge) : Q :=
  (if Nat.eqb (fst e) i then 1 else 0) * (x (snd e) - x (fst e))
  + (if Nat.eqb (snd e) i then 1 else 0) * (x (fst e) - x (snd e)).

Definition lnode (E : list Edge) (x : nat -> Q) (i : nat) : Q :=
  esum E (acontrib x i).

(* one leapfrog step of the mother equation's linear/quadratic sector,    *)
(* over an ARBITRARY per-node coefficient field m                        *)
Definition step (E : list Edge) (m : nat -> Q) (dt : Q)
                (prev curr : nat -> Q) (i : nat) : Q :=
  2 * curr i - prev i + dt * dt * (lnode E curr i - m i * curr i).

(* ------------------------------------------------------------------ *)
(* Toolbox                                                             *)
(* ------------------------------------------------------------------ *)

Lemma esum_ext_on_touching :
  forall (E : list Edge) (i : nat) (x y : nat -> Q),
  (forall e, In e E -> touches e i = true -> x (other_end e i) == y (other_end e i)) ->
  x i == y i ->
  esum E (acontrib x i) == esum E (acontrib y i).
Proof.
  induction E as [| e r IH]; intros i x y Hother Hself; simpl.
  - reflexivity.
  - assert (Hr : esum r (acontrib x i) == esum r (acontrib y i)).
    { apply IH.
      - intros e' He' Ht'. apply Hother; [right; exact He' | exact Ht'].
      - exact Hself. }
    assert (He : acontrib x i e == acontrib y i e).
    { unfold acontrib.
      destruct (Nat.eqb (fst e) i) eqn:Ef; destruct (Nat.eqb (snd e) i) eqn:Es.
      - apply Nat.eqb_eq in Ef. apply Nat.eqb_eq in Es.
        assert (Hfs : fst e = snd e) by (rewrite Ef, Es; reflexivity).
        rewrite <- Hfs, Ef. rewrite Hself. ring.
      - assert (Hteq : touches e i = true) by (unfold touches; rewrite Ef; reflexivity).
        assert (Hoe : other_end e i = snd e) by (unfold other_end; rewrite Ef; reflexivity).
        assert (Hxy : x (snd e) == y (snd e))
          by (rewrite <- Hoe; apply Hother; [left; reflexivity | exact Hteq]).
        apply Nat.eqb_eq in Ef. rewrite Ef, Hself, Hxy. ring.
      - assert (Hteq : touches e i = true) by (unfold touches; rewrite Ef, Es; reflexivity).
        assert (Hoe : other_end e i = fst e) by (unfold other_end; rewrite Ef; reflexivity).
        assert (Hxy : x (fst e) == y (fst e))
          by (rewrite <- Hoe; apply Hother; [left; reflexivity | exact Hteq]).
        apply Nat.eqb_eq in Es. rewrite Es, Hself, Hxy. ring.
      - reflexivity. }
    rewrite He, Hr. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* THE CAUSALITY CURRENCY                                              *)
(* ------------------------------------------------------------------ *)

Theorem shift_blind_step :
  forall (E : list Edge) (m : nat -> Q) (dt : Q)
         (prev prev' curr curr' : nat -> Q) (i : nat),
  prev i == prev' i ->
  curr i == curr' i ->
  (forall e, In e E -> touches e i = true ->
     curr (other_end e i) == curr' (other_end e i)) ->
  step E m dt prev curr i == step E m dt prev' curr' i.
Proof.
  intros E m dt prev prev' curr curr' i Hprev Hself Hother.
  unfold step, lnode.
  rewrite (esum_ext_on_touching E i curr curr' Hother Hself).
  rewrite Hself, Hprev. reflexivity.
Qed.

Theorem step_domain_of_dependence :
  forall (E : list Edge) (m : nat -> Q) (dt : Q)
         (prev curr curr' : nat -> Q) (i k : nat),
  i <> k ->
  (forall e, In e E -> touches e i = true -> other_end e i <> k) ->
  (forall j, j <> k -> curr j == curr' j) ->
  step E m dt prev curr i == step E m dt prev curr' i.
Proof.
  intros E m dt prev curr curr' i k Hik Hnotk Hagree.
  apply shift_blind_step.
  - apply Qeq_refl.
  - apply Hagree. exact Hik.
  - intros e He Ht.
    apply Hagree. intros Heq. apply (Hnotk e He Ht). exact Heq.
Qed.

(* specialized to a concrete PATH graph on {0,...,n} -- the radial/1D    *)
(* case a Regge-Wheeler-style equation actually uses *)
Fixpoint path_edges (n : nat) : list Edge :=
  match n with
  | 0%nat => []
  | S k => (k, S k) :: path_edges k
  end.

Theorem step_path_local_stencil :
  forall (n i : nat) (m : nat -> Q) (dt : Q)
         (prev curr curr' : nat -> Q),
  (0 < i)%nat -> (i < n)%nat ->
  curr (i - 1)%nat == curr' (i - 1)%nat ->
  curr i == curr' i ->
  curr (i + 1)%nat == curr' (i + 1)%nat ->
  step (path_edges n) m dt prev curr i == step (path_edges n) m dt prev curr' i.
Proof.
  intros n i m dt prev curr curr' Hi0 Hin Hleft Hself Hright.
  apply shift_blind_step; [apply Qeq_refl | exact Hself |].
  intros e He Ht.
  assert (Hcase : e = (i - 1, i)%nat \/ e = (i, i + 1)%nat).
  { clear Hleft Hself Hright Hi0 Hin.
    induction n as [| n' IHn]; simpl in He.
    - destruct He.
    - destruct He as [He | He].
      + subst e.
        assert (Htb : Nat.eqb n' i = true \/ Nat.eqb (S n') i = true).
        { unfold touches in Ht. simpl in Ht. apply Bool.orb_true_iff in Ht. exact Ht. }
        destruct Htb as [Ei | Ei2].
        * apply Nat.eqb_eq in Ei. subst i. right.
          apply injective_projections; simpl; lia.
        * apply Nat.eqb_eq in Ei2. subst i. left.
          apply injective_projections; simpl; lia.
      + apply IHn. exact He. }
  destruct Hcase as [Hcase | Hcase]; subst e; unfold other_end; simpl.
  - assert (Hfi : Nat.eqb (i - 1) i = false) by (apply Nat.eqb_neq; lia).
    rewrite Hfi. exact Hleft.
  - assert (Hfi : Nat.eqb i i = true) by (apply Nat.eqb_eq; reflexivity).
    rewrite Hfi. exact Hright.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions shift_blind_step.
Print Assumptions step_domain_of_dependence.
Print Assumptions step_path_local_stencil.

End ConeInheritance.
