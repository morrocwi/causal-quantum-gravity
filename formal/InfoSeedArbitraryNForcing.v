(******************************************************************************)
(* InfoSeedArbitraryNForcing.v -- EXPLORATORY, single-attempt.           *)
(*   Requires InfoAsymmetricSeedTrifurcation (this repo, R0/Parts 1-7,     *)
(*   untouched, for `ord` only). No axiom, no Reals, no continuum. TIER = Th_coqc.    *)
(*                                                                            *)
(* THE FRONTIER DOC'S ITEM 5, THE BIGGER REMAINDER: `InfoSeedN4Extension_attempt.v`      *)
(* checked the forcing pattern CONCRETELY at n=4, on top of the original n=3 -- two          *)
(* data points, honestly flagged there as suggestive, NOT a proof for arbitrary n. This         *)
(* file closes that gap: the seed's forced-D construction and its rowsum0 axiom are proved         *)
(* by GENUINE INDUCTION on an ARBITRARY finite vertex list, not re-checked case-by-case at            *)
(* each new size.                                                            *)
(*                                                                            *)
(* THE KEY TECHNICAL MOVE: represent the vertex set as a `list nat` (matching this repo's           *)
(* own existing style -- `InfoSpectralCeilingSharp_attempt.v`'s `esum`/`fold_right` over edge            *)
(* lists -- rather than introducing a fresh `Fin.t n` dependent-type carrier). `NoDup` on the             *)
(* list is the honest, minimal hypothesis standing in for 'n distinct vertices.' The core proof              *)
(* obligation reduces to one reusable list lemma (`fold_right_replace_one`): if two functions                  *)
(* agree everywhere except at one distinguished list element, their fold-sums differ by exactly                  *)
(* the value gap at that element -- proved once, by structural induction on the list, and reused                   *)
(* for EVERY vertex count at once.                                                                                     *)
(*                                                                            *)
(* WHAT IS PROVED (Th_coqc):                                                                                             *)
(*   fold_right_congruence     if two functions agree pointwise on a list, their fold-sums agree                            *)
(*                          -- a standard, general list fact, proved by induction.                                             *)
(*   fold_right_replace_one    THE KEY LEMMA: if `g`,`h` agree everywhere except possibly at a                                    *)
(*                          distinguished `i` (occurring exactly once, by `NoDup`), their fold-                                       *)
(*                          sums differ by exactly `g(i)-h(i)` -- proved by induction on the                                             *)
(*                          list, genuinely for ANY length, not any fixed n.                                                                 *)
(*   R0_general_rowsum0_forced   the seed's row-sum axiom holds by construction, for an                                                        *)
(*                          ARBITRARY (NoDup) vertex list `verts` and ANY `i` in it -- not                                                        *)
(*                          checked at n=3 or n=4 specifically, proved once for all n.                                                              *)
(*   R0_general_diagpart_forced   the SAME forced-D identity (`D_i = degree_i(Wt) -                                                                   *)
(*                          lam*circulation_i(ord)`) as `InfoAsymmetricSeedTrifurcation.v`'s                                                     *)
(*                          `diagpart_forced_by_rowsum0_full` (n=3) and                                                                                     *)
(*                          `InfoSeedN4Extension_attempt.v`'s n=4 analogue -- now proved for an                                                                 *)
(*                          ARBITRARY vertex list, via `RowSum_add`/`RowSum_scale` (fold-right                                                                    *)
(*                          linearity, each a standard small induction).                                                                                              *)
(*   seed_n5_witness          a NEW, genuinely different vertex count (n=5, not previously                                                                              *)
(*                          checked at n=3 or n=4) instantiating the GENERAL theorem above --                                                                              *)
(*                          demonstrating this is now really n-independent machinery being                                                                                   *)
(*                          APPLIED, not a third hand-derived special case.                                                                                                    *)
(*                                                                            *)
(* SCOPE / TIER HONESTY -- read before citing as more than it is:                                                                                                                 *)
(*   [Th_coqc] Every theorem above, exactly as stated -- genuinely proved for arbitrary `NoDup`                                                                                     *)
(*   vertex lists, not merely checked at additional fixed sizes. This CLOSES the 'two data                                                                                            *)
(*   points is not a proof' gap flagged in `InfoSeedN4Extension_attempt.v`.                                                                                                              *)
(*   [Dr, stated openly]: this generalizes `rowsum0_full`/the D-forcing identity, NOT the full                                                                                             *)
(*   Part 7 apparatus -- `offdiag_le0_full` (the CONDITIONAL small-skew hypothesis), the                                                                                                     *)
(*   `circulation_sums_to_zero` 'balance' fact (`InfoSeedAsymmetricButBalanced_attempt.v`), the                                                                                                *)
(*   torsion/curvature/floor/crossover results built on TOP of the n=3 seed, and the continuum-                                                                                                  *)
(*   limit connection (`InfoContinuumLimit_nD.v`) are all NOT re-derived at this generality here                                                                                                   *)
(*   -- each would need its own list-based argument, deferred. This file closes the SPECIFIC gap                                                                                                     *)
(*   about the forcing mechanism itself, not the entire thread's arbitrary-n closure.                                                                                                                   *)
(******************************************************************************)

Require InfoAsymmetricSeedTrifurcation.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Open Scope Q_scope.

(* ========================================================================= *)
(* PART A -- reusable list machinery: the KEY lemma, proved once for ANY       *)
(* vertex list, not per vertex count.                                          *)
(* ========================================================================= *)

Definition RowSum (f : nat -> Q) (verts : list nat) : Q :=
  fold_right (fun j acc => f j + acc) 0 verts.

Lemma fold_right_congruence :
  forall (verts : list nat) (g h : nat -> Q),
    (forall j, In j verts -> g j == h j) ->
    RowSum g verts == RowSum h verts.
Proof.
  induction verts as [| x xs IH]; intros g h Hagree; unfold RowSum in *; simpl.
  - reflexivity.
  - assert (Hx : g x == h x) by (apply Hagree; left; reflexivity).
    assert (Hrest : fold_right (fun j acc => g j + acc) 0 xs
                    == fold_right (fun j acc => h j + acc) 0 xs).
    { apply IH. intros j Hj. apply Hagree. right. exact Hj. }
    rewrite Hx, Hrest. reflexivity.
Qed.

(* [Th_coqc] THE KEY LEMMA: two functions agreeing everywhere except at one     *)
(* distinguished, non-repeated list element have fold-sums differing by         *)
(* EXACTLY the value gap at that element -- proved for ANY list, by induction. *)
Lemma fold_right_replace_one :
  forall (verts : list nat) (i : nat) (g h : nat -> Q),
    NoDup verts -> In i verts -> (forall j, j <> i -> g j == h j) ->
    RowSum g verts == (g i - h i) + RowSum h verts.
Proof.
  induction verts as [| x xs IH]; intros i g h Hnd Hin Hagree.
  - destruct Hin.
  - unfold RowSum in *. simpl.
    inversion Hnd as [| y ys Hnotin HndXs Heq]; subst.
    destruct Hin as [Heqi | Hin].
    + subst x.
      assert (Hcong : fold_right (fun j acc => g j + acc) 0 xs
                      == fold_right (fun j acc => h j + acc) 0 xs).
      { apply fold_right_congruence. intros j Hj.
        apply Hagree. intro Hc. subst j. apply Hnotin. exact Hj. }
      rewrite Hcong. ring.
    + assert (HIH : fold_right (fun j acc => g j + acc) 0 xs
                    == (g i - h i) + fold_right (fun j acc => h j + acc) 0 xs).
      { apply IH; assumption. }
      assert (Hxi : x <> i) by (intro Hc; subst x; apply Hnotin; exact Hin).
      assert (Hgx : g x == h x) by (apply Hagree; exact Hxi).
      rewrite HIH, Hgx. ring.
Qed.

Lemma RowSum_add : forall (f g : nat -> Q) (verts : list nat),
  RowSum (fun j => f j + g j) verts == RowSum f verts + RowSum g verts.
Proof.
  induction verts as [| x xs IH]; unfold RowSum in *; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

Lemma RowSum_scale : forall (c : Q) (f : nat -> Q) (verts : list nat),
  RowSum (fun j => c * f j) verts == c * RowSum f verts.
Proof.
  induction verts as [| x xs IH]; unfold RowSum in *; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

(* ========================================================================= *)
(* PART B -- the seed's forcing construction, for an ARBITRARY vertex list.    *)
(* ========================================================================= *)

Definition OffVal (Wt : nat -> nat -> Q) (lam : Q) (i j : nat) : Q :=
  if Nat.eqb i j then 0
  else - Wt i j + lam * InfoAsymmetricSeedTrifurcation.ord i j.

Definition R0_general (Wt : nat -> nat -> Q) (lam : Q) (verts : list nat)
    (i j : nat) : Q :=
  if Nat.eqb i j then - (RowSum (OffVal Wt lam i) verts) else OffVal Wt lam i j.

(* [Th_coqc] the row-sum axiom holds BY CONSTRUCTION, for ANY NoDup vertex        *)
(* list and any i in it -- proved ONCE, not per vertex count. *)
Theorem R0_general_rowsum0_forced :
  forall (Wt : nat -> nat -> Q) (lam : Q) (verts : list nat) (i : nat),
    NoDup verts -> In i verts ->
    RowSum (R0_general Wt lam verts i) verts == 0.
Proof.
  intros Wt lam verts i Hnd Hin.
  assert (Hagree : forall j, j <> i -> R0_general Wt lam verts i j == OffVal Wt lam i j).
  { intros j Hj. unfold R0_general.
    destruct (Nat.eqb i j) eqn:Heq.
    - apply Nat.eqb_eq in Heq. exfalso. apply Hj. symmetry. exact Heq.
    - reflexivity. }
  pose proof (fold_right_replace_one verts i (R0_general Wt lam verts i)
                (OffVal Wt lam i) Hnd Hin Hagree) as Hkey.
  assert (Hgi : R0_general Wt lam verts i i == - (RowSum (OffVal Wt lam i) verts)).
  { unfold R0_general. rewrite Nat.eqb_refl. reflexivity. }
  assert (Hhi : OffVal Wt lam i i == 0).
  { unfold OffVal. rewrite Nat.eqb_refl. reflexivity. }
  rewrite Hgi, Hhi in Hkey.
  rewrite Hkey. ring.
Qed.

Definition Degree (Wt : nat -> nat -> Q) (verts : list nat) (i : nat) : Q :=
  RowSum (fun j => if Nat.eqb i j then 0 else Wt i j) verts.

Definition Circulation (verts : list nat) (i : nat) : Q :=
  RowSum (fun j => if Nat.eqb i j then 0
                    else InfoAsymmetricSeedTrifurcation.ord i j) verts.

(* [Th_coqc] THE SAME forced-D identity as n=3/n=4, now for an ARBITRARY         *)
(* vertex list: D_i == degree_i(Wt) - lam*circulation_i(ord). *)
Theorem R0_general_diagpart_forced :
  forall (Wt : nat -> nat -> Q) (lam : Q) (verts : list nat) (i : nat),
    NoDup verts -> In i verts ->
    R0_general Wt lam verts i i == Degree Wt verts i - lam * Circulation verts i.
Proof.
  intros Wt lam verts i Hnd Hin.
  unfold R0_general. rewrite Nat.eqb_refl.
  unfold Degree, Circulation.
  assert (Hsplit : RowSum (OffVal Wt lam i) verts
    == RowSum (fun j => if Nat.eqb i j then 0 else - Wt i j) verts
       + RowSum (fun j => if Nat.eqb i j then 0 else lam * InfoAsymmetricSeedTrifurcation.ord i j) verts).
  { rewrite <- RowSum_add.
    apply fold_right_congruence.
    intros j _. unfold OffVal.
    destruct (Nat.eqb i j); ring. }
  rewrite Hsplit.
  assert (Hneg : RowSum (fun j => if Nat.eqb i j then 0 else - Wt i j) verts
                 == - RowSum (fun j => if Nat.eqb i j then 0 else Wt i j) verts).
  { rewrite <- (RowSum_scale (-1#1)).
    apply fold_right_congruence.
    intros j _. destruct (Nat.eqb i j); ring. }
  assert (Hlam : RowSum (fun j => if Nat.eqb i j then 0 else lam * InfoAsymmetricSeedTrifurcation.ord i j) verts
                 == lam * RowSum (fun j => if Nat.eqb i j then 0 else InfoAsymmetricSeedTrifurcation.ord i j) verts).
  { rewrite <- (RowSum_scale lam).
    apply fold_right_congruence.
    intros j _. destruct (Nat.eqb i j); ring. }
  rewrite Hneg, Hlam. ring.
Qed.

(* ========================================================================= *)
(* PART C -- a NEW vertex count (n=5), instantiating the GENERAL theorem --    *)
(* this is n-independent machinery being APPLIED, not a third hand-derived      *)
(* special case.                                                              *)
(* ========================================================================= *)

Definition Verts5 : list nat := [0%nat; 1%nat; 2%nat; 3%nat; 4%nat].

Theorem Verts5_NoDup : NoDup Verts5.
Proof.
  unfold Verts5.
  repeat (constructor; [simpl; intuition congruence | ]).
  constructor.
Qed.

Definition Wt5Root (i j : nat) : Q :=
  match i, j with
  | 0%nat,1%nat|1%nat,0%nat => 2  | 0%nat,2%nat|2%nat,0%nat => 3
  | 0%nat,3%nat|3%nat,0%nat => 4  | 0%nat,4%nat|4%nat,0%nat => 5
  | 1%nat,2%nat|2%nat,1%nat => 6  | 1%nat,3%nat|3%nat,1%nat => 7
  | 1%nat,4%nat|4%nat,1%nat => 8  | 2%nat,3%nat|3%nat,2%nat => 9
  | 2%nat,4%nat|4%nat,2%nat => 10 | 3%nat,4%nat|4%nat,3%nat => 11
  | _,_ => 0
  end.

(* the general rowsum0 theorem applies directly to this NEW n=5 instance --   *)
(* not re-derived, just invoked. *)
Theorem seed_n5_rowsum0 :
  forall i, In i Verts5 -> RowSum (R0_general Wt5Root (1#1) Verts5 i) Verts5 == 0.
Proof.
  intros i Hin. apply R0_general_rowsum0_forced; [exact Verts5_NoDup | exact Hin].
Qed.

(* concrete D values (10, 21, 28, 33, 38) -- genuinely different numbers from  *)
(* the n=3 (5,9,10) and n=4 (6,14,16,18) witnesses, on a genuinely different    *)
(* vertex count, all produced by the SAME general machinery. *)
Example seed_n5_witness :
  R0_general Wt5Root (1#1) Verts5 0%nat 0%nat == 10#1
  /\ R0_general Wt5Root (1#1) Verts5 1%nat 1%nat == 21#1
  /\ R0_general Wt5Root (1#1) Verts5 2%nat 2%nat == 28#1
  /\ R0_general Wt5Root (1#1) Verts5 3%nat 3%nat == 33#1
  /\ R0_general Wt5Root (1#1) Verts5 4%nat 4%nat == 38#1.
Proof.
  unfold R0_general, Verts5, RowSum, OffVal, Wt5Root,
    InfoAsymmetricSeedTrifurcation.ord.
  simpl. repeat split; lra.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions fold_right_congruence.
Print Assumptions fold_right_replace_one.
Print Assumptions RowSum_add.
Print Assumptions RowSum_scale.
Print Assumptions R0_general_rowsum0_forced.
Print Assumptions R0_general_diagpart_forced.
Print Assumptions Verts5_NoDup.
Print Assumptions seed_n5_rowsum0.
Print Assumptions seed_n5_witness.
