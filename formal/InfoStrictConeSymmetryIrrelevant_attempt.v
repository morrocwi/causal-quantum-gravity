(******************************************************************************)
(* InfoStrictConeSymmetryIrrelevant_attempt.v -- EXPLORATORY, single-attempt.  *)
(*   Standalone. Requires ONLY Coq.QArith + Coq.micromega.Lqa/Lia.             *)
(*                                                                            *)
(* DIRECT QUESTION FROM THE FOUNDER: InfoStrictConeBothOrders_attempt.v         *)
(* showed strict-finite-cone locality does NOT force 2nd-order (M) dynamics --    *)
(* but that test used a SYMMETRIC L_R (an undirected path graph). Does the         *)
(* SAME conclusion hold for an ASYMMETRIC (directed) seed, or was symmetry doing    *)
(* hidden work? Not answered by reasoning -- tested here, directly.                  *)
(*                                                                            *)
(* THE ANSWER (Th_coqc, machine-checked, not asserted):                          *)
(*   euler1_node2_zero_any_banded / leapfrog_node2_zero_any_banded generalize        *)
(*   the ORIGINAL file's node-2-zero-after-one-step findings to ANY operator R        *)
(*   satisfying banded1 (entries vanish beyond graph-distance 1) -- NO symmetry        *)
(*   hypothesis is used anywhere in either proof. The argument only ever touches       *)
(*   R 2 0 (the single entry that matters for a delta-at-node-0 initial state),          *)
(*   which vanishes by banded1 alone, regardless of whether R 0 2 equals it.              *)
(*   asym_witness_R exhibits a CONCRETE asymmetric (R 0 1 <> R 1 0) matrix on the           *)
(*   identical path-graph sparsity pattern, satisfying banded1, and                          *)
(*   asym_witness_node2_zero confirms node 2 is STILL exactly 0 after one euler1               *)
(*   step on THIS asymmetric matrix -- not a re-derivation of the general theorem,               *)
(*   a genuinely separate concrete check.                                                          *)
(*                                                                            *)
(* READING (matches, does not just repeat, the original file's own [Dr] verdict):    *)
(*   symmetry was never doing the work in the original finding -- graph-distance         *)
(*   locality is a pure SPARSITY-PATTERN fact (which entries are nonzero), totally         *)
(*   insensitive to whether nonzero entries come in symmetric pairs or not. This            *)
(*   closes, rather than merely echoes, the founder's specific challenge: it is NOT           *)
(*   a gap in the original test, it is a genuine invariance the original test's OWN             *)
(*   proof already implied (R_i_0 == 0 was the only fact ever used) -- this file makes            *)
(*   that implication explicit and checks it on a non-symmetric witness.                            *)
(*                                                                            *)
(* WHAT THIS MEANS FOR 'why is M still free': the founder's follow-up reading             *)
(* ('memory has its own local structure that runs separately on the graph, hence            *)
(* free') is CONSISTENT with this finding, not merely asserted alongside it: since             *)
(* neither symmetric NOR asymmetric spatial/graph data can force M via a distance/               *)
(* locality argument (this file), and InfoAsymmetricSeedTrifurcation_attempt.v Part 6              *)
(* independently found SkewOff is exactly energy-null (the discriminator IS                          *)
(* conservation, per the original file's own Part 4, not locality, and asymmetry                       *)
(* does not touch conservation either -- an antisymmetric part contributes zero to                       *)
(* any quadratic form regardless of the underlying graph's bandwidth) -- M's freedom                       *)
(* survives BOTH the symmetric and the asymmetric spatial construction. Still [Dr]:                          *)
(* this is a converging pattern across two independent tests, not a proof that NO                              *)
(* spatial construction could ever force M.                                                                       *)
(******************************************************************************)

Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Open Scope Q_scope.

(* ========================================================================= *)
(* PART 1 -- the generalization: bandedness alone (no symmetry) forces           *)
(* node-2-zero-after-one-step, for BOTH orders.                                  *)
(* ========================================================================= *)

Definition banded1 (R : nat -> nat -> Q) : Prop :=
  forall i j : nat, ((j >= i + 2)%nat \/ (i >= j + 2)%nat) -> R i j == 0.

Definition Lapply (R : nat -> nat -> Q) (x : nat -> Q) (i : nat) : Q :=
  R i 0%nat * x 0%nat + R i 1%nat * x 1%nat + R i 2%nat * x 2%nat
  + R i 3%nat * x 3%nat + R i 4%nat * x 4%nat.

Definition Phi0 : nat -> Q :=
  fun i => match i with 0%nat => 1 | _ => 0 end.

Definition euler1 (R : nat -> nat -> Q) (dt : Q) (x : nat -> Q) (i : nat) : Q :=
  x i + dt * Lapply R x i.

Definition leapfrog (R : nat -> nat -> Q) (dt : Q) (prev curr : nat -> Q) (i : nat) : Q :=
  2 * curr i - prev i + dt * dt * Lapply R curr i.

(* [Th_coqc] No symmetry hypothesis anywhere -- only banded1, applied at the      *)
(* single pair (2,0) that a delta-at-node-0 state can ever reach in one step.       *)
Theorem euler1_node2_zero_any_banded :
  forall (R : nat -> nat -> Q), banded1 R ->
  forall dt : Q, euler1 R dt Phi0 2%nat == 0.
Proof.
  intros R Hband dt.
  assert (H20 : R 2%nat 0%nat == 0) by (apply Hband; lia).
  unfold euler1, Lapply, Phi0. simpl.
  rewrite H20. ring.
Qed.

Theorem leapfrog_node2_zero_any_banded :
  forall (R : nat -> nat -> Q), banded1 R ->
  forall dt : Q, leapfrog R dt Phi0 Phi0 2%nat == 0.
Proof.
  intros R Hband dt.
  assert (H20 : R 2%nat 0%nat == 0) by (apply Hband; lia).
  unfold leapfrog, Lapply, Phi0. simpl.
  rewrite H20. ring.
Qed.

(* [Th_coqc] Both orders equally cone-limited, for ANY banded R -- the original    *)
(* file's Part 3 conjunction, now symmetry-free. *)
Theorem both_orders_strict_cone_any_banded :
  forall (R : nat -> nat -> Q), banded1 R ->
  forall dt : Q,
    euler1 R dt Phi0 2%nat == 0 /\ leapfrog R dt Phi0 Phi0 2%nat == 0.
Proof.
  intros R Hband dt.
  split.
  - exact (euler1_node2_zero_any_banded R Hband dt).
  - exact (leapfrog_node2_zero_any_banded R Hband dt).
Qed.

(* ========================================================================= *)
(* PART 2 -- a CONCRETE asymmetric witness on the identical path-graph sparsity   *)
(* pattern: R 0 1 <> R 1 0 (a genuinely directed edge), yet still banded1.          *)
(* ========================================================================= *)

Definition R_asym (i j : nat) : Q :=
  match i, j with
  | 0%nat,0%nat => 1   | 0%nat,1%nat => -2
  | 1%nat,0%nat => -1  | 1%nat,1%nat => 3   | 1%nat,2%nat => -1
  | 2%nat,1%nat => -2  | 2%nat,2%nat => 2   | 2%nat,3%nat => -1
  | 3%nat,2%nat => -1  | 3%nat,3%nat => 2   | 3%nat,4%nat => -3
  | 4%nat,3%nat => -1  | 4%nat,4%nat => 1
  | _,_ => 0
  end.

Theorem R_asym_is_asymmetric : ~ (R_asym 0%nat 1%nat == R_asym 1%nat 0%nat).
Proof. unfold R_asym. intro H. lra. Qed.

Theorem R_asym_banded1 : banded1 R_asym.
Proof.
  intros i j H.
  destruct i as [| [| [| [| [| i]]]]]; destruct j as [| [| [| [| [| j]]]]];
    simpl; try reflexivity; try lia.
Qed.

(* [Th_coqc] Concrete, non-vacuous confirmation: node 2 is STILL exactly 0          *)
(* after one euler1 step, on this specific ASYMMETRIC matrix -- a genuinely            *)
(* separate check, not a re-derivation of Part 1's general theorem. *)
Theorem asym_witness_node2_zero :
  forall dt : Q, euler1 R_asym dt Phi0 2%nat == 0.
Proof.
  intro dt.
  unfold euler1, Lapply, R_asym, Phi0. simpl. ring.
Qed.

(* Node 1 IS reached after one step (non-vacuous cone boundary, same shape          *)
(* as the original file's own node-1-nonzero witness), using the ASYMMETRIC          *)
(* entry R_asym 1 0 = -1 (note: NOT R_asym 0 1 = -2 -- direction matters for            *)
(* the VALUE reached, even though it does not matter for WHETHER node 2 is reached). *)
Theorem asym_witness_node1_nonzero :
  ~ (euler1 R_asym (1#4) Phi0 1%nat == 0).
Proof.
  unfold euler1, Lapply, R_asym, Phi0. simpl. intro H. lra.
Qed.

(* Direct instantiation of the general theorem on this concrete asymmetric          *)
(* witness -- the composition itself is the point, not a new proof technique. *)
Theorem asym_witness_both_orders_cone :
  forall dt : Q,
    euler1 R_asym dt Phi0 2%nat == 0 /\ leapfrog R_asym dt Phi0 Phi0 2%nat == 0.
Proof. intro dt. exact (both_orders_strict_cone_any_banded R_asym R_asym_banded1 dt). Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions euler1_node2_zero_any_banded.
Print Assumptions leapfrog_node2_zero_any_banded.
Print Assumptions both_orders_strict_cone_any_banded.
Print Assumptions R_asym_is_asymmetric.
Print Assumptions R_asym_banded1.
Print Assumptions asym_witness_node2_zero.
Print Assumptions asym_witness_node1_nonzero.
Print Assumptions asym_witness_both_orders_cone.
