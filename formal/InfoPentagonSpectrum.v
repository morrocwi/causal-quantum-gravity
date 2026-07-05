(* ===================================================================
   InfoPentagonSpectrum_attempt.v

   Bridges the graph-Laplacian track (C6 as the automorphism witness of
   InfoGraphNoether_attempt.v / InfoCurvatureNoether_attempt.v) to the
   golden-ratio/roots-of-unity track (InfoGoldenFromRootsOfUnity_
   attempt.v, InfoGoldenPiAlgebraic_attempt.v) via the FIVE-cycle C5's
   own Laplacian spectrum -- not by analogy, but by exhibiting the same
   defining relation (x^2+x-1=0-shape) directly as a graph-spectral
   fact.

   THE CLAIM, verified by hand before writing a line of Coq: the cycle
   graph C_n's Laplacian eigenvalues are 2-2*cos(2*pi*k/n). For n=5,
   the two nonzero DISTINCT eigenvalues lambda = 2-2cos(72 deg) and
   2-2cos(144 deg) satisfy (by direct trig identity, cross-checked by
   hand): their SUM = 5 and PRODUCT = 5, hence they are exactly the
   roots of lambda^2 - 5*lambda + 5 = 0 -- and since lambda=0 is also
   an eigenvalue, the Laplacian L of C5 satisfies the CUBIC operator
   identity L^3 - 5*L^2 + 5*L = 0 (factoring lambda*(lambda^2-5*lambda
   +5) = lambda^3-5*lambda^2+5*lambda). This is verified below as an
   EXACT Q-arithmetic identity, pointwise on each of the 5 nodes, via
   `ring` -- no eigenvalue theory, no trigonometry, no continuum,
   invoked in the Coq proof itself (the motivating trig computation is
   prose only, in this header).

   By contrast, C6 (InfoGraphNoether/InfoCurvatureNoether's own
   automorphism witness) has ALL FOUR of its distinct eigenvalues
   {0,1,3,4} rational, with explicit rational eigenvectors verified
   below. C6 is, in this precise sense, the LAST cycle whose full
   spectrum stays in Q; C5 is the FIRST cycle whose spectrum leaves Q
   and lands in Q(sqrt5) -- exactly the field InfoGoldenFromRootsOfUnity
   _attempt.v and InfoGoldenPiAlgebraic_attempt.v already work in. The
   quadratic factor lambda^2-5*lambda+5 of C5's Laplacian is, up to an
   affine rescaling, the SAME defining-relation SHAPE as phi's own
   x^2=x+1 (both are the minimal polynomial of an element of Q(sqrt5)).
   This file does not prove that rescaling identity (it would require
   Coq.Reals or the nested-radical algebraic technique of
   InfoGoldenPiAlgebraic_attempt.v to state without leaving Q) -- it is
   noted in prose only, tagged Dr, not re-derived here.

   TIER: every theorem below is Tier-0, Q-only, axiom-free (ring),
   proved by explicit case-splitting on the five (resp. six) nodes --
   no general n-cycle theory, no eigenvalue machinery.
   =================================================================== *)

Require Coq.QArith.QArith.
Require Coq.micromega.Lqa.
Require Coq.micromega.Lia.

Import Coq.QArith.QArith.
Import Coq.micromega.Lqa.
Import Coq.micromega.Lia.
Open Scope Q_scope.

Module PentagonSpectrum.

(* ------------------------------------------------------------------ *)
(*  C5: the 5-cycle Laplacian, as an explicit operator on functions    *)
(*  nat -> Q restricted to nodes 0..4 (case-matched, no general n).    *)
(* ------------------------------------------------------------------ *)

Definition L5 (x : nat -> Q) (i : nat) : Q :=
  match i with
  | 0%nat => 2 * x 0%nat - x 4%nat - x 1%nat
  | 1%nat => 2 * x 1%nat - x 0%nat - x 2%nat
  | 2%nat => 2 * x 2%nat - x 1%nat - x 3%nat
  | 3%nat => 2 * x 3%nat - x 2%nat - x 4%nat
  | 4%nat => 2 * x 4%nat - x 3%nat - x 0%nat
  | _ => 0
  end.

(* THE CUBIC IDENTITY: L5^3 - 5*L5^2 + 5*L5 = 0, pointwise on each of  *)
(* the 5 nodes -- an exact Q identity, verified by `ring` per node.    *)
Theorem L5_cubic_identity : forall (x : nat -> Q) (i : nat),
  (i < 5)%nat ->
  L5 (fun j => L5 (fun k => L5 x k) j) i
    - 5 * L5 (fun j => L5 x j) i
    + 5 * L5 x i == 0.
Proof.
  intros x i Hi.
  destruct i as [|[|[|[|[|i]]]]]; [ | | | | | lia];
    unfold L5; ring.
Qed.

(* ------------------------------------------------------------------ *)
(*  C6: the 6-cycle Laplacian (the same graph as InfoGraphNoether's    *)
(*  rot6 witness), with all four distinct eigenvalues {0,1,3,4}        *)
(*  exhibited by explicit RATIONAL (integer) eigenvectors, hand-       *)
(*  verified before writing (see file header of the session log).     *)
(* ------------------------------------------------------------------ *)

Definition L6 (x : nat -> Q) (i : nat) : Q :=
  match i with
  | 0%nat => 2 * x 0%nat - x 5%nat - x 1%nat
  | 1%nat => 2 * x 1%nat - x 0%nat - x 2%nat
  | 2%nat => 2 * x 2%nat - x 1%nat - x 3%nat
  | 3%nat => 2 * x 3%nat - x 2%nat - x 4%nat
  | 4%nat => 2 * x 4%nat - x 3%nat - x 5%nat
  | 5%nat => 2 * x 5%nat - x 4%nat - x 0%nat
  | _ => 0
  end.

Definition v0 (i : nat) : Q := 1.

Definition v1 (i : nat) : Q :=
  match i with
  | 0%nat => 2 | 1%nat => 1 | 2%nat => -1 | 3%nat => -2
  | 4%nat => -1 | 5%nat => 1 | _ => 0
  end.

Definition v3 (i : nat) : Q :=
  match i with
  | 0%nat => 1 | 1%nat => 1 | 2%nat => -2 | 3%nat => 1
  | 4%nat => 1 | 5%nat => -2 | _ => 0
  end.

Definition v4 (i : nat) : Q :=
  match i with
  | 0%nat => 1 | 1%nat => -1 | 2%nat => 1 | 3%nat => -1
  | 4%nat => 1 | 5%nat => -1 | _ => 0
  end.

Theorem L6_v0_eigen : forall i, (i < 6)%nat -> L6 v0 i == 0 * v0 i.
Proof.
  intros i Hi. destruct i as [|[|[|[|[|[|i]]]]]]; [ | | | | | | lia];
    unfold L6, v0; ring.
Qed.

Theorem L6_v1_eigen : forall i, (i < 6)%nat -> L6 v1 i == 1 * v1 i.
Proof.
  intros i Hi. destruct i as [|[|[|[|[|[|i]]]]]]; [ | | | | | | lia];
    unfold L6, v1; ring.
Qed.

Theorem L6_v3_eigen : forall i, (i < 6)%nat -> L6 v3 i == 3 * v3 i.
Proof.
  intros i Hi. destruct i as [|[|[|[|[|[|i]]]]]]; [ | | | | | | lia];
    unfold L6, v3; ring.
Qed.

Theorem L6_v4_eigen : forall i, (i < 6)%nat -> L6 v4 i == 4 * v4 i.
Proof.
  intros i Hi. destruct i as [|[|[|[|[|[|i]]]]]]; [ | | | | | | lia];
    unfold L6, v4; ring.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions L5_cubic_identity.
Print Assumptions L6_v0_eigen.
Print Assumptions L6_v1_eigen.
Print Assumptions L6_v3_eigen.
Print Assumptions L6_v4_eigen.

End PentagonSpectrum.
