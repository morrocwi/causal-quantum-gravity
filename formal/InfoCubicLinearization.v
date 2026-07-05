(* ===================================================================== *)
(*  InfoCubicLinearization.v                                              *)
(*  EXACT LINEARIZATION OF THE CUBIC ON-SITE TERM OF THE MOTHER FORCE.    *)
(*                                                                        *)
(*  This is the first kernel file to open the potential slot V(x) of the  *)
(*  mother equation (here the minimal quartic, force term -g x^3).  The   *)
(*  results are exact algebraic identities over Q:                        *)
(*                                                                        *)
(*    lap_linear             the edge-difference operator is additive     *)
(*    cubic_expansion        g(p+d)^3 expands exactly, all four terms     *)
(*    force_expansion_exact  F(bg+pert) - F(bg) has the exact four-term   *)
(*                           form: linear edge part, first-order on-site  *)
(*                           part with pointwise coefficient shift        *)
(*                           qshift(i) = 3 g bg(i)^2, plus the explicit   *)
(*                           second- and third-order remainder            *)
(*    linearized_residual    subtracting the shifted linear operator      *)
(*                           leaves EXACTLY  -3 g bg pert^2 - g pert^3    *)
(*    qshift_nonneg /        the coefficient shift is nonnegative for     *)
(*    qshift_pos             g >= 0, and strictly positive on the         *)
(*                           support of the background when g > 0        *)
(*                                                                        *)
(*  HONESTLY NOT CLAIMED: any time-averaging / homogenization statement   *)
(*  (the passage from the pointwise shift to an effective medium is a     *)
(*  separate, disclosed step outside this file), and any spectral or      *)
(*  propagation consequence.  Physics readings live in the papers, not    *)
(*  here.                                                                 *)
(*                                                                        *)
(*  Pre-verified symbolically (all identities, sympy) before authoring.   *)
(*  Expected: Print Assumptions => Closed under the global context.       *)
(* ===================================================================== *)

Require Coq.Arith.PeanoNat.
Require Coq.Lists.List.
Require Coq.QArith.QArith.
Require Coq.micromega.Lqa.

Module CubicLinearization.

Import Coq.Lists.List. Import ListNotations.
Import Coq.Arith.PeanoNat.
Import Coq.QArith.QArith.
Import Coq.micromega.Lqa.
Local Open Scope Q_scope.

Definition Edge : Type := (nat * nat)%type.

Definition esum (E : list Edge) (h : Edge -> Q) : Q :=
  fold_right (fun e acc => h e + acc) 0 E.

(* node form of the edge-difference (Laplacian) action *)
Definition lnode (E : list Edge) (x : nat -> Q) (i : nat) : Q :=
  esum E (fun e =>
    (if Nat.eqb (fst e) i then 1 else 0) * (x (fst e) - x (snd e))
    + (if Nat.eqb (snd e) i then 1 else 0) * (x (snd e) - x (fst e))).

(* total force at a node: linear edge part plus cubic on-site part *)
Definition force (E : list Edge) (K g : Q) (x : nat -> Q) (i : nat) : Q :=
  - K * lnode E x i - g * (x i * x i * x i).

(* the pointwise coefficient shift produced by a background *)
Definition qshift (g : Q) (bg : nat -> Q) (i : nat) : Q :=
  3 * g * (bg i * bg i).

(* ------------------------------------------------------------------ *)
(* Toolbox                                                             *)
(* ------------------------------------------------------------------ *)

Lemma esum_ext : forall E (f h : Edge -> Q),
  (forall e, In e E -> f e == h e) ->
  esum E f == esum E h.
Proof.
  induction E as [| e r IH]; intros f h H; simpl.
  - reflexivity.
  - rewrite (H e); [| left; reflexivity].
    rewrite (IH f h); [reflexivity | intros e' He'; apply H; right; exact He'].
Qed.

Lemma esum_plus : forall E (f h : Edge -> Q),
  esum E (fun e => f e + h e) == esum E f + esum E h.
Proof.
  induction E as [| e r IH]; intros f h; simpl; [ring | rewrite IH; ring].
Qed.

(* ------------------------------------------------------------------ *)
(* The edge part is additive                                           *)
(* ------------------------------------------------------------------ *)

Theorem lap_linear : forall E (bg pert : nat -> Q) (i : nat),
  lnode E (fun j => bg j + pert j) i == lnode E bg i + lnode E pert i.
Proof.
  intros E bg pert i. unfold lnode.
  rewrite (esum_ext E
    (fun e =>
      (if Nat.eqb (fst e) i then 1 else 0)
        * ((bg (fst e) + pert (fst e)) - (bg (snd e) + pert (snd e)))
      + (if Nat.eqb (snd e) i then 1 else 0)
        * ((bg (snd e) + pert (snd e)) - (bg (fst e) + pert (fst e))))
    (fun e =>
      ((if Nat.eqb (fst e) i then 1 else 0) * (bg (fst e) - bg (snd e))
       + (if Nat.eqb (snd e) i then 1 else 0) * (bg (snd e) - bg (fst e)))
      + ((if Nat.eqb (fst e) i then 1 else 0) * (pert (fst e) - pert (snd e))
         + (if Nat.eqb (snd e) i then 1 else 0) * (pert (snd e) - pert (fst e)))));
    [ apply (esum_plus E
        (fun e => (if Nat.eqb (fst e) i then 1 else 0) * (bg (fst e) - bg (snd e))
                  + (if Nat.eqb (snd e) i then 1 else 0) * (bg (snd e) - bg (fst e)))
        (fun e => (if Nat.eqb (fst e) i then 1 else 0) * (pert (fst e) - pert (snd e))
                  + (if Nat.eqb (snd e) i then 1 else 0) * (pert (snd e) - pert (fst e))))
    | intros e _; ring ].
Qed.

(* ------------------------------------------------------------------ *)
(* The cubic part expands exactly                                      *)
(* ------------------------------------------------------------------ *)

Theorem cubic_expansion : forall g p d : Q,
  g * ((p + d) * (p + d) * (p + d))
  == g * (p * p * p) + 3 * g * (p * p) * d
     + 3 * g * p * (d * d) + g * (d * d * d).
Proof.
  intros g p d. ring.
Qed.

(* ------------------------------------------------------------------ *)
(* THE EXACT FOUR-TERM EXPANSION OF THE FORCE                           *)
(* ------------------------------------------------------------------ *)

Theorem force_expansion_exact :
  forall E (K g : Q) (bg pert : nat -> Q) (i : nat),
  force E K g (fun j => bg j + pert j) i - force E K g bg i
  == - K * lnode E pert i
     - qshift g bg i * pert i
     - 3 * g * bg i * (pert i * pert i)
     - g * (pert i * pert i * pert i).
Proof.
  intros E K g bg pert i. unfold force, qshift.
  rewrite (lap_linear E bg pert i).
  ring.
Qed.

(* subtracting the shifted linear operator leaves an EXACT remainder    *)
(* of second and third order only                                       *)
Theorem linearized_residual :
  forall E (K g : Q) (bg pert : nat -> Q) (i : nat),
  (force E K g (fun j => bg j + pert j) i - force E K g bg i)
  - (- K * lnode E pert i - qshift g bg i * pert i)
  == - 3 * g * bg i * (pert i * pert i)
     - g * (pert i * pert i * pert i).
Proof.
  intros E K g bg pert i.
  rewrite (force_expansion_exact E K g bg pert i).
  ring.
Qed.

(* ------------------------------------------------------------------ *)
(* Sign of the coefficient shift                                       *)
(* ------------------------------------------------------------------ *)

Theorem qshift_nonneg : forall (g : Q) (bg : nat -> Q) (i : nat),
  0 <= g -> 0 <= qshift g bg i.
Proof.
  intros g bg i Hg. unfold qshift.
  assert (Hsq : 0 <= bg i * bg i) by nra.
  nra.
Qed.

Theorem qshift_pos : forall (g : Q) (bg : nat -> Q) (i : nat),
  0 < g -> ~ (bg i == 0) -> 0 < qshift g bg i.
Proof.
  intros g bg i Hg Hne. unfold qshift.
  assert (Hsq : 0 < bg i * bg i).
  { destruct (Q_dec 0 (bg i)) as [[Hlt | Hgt] | Heq].
    - nra.
    - nra.
    - exfalso. apply Hne. symmetry. exact Heq. }
  nra.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions lap_linear.
Print Assumptions cubic_expansion.
Print Assumptions force_expansion_exact.
Print Assumptions linearized_residual.
Print Assumptions qshift_nonneg.
Print Assumptions qshift_pos.

End CubicLinearization.
