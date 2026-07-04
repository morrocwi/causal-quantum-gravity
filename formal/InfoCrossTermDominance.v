(* ===================================================================== *)
(*  RDL_CrossTermDominance.v                                               *)
(*  OFF-DIAGONAL COEFFICIENTS AND THE GRAPH-REPRESENTABILITY CRITERION —   *)
(*  the anisotropic quadratic form  A v^2 + 2B vw + C w^2  is a            *)
(*  NONNEGATIVELY WEIGHTED sum of direction squares (axis, axis,           *)
(*  diagonal) IF AND ONLY IF the off-diagonal coefficient is dominated:    *)
(*      0 <= B <= A  and  B <= C        (diagonal family  (v+w)^2 ), or    *)
(*      B <= 0, -B <= A and -B <= C     (antidiagonal family (v-w)^2).     *)
(*  Entirely over Q; both directions of both iffs are exact.               *)
(*                                                                        *)
(*  WHY THIS IS THE LAST RUNG'S THEOREM.  A cross-term stencil is a        *)
(*  graph Laplacian exactly when all its edge weights are nonnegative;     *)
(*  representability above IS that condition at the quadratic-form         *)
(*  level.  Under dominance, every Tier-0 result of this kernel line       *)
(*  (spectral ceiling, flux balance, product spectra) applies to the       *)
(*  augmented graph verbatim, and the readout along the three stencil      *)
(*  directions is supplied by the weighted multi-axis theorems of          *)
(*  RDL_ContinuumLimit_nD.v / RDL_WeightedReadout.v applied to the         *)
(*  axis and diagonal slices.  When dominance FAILS, the necessity         *)
(*  theorems below show NO nonnegative representation exists: the          *)
(*  obstruction is sharp, not an artifact of one decomposition.            *)
(*                                                                        *)
(*  CLAIMED HERE (candidate for coqc 8.18.0, axiom-free target):           *)
(*    decomp_pos_identity / decomp_neg_identity                            *)
(*        the two explicit decompositions (pure ring identities)           *)
(*    dominant_psd_pos / dominant_psd_neg                                  *)
(*        under dominance the form is positive semidefinite                *)
(*    repr_pos_iff_dominant / repr_neg_iff_dominant                        *)
(*        THE CRITERION, both directions exact: nonnegative                *)
(*        representability in a diagonal family  <->  dominance            *)
(*        (necessity is extracted by evaluating any representation at      *)
(*        (1,0), (0,1), (1,1) resp. (1,-1); the third weight is pinned     *)
(*        to +-B, so a supercritical B forces a negative weight)           *)
(*    cell_antidiag / cell_diag / cell_cross_polarization                  *)
(*        the exact lattice identities that carry the cross term on a      *)
(*        unit cell: the antidiagonal difference is the difference of      *)
(*        axis differences, and                                            *)
(*          dp^2 - dm^2 == (d1 + d1') * (d2 + d2')                         *)
(*        — the discrete polarization identity behind the stencil.         *)
(*                                                                        *)
(*  HONESTLY NOT CLAIMED: general-metric (non-dominant) convergence —      *)
(*  that is the open remainder, carried by imported literature at its      *)
(*  own tier, exactly as scoped at the top of the ladder.                  *)
(*                                                                        *)
(*  Pre-verified symbolically and with exact rationals (identities,        *)
(*  necessity on 300 random nonnegative representations, and the           *)
(*  sharpness example A = C = 1, B = 2) before authoring.                  *)
(*  Expected: Print Assumptions => Closed under the global context.        *)
(* ===================================================================== *)

Require Coq.QArith.QArith.
Require Coq.micromega.Lqa.

Module CrossTermDominance.

Import Coq.QArith.QArith.
Import Coq.micromega.Lqa.
Local Open Scope Q_scope.

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

(* ------------------------------------------------------------------ *)
(* THE TWO DECOMPOSITIONS (exact ring identities)                      *)
(* ------------------------------------------------------------------ *)

Theorem decomp_pos_identity : forall A B C v w : Q,
  A * (v * v) + 2 * B * (v * w) + C * (w * w)
  == (A - B) * (v * v) + (C - B) * (w * w) + B * ((v + w) * (v + w)).
Proof. intros. ring. Qed.

Theorem decomp_neg_identity : forall A B C v w : Q,
  A * (v * v) + 2 * B * (v * w) + C * (w * w)
  == (A + B) * (v * v) + (C + B) * (w * w) + (- B) * ((v - w) * (v - w)).
Proof. intros. ring. Qed.

(* ------------------------------------------------------------------ *)
(* SUFFICIENCY: under dominance the form is a nonnegative edge-square  *)
(* combination, hence positive semidefinite                            *)
(* ------------------------------------------------------------------ *)

Theorem dominant_psd_pos : forall A B C v w : Q,
  0 <= B -> B <= A -> B <= C ->
  0 <= A * (v * v) + 2 * B * (v * w) + C * (w * w).
Proof.
  intros A B C v w HB HA HC.
  assert (Hid := decomp_pos_identity A B C v w).
  assert (H1 : 0 <= (A - B) * (v * v))
    by (apply Qmult_le_0_compat; [lra | apply sq_nonneg]).
  assert (H2 : 0 <= (C - B) * (w * w))
    by (apply Qmult_le_0_compat; [lra | apply sq_nonneg]).
  assert (H3 : 0 <= B * ((v + w) * (v + w)))
    by (apply Qmult_le_0_compat; [lra | apply sq_nonneg]).
  lra.
Qed.

Theorem dominant_psd_neg : forall A B C v w : Q,
  B <= 0 -> - B <= A -> - B <= C ->
  0 <= A * (v * v) + 2 * B * (v * w) + C * (w * w).
Proof.
  intros A B C v w HB HA HC.
  assert (Hid := decomp_neg_identity A B C v w).
  assert (H1 : 0 <= (A + B) * (v * v))
    by (apply Qmult_le_0_compat; [lra | apply sq_nonneg]).
  assert (H2 : 0 <= (C + B) * (w * w))
    by (apply Qmult_le_0_compat; [lra | apply sq_nonneg]).
  assert (H3 : 0 <= (- B) * ((v - w) * (v - w)))
    by (apply Qmult_le_0_compat; [lra | apply sq_nonneg]).
  lra.
Qed.

(* ------------------------------------------------------------------ *)
(* THE CRITERION: nonnegative representability in the diagonal family  *)
(* is EQUIVALENT to dominance (both directions exact)                  *)
(* ------------------------------------------------------------------ *)

Definition repr_pos (A B C : Q) : Prop :=
  exists w1 w2 w3 : Q,
    0 <= w1 /\ 0 <= w2 /\ 0 <= w3 /\
    forall v w : Q,
      A * (v * v) + 2 * B * (v * w) + C * (w * w)
      == w1 * (v * v) + w2 * (w * w) + w3 * ((v + w) * (v + w)).

Definition repr_neg (A B C : Q) : Prop :=
  exists w1 w2 w3 : Q,
    0 <= w1 /\ 0 <= w2 /\ 0 <= w3 /\
    forall v w : Q,
      A * (v * v) + 2 * B * (v * w) + C * (w * w)
      == w1 * (v * v) + w2 * (w * w) + w3 * ((v - w) * (v - w)).

Theorem repr_pos_iff_dominant : forall A B C : Q,
  repr_pos A B C <-> (0 <= B /\ B <= A /\ B <= C).
Proof.
  intros A B C. split.
  - (* necessity: evaluate any representation at (1,0), (0,1), (1,1) *)
    intros [w1 [w2 [w3 [H1 [H2 [H3 Hid]]]]]].
    assert (E10 := Hid 1 0).
    assert (E01 := Hid 0 1).
    assert (E11 := Hid 1 1).
    split; [lra | split; lra].
  - (* sufficiency: the explicit witness *)
    intros [HB [HA HC]].
    exists (A - B), (C - B), B.
    split; [lra |]. split; [lra |]. split; [lra |].
    intros v w. apply decomp_pos_identity.
Qed.

Theorem repr_neg_iff_dominant : forall A B C : Q,
  repr_neg A B C <-> (B <= 0 /\ - B <= A /\ - B <= C).
Proof.
  intros A B C. split.
  - (* necessity: evaluate at (1,0), (0,1), (1,-1) *)
    intros [w1 [w2 [w3 [H1 [H2 [H3 Hid]]]]]].
    assert (E10 := Hid 1 0).
    assert (E01 := Hid 0 1).
    assert (E1m := Hid 1 (- (1))).
    split; [lra | split; lra].
  - intros [HB [HA HC]].
    exists (A + B), (C + B), (- B).
    split; [lra |]. split; [lra |]. split; [lra |].
    intros v w. apply decomp_neg_identity.
Qed.

(* ------------------------------------------------------------------ *)
(* THE LATTICE CELL: the exact identities that carry the cross term.   *)
(* On a unit cell with corner values u00 u10 u01 u11, write            *)
(*   d1 = u10-u00, d1' = u11-u01  (the two axis-1 differences)         *)
(*   d2 = u01-u00, d2' = u11-u10  (the two axis-2 differences)         *)
(*   dp = u11-u00, dm = u10-u01   (the two cell diagonals)             *)
(* ------------------------------------------------------------------ *)

(* the antidiagonal is the difference of axis differences *)
Theorem cell_antidiag : forall u00 u10 u01 u11 : Q,
  u10 - u01 == (u10 - u00) - (u01 - u00)
  /\ u10 - u01 == (u11 - u01) - (u11 - u10).
Proof. intros. split; ring. Qed.

(* the diagonal is the sum of consecutive axis differences *)
Theorem cell_diag : forall u00 u10 u01 u11 : Q,
  u11 - u00 == (u10 - u00) + (u11 - u10)
  /\ u11 - u00 == (u01 - u00) + (u11 - u01).
Proof. intros. split; ring. Qed.

(* THE DISCRETE POLARIZATION IDENTITY: the difference of diagonal      *)
(* squares is exactly the symmetrized cross product of the axis        *)
(* differences — this is how the diagonal edges of the stencil carry   *)
(* the off-diagonal coefficient                                        *)
Theorem cell_cross_polarization : forall u00 u10 u01 u11 : Q,
  (u11 - u00) * (u11 - u00) - (u10 - u01) * (u10 - u01)
  == ((u10 - u00) + (u11 - u01)) * ((u01 - u00) + (u11 - u10)).
Proof. intros. ring. Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions decomp_pos_identity.
Print Assumptions decomp_neg_identity.
Print Assumptions dominant_psd_pos.
Print Assumptions dominant_psd_neg.
Print Assumptions repr_pos_iff_dominant.
Print Assumptions repr_neg_iff_dominant.
Print Assumptions cell_antidiag.
Print Assumptions cell_diag.
Print Assumptions cell_cross_polarization.

End CrossTermDominance.
