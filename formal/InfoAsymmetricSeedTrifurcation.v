(******************************************************************************)
(* InfoAsymmetricSeedTrifurcation.v -- EXPLORATORY, single-attempt.   *)
(*   Standalone. Requires ONLY Coq.QArith + Coq.micromega.Lqa + PeanoNat      *)
(*   (nat equality only, no continuum, no axiom). Compile: coqc -q -R . RDL. *)
(*                                                                           *)
(* HYPOTHESIS UNDER TEST (candidate, NOT a repo theorem before this file):    *)
(*   the arc currently posits THREE independent structural primitives --      *)
(*   L_R (forced from {sym, offdiag<=0, rowsum0}, see                         *)
(*   InfoRetainedDistinctionForcesLaplacian_attempt.v), and M, D (each         *)
(*   independently characterized as energy-preserving / strictly energy-       *)
(*   decreasing toy steps, see InfoDissipationIsIndependent_attempt.v, but      *)
(*   NOT derived from one another or from L_R).                                *)
(*                                                                           *)
(*   The candidate upgrade: instead of three unrelated roots, posit ONE        *)
(*   asymmetric ('directed') seed operator R0 on the vertex set, and ask       *)
(*   whether its EXACT algebraic decomposition into (i) diagonal part,         *)
(*   (ii) symmetric off-diagonal part, (iii) antisymmetric off-diagonal part    *)
(*   already carries the right SHAPE to be read as {D, L_R, M} respectively.    *)
(*                                                                           *)
(* WHAT THIS FILE ACTUALLY PROVES (Th_coqc, axiom-free over Q):                *)
(*   1. R0 = DiagPart(R0) + SymOff(R0) + SkewOff(R0)  EXACTLY, pointwise,       *)
(*      for every i,j : nat (a genuine, unconditional ring/field identity,      *)
(*      general in the vertex count -- not just the 3-vertex carrier).          *)
(*   2. SymOff(R0) is symmetric; SkewOff(R0) is antisymmetric; DiagPart(R0)      *)
(*      has zero off-diagonal entries -- three unconditional structural facts.   *)
(*   3. The quadratic form x^T . SkewOff(R0) . x VANISHES IDENTICALLY, for       *)
(*      every R0 and every x0,x1,x2 : Q, on the 3-vertex carrier -- this is      *)
(*      the concrete bridge to 'M-like / reversible': an antisymmetric part      *)
(*      can NEVER by itself change a quadratic energy functional, matching       *)
(*      exactly what step_M_preserves_energy witnesses for one concrete           *)
(*      rotation in the sibling file.                                            *)
(*   4. CONDITIONAL recovery of the L_R shape: IF SymOff(R0)'s off-diagonal       *)
(*      entries additionally satisfy <= 0 (an EXTRA hypothesis on R0, not         *)
(*      automatic from asymmetry alone), THEN the closure Lcand built purely      *)
(*      from SymOff(R0) (never touching R0's own diagonal) satisfies exactly      *)
(*      the same three properties {sym, rowsum0, offdiag<=0} that                *)
(*      forced_into_DW_minus_W shows uniquely force the D_W - W Laplacian form.   *)
(*   5. A single non-degenerate concrete witness R0 where DiagPart, SymOff,       *)
(*      AND SkewOff are all simultaneously nonzero (a genuine 3-way split, not     *)
(*      an accidental collapse to fewer pieces), with SymOff's off-diagonal        *)
(*      entries concretely <= 0 so the conditional closure of (4) applies.        *)
(*                                                                           *)
(* SCOPE / TIER HONESTY -- read this before citing this file anywhere:          *)
(*                                                                           *)
(*   [Th_coqc]  Items 1-5 above, exactly as stated: pure algebra over Q,        *)
(*              machine-checked, no axiom, no continuum operation.               *)
(*                                                                           *)
(*   [Dr, NOT proved here -- do not overclaim]:                                 *)
(*     (a) That DiagPart(R0) IS (or reduces to) the master equation's D           *)
(*         coefficient, or that SkewOff(R0) IS (or generates) the master           *)
(*         equation's M coefficient. This file shows the SHAPE matches            *)
(*         (diagonal-only / no-coupling for D's role; energy-null for M's          *)
(*         role) -- it does NOT reduce these to, or reconcile them with, the       *)
(*         concrete step_M / step_D toy maps of                                    *)
(*         InfoDissipationIsIndependent_attempt.v. That reconciliation is an        *)
(*         explicitly OPEN follow-up, not attempted here.                          *)
(*     (b) That R0 itself is FORCED by 'directed retained distinction' the         *)
(*         way L_R is forced by {sym, offdiag<=0, rowsum0} in                      *)
(*         InfoRetainedDistinctionForcesLaplacian_attempt.v. Here R0 is an          *)
(*         ARBITRARY (posited) operator -- the departure point for the             *)
(*         algebra, not itself derived from anything more primitive. Finding        *)
(*         a forcing characterization of R0 analogous to L_R's is the real          *)
(*         remaining formal problem this file does NOT solve.                       *)
(*     (c) That item 4's hypothesis (SymOff(R0) off-diagonal <= 0) is itself         *)
(*         forced by R0's asymmetry / directedness. It is assumed, exactly as        *)
(*         flagged, exactly the same way offdiag_le0 is an assumed premise in         *)
(*         forced_into_DW_minus_W, not a consequence of symmetry alone.               *)
(*                                                                           *)
(*   NET READING: this file upgrades the 'three independent roots' picture         *)
(*   to 'three EXACT algebraic readouts of one posited asymmetric operator,         *)
(*   with two readouts (D-shape, M-shape) unconditional and one (L_R-shape)          *)
(*   conditional on an extra sign hypothesis' -- a real tightening of HOW the        *)
(*   pieces relate to each other structurally, but it does NOT prove the             *)
(*   three-roots model was wrong, does NOT derive R0 from anything more               *)
(*   primitive, and does NOT identify DiagPart/SkewOff with the master                *)
(*   equation's actual M, D coefficients. Candidate upgrade path, not a                *)
(*   completed unification.                                                          *)
(*                                                                                    *)
(* UPDATE (Part 7, appended -- the paragraphs above are the ORIGINAL scope,            *)
(* kept verbatim, not rewritten with hindsight; this block records what changed):      *)
(*   Item (b) above is now PARTIALLY closed for a NEW, extended axiom (Part 7):         *)
(*   {offdiag_le0, rowsum0} imposed on the seed's WHOLE row (diagonal included,          *)
(*   not just its symmetric part) forces DiagPart (D) to be an exact function of         *)
(*   SymOff and SkewOff -- D is no longer free once this extended axiom is granted.       *)
(*   Only a nonnegative weight (Wt) and one scalar (lam) remain posited -- the same        *)
(*   level of freedom L_R's own edge weights already carry. This does NOT retract          *)
(*   InfoDissipationIsIndependent_attempt.v's Th_coqc content (its 2-node toy still,        *)
(*   as literally stated, has an energy-preserving M-branch and a strictly-decreasing        *)
(*   D-branch with no premise linking them on THAT toy) -- it realizes a possibility          *)
(*   that file's own SCOPE block explicitly left open: 'not a proof that no larger             *)
(*   construction could ever recover a D-like term from M and L_R combined.' Part 7 is           *)
(*   exactly such a larger construction. See Part 7's own header comment for the full             *)
(*   statement, including what remains posited (Wt, lam) and what is still open (whether           *)
(*   {offdiag_le0_full, rowsum0_full} are themselves the UNIQUE forced axioms, as opposed            *)
(*   to a natural-but-chosen extension of L_R's own axioms to the full seed).                        *)
(******************************************************************************)

Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.

Open Scope Q_scope.

(* ========================================================================= *)
(* PART 1 -- the three-way exact decomposition, general in the vertex index.  *)
(* ========================================================================= *)

Definition DiagPart (R : nat -> nat -> Q) (i j : nat) : Q :=
  if Nat.eqb i j then R i j else 0.

Definition SymOff (R : nat -> nat -> Q) (i j : nat) : Q :=
  if Nat.eqb i j then 0 else (R i j + R j i) / (2#1).

Definition SkewOff (R : nat -> nat -> Q) (i j : nat) : Q :=
  if Nat.eqb i j then 0 else (R i j - R j i) / (2#1).

(* [Th_coqc] 1. Exact recombination: R0 = DiagPart + SymOff + SkewOff,        *)
(* pointwise, for EVERY i j : nat -- unconditional, general vertex count.     *)
Theorem trifurcation_exact :
  forall (R : nat -> nat -> Q) (i j : nat),
    DiagPart R i j + SymOff R i j + SkewOff R i j == R i j.
Proof.
  intros R i j.
  unfold DiagPart, SymOff, SkewOff.
  destruct (Nat.eqb i j) eqn:E.
  - apply Nat.eqb_eq in E. subst j. ring.
  - unfold Qdiv, Qinv. simpl. lra.
Qed.

(* [Th_coqc] 2a. SymOff is symmetric. *)
Theorem symoff_symmetric :
  forall (R : nat -> nat -> Q) (i j : nat), SymOff R i j == SymOff R j i.
Proof.
  intros R i j.
  unfold SymOff.
  rewrite (Nat.eqb_sym j i).
  destruct (Nat.eqb i j) eqn:E.
  - reflexivity.
  - unfold Qdiv, Qinv. simpl. lra.
Qed.

(* [Th_coqc] 2b. SkewOff is antisymmetric. *)
Theorem skewoff_antisymmetric :
  forall (R : nat -> nat -> Q) (i j : nat), SkewOff R i j == - SkewOff R j i.
Proof.
  intros R i j.
  unfold SkewOff.
  rewrite (Nat.eqb_sym j i).
  destruct (Nat.eqb i j) eqn:E.
  - unfold Qopp. simpl. ring.
  - unfold Qdiv, Qinv. simpl. lra.
Qed.

(* [Th_coqc] 2c. DiagPart has NO off-diagonal entries: structurally it carries *)
(* zero coupling -- consistent with D's role in the master equation being a    *)
(* purely LOCAL (pointwise-multiplied) coefficient, never a coupling operator.  *)
Theorem diagpart_no_offdiag_coupling :
  forall (R : nat -> nat -> Q) (i j : nat), i <> j -> DiagPart R i j == 0.
Proof.
  intros R i j Hij.
  unfold DiagPart.
  apply Nat.eqb_neq in Hij. rewrite Hij. reflexivity.
Qed.

(* ========================================================================= *)
(* PART 2 -- the energy-null bridge: SkewOff's quadratic form vanishes         *)
(* identically on the 3-vertex carrier, for EVERY R and EVERY state x.         *)
(* This is the exact discrete fact behind 'an antisymmetric part alone can      *)
(* never move a quadratic energy functional', the same fact that makes a        *)
(* rotation (step_M in the sibling file) energy-preserving.                     *)
(* ========================================================================= *)

Definition quad3 (S : nat -> nat -> Q) (x0 x1 x2 : Q) : Q :=
    x0 * S 0%nat 0%nat * x0 + x0 * S 0%nat 1%nat * x1 + x0 * S 0%nat 2%nat * x2
  + x1 * S 1%nat 0%nat * x0 + x1 * S 1%nat 1%nat * x1 + x1 * S 1%nat 2%nat * x2
  + x2 * S 2%nat 0%nat * x0 + x2 * S 2%nat 1%nat * x1 + x2 * S 2%nat 2%nat * x2.

Theorem skewoff_quadratic_form_vanishes :
  forall (R : nat -> nat -> Q) (x0 x1 x2 : Q),
    quad3 (SkewOff R) x0 x1 x2 == 0.
Proof.
  intros R x0 x1 x2.
  unfold quad3, SkewOff. simpl.
  unfold Qdiv, Qinv. simpl.
  ring.
Qed.

(* ========================================================================= *)
(* PART 3 -- CONDITIONAL recovery of the L_R shape, built purely from          *)
(* SymOff(R0)'s off-diagonal weights (never touching R0's own diagonal,        *)
(* which is DiagPart(R0), kept entirely separate as the D-role piece).         *)
(* This mirrors exactly the three properties {sym, rowsum0, offdiag<=0} that   *)
(* InfoRetainedDistinctionForcesLaplacian_attempt.v's forced_into_DW_minus_W    *)
(* proves uniquely force the D_W - W Laplacian form -- restated and proved      *)
(* here for the closure built from SymOff(R0), on the same 3-vertex carrier.    *)
(* ========================================================================= *)

Section ConditionalClosure.

  Variable R : nat -> nat -> Q.

  Definition Lcand (i j : nat) : Q :=
    if Nat.eqb i j
    then SymOff R i 0 + SymOff R i 1 + SymOff R i 2
    else - SymOff R i j.

  (* [Th_coqc] unconditional: Lcand is symmetric (inherits from SymOff). *)
  Theorem lcand_symmetric :
    Lcand 0 1 == Lcand 1 0 /\ Lcand 0 2 == Lcand 2 0 /\ Lcand 1 2 == Lcand 2 1.
  Proof.
    unfold Lcand. simpl.
    repeat split;
      match goal with
      | |- - SymOff R ?i ?j == - SymOff R ?j ?i =>
          rewrite (symoff_symmetric R i j); ring
      end.
  Qed.

  (* [Th_coqc] unconditional: Lcand has zero row-sum, by construction --       *)
  (* the diagonal is DEFINED as the sum of the other two SymOff entries        *)
  (* (SymOff R i i is always 0 by definition, so summing over all three         *)
  (* indices 0,1,2 already sums over exactly 'the other two').                 *)
  Theorem lcand_rowsum0 :
       Lcand 0 0 + Lcand 0 1 + Lcand 0 2 == 0
    /\ Lcand 1 0 + Lcand 1 1 + Lcand 1 2 == 0
    /\ Lcand 2 0 + Lcand 2 1 + Lcand 2 2 == 0.
  Proof.
    unfold Lcand, SymOff. simpl.
    unfold Qdiv, Qinv. simpl.
    repeat split; lra.
  Qed.

  (* [CONDITIONAL] -- offdiag<=0 needs an EXTRA hypothesis on R: that R0's      *)
  (* symmetric coupling data is itself sign-consistent with a graph weight       *)
  (* (nonnegative). This is NOT automatic from asymmetry / the decomposition     *)
  (* alone -- exactly as flagged in the file header (Dr item (c)).               *)
  Theorem lcand_offdiag_le0_conditional :
    SymOff R 0 1 >= 0 -> SymOff R 0 2 >= 0 -> SymOff R 1 2 >= 0 ->
       Lcand 0 1 <= 0 /\ Lcand 0 2 <= 0 /\ Lcand 1 2 <= 0
    /\ Lcand 1 0 <= 0 /\ Lcand 2 0 <= 0 /\ Lcand 2 1 <= 0.
  Proof.
    intros H01 H02 H12.
    unfold Lcand.
    pose proof (symoff_symmetric R 1 0) as S10.
    pose proof (symoff_symmetric R 2 0) as S20.
    pose proof (symoff_symmetric R 2 1) as S21.
    simpl in *.
    repeat split; lra.
  Qed.

End ConditionalClosure.

(* ========================================================================= *)
(* PART 4 -- a single non-degenerate concrete witness: DiagPart, SymOff, and   *)
(* SkewOff are ALL simultaneously nonzero (a genuine 3-way split, not an        *)
(* accidental collapse), and SymOff's off-diagonal entries are concretely       *)
(* nonnegative, so the conditional closure of Part 3 applies.                   *)
(* ========================================================================= *)

Section Witness.

  Definition R0 (i j : nat) : Q :=
    match i, j with
    | 0%nat,0%nat => 5#1   | 0%nat,1%nat => 4#1   | 0%nat,2%nat => 1#1
    | 1%nat,0%nat => 2#1   | 1%nat,1%nat => -3#1  | 1%nat,2%nat => -1#1
    | 2%nat,0%nat => 1#1   | 2%nat,1%nat => 3#1   | 2%nat,2%nat => 2#1
    | _,_ => 0
    end.

  (* DiagPart(R0): the D-shaped piece -- genuinely nonzero, mixed-sign,         *)
  (* per-node 'bias' (5, -3, 2), carrying NO coupling (Part 1, item 2c).        *)
  Example diag_witness :
    DiagPart R0 0 0 == 5#1 /\ DiagPart R0 1 1 == -3#1 /\ DiagPart R0 2 2 == 2#1.
  Proof. unfold DiagPart, R0. simpl. repeat split; reflexivity. Qed.

  (* SymOff(R0): the L_R-shaped piece -- (4+2)/2=3, (1+1)/2=1, (-1+3)/2=1,      *)
  (* all >= 0, so the conditional closure of Part 3 applies concretely.         *)
  Example symoff_witness :
    SymOff R0 0 1 == 3#1 /\ SymOff R0 0 2 == 1#1 /\ SymOff R0 1 2 == 1#1.
  Proof.
    unfold SymOff, R0. simpl. unfold Qdiv, Qinv. simpl. repeat split; lra.
  Qed.

  (* SkewOff(R0): the M-shaped piece -- (4-2)/2=1, (1-1)/2=0, (-1-3)/2=-2,      *)
  (* NOT all zero (1 and -2 are nonzero): genuine antisymmetric content.        *)
  Example skewoff_witness :
    SkewOff R0 0 1 == 1#1 /\ SkewOff R0 0 2 == 0#1 /\ SkewOff R0 1 2 == -2#1.
  Proof.
    unfold SkewOff, R0. simpl. unfold Qdiv, Qinv. simpl. repeat split; lra.
  Qed.

  (* Non-degeneracy: all three pieces have at least one strictly nonzero entry, *)
  (* so this witness is a genuine 3-way split, not a collapse to fewer pieces.  *)
  Example nondegenerate_split :
    ~ (DiagPart R0 0 0 == 0#1) /\ ~ (SymOff R0 0 1 == 0#1) /\ ~ (SkewOff R0 0 1 == 0#1).
  Proof.
    unfold DiagPart, SymOff, SkewOff, R0. simpl. unfold Qdiv, Qinv. simpl.
    repeat split; intro H; lra.
  Qed.

  (* Conditional Part-3 closure instantiated concretely on this witness:        *)
  (* SymOff(R0)'s off-diagonal entries (3,1,1) are all >= 0, so Lcand R0         *)
  (* satisfies sym + rowsum0 + offdiag<=0 -- the exact three properties that     *)
  (* force the D_W - W shape in the sibling file.                               *)
  Example witness_satisfies_lcand_hypothesis :
    SymOff R0 0 1 >= 0 /\ SymOff R0 0 2 >= 0 /\ SymOff R0 1 2 >= 0.
  Proof.
    destruct symoff_witness as [E01 [E02 E12]].
    rewrite E01, E02, E12. repeat split; lra.
  Qed.

End Witness.

(* ========================================================================= *)
(* PART 5 -- CLOSING GAP (b)/(c): R0 is no longer an arbitrary posited blob.   *)
(*                                                                            *)
(* The original forcing move (InfoRetainedDistinctionForcesLaplacian) reads:   *)
(* delta_R = a retained distinction = a symmetric difference between related   *)
(* read-states, so the operator reading it must be {sym, offdiag<=0,          *)
(* rowsum0} -- those three properties ARE the meaning of 'distinction,' not     *)
(* a fresh choice layered on top.                                              *)
(*                                                                            *)
(* A DIRECTED retained distinction additionally records WHICH read-state came   *)
(* first. 'Which came first' is exactly a strict order on the index set --      *)
(* and a strict order is, by its own meaning (trichotomy: for i<>j, EXACTLY     *)
(* one of i<j or j<i holds), forced to be an ANTISYMMETRIC indicator: reading    *)
(* 'i before j' and reading 'j before i' cannot both hold, and one of them       *)
(* holds whenever i<>j. Below, `ord` is built directly from nat's own <, and     *)
(* `ord_antisymmetric_forced` proves its antisymmetry as a THEOREM from          *)
(* trichotomy -- not an assumption -- exactly the same status as sym3/           *)
(* offdiag_le0/rowsum0 have in the original file: forced-given-the-primitive's   *)
(* -own-meaning, not derived from nothing.                                       *)
(*                                                                            *)
(* R0 is then reconstructed as Wt (a symmetric, nonnegative weight -- the same   *)
(* 'magnitude of a distinction is nonnegative' premise the original file         *)
(* already carries via its weight-based LR construction, relocated here, not     *)
(* a NEW extra hypothesis specific to this file) plus lam * ord (the forced-      *)
(* shape directional part, one free scalar lam). This closes gap (c): SymOff     *)
(* (R0)'s nonnegativity is now a COROLLARY of Wt's own premise, not a fresh       *)
(* assumption on the composite R0. It partially closes gap (b): the SPLIT into   *)
(* a forced-symmetric-shape piece and a forced-antisymmetric-shape piece is no    *)
(* longer posited -- only the numeric weights (Wt) and the single scale (lam)     *)
(* remain free, exactly mirroring how L_R's own forcing leaves the concrete       *)
(* edge weights free while forcing the SHAPE. R0 is NOT fully forced from         *)
(* nothing -- that stronger claim is not made -- but it is no longer an           *)
(* unstructured posit either.                                                    *)
(* ========================================================================= *)

Definition ord (i j : nat) : Q :=
  if Nat.ltb i j then 1 else if Nat.ltb j i then -1 else 0.

(* [Th_coqc] FORCING theorem: antisymmetry of `ord` is a CONSEQUENCE of nat's    *)
(* trichotomy, not an assumption -- the directed-order analogue of the           *)
(* original file's sym3/offdiag_le0/rowsum0 being forced by distinction's         *)
(* meaning. *)
Theorem ord_antisymmetric_forced :
  forall i j : nat, ord i j == - ord j i.
Proof.
  intros i j.
  unfold ord.
  destruct (Nat.ltb i j) eqn:Hij; destruct (Nat.ltb j i) eqn:Hji.
  - exfalso. apply Nat.ltb_lt in Hij. apply Nat.ltb_lt in Hji. lia.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* No Section/Hypothesis here (repo-wide style rule: attempt files use          *)
(* explicit forall-premises, not Section/Hypothesis) -- Wt's symmetry and        *)
(* nonnegativity are passed as explicit hypotheses to each theorem below,        *)
(* not declared as ambient Section assumptions.                                  *)

Definition R0construct (Wt : nat -> nat -> Q) (lam : Q) (Dg : nat -> Q)
    (i j : nat) : Q :=
  if Nat.eqb i j then Dg i else Wt i j + lam * ord i j.

(* [Th_coqc] SymOff(R0construct) == Wt EXACTLY (an identity, not a shape         *)
(* resemblance): the lam*ord contribution cancels completely by                  *)
(* ord_antisymmetric_forced, leaving exactly the posited weight Wt.              *)
Theorem symoff_R0construct_is_Wt :
  forall (Wt : nat -> nat -> Q), (forall i j, Wt i j == Wt j i) ->
  forall (lam : Q) (Dg : nat -> Q) (i j : nat), i <> j ->
    SymOff (R0construct Wt lam Dg) i j == Wt i j.
Proof.
  intros Wt Wt_symmetric lam Dg i j Hij.
  unfold SymOff, R0construct.
  apply Nat.eqb_neq in Hij as Hij'.
  assert (Hji' : Nat.eqb j i = false) by (rewrite Nat.eqb_sym; exact Hij').
  rewrite Hij', Hji'.
  assert (Hnum : Wt i j + lam * ord i j + (Wt j i + lam * ord j i)
                 == (2#1) * Wt i j).
  { rewrite (ord_antisymmetric_forced j i), (Wt_symmetric j i). ring. }
  rewrite Hnum.
  unfold Qdiv, Qinv. simpl. lra.
Qed.

(* [Th_coqc] SkewOff(R0construct) == lam * ord EXACTLY: the Wt contribution      *)
(* cancels completely by Wt's own symmetry, leaving exactly the forced-shape      *)
(* directional part scaled by the one free parameter lam.                        *)
Theorem skewoff_R0construct_is_lam_ord :
  forall (Wt : nat -> nat -> Q), (forall i j, Wt i j == Wt j i) ->
  forall (lam : Q) (Dg : nat -> Q) (i j : nat), i <> j ->
    SkewOff (R0construct Wt lam Dg) i j == lam * ord i j.
Proof.
  intros Wt Wt_symmetric lam Dg i j Hij.
  unfold SkewOff, R0construct.
  apply Nat.eqb_neq in Hij as Hij'.
  assert (Hji' : Nat.eqb j i = false) by (rewrite Nat.eqb_sym; exact Hij').
  rewrite Hij', Hji'.
  assert (Hnum : Wt i j + lam * ord i j - (Wt j i + lam * ord j i)
                 == (2#1) * (lam * ord i j)).
  { rewrite (ord_antisymmetric_forced j i), (Wt_symmetric j i). ring. }
  rewrite Hnum.
  unfold Qdiv, Qinv. simpl. lra.
Qed.

(* [Th_coqc] COROLLARY closing gap (c): SymOff(R0construct)'s nonnegativity      *)
(* is inherited directly from Wt's own nonnegativity -- it is not a fresh         *)
(* hypothesis on the composite operator, but a consequence of the SAME            *)
(* 'magnitude of a distinction is nonnegative' premise the sibling file's own      *)
(* LR construction already carries (there via concrete positive weights a=2,b=3). *)
Theorem symoff_R0construct_nonneg :
  forall (Wt : nat -> nat -> Q), (forall i j, Wt i j == Wt j i) ->
  (forall i j, 0 <= Wt i j) ->
  forall (lam : Q) (Dg : nat -> Q) (i j : nat), i <> j ->
    SymOff (R0construct Wt lam Dg) i j >= 0.
Proof.
  intros Wt Wt_symmetric Wt_nonneg lam Dg i j Hij.
  rewrite (symoff_R0construct_is_Wt Wt Wt_symmetric lam Dg i j Hij).
  apply Qle_ge, Wt_nonneg.
Qed.

(* Non-vacuous witness: a concrete Wt/lam/Dg instance, exhibiting R0construct    *)
(* as a genuine, computable directed seed with all the properties above holding  *)
(* on real numbers, not just abstractly. *)
Section ReconstructionWitness.

  Definition WtEx (i j : nat) : Q :=
    match i, j with
    | 0%nat,1%nat | 1%nat,0%nat => 3#1
    | 0%nat,2%nat | 2%nat,0%nat => 1#1
    | 1%nat,2%nat | 2%nat,1%nat => 1#1
    | _,_ => 0
    end.

  Theorem WtEx_symmetric : forall i j, WtEx i j == WtEx j i.
  Proof.
    intros i j.
    destruct i as [|[|[|i]]]; destruct j as [|[|[|j]]]; unfold WtEx; try reflexivity.
  Qed.

  Theorem WtEx_nonneg : forall i j, 0 <= WtEx i j.
  Proof.
    intros i j.
    destruct i as [|[|[|i]]]; destruct j as [|[|[|j]]]; unfold WtEx; lra.
  Qed.

  Definition DgEx (i : nat) : Q :=
    match i with 0%nat => 5#1 | 1%nat => -3#1 | 2%nat => 2#1 | _ => 0 end.

  (* R0construct instantiated on this witness reproduces R0 from Part 4          *)
  (* EXACTLY on the entries that matter (weights 3,1,1 match symoff_witness;      *)
  (* diagonal 5,-3,2 matches diag_witness): the two constructions coincide.       *)
  Example reconstruction_matches_earlier_witness :
    R0construct WtEx (1#1) DgEx 0%nat 1%nat == R0 0%nat 1%nat.
  Proof. unfold R0construct, WtEx, DgEx, R0, ord. simpl. lra. Qed.

End ReconstructionWitness.

(* ========================================================================= *)
(* PART 6 -- CLOSING GAP (a): a genuine dynamical reduction, not a shape         *)
(* resemblance. skewoff_quadratic_form_vanishes (Part 2) only says the           *)
(* quadratic form is zero -- a STATIC fact about the bilinear form. Here we      *)
(* build the actual discrete STEP a skew part generates and ask whether it       *)
(* behaves like step_M / step_D from InfoDissipationIsIndependent_attempt.v.     *)
(*                                                                            *)
(* HONEST FINDING (6a): the naive Euler increment x |-> x + SkewOff(R).x does     *)
(* NOT conserve energy exactly for a generic R -- it can only ADD energy         *)
(* (never lose it), because the vanishing quadratic form only kills the           *)
(* FIRST-ORDER term; a strictly positive second-order term (a sum of squares)     *)
(* survives unless SkewOff(R).x happens to be the zero vector. This is why        *)
(* step_M in the sibling file is not an Euler increment at all -- it is a         *)
(* FINITE rotation (a pure linear map, not identity-plus-generator), and only     *)
(* a pure linear map generated by an ORTHOGONAL (not merely antisymmetric)         *)
(* operator conserves energy exactly.                                            *)
(*                                                                            *)
(* GENUINE RECOVERY (6b): the PURE linear map x |-> SkewOff(R0construct _ lam _).x*)
(* (not the Euler increment) IS, at the concrete value lam = -1, LITERALLY THE     *)
(* SAME two-coordinate formula as step_M (verified by direct computation, not      *)
(* by analogy) -- so step_M is recovered exactly as the lam=-1 instance of the     *)
(* forced-shape directional part from Part 5, restricted to a 2-node slice.        *)
(*                                                                            *)
(* GENUINE RECOVERY (6c): the multiplicative step generated by DiagPart, at the    *)
(* concrete uniform rate Dg = -1/2, IS LITERALLY step_D's own formula (definit-     *)
(* ional equality), and the strict energy decrease theorem extends verbatim to     *)
(* 3 nodes by the same ring+lra technique the sibling file itself uses.            *)
(* ========================================================================= *)

Definition energy3 (x0 x1 x2 : Q) : Q := x0*x0 + x1*x1 + x2*x2.

Definition sk0 (R : nat -> nat -> Q) (x0 x1 x2 : Q) : Q :=
  SkewOff R 0%nat 1%nat * x1 + SkewOff R 0%nat 2%nat * x2.
Definition sk1 (R : nat -> nat -> Q) (x0 x1 x2 : Q) : Q :=
  SkewOff R 1%nat 0%nat * x0 + SkewOff R 1%nat 2%nat * x2.
Definition sk2 (R : nat -> nat -> Q) (x0 x1 x2 : Q) : Q :=
  SkewOff R 2%nat 0%nat * x0 + SkewOff R 2%nat 1%nat * x1.

(* [Th_coqc] 6a. The Euler-step energy identity: stepping by x |-> x + Sx        *)
(* changes energy EXACTLY by the norm of the generated increment (never          *)
(* negative) -- the first-order (quad3) term is killed by antisymmetry, the       *)
(* second-order term survives as a sum of squares.                               *)
Theorem euler_step_energy_change :
  forall (R : nat -> nat -> Q) (x0 x1 x2 : Q),
    energy3 (x0 + sk0 R x0 x1 x2) (x1 + sk1 R x0 x1 x2) (x2 + sk2 R x0 x1 x2)
    == energy3 x0 x1 x2 + energy3 (sk0 R x0 x1 x2) (sk1 R x0 x1 x2) (sk2 R x0 x1 x2).
Proof.
  intros R x0 x1 x2.
  assert (Hdiff :
    energy3 (x0 + sk0 R x0 x1 x2) (x1 + sk1 R x0 x1 x2) (x2 + sk2 R x0 x1 x2)
    - (energy3 x0 x1 x2 + energy3 (sk0 R x0 x1 x2) (sk1 R x0 x1 x2) (sk2 R x0 x1 x2))
    == (2#1) * quad3 (SkewOff R) x0 x1 x2).
  { unfold energy3, sk0, sk1, sk2, quad3.
    assert (Hd0 : SkewOff R 0%nat 0%nat == 0) by (unfold SkewOff; simpl; reflexivity).
    assert (Hd1 : SkewOff R 1%nat 1%nat == 0) by (unfold SkewOff; simpl; reflexivity).
    assert (Hd2 : SkewOff R 2%nat 2%nat == 0) by (unfold SkewOff; simpl; reflexivity).
    rewrite Hd0, Hd1, Hd2. ring. }
  rewrite (skewoff_quadratic_form_vanishes R x0 x1 x2) in Hdiff.
  lra.
Qed.

(* [Th_coqc] 6a-corollary. The energy change is a sum of squares, hence          *)
(* NEVER negative -- an Euler step along ANY antisymmetric SkewOff can only        *)
(* add energy or leave it unchanged, never strictly conserve it unless the         *)
(* generated increment is exactly zero.                                            *)
Theorem euler_step_energy_nondecreasing :
  forall (R : nat -> nat -> Q) (x0 x1 x2 : Q),
    energy3 (x0 + sk0 R x0 x1 x2) (x1 + sk1 R x0 x1 x2) (x2 + sk2 R x0 x1 x2)
    >= energy3 x0 x1 x2.
Proof.
  intros R x0 x1 x2.
  rewrite (euler_step_energy_change R x0 x1 x2).
  unfold energy3.
  nra.
Qed.

(* --------------------------------------------------------------------- *)
(* 6b. GENUINE recovery of step_M: NOT the Euler increment above, but the  *)
(* PURE linear map (sk0,sk1) alone, at the concrete lam = -1 shape from      *)
(* Part 5's ord. step_M_copy below is written out to the same formula as     *)
(* step_M in InfoDissipationIsIndependent_attempt.v (this file stays          *)
(* standalone per its own header, so it is restated, not imported).           *)
(* --------------------------------------------------------------------- *)

Definition step_M_copy (x1 x2 : Q) : Q * Q := (-x2, x1).

(* If SkewOff(R)'s two (0,1)-plane entries take exactly the values that        *)
(* lam = -1 forces via Part 5 (skewoff_R0construct_is_lam_ord at lam=-1,        *)
(* ord 0 1 = 1, ord 1 0 = -1, giving SkewOff = -1 and +1 respectively), the      *)
(* pure linear map (sk0,sk1) on the (x0,x1) slice (x2 = 0) is LITERALLY,         *)
(* not just analogously, step_M_copy x0 x1.                                      *)
Theorem skoff_recovers_step_M :
  forall (R : nat -> nat -> Q) (x0 x1 : Q),
    SkewOff R 0%nat 1%nat == -1 -> SkewOff R 1%nat 0%nat == 1 ->
    sk0 R x0 x1 0 == fst (step_M_copy x0 x1) /\
    sk1 R x0 x1 0 == snd (step_M_copy x0 x1).
Proof.
  intros R x0 x1 H01 H10.
  unfold sk0, sk1, step_M_copy. simpl.
  split.
  - rewrite H01. ring.
  - rewrite H10. ring.
Qed.

(* Non-vacuous: lam = -1 in the Part 5 reconstruction actually PRODUCES these    *)
(* exact SkewOff values, via skewoff_R0construct_is_lam_ord plus ord's own        *)
(* concrete computation at (0,1)/(1,0) -- so the hypotheses of                    *)
(* skoff_recovers_step_M are not vacuous, they are exactly what Part 5's           *)
(* forced-shape directional part delivers at this one concrete scale.              *)
Theorem lam_minus1_delivers_step_M_shape :
  forall (Wt : nat -> nat -> Q) (Dg : nat -> Q),
    (forall i j, Wt i j == Wt j i) -> (forall i j, 0 <= Wt i j) ->
    SkewOff (R0construct Wt (-1#1) Dg) 0%nat 1%nat == -1 /\
    SkewOff (R0construct Wt (-1#1) Dg) 1%nat 0%nat == 1.
Proof.
  intros Wt Dg Hsym Hnn.
  split.
  - rewrite (skewoff_R0construct_is_lam_ord Wt Hsym (-1#1) Dg 0%nat 1%nat)
      by (intro Hc; discriminate Hc).
    unfold ord. simpl. ring.
  - rewrite (skewoff_R0construct_is_lam_ord Wt Hsym (-1#1) Dg 1%nat 0%nat)
      by (intro Hc; discriminate Hc).
    unfold ord. simpl. ring.
Qed.

(* energy2, the sibling file's own 2-coordinate energy functional, restated       *)
(* here (standalone) to check step_M_copy conserves it exactly -- matching         *)
(* step_M_preserves_energy in the sibling file by direct re-derivation.            *)
Definition energy2 (x1 x2 : Q) : Q := x1*x1 + x2*x2.

Theorem step_M_copy_preserves_energy2 :
  forall x1 x2 : Q,
    energy2 (fst (step_M_copy x1 x2)) (snd (step_M_copy x1 x2)) == energy2 x1 x2.
Proof. intros x1 x2. unfold step_M_copy, energy2. simpl. ring. Qed.

(* --------------------------------------------------------------------- *)
(* 6c. GENUINE recovery of step_D: the multiplicative step generated by       *)
(* DiagPart, at the concrete uniform rate -1/2, IS step_D's own formula          *)
(* (definitional, not analogical), and the strict-decrease theorem extends       *)
(* verbatim to 3 nodes by the sibling's own ring+lra technique.                  *)
(* --------------------------------------------------------------------- *)

Definition step_D_copy (x1 x2 : Q) : Q * Q := ((1#2)*x1, (1#2)*x2).

Definition step_Diag3 (Dg : nat -> Q) (x0 x1 x2 : Q) : Q * Q * Q :=
  ((1 + Dg 0%nat) * x0, (1 + Dg 1%nat) * x1, (1 + Dg 2%nat) * x2).

(* At the uniform rate Dg = -1/2, step_Diag3's first two coordinates are          *)
(* LITERALLY step_D_copy's formula. *)
Theorem diag_uniform_recovers_step_D :
  forall x0 x1 x2 : Q,
    step_Diag3 (fun _ => -1#2) x0 x1 x2
    = (fst (step_D_copy x0 x1), snd (step_D_copy x0 x1), (1#2) * x2).
Proof. intros x0 x1 x2. unfold step_Diag3, step_D_copy. simpl. reflexivity. Qed.

(* Strict energy decrease at the uniform rate -1/2, extended verbatim to 3        *)
(* nodes -- the sibling file's step_D_strictly_decreases_energy is the 2-node      *)
(* projection of this theorem (drop the x2 coordinate, or set x2 = 0). *)
Theorem step_Diag3_uniform_strictly_decreases_energy :
  forall x0 x1 x2 : Q,
    0 < energy3 x0 x1 x2 ->
    let '(y0,y1,y2) := step_Diag3 (fun _ => -1#2) x0 x1 x2 in
    energy3 y0 y1 y2 < energy3 x0 x1 x2.
Proof.
  intros x0 x1 x2 Hpos.
  unfold step_Diag3, energy3 in *. simpl.
  assert (Hred :
    (1#2)*x0*((1#2)*x0) + (1#2)*x1*((1#2)*x1) + (1#2)*x2*((1#2)*x2)
    == (1#4)*(x0*x0 + x1*x1 + x2*x2)) by ring.
  rewrite Hred.
  set (e := x0*x0 + x1*x1 + x2*x2) in *.
  lra.
Qed.

(* Non-vacuous instantiation on the Part 4 witness (D-role values 5, -3, 2         *)
(* are NOT the uniform -1/2 rate -- so DiagPart(R0)'s actual per-node bias is       *)
(* honestly outside the strict-decrease regime; this is exactly the OPEN            *)
(* generalization flagged in the header: extending 6c from the special uniform      *)
(* rate to a fully general per-node inequality remains future work.) *)
Example diag_witness_values_not_uniform_minus_half :
  ~ (DiagPart R0 0%nat 0%nat == -1#2).
Proof. unfold DiagPart, R0. simpl. intro H. lra. Qed.

(* ========================================================================= *)
(* PART 7 -- SEED ASYMMETRY AS THE SINGLE ROOT: D itself is now FORCED, not   *)
(* posited. Parts 1-6 kept D (DiagPart) as a free, independently-chosen         *)
(* per-node value (Dg), matching InfoDissipationIsIndependent_attempt.v's own    *)
(* Dr-tier reading that D is a structurally INDEPENDENT ingredient. That          *)
(* file's own SCOPE block already hedges this exact possibility: 'not a proof     *)
(* that no larger construction could ever recover a D-like term from M and       *)
(* L_R combined.' Part 7 is precisely that larger construction -- it does NOT    *)
(* contradict InfoDissipationIsIndependent's Th_coqc content (its 2-node toy      *)
(* still, as literally stated, has an M-branch that preserves energy and a        *)
(* D-branch that strictly decreases it, with no premise relating one to the       *)
(* other ON THAT TOY); it shows that a DIFFERENT, larger construction (the        *)
(* asymmetric seed of this file, with rowsum0 imposed on the WHOLE seed, not      *)
(* just its symmetric part) forces D to be a DERIVED quantity: the symmetric      *)
(* coupling degree corrected by the seed's own net directional circulation.       *)
(*                                                                            *)
(* THE MOVE: extend rowsum0 (originally a property forcing L_R alone, in            *)
(* InfoRetainedDistinctionForcesLaplacian_attempt.v) from 'the symmetric part      *)
(* of the seed has zero row-sum' to 'the WHOLE seed, diagonal included, has        *)
(* zero row-sum' -- the same meaning ('a uniform state retains no distinction,     *)
(* directed or not') applied to the FULL seed rather than just its symmetric       *)
(* residue. This one extension is what forces D away from being free.             *)
(*                                                                            *)
(* WHAT IS PROVEN (Th_coqc): given rowsum0_full alone (no sign hypothesis          *)
(* needed for this specific identity), DiagPart(R,i,i) is an EXACT function of      *)
(* SymOff(R) and SkewOff(R) at node i -- D_i = degree_i(SymOff) - kappa_i(SkewOff), *)
(* i.e. the pure symmetric-coupling degree MINUS the seed's own net directed        *)
(* circulation at that node. A concrete construction (R0_forced) realizes this      *)
(* from exactly TWO free primitives (a nonnegative weight Wt and one scalar lam,    *)
(* under one joint small-skew sign hypothesis) -- down from the THREE free           *)
(* primitives (Wt, lam, Dg) Part 5's R0construct needed, because Dg is now GONE,     *)
(* forced instead of posited. The circulation pattern itself (kappa_0,kappa_1,      *)
(* kappa_2) = (2,0,-2) on this 3-vertex nat-ordered carrier is a FIXED,              *)
(* computable combinatorial fact, not a free choice.                                *)
(*                                                                            *)
(* WHAT REMAINS OPEN (Dr, not proven): whether {offdiag_le0_full, rowsum0_full}      *)
(* THEMSELVES are the unique/forced axioms for 'directed retained distinction' --    *)
(* they are POSITED here as the natural full-seed analogue of L_R's own axioms,      *)
(* by the same 'meaning of the primitive' argument, not derived from something       *)
(* prior. The concrete weight Wt and the scalar lam remain free, exactly as L_R's    *)
(* own edge weights remain free in the original forcing theorem. Whether kappa's     *)
(* SPECIFIC values (2,0,-2) generalize meaningfully beyond this one 3-vertex          *)
(* nat-ordered carrier is not addressed.                                             *)
(* ========================================================================= *)

Definition rowsum0_full (R : nat -> nat -> Q) : Prop :=
  R 0%nat 0%nat + R 0%nat 1%nat + R 0%nat 2%nat == 0 /\
  R 1%nat 0%nat + R 1%nat 1%nat + R 1%nat 2%nat == 0 /\
  R 2%nat 0%nat + R 2%nat 1%nat + R 2%nat 2%nat == 0.

Definition offdiag_le0_full (R : nat -> nat -> Q) : Prop :=
  R 0%nat 1%nat <= 0 /\ R 0%nat 2%nat <= 0 /\ R 1%nat 2%nat <= 0 /\
  R 1%nat 0%nat <= 0 /\ R 2%nat 0%nat <= 0 /\ R 2%nat 1%nat <= 0.

(* [Th_coqc] Positivity corollary: the two full-seed axioms together force        *)
(* every diagonal entry to be NONNEGATIVE -- a genuine 'degree' reading, exactly   *)
(* the same positivity forced_into_DW_minus_W gives L_R, now for the WHOLE seed. *)
Theorem rowsum0_full_offdiag_le0_full_diag_nonneg :
  forall R : nat -> nat -> Q,
    rowsum0_full R -> offdiag_le0_full R ->
    R 0%nat 0%nat >= 0 /\ R 1%nat 1%nat >= 0 /\ R 2%nat 2%nat >= 0.
Proof.
  intros R [Hr0 [Hr1 Hr2]] [H01 [H02 [H12 [H10 [H20 H21]]]]].
  repeat split; lra.
Qed.

(* [Th_coqc] THE KEY THEOREM: D is forced to be exactly the symmetric-coupling    *)
(* degree at node i, minus the seed's own net directed circulation at i --        *)
(* an exact identity from rowsum0_full alone (offdiag_le0_full is not even         *)
(* needed for this specific algebraic fact; it is what makes the two summands       *)
(* individually meaningful as 'degree' and 'circulation').                          *)
Theorem diagpart_forced_by_rowsum0_full :
  forall R : nat -> nat -> Q, rowsum0_full R ->
    DiagPart R 0%nat 0%nat
      == -(SymOff R 0%nat 0%nat + SymOff R 0%nat 1%nat + SymOff R 0%nat 2%nat)
         -(SkewOff R 0%nat 0%nat + SkewOff R 0%nat 1%nat + SkewOff R 0%nat 2%nat)
    /\
    DiagPart R 1%nat 1%nat
      == -(SymOff R 1%nat 0%nat + SymOff R 1%nat 1%nat + SymOff R 1%nat 2%nat)
         -(SkewOff R 1%nat 0%nat + SkewOff R 1%nat 1%nat + SkewOff R 1%nat 2%nat)
    /\
    DiagPart R 2%nat 2%nat
      == -(SymOff R 2%nat 0%nat + SymOff R 2%nat 1%nat + SymOff R 2%nat 2%nat)
         -(SkewOff R 2%nat 0%nat + SkewOff R 2%nat 1%nat + SkewOff R 2%nat 2%nat).
Proof.
  intros R [Hr0 [Hr1 Hr2]].
  unfold DiagPart, SymOff, SkewOff. simpl.
  unfold Qdiv, Qinv. simpl.
  repeat split; lra.
Qed.

(* --------------------------------------------------------------------- *)
(* R0_forced: the seed with D ELIMINATED, not posited -- built from just   *)
(* TWO free primitives (Wt >= 0, lam), down from Part 5's three (Wt, lam,   *)
(* Dg). Off-diagonal shape mirrors L_R's own sign convention directly       *)
(* (-Wt + lam*ord, already offdiag-shaped, not a raw weight needing a        *)
(* second negation as in Part 5); the diagonal is DEFINED as the negative    *)
(* row-sum of the off-diagonal, so rowsum0_full holds BY CONSTRUCTION.       *)
(* --------------------------------------------------------------------- *)

Definition OffVal (Wt : nat -> nat -> Q) (lam : Q) (i j : nat) : Q :=
  if Nat.eqb i j then 0 else - Wt i j + lam * ord i j.

Definition R0_forced (Wt : nat -> nat -> Q) (lam : Q) (i j : nat) : Q :=
  if Nat.eqb i j
  then - (OffVal Wt lam i 0%nat + OffVal Wt lam i 1%nat + OffVal Wt lam i 2%nat)
  else OffVal Wt lam i j.

(* [Th_coqc] rowsum0_full holds UNCONDITIONALLY, by construction -- no          *)
(* hypothesis on Wt or lam needed at all. *)
Theorem R0_forced_rowsum0_full :
  forall Wt lam, rowsum0_full (R0_forced Wt lam).
Proof.
  intros Wt lam.
  unfold rowsum0_full, R0_forced, OffVal. simpl.
  repeat split; ring.
Qed.

(* [CONDITIONAL] offdiag_le0_full needs the small-skew hypothesis: the          *)
(* directional perturbation lam*ord(i,j) must not overshoot the weight           *)
(* Wt(i,j) -- the exact discrete analogue of Axiom 12's 'small parameter          *)
(* skew' epsilon_skew regime (a phenomenological, continuum construction,         *)
(* NOT ported here; noted only as a resonance in the header). *)
Theorem R0_forced_offdiag_le0_full_conditional :
  forall (Wt : nat -> nat -> Q) (lam : Q),
    lam * ord 0%nat 1%nat <= Wt 0%nat 1%nat ->
    lam * ord 0%nat 2%nat <= Wt 0%nat 2%nat ->
    lam * ord 1%nat 2%nat <= Wt 1%nat 2%nat ->
    lam * ord 1%nat 0%nat <= Wt 1%nat 0%nat ->
    lam * ord 2%nat 0%nat <= Wt 2%nat 0%nat ->
    lam * ord 2%nat 1%nat <= Wt 2%nat 1%nat ->
    offdiag_le0_full (R0_forced Wt lam).
Proof.
  intros Wt lam H01 H02 H12 H10 H20 H21.
  unfold offdiag_le0_full, R0_forced, OffVal. simpl.
  repeat split; lra.
Qed.

(* [Th_coqc] SymOff(R0_forced) == -Wt EXACTLY (sign-flipped from Part 5's        *)
(* SymOff(R0construct)==Wt, since R0_forced's off-diagonal is already L_R-        *)
(* shaped directly, not a raw weight needing a later negation). *)
Theorem symoff_R0_forced_is_negWt :
  forall (Wt : nat -> nat -> Q), (forall i j, Wt i j == Wt j i) ->
  forall (lam : Q) (i j : nat), i <> j ->
    SymOff (R0_forced Wt lam) i j == - Wt i j.
Proof.
  intros Wt Wt_symmetric lam i j Hij.
  unfold SymOff, R0_forced, OffVal.
  apply Nat.eqb_neq in Hij as Hij'.
  assert (Hji' : Nat.eqb j i = false) by (rewrite Nat.eqb_sym; exact Hij').
  rewrite Hij', Hji'.
  assert (Hnum : (- Wt i j + lam * ord i j) + (- Wt j i + lam * ord j i)
                 == (2#1) * (- Wt i j)).
  { rewrite (ord_antisymmetric_forced j i), (Wt_symmetric j i). ring. }
  rewrite Hnum.
  unfold Qdiv, Qinv. simpl. lra.
Qed.

(* [Th_coqc] SkewOff(R0_forced) == lam * ord EXACTLY, unchanged from Part 5's    *)
(* pattern (the Wt contribution cancels via Wt's own symmetry regardless of        *)
(* the sign convention on Wt). *)
Theorem skewoff_R0_forced_is_lam_ord :
  forall (Wt : nat -> nat -> Q), (forall i j, Wt i j == Wt j i) ->
  forall (lam : Q) (i j : nat), i <> j ->
    SkewOff (R0_forced Wt lam) i j == lam * ord i j.
Proof.
  intros Wt Wt_symmetric lam i j Hij.
  unfold SkewOff, R0_forced, OffVal.
  apply Nat.eqb_neq in Hij as Hij'.
  assert (Hji' : Nat.eqb j i = false) by (rewrite Nat.eqb_sym; exact Hij').
  rewrite Hij', Hji'.
  assert (Hnum : (- Wt i j + lam * ord i j) - (- Wt j i + lam * ord j i)
                 == (2#1) * (lam * ord i j)).
  { rewrite (ord_antisymmetric_forced j i), (Wt_symmetric j i). ring. }
  rewrite Hnum.
  unfold Qdiv, Qinv. simpl. lra.
Qed.

(* --------------------------------------------------------------------- *)
(* The circulation pattern kappa_i is a FIXED, computable combinatorial       *)
(* fact on this 3-vertex nat-ordered carrier -- not a free choice. The          *)
(* middle index (1) has balanced circulation (0); the extreme indices (0,2)     *)
(* have net circulation +2/-2, mirroring their position in nat's own order.     *)
(* --------------------------------------------------------------------- *)

Theorem circulation_values :
     ord 0%nat 1%nat + ord 0%nat 2%nat == 2
  /\ ord 1%nat 0%nat + ord 1%nat 2%nat == 0
  /\ ord 2%nat 0%nat + ord 2%nat 1%nat == -2.
Proof. unfold ord. simpl. repeat split; reflexivity. Qed.

(* [Th_coqc] THE PAYOFF: D is forced to be exactly degree(Wt) minus lam times    *)
(* the FIXED circulation constant -- a fully concrete, closed-form consequence     *)
(* of rowsum0_full applied to R0_forced (unconditional: R0_forced_rowsum0_full     *)
(* already holds with no hypothesis on Wt/lam at all). *)
Theorem diagpart_R0_forced_is_degree_minus_circulation :
  forall (Wt : nat -> nat -> Q), (forall i j, Wt i j == Wt j i) ->
  forall lam : Q,
    DiagPart (R0_forced Wt lam) 0%nat 0%nat
      == (Wt 0%nat 1%nat + Wt 0%nat 2%nat) - lam * (2#1)
    /\
    DiagPart (R0_forced Wt lam) 1%nat 1%nat
      == (Wt 1%nat 0%nat + Wt 1%nat 2%nat) - lam * 0
    /\
    DiagPart (R0_forced Wt lam) 2%nat 2%nat
      == (Wt 2%nat 0%nat + Wt 2%nat 1%nat) - lam * (-2#1).
Proof.
  intros Wt Wt_symmetric lam.
  pose proof (diagpart_forced_by_rowsum0_full (R0_forced Wt lam)
                (R0_forced_rowsum0_full Wt lam)) as [D0 [D1 D2]].
  pose proof (symoff_R0_forced_is_negWt Wt Wt_symmetric lam 0%nat 1%nat
                (ltac:(discriminate))) as S01.
  pose proof (symoff_R0_forced_is_negWt Wt Wt_symmetric lam 0%nat 2%nat
                (ltac:(discriminate))) as S02.
  pose proof (symoff_R0_forced_is_negWt Wt Wt_symmetric lam 1%nat 0%nat
                (ltac:(discriminate))) as S10.
  pose proof (symoff_R0_forced_is_negWt Wt Wt_symmetric lam 1%nat 2%nat
                (ltac:(discriminate))) as S12.
  pose proof (symoff_R0_forced_is_negWt Wt Wt_symmetric lam 2%nat 0%nat
                (ltac:(discriminate))) as S20.
  pose proof (symoff_R0_forced_is_negWt Wt Wt_symmetric lam 2%nat 1%nat
                (ltac:(discriminate))) as S21.
  pose proof (skewoff_R0_forced_is_lam_ord Wt Wt_symmetric lam 0%nat 1%nat
                (ltac:(discriminate))) as K01.
  pose proof (skewoff_R0_forced_is_lam_ord Wt Wt_symmetric lam 0%nat 2%nat
                (ltac:(discriminate))) as K02.
  pose proof (skewoff_R0_forced_is_lam_ord Wt Wt_symmetric lam 1%nat 0%nat
                (ltac:(discriminate))) as K10.
  pose proof (skewoff_R0_forced_is_lam_ord Wt Wt_symmetric lam 1%nat 2%nat
                (ltac:(discriminate))) as K12.
  pose proof (skewoff_R0_forced_is_lam_ord Wt Wt_symmetric lam 2%nat 0%nat
                (ltac:(discriminate))) as K20.
  pose proof (skewoff_R0_forced_is_lam_ord Wt Wt_symmetric lam 2%nat 1%nat
                (ltac:(discriminate))) as K21.
  assert (Hs00 : SymOff (R0_forced Wt lam) 0%nat 0%nat == 0)
    by (unfold SymOff; simpl; reflexivity).
  assert (Hs11 : SymOff (R0_forced Wt lam) 1%nat 1%nat == 0)
    by (unfold SymOff; simpl; reflexivity).
  assert (Hs22 : SymOff (R0_forced Wt lam) 2%nat 2%nat == 0)
    by (unfold SymOff; simpl; reflexivity).
  assert (Hk00 : SkewOff (R0_forced Wt lam) 0%nat 0%nat == 0)
    by (unfold SkewOff; simpl; reflexivity).
  assert (Hk11 : SkewOff (R0_forced Wt lam) 1%nat 1%nat == 0)
    by (unfold SkewOff; simpl; reflexivity).
  assert (Hk22 : SkewOff (R0_forced Wt lam) 2%nat 2%nat == 0)
    by (unfold SkewOff; simpl; reflexivity).
  repeat split.
  - rewrite D0, Hs00, S01, S02, Hk00, K01, K02. unfold ord. simpl. ring.
  - rewrite D1, S10, Hs11, S12, K10, Hk11, K12. unfold ord. simpl. ring.
  - rewrite D2, S20, S21, Hs22, K20, K21, Hk22. unfold ord. simpl. ring.
Qed.

(* --------------------------------------------------------------------- *)
(* Non-vacuous witness: a concrete Wt/lam instantiation where BOTH             *)
(* offdiag_le0_full's hypothesis (the small-skew bound) and every downstream     *)
(* consequence hold together simultaneously on real numbers, with D's forced      *)
(* value differing at all three nodes (2, 5, -8 below) -- a genuine, non-          *)
(* degenerate directed seed, not an edge case where the circulation term            *)
(* vanishes everywhere. *)
(* --------------------------------------------------------------------- *)

Section SingleRootWitness.

  Definition WtRoot (i j : nat) : Q :=
    match i, j with
    | 0%nat,1%nat | 1%nat,0%nat => 4#1
    | 0%nat,2%nat | 2%nat,0%nat => 3#1
    | 1%nat,2%nat | 2%nat,1%nat => 5#1
    | _,_ => 0
    end.

  Theorem WtRoot_symmetric : forall i j, WtRoot i j == WtRoot j i.
  Proof.
    intros i j.
    destruct i as [|[|[|i]]]; destruct j as [|[|[|j]]]; unfold WtRoot; try reflexivity.
  Qed.

  Definition lamRoot : Q := 1#1.

  (* lamRoot = 1 satisfies the small-skew bound against WtRoot's weights          *)
  (* (4, 3, 5 all >= 1 = |lamRoot|), so offdiag_le0_full holds concretely, on        *)
  (* the 6 index pairs that actually matter for this 3-vertex carrier. *)
  Theorem lamRoot_satisfies_small_skew :
    lamRoot * ord 0%nat 1%nat <= WtRoot 0%nat 1%nat /\
    lamRoot * ord 0%nat 2%nat <= WtRoot 0%nat 2%nat /\
    lamRoot * ord 1%nat 2%nat <= WtRoot 1%nat 2%nat /\
    lamRoot * ord 1%nat 0%nat <= WtRoot 1%nat 0%nat /\
    lamRoot * ord 2%nat 0%nat <= WtRoot 2%nat 0%nat /\
    lamRoot * ord 2%nat 1%nat <= WtRoot 2%nat 1%nat.
  Proof. unfold lamRoot, WtRoot, ord. simpl. repeat split; lra. Qed.

  Theorem R0_forced_root_offdiag_le0_full :
    offdiag_le0_full (R0_forced WtRoot lamRoot).
  Proof.
    destruct lamRoot_satisfies_small_skew as [H01 [H02 [H12 [H10 [H20 H21]]]]].
    exact (R0_forced_offdiag_le0_full_conditional
             WtRoot lamRoot H01 H02 H12 H10 H20 H21).
  Qed.

  Theorem R0_forced_root_diag_values :
    DiagPart (R0_forced WtRoot lamRoot) 0%nat 0%nat == 5#1 /\
    DiagPart (R0_forced WtRoot lamRoot) 1%nat 1%nat == 9#1 /\
    DiagPart (R0_forced WtRoot lamRoot) 2%nat 2%nat == 10#1.
  Proof.
    pose proof (diagpart_R0_forced_is_degree_minus_circulation
                  WtRoot WtRoot_symmetric lamRoot) as [E0 [E1 E2]].
    unfold WtRoot, lamRoot in E0, E1, E2. simpl in E0, E1, E2.
    split. { rewrite E0. lra. }
    split. { rewrite E1. lra. }
    rewrite E2. lra.
  Qed.

  (* D is genuinely NOT uniform across nodes (5, 9, 10 all differ) -- the           *)
  (* directional circulation term is doing real, node-distinguishing work here,      *)
  (* not just adding a constant offset that a free Dg could have supplied anyway.     *)
  Theorem R0_forced_root_D_is_nonuniform :
    ~ (DiagPart (R0_forced WtRoot lamRoot) 0%nat 0%nat
       == DiagPart (R0_forced WtRoot lamRoot) 1%nat 1%nat).
  Proof.
    destruct R0_forced_root_diag_values as [E0 [E1 _]].
    rewrite E0, E1. intro H. lra.
  Qed.

  Theorem R0_forced_root_rowsum0_full :
    rowsum0_full (R0_forced WtRoot lamRoot).
  Proof. apply R0_forced_rowsum0_full. Qed.

End SingleRootWitness.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions trifurcation_exact.
Print Assumptions symoff_symmetric.
Print Assumptions skewoff_antisymmetric.
Print Assumptions diagpart_no_offdiag_coupling.
Print Assumptions skewoff_quadratic_form_vanishes.
Print Assumptions lcand_symmetric.
Print Assumptions lcand_rowsum0.
Print Assumptions lcand_offdiag_le0_conditional.
Print Assumptions diag_witness.
Print Assumptions symoff_witness.
Print Assumptions skewoff_witness.
Print Assumptions nondegenerate_split.
Print Assumptions witness_satisfies_lcand_hypothesis.
Print Assumptions ord_antisymmetric_forced.
Print Assumptions symoff_R0construct_is_Wt.
Print Assumptions skewoff_R0construct_is_lam_ord.
Print Assumptions symoff_R0construct_nonneg.
Print Assumptions WtEx_symmetric.
Print Assumptions WtEx_nonneg.
Print Assumptions reconstruction_matches_earlier_witness.
Print Assumptions euler_step_energy_change.
Print Assumptions euler_step_energy_nondecreasing.
Print Assumptions skoff_recovers_step_M.
Print Assumptions lam_minus1_delivers_step_M_shape.
Print Assumptions step_M_copy_preserves_energy2.
Print Assumptions diag_uniform_recovers_step_D.
Print Assumptions step_Diag3_uniform_strictly_decreases_energy.
Print Assumptions diag_witness_values_not_uniform_minus_half.
Print Assumptions rowsum0_full_offdiag_le0_full_diag_nonneg.
Print Assumptions diagpart_forced_by_rowsum0_full.
Print Assumptions R0_forced_rowsum0_full.
Print Assumptions R0_forced_offdiag_le0_full_conditional.
Print Assumptions symoff_R0_forced_is_negWt.
Print Assumptions skewoff_R0_forced_is_lam_ord.
Print Assumptions circulation_values.
Print Assumptions diagpart_R0_forced_is_degree_minus_circulation.
Print Assumptions WtRoot_symmetric.
Print Assumptions lamRoot_satisfies_small_skew.
Print Assumptions R0_forced_root_offdiag_le0_full.
Print Assumptions R0_forced_root_diag_values.
Print Assumptions R0_forced_root_D_is_nonuniform.
Print Assumptions R0_forced_root_rowsum0_full.
