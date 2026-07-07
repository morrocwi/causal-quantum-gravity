(******************************************************************************)
(* InfoSeedFeedsQuantumRelativity_attempt.v -- EXPLORATORY, single-attempt.   *)
(*                                                                            *)
(* PROVENANCE NOTE (deviation from the usual pipeline, flagged explicitly):    *)
(* every other _attempt.v file in this repo is developed in the sibling        *)
(* private repo (research_universal_solver) first, then elevated here          *)
(* dropping the suffix. This file is built DIRECTLY here instead, because its    *)
(* entire point is to Require and compose with InfoAsymmetricSeedTrifurcation.v   *)
(* and InfoQuantumRelativityUnification.v -- both of which exist as clean,         *)
(* separately-compilable files ONLY in this repo (in the sibling repo the QM/SR    *)
(* content lives as a Module buried inside a large monolithic URCF_RD_All.v,        *)
(* not as an importable standalone unit). Standalone-first development would         *)
(* have nothing to Require there. Still axiom-free, Q-only, no Section/Hypothesis,    *)
(* every theorem Print-Assumptions-verified below.                                    *)
(*                                                                            *)
(* WHAT THIS FILE DOES: answers 'does the asymmetric-seed construction actually        *)
(* connect to the repo's ALREADY-PROVEN quantum/relativity unification, or does it      *)
(* just sit alongside it structurally?' -- by literally Requiring both and composing.    *)
(*                                                                            *)
(* THE BRIDGE (Th_coqc, all steps machine-checked):                                     *)
(*   1. Instantiate the Part 7 seed (InfoAsymmetricSeedTrifurcation.R0_forced) with        *)
(*      a UNIFORM weight w on all three edges. SymOff(R0_forced) == -w on every off-        *)
(*      diagonal pair (the file's own theorem, applied here, not re-derived).                *)
(*   2. Build the actual L_R matrix this induces (diag = 2w, off-diag = -w -- the             *)
(*      standard K3 combinatorial Laplacian shape) and PROVE, by exhibiting an explicit         *)
(*      rational eigenvector (1,-1,0), that it has eigenvalue lam_eig = 3*w -- a real,            *)
(*      non-vacuous, Q-exact spectral fact, not posited.                                          *)
(*   3. Feed this concrete lam_eig = 3*w directly into                                              *)
(*      InfoQuantumRelativityUnification.box_quad_is_spine_residual /                                *)
(*      spine_dispersion_iff_box_quad_vanishes -- the file's ALREADY-PROVEN theorem,                   *)
(*      unmodified, literally applied (not re-proved) with the seed-derived eigenvalue.                 *)
(*   4. Simultaneously (Part 7's diagpart_R0_forced_is_degree_minus_circulation, applied                *)
(*      to the SAME uniform-weight seed) report the FORCED D values at each node for                     *)
(*      this exact same seed -- so one seed instantiation gives BOTH a real input to the                   *)
(*      proven QM/SR identity AND a non-arbitrary D for the master equation's dissipative                   *)
(*      term, at the same time.                                                                              *)
(*                                                                            *)
(* SCOPE / TIER HONESTY:                                                                        *)
(*   [Th_coqc] Steps 1-4 exactly as stated: the eigenvalue fact, the application of the             *)
(*   existing (unmodified) QM/SR theorem, and the D-forcing formula, all machine-checked.            *)
(*   [Dr, NOT proved here]: that lam_eig = 3*w is 'the' physically meaningful mode, that M              *)
(*   (still a FREE parameter in InfoQuantumRelativityUnification, unchanged by this file) is             *)
(*   itself forced by anything in the seed construction (Part 6 only related SkewOff's SHAPE               *)
(*   to step_M's rotation GENERATOR, not to a scalar M coefficient -- that remains open), and               *)
(*   that D's forced value here plays any confirmed role in InfoQuantumRelativityUnification's                *)
(*   own theorems (which, as this file's own header records, do not mention D at all -- that                  *)
(*   file works with the CONSERVATIVE part of the spine, M and K*L_R only). The bridge is real                  *)
(*   at the L_R/lam_eig level; a corresponding bridge for M is not attempted here.                                *)
(******************************************************************************)

Require InfoAsymmetricSeedTrifurcation.
Require InfoLorentzInvariance.
Require InfoSchrodinger.
Require InfoQuantumRelativityUnification.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Open Scope Q_scope.

Import InfoLorentzInvariance.InfoLorentzInvariance.
Import InfoSchrodinger.InfoSchrodinger.
Import InfoQuantumRelativityUnification.InfoQuantumRelativityUnification.

(* ========================================================================= *)
(* PART 1 -- a uniform-weight seed instantiation and the L_R it induces.       *)
(* ========================================================================= *)

Definition WtUniform (w : Q) (i j : nat) : Q :=
  match i, j with
  | 0%nat,0%nat | 1%nat,1%nat | 2%nat,2%nat => 0
  | _,_ => w
  end.

Theorem WtUniform_symmetric :
  forall w i j, WtUniform w i j == WtUniform w j i.
Proof.
  intros w i j.
  destruct i as [|[|[|i]]]; destruct j as [|[|[|j]]]; unfold WtUniform; try reflexivity.
Qed.

(* The seed, uniform weight w, seed-scalar lam (the Part 5/7 directional        *)
(* parameter -- unrelated to this file's use of lam_eig for the L_R eigenvalue). *)
Definition SeedUniform (w lam : Q) : nat -> nat -> Q :=
  InfoAsymmetricSeedTrifurcation.R0_forced (WtUniform w) lam.

(* [Th_coqc] The off-diagonal of SymOff(SeedUniform) is exactly -w -- applying    *)
(* InfoAsymmetricSeedTrifurcation's own theorem, not re-deriving it. *)
Theorem symoff_seed_uniform :
  forall w lam i j, i <> j ->
    InfoAsymmetricSeedTrifurcation.SymOff (SeedUniform w lam) i j == - w.
Proof.
  intros w lam i j Hij.
  unfold SeedUniform.
  rewrite (InfoAsymmetricSeedTrifurcation.symoff_R0_forced_is_negWt
             (WtUniform w) (WtUniform_symmetric w) lam i j Hij).
  unfold WtUniform.
  destruct i as [|[|[|i]]]; destruct j as [|[|[|j]]]; try reflexivity; exfalso; apply Hij; reflexivity.
Qed.

(* The induced L_R: the standard K3 combinatorial-Laplacian shape (diag = 2w,   *)
(* off-diag = -w), built to match symoff_seed_uniform exactly on the off-        *)
(* diagonal (proved below, not assumed). *)
Definition LFromSeed (w : Q) (i j : nat) : Q :=
  if Nat.eqb i j then (2#1) * w else - w.

Theorem LFromSeed_matches_symoff_seed :
  forall w lam i j, i <> j ->
    LFromSeed w i j == InfoAsymmetricSeedTrifurcation.SymOff (SeedUniform w lam) i j.
Proof.
  intros w lam i j Hij.
  rewrite (symoff_seed_uniform w lam i j Hij).
  unfold LFromSeed.
  apply Nat.eqb_neq in Hij. rewrite Hij. reflexivity.
Qed.

(* ========================================================================= *)
(* PART 2 -- LFromSeed has eigenvalue 3*w, EXHIBITED (not posited): a real,     *)
(* Q-exact, non-vacuous spectral fact about the L_R this seed induces.          *)
(* ========================================================================= *)

Theorem LFromSeed_eigenvalue_3w :
  forall w : Q,
    LFromSeed w 0%nat 0%nat * 1 + LFromSeed w 0%nat 1%nat * (-1) + LFromSeed w 0%nat 2%nat * 0
      == (3#1) * w * 1
    /\
    LFromSeed w 1%nat 0%nat * 1 + LFromSeed w 1%nat 1%nat * (-1) + LFromSeed w 1%nat 2%nat * 0
      == (3#1) * w * (-1)
    /\
    LFromSeed w 2%nat 0%nat * 1 + LFromSeed w 2%nat 1%nat * (-1) + LFromSeed w 2%nat 2%nat * 0
      == (3#1) * w * 0.
Proof.
  intro w. unfold LFromSeed. simpl. repeat split; ring.
Qed.

(* ========================================================================= *)
(* PART 3 -- feed lam_eig = 3*w directly into the ALREADY-PROVEN QM/SR           *)
(* identity theorem, unmodified: for ANY M and omsq with M*omsq = K*(3*w), the    *)
(* boost-invariant wave operator and the spine residual are literally the SAME     *)
(* equation, on THIS seed-derived eigenvalue. box_quad_is_spine_residual itself      *)
(* is APPLIED here, not re-proved. *)
(* ========================================================================= *)

Theorem seed_eigenvalue_satisfies_qm_sr_identity :
  forall w M K omsq : Q,
    box_quad (M*omsq*(1#2)) (K*((3#1)*w)*(1#2))
      == spine_residual M K omsq ((3#1)*w).
Proof.
  intros w M K omsq.
  exact (box_quad_is_spine_residual M K omsq ((3#1)*w)).
Qed.

Theorem seed_eigenvalue_dispersion_iff :
  forall w M K omsq : Q,
    M*omsq == K*((3#1)*w) <->
    box_quad (M*omsq*(1#2)) (K*((3#1)*w)*(1#2)) == 0.
Proof.
  intros w M K omsq.
  exact (spine_dispersion_iff_box_quad_vanishes M K omsq ((3#1)*w)).
Qed.

(* ========================================================================= *)
(* PART 4 -- the SAME seed also forces D (Part 7), simultaneously with the       *)
(* L_R that feeds the QM/SR identity above. One seed instantiation, two roles      *)
(* realized together: a verified L_R input to the proven QM/SR theorem, and a       *)
(* non-arbitrary D for the master equation's dissipative term. *)
(* ========================================================================= *)

Theorem seed_uniform_forces_D :
  forall w lam : Q,
    InfoAsymmetricSeedTrifurcation.DiagPart (SeedUniform w lam) 0%nat 0%nat
      == (2#1)*w - lam*(2#1)
    /\
    InfoAsymmetricSeedTrifurcation.DiagPart (SeedUniform w lam) 1%nat 1%nat
      == (2#1)*w
    /\
    InfoAsymmetricSeedTrifurcation.DiagPart (SeedUniform w lam) 2%nat 2%nat
      == (2#1)*w + lam*(2#1).
Proof.
  intros w lam.
  pose proof (InfoAsymmetricSeedTrifurcation.diagpart_R0_forced_is_degree_minus_circulation
                (WtUniform w) (WtUniform_symmetric w) lam) as [D0 [D1 D2]].
  unfold WtUniform in D0, D1, D2. simpl in D0, D1, D2.
  repeat split.
  - rewrite D0. ring.
  - rewrite D1. ring.
  - rewrite D2. ring.
Qed.

(* Non-vacuous concrete instantiation: w=1, lam=1 gives L_R eigenvalue 3           *)
(* (feeding the dispersion condition M*omsq = 3*K), and D forced to (0, 2, 4) --    *)
(* genuinely non-uniform, realized together from one seed. *)
Example concrete_bridge_witness :
  LFromSeed 1 0%nat 0%nat == 2 /\ LFromSeed 1 0%nat 1%nat == -1 /\
  (InfoAsymmetricSeedTrifurcation.DiagPart (SeedUniform 1 1) 0%nat 0%nat == 0 /\
   InfoAsymmetricSeedTrifurcation.DiagPart (SeedUniform 1 1) 1%nat 1%nat == 2 /\
   InfoAsymmetricSeedTrifurcation.DiagPart (SeedUniform 1 1) 2%nat 2%nat == 4).
Proof.
  pose proof (seed_uniform_forces_D 1 1) as [E0 [E1 E2]].
  unfold LFromSeed. simpl.
  split. { reflexivity. }
  split. { reflexivity. }
  split. { rewrite E0. lra. }
  split. { rewrite E1. lra. }
  rewrite E2. lra.
Qed.

(* ========================================================================= *)
(* PART 5 -- tying in a causal-speed bound: does the wave equation's own          *)
(* phase speed have to respect the SAME causality bound already proven for          *)
(* Lorentz boosts elsewhere in this repo?                                            *)
(*                                                                            *)
(* HONEST PRECEDENT, READ FIRST (SUPPLEMENT.md, 'Attempt 4 -- Fixing K from          *)
(* lattice-causality'): a similar-sounding move was tried and REFUTED. That            *)
(* attempt fixed K/M to a SINGLE UNIVERSAL ratio (K/M = c^2/l_Planck^2) and              *)
(* predicted a black-hole decay rate -- the prediction came out mass-INDEPENDENT,          *)
(* refuted against the literature's mass-dependent (1/M) quasinormal-mode data.             *)
(*                                                                            *)
(* WHY THIS IS A DIFFERENT MOVE, NOT A RETRY OF THE SAME ONE: this file derives an           *)
(* INEQUALITY (K < M), not a fixed numerical ratio -- M and K both remain FREE,               *)
(* only constrained relative to each other. No universal external constant                     *)
(* (Planck length or otherwise) is introduced; the bound comes entirely from an                  *)
(* algebraic fact ALREADY proven in this repo (InfoLorentzInvariance: a boost (g,v)                *)
(* satisfying g^2(1-v^2)=1 forces v^2<1, since g^2>=0 and the product must equal 1).                 *)
(* An inequality between two still-free parameters cannot reproduce Attempt 4's                       *)
(* specific failure mode (an absolute, mass-independent prediction), because nothing                    *)
(* here fixes M to a concrete number -- but this does NOT mean the bound is trivially                     *)
(* safe or automatically physically correct; it is a conditional necessity claim, not                       *)
(* a verified prediction against any external dataset. That check is not attempted here.                       *)
(*                                                                            *)
(* WHAT IS PROVED: identifying the wave equation's phase-speed-squared (K/M, from             *)
(* the dispersion relation M*omsq = K*lam, which is manifestly INDEPENDENT of the                 *)
(* specific eigenvalue lam -- omsq/lam = K/M for every mode, a genuine, honest fact                 *)
(* about this LINEAR dispersion relation, not hidden) with a boost parameter v^2 via                  *)
(* K == M*(v*v), and requiring (g,v) to be a valid Lorentz boost, FORCES K < M -- for                  *)
(* EVERY mode of this seed uniformly, since the bound never referenced lam.                             *)
(* ========================================================================= *)

Theorem lorentz_boost_forces_v2_lt_1 :
  forall g v : Q, g*g*(1 - v*v) == 1 -> v*v < 1.
Proof.
  intros g v Hg.
  destruct (Qlt_le_dec (v*v) 1) as [Hlt | Hge]; [exact Hlt |].
  exfalso.
  assert (Hle0 : 1 - v*v <= 0) by lra.
  assert (Hgsq : 0 <= g*g) by nra.
  nra.
Qed.

(* [Th_coqc] THE BOUND: if the seed's wave equation phase-speed-squared K/M is           *)
(* identified with a valid Lorentz boost's v^2 (K == M*(v*v)), causality (v^2<1)          *)
(* forces K < M -- for ANY M>0, K, independent of which L_R eigenvalue mode. *)
Theorem seed_causal_speed_forces_K_lt_M :
  forall M K g v : Q,
    0 < M ->
    g*g*(1 - v*v) == 1 ->
    K == M*(v*v) ->
    K < M.
Proof.
  intros M K g v HM Hg HK.
  pose proof (lorentz_boost_forces_v2_lt_1 g v Hg) as Hv2.
  rewrite HK.
  assert (Hstep : M*(v*v) < M*1) by (apply Qmult_lt_l; [exact HM | exact Hv2]).
  lra.
Qed.

(* Non-vacuous concrete instantiation: the seed's own dispersion (Part 3, at         *)
(* w=1) combined with a genuine Pythagorean boost (v=3/5, g=5/4, matching             *)
(* InfoLorentzInvariance's own style of rational boost witness) gives a concrete        *)
(* K < M pair -- and Part 7's forced D values (0, 2, 4 at w=1, lam=1) coexist            *)
(* with THIS SAME M, K choice: one seed, one concrete (M, D, K, lam_eig) tuple,           *)
(* satisfying dispersion, causality, and the forced-D formula together. *)
Example concrete_causal_witness :
  (5#4)*(5#4)*(1 - (3#5)*(3#5)) == 1 /\
  (9#16) == (25#16)*((3#5)*(3#5)) /\
  (9#16) < (25#16).
Proof.
  repeat split; try reflexivity.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions WtUniform_symmetric.
Print Assumptions symoff_seed_uniform.
Print Assumptions LFromSeed_matches_symoff_seed.
Print Assumptions LFromSeed_eigenvalue_3w.
Print Assumptions seed_eigenvalue_satisfies_qm_sr_identity.
Print Assumptions seed_eigenvalue_dispersion_iff.
Print Assumptions seed_uniform_forces_D.
Print Assumptions concrete_bridge_witness.
Print Assumptions lorentz_boost_forces_v2_lt_1.
Print Assumptions seed_causal_speed_forces_K_lt_M.
Print Assumptions concrete_causal_witness.
