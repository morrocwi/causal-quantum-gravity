(*
   InfoSeedLambdaCCrossover.v -- PROMOTED EXTRACT
   Provenance: elevated 2026-07-08/10 from research_universal_solver/formal/InfoSeedLambdaCCrossover_attempt.v
   (renamed, "_attempt" dropped; Require targets adjusted to this repo's file names).
   Verified standalone at elevation (coqc -q -R . DQG; all Print Assumptions "Closed under
   the global context") and wired into COQFILES/make verify + CI on 2026-07-10, closing a
   review finding that elevation alone had left these outside the CI-guarded build.
   The original header below is kept verbatim from the audited source (including its
   "EXPLORATORY, single-attempt" self-description, which refers to its role in the source
   repo's exploratory arc, not to its verification status here).
*)
(******************************************************************************)
(* InfoSeedLambdaCCrossover.v -- EXPLORATORY, single-attempt.           *)
(*   Requires InfoTelegraphCrossover_attempt, InfoAsymmetricSeedTrifurcation_     *)
(*   attempt (both this repo, untouched). No axiom, no Reals, no continuum.        *)
(*   TIER = Th_coqc (Q-only).                                                *)
(*                                                                            *)
(* THE FRONTIER DOC'S ITEM 4: plug Part 7's forced D and the seed's own verified      *)
(* eigenvalue (item 3) into `InfoTelegraphCrossover_attempt.v`'s already-existing         *)
(* under/over-damped classification, checking HONESTLY whether this produces a genuinely     *)
(* NEW regime classification for THIS seed's concrete numbers, or merely another               *)
(* application of an already-general theorem (the SAME discipline as items 1-3).                 *)
(*                                                                            *)
(* THE HONEST FINDING, stated up front: M and K remain genuinely free in this thread          *)
(* (neither is forced by anything built so far) -- so the seed does NOT, by itself, force          *)
(* a REGIME (under- vs over-damped). What the seed DOES force, given its own concrete D and          *)
(* verified eigenvalue, is WHERE the crossover threshold sits in the free (M,K)-plane: the             *)
(* critical PRODUCT `M*K = D^2/(4*lam)` becomes a single, seed-determined NUMBER (not free),             *)
(* even though M and K individually remain unpinned. This is a genuine, if modest, narrowing --            *)
(* not a fake 'the seed determines the regime' overclaim.                                                    *)
(*                                                                            *)
(* WHAT IS PROVED (Th_coqc):                                                                                  *)
(*   seed_regime_by_MK_product   REWRITES `underdamped_iff_above_crit` (existing, not re-derived)                *)
(*                              at D=5 (Part 7's forced D at node 0, WtRoot/lamRoot) and                             *)
(*                              lam=3 (item 3's verified seed eigenvalue): disc<0 (under-damped)                       *)
(*                              iff 25 < 12*M*K -- an explicit, concrete threshold on the free                          *)
(*                              (M,K) PRODUCT, forced by the seed's own numbers.                                          *)
(*   seed_crossover_witnesses    TWO concrete (M,K) pairs straddling the threshold, both also                             *)
(*                              respecting the causal bound K<M (`causal_speed_forces_K_lt_M`,                              *)
(*                              causal-quantum-gravity, cited not re-proved here) as a sanity                                 *)
(*                              check that the two constraints this thread has built are mutually                              *)
(*                              satisfiable, not in tension: (M,K)=(3,1) is UNDER-damped                                         *)
(*                              (disc=-11<0, quantum/oscillatory reading); (M,K)=(2,1) is                                         *)
(*                              OVER-damped (disc=1>0, classical/decay reading) -- same D, same                                    *)
(*                              lam, different free (M,K), genuinely different regime, exactly as                                    *)
(*                              expected since M,K are NOT forced.                                                                     *)
(*                                                                            *)
(* SCOPE / TIER HONESTY -- read before citing as more than it is:                                                                        *)
(*   [Th_coqc] Every theorem above, exactly as stated -- `underdamped_iff_above_crit`,                                                       *)
(*   `char_complete_square`, and the D/lam concrete values are all APPLIED, not re-derived.                                                     *)
(*   [Dr, stated openly]: this file does NOT show the seed forces a regime -- it explicitly does                                                 *)
(*   NOT (M,K free); it shows the seed forces WHERE the (M,K)-plane's crossover boundary sits.                                                    *)
(*   Whether M,K SHOULD be further constrained (e.g. by the K<M causal bound alone, which is NOT                                                    *)
(*   enough by itself to pick a regime -- both witnesses below satisfy K<M) is explicitly [Open],                                                    *)
(*   not smuggled as resolved here.                                                                                                                      *)
(******************************************************************************)

Require InfoTelegraphCrossover_attempt.
Require InfoAsymmetricSeedTrifurcation.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Open Scope Q_scope.

Import InfoTelegraphCrossover_attempt.InfoTelegraphCrossover.

(* ========================================================================= *)
(* PART A -- the seed's own D and lam, feeding the existing crossover machinery. *)
(* ========================================================================= *)

(* Part 7's forced D at node 0 (WtRoot/lamRoot witness): D=5. Item 3's verified   *)
(* seed eigenvalue on the unweighted K3 carrier: lam=3.                          *)
Definition SeedD : Q := 5#1.
Definition SeedLam : Q := 3#1.

Theorem SeedD_matches_forced_D0 :
  InfoAsymmetricSeedTrifurcation.DiagPart
    (InfoAsymmetricSeedTrifurcation.R0_forced
       InfoAsymmetricSeedTrifurcation.WtRoot
       InfoAsymmetricSeedTrifurcation.lamRoot) 0%nat 0%nat
  == SeedD.
Proof.
  destruct InfoAsymmetricSeedTrifurcation.R0_forced_root_diag_values
    as [E0 [_ _]].
  exact E0.
Qed.

(* [Th_coqc] rewriting the existing iff at THIS seed's own D, lam: a concrete,   *)
(* explicit threshold on the free (M,K) PRODUCT, forced by the seed. *)
Theorem seed_regime_by_MK_product :
  forall M K : Q,
    disc M SeedD K SeedLam < 0 <-> (25#1) < (12#1) * (M * K).
Proof.
  intros M K.
  rewrite (underdamped_iff_above_crit M SeedD K SeedLam).
  unfold SeedD, SeedLam. split; intro H; lra.
Qed.

(* ========================================================================= *)
(* PART B -- two concrete (M,K) witnesses straddling the threshold, both        *)
(* respecting the causal bound K<M -- the two constraints coexist, they do not  *)
(* by themselves pick a single regime.                                          *)
(* ========================================================================= *)

Example seed_crossover_witnesses :
  disc (3#1) SeedD (1#1) SeedLam == -11#1
  /\ (1#1) < (3#1)
  /\ disc (2#1) SeedD (1#1) SeedLam == 1#1
  /\ (1#1) < (2#1).
Proof.
  unfold disc, SeedD, SeedLam.
  repeat split; try ring; lra.
Qed.

(* the (3,1) pair is genuinely UNDER-damped: no real frequency root, every mode  *)
(* oscillatory (quantum/wave reading) -- applying underdamped_positive, not       *)
(* re-deriving it. *)
Example seed_underdamped_instance :
  forall w : Q, 0 < pchar (3#1) SeedD (1#1) SeedLam w.
Proof.
  intro w.
  apply underdamped_positive; [ lra | ].
  destruct seed_crossover_witnesses as [E _]. rewrite E. lra.
Qed.

(* the (2,1) pair is genuinely OVER-damped: a real decay root exists at the       *)
(* characteristic's minimum -- applying overdamped_min_nonpositive, not            *)
(* re-deriving it. *)
Example seed_overdamped_instance :
  pchar (2#1) SeedD (1#1) SeedLam (- SeedD / (2 * (2#1))) <= 0.
Proof.
  apply overdamped_min_nonpositive; [ lra | ].
  destruct seed_crossover_witnesses as [_ [_ [E _]]]. rewrite E. lra.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions SeedD_matches_forced_D0.
Print Assumptions seed_regime_by_MK_product.
Print Assumptions seed_crossover_witnesses.
Print Assumptions seed_underdamped_instance.
Print Assumptions seed_overdamped_instance.
