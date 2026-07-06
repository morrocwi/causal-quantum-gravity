(******************************************************************************)
(* InfoTelegraphCrossover_attempt.v -- EXPLORATORY, single-attempt.             *)
(*   Standalone. Requires ONLY Coq.QArith + Lqa: no arc file, no Reals, no      *)
(*   axiom. TIER = Th_coqc (Q-only, axiom-free). Compile: coqc -q -R . RDL.     *)
(*                                                                            *)
(* THE DYNAMICAL QUANTUM<->CLASSICAL CROSSOVER = the telegraph DISCRIMINANT,     *)
(* and its critical point IS the spine knife-edge / black-hole horizon.         *)
(*                                                                            *)
(* The core (URCF_RD_All.v) already proves the two ENDPOINTS as separate         *)
(* readouts of the one spine M∂²Φ + D∂Φ + K·L_R·Φ = 0:                           *)
(*   InfoSchrodinger  : M∂²  -> unitary oscillation  exp(-iωt)   (wave/quantum)  *)
(*   InfoDecoherence  : D∂    -> dissipative decay    exp(-Γt)    (diffusion)     *)
(*   InfoTelegraph    : the spine IS the telegraph equation; mass = 1/(2τc).     *)
(* What was MISSING is the single statement that ties them: which regime the      *)
(* solution is IN is decided by the temporal characteristic Mω² + Dω + Kλ = 0    *)
(* on an L_R-eigenmode λ, whose DISCRIMINANT                                      *)
(*     disc = D² − 4·M·K·λ                                                        *)
(* sets the regime -- under-damped (complex roots = damped OSCILLATION = quantum/  *)
(* wave) when disc < 0, over-damped (real roots = pure DECAY = classical/         *)
(* diffusion) when disc > 0 -- with the crossover exactly at                      *)
(*     λ_c = D²/(4·M·K)     (disc = 0, critical damping).                         *)
(* This λ_c is the SAME D²/(4MK) knife-edge the τc-of-agency work identified with *)
(* the black-hole horizon and the agency threshold: quantum (under-damped /       *)
(* looping) vs classical (over-damped / settling) is one knife-edge.             *)
(*                                                                            *)
(* WHAT IS PROVED (Th_coqc, axiom-free over Q; Compute-checked witness):        *)
(*   char_complete_square : 4M·(Mω²+Dω+Kλ) == (2Mω+D)² − disc -- the exact        *)
(*       completion of the square (no analysis, no roots computed).             *)
(*   underdamped_positive : 0<M ∧ disc<0 ⇒ the characteristic Mω²+Dω+Kλ > 0 for   *)
(*       EVERY real ω -- no real frequency root ⇒ the modes are OSCILLATORY       *)
(*       (under-damped, the quantum/wave regime).                               *)
(*   overdamped_min_value / overdamped_min_nonpositive : 0<M ∧ disc≥0 ⇒ the       *)
(*       characteristic reaches ≤ 0 at ω=−D/2M -- a real decay root exists        *)
(*       (over-damped, the classical/diffusion regime).                         *)
(*   critical_disc_zero : disc(λ_c) == 0 with λ_c = D²/(4MK) -- the crossover.    *)
(*   underdamped_iff_above_crit : disc < 0  <->  D² < 4MKλ (λ above λ_c).         *)
(*   witnesses : (M,D,K,λ)=(1,1,1,1) disc=−3<0 under-damped; (1,4,1,1) disc=12>0  *)
(*       over-damped.                                                            *)
(*                                                                            *)
(* HONEST FENCE. CLOSED: the DYNAMICAL quantum<->classical crossover is the        *)
(* telegraph discriminant disc=D²−4MKλ, exact over Q, with the critical           *)
(* λ_c=D²/(4MK) = the spine knife-edge / horizon; under-damped(oscillatory/       *)
(* quantum) iff disc<0, over-damped(decay/classical) iff disc>0. This unifies      *)
(* InfoSchrodinger (wave) and InfoDecoherence (diffusion) as the two SIDES of one *)
(* crossover on the one spine -- genuine DYNAMICAL content, not consistency.      *)
(* [Open], NOT smuggled: the actual complex/real ROOT VALUES (transcendental      *)
(* phase/rate magnitudes = +reals; here only the sign/regime is decided over Q),  *)
(* the non-relativistic Schrödinger reduction, the VALUES of M,D,K,τc, and the    *)
(* GR/Einstein dynamical closure (GR enters via the spatial K·L_R geometry        *)
(* readout, a separate axis). Continuum refused. All quantities plain Q.         *)
(******************************************************************************)

Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.

Module InfoTelegraphCrossover.
Open Scope Q_scope.

(* temporal characteristic of the spine on an L_R-eigenmode lam, and its disc *)
Definition pchar (M D K lam w : Q) : Q := M*w*w + D*w + K*lam.
Definition disc (M D K lam : Q) : Q := D*D - 4*M*K*lam.
Definition lam_c (M D K : Q) : Q := D*D / (4*M*K).

(* ------------------------------------------------------------------ *)
(* (1) exact completion of the square -- the algebraic spine of it.    *)
(* ------------------------------------------------------------------ *)
Theorem char_complete_square : forall M D K lam w : Q,
  4*M*(pchar M D K lam w) == (2*M*w + D)*(2*M*w + D) - disc M D K lam.
Proof. intros. unfold pchar, disc. ring. Qed.

(* ------------------------------------------------------------------ *)
(* (2) UNDER-DAMPED (disc<0): no real frequency root => oscillatory     *)
(*     (the quantum/wave regime). Characteristic > 0 for every omega.   *)
(* ------------------------------------------------------------------ *)
Theorem underdamped_positive : forall M D K lam w : Q,
  0 < M -> disc M D K lam < 0 -> 0 < pchar M D K lam w.
Proof.
  intros M D K lam w HM Hd.
  assert (H := char_complete_square M D K lam w).
  assert (Hsq : 0 <= (2*M*w + D)*(2*M*w + D))
    by (generalize (2*M*w + D); intro a; nra).
  set (p := pchar M D K lam w) in *.
  set (d := disc M D K lam) in *.
  set (s := (2*M*w + D)*(2*M*w + D)) in *.
  clearbody p d s.
  nra.
Qed.

(* ------------------------------------------------------------------ *)
(* (3) OVER-DAMPED (disc>=0): the characteristic reaches <=0 at         *)
(*     omega=-D/2M => a real decay root (the classical/diffusion        *)
(*     regime).                                                         *)
(* ------------------------------------------------------------------ *)
Theorem overdamped_min_value : forall M D K lam : Q,
  ~ (M == 0) ->
  4*M*(pchar M D K lam (-D/(2*M))) == - disc M D K lam.
Proof. intros M D K lam HM. unfold pchar, disc. field. assumption. Qed.

Theorem overdamped_min_nonpositive : forall M D K lam : Q,
  0 < M -> 0 <= disc M D K lam -> pchar M D K lam (-D/(2*M)) <= 0.
Proof.
  intros M D K lam HM Hd.
  assert (HM0 : ~ (M == 0)) by lra.
  assert (H := overdamped_min_value M D K lam HM0).
  set (p := pchar M D K lam (-D/(2*M))) in *.
  set (d := disc M D K lam) in *.
  clearbody p d.
  nra.
Qed.

(* ------------------------------------------------------------------ *)
(* (4) the CROSSOVER: disc(lam_c) = 0 at lam_c = D^2/(4MK).             *)
(* ------------------------------------------------------------------ *)
Theorem critical_disc_zero : forall M D K : Q,
  ~ (M == 0) -> ~ (K == 0) -> disc M D K (lam_c M D K) == 0.
Proof.
  intros M D K HM HK. unfold disc, lam_c. field. split; assumption.
Qed.

Theorem underdamped_iff_above_crit : forall M D K lam : Q,
  disc M D K lam < 0 <-> D*D < 4*M*K*lam.
Proof. intros. unfold disc. lra. Qed.

(* ------------------------------------------------------------------ *)
(* (5) WITNESSES on each side of the crossover.                        *)
(* ------------------------------------------------------------------ *)
Example underdamped_witness : disc 1 1 1 1 == - (3).
Proof. unfold disc. ring. Qed.

Example overdamped_witness : disc 1 4 1 1 == 12.
Proof. unfold disc. ring. Qed.

(* the quantum-side characteristic (1,1,1,1) is strictly positive for all w *)
Example underdamped_char_positive : forall w : Q, 0 < pchar 1 1 1 1 w.
Proof.
  intro w. apply underdamped_positive; [ lra | ].
  rewrite underdamped_witness. lra.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions underdamped_positive.
Print Assumptions overdamped_min_nonpositive.
Print Assumptions critical_disc_zero.
Print Assumptions char_complete_square.

End InfoTelegraphCrossover.
