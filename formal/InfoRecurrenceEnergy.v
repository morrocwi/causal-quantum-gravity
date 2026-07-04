(* ===================================================================== *)
(*  RDL_RecurrenceEnergy.v                                                 *)
(*  EXACT ENERGY STRUCTURE of the second-difference two-step recurrence    *)
(*      u_{k+1} = (2 - a) * u_k - u_{k-1}          (conservative)          *)
(*      (M+c) u' = (2M - s) u - (M-c) v            (dissipative, c >= 0)   *)
(*  entirely over Q (no reals, no square roots, no limits).                *)
(*                                                                         *)
(*  CLAIMED HERE (candidate for coqc 8.18.0, axiom-free target):           *)
(*    Qf_step_invariant   the quadratic form                               *)
(*                          Qf a u v = u^2 - (2-a) u v + v^2               *)
(*                        is EXACTLY conserved by every conservative step  *)
(*    Qf_decomp           4*Qf = (2u - (2-a)v)^2 + a(4-a) v^2   (ring)     *)
(*    Qf_window_nonneg    0 <= a <= 4  ==>  0 <= Qf                        *)
(*    Qf_lower            0 <= a <= 4  ==>  a(4-a) v^2 <= 4*Qf             *)
(*    orbit_invariant     Qf is constant along the whole orbit             *)
(*    orbit_bounded       0 <= a <= 4  ==>  a(4-a) * u_k^2 <= 4*Qf(u1,u0)  *)
(*                        for EVERY k  (division-free boundedness; with    *)
(*                        0 < a < 4 this pins every orbit in a fixed       *)
(*                        interval determined by the initial data)         *)
(*    damped_energy_identity                                               *)
(*                        G(u',u) - G(u,v) == - c * (u' - v)^2   EXACTLY,  *)
(*                        where G M s p q = M (p-q)^2 + s p q  and the     *)
(*                        step is the dissipative recurrence above         *)
(*    damped_energy_monotone   c >= 0 ==> G never increases                *)
(*    damped_energy_conserved  c == 0 ==> G exactly conserved              *)
(*    G_scales_to_Qf      s == M*a  ==>  G M s u v == M * Qf a u v         *)
(*                        (the dissipative and conservative energies are   *)
(*                         the SAME object; links to the window/ceiling    *)
(*                         results of RDL_SpectralCeiling.v via the        *)
(*                         step-ratio relation  M*a == h*h*K*lam)          *)
(*                                                                         *)
(*  All ring identities and both inequality families pre-verified with    *)
(*  exact rational arithmetic (200 random trials each; conservative       *)
(*  invariant checked exactly over 500-step orbits) before authoring.     *)
(*  Expected: Print Assumptions => Closed under the global context.       *)
(* ===================================================================== *)

Require Coq.QArith.QArith.
Require Coq.micromega.Lqa.

Module RecurrenceEnergy.

Import Coq.QArith.QArith.
Import Coq.micromega.Lqa.
Local Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(* The conserved quadratic form of the conservative step               *)
(* ------------------------------------------------------------------ *)

Definition Qf (a u v : Q) : Q := u * u - (2 - a) * u * v + v * v.

Lemma sq_nonneg : forall q : Q, 0 <= q * q.
Proof.
  intro q. destruct (Qlt_le_dec q 0) as [Hneg | Hpos].
  - setoid_replace (q * q) with ((- q) * (- q)) by ring.
    apply Qmult_le_0_compat; lra.
  - apply Qmult_le_0_compat; lra.
Qed.

Lemma Qf_sym : forall a u v, Qf a u v == Qf a v u.
Proof. intros. unfold Qf. ring. Qed.

(* one conservative step preserves Qf exactly *)
Lemma Qf_step_invariant : forall a u v,
  Qf a ((2 - a) * u - v) u == Qf a u v.
Proof. intros. unfold Qf. ring. Qed.

(* the sum-of-squares decomposition (pure ring identity) *)
Lemma Qf_decomp : forall a u v,
  4 * Qf a u v
    == (2 * u - (2 - a) * v) * (2 * u - (2 - a) * v)
       + (a * (4 - a)) * (v * v).
Proof. intros. unfold Qf. ring. Qed.

Lemma Qf_window_nonneg : forall a u v,
  0 <= a -> a <= 4 -> 0 <= Qf a u v.
Proof.
  intros a u v Ha0 Ha4.
  assert (Hd := Qf_decomp a u v).
  assert (H1 := sq_nonneg (2 * u - (2 - a) * v)).
  assert (H2 : 0 <= (a * (4 - a)) * (v * v)).
  { apply Qmult_le_0_compat; [apply Qmult_le_0_compat; lra | apply sq_nonneg]. }
  lra.
Qed.

Lemma Qf_lower : forall a u v,
  0 <= a -> a <= 4 ->
  (a * (4 - a)) * (v * v) <= 4 * Qf a u v.
Proof.
  intros a u v Ha0 Ha4.
  assert (Hd := Qf_decomp a u v).
  assert (H1 := sq_nonneg (2 * u - (2 - a) * v)).
  lra.
Qed.

(* ------------------------------------------------------------------ *)
(* Whole-orbit statements.                                             *)
(* orbit a (u1,u0) k = (u_{k+1}, u_k)  for the conservative step.      *)
(* ------------------------------------------------------------------ *)

Fixpoint orbit (a : Q) (p : Q * Q) (k : nat) : Q * Q :=
  match k with
  | O => p
  | S m => let q := orbit a p m in ((2 - a) * fst q - snd q, fst q)
  end.

Lemma orbit_invariant : forall a p k,
  Qf a (fst (orbit a p k)) (snd (orbit a p k)) == Qf a (fst p) (snd p).
Proof.
  intros a p k. induction k as [| m IH].
  - simpl. reflexivity.
  - simpl. destruct (orbit a p m) as [u v]. simpl in *.
    rewrite (Qf_step_invariant a u v). exact IH.
Qed.

(* division-free boundedness of every orbit point inside the window:   *)
(* with 0 < a < 4 the factor a(4-a) is strictly positive, so this      *)
(* confines |u_k| for all k by the initial quadratic form alone.       *)
Theorem orbit_bounded : forall a p k,
  0 <= a -> a <= 4 ->
  (a * (4 - a)) * (snd (orbit a p k) * snd (orbit a p k))
    <= 4 * Qf a (fst p) (snd p).
Proof.
  intros a p k Ha0 Ha4.
  assert (Hinv := orbit_invariant a p k).
  assert (Hlow := Qf_lower a (fst (orbit a p k)) (snd (orbit a p k)) Ha0 Ha4).
  lra.
Qed.

(* every orbit point occurs as  snd (orbit a p k)  for some k          *)
(* (u_0 at k = 0, u_k at step k), so orbit_bounded covers the whole    *)
(* trajectory; the symmetric bound on fst follows from Qf_sym.         *)
Theorem orbit_bounded_fst : forall a p k,
  0 <= a -> a <= 4 ->
  (a * (4 - a)) * (fst (orbit a p k) * fst (orbit a p k))
    <= 4 * Qf a (fst p) (snd p).
Proof.
  intros a p k Ha0 Ha4.
  assert (Hinv := orbit_invariant a p k).
  assert (Hsym := Qf_sym a (fst (orbit a p k)) (snd (orbit a p k))).
  assert (Hlow := Qf_lower a (snd (orbit a p k)) (fst (orbit a p k)) Ha0 Ha4).
  lra.
Qed.

(* ------------------------------------------------------------------ *)
(* Dissipative step: exact decrement of the quadratic energy.          *)
(*   step:   (M + c) * u' == (2*M - s) * u - (M - c) * v               *)
(*   energy: G M s p q = M * (p - q)^2 + s * (p * q)                   *)
(* ------------------------------------------------------------------ *)

Definition G (M s p q : Q) : Q := M * ((p - q) * (p - q)) + s * (p * q).

(* the KEY ring identity: the energy decrement plus c*(u'-v)^2 factors  *)
(* through the step polynomial, so on-step it vanishes identically      *)
Theorem damped_energy_identity : forall M c s u v u',
  (M + c) * u' == (2 * M - s) * u - (M - c) * v ->
  G M s u' u - G M s u v == - (c * ((u' - v) * (u' - v))).
Proof.
  intros M c s u v u' Hstep.
  assert (Hkey : G M s u' u - G M s u v + c * ((u' - v) * (u' - v))
                 == (u' - v)
                    * ((M + c) * u' - ((2 * M - s) * u - (M - c) * v)))
    by (unfold G; ring).
  assert (Hz : (M + c) * u' - ((2 * M - s) * u - (M - c) * v) == 0) by lra.
  rewrite Hz in Hkey.
  assert (Hm : (u' - v) * 0 == 0) by ring.
  lra.
Qed.

(* monotonicity: with c >= 0 the energy never increases *)
Theorem damped_energy_monotone : forall M c s u v u',
  0 <= c ->
  (M + c) * u' == (2 * M - s) * u - (M - c) * v ->
  G M s u' u <= G M s u v.
Proof.
  intros M c s u v u' Hc Hstep.
  assert (Hid := damped_energy_identity M c s u v u' Hstep).
  assert (Hsq : 0 <= c * ((u' - v) * (u' - v)))
    by (apply Qmult_le_0_compat; [exact Hc | apply sq_nonneg]).
  lra.
Qed.

(* the conservative limit: c == 0 gives exact conservation *)
Theorem damped_energy_conserved : forall M c s u v u',
  c == 0 ->
  (M + c) * u' == (2 * M - s) * u - (M - c) * v ->
  G M s u' u == G M s u v.
Proof.
  intros M c s u v u' Hc Hstep.
  assert (Hid := damped_energy_identity M c s u v u' Hstep).
  assert (Hz : c * ((u' - v) * (u' - v)) == 0)
    by (rewrite Hc; ring).
  lra.
Qed.

(* the dissipative energy is the conservative form, rescaled:           *)
(* under  s == M * a  the two energies coincide up to the factor M —    *)
(* this is the exact algebraic joint between this file and              *)
(* RDL_SpectralCeiling.v (whose step_ratio_window puts a in [0,4]).     *)
Theorem G_scales_to_Qf : forall M a s u v,
  s == M * a ->
  G M s u v == M * Qf a u v.
Proof.
  intros M a s u v Hs. unfold G, Qf. rewrite Hs. ring.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions Qf_step_invariant.
Print Assumptions Qf_decomp.
Print Assumptions Qf_window_nonneg.
Print Assumptions Qf_lower.
Print Assumptions orbit_invariant.
Print Assumptions orbit_bounded.
Print Assumptions orbit_bounded_fst.
Print Assumptions damped_energy_identity.
Print Assumptions damped_energy_monotone.
Print Assumptions damped_energy_conserved.
Print Assumptions G_scales_to_Qf.

End RecurrenceEnergy.
