(* ===================================================================== *)
(*  InfoEntropyLicense_attempt.v   (repo namespace: RDL)                  *)
(*  ENTROPY-LANGUAGE READING of the degree/handshake/ceiling family:      *)
(*  reuses the Edge/deg/esum/qsum boilerplate of InfoSpectralCeiling_     *)
(*  attempt.v, the Es++E growth shape of InfoCeilingMonotone_attempt.v,   *)
(*  and the mode_product_ceiling frequency ceiling of the same file,      *)
(*  entirely over Q (no reals).                                          *)
(*                                                                        *)
(*  CLAIMED HERE (candidate for coqc 8.20.1, axiom-free target):          *)
(*    handshake            qsum n (Sloc s0 E) == 2*s0*Scount E            *)
(*                          (degree-sum = 2*|edges| identity, scaled by   *)
(*                           a per-node entropy weight s0)                *)
(*    entropy_monotone     0<=s0 -> Sloc s0 E i <= Sloc s0 (Es++E) i      *)
(*                          (retention-only growth never lowers Sloc)     *)
(*    entropy_identity     s0<>0 -> deg E u+deg E v                       *)
(*                            == (Sloc s0 E u + Sloc s0 E v)/s0           *)
(*    entropy_ceiling      genuinely composes entropy_identity with      *)
(*                          mode_product_ceiling (duplicated locally):    *)
(*                          given the extra "achieving" hypothesis        *)
(*                          2*dmax == deg E u + deg E v (dmax realized     *)
(*                          at the edge (u,v), exactly the kind of         *)
(*                          hypothesis license_inequality already takes   *)
(*                          for a single node), the frequency-side         *)
(*                          quantity M*omsq is bounded by K times the      *)
(*                          entropy-language quantity at u,v:              *)
(*                            M*omsq <= K*((Sloc s0 E u+Sloc s0 E v)/s0)   *)
(*    license_bound        M*omsq <= K*(2*dmax), 0<K  ==>                 *)
(*                            M*omsq/(2*K) <= dmax        (division,      *)
(*                          handled explicitly via Qle_shift_div_r with   *)
(*                          the side condition 0 < 2*K)                   *)
(*    license_inequality   dmax = deg E i (node i realizes the ceiling)   *)
(*                          and  m*(2*c*c) == hbar*omega  (energy         *)
(*                          relation, hbar<>0)  ==>                       *)
(*                            Sloc s0 E i >= s0*(M/(2*K))*omega*omega      *)
(*                          i.e. the entropy at i must be large enough    *)
(*                          to "license" the quantum omega == 2*m*c*c/hbar*)
(*                                                                        *)
(*  HONESTLY NOT CLAIMED: mode_product_ceiling/entropy_ceiling do NOT     *)
(*  prove that some edge (u,v) actually ACHIEVES 2*dmax = deg u + deg v;  *)
(*  that "achieving" step is left as a hypothesis (dmax = deg E i, or     *)
(*  2*dmax == deg E u + deg E v) exactly as InfoSpectralCeiling_attempt.v *)
(*  itself leaves "forall i, deg E i <= dmax" as a hypothesis rather than *)
(*  deriving dmax from a max-search function. No physical identification *)
(*  of s0, M, K, m, c, hbar, omega is claimed; they are plain Q           *)
(*  parameters, mirroring InfoDegreeFromCurvature_attempt.v's own         *)
(*  explicit refusal to smuggle in a physical reading.                   *)
(*                                                                        *)
(*  Pre-checked with exact rationals before authoring.  Expected:         *)
(*  Print Assumptions => Closed under the global context.                *)
(*                                                                        *)
(*  CITATION YEARS for the entropy-language naming used in comments here  *)
(*  (cross-checked against causal-quantum-gravity/paper/mass_note.tex's   *)
(*  bibliography): Bekenstein 1973 (black-hole area-entropy law, Phys.    *)
(*  Rev. D 7:2333-2346) and Wheeler 1990 (it-from-bit framing,            *)
(*  "Information, physics, quantum: the search for links"). Neither is    *)
(*  claimed, proved, or depended on by any theorem below -- s0, Sloc,     *)
(*  Scount are plain Q-valued definitions; calling them "entropy" is a    *)
(*  naming choice, not a physical identification.                        *)
(* ===================================================================== *)

Require Coq.Arith.PeanoNat.
Require Coq.Lists.List.
Require Coq.QArith.QArith.
Require Coq.micromega.Lia.
Require Coq.micromega.Lqa.

Module InfoEntropyLicense.

Import Coq.Lists.List. Import ListNotations.
Import Coq.Arith.PeanoNat.
Import Coq.QArith.QArith.
Import Coq.micromega.Lia.
Import Coq.micromega.Lqa.
Local Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(* Graph boilerplate (mirrors InfoSpectralCeiling_attempt.v /           *)
(* InfoCeilingMonotone_attempt.v).                                      *)
(* ------------------------------------------------------------------ *)

Definition Edge : Type := (nat * nat)%type.

Definition ind (u i : nat) : Q := if Nat.eqb u i then 1 else 0.

Definition share (e : Edge) (i : nat) : Q := ind (fst e) i + ind (snd e) i.

Fixpoint qsum (n : nat) (f : nat -> Q) : Q :=
  match n with
  | O => 0
  | S m => qsum m f + f m
  end.

Definition esum (E : list Edge) (g : Edge -> Q) : Q :=
  fold_right (fun e acc => g e + acc) 0 E.

Definition deg (E : list Edge) (i : nat) : Q := esum E (fun e => share e i).

Definition nodes_ok (n : nat) (E : list Edge) : Prop :=
  forall e, In e E -> (fst e < n)%nat /\ (snd e < n)%nat.

(* ------------------------------------------------------------------ *)
(* Entropy-language definitions.                                       *)
(* ------------------------------------------------------------------ *)

Definition Scount (E : list Edge) : Q := esum E (fun _ => 1).

Definition Sloc (s0 : Q) (E : list Edge) (i : nat) : Q := s0 * deg E i.

(* ------------------------------------------------------------------ *)
(* Toolbox: qsum / esum lemmas (mirrors InfoSpectralCeiling_attempt.v). *)
(* ------------------------------------------------------------------ *)

Lemma qsum_ext : forall n (f g : nat -> Q),
  (forall i, (i < n)%nat -> f i == g i) ->
  qsum n f == qsum n g.
Proof.
  induction n as [| m IH]; intros f g H; simpl.
  - reflexivity.
  - rewrite (IH f g); [| intros i Hi; apply H; lia].
    rewrite (H m); [reflexivity | lia].
Qed.

Lemma qsum_zero : forall n, qsum n (fun _ => 0) == 0.
Proof.
  induction n as [| m IH]; simpl; [reflexivity | rewrite IH; ring].
Qed.

Lemma qsum_plus : forall n (f g : nat -> Q),
  qsum n (fun i => f i + g i) == qsum n f + qsum n g.
Proof.
  induction n as [| m IH]; intros f g; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

Lemma qsum_scale : forall n (c : Q) (f : nat -> Q),
  qsum n (fun i => c * f i) == c * qsum n f.
Proof.
  induction n as [| m IH]; intros c f; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

Lemma esum_scale : forall E (c : Q) (g : Edge -> Q),
  esum E (fun e => c * g e) == c * esum E g.
Proof.
  induction E as [| e r IH]; intros c g; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

Lemma esum_const : forall E (c : Q), esum E (fun _ => c) == c * esum E (fun _ => 1).
Proof.
  induction E as [| e r IH]; intro c; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

Lemma esum_app : forall (a b : list Edge) (g : Edge -> Q),
  esum (a ++ b) g == esum a g + esum b g.
Proof.
  induction a as [| e r IH]; intros b g; simpl.
  - ring.
  - rewrite (IH b g). ring.
Qed.

Lemma esum_nonneg : forall E (g : Edge -> Q),
  (forall e, In e E -> 0 <= g e) ->
  0 <= esum E g.
Proof.
  induction E as [| e r IH]; intros g H; simpl.
  - lra.
  - assert (H1 : 0 <= g e) by (apply H; left; reflexivity).
    assert (H2 : 0 <= esum r g)
      by (apply IH; intros e' He'; apply H; right; exact He').
    lra.
Qed.

Lemma share_nonneg : forall (e : Edge) (i : nat), 0 <= share e i.
Proof.
  intros e i. unfold share, ind.
  destruct (Nat.eqb (fst e) i); destruct (Nat.eqb (snd e) i); lra.
Qed.

Lemma isum_out : forall n u (g : nat -> Q),
  (n <= u)%nat ->
  qsum n (fun i => ind u i * g i) == 0.
Proof.
  induction n as [| m IH]; intros u g H; simpl.
  - reflexivity.
  - assert (Eq : Nat.eqb u m = false) by (apply Nat.eqb_neq; lia).
    unfold ind at 2. rewrite Eq.
    rewrite (IH u g); [ring | lia].
Qed.

Lemma isum_in : forall n u (g : nat -> Q),
  (u < n)%nat ->
  qsum n (fun i => ind u i * g i) == g u.
Proof.
  induction n as [| m IH]; intros u g H; simpl.
  - lia.
  - destruct (Nat.eq_dec u m) as [-> | Hne].
    + rewrite (isum_out m m g); [| lia].
      unfold ind at 1. rewrite Nat.eqb_refl. ring.
    + assert (Eq : Nat.eqb u m = false) by (apply Nat.eqb_neq; lia).
      unfold ind at 2. rewrite Eq.
      rewrite (IH u g); [ring | lia].
Qed.

Lemma share_sum : forall n (e : Edge) (g : nat -> Q),
  (fst e < n)%nat -> (snd e < n)%nat ->
  qsum n (fun i => share e i * g i) == g (fst e) + g (snd e).
Proof.
  intros n e g Hu Hv.
  rewrite (qsum_ext n (fun i => share e i * g i)
                      (fun i => ind (fst e) i * g i + ind (snd e) i * g i));
    [| intros i _; unfold share; ring].
  rewrite qsum_plus.
  rewrite (isum_in n (fst e) g Hu).
  rewrite (isum_in n (snd e) g Hv).
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* (1) THE HANDSHAKE LEMMA:  qsum n (deg E) == 2 * Scount E,            *)
(* i.e. every edge contributes exactly 2 to the total degree sum.       *)
(* ------------------------------------------------------------------ *)

Lemma deg_qsum_swap : forall E n,
  nodes_ok n E ->
  qsum n (fun i => deg E i) == esum E (fun _ => 2).
Proof.
  induction E as [| e r IH]; intros n Hok; simpl.
  - rewrite qsum_zero. reflexivity.
  - destruct (Hok e (or_introl eq_refl)) as [Hu Hv].
    rewrite qsum_plus.
    rewrite (qsum_ext n (fun i => share e i) (fun i => share e i * 1));
      [| intros i _; ring].
    rewrite (share_sum n e (fun _ => 1) Hu Hv).
    rewrite (IH n); [ring |].
    intros e' He'. apply Hok. right. exact He'.
Qed.

(* THE HANDSHAKE, entropy-scaled: qsum n (Sloc s0 E) == 2*s0*Scount E.   *)
Theorem handshake : forall (s0 : Q) (E : list Edge) (n : nat),
  nodes_ok n E ->
  qsum n (fun i => Sloc s0 E i) == 2 * s0 * Scount E.
Proof.
  intros s0 E n Hok.
  unfold Sloc.
  rewrite (qsum_scale n s0 (deg E)).
  rewrite (deg_qsum_swap E n Hok).
  unfold Scount.
  rewrite (esum_const E 2).
  ring.
Qed.

(* ------------------------------------------------------------------ *)
(* (2) ENTROPY MONOTONE UNDER RETENTION-ONLY GROWTH (Es ++ E shape,     *)
(* exactly as in InfoCeilingMonotone_attempt.v's deg_monotone_app).     *)
(* ------------------------------------------------------------------ *)

Theorem deg_step_add : forall (E : list Edge) (e : Edge) (i : nat),
  deg (e :: E) i == deg E i + share e i.
Proof.
  intros E e i. unfold deg, esum. simpl. ring.
Qed.

Theorem deg_monotone_app : forall (Es E : list Edge) (i : nat),
  deg E i <= deg (Es ++ E) i.
Proof.
  intros Es E i.
  assert (Ha := esum_app Es E (fun e => share e i)).
  assert (Hn : 0 <= esum Es (fun e => share e i))
    by (apply esum_nonneg; intros e _; apply share_nonneg).
  unfold deg in *. lra.
Qed.

Theorem entropy_monotone : forall (s0 : Q) (Es E : list Edge) (i : nat),
  0 <= s0 ->
  Sloc s0 E i <= Sloc s0 (Es ++ E) i.
Proof.
  intros s0 Es E i Hs0. unfold Sloc.
  rewrite (Qmult_comm s0 (deg E i)), (Qmult_comm s0 (deg (Es ++ E) i)).
  apply Qmult_le_compat_r; [apply deg_monotone_app | exact Hs0].
Qed.

(* ------------------------------------------------------------------ *)
(* (3) THE ALGEBRAIC ENTROPY IDENTITY and its composition with the      *)
(* frequency ceiling (mode_product_ceiling, duplicated from             *)
(* InfoSpectralCeiling_attempt.v -- pure Q algebra, no graph data).      *)
(* ------------------------------------------------------------------ *)

Theorem entropy_identity : forall (s0 : Q) (E : list Edge) (u v : nat),
  ~ s0 == 0 ->
  deg E u + deg E v == (Sloc s0 E u + Sloc s0 E v) / s0.
Proof.
  intros s0 E u v Hs0. unfold Sloc.
  assert (Hsum : s0 * deg E u + s0 * deg E v == (deg E u + deg E v) * s0)
    by ring.
  rewrite Hsum.
  symmetry.
  apply Qdiv_mult_l. exact Hs0.
Qed.

Theorem mode_product_ceiling : forall M K omsq lam dmax,
  0 <= K ->
  M * omsq == K * lam ->
  lam <= 2 * dmax ->
  M * omsq <= K * (2 * dmax).
Proof.
  intros M K omsq lam dmax HK Hd Hlam.
  assert (Hkl : lam * K <= (2 * dmax) * K)
    by (apply Qmult_le_compat_r; assumption).
  lra.
Qed.

(* dmax realized at the edge (u,v) (an explicit "achieving" hypothesis, *)
(* of exactly the kind license_inequality already takes for a single    *)
(* node -- here for a pair of nodes summing to 2*dmax), composed with    *)
(* entropy_identity so the frequency-side ceiling becomes a genuine       *)
(* bound on the entropy-language quantity at u,v -- not a mere pairing.  *)
Corollary entropy_ceiling :
  forall (s0 : Q) (E : list Edge) (u v : nat) (M K omsq lam dmax : Q),
  ~ s0 == 0 ->
  0 <= K -> M * omsq == K * lam -> lam <= 2 * dmax ->
  2 * dmax == deg E u + deg E v ->
  M * omsq <= K * ((Sloc s0 E u + Sloc s0 E v) / s0).
Proof.
  intros s0 E u v M K omsq lam dmax Hs0 HK Hd Hlam Hachieve.
  assert (Hceil := mode_product_ceiling M K omsq lam dmax HK Hd Hlam).
  rewrite Hachieve in Hceil.
  rewrite (entropy_identity s0 E u v Hs0) in Hceil.
  exact Hceil.
Qed.

(* ------------------------------------------------------------------ *)
(* (4) THE LICENSE INEQUALITY: rearranging the ceiling into a LOWER     *)
(* bound on the entropy at the node realizing the maximum degree, and   *)
(* reading the frequency omega through a plain energy relation.         *)
(* ------------------------------------------------------------------ *)

Theorem license_bound : forall M K omsq dmax : Q,
  0 < K ->
  M * omsq <= K * (2 * dmax) ->
  M * omsq / (2 * K) <= dmax.
Proof.
  intros M K omsq dmax HK Hle.
  apply Qle_shift_div_r; [lra |].
  assert (Heq : dmax * (2 * K) == K * (2 * dmax)) by ring.
  rewrite Heq. exact Hle.
Qed.

(* dmax realized at node i (an explicit hypothesis, exactly as          *)
(* InfoSpectralCeiling_attempt.v leaves "forall i, deg E i <= dmax" as   *)
(* a hypothesis rather than deriving dmax from a max-search function),  *)
(* plus a plain-Q energy relation m*(2*c*c) == hbar*omega, hbar<>0.      *)
Theorem license_inequality :
  forall (s0 : Q) (E : list Edge) (i : nat) (M K omsq dmax m c hbar omega : Q),
  0 <= s0 ->
  0 < K ->
  ~ hbar == 0 ->
  M * omsq <= K * (2 * dmax) ->
  dmax == deg E i ->
  m * (2 * c * c) == hbar * omega ->
  omsq == omega * omega ->
  Sloc s0 E i >= s0 * (M / (2 * K)) * ((2 * m * c * c) / hbar) * ((2 * m * c * c) / hbar).
Proof.
  intros s0 E i M K omsq dmax m c hbar omega Hs0 HK Hhbar Hle Hdmax Homega Homsq.
  unfold Sloc.
  assert (Hbound := license_bound M K omsq dmax HK Hle).
  rewrite Hdmax in Hbound.
  (* omega == (2*m*c*c)/hbar, from the energy relation and hbar<>0 *)
  assert (Hom : omega == (2 * m * c * c) / hbar).
  { symmetry.
    assert (Hcomm : 2 * m * c * c == omega * hbar).
    { transitivity (m * (2 * c * c)); [ring |].
      transitivity (hbar * omega); [exact Homega | ring]. }
    rewrite Hcomm.
    apply Qdiv_mult_l. exact Hhbar. }
  (* rewrite the RHS of the goal to M/(2K) * omsq, then use Hbound *)
  assert (HRHS : s0 * (M / (2 * K)) * ((2 * m * c * c) / hbar) * ((2 * m * c * c) / hbar)
                 == s0 * ((M / (2 * K)) * omsq)).
  { rewrite <- Hom, Homsq. ring. }
  apply Qle_ge.
  rewrite HRHS.
  assert (Hstep : s0 * ((M / (2*K)) * omsq) == s0 * (M * omsq / (2*K))).
  { assert (Hh : M / (2*K) * omsq == M * omsq / (2*K)) by (unfold Qdiv; ring).
    rewrite Hh. reflexivity. }
  rewrite Hstep.
  rewrite (Qmult_comm s0 (M * omsq / (2 * K))), (Qmult_comm s0 (deg E i)).
  apply Qmult_le_compat_r; [exact Hbound | exact Hs0].
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions handshake.
Print Assumptions entropy_monotone.
Print Assumptions entropy_identity.
Print Assumptions entropy_ceiling.
Print Assumptions license_bound.
Print Assumptions license_inequality.

End InfoEntropyLicense.
