(* ===================================================================== *)
(*  RDL_CurvatureBalance.v                                                 *)
(*  THE BALANCE LAW IN CURVATURE FORM, THE THRESHOLD PAIR, AND THE         *)
(*  JOINT STATIONARY CONFIGURATION — closing the structural loop           *)
(*    field <-> geometry <-> curvature <-> threshold                       *)
(*  entirely over Q.                                                       *)
(*                                                                         *)
(*  Conventions: forman(e) = 4 - deg(u) - deg(v)  (as in the C40 line and  *)
(*  RDL_GraphGrowth.v);  Sgeo, retention balance as in                     *)
(*  RDL_ActionStationarity.v;  the modal energy G and dissipative step     *)
(*  as in RDL_RecurrenceEnergy.v, here extended with a bounded control     *)
(*  slot a (total per-mode dissipation c + a, |a| <= B).                   *)
(*                                                                         *)
(*  CLAIMED HERE (candidate for coqc 8.18.0, axiom-free target):           *)
(*    edge_deg_curvature      deg(u) + deg(v) == 4 - forman(e)   (exact)   *)
(*    forman_growth_shift     re-proved locally (standalone file)          *)
(*    self_curvature_drop     a simple edge's own creation lowers its own  *)
(*                            curvature by EXACTLY 2                       *)
(*    curvature_balance_add / curvature_balance_rem                        *)
(*        with the retention benefit priced AFFINELY IN CURVATURE          *)
(*        (b(e) = alpha + beta * forman(e), curvature taken in the         *)
(*        reference graph), the geometry-variation balance becomes an      *)
(*        exact iff between quadratic field strain and curvature:          *)
(*          edge absent-stable  iff  alpha + beta*F(e) <= strain(e)        *)
(*          edge retained-stable iff strain(e) <= alpha + beta*F(e)        *)
(*        — strain determines curvature and curvature determines strain,   *)
(*        both directions, exactly.                                        *)
(*    horizon_threshold_curvature / threshold_antitone                     *)
(*        the combined per-edge dissipation threshold                      *)
(*          Cs * (deg u + deg v)                                           *)
(*        is EXACTLY the affine function Cs * (4 - forman(e)) of that      *)
(*        edge's curvature, and is antitone in curvature: the more         *)
(*        negative the curvature, the higher the threshold.                *)
(*    control_energy_identity                                              *)
(*        the dissipative step with control a obeys                        *)
(*          G(u',u) - G(u,v) == -((c+a) * (u'-v)^2)   EXACTLY              *)
(*    no_escape / no_escape_strict                                         *)
(*        if the ambient dissipation exceeds the whole control budget      *)
(*        (B < c), then EVERY admissible control (|a| <= B) leaves the     *)
(*        energy nonincreasing (strictly decreasing off the fixed ray):    *)
(*        past the threshold no selection changes the outcome — the        *)
(*        threshold is a theorem, not a definition.                        *)
(*    repair_exists                                                        *)
(*        below the threshold (c < B) an explicit admissible control       *)
(*        (a = -B) makes the energy nondecreasing: selection retains       *)
(*        force exactly up to the threshold.                               *)
(*    vacuum_joint_stationary                                              *)
(*        the constant field is a SIMULTANEOUS stationary configuration    *)
(*        of both variations: its step residual vanishes at every node     *)
(*        of every graph, and every retained edge with nonnegative         *)
(*        benefit satisfies the retained-stability balance — the joint     *)
(*        fixed point of the field and geometry selections is nonempty.    *)
(*                                                                         *)
(*  HONESTLY NOT CLAIMED: any continuum limit, any metric, and the         *)
(*  identification of the threshold pair with any physical boundary —      *)
(*  those readings live outside the .v files, at their stated tiers.       *)
(*                                                                         *)
(*  Pre-verified with exact rational arithmetic (300 random draws; every   *)
(*  identity, both iff directions, both threshold branches, and the        *)
(*  vacuum configuration checked exactly) before authoring.                *)
(*  Expected: Print Assumptions => Closed under the global context.        *)
(* ===================================================================== *)

Require Coq.Arith.PeanoNat.
Require Coq.Lists.List.
Require Coq.QArith.QArith.
Require Coq.micromega.Lia.
Require Coq.micromega.Lqa.

Module CurvatureBalance.

Import Coq.Lists.List. Import ListNotations.
Import Coq.Arith.PeanoNat.
Import Coq.QArith.QArith.
Import Coq.micromega.Lia.
Import Coq.micromega.Lqa.
Local Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(* Graph data (shared conventions; self-contained for standalone coqc) *)
(* ------------------------------------------------------------------ *)

Definition Edge : Type := (nat * nat)%type.

Definition esum (E : list Edge) (g : Edge -> Q) : Q :=
  fold_right (fun e acc => g e + acc) 0 E.

Definition ediff (x : nat -> Q) (e : Edge) : Q := x (fst e) - x (snd e).

Definition ind (u i : nat) : Q := if Nat.eqb u i then 1 else 0.

Definition lint (x : nat -> Q) (i : nat) (e : Edge) : Q :=
  (ind (fst e) i - ind (snd e) i) * ediff x e.

Definition lap (E : list Edge) (x : nat -> Q) (i : nat) : Q :=
  esum E (lint x i).

Definition gform (E : list Edge) (x y : nat -> Q) : Q :=
  esum E (fun e => ediff x e * ediff y e).

Definition share (e : Edge) (i : nat) : Q :=
  (if Nat.eqb (fst e) i then 1 else 0) + (if Nat.eqb (snd e) i then 1 else 0).

Definition deg (E : list Edge) (i : nat) : Q := esum E (fun e => share e i).

Definition forman (E : list Edge) (e : Edge) : Q :=
  4 - deg E (fst e) - deg E (snd e).

(* geometric functional (as in RDL_ActionStationarity.v) *)
Definition Sgeo (E : list Edge) (m : nat -> Q) (b : Edge -> Q)
                (h K : Q) : Q :=
  (h * h * K) * gform E m m - esum E b.

(* modal energy (as in RDL_RecurrenceEnergy.v) *)
Definition G (M s p q : Q) : Q := M * ((p - q) * (p - q)) + s * (p * q).

(* ------------------------------------------------------------------ *)
(* Toolbox                                                             *)
(* ------------------------------------------------------------------ *)

Lemma sq_nonneg : forall x : Q, 0 <= x * x.
Proof.
  intro x. destruct (Qlt_le_dec x 0) as [Hneg | Hpos].
  - setoid_replace (x * x) with ((- x) * (- x)) by ring.
    apply Qmult_le_0_compat; lra.
  - apply Qmult_le_0_compat; lra.
Qed.

Lemma sq_pos : forall x : Q, ~ x == 0 -> 0 < x * x.
Proof.
  intros x Hx.
  destruct (Qlt_le_dec x 0) as [Hneg | Hpos].
  - setoid_replace (x * x) with ((- x) * (- x)) by ring.
    assert (H0 : 0 < - x) by lra.
    assert (Hm : 0 * (- x) < (- x) * (- x))
      by (apply Qmult_lt_compat_r; lra).
    lra.
  - assert (H0 : 0 < x) by lra.
    assert (Hm : 0 * x < x * x)
      by (apply Qmult_lt_compat_r; lra).
    lra.
Qed.

Lemma esum_ext : forall E (f g : Edge -> Q),
  (forall e, In e E -> f e == g e) ->
  esum E f == esum E g.
Proof.
  induction E as [| e r IH]; intros f g H; simpl.
  - reflexivity.
  - rewrite (H e); [| left; reflexivity].
    rewrite (IH f g); [reflexivity | intros e' He'; apply H; right; exact He'].
Qed.

Lemma esum_zero : forall E, esum E (fun _ => 0) == 0.
Proof.
  induction E as [| e r IH]; simpl; [reflexivity | rewrite IH; ring].
Qed.

(* ------------------------------------------------------------------ *)
(* PART I — CURVATURE, DEGREE, AND THE THRESHOLD                       *)
(* ------------------------------------------------------------------ *)

(* the exact affine bridge between the degree pair and curvature *)
Theorem edge_deg_curvature : forall E (e : Edge),
  deg E (fst e) + deg E (snd e) == 4 - forman E e.
Proof.
  intros E e. unfold forman. ring.
Qed.

(* re-proved locally: the exact law of curvature under growth *)
Theorem forman_growth_shift : forall E (estar e : Edge),
  forman (estar :: E) e
  == forman E e - share estar (fst e) - share estar (snd e).
Proof.
  intros E estar e. unfold forman, deg. simpl. ring.
Qed.

(* a simple edge's own creation lowers its own curvature by EXACTLY 2 *)
Theorem self_curvature_drop : forall E (estar : Edge),
  fst estar <> snd estar ->
  forman (estar :: E) estar == forman E estar - 2.
Proof.
  intros E estar Hne.
  assert (Hs := forman_growth_shift E estar estar).
  assert (H1 : share estar (fst estar) == 1).
  { unfold share. rewrite Nat.eqb_refl.
    assert (Ef : Nat.eqb (snd estar) (fst estar) = false)
      by (apply Nat.eqb_neq; intro Hvu; apply Hne; symmetry; exact Hvu).
    rewrite Ef. ring. }
  assert (H2 : share estar (snd estar) == 1).
  { unfold share. rewrite Nat.eqb_refl.
    assert (Ef : Nat.eqb (fst estar) (snd estar) = false)
      by (apply Nat.eqb_neq; exact Hne).
    rewrite Ef. ring. }
  lra.
Qed.

(* the combined per-edge dissipation threshold is EXACTLY affine in    *)
(* that edge's curvature                                               *)
Theorem horizon_threshold_curvature : forall E (e : Edge) (Cs : Q),
  Cs * (deg E (fst e) + deg E (snd e)) == Cs * (4 - forman E e).
Proof.
  intros E e Cs.
  assert (H := edge_deg_curvature E e).
  rewrite H. reflexivity.
Qed.

(* ... and antitone in curvature: the more negative the curvature, the *)
(* higher the threshold                                                *)
Theorem threshold_antitone : forall E (e1 e2 : Edge) (Cs : Q),
  0 <= Cs ->
  forman E e1 <= forman E e2 ->
  Cs * (4 - forman E e2) <= Cs * (4 - forman E e1).
Proof.
  intros E e1 e2 Cs HCs Hf.
  assert (Hm : (4 - forman E e2) * Cs <= (4 - forman E e1) * Cs)
    by (apply Qmult_le_compat_r; [lra | exact HCs]).
  lra.
Qed.

(* ------------------------------------------------------------------ *)
(* PART II — THE BALANCE LAW IN CURVATURE FORM.                        *)
(* The retention benefit is priced affinely in the REFERENCE graph's   *)
(* curvature:  b(e) := alpha + beta * forman(E, e).                    *)
(* ------------------------------------------------------------------ *)

(* the exact variation of the functional under adding one edge         *)
(* (generic in the benefit; as in RDL_ActionStationarity.v)            *)
Theorem addition_variation :
  forall E (m : nat -> Q) (b : Edge -> Q) (h K : Q) (estar : Edge),
  Sgeo (estar :: E) m b h K - Sgeo E m b h K
  == (h * h * K) * (ediff m estar * ediff m estar) - b estar.
Proof.
  intros E m b h K estar.
  unfold Sgeo, gform. simpl. ring.
Qed.

(* absent edge stays absent  iff  its curvature-priced benefit does    *)
(* not exceed the quadratic field strain it would carry                *)
Theorem curvature_balance_add :
  forall E (m : nat -> Q) (h K alpha beta : Q) (estar : Edge),
  Sgeo E m (fun e => alpha + beta * forman E e) h K
    <= Sgeo (estar :: E) m (fun e => alpha + beta * forman E e) h K
  <-> alpha + beta * forman E estar
      <= (h * h * K) * (ediff m estar * ediff m estar).
Proof.
  intros E m h K alpha beta estar.
  assert (Hv := addition_variation E m
                  (fun e => alpha + beta * forman E e) h K estar).
  cbv beta in Hv.
  split; intro H; lra.
Qed.

(* retained edge stays retained  iff  its strain does not exceed its   *)
(* curvature-priced benefit                                            *)
Theorem curvature_balance_rem :
  forall E (m : nat -> Q) (h K alpha beta : Q) (e : Edge),
  Sgeo (e :: E) m (fun e' => alpha + beta * forman E e') h K
    <= Sgeo E m (fun e' => alpha + beta * forman E e') h K
  <-> (h * h * K) * (ediff m e * ediff m e)
      <= alpha + beta * forman E e.
Proof.
  intros E m h K alpha beta e.
  assert (Hv := addition_variation E m
                  (fun e' => alpha + beta * forman E e') h K e).
  cbv beta in Hv.
  split; intro H; lra.
Qed.

(* ------------------------------------------------------------------ *)
(* PART III — THE THRESHOLD PAIR: past it no selection matters; below  *)
(* it selection retains force.  Total per-mode dissipation is c + a,   *)
(* with the control a admissible when -B <= a <= B.                    *)
(* ------------------------------------------------------------------ *)

(* the exact energy identity of the controlled dissipative step *)
Theorem control_energy_identity : forall M c a s u v u' : Q,
  (M + (c + a)) * u' == (2 * M - s) * u - (M - (c + a)) * v ->
  G M s u' u - G M s u v == - ((c + a) * ((u' - v) * (u' - v))).
Proof.
  intros M c a s u v u' Hstep.
  assert (Hkey : G M s u' u - G M s u v
                 + (c + a) * ((u' - v) * (u' - v))
                 == (u' - v)
                    * ((M + (c + a)) * u'
                       - ((2 * M - s) * u - (M - (c + a)) * v)))
    by (unfold G; ring).
  assert (Hz : (M + (c + a)) * u'
               - ((2 * M - s) * u - (M - (c + a)) * v) == 0) by lra.
  rewrite Hz in Hkey.
  assert (Hm : (u' - v) * 0 == 0) by ring.
  lra.
Qed.

(* PAST THE THRESHOLD (B < c): every admissible control leaves the     *)
(* energy nonincreasing — no selection changes the outcome             *)
Theorem no_escape : forall M c a s B u v u' : Q,
  0 <= B -> B < c ->
  - B <= a -> a <= B ->
  (M + (c + a)) * u' == (2 * M - s) * u - (M - (c + a)) * v ->
  G M s u' u <= G M s u v.
Proof.
  intros M c a s B u v u' HB Hth Ha1 Ha2 Hstep.
  assert (Hid := control_energy_identity M c a s u v u' Hstep).
  assert (Hca : 0 < c + a) by lra.
  assert (Hsq := sq_nonneg (u' - v)).
  assert (Hp : 0 <= (c + a) * ((u' - v) * (u' - v)))
    by (apply Qmult_le_0_compat; lra).
  lra.
Qed.

Theorem no_escape_strict : forall M c a s B u v u' : Q,
  0 <= B -> B < c ->
  - B <= a -> a <= B ->
  (M + (c + a)) * u' == (2 * M - s) * u - (M - (c + a)) * v ->
  ~ (u' - v == 0) ->
  G M s u' u < G M s u v.
Proof.
  intros M c a s B u v u' HB Hth Ha1 Ha2 Hstep Hnz.
  assert (Hid := control_energy_identity M c a s u v u' Hstep).
  assert (Hca : 0 < c + a) by lra.
  assert (Hsq : 0 < (u' - v) * (u' - v)) by (apply sq_pos; exact Hnz).
  assert (Hp : 0 * ((u' - v) * (u' - v))
               < (c + a) * ((u' - v) * (u' - v)))
    by (apply Qmult_lt_compat_r; [exact Hsq | exact Hca]).
  lra.
Qed.

(* BELOW THE THRESHOLD (c < B): an explicit admissible control makes   *)
(* the energy nondecreasing — selection retains force                  *)
Theorem repair_exists : forall M c s B : Q,
  0 <= c ->
  c < B ->
  exists a : Q,
    - B <= a /\ a <= B /\
    forall u v u' : Q,
      (M + (c + a)) * u' == (2 * M - s) * u - (M - (c + a)) * v ->
      G M s u v <= G M s u' u.
Proof.
  intros M c s B Hc Hth.
  exists (- B).
  split; [lra |]. split; [lra |].
  intros u v u' Hstep.
  assert (Hid := control_energy_identity M c (- B) s u v u' Hstep).
  assert (Hsq := sq_nonneg (u' - v)).
  assert (Hp : 0 <= (B - c) * ((u' - v) * (u' - v)))
    by (apply Qmult_le_0_compat; lra).
  assert (Hneg : (c + - B) * ((u' - v) * (u' - v))
               == - ((B - c) * ((u' - v) * (u' - v)))) by ring.
  lra.
Qed.

(* ------------------------------------------------------------------ *)
(* PART IV — THE JOINT STATIONARY CONFIGURATION IS NONEMPTY:           *)
(* the constant field is stationary for BOTH variations at once.       *)
(* ------------------------------------------------------------------ *)

Lemma lap_const : forall E (k : Q) (i : nat),
  lap E (fun _ => k) i == 0.
Proof.
  intros E k i. unfold lap.
  rewrite (esum_ext E (lint (fun _ => k) i) (fun _ => 0));
    [apply esum_zero |].
  intros e _. unfold lint, ediff. ring.
Qed.

Theorem vacuum_joint_stationary :
  forall E (M h K k : Q) (b : Edge -> Q),
  (forall e, In e E -> 0 <= b e) ->
  (forall i : nat,
     M * (k - 2 * k + k) + (h * h * K) * lap E (fun _ => k) i == 0)
  /\
  (forall e, In e E ->
     (h * h * K) * (ediff (fun _ => k) e * ediff (fun _ => k) e) <= b e).
Proof.
  intros E M h K k b Hb.
  split.
  - intro i.
    assert (Hl := lap_const E k i).
    rewrite Hl. ring.
  - intros e He.
    assert (Hd : ediff (fun _ => k) e == 0) by (unfold ediff; ring).
    assert (Hs : (h * h * K) * (ediff (fun _ => k) e * ediff (fun _ => k) e)
               == 0)
      by (rewrite Hd; ring).
    assert (Hbe := Hb e He).
    lra.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions edge_deg_curvature.
Print Assumptions forman_growth_shift.
Print Assumptions self_curvature_drop.
Print Assumptions horizon_threshold_curvature.
Print Assumptions threshold_antitone.
Print Assumptions curvature_balance_add.
Print Assumptions curvature_balance_rem.
Print Assumptions control_energy_identity.
Print Assumptions no_escape.
Print Assumptions no_escape_strict.
Print Assumptions repair_exists.
Print Assumptions vacuum_joint_stationary.

End CurvatureBalance.
