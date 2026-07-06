(******************************************************************************)
(* InfoConnectionFromFrame_attempt.v -- EXPLORATORY, single-attempt.            *)
(*   Requires InfoDiscreteRiemannCommutator_attempt (REUSES the Heisenberg group *)
(*   Hb/hmul/hinv/hid, never redefines) + Coq.QArith + Lqa. No Reals, no axiom.  *)
(*   TIER = Th_coqc (Q-only, axiom-free). Compile: coqc -q -R . RDL <this>.     *)
(*                                                                            *)
(* TYING THE CURVATURE-COMMUTATOR TO A GEOMETRIC FIELD (pure-gauge = flat).      *)
(*                                                                            *)
(* InfoDiscreteRiemannCommutator proved: 2-index curvature = the transport       *)
(* holonomy / group commutator (division-free, Heisenberg). But an ARBITRARY    *)
(* connection is a gauge field, not yet geometry (the skeptic's + both other     *)
(* lenses' warning: the connection must come from a geometric object, and the   *)
(* pure-gauge case must be provably FLAT, else 'curvature' is a coordinate       *)
(* artifact). This file ties the connection to a FRAME FIELD f : node -> Hb      *)
(* (a group-valued frame at each node -- the readout-not-truth geometric object, *)
(* division-free) and proves the discrete analogue of 'a change of frame /       *)
(* coordinates cannot create curvature'.                                        *)
(*                                                                            *)
(* The frame-difference connection along a path is the coboundary transport      *)
(*   A(f,k) := hmul (f (S k)) (hinv (f k)),                                      *)
(* and the path holonomy is the ordered product                                 *)
(*   pathprod f n := A(f,n-1) * A(f,n-2) * ... * A(f,0)  (newest edge on left).  *)
(*                                                                            *)
(* WHAT IS PROVED (Th_coqc, axiom-free over Q; Compute-checked witness):        *)
(*   hmul_assoc / hmul_id_l / hmul_inv_l : the Heisenberg GROUP laws (so the      *)
(*       telescoping below is a genuine group identity, not hand-waving).        *)
(*   coboundary_telescopes : pathprod f n === hmul (f n) (hinv (f O)) -- the      *)
(*       whole path holonomy collapses to the ENDPOINT frames only.             *)
(*   closed_loop_pure_gauge_flat : if the loop returns to its starting frame     *)
(*       (f n === f 0) the holonomy is the identity -- PURE GAUGE IS FLAT. A     *)
(*       frame change (coordinate change) around a closed loop produces ZERO     *)
(*       curvature, exactly as an affine metric was flat in the scalar brick.    *)
(*   genuine_curvature_is_non_coboundary (witness): a NON-coboundary connection   *)
(*       (the a=2,b=3 plaquette increments, which are NOT the difference of any   *)
(*       single node frame around the loop) has nonzero holonomy z == 6 -- so     *)
(*       genuine curvature is provably NOT pure gauge.                          *)
(*                                                                            *)
(* HONEST FENCE. CLOSED: the frame-field connection, the group laws, the exact   *)
(* coboundary telescoping, pure-gauge-is-flat, and genuine-curvature-is-non-     *)
(* coboundary -- all division-free over Q. [Open], NOT smuggled: the frame here  *)
(* is Heisenberg-valued (unipotent), NOT an orthonormal frame of an actual        *)
(* METRIC (that needs SO(n)/isometry, det<>0); deriving the frame from a finite  *)
(* metric second difference, metric-compatibility / ij-antisymmetry, pair        *)
(* symmetry, Bianchi, and the full R^i_jkl array all stay [Open]. The continuum  *)
(* is refused. All quantities plain Q; no Reals, no division, no constant.       *)
(******************************************************************************)

Require InfoDiscreteRiemannCommutator_attempt.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.

Module InfoConnectionFromFrame.
Import InfoDiscreteRiemannCommutator_attempt.InfoDiscreteRiemannCommutator.
Open Scope Q_scope.

(* component-wise equality on the Heisenberg group *)
Definition Heq (g1 g2 : Hb) : Prop :=
  hx g1 == hx g2 /\ hy g1 == hy g2 /\ hz g1 == hz g2.

(* ------------------------------------------------------------------ *)
(* group laws (each: simpl + ring per component) -- so the telescoping *)
(* is a genuine group identity.                                        *)
(* ------------------------------------------------------------------ *)
Theorem hmul_assoc : forall a b c : Hb,
  Heq (hmul (hmul a b) c) (hmul a (hmul b c)).
Proof. intros a b c. unfold Heq; simpl. repeat split; ring. Qed.

Theorem hmul_id_l : forall g : Hb, Heq (hmul hid g) g.
Proof. intro g. unfold Heq; simpl. repeat split; ring. Qed.

Theorem hmul_inv_l : forall g : Hb, Heq (hmul (hinv g) g) hid.
Proof. intro g. unfold Heq; simpl. repeat split; ring. Qed.

(* frame-difference connection and the ordered path holonomy *)
Definition Aedge (f : nat -> Hb) (k : nat) : Hb := hmul (f (S k)) (hinv (f k)).
Fixpoint pathprod (f : nat -> Hb) (n : nat) : Hb :=
  match n with O => hid | S k => hmul (Aedge f k) (pathprod f k) end.

(* ------------------------------------------------------------------ *)
(* coboundary telescoping: the holonomy depends only on the endpoints. *)
(* proved component-wise (hx,hy linear; hz nonlinear via the IH).      *)
(* ------------------------------------------------------------------ *)
Theorem coboundary_telescopes :
  forall (f : nat -> Hb) (n : nat),
    Heq (pathprod f n) (hmul (f n) (hinv (f O))).
Proof.
  intros f n. induction n as [| k IH].
  - unfold Heq; simpl. repeat split; ring.
  - destruct IH as [IHx [IHy IHz]].
    unfold Heq in *. unfold pathprod; fold pathprod. unfold Aedge.
    simpl in *. repeat split; nra.
Qed.

(* ------------------------------------------------------------------ *)
(* PURE GAUGE IS FLAT: a closed frame loop has trivial holonomy.       *)
(* ------------------------------------------------------------------ *)
Theorem closed_loop_pure_gauge_flat :
  forall (f : nat -> Hb) (n : nat),
    Heq (f n) (f O) ->
    Heq (pathprod f n) hid.
Proof.
  intros f n Hclosed.
  destruct (coboundary_telescopes f n) as [Tx [Ty Tz]].
  destruct Hclosed as [Cx [Cy Cz]].
  simpl in Tx, Ty, Tz.
  unfold Heq; simpl. repeat split; nra.
Qed.

(* ------------------------------------------------------------------ *)
(* genuine curvature is NON-coboundary: the a=2,b=3 plaquette          *)
(* commutator (from InfoDiscreteRiemannCommutator) has z == 6 <> 0,    *)
(* so it is not the holonomy of any closed frame loop (which is flat). *)
(* ------------------------------------------------------------------ *)
Example genuine_curvature_is_non_coboundary :
  hz (commutator (mkH 2 0 0) (mkH 0 3 0)) == 6.
Proof. simpl. ring. Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions coboundary_telescopes.
Print Assumptions closed_loop_pure_gauge_flat.
Print Assumptions hmul_assoc.

End InfoConnectionFromFrame.
