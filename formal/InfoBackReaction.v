(* ===================================================================== *)
(*  InfoBackReaction.v                                                    *)
(*  THE MISSING LINK OF THE FEEDBACK LOOP: BACKGROUND STRAIN IS EXACT.    *)
(*                                                                        *)
(*  A background field acts on the geometry side through edge strain.     *)
(*  Results (all exact over Q):                                           *)
(*                                                                        *)
(*    edge_strain_expansion_exact   the strain of background+perturbation *)
(*                                  splits EXACTLY into background        *)
(*                                  strain, cross term, perturbation      *)
(*                                  strain --- nothing dropped            *)
(*    budget_consumed_exact         the retention budget left for the     *)
(*                                  perturbation is the original budget   *)
(*                                  minus EXACTLY what the background     *)
(*                                  and the cross term take               *)
(*    retention_shift_iff           the balance test for the total field  *)
(*                                  is EQUIVALENT to the shifted test     *)
(*                                  for the perturbation                  *)
(*    strain_nonneg /               strain is a square: nonnegative, and  *)
(*    strain_zero_iff               zero exactly on flat edges            *)
(*                                                                        *)
(*  SCOPE, STATED EXACTLY: this file closes ONE joint of the feedback     *)
(*  loop --- the strain face of back-reaction (stored field -> edge       *)
(*  strain -> retention budget).  The loop                                *)
(*     stored energy -> edge strain -> retention decision -> geometry     *)
(*     -> inertia -> motion                                               *)
(*  is NOT closed by it: two joints remain Open and are named ---         *)
(*  OB-HOMOGENIZATION (the passage from the pointwise coefficient shift   *)
(*  3*g*psi^2 of InfoCubicLinearization.v to an effective inertia; a      *)
(*  time-averaging step, disclosed there) and OB-GEODESIC (a general      *)
(*  trajectory theorem; only a one-dimensional numerical demonstration    *)
(*  exists).  ALSO NOT CLAIMED: any statement about the RANGE of the      *)
(*  geometry response, an open question this file deliberately tees up.   *)
(*  Expected: Print Assumptions => Closed under the global context.       *)
(* ===================================================================== *)

Require Coq.QArith.QArith.
Require Coq.micromega.Lqa.

Module BackReaction.

Import Coq.QArith.QArith.
Import Coq.micromega.Lqa.
Local Open Scope Q_scope.

Definition Edge : Type := (nat * nat)%type.

Definition ediff (x : nat -> Q) (e : Edge) : Q := x (fst e) - x (snd e).

Definition strain (x : nat -> Q) (e : Edge) : Q := ediff x e * ediff x e.

(* ------------------------------------------------------------------ *)
(* Exact split of strain                                               *)
(* ------------------------------------------------------------------ *)

Theorem edge_strain_expansion_exact :
  forall (bg pert : nat -> Q) (e : Edge),
  strain (fun k => bg k + pert k) e
  == strain bg e + 2 * (ediff bg e * ediff pert e) + strain pert e.
Proof. intros bg pert e. unfold strain, ediff. simpl. ring. Qed.

Theorem budget_consumed_exact :
  forall (bg pert : nat -> Q) (e : Edge) (b : Q),
  b - strain (fun k => bg k + pert k) e
  == (b - strain pert e) - strain bg e - 2 * (ediff bg e * ediff pert e).
Proof. intros bg pert e b. unfold strain, ediff. simpl. ring. Qed.

Theorem retention_shift_iff :
  forall (bg pert : nat -> Q) (e : Edge) (b : Q),
  strain (fun k => bg k + pert k) e <= b
  <->
  strain pert e <= b - strain bg e - 2 * (ediff bg e * ediff pert e).
Proof.
  intros bg pert e b.
  assert (H := edge_strain_expansion_exact bg pert e).
  split; intros Hle; lra.
Qed.

(* ------------------------------------------------------------------ *)
(* Signs                                                               *)
(* ------------------------------------------------------------------ *)

Theorem strain_nonneg : forall (x : nat -> Q) (e : Edge),
  0 <= strain x e.
Proof. intros x e. unfold strain. nra. Qed.

Theorem strain_zero_iff : forall (x : nat -> Q) (e : Edge),
  strain x e == 0 <-> ediff x e == 0.
Proof.
  intros x e. unfold strain. split; intros H.
  - destruct (Q_dec 0 (ediff x e)) as [[Hlt | Hgt] | Heq]; [nra | nra |].
    symmetry. exact Heq.
  - nra.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions edge_strain_expansion_exact.
Print Assumptions budget_consumed_exact.
Print Assumptions retention_shift_iff.
Print Assumptions strain_nonneg.
Print Assumptions strain_zero_iff.

End BackReaction.
