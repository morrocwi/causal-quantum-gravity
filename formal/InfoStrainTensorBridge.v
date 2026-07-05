(* ===================================================================== *)
(*  RDL_StrainTensorBridge.v  (repo namespace: rename Info* mechanically) *)
(*  WELDING TWO OF THE FOUR NAMED GAPS.                                   *)
(*                                                                        *)
(*  GAP 1 (retention/curvature <-> tensor), CLOSED AT Th LEVEL:           *)
(*  the strain functional of the retention balance                        *)
(*  (RDL_ActionStationarity.v), evaluated on the edges of a unit cell     *)
(*  WITH its diagonal candidate, IS the frame-evaluation data of the      *)
(*  gradient two-tensor Tg(i,j) = g_i g_j of RDL_TensorFrame.v —          *)
(*  exactly for cell-affine fields, and with an EXACT defect identity     *)
(*  (the discrete cross second difference X) in general.  Hence the       *)
(*  balance law does not merely coexist with the tensor frame:            *)
(*  retaining the diagonal edge literally PRICES a tensor evaluation,     *)
(*  and the polarization key recovers the off-diagonal component from     *)
(*  three edge strains.                                                   *)
(*                                                                        *)
(*  GAP 3 (dynamics <-> Clausius), FIRST MECHANIZED CONTENT:              *)
(*  (i) the screen partition: the quadratic form of any graph splits      *)
(*  EXACTLY into inside + outside + cut against any region — the cut      *)
(*  is the only channel between a region and its complement (the          *)
(*  native local screen); (ii) with the single disclosed lens             *)
(*  ansatz-T (benefit per retained distinction := Temp * s0), the         *)
(*  retention balance becomes an iff THEOREM of the Clausius form         *)
(*      delta E  <=  Temp * (s0 * delta Scount)                           *)
(*  where Scount is the retained-distinction count.                       *)
(*                                                                        *)
(*  HONESTLY NOT CLAIMED (the remaining two gaps, by name):               *)
(*  GAP 2 — that the mother dynamics evolves the reconstructed tensor     *)
(*  by a field equation;  GAP 4 — OB-FORMAN-RICCI.  Nothing here          *)
(*  touches either.                                                       *)
(*                                                                        *)
(*  Pre-verified symbolically (all five cell identities, both iff         *)
(*  directions, all four indicator cases) before authoring.               *)
(*  Expected: Print Assumptions => Closed under the global context.       *)
(* ===================================================================== *)

Require Coq.Arith.PeanoNat.
Require Coq.Lists.List.
Require Coq.QArith.QArith.
Require Coq.micromega.Lqa.

Module StrainTensorBridge.

Import Coq.Lists.List. Import ListNotations.
Import Coq.Arith.PeanoNat.
Import Coq.QArith.QArith.
Import Coq.micromega.Lqa.
Local Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(* Shared data (self-contained)                                        *)
(* ------------------------------------------------------------------ *)

Definition Edge : Type := (nat * nat)%type.

Definition esum (E : list Edge) (g : Edge -> Q) : Q :=
  fold_right (fun e acc => g e + acc) 0 E.

Definition ediff (x : nat -> Q) (e : Edge) : Q := x (fst e) - x (snd e).

Definition gform (E : list Edge) (x : nat -> Q) : Q :=
  esum E (fun e => ediff x e * ediff x e).

Definition ind (u i : nat) : Q := if Nat.eqb u i then 1 else 0.

Fixpoint qsum (n : nat) (f : nat -> Q) : Q :=
  match n with
  | O => 0
  | S m => qsum m f + f m
  end.

Definition qform (n : nat) (T : nat -> nat -> Q) (v : nat -> Q) : Q :=
  qsum n (fun i => qsum n (fun j => v i * T i j * v j)).

Definition Sgeo (E : list Edge) (m : nat -> Q) (b : Edge -> Q)
                (h K : Q) : Q :=
  (h * h * K) * gform E m - esum E b.

(* ------------------------------------------------------------------ *)
(* Toolbox                                                             *)
(* ------------------------------------------------------------------ *)

Lemma esum_ext : forall E (f g : Edge -> Q),
  (forall e, In e E -> f e == g e) ->
  esum E f == esum E g.
Proof.
  induction E as [| e r IH]; intros f g H; simpl.
  - reflexivity.
  - rewrite (H e); [| left; reflexivity].
    rewrite (IH f g); [reflexivity | intros e' He'; apply H; right; exact He'].
Qed.

Lemma esum_plus : forall E (f g : Edge -> Q),
  esum E (fun e => f e + g e) == esum E f + esum E g.
Proof.
  induction E as [| e r IH]; intros f g; simpl; [ring | rewrite IH; ring].
Qed.

(* ------------------------------------------------------------------ *)
(* PART I — GAP 1: cell strains ARE tensor frame evaluations           *)
(* Cell corners: 0 = (0,0), 1 = (1,0), 2 = (0,1), 3 = (1,1).           *)
(* ------------------------------------------------------------------ *)

Definition ea1 : Edge := (0%nat, 1%nat).
Definition ea2 : Edge := (0%nat, 2%nat).
Definition edg : Edge := (0%nat, 3%nat).

(* the discrete gradient at corner 0 and its rank-one two-tensor *)
Definition grad (u : nat -> Q) (k : nat) : Q :=
  match k with
  | O => u 1%nat - u 0%nat
  | S O => u 2%nat - u 0%nat
  | _ => 0
  end.

Definition Tg (u : nat -> Q) (i j : nat) : Q := grad u i * grad u j.

(* the axis strains read the diagonal tensor components *)
Theorem axis1_strain_reads : forall u : nat -> Q,
  ediff u ea1 * ediff u ea1 == qform 2 (Tg u) (fun k => ind 0 k).
Proof.
  intro u. unfold ediff, ea1, qform, Tg, grad, ind. simpl. ring.
Qed.

Theorem axis2_strain_reads : forall u : nat -> Q,
  ediff u ea2 * ediff u ea2 == qform 2 (Tg u) (fun k => ind 1 k).
Proof.
  intro u. unfold ediff, ea2, qform, Tg, grad, ind. simpl. ring.
Qed.

(* on a cell-affine field (vanishing cross second difference) the       *)
(* diagonal strain reads the pair evaluation exactly                    *)
Theorem diag_strain_affine : forall u : nat -> Q,
  u 3%nat - u 1%nat - u 2%nat + u 0%nat == 0 ->
  ediff u edg * ediff u edg
  == qform 2 (Tg u) (fun k => ind 0 k + ind 1 k).
Proof.
  intros u HX.
  assert (Hu3 : u 3%nat == u 1%nat + u 2%nat - u 0%nat) by lra.
  unfold ediff, edg, qform, Tg, grad, ind. simpl.
  rewrite Hu3. ring.
Qed.

(* ... and in general the defect is EXACTLY the cross second            *)
(* difference term: nothing is hidden                                   *)
Theorem diag_strain_defect : forall u : nat -> Q,
  ediff u edg * ediff u edg
  == qform 2 (Tg u) (fun k => ind 0 k + ind 1 k)
     + (u 3%nat - u 1%nat - u 2%nat + u 0%nat)
       * (2 * ((u 1%nat - u 0%nat) + (u 2%nat - u 0%nat))
          + (u 3%nat - u 1%nat - u 2%nat + u 0%nat)).
Proof.
  intro u. unfold ediff, edg, qform, Tg, grad, ind. simpl. ring.
Qed.

(* the polarization key in strain form: the off-diagonal component      *)
(* is recovered from three edge strains                                 *)
Theorem offdiag_from_strains : forall u : nat -> Q,
  u 3%nat - u 1%nat - u 2%nat + u 0%nat == 0 ->
  2 * ((u 1%nat - u 0%nat) * (u 2%nat - u 0%nat))
  == ediff u edg * ediff u edg
     - ediff u ea1 * ediff u ea1
     - ediff u ea2 * ediff u ea2.
Proof.
  intros u HX.
  assert (Hu3 : u 3%nat == u 1%nat + u 2%nat - u 0%nat) by lra.
  unfold ediff, edg, ea1, ea2. simpl.
  rewrite Hu3. ring.
Qed.

(* local re-proof of the exact edge variation and the balance iff *)
Theorem addition_variation :
  forall E (m : nat -> Q) (b : Edge -> Q) (h K : Q) (estar : Edge),
  Sgeo (estar :: E) m b h K - Sgeo E m b h K
  == (h * h * K) * (ediff m estar * ediff m estar) - b estar.
Proof.
  intros E m b h K estar. unfold Sgeo, gform. simpl. ring.
Qed.

Theorem retention_balance_add :
  forall E (m : nat -> Q) (b : Edge -> Q) (h K : Q) (estar : Edge),
  Sgeo E m b h K <= Sgeo (estar :: E) m b h K
  <-> b estar <= (h * h * K) * (ediff m estar * ediff m estar).
Proof.
  intros E m b h K estar.
  assert (Hv := addition_variation E m b h K estar).
  split; intro H; lra.
Qed.

(* THE WELD: the retention balance for the diagonal candidate is,       *)
(* verbatim, a price on a tensor frame evaluation                       *)
Theorem diagonal_retention_prices_tensor :
  forall E (u : nat -> Q) (b : Edge -> Q) (h K : Q),
  u 3%nat - u 1%nat - u 2%nat + u 0%nat == 0 ->
  (Sgeo E u b h K <= Sgeo (edg :: E) u b h K
   <-> b edg <= (h * h * K)
                * qform 2 (Tg u) (fun k => ind 0 k + ind 1 k)).
Proof.
  intros E u b h K HX.
  assert (Hs := diag_strain_affine u HX).
  assert (HhK : (h * h * K) * (ediff u edg * ediff u edg)
              == (h * h * K)
                 * qform 2 (Tg u) (fun k => ind 0 k + ind 1 k))
    by (rewrite Hs; reflexivity).
  assert (Hb := retention_balance_add E u b h K edg).
  split; intro H.
  - apply Hb in H. lra.
  - apply Hb. lra.
Qed.

(* ------------------------------------------------------------------ *)
(* PART II — GAP 3: the native screen and the Clausius form             *)
(* ------------------------------------------------------------------ *)

Definition inb (reg : nat -> bool) (e : Edge) : Q :=
  (if reg (fst e) then 1 else 0) * (if reg (snd e) then 1 else 0).

Definition outb (reg : nat -> bool) (e : Edge) : Q :=
  (if reg (fst e) then 0 else 1) * (if reg (snd e) then 0 else 1).

Definition cutb (reg : nat -> bool) (e : Edge) : Q :=
  (if reg (fst e) then 1 else 0) * (if reg (snd e) then 0 else 1)
  + (if reg (fst e) then 0 else 1) * (if reg (snd e) then 1 else 0).

Lemma indicator_partition : forall (reg : nat -> bool) (e : Edge),
  inb reg e + outb reg e + cutb reg e == 1.
Proof.
  intros reg e. unfold inb, outb, cutb.
  destruct (reg (fst e)); destruct (reg (snd e)); ring.
Qed.

(* the quadratic form of ANY graph splits exactly into inside +         *)
(* outside + cut against ANY region: the cut is the only channel        *)
Theorem gform_screen_partition :
  forall E (reg : nat -> bool) (x : nat -> Q),
  gform E x
  == esum E (fun e => inb reg e * (ediff x e * ediff x e))
     + esum E (fun e => outb reg e * (ediff x e * ediff x e))
     + esum E (fun e => cutb reg e * (ediff x e * ediff x e)).
Proof.
  intros E reg x. unfold gform.
  rewrite (esum_ext E
    (fun e => ediff x e * ediff x e)
    (fun e => inb reg e * (ediff x e * ediff x e)
              + (outb reg e * (ediff x e * ediff x e)
                 + cutb reg e * (ediff x e * ediff x e)))).
  - rewrite (esum_plus E
      (fun e => inb reg e * (ediff x e * ediff x e))
      (fun e => outb reg e * (ediff x e * ediff x e)
                + cutb reg e * (ediff x e * ediff x e))).
    rewrite (esum_plus E
      (fun e => outb reg e * (ediff x e * ediff x e))
      (fun e => cutb reg e * (ediff x e * ediff x e))).
    lra.
  - intros e _.
    assert (Hp := indicator_partition reg e).
    assert (H1 : (inb reg e + outb reg e + cutb reg e)
                   * (ediff x e * ediff x e)
                 == 1 * (ediff x e * ediff x e))
      by (rewrite Hp; reflexivity).
    lra.
Qed.

(* the retained-distinction count *)
Definition Scount (E : list Edge) : Q := esum E (fun _ => 1).

Theorem entropy_step : forall E (e : Edge),
  Scount (e :: E) == Scount E + 1.
Proof.
  intros E e. unfold Scount. simpl. ring.
Qed.

(* THE CLAUSIUS FORM: with the single disclosed lens                    *)
(*   benefit per retained distinction := Temp * s0        (ansatz-T)    *)
(* the retention balance IS  delta E <= Temp * (s0 * delta Scount),     *)
(* both directions exact                                                *)
Theorem clausius_form :
  forall E (x : nat -> Q) (h K Temp s0 : Q) (e : Edge),
  Sgeo (e :: E) x (fun _ => Temp * s0) h K
    <= Sgeo E x (fun _ => Temp * s0) h K
  <-> (h * h * K) * (ediff x e * ediff x e)
      <= Temp * (s0 * (Scount (e :: E) - Scount E)).
Proof.
  intros E x h K Temp s0 e.
  assert (Hv := addition_variation E x (fun _ => Temp * s0) h K e).
  cbv beta in Hv.
  assert (Hs := entropy_step E e).
  assert (HR : Temp * (s0 * (Scount (e :: E) - Scount E)) == Temp * s0)
    by (rewrite Hs; ring).
  split; intro H; lra.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions axis1_strain_reads.
Print Assumptions axis2_strain_reads.
Print Assumptions diag_strain_affine.
Print Assumptions diag_strain_defect.
Print Assumptions offdiag_from_strains.
Print Assumptions addition_variation.
Print Assumptions retention_balance_add.
Print Assumptions diagonal_retention_prices_tensor.
Print Assumptions indicator_partition.
Print Assumptions gform_screen_partition.
Print Assumptions entropy_step.
Print Assumptions clausius_form.

End StrainTensorBridge.
