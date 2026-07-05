(* ===================================================================== *)
(*  InfoBoundaryScreening_attempt.v                                       *)
(*                                                                        *)
(*  Reuses InfoStrainTensorBridge_attempt.v's gform_screen_partition      *)
(*  (the quadratic form of any graph splits EXACTLY into inside + outside *)
(*  + cut against any region reg : nat -> bool) to prove a screening      *)
(*  fact: the "outside + cut" part of the form -- called Exterior here -- *)
(*  depends on a field x ONLY through its values at nodes that are not    *)
(*  in the *strict interior* of the region (interior = in the region AND *)
(*  every edge of E touching that node stays inside the region).          *)
(*                                                                        *)
(*  Mechanism (verified against gform_screen_partition's own edge         *)
(*  classification, not assumed): inb/outb/cutb are 0/1 indicators with   *)
(*  inb e + outb e + cutb e == 1 for every edge (indicator_partition), and *)
(*  for a fixed edge e = (u,v) exactly one of the three is 1, matching     *)
(*  which of reg u, reg v is true/false.  So "not a fully-inside edge"    *)
(*  (inb e = 0) means at least one of u, v is *outside* the region.  Any   *)
(*  node that is an endpoint of such an edge automatically fails the      *)
(*  strict-interior test above (that very edge witnesses a boundary       *)
(*  crossing at that node, whichever side it sits on).  Hence BOTH        *)
(*  endpoints of every edge counted in Exterior are non-interior nodes,   *)
(*  and agreement of x, y off the strict interior forces edge-by-edge     *)
(*  agreement of the summand, hence of the whole sum -- EXACTLY, no       *)
(*  extra hypothesis needed.                                              *)
(*                                                                        *)
(*  Expected: Print Assumptions => Closed under the global context.       *)
(*                                                                        *)
(*  CITATION YEARS: this file cites no named physical equation or dated  *)
(*  result -- it is pure graph algebra over gform_screen_partition        *)
(*  (already present in InfoStrainTensorBridge_attempt.v). The words      *)
(*  "boundary"/"screen"/"Exterior"/"capacity" here are graph-native names *)
(*  chosen for readability; they are NOT a claim about holography, the    *)
(*  Bekenstein-Hawking area law (Bekenstein 1973), or 't Hooft/Susskind    *)
(*  holographic screens ('t Hooft 1993; Susskind 1995) -- no theorem      *)
(*  below is checked against, or depends on, any of that physics.         *)
(* ===================================================================== *)

Require InfoStrainTensorBridge.
Require Coq.Lists.List.
Require Coq.QArith.QArith.
Require Coq.micromega.Lqa.

Module InfoBoundaryScreening.

Import Coq.Lists.List. Import ListNotations.
Import Coq.QArith.QArith.
Import Coq.micromega.Lqa.
Import InfoStrainTensorBridge.StrainTensorBridge.
Local Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(* 1. Exterior: reuse the outside+cut term of gform_screen_partition   *)
(*    verbatim (same two summands, same order) -- not redefined.       *)
(* ------------------------------------------------------------------ *)

Definition Exterior (E : list Edge) (reg : nat -> bool) (x : nat -> Q) : Q :=
  esum E (fun e => outb reg e * (ediff x e * ediff x e))
  + esum E (fun e => cutb reg e * (ediff x e * ediff x e)).

(* Sanity: Exterior really is "the rest" of gform_screen_partition once  *)
(* the inside term is removed -- immediate from that theorem.           *)
Lemma exterior_is_gform_minus_inside :
  forall E (reg : nat -> bool) (x : nat -> Q),
  gform E x
  == esum E (fun e => inb reg e * (ediff x e * ediff x e)) + Exterior E reg x.
Proof.
  intros E reg x. unfold Exterior.
  rewrite (gform_screen_partition E reg x). lra.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. Strict interior of a region, relative to a fixed edge list E:     *)
(*    a node i is interior iff reg i = true and every E-edge touching   *)
(*    i has BOTH endpoints inside reg (so no edge at i is outb/cutb).   *)
(* ------------------------------------------------------------------ *)

Definition TouchesEdge (e : Edge) (i : nat) : Prop :=
  fst e = i \/ snd e = i.

Definition Interior (E : list Edge) (reg : nat -> bool) (i : nat) : Prop :=
  reg i = true
  /\ (forall e, In e E -> TouchesEdge e i -> reg (fst e) = true /\ reg (snd e) = true).

(* ------------------------------------------------------------------ *)
(* 3. Toolbox: pin down exactly which edges carry outb/cutb weight.     *)
(* ------------------------------------------------------------------ *)

(* An edge is a "screening edge" (outb+cutb nonzero, i.e. not fully      *)
(* inside) exactly when it is not the case that both endpoints are in   *)
(* the region.                                                          *)
Lemma screening_edge_iff : forall (reg : nat -> bool) (e : Edge),
  outb reg e + cutb reg e == 0 <-> (reg (fst e) = true /\ reg (snd e) = true).
Proof.
  intros reg e. unfold outb, cutb.
  destruct (reg (fst e)) eqn:Hu; destruct (reg (snd e)) eqn:Hv; simpl; split;
    intro H; try (split; reflexivity); try lra; try discriminate.
Qed.

(* Both endpoints of a screening edge are non-interior: whichever        *)
(* endpoint is examined, this very edge is a witness against Interior.  *)
Lemma screening_edge_endpoints_not_interior :
  forall E (reg : nat -> bool) (e : Edge),
  In e E ->
  ~ (reg (fst e) = true /\ reg (snd e) = true) ->
  ~ Interior E reg (fst e) /\ ~ Interior E reg (snd e).
Proof.
  intros E reg e Hin Hnot.
  split; intros [_ Hint].
  - apply Hnot. apply (Hint e Hin). left; reflexivity.
  - apply Hnot. apply (Hint e Hin). right; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. THE THEOREM: Exterior is invisible to any change confined to the *)
(*    strict interior -- fields agreeing off the interior give the      *)
(*    exact same Exterior value.                                       *)
(* ------------------------------------------------------------------ *)

Theorem exterior_invisible_to_interior_swap :
  forall E (reg : nat -> bool) (x y : nat -> Q),
  (forall i, ~ Interior E reg i -> x i == y i) ->
  Exterior E reg x == Exterior E reg y.
Proof.
  intros E reg x y Hagree. unfold Exterior.
  assert (Ho : esum E (fun e => outb reg e * (ediff x e * ediff x e))
             == esum E (fun e => outb reg e * (ediff y e * ediff y e))).
  { apply esum_ext. intros e Hin.
    destruct (Qeq_dec (outb reg e + cutb reg e) 0) as [Hz | Hnz].
    - assert (Hboth : reg (fst e) = true /\ reg (snd e) = true).
      { apply (screening_edge_iff reg e). exact Hz. }
      unfold outb. rewrite (proj1 Hboth). rewrite (proj2 Hboth). ring.
    - assert (Hnb : ~ (reg (fst e) = true /\ reg (snd e) = true)).
      { intro Hb. apply Hnz. apply (screening_edge_iff reg e). exact Hb. }
      destruct (screening_edge_endpoints_not_interior E reg e Hin Hnb)
        as [Hnfst Hnsnd].
      assert (Hxf := Hagree (fst e) Hnfst).
      assert (Hxs := Hagree (snd e) Hnsnd).
      unfold ediff. rewrite Hxf, Hxs. reflexivity. }
  assert (Hc : esum E (fun e => cutb reg e * (ediff x e * ediff x e))
             == esum E (fun e => cutb reg e * (ediff y e * ediff y e))).
  { apply esum_ext. intros e Hin.
    destruct (Qeq_dec (outb reg e + cutb reg e) 0) as [Hz | Hnz].
    - assert (Hboth : reg (fst e) = true /\ reg (snd e) = true).
      { apply (screening_edge_iff reg e). exact Hz. }
      unfold cutb. rewrite (proj1 Hboth). rewrite (proj2 Hboth). ring.
    - assert (Hnb : ~ (reg (fst e) = true /\ reg (snd e) = true)).
      { intro Hb. apply Hnz. apply (screening_edge_iff reg e). exact Hb. }
      destruct (screening_edge_endpoints_not_interior E reg e Hin Hnb)
        as [Hnfst Hnsnd].
      assert (Hxf := Hagree (fst e) Hnfst).
      assert (Hxs := Hagree (snd e) Hnsnd).
      unfold ediff. rewrite Hxf, Hxs. reflexivity. }
  rewrite Ho, Hc. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 5. Capacity: number of cut edges, trivially field-independent.       *)
(*    Honesty note: this is NOT a deep corollary of the swap theorem --  *)
(*    capacity never mentions a field at all, so its independence from   *)
(*    field values is true by construction (esum with the constant      *)
(*    function 1 over a fixed weighting cutb reg, both fixed by E/reg    *)
(*    alone). Stated anyway, as asked, with an honest one-line proof.    *)
(* ------------------------------------------------------------------ *)

Definition capacity (E : list Edge) (reg : nat -> bool) : Q :=
  esum E (fun e => cutb reg e).

Corollary capacity_eq_boundary :
  forall E (reg : nat -> bool) (x y : nat -> Q),
  capacity E reg == capacity E reg.
Proof.
  intros E reg x y. reflexivity.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions exterior_is_gform_minus_inside.
Print Assumptions screening_edge_iff.
Print Assumptions screening_edge_endpoints_not_interior.
Print Assumptions exterior_invisible_to_interior_swap.
Print Assumptions capacity_eq_boundary.

End InfoBoundaryScreening.
