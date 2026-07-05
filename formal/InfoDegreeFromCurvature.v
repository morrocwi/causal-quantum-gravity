(* ===================================================================
   InfoDegreeFromCurvature_attempt.v

   The requested Th_coqc lemma: a node's degree is bounded by the
   local Forman curvature of any edge incident to it, and (given a
   global curvature floor) the graph's maximum degree is bounded by
   4 minus that floor -- feeding InfoSpectralCeiling_attempt.v's
   (C41) dmax hypothesis with a curvature-derived value instead of an
   independent assumption.

   THIS FILE DOES NOT CLAIM, PROVE, OR DEPEND ON: Jacobson's 1995
   thermodynamic derivation of Einstein's equation, the Clausius
   relation, the Bekenstein-Hawking area law, a holographic screen, a
   cosmological constant, or Newton's constant. It proves one small,
   purely combinatorial fact about Forman curvature (already defined
   in InfoDiscreteGraphCurvature_attempt.v / InfoGraphGrowth_attempt.v)
   and composes it with C41's own hypothesis shape. Any interpretation
   connecting this bound to mass, holography, or general relativity is
   Dr-tier and lives in prose elsewhere (CARD_SEED_CURVATURE_MASS_
   ANSATZ.md and related discussion), not in this file.

   TIER: Tier-0, Q-only, axiom-free (lra).
   =================================================================== *)

Require Coq.Lists.List.
Require Coq.QArith.QArith.
Require Coq.micromega.Lqa.

Import Coq.Lists.List.
Import Coq.QArith.QArith.
Import Coq.micromega.Lqa.
Open Scope Q_scope.

Module DegreeFromCurvature.

Definition Edge : Type := (nat * nat)%type.

Definition esum (E : list Edge) (g : Edge -> Q) : Q :=
  fold_right (fun e acc => g e + acc) 0 E.

Definition share (e : Edge) (i : nat) : Q :=
  (if Nat.eqb (fst e) i then 1 else 0) + (if Nat.eqb (snd e) i then 1 else 0).

Definition deg (E : list Edge) (i : nat) : Q := esum E (fun e => share e i).

Definition forman (E : list Edge) (e : Edge) : Q :=
  4 - deg E (fst e) - deg E (snd e).

Lemma share_nonneg : forall e i, 0 <= share e i.
Proof.
  intros e i. unfold share.
  destruct (Nat.eqb (fst e) i); destruct (Nat.eqb (snd e) i); lra.
Qed.

Lemma esum_nonneg : forall E (g : Edge -> Q),
  (forall e, In e E -> 0 <= g e) -> 0 <= esum E g.
Proof.
  induction E as [| e r IH]; intros g H; simpl.
  - lra.
  - assert (H1 := H e (or_introl eq_refl)).
    assert (H2 := IH g (fun e' He' => H e' (or_intror He'))).
    lra.
Qed.

Lemma deg_nonneg : forall E i, 0 <= deg E i.
Proof.
  intros E i. unfold deg. apply esum_nonneg. intros e _. apply share_nonneg.
Qed.

(* ------------------------------------------------------------------ *)
(*  THE LOCAL BOUND: each endpoint of an edge has degree at most       *)
(*  4 minus that edge's own Forman curvature (using the OTHER          *)
(*  endpoint's degree being nonnegative). Exact, unconditional.        *)
(* ------------------------------------------------------------------ *)

Theorem deg_bound_by_local_curvature :
  forall (E : list Edge) (e : Edge),
  deg E (fst e) <= 4 - forman E e /\ deg E (snd e) <= 4 - forman E e.
Proof.
  intros E e. unfold forman.
  assert (Hu := deg_nonneg E (fst e)).
  assert (Hv := deg_nonneg E (snd e)).
  split; lra.
Qed.

(* ------------------------------------------------------------------ *)
(*  THE GLOBAL BOUND: given a curvature floor Fmin holding on every    *)
(*  edge of E, any node incident to at least one edge of E has degree  *)
(*  at most 4 - Fmin. This is exactly the "dmax <= 4 - Fmin" bound,    *)
(*  stated so it can feed InfoSpectralCeiling_attempt.v's (C41) own    *)
(*  "forall i, deg E i <= dmax" hypothesis with dmax := 4 - Fmin.      *)
(* ------------------------------------------------------------------ *)

Theorem deg_bound_by_curvature_floor :
  forall (E : list Edge) (Fmin : Q),
  (forall e, In e E -> Fmin <= forman E e) ->
  forall (i : nat) (e : Edge), In e E -> (fst e = i \/ snd e = i) ->
  deg E i <= 4 - Fmin.
Proof.
  intros E Fmin Hfloor i e Hin Hi.
  assert (Hlocal := deg_bound_by_local_curvature E e).
  assert (Hf := Hfloor e Hin).
  destruct Hi as [Hi | Hi]; subst.
  - destruct Hlocal as [H1 _]. lra.
  - destruct Hlocal as [_ H2]. lra.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions share_nonneg.
Print Assumptions deg_nonneg.
Print Assumptions deg_bound_by_local_curvature.
Print Assumptions deg_bound_by_curvature_floor.

End DegreeFromCurvature.
