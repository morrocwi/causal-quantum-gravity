(* ===================================================================
   InfoDiskBeforeLock_attempt.v

   A discrete, graph-native analog of "Axiom 11 -- Disk Before Mass"
   (Y. Lahtee, Zenodo 17599562). That document is a CONTINUUM PDE
   result stated with a provenance map but not a worked derivation
   (Dr tier there, not machine-checked) -- this file does not import,
   restate, or depend on it in any way. It builds, from scratch, a
   genuinely discrete analog of the SAME qualitative claim -- that
   anisotropic growth produces geometric flattening strictly before
   (or independent of) the whole system's growth halting -- using only
   this repository's own already-proven retention machinery
   (addition_variation, from InfoActionStationarity_attempt.v,
   reproduced standalone here per this repo's convention).

   THE ANALOGY, stated precisely (read before citing this file):
     - a partition of edges into "perp" (vertical / height-controlling)
       and "par" (in-plane / radius-controlling) classes
     - "mass-locking" (Axiom 11's E7)  <->  a class's growth
       permanently excluded (the seed's own retention criterion
       rejects it, from ANY current graph state, unconditionally)
     - "disk state" (Axiom 11's E6, H/R <= eta)  <->  perp edges are
       excluded while par edges are admitted, so the height-controlling
       count never grows while the radius-controlling count can

   THE RESULT: under an explicit ANISOTROPY HYPOTHESIS (perp-classified
   candidates always have benefit strictly below their strain; par-
   classified candidates always have benefit at least their strain --
   an assumption about input data, not derived from anything else),
   a perp candidate strictly worsens the retention functional while a
   par candidate does not, FROM THE SAME CURRENT GRAPH STATE,
   unconditionally and independent of growth history (Th_coqc,
   ring/lra-level; no continuum, no PDE, no stochastic analysis, no
   Section/Hypothesis -- explicit ∀-premises throughout).

   HONESTY: the anisotropy hypothesis (which edges are labeled "perp"
   vs "par", and that their benefits are skewed as assumed) is an
   INPUT to this file, not something it derives -- exactly like
   InfoCurvatureBalance's own curvature-affine ansatz. This file proves
   what follows FROM that assumption; it does not derive anisotropy
   itself from the mother equation, and it does not claim to have
   proved anything about actual disk formation, cosmology, or physical
   mass. It is a modest, honest instance of "anisotropic retention
   responds immediately and simultaneously," not a limiting/asymptotic
   claim about many growth steps -- that extension (aggregating over a
   candidate list) is a natural, mechanical next step (a short
   induction) and is NOT attempted here.
   =================================================================== *)

Require Coq.Lists.List.
Require Coq.QArith.QArith.
Require Coq.micromega.Lqa.

Import Coq.Lists.List.
Import Coq.QArith.QArith.
Import Coq.micromega.Lqa.
Open Scope Q_scope.
Import ListNotations.

Module DiskBeforeLock.

Definition Edge : Type := (nat * nat)%type.

Definition esum (E : list Edge) (g : Edge -> Q) : Q :=
  fold_right (fun e acc => g e + acc) 0 E.

Definition ediff (x : nat -> Q) (e : Edge) : Q := x (fst e) - x (snd e).

Definition gform (E : list Edge) (x y : nat -> Q) : Q :=
  esum E (fun e => ediff x e * ediff y e).

(* ---- the seed: retention/strain-benefit machinery, reproduced      *)
(* verbatim from InfoActionStationarity_attempt.v so this file         *)
(* compiles standalone. ---- *)
Definition Sgeo (E : list Edge) (m : nat -> Q) (b : Edge -> Q)
                (h K : Q) : Q :=
  (h * h * K) * gform E m m - esum E b.

Theorem addition_variation :
  forall E (m : nat -> Q) (b : Edge -> Q) (h K : Q) (estar : Edge),
  Sgeo (estar :: E) m b h K - Sgeo E m b h K
  == (h * h * K) * (ediff m estar * ediff m estar) - b estar.
Proof.
  intros E m b h K estar.
  unfold Sgeo, gform. simpl. ring.
Qed.

(* ================================================================= *)
(*  THE ANISOTROPY HYPOTHESIS: a classification of edges into         *)
(*  "vertical" (perp) and "in-plane" (par), with skewed benefit vs    *)
(*  strain. This is INPUT DATA, not derived by this file.             *)
(* ================================================================= *)

Definition strain (m : nat -> Q) (h K : Q) (e : Edge) : Q :=
  (h * h * K) * (ediff m e * ediff m e).

Definition PerpStarved (is_perp : Edge -> bool) (m : nat -> Q) (b : Edge -> Q)
                        (h K : Q) (e : Edge) : Prop :=
  is_perp e = true -> b e < strain m h K e.

Definition ParFavored (is_perp : Edge -> bool) (m : nat -> Q) (b : Edge -> Q)
                       (h K : Q) (e : Edge) : Prop :=
  is_perp e = false -> strain m h K e <= b e.

(* A perp candidate STRICTLY worsens (increases) the retention         *)
(* functional wherever it is added -- excluded by the seed's own       *)
(* criterion, from ANY current graph state E, independent of history.  *)
Theorem perp_excluded :
  forall (is_perp : Edge -> bool) (m : nat -> Q) (b : Edge -> Q) (h K : Q)
         (E : list Edge) (e : Edge),
  PerpStarved is_perp m b h K e -> is_perp e = true ->
  Sgeo E m b h K < Sgeo (e :: E) m b h K.
Proof.
  intros is_perp m b h K E e Hstarved Hperp.
  assert (Hv := addition_variation E m b h K e).
  unfold PerpStarved in Hstarved. specialize (Hstarved Hperp).
  unfold strain in Hstarved. lra.
Qed.

(* A par candidate never worsens the retention functional -- always    *)
(* safe to admit, from ANY current graph state E. *)
Theorem par_admitted :
  forall (is_perp : Edge -> bool) (m : nat -> Q) (b : Edge -> Q) (h K : Q)
         (E : list Edge) (e : Edge),
  ParFavored is_perp m b h K e -> is_perp e = false ->
  Sgeo (e :: E) m b h K <= Sgeo E m b h K.
Proof.
  intros is_perp m b h K E e Hfav Hpar.
  assert (Hv := addition_variation E m b h K e).
  unfold ParFavored in Hfav. specialize (Hfav Hpar).
  unfold strain in Hfav. lra.
Qed.

(* ================================================================= *)
(*  THE MAIN THEOREM: disk-before-lock. From the SAME current graph    *)
(*  state, a perp candidate is excluded while a par candidate is       *)
(*  admitted -- the anisotropic response is immediate and              *)
(*  simultaneous, not something that only emerges after many growth    *)
(*  steps or requires any notion of elapsed time.                      *)
(* ================================================================= *)

Theorem disk_before_lock :
  forall (is_perp : Edge -> bool) (m : nat -> Q) (b : Edge -> Q) (h K : Q)
         (E : list Edge) (eperp epar : Edge),
  PerpStarved is_perp m b h K eperp -> is_perp eperp = true ->
  ParFavored  is_perp m b h K epar  -> is_perp epar  = false ->
  Sgeo (epar :: E) m b h K <= Sgeo E m b h K
  /\ Sgeo E m b h K < Sgeo (eperp :: E) m b h K.
Proof.
  intros is_perp m b h K E eperp epar Hstarved Hperp Hfav Hpar.
  split.
  - apply (par_admitted is_perp m b h K E epar Hfav Hpar).
  - apply (perp_excluded is_perp m b h K E eperp Hstarved Hperp).
Qed.

(* Corollary, stated for readability: the two candidates are never     *)
(* treated the same way -- the retained-safe threshold (Sgeo E itself) *)
(* strictly separates them. *)
Corollary anisotropy_gap :
  forall (is_perp : Edge -> bool) (m : nat -> Q) (b : Edge -> Q) (h K : Q)
         (E : list Edge) (eperp epar : Edge),
  PerpStarved is_perp m b h K eperp -> is_perp eperp = true ->
  ParFavored  is_perp m b h K epar  -> is_perp epar  = false ->
  Sgeo (epar :: E) m b h K < Sgeo (eperp :: E) m b h K.
Proof.
  intros is_perp m b h K E eperp epar Hstarved Hperp Hfav Hpar.
  destruct (disk_before_lock is_perp m b h K E eperp epar
              Hstarved Hperp Hfav Hpar) as [H1 H2].
  lra.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions addition_variation.
Print Assumptions perp_excluded.
Print Assumptions par_admitted.
Print Assumptions disk_before_lock.
Print Assumptions anisotropy_gap.

End DiskBeforeLock.
