(******************************************************************************)
(* InfoDiscreteLeibnizObstruction_attempt.v -- EXPLORATORY, single-attempt.     *)
(*   Requires InfoMetricCompatibleCurvature_attempt (REUSES V3/cross/Veq)        *)
(*   + Coq.QArith + Lqa. No Reals, no axiom. TIER = Th_coqc (Q-only).           *)
(*   Compile: coqc -q -R . RDL <this>.                                          *)
(*                                                                            *)
(* WHY THE NON-ABELIAN COVARIANT BIANCHI IS NOT A NAIVE DISCRETE READOUT --      *)
(* the discrete Leibniz DEFECT is exactly cross(dA, dB).                        *)
(*                                                                            *)
(* InfoDiscreteSecondBianchi closed the ABELIAN differential Bianchi dF = 0. The *)
(* non-abelian covariant Bianchi (dF + [A,F] = 0) would need the continuum        *)
(* Leibniz rule d[A,B] = [dA,B] + [A,dB]. On the lattice, FINITE differences do   *)
(* NOT satisfy Leibniz exactly: there is an exact, computable DEFECT. This file   *)
(* isolates it -- for the Lie bracket cross (so(3)),                             *)
(*   d(cross(A,B)) = cross(dA,B) + cross(A,dB) + cross(dA,dB),                    *)
(* so the Leibniz defect is exactly cross(dA,dB), a genuinely nonzero            *)
(* second-order term. Hence the NAIVE algebra-level discrete non-abelian Bianchi  *)
(* carries this defect and is NOT an exact identity; the EXACT non-abelian        *)
(* curvature identity must use the transport-corrected GROUP / holonomy form      *)
(* (product of plaquette-holonomies around a 3-cube = identity), which is the      *)
(* honest [Open]. This is the readout-not-truth signature: a continuum identity    *)
(* (Leibniz/Bianchi) is a non-readout at the discrete algebra level, and its       *)
(* exact discrete appearance is PREDICTED (the defect) rather than assumed away.  *)
(*                                                                            *)
(* A, B : lattice(1-D) -> V3 (so(3)-valued fields); forward difference dvec.     *)
(*                                                                            *)
(* WHAT IS PROVED (Th_coqc, axiom-free over Q; Compute-checked witness):        *)
(*   discrete_leibniz : d(cross(A,B)) == cross(dA,B) + cross(A,dB) + cross(dA,dB) *)
(*       -- the exact discrete product rule for the Lie bracket, with the extra   *)
(*       cross(dA,dB) term the continuum rule lacks.                             *)
(*   leibniz_defect_is_cross_dA_dB : the defect d(cross) - cross(dA,B) -          *)
(*       cross(A,dB) == cross(dA,dB) -- the obstruction, exact.                   *)
(*   defect_nonzero_witness : a concrete A,B with cross(dA,dB) <> 0 -- so the      *)
(*       defect genuinely breaks the naive Leibniz/Bianchi (not a vacuous zero).  *)
(*                                                                            *)
(* HONEST FENCE. CLOSED: the exact discrete Leibniz defect for the Lie bracket    *)
(* is cross(dA,dB), nonzero in general -- so the naive algebra-level discrete      *)
(* non-abelian covariant Bianchi FAILS by exactly this term (a clean obstruction/ *)
(* negative result). [Open], NOT smuggled: the EXACT non-abelian Bianchi via the   *)
(* transport-corrected group/holonomy form (cube-of-plaquettes = identity); this   *)
(* file explains WHY that form is necessary, it does not build it. The continuum   *)
(* Leibniz/Bianchi is a refused non-readout. All quantities plain Q; no Reals.    *)
(******************************************************************************)

Require InfoMetricCompatibleCurvature_attempt.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.

Module InfoDiscreteLeibnizObstruction.
Import InfoMetricCompatibleCurvature_attempt.InfoMetricCompatibleCurvature.
Open Scope Q_scope.

Definition vadd (u w : V3) : V3 :=
  mkV (v1 u + v1 w) (v2 u + v2 w) (v3 u + v3 w).
Definition vsub (u w : V3) : V3 :=
  mkV (v1 u - v1 w) (v2 u - v2 w) (v3 u - v3 w).

(* forward difference of a lattice field of vectors *)
Definition dvec (A : nat -> V3) (n : nat) : V3 := vsub (A (S n)) (A n).

(* ------------------------------------------------------------------ *)
(* (1) the EXACT discrete product rule for the Lie bracket:            *)
(*     d(cross(A,B)) = cross(dA,B) + cross(A,dB) + cross(dA,dB).        *)
(* ------------------------------------------------------------------ *)
Theorem discrete_leibniz :
  forall (A B : nat -> V3) (n : nat),
    Veq (vsub (cross (A (S n)) (B (S n))) (cross (A n) (B n)))
        (vadd (vadd (cross (dvec A n) (B n)) (cross (A n) (dvec B n)))
              (cross (dvec A n) (dvec B n))).
Proof.
  intros A B n. unfold Veq, vadd, vsub, dvec, cross; simpl.
  repeat split; ring.
Qed.

(* ------------------------------------------------------------------ *)
(* (2) the Leibniz DEFECT is exactly cross(dA, dB).                    *)
(* ------------------------------------------------------------------ *)
Theorem leibniz_defect_is_cross_dA_dB :
  forall (A B : nat -> V3) (n : nat),
    Veq (vsub (vsub (vsub (cross (A (S n)) (B (S n))) (cross (A n) (B n)))
                    (cross (dvec A n) (B n)))
              (cross (A n) (dvec B n)))
        (cross (dvec A n) (dvec B n)).
Proof.
  intros A B n. unfold Veq, vsub, dvec, cross; simpl.
  repeat split; ring.
Qed.

(* ------------------------------------------------------------------ *)
(* (3) NON-VACUOUS: a concrete defect that is nonzero.                 *)
(*     A: 0 -> e1, 1 -> e2 ; B: 0 -> 0, 1 -> e3.                        *)
(*     dA = e2 - e1, dB = e3 ; cross(dA, dB) has a nonzero component.   *)
(* ------------------------------------------------------------------ *)
Definition Aw (n : nat) : V3 := match n with O => mkV 1 0 0 | _ => mkV 0 1 0 end.
Definition Bw (n : nat) : V3 := match n with O => mkV 0 0 0 | _ => mkV 0 0 1 end.

Example defect_nonzero_witness :
  ~ Veq (cross (dvec Aw 0) (dvec Bw 0)) (mkV 0 0 0).
Proof.
  unfold Veq, dvec, vsub, cross, Aw, Bw; simpl.
  intros [H1 [H2 H3]]. (* v1 component: (0-0)*1 - ... let lra find the contradiction *)
  lra.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions discrete_leibniz.
Print Assumptions leibniz_defect_is_cross_dA_dB.

End InfoDiscreteLeibnizObstruction.
