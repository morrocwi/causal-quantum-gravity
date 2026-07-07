(******************************************************************************)
(* InfoDissipationIsIndependent_attempt.v -- EXPLORATORY, single-attempt file. *)
(*   Standalone. Requires ONLY Coq.QArith + Coq.micromega.Lqa: no arc file,    *)
(*   no Reals, no axiom. Compile: coqc -q -R . RDL.                            *)
(*                                                                            *)
(* CONTEXT (master equation). The arc's master equation is                     *)
(*   M*d_tt Phi + D*d_t Phi - K*L_R*Phi + grad V(Phi) = J - eta.               *)
(* M is the 2nd-order (inertial) coefficient; D is the 1st-order (dissipative) *)
(* coefficient. This file gives a Q-exact, 2-node, discrete-time toy model     *)
(* that isolates what each coefficient DOES to a quadratic energy functional,  *)
(* to characterize D as a STRUCTURALLY INDEPENDENT ingredient (the arrow of    *)
(* time) rather than something derivable from M or from L_R.                   *)
(*                                                                            *)
(* THE TOY MODEL (a 2-node state x = (x1,x2) in Q^2, energy(x) = x1^2+x2^2):    *)
(*   step_M  : the M-branch, D=0.  A quarter-turn (x1,x2) |-> (-x2,x1).        *)
(*             This is an EXACT rational orthogonal ("rotation") map -- no      *)
(*             sqrt(2)/irrational entries needed, since cos(90deg)=0 and        *)
(*             sin(90deg)=1 are both already rational. It is invertible with    *)
(*             an explicit rational inverse (step_M_inv), so it is REVERSIBLE   *)
(*             as a map, on top of (separately) preserving energy exactly.      *)
(*   step_D  : the D-branch, D>0.  A contraction (x1,x2) |-> ((1/2)x1,(1/2)x2), *)
(*             standing for a discrete Euler step of D*d_t Phi with a rate       *)
(*             (here 1/2) strictly between 0 and 1 -- the concrete, rational      *)
(*             representative of "D>0".                                        *)
(*                                                                            *)
(* CLAIM (what the Coq actually PROVES, machine-checked over Q):               *)
(*   1. step_M_preserves_energy : for ALL x1,x2 in Q, energy(step_M x1 x2)      *)
(*      == energy(x1,x2) EXACTLY (a ring identity -- no inequality, no          *)
(*      approximation, no hypothesis needed). The M-branch alone has NO arrow.  *)
(*   2. step_M_reversible : step_M has an explicit two-sided rational inverse    *)
(*      step_M_inv, so the M-branch is invertible on top of being energy-        *)
(*      preserving -- reinforcing that M alone supplies no directionality.       *)
(*   3. step_D_strictly_decreases_energy : for ALL x1,x2 in Q with energy(x1,x2) *)
(*      strictly positive, energy(step_D x1 x2) < energy(x1,x2) STRICTLY (a      *)
(*      genuine Q-inequality, discharged by `lra` on the atom e := x1*x1+x2*x2,  *)
(*      after `ring`-reducing the contracted energy to (1/4)*e). The D-branch    *)
(*      alone strictly shrinks the energy functional every single step: THAT     *)
(*      monotone strict decrease is the machine-checked arrow.                   *)
(*   4. Two concrete Q witnesses (x1,x2) = (3,4): energy before is 25 exactly;    *)
(*      after step_M it is still 25 exactly (no arrow); after step_D it is        *)
(*      25/4 < 25 exactly (a strict, measured drop -- the arrow, in numbers).     *)
(*   5. dissipation_is_independent_arrow bundles 1 and 3 into one conjunction:    *)
(*      the M-branch preserves energy for all states AND the D-branch             *)
(*      strictly decreases energy for all positive-energy states -- proved        *)
(*      side by side from the SAME energy functional, with NO shared premise      *)
(*      linking D's behavior to M's structure or vice versa.                      *)
(*                                                                            *)
(* SCOPE / TIER HONESTY (a skeptic should read this):                          *)
(*   [Th_coqc]  Items 1-5 above are the Coq content: a ring identity (energy      *)
(*              conservation under step_M), an explicit inverse (reversibility    *)
(*              of step_M), a linear-after-ring-reduction strict inequality       *)
(*              (energy contraction under step_D), and their concrete numeric     *)
(*              instances. All of it is elementary algebra over Q -- exact,       *)
(*              finite, no continuum, no axiom.                                  *)
(*                                                                            *)
(*   [Dr]       The INTERPRETATION -- that this is why D, not M, supplies the     *)
(*              arrow of time, and that D is a STRUCTURALLY INDEPENDENT            *)
(*              ingredient, not a derived consequence of M or of L_R -- is Dr      *)
(*              (readout-not-truth), NOT itself a Coq theorem:                     *)
(*                - The toy model only has an M-slot and a D-slot; L_R (the       *)
(*                  graph Laplacian coupling term) does not appear in either       *)
(*                  step_M or step_D at all, so nothing here derives D FROM        *)
(*                  L_R either. The independence reading is a design fact          *)
(*                  about the toy, offered as the minimal witness of the           *)
(*                  general claim, not a proof that no larger construction         *)
(*                  could ever recover a D-like term from M and L_R combined.       *)
(*                - Irreversibility here is characterized purely via strict        *)
(*                  monotone decrease of the energy functional (a 2nd-law-style     *)
(*                  criterion), NOT via non-invertibility of step_D as a bare        *)
(*                  map: scalar multiplication by a nonzero rational (1/2) is        *)
(*                  in fact injective/invertible in Q. The arrow claimed is           *)
(*                  energy strictly falling every step and never coming back up        *)
(*                  under repeated application, not that the map cannot be           *)
(*                  undone in principle. This project does not overclaim the           *)
(*                  stronger (non-invertibility) reading here.                         *)
(*                - Reading energy as a stand-in for a Landauer-style dissipated        *)
(*                  quantity, and M-has-an-inverse-but-D's-energy-decrease-             *)
(*                  compounds-under-iteration as physical time's arrow, is Dr           *)
(*                  narrative, not proved by the two isolated single-step Q             *)
(*                  facts above.                                                        *)
(******************************************************************************)

Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.

Open Scope Q_scope.

(* -------------------------------------------------------------------- *)
(* The quadratic energy functional on a 2-node state.                    *)
(* -------------------------------------------------------------------- *)

Definition energy (x1 x2 : Q) : Q := x1*x1 + x2*x2.

(* -------------------------------------------------------------------- *)
(* The M-branch (D=0): an exact rational quarter-turn "rotation".         *)
(* cos(90deg)=0, sin(90deg)=1 are both already rational, so no sqrt(2)     *)
(* or any irrational is needed for this orthogonal step.                  *)
(* -------------------------------------------------------------------- *)

Definition step_M (x1 x2 : Q) : Q * Q := (-x2, x1).

Definition step_M_inv (y1 y2 : Q) : Q * Q := (y2, -y1).

(* -------------------------------------------------------------------- *)
(* The D-branch (D>0): a contraction with rate 1/2, the concrete           *)
(* rational representative of a discrete dissipative Euler step.           *)
(* -------------------------------------------------------------------- *)

Definition step_D (x1 x2 : Q) : Q * Q := ((1#2)*x1, (1#2)*x2).

(* ======================================================================= *)
(* [Th_coqc] 1. The M-branch preserves energy EXACTLY, for ALL states.      *)
(* ======================================================================= *)

Theorem step_M_preserves_energy :
  forall x1 x2 : Q,
    energy (fst (step_M x1 x2)) (snd (step_M x1 x2)) == energy x1 x2.
Proof.
  intros x1 x2. unfold step_M, energy. simpl. ring.
Qed.

(* ======================================================================= *)
(* [Th_coqc] 2. The M-branch is REVERSIBLE: step_M_inv is an explicit        *)
(* two-sided rational inverse of step_M.                                     *)
(* ======================================================================= *)

Theorem step_M_reversible :
  forall x1 x2 : Q,
    fst (step_M_inv (fst (step_M x1 x2)) (snd (step_M x1 x2))) == x1
    /\
    snd (step_M_inv (fst (step_M x1 x2)) (snd (step_M x1 x2))) == x2.
Proof.
  intros x1 x2. unfold step_M, step_M_inv. simpl. split; ring.
Qed.

(* ======================================================================= *)
(* [Th_coqc] 3. The D-branch STRICTLY DECREASES energy, for every state      *)
(* with strictly positive energy.                                            *)
(* ======================================================================= *)

Theorem step_D_strictly_decreases_energy :
  forall x1 x2 : Q,
    0 < energy x1 x2 ->
    energy (fst (step_D x1 x2)) (snd (step_D x1 x2)) < energy x1 x2.
Proof.
  intros x1 x2 Hpos.
  unfold step_D, energy in *. simpl.
  assert (Hred :
    (1#2)*x1*((1#2)*x1) + (1#2)*x2*((1#2)*x2) == (1#4)*(x1*x1 + x2*x2))
    by ring.
  rewrite Hred.
  set (e := x1*x1 + x2*x2) in *.
  lra.
Qed.

(* ======================================================================= *)
(* [Th_coqc] 4. Concrete Q witnesses: (x1,x2) = (3,4), energy = 25 exactly.  *)
(*   - After step_M: still 25 exactly (no arrow: an equality).               *)
(*   - After step_D: 25/4 < 25 exactly (an arrow: a strict, measured drop).  *)
(* ======================================================================= *)

Example energy_before_witness : energy (3#1) (4#1) == 25#1.
Proof. unfold energy. reflexivity. Qed.

(* step_M sends (3,4) to (-4,3): the components carry over unreduced,          *)
(* so this one IS a literal (Leibniz) equality.                                *)
Example step_M_witness : step_M (3#1) (4#1) = (-(4#1), 3#1).
Proof. reflexivity. Qed.

Example energy_after_M_witness :
  energy (fst (step_M (3#1) (4#1))) (snd (step_M (3#1) (4#1))) == 25#1.
Proof. unfold step_M, energy. simpl. ring. Qed.

(* step_D sends (3,4) to (3/2,2); (1#2)*(4#1) reduces to 4#2, not the same      *)
(* raw pair as 2#1, so this is stated and proved as a setoid ("==") fact,       *)
(* not a literal ("=") one.                                                     *)
Example step_D_witness :
  fst (step_D (3#1) (4#1)) == 3#2 /\ snd (step_D (3#1) (4#1)) == 2#1.
Proof. unfold step_D. simpl. split; lra. Qed.

Example energy_after_D_witness :
  energy (fst (step_D (3#1) (4#1))) (snd (step_D (3#1) (4#1))) == 25#4.
Proof. unfold step_D, energy. simpl. lra. Qed.

Example energy_after_D_lt_before :
  energy (fst (step_D (3#1) (4#1))) (snd (step_D (3#1) (4#1)))
  < energy (3#1) (4#1).
Proof.
  rewrite energy_after_D_witness, energy_before_witness. lra.
Qed.

(* ======================================================================= *)
(* [Th_coqc] 5. Bundled statement: D is an ingredient INDEPENDENT of M --    *)
(* the M-branch preserves energy for ALL states (no arrow) and the D-branch  *)
(* strictly decreases energy for ALL positive-energy states (an arrow),      *)
(* proved side by side from the same energy functional with no premise        *)
(* relating one branch's behavior to the other's structure.                   *)
(* ======================================================================= *)

Theorem dissipation_is_independent_arrow :
  (forall x1 x2 : Q,
     energy (fst (step_M x1 x2)) (snd (step_M x1 x2)) == energy x1 x2)
  /\
  (forall x1 x2 : Q,
     0 < energy x1 x2 ->
     energy (fst (step_D x1 x2)) (snd (step_D x1 x2)) < energy x1 x2).
Proof.
  split.
  - exact step_M_preserves_energy.
  - exact step_D_strictly_decreases_energy.
Qed.

(* ------------------------------------------------------------------------- *)
(* NON-VACUOUS witness: the (3,4) state has strictly positive energy, so      *)
(* the strict-decrease theorem above is instantiated on a genuinely non-zero, *)
(* non-trivial state, not a vacuous statement about the zero vector.          *)
(* ------------------------------------------------------------------------- *)

Example dissipation_witness_nonzero_energy : 0 < energy (3#1) (4#1).
Proof. rewrite energy_before_witness. lra. Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions step_M_preserves_energy.
Print Assumptions step_M_reversible.
Print Assumptions step_D_strictly_decreases_energy.
Print Assumptions energy_before_witness.
Print Assumptions step_M_witness.
Print Assumptions energy_after_M_witness.
Print Assumptions step_D_witness.
Print Assumptions energy_after_D_witness.
Print Assumptions energy_after_D_lt_before.
Print Assumptions dissipation_is_independent_arrow.
Print Assumptions dissipation_witness_nonzero_energy.
