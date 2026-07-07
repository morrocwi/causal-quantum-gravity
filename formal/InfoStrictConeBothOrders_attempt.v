(* ===================================================================== *)
(*  InfoStrictConeBothOrders_attempt.v                                    *)
(*  THE DECISIVE TEST: does finite discrete strict causality FORCE a       *)
(*  2nd-order (leapfrog / M-term) equation of motion, or is discrete        *)
(*  FIRST-ORDER already strict-finite-cone too -- so finitude alone does     *)
(*  NOT force M?                                                            *)
(*                                                                          *)
(*  Concrete carrier (exact, over Q, no reals): a 5-node PATH graph          *)
(*  0-1-2-3-4, unit edge weight, and the explicit rational graph              *)
(*  Laplacian matrix L_R = D_W - W (degree minus adjacency):                  *)
(*                                                                            *)
(*        [ 1 -1  0  0  0 ]                                                  *)
(*        [-1  2 -1  0  0 ]                                                  *)
(*    L_R= [ 0 -1  2 -1  0 ]                                                  *)
(*        [ 0  0 -1  2 -1 ]                                                  *)
(*        [ 0  0  0 -1  1 ]                                                  *)
(*                                                                            *)
(*  Every off-diagonal entry L_R i j with |i-j| >= 2 is exactly 0            *)
(*  (L_R_banded, proved below): the matrix has BANDWIDTH 1 by construction,   *)
(*  which is exactly why (I + dt*L_R)^n and every leapfrog iterate have        *)
(*  bandwidth <= n -- a step can only move influence to a node's immediate      *)
(*  graph-neighbors.                                                          *)
(*                                                                            *)
(*  CLAIMED HERE (Th_coqc, exact over Q, coqc 8.20.1 target):                  *)
(*    L_R_banded                    the matrix entries vanish beyond           *)
(*                                  graph-distance 1 (the bandwidth-1 fact)      *)
(*    euler1_dt14_Phi0_node2_zero   FIRST-ORDER forward-Euler, one step of        *)
(*                                  Phi1 = Phi0 + dt*(L_R Phi0), dt = 1/4,         *)
(*                                  from delta Phi0 = e_0: node 2 reads EXACTLY     *)
(*                                  0 (distance-2 not yet reached; strict cone)      *)
(*    euler1_dt14_Phi0_node1_nonzero  the cone genuinely reached distance 1:          *)
(*                                  node 1 (Phi0's only neighbor) is NONZERO           *)
(*                                  after that same one step (-1/4)                     *)
(*    euler1_two_steps_node2_nonzero  after a SECOND first-order Euler step,             *)
(*                                  node 2 becomes NONZERO (exactly 1/16):                *)
(*                                  bandwidth = step count, exactly as (I+dtL)^n           *)
(*                                  predicts                                                *)
(*    leapfrog_dt14_Phi0_node2_zero   SECOND-ORDER leapfrog, one step of                     *)
(*                                  Phi1 = 2*Phi0 - Phiprev + dt^2*(L_R Phi0),                 *)
(*                                  Phiprev = Phi0, dt = 1/4: node 2 is ALSO EXACTLY             *)
(*                                  0 after one step -- equally strict-finite-cone                *)
(*    both_orders_strict_cone_node2   the CORE CONJUNCTION: both the 1st- and                      *)
(*                                  2nd-order one-step updates leave node 2 at                       *)
(*                                  exactly 0 -- strict-causal-cone locality does                      *)
(*                                  NOT distinguish the two orders                                       *)
(*    heat_step_strictly_dissipates   what DOES distinguish them: the SAME linear                         *)
(*                                  map run in the physical heat/diffusion direction                        *)
(*                                  (dt = -1/4, i.e. dPhi/dt = -L_R Phi, since L_R is                          *)
(*                                  positive-semidefinite) STRICTLY DECREASES the                                *)
(*                                  quadratic energy sum_i Phi_i^2: 5/8 < 1                                        *)
(*    givens_energy_preserved       a conservative (orthogonal, a^2+b^2=1) step on                                  *)
(*                                  two coordinates leaves the total energy EXACTLY                                    *)
(*                                  fixed, for ANY 5-node reading                                                        *)
(*    conservative_step_preserves_energy  the concrete rational 3-4-5 Pythagorean                                         *)
(*                                  witness instance: energy is exactly the SAME                                            *)
(*                                  before and after (1 == 1)                                                                 *)
(*    dissipative_vs_conservative_node2   the closing conjunction: dissipation is                                              *)
(*                                  strict (<) while conservation is exact (==) --                                                *)
(*                                  the discriminator is CONSERVATION, not CONE.                                                    *)
(*                                                                                                                                     *)
(*  HONEST NOTE ON THE SIGN OF dt: the update rule used throughout is the                                                              *)
(*  LITERAL one, Phi1 = Phi0 + dt*(L_R applied to Phi0), for a single fixed                                                              *)
(*  operator L_R = D_W - W (positive-semidefinite, matching the header). The                                                              *)
(*  bandwidth/cone-locality facts (Part 1-3) hold for that formula at ANY                                                                    *)
(*  nonzero dt, including dt = +1/4 as used there -- locality is a property of                                                                *)
(*  the MATRIX's zero pattern, not of the sign of dt. The energy claim (Part 4)                                                                 *)
(*  is a different question (which TIME DIRECTION of the same linear step is                                                                     *)
(*  dissipative), so it honestly uses dt = -1/4 in the SAME literal formula --                                                                     *)
(*  this is exactly one forward-Euler step, time-step 1/4, of the PHYSICAL heat                                                                      *)
(*  equation dPhi/dt = -L_R Phi (decay toward the graph average, since -L_R is                                                                          *)
(*  negative-semidefinite). Running dt = +1/4 instead (as in Part 1) traverses the                                                                        *)
(*  SAME linear map in the anti-diffusive direction; it is used there ONLY to                                                                               *)
(*  witness locality, and is honestly NOT claimed dissipative -- Compute confirms                                                                             *)
(*  its energy actually grows (13/8 > 1), which is exactly the point: sign of dt                                                                                *)
(*  does not affect the cone, but does flip the arrow of time. This is documented,                                                                                *)
(*  not hidden.                                                                                                                                                    *)
(*                                                                                                                                                                     *)
(*  HONESTLY NOT CLAIMED (machine-proved): any statement about n-step iterated                                                                                        *)
(*  bandwidth for general n (only n=1 and n=2 are checked, concretely, on this                                                                                          *)
(*  5-node witness); any general theorem that ALL conservative discrete updates                                                                                          *)
(*  are orthogonal Givens rotations (only ONE concrete conservative instance is                                                                                            *)
(*  exhibited, deliberately disjoint machinery from the dissipative heat step,                                                                                              *)
(*  mirroring the existing InfoDistinctionConserved_attempt.v / InfoErasureArrowOfTime_attempt.v *)
(*  lens pair but reproved standalone here, no Require of either); that leapfrog's                                                                                            *)
(*  OWN true symplectic invariant (kinetic+Dirichlet energy of the 2nd-order wave                                                                                              *)
(*  equation, not plain sum-of-squares) is conserved -- only an UNRELATED orthogonal                                                                                             *)
(*  witness step is shown conservative, on purpose, to keep the conservation-not-                                                                                                 *)
(*  cone point independent of which order is being run; any real quantum-gravity,                                                                                                   *)
(*  Regge-Wheeler, or other physical claim.                                                                                                                                            *)
(*                                                                                                                                                                                        *)
(*  SCOPE:                                                                                                                                                                                *)
(*   [Th_coqc]  Both orders are strict-finite-cone on this concrete 5-node witness             *)
(*              (Parts 1-3); the first-order Euler step in the physical heat direction           *)
(*              strictly dissipates a quadratic energy while a concrete orthogonal step            *)
(*              exactly conserves it (Part 4). Exact over Q, axiom-free, no continuum,               *)
(*              no limit, no I1-I4 injected anywhere -- readout-not-truth throughout.                  *)
(*   [Dr, NOT machine-proved]  The reading that first-order INFINITE propagation speed                  *)
(*              is a property only of the CONTINUUM operator e^{tL} (an I2 non-readout:                   *)
(*              it needs an infinite Taylor sum / infinitesimal dt -> 0 limit); in the                      *)
(*              finite discrete readout that this file actually checks, finitude/strict-                     *)
(*              causality does NOT force second order at all -- BOTH orders are exactly                        *)
(*              as finite-cone as each other, one step at a time. What genuinely                                 *)
(*              distinguishes 1st from 2nd order is CONSERVATION / REVERSIBILITY (an                               *)
(*              orthogonal, energy-preserving step exists at either order in principle;                              *)
(*              a dissipative step exists at either order too -- M, inertia, is really                                 *)
(*              about which structure a given step has, not about which order forces a                                  *)
(*              finite cone). So the framework carries TWO independent roots: distinction                                  *)
(*              (delta_R, the graph/bandwidth structure) and conservation/inertia (M, an                                     *)
(*              orthogonality/reversibility property layered on TOP of whichever order is                                      *)
(*              chosen) -- not one root forcing the other. This reading is Dr: a human                                           *)
(*              narrative built on the Th_coqc facts above, not itself machine-checked.                                            *)
(* ===================================================================== *)

Require Coq.QArith.QArith.
Require Coq.micromega.Lqa.
Require Coq.micromega.Lia.

Module StrictConeBothOrders.

Import Coq.QArith.QArith.
Import Coq.micromega.Lqa.
Import Coq.micromega.Lia.
Local Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(* THE EXPLICIT RATIONAL MATRIX: L_R = D_W - W on the path 0-1-2-3-4,     *)
(* unit edge weight. Total on all of nat*nat; every pair NOT one of the    *)
(* 13 diagonal/adjacent entries below is definitionally 0 -- this IS the    *)
(* bandwidth-1 property, built directly into the definition.                 *)
(* ------------------------------------------------------------------ *)

Definition L_R (i j : nat) : Q :=
  match i, j with
  | 0%nat, 0%nat => 1
  | 0%nat, 1%nat => -1
  | 1%nat, 0%nat => -1
  | 1%nat, 1%nat => 2
  | 1%nat, 2%nat => -1
  | 2%nat, 1%nat => -1
  | 2%nat, 2%nat => 2
  | 2%nat, 3%nat => -1
  | 3%nat, 2%nat => -1
  | 3%nat, 3%nat => 2
  | 3%nat, 4%nat => -1
  | 4%nat, 3%nat => -1
  | 4%nat, 4%nat => 1
  | _, _ => 0
  end.

(* Matrix-vector product, restricted to the 5 live coordinates (every        *)
(* other column of L_R is 0 on this graph, so nothing outside 0..4 matters). *)
Definition Lapply (x : nat -> Q) (i : nat) : Q :=
  L_R i 0%nat * x 0%nat + L_R i 1%nat * x 1%nat + L_R i 2%nat * x 2%nat
  + L_R i 3%nat * x 3%nat + L_R i 4%nat * x 4%nat.

(* THE KEY STRUCTURAL FACT: L_R has bandwidth 1 -- any two indices at         *)
(* graph-distance >= 2 give a zero entry. Proved by finite case split; no      *)
(* pair beyond the 13 explicit ones above was ever given a nonzero value.       *)
Theorem L_R_banded :
  forall i j : nat, ((j >= i + 2)%nat \/ (i >= j + 2)%nat) -> L_R i j == 0.
Proof.
  intros i j H.
  destruct i as [| [| [| [| [| i]]]]]; destruct j as [| [| [| [| [| j]]]]];
    simpl; try reflexivity; try lia.
Qed.

(* ------------------------------------------------------------------ *)
(* THE WITNESS INITIAL STATE: a delta at node 0.                          *)
(* ------------------------------------------------------------------ *)

Definition Phi0 : nat -> Q :=
  fun i => match i with 0%nat => 1 | _ => 0 end.

Definition dt14 : Q := 1 # 4.

Compute (Lapply Phi0 0%nat).  (* =  1 *)
Compute (Lapply Phi0 1%nat).  (* = -1 *)
Compute (Lapply Phi0 2%nat).  (* =  0 (node 2 is not yet reached) *)

(* ------------------------------------------------------------------ *)
(* PART 1 -- FIRST-ORDER forward-Euler:                                   *)
(*   Phi1 = Phi0 + dt * (L_R applied to Phi0)                              *)
(* is STRICT-finite-cone: node 2 is exactly 0 after one step, and           *)
(* becomes nonzero only after a second step. Bandwidth = step count.         *)
(* ------------------------------------------------------------------ *)

Definition euler1 (dt : Q) (x : nat -> Q) (i : nat) : Q :=
  x i + dt * Lapply x i.

Definition Phi1 : nat -> Q := euler1 dt14 Phi0.

Compute (Phi1 0%nat).  (* =  5#4 *)
Compute (Phi1 1%nat).  (* = -1#4 *)
Compute (Phi1 2%nat).  (* =     0 *)

Theorem euler1_dt14_Phi0_node2_zero : euler1 dt14 Phi0 2%nat == 0.
Proof.
  unfold euler1, Lapply, L_R, Phi0, dt14. simpl. ring.
Qed.

(* the cone genuinely reached distance 1: node 1 (Phi0's only neighbor)     *)
(* is NONZERO after that same one step, so this is a real, non-vacuous       *)
(* strict-cone boundary, not an all-zero degenerate case.                     *)
Theorem euler1_dt14_Phi0_node1_nonzero : ~ (euler1 dt14 Phi0 1%nat == 0).
Proof.
  unfold euler1, Lapply, L_R, Phi0, dt14. simpl. intro H. lra.
Qed.

Definition Phi2 : nat -> Q := euler1 dt14 Phi1.

Compute (Phi2 2%nat).  (* = 1#16, nonzero: distance-2 reached on step 2 *)

Theorem euler1_two_steps_node2_nonzero : ~ (euler1 dt14 Phi1 2%nat == 0).
Proof.
  cbv [euler1 Lapply L_R Phi1 Phi0 dt14]. intro H. lra.
Qed.

(* ------------------------------------------------------------------ *)
(* PART 2 -- SECOND-ORDER leapfrog:                                       *)
(*   Phi1 = 2*Phi0 - Phiprev + dt*dt * (L_R applied to Phi0), Phiprev=Phi0  *)
(* is ALSO strict-finite-cone: node 2 is exactly 0 after one step.           *)
(* ------------------------------------------------------------------ *)

Definition leapfrog (dt : Q) (prev curr : nat -> Q) (i : nat) : Q :=
  2 * curr i - prev i + dt * dt * Lapply curr i.

Compute (leapfrog dt14 Phi0 Phi0 0%nat).  (* = 17#16 *)
Compute (leapfrog dt14 Phi0 Phi0 1%nat).  (* = -1#16 *)
Compute (leapfrog dt14 Phi0 Phi0 2%nat).  (* =     0 *)

Theorem leapfrog_dt14_Phi0_node2_zero :
  leapfrog dt14 Phi0 Phi0 2%nat == 0.
Proof.
  unfold leapfrog, Lapply, L_R, Phi0, dt14. simpl. ring.
Qed.

(* ------------------------------------------------------------------ *)
(* PART 3 -- THE CORE CONJUNCTION: strict-causal-cone locality does NOT     *)
(* distinguish first-order from second-order -- BOTH give node 2 = 0         *)
(* after one step on the identical witness.                                   *)
(* ------------------------------------------------------------------ *)

Theorem both_orders_strict_cone_node2 :
  euler1 dt14 Phi0 2%nat == 0 /\ leapfrog dt14 Phi0 Phi0 2%nat == 0.
Proof.
  split.
  - exact euler1_dt14_Phi0_node2_zero.
  - exact leapfrog_dt14_Phi0_node2_zero.
Qed.

(* ------------------------------------------------------------------ *)
(* PART 4 -- THE DISTINGUISHING PROPERTY IS CONSERVATION, NOT CONE.         *)
(*   (a) the first-order Euler step run in the PHYSICAL heat direction        *)
(*       (dt = -1/4, i.e. one forward-Euler step of dPhi/dt = -L_R Phi)         *)
(*       STRICTLY DECREASES the quadratic energy sum_i Phi_i^2.                  *)
(*   (b) a conservative (orthogonal) step on two coordinates leaves the           *)
(*       SAME energy EXACTLY fixed.                                                *)
(* ------------------------------------------------------------------ *)

Definition energy5 (x : nat -> Q) : Q :=
  x 0%nat * x 0%nat + x 1%nat * x 1%nat + x 2%nat * x 2%nat
  + x 3%nat * x 3%nat + x 4%nat * x 4%nat.

Definition dtm14 : Q := -(1 # 4).

Definition Phi1heat : nat -> Q := euler1 dtm14 Phi0.

Compute (Phi1heat 0%nat).      (* = 3#4 *)
Compute (Phi1heat 1%nat).      (* = 1#4 *)
Compute (energy5 Phi0).        (* = 1     *)
Compute (energy5 Phi1heat).    (* = 5#8, strictly less than 1 *)
Compute (energy5 Phi1).        (* = 13#8, the dt=+1/4 (anti-diffusive) instance grows -- shown for contrast, honestly NOT the dissipative direction *)

Theorem heat_step_strictly_dissipates :
  energy5 (euler1 dtm14 Phi0) < energy5 Phi0.
Proof.
  unfold energy5, euler1, Lapply, L_R, Phi0, dtm14. simpl. lra.
Qed.

(* THE CONSERVATIVE COUNTERPART: a rational orthogonal (Givens) step on        *)
(* coordinates 0 and 1 only -- every other coordinate is left untouched by       *)
(* construction. Reproved standalone here (no Require) in the spirit of          *)
(* InfoDistinctionConserved_attempt.v's Parseval lens.                            *)

Definition givens_step (a b : Q) (x : nat -> Q) (i : nat) : Q :=
  match i with
  | 0%nat => a * x 0%nat + b * x 1%nat
  | 1%nat => b * x 0%nat - a * x 1%nat
  | _ => x i
  end.

Theorem givens_energy_preserved :
  forall (a b : Q) (x : nat -> Q),
  a * a + b * b == 1 ->
  energy5 (givens_step a b x) == energy5 x.
Proof.
  intros a b x Hab.
  unfold energy5, givens_step. simpl.
  assert (Key :
    (a * x 0%nat + b * x 1%nat) * (a * x 0%nat + b * x 1%nat)
    + (b * x 0%nat - a * x 1%nat) * (b * x 0%nat - a * x 1%nat)
    == (a * a + b * b) * (x 0%nat * x 0%nat + x 1%nat * x 1%nat)) by ring.
  rewrite Key, Hab. ring.
Qed.

Definition ga : Q := 3 # 5.
Definition gb : Q := 4 # 5.

Theorem pyth_3_4_5_orthogonal : ga * ga + gb * gb == 1.
Proof. unfold ga, gb. reflexivity. Qed.

Compute (givens_step ga gb Phi0 0%nat).  (* = 3#5 *)
Compute (givens_step ga gb Phi0 1%nat).  (* = 4#5 *)
Compute (energy5 (givens_step ga gb Phi0)).  (* = 1, exactly energy5 Phi0 *)

Theorem conservative_step_preserves_energy :
  energy5 (givens_step ga gb Phi0) == energy5 Phi0.
Proof.
  apply givens_energy_preserved. exact pyth_3_4_5_orthogonal.
Qed.

(* THE CLOSING CONJUNCTION: dissipation is strict (<) while conservation      *)
(* is exact (==), on the very same node-2 strict-cone witness of Parts 1-3 -- *)
(* the discriminator between the two orders is conservation, not cone.         *)
Theorem dissipative_vs_conservative_node2 :
  (euler1 dt14 Phi0 2%nat == 0 /\ leapfrog dt14 Phi0 Phi0 2%nat == 0)
  /\ energy5 (euler1 dtm14 Phi0) < energy5 Phi0
  /\ energy5 (givens_step ga gb Phi0) == energy5 Phi0.
Proof.
  split; [| split].
  - exact both_orders_strict_cone_node2.
  - exact heat_step_strictly_dissipates.
  - exact conservative_step_preserves_energy.
Qed.

(* ================== AXIOM-FREEDOM CHECK ================== *)
Print Assumptions L_R_banded.
Print Assumptions euler1_dt14_Phi0_node2_zero.
Print Assumptions euler1_dt14_Phi0_node1_nonzero.
Print Assumptions euler1_two_steps_node2_nonzero.
Print Assumptions leapfrog_dt14_Phi0_node2_zero.
Print Assumptions both_orders_strict_cone_node2.
Print Assumptions heat_step_strictly_dissipates.
Print Assumptions givens_energy_preserved.
Print Assumptions pyth_3_4_5_orthogonal.
Print Assumptions conservative_step_preserves_energy.
Print Assumptions dissipative_vs_conservative_node2.

End StrictConeBothOrders.
