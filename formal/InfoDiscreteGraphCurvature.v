(******************************************************************************)
(* InfoDiscreteGraphCurvature.v -- (axiom-free, Q-only). Requires but does   *)
(*  not modify InfoCoercivityBoundedClosure.v (reuses its wdeg/wshare, does  *)
(*  not redefine them).                                                     *)
(*                                                                            *)
(*  PROVENANCE: extracted 2026-07-05 into discrete-quantum-gravity-journal   *)
(*  from research_universal_solver/formal/                                  *)
(*  InfoDiscreteGraphCurvature_attempt.v (dropping "_attempt"), together     *)
(*  with trimmed-extract copies of its two dependencies, RDL_GammaSpectral.v *)
(*  (Edge/w_of/u_of/v_of only) and InfoCoercivityBoundedClosure.v            *)
(*  (Csafe/wshare/wdeg only, also dropping "_attempt"). Module content       *)
(*  below is otherwise VERBATIM from the source file. See the source file   *)
(*  in research_universal_solver for the full motivation, the eight prior   *)
(*  Schwarzschild-derivation attempts it responds to, the Python exact-     *)
(*  integer pre-check on C6/P6/star/K4 graphs, and the complete SCOPE       *)
(*  discussion (Forman-Ricci curvature is NOT claimed to equal or converge  *)
(*  to continuum Ricci curvature; the "gravity-flavored" framing is Dr, not *)
(*  Th_coqc; only the algebraic wdeg=w*deg link is Th_coqc).                *)
(*                                                                            *)
(*  MOTIVATION -- a philosophy correction, not a retreat. Eight independent  *)
(*  attempts (same day) to derive Schwarzschild/GR structure FROM this      *)
(*  repo's L_R graph operator were tested and refuted or left open. On      *)
(*  reflection: continuum General Relativity (a smooth manifold, curvature  *)
(*  defined via derivative limits ∂g->Christoffel->Riemann) is, by this     *)
(*  repo's OWN stated commitment, a NON-READOUT -- an I1 (manifold          *)
(*  completeness) + I2 (h->0 in the curvature definition) injected-infinity  *)
(*  construction. Chasing an exact match to it was chasing the wrong        *)
(*  target BY THIS REPO'S OWN STANDARD, not a difficulty to be overcome by   *)
(*  cleverer numerics.                                                      *)
(*                                                                            *)
(*  The correct move: ask whether L_R has a NATIVE, discrete notion of      *)
(*  curvature -- one that needs no continuum limit at all -- and treat      *)
(*  THAT as the honest "gravity-flavored" readout, rather than a degraded   *)
(*  substitute for Schwarzschild curvature.                                 *)
(*                                                                            *)
(*  Such a notion already exists in graph theory, decades old, purely       *)
(*  combinatorial: FORMAN-RICCI CURVATURE (R. Forman, Bochner's method for   *)
(*  cell complexes and combinatorial Ricci curvature, 2003). For a simple    *)
(*  unweighted graph, the curvature of an edge (u,v) is exactly              *)
(*    F(u,v) = 4 - deg(u) - deg(v),                                         *)
(*  a NATURAL NUMBER formula with NO derivative, NO limit, NO manifold, and  *)
(*  NO square root -- it is already, natively, a ℚ-valued (in fact ℤ-valued) *)
(*  readout of the SAME edge/degree data this repo's L_R is built from.     *)
(*  This file does not claim Forman curvature itself is new (it is         *)
(*  Forman's, 2003, cited); the contribution here is showing it is         *)
(*  ALREADY a genuine, axiom-free readout of this repo's own graph          *)
(*  primitives, and connecting it -- honestly, by direct substitution, not  *)
(*  by a new derivation -- to the ALREADY-PROVEN coercivity/dissipation     *)
(*  threshold from InfoCoercivityBoundedClosure.v.                          *)
(*                                                                            *)
(*  (1) deg_nonneg / forman well-defined for any edge list (trivial, stated  *)
(*      for completeness).                                                  *)
(*  (2) forman_flat_if_both_degree_two: the "cycle is flat" fact -- if both   *)
(*      endpoints of an edge have degree exactly 2 (as in ANY simple cycle,  *)
(*      not just C6), that edge's Forman curvature is exactly 0.            *)
(*  (3) wdeg_uniform_weight: THE HONEST LINK to the coercivity closure --     *)
(*      when every edge shares one weight w, the WEIGHTED degree (wdeg,      *)
(*      from InfoCoercivityBoundedClosure.v, reused not redefined) equals    *)
(*      w times the UNWEIGHTED degree (deg, this file). Since that file's    *)
(*      own dissipation threshold is D_i >= Csafe*Vmax*wdeg(edges,i),        *)
(*      substituting gives D_i >= Csafe*Vmax*w*deg(edges,i) -- THE SAME       *)
(*      degree number that sets an edge's Forman curvature (more negative    *)
(*      for higher degree) ALSO sets (linearly, via this substitution) how   *)
(*      much dissipation a node needs for the spine to stay coercive. This   *)
(*      is a genuine, native, non-borrowed structural link between          *)
(*      "discrete curvature" and "stability requirement" -- both are        *)
(*      honest functions of the SAME already-defined graph quantity,        *)
(*      connected by direct substitution, not a fresh unproven analogy.     *)
(*                                                                            *)
(* SCOPE -- read before citing this as more than it is:                     *)
(*  (a) Forman-Ricci curvature is NOT claimed to equal, approximate, or      *)
(*      converge to continuum Ricci curvature in any limit -- taking such a  *)
(*      limit would reintroduce exactly the I1/I2 injection this file exists *)
(*      to avoid. It stands on its own as a discrete readout, tier Th_coqc. *)
(*  (b) The "gravity-flavored" framing is Dr (an interpretive stance): this  *)
(*      file proves the ALGEBRAIC link (wdeg = w*deg) exactly; whether       *)
(*      "curvature" and "stability requirement" being the same function of   *)
(*      degree constitutes a physically meaningful statement about gravity   *)
(*      is not adjudicated here and remains open.                           *)
(*  (c) Does not modify InfoCoercivityBoundedClosure.v or any other          *)
(*      Required file.                                                      *)
(******************************************************************************)

Require RDL_GammaSpectral.
Require InfoCoercivityBoundedClosure.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Open Scope Q_scope.

Module InfoDiscreteGraphCurvature.
  Import RDL_GammaSpectral.
  Import InfoCoercivityBoundedClosure.InfoCoercivityBoundedClosure.

  (* UNWEIGHTED share/degree -- the same fold-right pattern wshare/wdeg
     already use, with weight replaced by a flat count of 1 per incidence. *)
  Definition share (e : Edge) (i : nat) : Q :=
    (if Nat.eqb (u_of e) i then 1 else 0) + (if Nat.eqb (v_of e) i then 1 else 0).

  Definition deg (edges : list Edge) (i : nat) : Q :=
    fold_right (fun e acc => share e i + acc) 0 edges.

  (* FORMAN-RICCI CURVATURE of an edge (Forman 2003, the simple/unweighted
     graph case): F(e) = 4 - deg(u_of e) - deg(v_of e). *)
  Definition forman (edges : list Edge) (e : Edge) : Q :=
    (4#1) - deg edges (u_of e) - deg edges (v_of e).

  (* (1) sanity: deg is a well-defined nonnegative count (immediate from the
     fold summing nonnegative 0/1 contributions). *)
  Theorem share_nonneg : forall e i, 0 <= share e i.
  Proof.
    intros e i. unfold share.
    destruct (Nat.eqb (u_of e) i), (Nat.eqb (v_of e) i); lra.
  Qed.

  Theorem deg_nonneg : forall edges i, 0 <= deg edges i.
  Proof.
    induction edges as [| e es IH]; intro i.
    - simpl. lra.
    - unfold deg. simpl. fold (deg es i).
      assert (H1 := share_nonneg e i). assert (H2 := IH i). lra.
  Qed.

  (* (2) THE "CYCLE IS FLAT" FACT: any edge whose two endpoints both have
     degree exactly 2 (true of every edge in any simple cycle graph, e.g.
     the C6 benzene-ring graph from the Huckel bridge) has Forman
     curvature exactly 0. *)
  Theorem forman_flat_if_both_degree_two : forall edges e,
    deg edges (u_of e) == 2 -> deg edges (v_of e) == 2 -> forman edges e == 0.
  Proof. intros edges e Hu Hv. unfold forman. rewrite Hu, Hv. ring. Qed.

  (* THE HONEST LINK -- uniform edge weight ties wdeg (weighted degree, from
     InfoCoercivityBoundedClosure.v, reused verbatim) to deg (this
     file) by exact substitution, no new derivation needed. *)
  Theorem wshare_uniform_weight : forall e i w,
    w_of e == w -> wshare e i == w * share e i.
  Proof.
    intros e i w Hw. unfold wshare, share.
    destruct (Nat.eqb (u_of e) i), (Nat.eqb (v_of e) i).
    - rewrite Hw. ring.
    - rewrite Hw. ring.
    - rewrite Hw. ring.
    - lra.
  Qed.

  Theorem wdeg_uniform_weight : forall edges i w,
    (forall e, In e edges -> w_of e == w) -> wdeg edges i == w * deg edges i.
  Proof.
    induction edges as [| e es IH]; intros i w Hw.
    - unfold wdeg, deg. simpl. ring.
    - assert (Hwe : w_of e == w) by (apply Hw; left; reflexivity).
      assert (Hrest : forall e', In e' es -> w_of e' == w)
        by (intros e' He'; apply Hw; right; exact He').
      unfold wdeg, deg. simpl. fold (wdeg es i). fold (deg es i).
      rewrite (wshare_uniform_weight e i w Hwe).
      rewrite (IH i w Hrest).
      ring.
  Qed.

  (* (3) THE COERCIVITY-CURVATURE SUBSTITUTION: under uniform edge weight w,
     InfoCoercivityBoundedClosure's own per-node dissipation threshold
     (D_i >= Csafe*Vmax*wdeg(edges,i)) is EXACTLY D_i >= Csafe*Vmax*w*deg(edges,i)
     -- the same degree count that sets Forman curvature (more edges at a
     node => more negative curvature there) also sets (linearly) how much
     dissipation that node needs. Stated as a direct corollary of the two
     already-proven facts above, not a fresh claim. *)
  Corollary coercivity_threshold_via_degree : forall edges i w Vmax D,
    (forall e, In e edges -> w_of e == w) ->
    Csafe * Vmax * wdeg edges i <= D ->
    Csafe * Vmax * w * deg edges i <= D.
  Proof.
    intros edges i w Vmax D Hw Hthr.
    rewrite (wdeg_uniform_weight edges i w Hw) in Hthr.
    lra.
  Qed.

  Print Assumptions deg_nonneg.
  Print Assumptions forman_flat_if_both_degree_two.
  Print Assumptions wdeg_uniform_weight.
  Print Assumptions coercivity_threshold_via_degree.

End InfoDiscreteGraphCurvature.

(* PRIMARY TARGET: InfoDiscreteGraphCurvature.wdeg_uniform_weight and          *)
(* .coercivity_threshold_via_degree -- the honest, axiom-free link between     *)
(* Forman-Ricci discrete curvature (a genuine, native, non-borrowed readout    *)
(* of this repo's own edge/degree data, no continuum limit anywhere) and       *)
(* the ALREADY-PROVEN coercivity dissipation threshold from                    *)
(* InfoCoercivityBoundedClosure.v. As documented at length in the header:      *)
(* this is a philosophy correction, not a weaker substitute for deriving       *)
(* Schwarzschild -- continuum GR is, by this repo's own stated commitment,     *)
(* a non-readout, and chasing it (as eight same-day attempts did) was          *)
(* chasing the wrong target. This file instead exhibits a genuine discrete     *)
(* "gravity-flavored" structural fact with zero external borrowing.            *)
(* Does not modify InfoCoercivityBoundedClosure.v or any other Required file.  *)
