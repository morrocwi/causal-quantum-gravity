(* ===================================================================== *)
(*  InfoZeroInfinityReciprocal_attempt.v                                   *)
(*  ZERO AND INFINITY AS RECIPROCAL NON-READOUTS (1/0 = infinity), THAT     *)
(*  APPEAR TOGETHER AT A SINGULARITY.  Entirely over Q (QArith): the        *)
(*  reciprocal is Qinv, the "approach to 0" is the strictly positive        *)
(*  sequence r_n = 1/(n+1) that never reaches 0, and "infinity" is          *)
(*  rendered honestly as "no finite Q bounds the reciprocals" -- the        *)
(*  refused +infinity is reached only in the unreachable x = 0 limit.       *)
(*  NO literal division by 0 is used (Coq's 1/0 = 0 convention is never     *)
(*  relied on): every statement is about r_n > 0.                           *)
(*                                                                          *)
(*  ------------------------- SCOPE (read me) --------------------------    *)
(*  [Th_coqc]  (actually machine-checked below, coqc, axiom-free):          *)
(*    Th_coqc_r_strictly_positive                                           *)
(*        r_n = 1/(n+1) is STRICTLY POSITIVE for every n: 0 is never        *)
(*        attained by the sequence (the zero end is only approached).       *)
(*    Th_coqc_reciprocal_blowup                                             *)
(*        the reciprocal 1/r_n = (n+1) EXCEEDS ANY finite bound B:Q --      *)
(*        no finite rational bounds all the reciprocals, so "1/0" is the    *)
(*        refused +infinity reached only in the unreachable x=0 limit.      *)
(*    Th_coqc_reciprocal_witness                                            *)
(*        concrete: 1/(1/1000) = 1000 > 100.                                *)
(*    Th_coqc_pair_product_invariant                                        *)
(*        for a density rho(r) = M/r with M>0 on r_n = 1/(n+1):             *)
(*        rho_n * r_n == M EXACTLY -- the finite invariant READOUT.         *)
(*    Th_coqc_density_blowup                                                *)
(*        (a) rho_n = M*(n+1) exceeds any bound B:Q (the "infinity" end),   *)
(*    Th_coqc_radius_to_zero                                                *)
(*        (b) WHILE r_n falls below any positive eps (the "zero" end):      *)
(*        both ends of the SAME small-r <-> large-rho event.                *)
(*    Th_coqc_pair_witness                                                  *)
(*        concrete pairing at M=5, n=999: rho=5000, r=1/1000, product=5.    *)
(*    Th_coqc_neither_endpoint_is_readout                                   *)
(*        the honest core: r_n > 0 always (0 unreached) AND the reciprocal  *)
(*        exceeds every finite bound (infinity unreached) -- both ends      *)
(*        approached, neither reached; only rho*r=M is a finite readout.    *)
(*    BE HONEST: these are ELEMENTARY facts about 1/n and M/r over Q,       *)
(*    proved by the Archimedean property.  A THIN anchor -- the algebra     *)
(*    carries no physics by itself.                                         *)
(*                                                                          *)
(*  [Dr]  (the POINT -- explicitly NOT proved by Coq, an interpretive       *)
(*        reading laid on top of the elementary algebra):                   *)
(*    - zero and infinity are RECIPROCAL non-readouts: "1/0 = infinity" is  *)
(*      the pairing, not an arithmetic fact (Coq's 1/0 is the placeholder   *)
(*      0, deliberately avoided here).                                      *)
(*    - a SINGULARITY injects BOTH at once: the radius zero (Z1, an         *)
(*      injected zero) and the density infinity (I4, a refused +infinity)   *)
(*      are the same event, tied by the finite invariant rho*r = M.         *)
(*    - the third law (T=0 unreachable) is physics confessing the           *)
(*      injected-zero: the strictly-positive sequence models exactly that   *)
(*      "approached, never reached".                                        *)
(*    - readout-not-truth refuses BOTH divergent ends; the finite reader    *)
(*      lives BETWEEN them, touching neither.  The only readout is the      *)
(*      finite PRODUCT rho*r = M, never the two divergent factors r and     *)
(*      rho separately.                                                     *)
(* ===================================================================== *)

Require Import QArith.
Require Import ZArith.

(* ----- the honest sequence: r_n = 1/(n+1), never 0, and its reciprocal --- *)

(* denom n = n+1 as a rational, always >= 1 (the reciprocal 1/r_n). *)
Definition denom (n : nat) : Q := inject_Z (Z.of_nat (S n)).

(* r_n = 1/(n+1): the small radius, strictly positive, tending to 0. *)
Definition r (n : nat) : Q := / denom n.

(* rho M n = M/r_n = M*(n+1): the density that blows up as r shrinks. *)
Definition rho (M : Q) (n : nat) : Q := M * denom n.

(* denom n is strictly positive for every n. *)
Lemma denom_pos : forall n : nat, 0 < denom n.
Proof.
  intro n. unfold denom.
  assert (H : (0 < Z.of_nat (S n))%Z).
  { apply (Nat2Z.inj_lt 0 (S n)). apply Nat.lt_0_succ. }
  rewrite Zlt_Qlt in H. exact H.
Qed.

Lemma pos_nonzero : forall x : Q, 0 < x -> ~ x == 0.
Proof.
  intros x Hx. apply Qnot_eq_sym. apply Qlt_not_eq. exact Hx.
Qed.

Lemma denom_nonzero : forall n : nat, ~ denom n == 0.
Proof.
  intro n. apply pos_nonzero. apply denom_pos.
Qed.

Lemma Qinv_mult_l : forall x : Q, ~ x == 0 -> / x * x == 1.
Proof.
  intros x Hx. rewrite Qmult_comm. apply Qmult_inv_r. exact Hx.
Qed.

(* --------- ARCHIMEDEAN CORE: (n+1) exceeds any finite bound ------------- *)

(* No finite rational B bounds all the reciprocals (n+1). *)
Lemma denom_unbounded : forall B : Q, exists n : nat, B < denom n.
Proof.
  intro B.
  destruct (Qarchimedean B) as [p Hp].
  destruct (Pos2Nat.is_succ p) as [m Hm].
  exists m. unfold denom. rewrite <- Hm.
  rewrite positive_nat_Z. exact Hp.
Qed.

(* ============================ Th_coqc ================================== *)

(* (1) STRICT POSITIVITY: 0 is never attained by the sequence. *)
Theorem Th_coqc_r_strictly_positive : forall n : nat, 0 < r n.
Proof.
  intro n. unfold r. apply Qinv_lt_0_compat. apply denom_pos.
Qed.

(* r_n and its reciprocal multiply to 1 (the reciprocal really is 1/r_n). *)
Theorem Th_coqc_r_times_reciprocal : forall n : nat, r n * denom n == 1.
Proof.
  intro n. unfold r. apply Qinv_mult_l. apply denom_nonzero.
Qed.

(* (1) RECIPROCAL BLOW-UP: the reciprocal 1/r_n = (n+1) exceeds any bound. *)
Theorem Th_coqc_reciprocal_blowup :
  forall B : Q, exists n : nat, B < denom n.
Proof.
  exact denom_unbounded.
Qed.

(* (1) concrete witness: 1/(1/1000) = 1000 > 100. *)
Theorem Th_coqc_reciprocal_witness :
  r 999 == / inject_Z 1000 /\ denom 999 == inject_Z 1000 /\ inject_Z 100 < denom 999.
Proof.
  unfold r, denom. repeat split.
Qed.

(* (2) THE PAIRING -- product invariant: rho_n * r_n == M exactly. *)
Theorem Th_coqc_pair_product_invariant :
  forall (M : Q) (n : nat), rho M n * r n == M.
Proof.
  intros M n. unfold rho, r.
  rewrite <- Qmult_assoc.
  rewrite Qmult_inv_r by (apply denom_nonzero).
  apply Qmult_1_r.
Qed.

(* (2a) DENSITY BLOW-UP: rho_n = M*(n+1) exceeds any bound (M>0). *)
Theorem Th_coqc_density_blowup :
  forall M : Q, 0 < M -> forall B : Q, exists n : nat, B < rho M n.
Proof.
  intros M HM B.
  destruct (denom_unbounded (B * / M)) as [n Hn].
  exists n. unfold rho.
  (* from B*/M < denom n, multiply by M>0 on the right *)
  assert (Hr : (B * / M) * M < denom n * M).
  { apply (proj2 (Qmult_lt_r (B * / M) (denom n) M HM)). exact Hn. }
  assert (He : (B * / M) * M == B).
  { rewrite <- Qmult_assoc. rewrite Qinv_mult_l by (apply pos_nonzero; exact HM).
    apply Qmult_1_r. }
  rewrite He in Hr.
  rewrite (Qmult_comm M (denom n)). exact Hr.
Qed.

(* (2b) RADIUS TO ZERO: r_n falls below any positive eps (the zero end). *)
Theorem Th_coqc_radius_to_zero :
  forall eps : Q, 0 < eps -> exists n : nat, r n < eps.
Proof.
  intros eps Heps.
  destruct (denom_unbounded (/ eps)) as [n Hn].
  exists n. unfold r.
  (* need /denom n < eps; both positive.  Multiply by denom n > 0. *)
  apply (proj1 (Qmult_lt_r (/ denom n) eps (denom n) (denom_pos n))).
  (* goal: /denom n * denom n < eps * denom n *)
  rewrite Qinv_mult_l by (apply denom_nonzero).
  (* goal: 1 < eps * denom n; from /eps < denom n multiply by eps>0 *)
  assert (Hstep : eps * / eps < eps * denom n).
  { apply (proj2 (Qmult_lt_l (/ eps) (denom n) eps Heps)). exact Hn. }
  assert (He1 : eps * / eps == 1).
  { apply Qmult_inv_r. apply pos_nonzero. exact Heps. }
  rewrite He1 in Hstep. exact Hstep.
Qed.

(* (2) concrete pairing witness at M=5, n=999: rho=5000, r=1/1000, prod=5. *)
Theorem Th_coqc_pair_witness :
  rho (inject_Z 5) 999 == inject_Z 5000
  /\ r 999 == / inject_Z 1000
  /\ rho (inject_Z 5) 999 * r 999 == inject_Z 5.
Proof.
  split; [ | split ].
  - unfold rho, denom. reflexivity.
  - unfold r, denom. reflexivity.
  - apply Th_coqc_pair_product_invariant.
Qed.

(* (3) NEITHER ENDPOINT IS A FINITE READOUT -- the honest core: r_n > 0 for
   all n (0 unreached), yet the reciprocal exceeds every finite bound
   (infinity unreached).  Both ends are approached, neither reached; only
   the product rho*r = M is a finite readout. *)
Theorem Th_coqc_neither_endpoint_is_readout :
  (forall n : nat, 0 < r n)
  /\ (forall B : Q, exists n : nat, B < denom n)
  /\ (forall (M : Q) (n : nat), rho M n * r n == M).
Proof.
  split; [ | split ].
  - apply Th_coqc_r_strictly_positive.
  - apply Th_coqc_reciprocal_blowup.
  - apply Th_coqc_pair_product_invariant.
Qed.

(* ------------------- axiom-freedom audit (REAL calls) ------------------- *)
Print Assumptions Th_coqc_r_strictly_positive.
Print Assumptions Th_coqc_r_times_reciprocal.
Print Assumptions Th_coqc_reciprocal_blowup.
Print Assumptions Th_coqc_reciprocal_witness.
Print Assumptions Th_coqc_pair_product_invariant.
Print Assumptions Th_coqc_density_blowup.
Print Assumptions Th_coqc_radius_to_zero.
Print Assumptions Th_coqc_pair_witness.
Print Assumptions Th_coqc_neither_endpoint_is_readout.
