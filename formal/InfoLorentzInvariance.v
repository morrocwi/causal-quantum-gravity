(******************************************************************************)
(* InfoLorentzInvariance.v -- extracted verbatim (definitions + Module        *)
(*  InfoLorentzInvariance) from a private research repository's              *)
(*  formal/URCF_RD_All.v, lines 7090-7146. Authored 2026-06-27. Axiom-free,   *)
(*  Th_coqc, Q-only. No content changed beyond isolating the module into      *)
(*  its own file.                                                            *)
(*                                                                            *)
(*  The algebraic core of Lorentz invariance: a boost (g,v) with              *)
(*  g^2(1-v^2)=1 preserves the Minkowski interval -t^2+x^2, and the exact     *)
(*  quadratic-class d'Alembertian symbol box_quad(att,axx)=-2att+2axx is      *)
(*  boost-invariant. Reused (not re-proved) by                               *)
(*  InfoQuantumRelativityUnification.v to connect this repo's quantum         *)
(*  dispersion relation to this same boost-invariant operator.               *)
(******************************************************************************)

Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Open Scope Q_scope.

Module InfoLorentzInvariance.
  Import Coq.QArith.QArith.
  Import Coq.micromega.Lqa.

  Definition interval (t x : Q) : Q := - (t*t) + x*x.
  Definition boost_t (g v t x : Q) : Q := g * (t - v*x).
  Definition boost_x (g v t x : Q) : Q := g * (x - v*t).

  Theorem boost_preserves_interval :
    forall g v t x, g*g*(1 - v*v) == 1 ->
      interval (boost_t g v t x) (boost_x g v t x) == interval t x.
  Proof.
    intros g v t x Hg.
    assert (Hid : interval (boost_t g v t x) (boost_x g v t x)
                  == (g*g*(1 - v*v)) * interval t x).
    { unfold interval, boost_t, boost_x. ring. }
    rewrite Hid, Hg. ring.
  Qed.

  Definition hp_tt (g v htt htx hxx : Q) : Q := g*g*htt - 2*g*g*v*htx + g*g*v*v*hxx.
  Definition hp_xx (g v htt htx hxx : Q) : Q := g*g*v*v*htt - 2*g*g*v*htx + g*g*hxx.

  Theorem box_symbol_boost_invariant :
    forall g v htt htx hxx, g*g*(1 - v*v) == 1 ->
      - (hp_tt g v htt htx hxx) + hp_xx g v htt htx hxx == - htt + hxx.
  Proof.
    intros g v htt htx hxx Hg.
    assert (Hid : - (hp_tt g v htt htx hxx) + hp_xx g v htt htx hxx
                  == (g*g*(1 - v*v)) * (- htt + hxx)).
    { unfold hp_tt, hp_xx. ring. }
    rewrite Hid, Hg. ring.
  Qed.

  Definition box_quad (att axx : Q) : Q := - (2) * att + 2 * axx.
  Definition catt (g v att atx axx : Q) : Q := g*g*(att - atx*v + axx*v*v).
  Definition caxx (g v att atx axx : Q) : Q := g*g*(att*v*v - atx*v + axx).

  Theorem box_quad_boost_invariant :
    forall g v att atx axx, g*g*(1 - v*v) == 1 ->
      box_quad (catt g v att atx axx) (caxx g v att atx axx) == box_quad att axx.
  Proof.
    intros g v att atx axx Hg.
    assert (Hid : box_quad (catt g v att atx axx) (caxx g v att atx axx)
                  == (g*g*(1 - v*v)) * box_quad att axx).
    { unfold box_quad, catt, caxx. ring. }
    rewrite Hid, Hg. ring.
  Qed.
End InfoLorentzInvariance.
