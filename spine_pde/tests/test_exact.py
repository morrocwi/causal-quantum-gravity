"""Tests for the exact-rational front-end: Coq witnesses reproduced bit-for-bit."""

from fractions import Fraction

import pytest

from spine_pde import exact


def test_all_theorem_witnesses_hold():
    results = exact.verify_theorems()
    assert results, "no witnesses registered"
    assert all(results.values()), f"failed witnesses: "\
        f"{[k for k, v in results.items() if not v]}"


def test_telegraph_witnesses_exact():
    assert exact.discriminant(1, 1, 1, 1) == Fraction(-3)
    assert exact.discriminant(1, 4, 1, 1) == Fraction(12)
    lam_c = exact.crossover(2, 3, 5)
    assert isinstance(lam_c, Fraction)
    assert exact.discriminant(2, 3, 5, lam_c) == 0
    assert exact.regime(1, 1, 1, 1) == exact.OSCILLATORY
    assert exact.regime(1, 4, 1, 1) == exact.DECAY
    assert exact.regime(2, 3, 5, lam_c) == exact.CRITICAL


def test_mass_and_tau_c_native_units():
    assert exact.mass(1, 1) == Fraction(1, 2)      # 1/(2M) at D=1
    assert exact.tau_c(3, 2) == Fraction(3, 2)     # M/D
    assert exact.decoherence_rate(5, 2, Fraction(1, 3)) == Fraction(5, 6)


def test_curvature_witnesses_exact():
    wsq = lambda n: n * n
    assert exact.riemann(wsq, 0) == Fraction(2)
    assert exact.total_curvature(wsq, 2) == Fraction(4)
    assert exact.gauss_bonnet_boundary(wsq, 2) == exact.total_curvature(wsq, 2)
    assert exact.R1212(wsq, 1) == Fraction(5, 4)
    assert exact.commutator_curvature(exact.Q(3, 5), exact.Q(-2)) == Fraction(-6, 5)


def test_results_are_fraction_not_float():
    for v in (
        exact.discriminant(1, 1, 1, 2),
        exact.crossover(1, 1, 1),
        exact.riemann(lambda n: n * n, 0),
        exact.R1212(lambda n: n * n, 2),
        exact.commutator_curvature(2, 3),
    ):
        assert isinstance(v, Fraction)


def test_Q_constructor_and_float_rejection():
    assert exact.Q(3, 5) + exact.Q(1, 5) == Fraction(4, 5)
    assert exact.Q("3/4") == Fraction(3, 4)
    with pytest.raises(TypeError):
        exact.Q(0.1)                       # float is ambiguous -> rejected
    with pytest.raises(TypeError):
        exact.discriminant(1.0, 1, 1, 1)   # float coeff rejected in exact mode


def test_zero_damping_guards():
    with pytest.raises(ZeroDivisionError):
        exact.tau_c(1, 0)
    with pytest.raises(ZeroDivisionError):
        exact.decoherence_rate(1, 0, 1)


def test_reverse_loop_antisymmetric_curvature():
    # Reversing the plaquette loop negates the curvature (Coq reverse_antisymmetric):
    # [X, Y] centre = a*b, [Y, X] centre = -a*b.
    a, b = exact.Q(3), exact.Q(7)
    X, Y = exact.Heisenberg(a, 0, 0), exact.Heisenberg(0, b, 0)
    fwd = X.commutator(Y).z
    rev = Y.commutator(X).z
    assert fwd == a * b
    assert rev == -fwd
