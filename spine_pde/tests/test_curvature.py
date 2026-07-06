"""Exact-mode curvature checks against the known theorem values."""

from fractions import Fraction

import pytest

from spine_pde import curvature as cv


def wsq(n):
    return n * n  # w(n) = n**2


def test_riemann_second_difference_identity():
    # riemann_fd == w(j+2) - 2 w(j+1) + w(j) for arbitrary rational data
    w = [Fraction(3), Fraction(1, 2), Fraction(-4), Fraction(7), Fraction(0)]
    for j in range(3):
        assert cv.riemann_fd(w, j) == cv.riemann_is_second_difference(w, j)


def test_curvature_nonzero_witness_is_two():
    # THE witness: riemann of w = n**2 is exactly 2
    assert cv.riemann_fd(wsq, 0) == 2
    assert isinstance(cv.riemann_fd(wsq, 0), int)


def test_affine_is_flat():
    # affine w(n) = a + b n has zero discrete Riemann everywhere
    a, b = Fraction(5, 3), Fraction(-2, 7)
    w = lambda n: a + b * n
    for j in range(6):
        assert cv.riemann_fd(w, j) == 0
        assert cv.is_flat(w, j)


def test_gauss_bonnet_telescopes():
    # total curvature == boundary christoffel difference; and == 4 for n**2, N=2
    for N in range(5):
        assert cv.total_curvature(wsq, N) == cv.gauss_bonnet_boundary(wsq, N)
    assert cv.total_curvature(wsq, 2) == 4


def test_R1212_metric_curvature_exact():
    # R1212(w, n) = -(1/2) ddw + dw**2/(4 w); exact rational for w = n**2
    # at n=1: w=1, dw=3, ddw=2  -> -1 + 9/4 = 5/4
    val = cv.R1212(wsq, 1)
    assert val == Fraction(5, 4)


def test_R1212_flat_constant_is_zero():
    w = lambda n: Fraction(7)  # constant metric -> flat
    assert cv.R1212(w, 3) == 0


def test_commutator_curvature_is_ab():
    # Heisenberg plaquette curvature: centre of [X,Y] == a*b, division-free
    a, b = Fraction(3, 5), Fraction(-2)
    assert cv.commutator_curvature(a, b) == a * b
    # reversing the loop negates it
    assert cv.Heisenberg(0, b, 0).commutator(cv.Heisenberg(a, 0, 0)).z == -(a * b)


def test_heisenberg_inverse():
    g = cv.Heisenberg(Fraction(2), Fraction(3), Fraction(5))
    e = g.mul(g.inv())
    assert (e.x, e.y, e.z) == (0, 0, 0)


def test_metric_zero_raises():
    with pytest.raises(ZeroDivisionError):
        cv.R1212([0, 1, 2], 0)
