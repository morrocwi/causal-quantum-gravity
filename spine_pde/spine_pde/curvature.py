"""Discrete curvature: finite-difference Riemann, Gauss-Bonnet, metric R1212,
and the division-free Heisenberg group-commutator curvature.

Everything is a *finite* difference on a 1-D metric field ``w`` sampled on the
nodes ``0, 1, 2, ...`` (``w`` may be a sequence or a callable ``n -> value``).
No continuum, no limit is taken.  Each routine is exact-rational capable: pass
:class:`~fractions.Fraction` (or ints) and the result is an exact ``Fraction``
that matches the Coq theorems bit-for-bit.

Mirrors of the formal (Coq) definitions
---------------------------------------
Each routine below reproduces, bit-for-bit in exact mode, a checked Coq theorem
from ``research_universal_solver/formal``.  The source module and theorem name
are cited in every docstring so the Python and Coq layers stay in lock-step.

* ``christoffel_fd(w, j) = w(j+1) - w(j)``  (forward diff)
    -- ``InfoDiscreteRiemannCurvature_attempt.christoffel_fd``
* ``riemann_fd(w, j) = christoffel_fd(w, j+1) - christoffel_fd(w, j)``
    ``= w(j+2) - 2 w(j+1) + w(j)``  (second diff)
    -- ``InfoDiscreteRiemannCurvature_attempt.riemann_is_second_difference``
* ``total_curvature(w, N) = christoffel_fd(w, N) - christoffel_fd(w, 0)``
    (Gauss-Bonnet: the bulk sum telescopes to the boundary)
    -- ``InfoDiscreteGaussBonnet_attempt.total_curvature_telescopes``
* ``R1212(w, n) = -(1/2) ddw(w, n) + dw(w, n)**2 / (4 w(n))``  (Levi-Civita, g = diag(1, w))
    -- ``InfoMetricDerivedCurvature_attempt.R1212``
* Heisenberg commutator ``[X, Y]`` has centre ``a*b`` -- the plaquette curvature.
    -- ``InfoDiscreteRiemannCommutator_attempt.plaquette_curvature_z``

Known theorem values (checked in the test suite)::

    riemann_fd(n -> n**2, 0) == 2      # curvature_nonzero_witness
    total_curvature(n -> n**2, 2) == 4 # total_curv_wsq_2
    R1212((1, 2, 4, ...), 0) == -1/4   # curved_witness
    commutator_curvature(a, b) == a*b  # plaquette_curvature_z
"""

from __future__ import annotations

from fractions import Fraction
from numbers import Rational
from typing import Callable, NamedTuple, Sequence, Union

Number = Union[int, float, Fraction]
Field = Union[Sequence[Number], Callable[[int], Number]]

__all__ = [
    "christoffel_fd",
    "riemann_fd",
    "riemann_is_second_difference",
    "total_curvature",
    "gauss_bonnet_boundary",
    "is_flat",
    "dw",
    "ddw",
    "G212",
    "R1212",
    "Heisenberg",
    "commutator_curvature",
]


def _eval(w: Field, n: int) -> Number:
    """Sample the metric field ``w`` at index ``n``."""
    if callable(w):
        return w(n)
    return w[n]


# --------------------------------------------------------------------------- #
# Finite-difference (affine-connection) curvature
# --------------------------------------------------------------------------- #


def christoffel_fd(w: Field, j: int) -> Number:
    """Forward difference ``w(j+1) - w(j)`` -- the discrete Christoffel symbol.

    Coq: ``InfoDiscreteRiemannCurvature_attempt.christoffel_fd``.  Note it can be
    nonzero while the Riemann curvature is zero (``christoffel_can_be_nonzero_while_flat``).
    """
    return _eval(w, j + 1) - _eval(w, j)


def riemann_fd(w: Field, j: int) -> Number:
    """Second difference ``christoffel_fd(w, j+1) - christoffel_fd(w, j)``.

    This is the discrete Riemann curvature at node ``j``.  An *affine* metric is
    flat (``riemann_fd == 0``, Coq ``affine_is_flat``); ``w(n) = n**2`` gives the
    nonzero witness ``riemann_fd(w, 0) == 2`` (Coq ``curvature_nonzero_witness``).
    Coq def: ``InfoDiscreteRiemannCurvature_attempt.riemann_fd``.
    """
    return christoffel_fd(w, j + 1) - christoffel_fd(w, j)


def riemann_is_second_difference(w: Field, j: int) -> Number:
    """Closed form ``w(j+2) - 2 w(j+1) + w(j)`` (equal to :func:`riemann_fd`).

    Coq theorem: ``InfoDiscreteRiemannCurvature_attempt.riemann_is_second_difference``.
    """
    return _eval(w, j + 2) - 2 * _eval(w, j + 1) + _eval(w, j)


def total_curvature(w: Field, N: int) -> Number:
    """Total discrete curvature ``sum_{j<N} riemann_fd(w, j)``.

    By the discrete Gauss-Bonnet identity this telescopes to the boundary
    Christoffel difference ``christoffel_fd(w, N) - christoffel_fd(w, 0)``; the
    sum is computed directly and both forms agree exactly.  For ``w(n) = n**2``,
    ``total_curvature(w, 2) == 4`` (Coq ``total_curv_wsq_2``).
    Coq theorem: ``InfoDiscreteGaussBonnet_attempt.total_curvature_telescopes``.
    """
    if N < 0:
        raise ValueError("N must be non-negative")
    total: Number = 0
    for j in range(N):
        total = total + riemann_fd(w, j)
    return total


def gauss_bonnet_boundary(w: Field, N: int) -> Number:
    """The boundary side of Gauss-Bonnet: ``christoffel_fd(w, N) - christoffel_fd(w, 0)``.

    Equals :func:`total_curvature` exactly (Coq ``total_curvature_telescopes``); a
    closed loop (matched boundary) has zero total curvature (``closed_loop_zero_total_curvature``).
    """
    return christoffel_fd(w, N) - christoffel_fd(w, 0)


def is_flat(w: Field, j: int) -> bool:
    """True iff ``riemann_fd(w, j) == 0`` (affine metrics are flat)."""
    return riemann_fd(w, j) == 0


# --------------------------------------------------------------------------- #
# Metric-derived Levi-Civita curvature for g = diag(1, w)
# --------------------------------------------------------------------------- #


def dw(w: Field, n: int) -> Number:
    """First difference ``w(n+1) - w(n)``."""
    return _eval(w, n + 1) - _eval(w, n)


def ddw(w: Field, n: int) -> Number:
    """Second difference ``w(n+2) - 2 w(n+1) + w(n)``."""
    return _eval(w, n + 2) - 2 * _eval(w, n + 1) + _eval(w, n)


def _is_rational(v: object) -> bool:
    return isinstance(v, (int, Rational, Fraction))


def _half(sample: Number) -> Number:
    """Return ``1/2`` in the arithmetic of ``sample`` (exact for rationals)."""
    if _is_rational(sample):
        return Fraction(1, 2)
    return 0.5


def _div(num: Number, den: Number) -> Number:
    """Divide, staying exact (``Fraction``) when both operands are rational.

    Plain ``int / int`` in Python is *float* true-division, which would silently
    drop the exact-mode guarantee; this keeps rationals rational.
    """
    if _is_rational(num) and _is_rational(den):
        return Fraction(num) / Fraction(den)
    return num / den


def G212(w: Field, n: int) -> Number:
    """Levi-Civita Christoffel ``Gamma^2_{12} = (1/2) dw / w`` for ``g = diag(1, w)``.

    Coq: ``InfoMetricDerivedCurvature_attempt.G212`` (``christoffel_G212_rational``).
    """
    wn = _eval(w, n)
    if wn == 0:
        raise ZeroDivisionError("metric component w(n) vanishes")
    return _half(wn) * _div(dw(w, n), wn)


def R1212(w: Field, n: int) -> Number:
    """Levi-Civita curvature ``R_{1212} = -(1/2) ddw + dw**2 / (4 w)`` for ``g = diag(1, w)``.

    The single independent Riemann component of the 2-D metric.  A constant metric
    field is flat (``R1212 == 0``, Coq ``flat_constant_zero_curvature``); the
    doubling field ``w = (1, 2, 4, ...)`` is the curved witness with
    ``R1212(w, 0) == -1/4`` (Coq ``curved_witness``).
    Coq def: ``InfoMetricDerivedCurvature_attempt.R1212``.
    """
    wn = _eval(w, n)
    if wn == 0:
        raise ZeroDivisionError("metric component w(n) vanishes")
    d = dw(w, n)
    return -_half(wn) * ddw(w, n) + _div(d * d, 4 * wn)


# --------------------------------------------------------------------------- #
# Group-commutator (Heisenberg) curvature -- division-free, exact
# --------------------------------------------------------------------------- #


class Heisenberg(NamedTuple):
    """An element of the discrete Heisenberg group with the polynomial law.

    ``mul`` : ``(x1+x2, y1+y2, z1+z2 + x1*y2)`` ;
    ``inv`` : ``(-x, -y, -z + x*y)``.  All operations are ring operations, so
    the group is exact over any ring (``int`` / :class:`~fractions.Fraction`) --
    division-free.  Coq: ``InfoDiscreteRiemannCommutator_attempt`` records
    ``Hb`` / ``hmul`` / ``hinv`` (``hinv_ok``).
    """

    x: Number
    y: Number
    z: Number

    def mul(self, other: "Heisenberg") -> "Heisenberg":
        return Heisenberg(
            self.x + other.x,
            self.y + other.y,
            self.z + other.z + self.x * other.y,
        )

    def inv(self) -> "Heisenberg":
        return Heisenberg(-self.x, -self.y, -self.z + self.x * self.y)

    def commutator(self, other: "Heisenberg") -> "Heisenberg":
        """Group commutator ``[g1, g2] = g1 g2 g1^-1 g2^-1``."""
        return self.mul(other).mul(self.inv()).mul(other.inv())


HID = Heisenberg(0, 0, 0)


def commutator_curvature(a: Number, b: Number) -> Number:
    """Plaquette curvature ``R_xy`` = centre of ``[X, Y]`` for ``X=(a,0,0)``, ``Y=(0,b,0)``.

    Equals ``a*b`` exactly, division-free (Coq ``plaquette_curvature_z``); the
    x/y components vanish (``curvature_is_central``) and reversing the loop negates
    it (``reverse_antisymmetric``).  Abelian / same-direction loops are flat
    (``abelian_flat_x`` / ``same_direction_flat``).
    """
    c = Heisenberg(a, 0, 0).commutator(Heisenberg(0, b, 0))
    assert c.x == 0 and c.y == 0, "curvature must be central"
    return c.z
