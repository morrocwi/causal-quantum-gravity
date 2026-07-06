"""Exact-rational front-end -- reproduce the Coq spine theorems bit-for-bit.

The continuum is refused: nothing here ever touches a float.  Every readout is
an exact :class:`fractions.Fraction` over ``Q``, so the values match the formal
``*_attempt.v`` witnesses of the theory *exactly* (not to a tolerance).

This module is a thin, ergonomic wrapper around the exact code paths that
already live in :mod:`spine_pde.telegraph` (the ``Telegraph`` analyser in
exact mode) and :mod:`spine_pde.curvature` (rational finite-difference and
division-free group-commutator curvature).  Its two jobs are:

1. Force every coefficient into a :class:`~fractions.Fraction` up front, so the
   exact guarantee can never silently degrade to float true-division.
2. Ship the canonical **Coq witnesses** as first-class, checkable objects
   (:data:`THEOREMS` + :func:`verify_theorems`), so a user can confirm the
   package still reproduces the formal theory on their machine.

Mirrored witnesses (module ``:=`` value in the Coq source)::

    InfoTelegraphCrossover.underdamped_witness   disc 1 1 1 1 == -3
    InfoTelegraphCrossover.overdamped_witness    disc 1 4 1 1 == 12
    InfoTelegraphCrossover.critical_disc_zero    disc(lam_c) == 0
    InfoDiscreteRiemannCurvature.curvature...    riemann_fd wsq 0 == 2
    InfoDiscreteGaussBonnet.total_curv_wsq_2     total_curv wsq 2 == 4
    InfoMetricDerivedCurvature (w=n**2, n=1)     R1212 == 5/4
    InfoDiscreteRiemannCommutator.plaquette...   commutator z == a*b

>>> from spine_pde import exact
>>> exact.discriminant(1, 1, 1, 1)
Fraction(-3, 1)
>>> exact.riemann(lambda n: n * n, 0)
Fraction(2, 1)
>>> all(t.holds() for t in exact.THEOREMS)
True
"""

from __future__ import annotations

from fractions import Fraction
from numbers import Rational
from typing import Callable, NamedTuple, Sequence, Union

from . import curvature as _cv
from .curvature import Heisenberg
from .telegraph import CRITICAL, DECAY, OSCILLATORY, Telegraph

__all__ = [
    "Q",
    "Field",
    "telegraph",
    "discriminant",
    "crossover",
    "regime",
    "mass",
    "tau_c",
    "decoherence_rate",
    "christoffel",
    "riemann",
    "total_curvature",
    "gauss_bonnet_boundary",
    "R1212",
    "G212",
    "commutator_curvature",
    "Heisenberg",
    "OSCILLATORY",
    "DECAY",
    "CRITICAL",
    "Witness",
    "THEOREMS",
    "verify_theorems",
]

QInput = Union[int, Fraction, str]
Number = Union[int, Fraction]
Field = Union[Sequence[Number], Callable[[int], Number]]


# --------------------------------------------------------------------------- #
# The exact scalar constructor
# --------------------------------------------------------------------------- #


def Q(num: QInput, den: QInput = 1) -> Fraction:
    """Build an exact rational ``num/den`` over ``Q`` (never a float).

    Accepts ints, existing :class:`~fractions.Fraction` values, or decimal /
    fraction strings (``"3/5"``, ``"0.25"``).  Floats are rejected on purpose:
    a binary float such as ``0.1`` is not the rational ``1/10`` and would break
    the bit-for-bit guarantee.

    >>> Q(3, 5) + Q(1, 5)
    Fraction(4, 5)
    """
    for name, v in (("num", num), ("den", den)):
        if isinstance(v, float):
            raise TypeError(
                f"{name} is a float ({v!r}); pass an int, Fraction or string "
                "so the exact rational is unambiguous"
            )
    return Fraction(num) / Fraction(den) if den != 1 else Fraction(num)


def _coerce(v: Number) -> Fraction:
    if isinstance(v, float):
        raise TypeError(
            f"exact mode rejects the float {v!r}; use spine_pde.exact.Q(...) "
            "or a fractions.Fraction"
        )
    if not isinstance(v, (int, Rational, Fraction)):
        raise TypeError(f"expected an exact rational, got {type(v).__name__}")
    return Fraction(v)


def _coerce_field(w: Field) -> Field:
    """Wrap a metric field so every sample is coerced to an exact ``Fraction``."""
    if callable(w):
        return lambda n: _coerce(w(n))
    seq = [_coerce(v) for v in w]
    return seq


# --------------------------------------------------------------------------- #
# Telegraph / horizon readouts (exact)
# --------------------------------------------------------------------------- #


def telegraph(M: Number, D: Number, K: Number) -> Telegraph:
    """An exact-mode :class:`~spine_pde.telegraph.Telegraph` analyser.

    All three coefficients are coerced to :class:`~fractions.Fraction` and the
    analyser is pinned to ``exact=True``.
    """
    return Telegraph(_coerce(M), _coerce(D), _coerce(K), exact=True)


def discriminant(M: Number, D: Number, K: Number, lam: Number) -> Fraction:
    """Exact telegraph discriminant ``disc = D**2 - 4 M K lam``.

    Matches ``InfoTelegraphCrossover.disc`` over ``Q`` bit-for-bit
    (``disc 1 1 1 1 == -3``).
    """
    return telegraph(M, D, K).discriminant(_coerce(lam))


def crossover(M: Number, D: Number, K: Number) -> Fraction:
    """Exact critical eigenvalue ``lam_c = D**2 / (4 M K)`` (``disc(lam_c) == 0``)."""
    return telegraph(M, D, K).crossover()


def regime(M: Number, D: Number, K: Number, lam: Number) -> str:
    """Regime of mode ``lam``: :data:`OSCILLATORY`, :data:`DECAY` or :data:`CRITICAL`."""
    return telegraph(M, D, K).regime(_coerce(lam))


def mass(M: Number, D: Number) -> Fraction:
    """Exact envelope mass ``D / (2 M) = 1 / (2 tau_c)``.

    In native units ``M = 1`` this is ``D/2``; the theory's ``mass == 1/(2M)``
    holds exactly for ``D = 1``.
    """
    return _coerce(D) / (2 * _coerce(M))


def tau_c(M: Number, D: Number) -> Fraction:
    """Exact correlation time ``tau_c = M / D`` (requires ``D != 0``)."""
    d = _coerce(D)
    if d == 0:
        raise ZeroDivisionError("tau_c = M/D is undefined for D == 0")
    return _coerce(M) / d


def decoherence_rate(K: Number, D: Number, lam: Number) -> Fraction:
    """Exact mode decoherence rate ``Gamma = K lam / D`` (requires ``D != 0``)."""
    d = _coerce(D)
    if d == 0:
        raise ZeroDivisionError("Gamma = K lam / D is undefined for D == 0")
    return _coerce(K) * _coerce(lam) / d


# --------------------------------------------------------------------------- #
# Curvature readouts (exact) -- delegate to spine_pde.curvature
# --------------------------------------------------------------------------- #


def christoffel(w: Field, j: int) -> Fraction:
    """Exact forward-difference Christoffel ``w(j+1) - w(j)``."""
    return _cv.christoffel_fd(_coerce_field(w), j)


def riemann(w: Field, j: int) -> Fraction:
    """Exact discrete Riemann (second difference) at node ``j``.

    ``riemann(n -> n**2, 0) == 2`` -- the ``curvature_nonzero_witness`` theorem.
    """
    return _cv.riemann_fd(_coerce_field(w), j)


def total_curvature(w: Field, N: int) -> Fraction:
    """Exact Gauss-Bonnet total curvature; ``total_curvature(n -> n**2, 2) == 4``."""
    return _cv.total_curvature(_coerce_field(w), N)


def gauss_bonnet_boundary(w: Field, N: int) -> Fraction:
    """Exact boundary side of Gauss-Bonnet (telescopes to the bulk sum)."""
    return _cv.gauss_bonnet_boundary(_coerce_field(w), N)


def R1212(w: Field, n: int) -> Fraction:
    """Exact Levi-Civita curvature ``-(1/2) ddw + dw**2/(4 w)`` for ``g = diag(1, w)``."""
    return _cv.R1212(_coerce_field(w), n)


def G212(w: Field, n: int) -> Fraction:
    """Exact Levi-Civita Christoffel ``Gamma^2_12 = (1/2) dw / w``."""
    return _cv.G212(_coerce_field(w), n)


def commutator_curvature(a: Number, b: Number) -> Fraction:
    """Exact division-free plaquette curvature; equals ``a*b`` (``= centre of [X, Y]``)."""
    return _cv.commutator_curvature(_coerce(a), _coerce(b))


# --------------------------------------------------------------------------- #
# The Coq witnesses as checkable objects
# --------------------------------------------------------------------------- #


class Witness(NamedTuple):
    """One named Coq theorem witness with a live, exact recomputation.

    ``value()`` recomputes the quantity through this package's exact paths;
    ``holds()`` is true iff it equals the ``expected`` rational recorded in the
    formal source.
    """

    name: str
    source: str
    expected: Fraction
    value: Callable[[], Fraction]

    def holds(self) -> bool:
        """True iff the recomputed value equals the Coq witness exactly."""
        return self.value() == self.expected


THEOREMS: tuple[Witness, ...] = (
    Witness(
        "underdamped_witness (disc 1 1 1 1)",
        "InfoTelegraphCrossover_attempt.v",
        Fraction(-3),
        lambda: discriminant(1, 1, 1, 1),
    ),
    Witness(
        "overdamped_witness (disc 1 4 1 1)",
        "InfoTelegraphCrossover_attempt.v",
        Fraction(12),
        lambda: discriminant(1, 4, 1, 1),
    ),
    Witness(
        "critical_disc_zero (disc at lam_c)",
        "InfoTelegraphCrossover_attempt.v",
        Fraction(0),
        lambda: discriminant(2, 3, 5, crossover(2, 3, 5)),
    ),
    Witness(
        "mass == 1/(2M) at D=1, M=1",
        "InfoTauCReadoutLaw_attempt.v",
        Fraction(1, 2),
        lambda: mass(1, 1),
    ),
    Witness(
        "curvature_nonzero_witness (riemann wsq 0)",
        "InfoDiscreteRiemannCurvature_attempt.v",
        Fraction(2),
        lambda: riemann(lambda n: n * n, 0),
    ),
    Witness(
        "total_curv_wsq_2 (Gauss-Bonnet)",
        "InfoDiscreteGaussBonnet_attempt.v",
        Fraction(4),
        lambda: total_curvature(lambda n: n * n, 2),
    ),
    Witness(
        "R1212 (w=n**2, n=1)",
        "InfoMetricDerivedCurvature_attempt.v",
        Fraction(5, 4),
        lambda: R1212(lambda n: n * n, 1),
    ),
    Witness(
        "plaquette_curvature_z (commutator == a*b)",
        "InfoDiscreteRiemannCommutator_attempt.v",
        Fraction(-6, 5),
        lambda: commutator_curvature(Q(3, 5), Q(-2)),
    ),
)


def verify_theorems() -> dict[str, bool]:
    """Recompute every :data:`THEOREMS` witness; return ``{name: holds}``.

    A fully passing dict (all ``True``) certifies that this install reproduces
    the formal spine theorems bit-for-bit.
    """
    return {w.name: w.holds() for w in THEOREMS}
