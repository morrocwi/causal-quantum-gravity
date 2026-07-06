"""Telegraph regime analysis of the spine, per ``L_R`` eigenmode.

Projecting the master equation onto an eigenmode of ``L_R`` with eigenvalue
``lam`` gives the scalar telegraph oscillator

    M w'' + D w' + K lam w = 0 ,

whose characteristic polynomial ``M s**2 + D s + K lam`` has discriminant

    disc(lam) = D**2 - 4 M K lam .

The sign of ``disc`` sorts every mode into a regime, with the crossover at

    lam_c = D**2 / (4 M K) .

* ``disc > 0``  (``lam < lam_c``): over-damped -> **DECAY** (classical readout).
* ``disc < 0``  (``lam > lam_c``): under-damped -> **OSCILLATORY** (quantum readout).
* ``disc == 0`` (``lam == lam_c``): critically damped -- the horizon / agency
  knife-edge separating the two.

Derived readouts:

    mass  = D / (2 M) = 1 / (2 tau_c)      (decay rate of the envelope)
    tau_c = M / D                          (correlation time)
    Gamma(lam) = K lam / D                 (mode decoherence rate)

Both an **exact** rational path (:class:`fractions.Fraction`) that matches the
Coq telegraph theorems bit-for-bit and a **float** path (vectorised over an
array of eigenvalues) are provided.
"""

from __future__ import annotations

from fractions import Fraction
from numbers import Rational
from typing import Union

import numpy as np

__all__ = ["Telegraph", "OSCILLATORY", "DECAY", "CRITICAL"]

OSCILLATORY = "under-damped/OSCILLATORY"  # quantum
DECAY = "over-damped/DECAY"  # classical
CRITICAL = "critically-damped/HORIZON"  # knife-edge

Number = Union[int, float, Fraction]


def _is_exact(*vals: object) -> bool:
    return all(isinstance(v, (int, Rational, Fraction)) for v in vals)


def _coerce_exact(v: Number) -> Fraction:
    return v if isinstance(v, Fraction) else Fraction(v)


class Telegraph:
    """Telegraph / horizon analyser for coefficients ``(M, D, K)``.

    Parameters
    ----------
    M, D, K:
        Inertia, damping and stiffness.  ``M > 0`` and ``K > 0`` are required so
        the crossover ``lam_c`` is well defined.  Pass Python ``int`` /
        :class:`~fractions.Fraction` for exact rational arithmetic; pass floats
        for the fast path.
    exact:
        ``None`` (default) auto-selects exact iff all three coefficients are
        exact rationals; ``True`` / ``False`` force the mode.
    """

    def __init__(self, M: Number, D: Number, K: Number, exact: bool | None = None) -> None:
        if float(M) <= 0:
            raise ValueError("M must be positive")
        if float(K) <= 0:
            raise ValueError("K must be positive")
        self.exact = _is_exact(M, D, K) if exact is None else bool(exact)
        if self.exact:
            self.M, self.D, self.K = map(_coerce_exact, (M, D, K))
        else:
            self.M, self.D, self.K = float(M), float(D), float(K)

    # -- scalar / exact-capable readouts ----------------------------------- #

    def discriminant(self, lam: Number) -> Number:
        """``disc(lam) = D**2 - 4 M K lam`` (exact if the analyser is exact)."""
        if self.exact:
            lam = _coerce_exact(lam)
        return self.D * self.D - 4 * self.M * self.K * lam

    def crossover(self) -> Number:
        """Critical eigenvalue ``lam_c = D**2 / (4 M K)``."""
        return (self.D * self.D) / (4 * self.M * self.K)

    def regime(self, lam: Number) -> str:
        """Classify mode ``lam`` as :data:`OSCILLATORY`, :data:`DECAY` or :data:`CRITICAL`."""
        disc = self.discriminant(lam)
        if disc < 0:
            return OSCILLATORY
        if disc > 0:
            return DECAY
        return CRITICAL

    def mass(self) -> Number:
        """Envelope decay rate ``mass = D / (2 M) = 1 / (2 tau_c)``."""
        return self.D / (2 * self.M)

    def tau_c(self) -> Number:
        """Correlation time ``tau_c = M / D`` (``inf`` if ``D == 0``)."""
        if float(self.D) == 0:
            return float("inf")
        return self.M / self.D

    def decoherence_rate(self, lam: Number) -> Number:
        """Mode decoherence rate ``Gamma(lam) = K lam / D`` (``inf`` if ``D == 0``)."""
        if self.exact:
            lam = _coerce_exact(lam)
        if float(self.D) == 0:
            return float("inf")
        return self.K * lam / self.D

    def roots(self, lam: Number) -> tuple[complex, complex]:
        """The two characteristic roots ``s = (-D +- sqrt(disc)) / (2 M)`` (float)."""
        M, D = float(self.M), float(self.D)
        disc = float(self.discriminant(lam))
        sq = np.lib.scimath.sqrt(disc)  # complex when disc < 0
        return ((-D + sq) / (2 * M), (-D - sq) / (2 * M))

    # -- vectorised float readouts (many modes at once) -------------------- #

    def discriminant_array(self, lam: np.ndarray) -> np.ndarray:
        """Vectorised ``disc`` over an array of eigenvalues (float)."""
        lam = np.asarray(lam, dtype=float)
        return float(self.D) ** 2 - 4 * float(self.M) * float(self.K) * lam

    def regime_array(self, lam: np.ndarray) -> np.ndarray:
        """Vectorised regime labels (object array of strings)."""
        disc = self.discriminant_array(lam)
        out = np.where(disc < 0, OSCILLATORY, np.where(disc > 0, DECAY, CRITICAL))
        return out

    def classify_spectrum(self, lam: np.ndarray) -> dict[str, np.ndarray]:
        """Summarise a whole spectrum: masks, decoherence rates and counts.

        Handy for a Laplacian with ``10**4``+ eigenvalues from
        :func:`scipy.sparse.linalg.eigsh` -- purely vectorised.
        """
        lam = np.asarray(lam, dtype=float)
        disc = self.discriminant_array(lam)
        D = float(self.D)
        gamma = np.full_like(lam, np.inf) if D == 0 else float(self.K) * lam / D
        osc = disc < 0
        dec = disc > 0
        return {
            "lam": lam,
            "disc": disc,
            "oscillatory": osc,
            "decay": dec,
            "critical": ~(osc | dec),
            "decoherence_rate": gamma,
            "n_oscillatory": int(np.count_nonzero(osc)),
            "n_decay": int(np.count_nonzero(dec)),
            "lam_c": float(self.crossover()),
        }

    def __repr__(self) -> str:  # pragma: no cover - cosmetic
        mode = "exact" if self.exact else "float"
        return f"Telegraph(M={self.M}, D={self.D}, K={self.K}, mode={mode})"
