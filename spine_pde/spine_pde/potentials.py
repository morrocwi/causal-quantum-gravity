"""On-site potentials ``V(x)`` and their gradients ``gradV(x)``.

The master spine equation carries a local potential term ``gradV(x)`` acting
node-by-node.  A potential is represented as a small object exposing

    grad(x) -> array      (the force -dV/dx, entering the PDE as +gradV)
    energy(x) -> float    (sum_i V(x_i), for the conserved-energy diagnostic)

The default is the symmetric double well ``V(x) = (x**2 - 1)**2 / 4`` whose two
minima ``x = +-1`` are the classic bistable readout states of the theory.
"""

from __future__ import annotations

from typing import Callable, Protocol

import numpy as np

__all__ = ["Potential", "DoubleWell", "Quadratic", "ZeroPotential", "as_potential"]


class Potential(Protocol):
    """Structural type for on-site potentials."""

    def grad(self, x: np.ndarray) -> np.ndarray: ...

    def energy(self, x: np.ndarray) -> float: ...


class ZeroPotential:
    """No on-site potential (pure graph dynamics)."""

    def grad(self, x: np.ndarray) -> np.ndarray:
        return np.zeros_like(np.asarray(x, dtype=float))

    def energy(self, x: np.ndarray) -> float:
        return 0.0


class Quadratic:
    """Harmonic well ``V(x) = 0.5 * k * (x - x0)**2``."""

    def __init__(self, k: float = 1.0, x0: float = 0.0) -> None:
        self.k = float(k)
        self.x0 = float(x0)

    def grad(self, x: np.ndarray) -> np.ndarray:
        x = np.asarray(x, dtype=float)
        return self.k * (x - self.x0)

    def energy(self, x: np.ndarray) -> float:
        x = np.asarray(x, dtype=float)
        return float(0.5 * self.k * np.sum((x - self.x0) ** 2))


class DoubleWell:
    """Symmetric quartic double well ``V(x) = a * (x**2 - b**2)**2``.

    Default ``a = 1/4, b = 1`` gives ``V = (x**2 - 1)**2 / 4`` and force
    ``gradV = x**3 - x`` with minima at ``x = +-1``.
    """

    def __init__(self, a: float = 0.25, b: float = 1.0) -> None:
        self.a = float(a)
        self.b = float(b)

    def grad(self, x: np.ndarray) -> np.ndarray:
        x = np.asarray(x, dtype=float)
        # dV/dx = 4 a (x^2 - b^2) x
        return 4.0 * self.a * (x**2 - self.b**2) * x

    def energy(self, x: np.ndarray) -> float:
        x = np.asarray(x, dtype=float)
        return float(self.a * np.sum((x**2 - self.b**2) ** 2))


def as_potential(obj: object) -> Potential:
    """Coerce ``None`` / a plain callable / a :class:`Potential` into a Potential.

    A bare callable is treated as ``gradV`` with an unknown energy (reported as
    ``nan`` so the energy diagnostic stays honest rather than silently wrong).
    """
    if obj is None:
        return DoubleWell()
    if hasattr(obj, "grad") and hasattr(obj, "energy"):
        return obj  # type: ignore[return-value]
    if callable(obj):
        return _CallableGrad(obj)
    raise TypeError(f"cannot interpret {obj!r} as a potential")


class _CallableGrad:
    def __init__(self, grad: Callable[[np.ndarray], np.ndarray]) -> None:
        self._grad = grad

    def grad(self, x: np.ndarray) -> np.ndarray:
        return np.asarray(self._grad(np.asarray(x, dtype=float)), dtype=float)

    def energy(self, x: np.ndarray) -> float:
        return float("nan")
