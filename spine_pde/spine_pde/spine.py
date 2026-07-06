"""The master spine PDE and its symplectic leapfrog integrator.

The discrete tensor-field master equation (all finite, no continuum):

    M x'' + D x' + K L_R x + gradV(x) = J - eta

with node states ``x`` (length ``n``), inertia ``M``, damping ``D``, graph
stiffness ``K``, the retained-difference Laplacian ``L_R`` (sparse, ``n x n``),
an on-site force ``gradV``, external forcing ``J`` and a dissipation/agency
draw ``eta``.

It is evolved with the leapfrog / semi-implicit-Euler symplectic scheme

    V[n+1] = V[n] + dtheta * ( -(D/M) V[n] - (K/M) L_R x[n] - gradV(x[n])/M + (J - eta)/M )
    x[n+1] = x[n] + dtheta * V[n+1]

which is the exact update named in the theory.  With ``D = 0`` and no forcing
the scheme conserves the shadow energy to O(dtheta**2), giving a faithful
symplectic readout of the conservative spine.

The single matrix operation per step is the sparse mat-vec ``L_R @ x``, so a
step costs O(nnz(L_R)) and the solver scales to ``10**4``-``10**5`` nodes.
"""

from __future__ import annotations

from typing import Callable

import numpy as np
import scipy.sparse as sp

from .graph import RetainedDifferenceGraph
from .potentials import Potential, as_potential

__all__ = ["Spine", "SpineHistory"]


def _as_laplacian(graph_or_L: object, n_hint: int | None = None) -> sp.spmatrix:
    """Accept a graph, a sparse matrix or a dense array; return sparse CSR ``L_R``."""
    if isinstance(graph_or_L, RetainedDifferenceGraph):
        return graph_or_L.laplacian("csr")
    if sp.issparse(graph_or_L):
        return graph_or_L.tocsr()
    L = np.asarray(graph_or_L, dtype=float)
    if L.ndim != 2 or L.shape[0] != L.shape[1]:
        raise ValueError("L_R must be a square matrix")
    return sp.csr_matrix(L)


class SpineHistory:
    """Recorded trajectory returned by :meth:`Spine.evolve` when ``record=True``."""

    def __init__(self) -> None:
        self.theta: list[float] = []
        self.x: list[np.ndarray] = []
        self.v: list[np.ndarray] = []
        self.energy: list[float] = []

    def _push(self, theta: float, x: np.ndarray, v: np.ndarray, e: float) -> None:
        self.theta.append(theta)
        self.x.append(x.copy())
        self.v.append(v.copy())
        self.energy.append(e)

    def as_arrays(self) -> dict[str, np.ndarray]:
        """Return the history as stacked numpy arrays."""
        return {
            "theta": np.asarray(self.theta),
            "x": np.asarray(self.x),
            "v": np.asarray(self.v),
            "energy": np.asarray(self.energy),
        }


class Spine:
    """Solver for the discrete master spine PDE.

    Parameters
    ----------
    M, D, K:
        Inertia, damping and graph-stiffness coefficients.  Scalars, or length
        ``n`` arrays for per-node (diagonal-tensor) values.  ``M > 0``.
    graph_or_L:
        A :class:`~spine_pde.graph.RetainedDifferenceGraph`, a scipy sparse
        matrix, or a dense array giving the Laplacian ``L_R``.
    gradV:
        A :class:`~spine_pde.potentials.Potential`, a bare callable ``x ->
        force``, or ``None`` for the default double well.
    J:
        External forcing: a length-``n`` array, a scalar, or a callable
        ``J(x, theta) -> array``.  Defaults to zero.
    eta:
        Dissipation / agency draw, same forms as ``J``.  Enters as ``-eta``.
    dtheta:
        Integrator step in the internal ``theta`` time.
    x0, v0:
        Initial state and rate (default zeros / small).
    """

    def __init__(
        self,
        M: float | np.ndarray,
        D: float | np.ndarray,
        K: float | np.ndarray,
        graph_or_L: object,
        gradV: Potential | Callable[[np.ndarray], np.ndarray] | None = None,
        J: float | np.ndarray | Callable[[np.ndarray, float], np.ndarray] = 0.0,
        eta: float | np.ndarray | Callable[[np.ndarray, float], np.ndarray] = 0.0,
        dtheta: float = 1e-2,
        x0: np.ndarray | None = None,
        v0: np.ndarray | None = None,
    ) -> None:
        self.L_R = _as_laplacian(graph_or_L)
        self.n = self.L_R.shape[0]

        self.M = self._coerce_coeff(M, "M", positive=True)
        self.D = self._coerce_coeff(D, "D")
        self.K = self._coerce_coeff(K, "K")
        if dtheta <= 0:
            raise ValueError("dtheta must be positive")
        self.dtheta = float(dtheta)

        self.potential = as_potential(gradV)
        self._J = J
        self._eta = eta

        self.theta = 0.0
        self.x = self._coerce_state(x0, "x0", default=0.0)
        self.v = self._coerce_state(v0, "v0", default=0.0)

    # -- coercion helpers --------------------------------------------------- #

    def _coerce_coeff(self, val: float | np.ndarray, name: str, positive: bool = False) -> np.ndarray:
        arr = np.asarray(val, dtype=float)
        if arr.ndim == 0:
            arr = np.full(self.n, float(arr))
        elif arr.shape != (self.n,):
            raise ValueError(f"{name} must be scalar or length {self.n}")
        if positive and np.any(arr <= 0):
            raise ValueError(f"{name} must be strictly positive")
        return arr

    def _coerce_state(self, val: np.ndarray | None, name: str, default: float) -> np.ndarray:
        if val is None:
            return np.full(self.n, float(default))
        arr = np.asarray(val, dtype=float).ravel()
        if arr.shape != (self.n,):
            raise ValueError(f"{name} must have length {self.n}")
        return arr.copy()

    def _eval_source(self, src, x: np.ndarray, theta: float) -> np.ndarray:
        if callable(src):
            return np.asarray(src(x, theta), dtype=float)
        arr = np.asarray(src, dtype=float)
        if arr.ndim == 0:
            return np.full(self.n, float(arr))
        if arr.shape != (self.n,):
            raise ValueError("forcing term has wrong length")
        return arr

    # -- dynamics ----------------------------------------------------------- #

    def acceleration(self, x: np.ndarray, v: np.ndarray, theta: float) -> np.ndarray:
        """Right-hand side ``x'' = (J - eta - D v - K L_R x - gradV(x)) / M``."""
        J = self._eval_source(self._J, x, theta)
        eta = self._eval_source(self._eta, x, theta)
        force = (
            J
            - eta
            - self.D * v
            - self.K * (self.L_R @ x)
            - self.potential.grad(x)
        )
        return force / self.M

    def step(self) -> "Spine":
        """Advance one leapfrog step (velocity first, then position)."""
        a = self.acceleration(self.x, self.v, self.theta)
        self.v = self.v + self.dtheta * a
        self.x = self.x + self.dtheta * self.v
        self.theta += self.dtheta
        return self

    def evolve(self, n_steps: int, record: bool = False, stride: int = 1) -> SpineHistory | None:
        """Advance ``n_steps`` steps.

        If ``record`` is true, snapshots every ``stride`` steps (plus the
        initial state) are returned in a :class:`SpineHistory`.
        """
        if n_steps < 0:
            raise ValueError("n_steps must be non-negative")
        hist: SpineHistory | None = None
        if record:
            hist = SpineHistory()
            hist._push(self.theta, self.x, self.v, self.energy())
        for k in range(1, n_steps + 1):
            self.step()
            if hist is not None and (k % stride == 0):
                hist._push(self.theta, self.x, self.v, self.energy())
        return hist

    # -- diagnostics -------------------------------------------------------- #

    def kinetic_energy(self) -> float:
        """``0.5 * sum_i M_i v_i**2``."""
        return float(0.5 * np.sum(self.M * self.v**2))

    def graph_energy(self) -> float:
        """Dirichlet form ``0.5 * K_bar * x^T L_R x`` (K averaged if per-node)."""
        Kbar = float(np.mean(self.K))
        return float(0.5 * Kbar * (self.x @ (self.L_R @ self.x)))

    def potential_energy(self) -> float:
        """On-site potential energy ``sum_i V(x_i)`` (nan if gradV is a bare callable)."""
        return self.potential.energy(self.x)

    def energy(self) -> float:
        """Total shadow energy: kinetic + graph (Dirichlet) + on-site potential."""
        return self.kinetic_energy() + self.graph_energy() + self.potential_energy()

    def state(self) -> tuple[np.ndarray, np.ndarray]:
        """Return copies of the current ``(x, v)``."""
        return self.x.copy(), self.v.copy()

    def __repr__(self) -> str:  # pragma: no cover - cosmetic
        return (
            f"Spine(n={self.n}, dtheta={self.dtheta}, theta={self.theta:.4g}, "
            f"nnz(L_R)={self.L_R.nnz})"
        )
