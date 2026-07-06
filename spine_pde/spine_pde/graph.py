"""Retained-difference graph -> sparse graph Laplacian ``L_R``.

The theory begins from a *retained-difference* (RD) graph: nodes carry states
``x_i`` and every retained edge ``(i, j)`` carries an information difference
``dI_ij`` and an address / adjacency weight ``A_ij``.  A kernel

    W_ij = K(dI_ij, A_ij)

turns those into edge weights, from which the (symmetric, combinatorial) graph
Laplacian is

    L_R = D_W - W ,   D_W = diag(sum_j W_ij).

``L_R`` is the discrete root operator of the whole spine field theory: it is
positive semi-definite, its constant vector is a null mode, and its eigenvalues
``lam`` drive the telegraph regime analysis (see :mod:`spine_pde.telegraph`).

Everything here is finite/discrete -- there is no continuum limit.  For large
problems the Laplacian is assembled directly as a :mod:`scipy.sparse` matrix so
that ``10**4``-``10**5`` node graphs cost O(nnz) memory, never O(n**2).
"""

from __future__ import annotations

from fractions import Fraction
from typing import Callable, Iterable, Sequence

import numpy as np
import scipy.sparse as sp

__all__ = [
    "gaussian_kernel",
    "adjacency_kernel",
    "RetainedDifferenceGraph",
]

# --------------------------------------------------------------------------- #
# Edge kernels W_ij = K(dI_ij, A_ij)
# --------------------------------------------------------------------------- #


def gaussian_kernel(dI: np.ndarray, A: np.ndarray, sigma: float = 1.0) -> np.ndarray:
    """Default kernel: ``A * exp(-dI**2 / (2 sigma**2))``.

    Large information differences are exponentially *forgotten* (retained less);
    ``A`` scales the raw address strength.  ``sigma > 0`` sets the retention
    length-scale.
    """
    if sigma <= 0:
        raise ValueError("sigma must be positive")
    dI = np.asarray(dI, dtype=float)
    A = np.asarray(A, dtype=float)
    return A * np.exp(-(dI**2) / (2.0 * sigma**2))


def adjacency_kernel(dI: np.ndarray, A: np.ndarray) -> np.ndarray:
    """Pure combinatorial kernel ``W_ij = A_ij`` (ignores ``dI``).

    Recovers the textbook combinatorial Laplacian and is exact-rational capable
    when ``A`` is rational.
    """
    return np.asarray(A, dtype=float)


# --------------------------------------------------------------------------- #
# The graph
# --------------------------------------------------------------------------- #


class RetainedDifferenceGraph:
    """A retained-difference graph that emits a sparse Laplacian ``L_R``.

    Parameters
    ----------
    n_nodes:
        Number of nodes.
    kernel:
        Callable ``K(dI, A) -> W`` applied elementwise to the stored edge
        arrays.  Defaults to :func:`gaussian_kernel`.

    Notes
    -----
    Edges are accumulated in coordinate (COO) triplet lists and only
    materialised into a CSR matrix on demand, so assembly is O(edges).
    """

    def __init__(
        self,
        n_nodes: int,
        kernel: Callable[[np.ndarray, np.ndarray], np.ndarray] | None = None,
    ) -> None:
        if n_nodes <= 0:
            raise ValueError("n_nodes must be positive")
        self.n_nodes = int(n_nodes)
        self.kernel = kernel if kernel is not None else gaussian_kernel
        self._rows: list[int] = []
        self._cols: list[int] = []
        self._dI: list[float] = []
        self._A: list[float] = []

    # -- construction ------------------------------------------------------- #

    def add_edge(
        self,
        i: int,
        j: int,
        dI: float = 0.0,
        A: float = 1.0,
        symmetric: bool = True,
    ) -> "RetainedDifferenceGraph":
        """Add a retained edge ``(i, j)`` with difference ``dI`` and address ``A``."""
        if not (0 <= i < self.n_nodes and 0 <= j < self.n_nodes):
            raise IndexError(f"node index out of range: ({i}, {j})")
        if i == j:
            raise ValueError("self-loops are not retained edges")
        self._rows.append(i)
        self._cols.append(j)
        self._dI.append(float(dI))
        self._A.append(float(A))
        if symmetric:
            self._rows.append(j)
            self._cols.append(i)
            self._dI.append(float(dI))
            self._A.append(float(A))
        return self

    def add_edges(
        self, edges: Iterable[Sequence[float]], symmetric: bool = True
    ) -> "RetainedDifferenceGraph":
        """Add many edges. Each item is ``(i, j)``, ``(i, j, dI)`` or ``(i, j, dI, A)``."""
        for e in edges:
            i, j = int(e[0]), int(e[1])
            dI = float(e[2]) if len(e) > 2 else 0.0
            A = float(e[3]) if len(e) > 3 else 1.0
            self.add_edge(i, j, dI, A, symmetric=symmetric)
        return self

    @property
    def n_edges(self) -> int:
        """Number of stored directed triplets."""
        return len(self._rows)

    # -- matrices ----------------------------------------------------------- #

    def weight_matrix(self, format: str = "csr") -> sp.spmatrix:
        """Sparse symmetric weight matrix ``W`` (duplicate triplets summed)."""
        if not self._rows:
            return sp.csr_matrix((self.n_nodes, self.n_nodes))
        w = self.kernel(np.asarray(self._dI), np.asarray(self._A))
        W = sp.coo_matrix(
            (np.asarray(w, dtype=float), (self._rows, self._cols)),
            shape=(self.n_nodes, self.n_nodes),
        )
        return W.asformat(format)

    def degree(self) -> np.ndarray:
        """Weighted degree vector ``D_W`` (row sums of ``W``)."""
        W = self.weight_matrix("csr")
        return np.asarray(W.sum(axis=1)).ravel()

    def laplacian(self, format: str = "csr") -> sp.spmatrix:
        """Sparse graph Laplacian ``L_R = D_W - W``.

        Positive semi-definite; ``L_R @ ones == 0`` up to round-off.
        """
        W = self.weight_matrix("csr")
        d = np.asarray(W.sum(axis=1)).ravel()
        L = sp.diags(d) - W
        return L.asformat(format)

    def laplacian_exact(self) -> list[list[Fraction]]:
        """Exact rational Laplacian as nested :class:`~fractions.Fraction` lists.

        Uses the *combinatorial* kernel ``W_ij = A_ij`` so the result is exact
        and matches the Coq combinatorial-Laplacian theorems bit-for-bit.  For
        small graphs only.
        """
        n = self.n_nodes
        W = [[Fraction(0) for _ in range(n)] for _ in range(n)]
        for i, j, A in zip(self._rows, self._cols, self._A):
            W[i][j] += Fraction(A).limit_denominator()
        L = [[-W[i][j] for j in range(n)] for i in range(n)]
        for i in range(n):
            L[i][i] = sum(W[i])
        return L

    # -- convenience constructors ------------------------------------------ #

    @classmethod
    def from_adjacency(
        cls,
        A: sp.spmatrix | np.ndarray,
        dI: sp.spmatrix | np.ndarray | None = None,
        kernel: Callable[[np.ndarray, np.ndarray], np.ndarray] | None = None,
    ) -> "RetainedDifferenceGraph":
        """Build from an adjacency matrix ``A`` (and optional ``dI`` matrix)."""
        A = sp.coo_matrix(A)
        g = cls(A.shape[0], kernel=kernel)
        if dI is not None:
            dI = sp.coo_matrix(dI).tocsr()
        for i, j, a in zip(A.row, A.col, A.data):
            if i == j:
                continue
            d = float(dI[i, j]) if dI is not None else 0.0
            g.add_edge(int(i), int(j), dI=d, A=float(a), symmetric=False)
        return g

    @classmethod
    def path(cls, n: int, A: float = 1.0, **kw) -> "RetainedDifferenceGraph":
        """1-D path graph on ``n`` nodes."""
        g = cls(n, **kw)
        for i in range(n - 1):
            g.add_edge(i, i + 1, A=A)
        return g

    @classmethod
    def ring(cls, n: int, A: float = 1.0, **kw) -> "RetainedDifferenceGraph":
        """Ring (cycle) graph on ``n`` nodes."""
        g = cls(n, **kw)
        for i in range(n):
            g.add_edge(i, (i + 1) % n, A=A)
        return g

    @classmethod
    def grid2d(cls, rows: int, cols: int, A: float = 1.0, **kw) -> "RetainedDifferenceGraph":
        """2-D lattice graph (4-neighbour) on ``rows*cols`` nodes."""
        g = cls(rows * cols, **kw)

        def idx(r: int, c: int) -> int:
            return r * cols + c

        for r in range(rows):
            for c in range(cols):
                if c + 1 < cols:
                    g.add_edge(idx(r, c), idx(r, c + 1), A=A)
                if r + 1 < rows:
                    g.add_edge(idx(r, c), idx(r + 1, c), A=A)
        return g

    def __repr__(self) -> str:  # pragma: no cover - cosmetic
        return (
            f"RetainedDifferenceGraph(n_nodes={self.n_nodes}, "
            f"n_edges={self.n_edges}, kernel={getattr(self.kernel, '__name__', self.kernel)})"
        )
