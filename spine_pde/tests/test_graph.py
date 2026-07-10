"""Retained-difference graph -> Laplacian: structure, PSD, sparsity, exact mode."""

from fractions import Fraction

import numpy as np
import scipy.sparse as sp
import scipy.sparse.linalg as spla
import pytest

from spine_pde import RetainedDifferenceGraph, adjacency_kernel, gaussian_kernel


def test_laplacian_rows_sum_to_zero():
    g = RetainedDifferenceGraph.ring(50)
    L = g.laplacian()
    row_sums = np.asarray(L.sum(axis=1)).ravel()
    assert np.allclose(row_sums, 0.0)


def test_laplacian_positive_semidefinite():
    g = RetainedDifferenceGraph.grid2d(8, 8)
    L = g.laplacian().toarray()
    evals = np.linalg.eigvalsh(0.5 * (L + L.T))
    assert evals.min() > -1e-9
    assert np.isclose(evals.min(), 0.0, atol=1e-9)   # constant null mode


def test_constant_vector_is_null_mode():
    g = RetainedDifferenceGraph.grid2d(10, 10)
    L = g.laplacian()
    ones = np.ones(L.shape[0])
    assert np.allclose(L @ ones, 0.0, atol=1e-10)


def test_path_laplacian_known_values():
    # combinatorial path on 3 nodes: L = [[1,-1,0],[-1,2,-1],[0,-1,1]]
    g = RetainedDifferenceGraph.path(3, kernel=adjacency_kernel)
    L = g.laplacian().toarray()
    expected = np.array([[1, -1, 0], [-1, 2, -1], [0, -1, 1]], dtype=float)
    assert np.allclose(L, expected)


def test_gaussian_kernel_forgets_large_difference():
    w_small = gaussian_kernel(0.0, 1.0)
    w_large = gaussian_kernel(10.0, 1.0)
    assert w_small == pytest.approx(1.0)
    assert w_large < 1e-10


def test_exact_laplacian_matches_float():
    g = RetainedDifferenceGraph.ring(5, kernel=adjacency_kernel)
    Lx = g.laplacian_exact()
    assert all(isinstance(v, Fraction) for row in Lx for v in row)
    # exact ring Laplacian: diagonal 2, off-diagonal -1 for neighbours
    assert Lx[0][0] == 2
    assert Lx[0][1] == -1
    assert Lx[0][4] == -1
    Lf = g.laplacian().toarray()
    assert np.allclose([[float(v) for v in row] for row in Lx], Lf)


def test_from_adjacency_roundtrip():
    A = sp.csr_matrix(np.array([[0, 2, 0], [2, 0, 1], [0, 1, 0]], dtype=float))
    g = RetainedDifferenceGraph.from_adjacency(A, kernel=adjacency_kernel)
    L = g.laplacian().toarray()
    assert np.allclose(L, np.array([[2, -2, 0], [-2, 3, -1], [0, -1, 1]], float))


def test_stays_sparse_and_scales():
    n = 200 * 200  # 40k nodes
    g = RetainedDifferenceGraph.grid2d(200, 200)
    L = g.laplacian()
    assert sp.issparse(L)
    assert L.shape == (n, n)
    # 4-neighbour lattice: nnz per row bounded -> O(n), nowhere near n^2
    assert L.nnz < 6 * n
    # a sparse eigen-solve for the smallest modes must succeed.
    # shift-invert (sigma=0, which="LM") instead of which="SM": plain "SM" on a
    # singular Laplacian is a documented ARPACK pathology that can iterate forever
    # on some scipy/ARPACK builds (reproduced hanging locally 2026-07-10 during the
    # release-closure audit; CI's build happened to converge). sigma is set just
    # below zero so the shifted matrix stays definite despite the exact zero mode.
    vals = spla.eigsh(L, k=3, sigma=-1e-9, which="LM",
                      return_eigenvectors=False, maxiter=5000)
    assert vals.min() < 1e-6   # zero mode present


def test_validation():
    g = RetainedDifferenceGraph(3)
    with pytest.raises(IndexError):
        g.add_edge(0, 9)
    with pytest.raises(ValueError):
        g.add_edge(1, 1)   # no self loops
    with pytest.raises(ValueError):
        RetainedDifferenceGraph(0)
