"""Spine leapfrog solver: symplectic energy behaviour, damping, forcing, scale."""

import numpy as np
import pytest

from spine_pde import (
    Quadratic,
    RetainedDifferenceGraph,
    Spine,
    Telegraph,
    ZeroPotential,
)


def _rng():
    return np.random.default_rng(0)


def test_conservative_energy_is_bounded():
    # D=0, quadratic on-site + graph coupling -> symplectic energy stays bounded
    g = RetainedDifferenceGraph.ring(64)
    x0 = _rng().standard_normal(64) * 0.1
    s = Spine(M=1.0, D=0.0, K=1.0, graph_or_L=g, gradV=Quadratic(k=1.0),
              dtheta=1e-2, x0=x0)
    e0 = s.energy()
    hist = s.evolve(4000, record=True, stride=50)
    e = hist.as_arrays()["energy"]
    # leapfrog: energy oscillates in a small O(dtheta^2) band, no secular drift.
    # Check both that the band is small AND that there is no linear drift (the
    # symplectic property: a non-symplectic Euler scheme would drift instead).
    assert np.max(np.abs(e - e0)) / abs(e0) < 1e-2
    first_half = np.mean(e[: len(e) // 2])
    second_half = np.mean(e[len(e) // 2 :])
    assert abs(second_half - first_half) / abs(e0) < 2e-3


def test_damping_dissipates_energy():
    g = RetainedDifferenceGraph.ring(32)
    x0 = _rng().standard_normal(32) * 0.5
    s = Spine(M=1.0, D=0.5, K=1.0, graph_or_L=g, gradV=Quadratic(k=1.0),
              dtheta=1e-2, x0=x0)
    e0 = s.energy()
    s.evolve(6000)
    assert s.energy() < 0.05 * e0     # relaxes toward the minimum


def test_single_mode_matches_telegraph_regime():
    # project onto one Laplacian eigenvector; under-damped -> oscillates (sign flips)
    g = RetainedDifferenceGraph.ring(16, kernel=None)
    from spine_pde.graph import adjacency_kernel
    g = RetainedDifferenceGraph.ring(16, kernel=adjacency_kernel)
    L = g.laplacian().toarray()
    evals, evecs = np.linalg.eigh(L)
    lam = evals[-1]                    # largest mode -> most oscillatory
    vec = evecs[:, -1]
    M, D, K = 1.0, 0.2, 1.0
    tg = Telegraph(M, D, K)
    assert "OSCILLATORY" in tg.regime(lam)
    s = Spine(M=M, D=D, K=K, graph_or_L=g, gradV=ZeroPotential(),
              dtheta=5e-3, x0=vec.copy())
    amp = s.x @ vec
    signs = []
    for _ in range(4000):
        s.step()
        signs.append(np.sign(s.x @ vec))
    # oscillatory mode must cross zero (sign changes) at least twice
    changes = np.count_nonzero(np.diff(signs) != 0)
    assert changes >= 2


def test_overdamped_mode_decays_without_oscillation():
    from spine_pde.graph import adjacency_kernel
    g = RetainedDifferenceGraph.ring(16, kernel=adjacency_kernel)
    L = g.laplacian().toarray()
    evals, evecs = np.linalg.eigh(L)
    # pick smallest nonzero mode with huge damping -> over-damped decay
    lam = evals[1]
    vec = evecs[:, 1]
    M, D, K = 1.0, 20.0, 1.0
    tg = Telegraph(M, D, K)
    assert "DECAY" in tg.regime(lam)
    s = Spine(M=M, D=D, K=K, graph_or_L=g, gradV=ZeroPotential(),
              dtheta=1e-3, x0=vec.copy())
    a0 = abs(s.x @ vec)
    proj = []
    for _ in range(2000):
        s.step()
        proj.append(s.x @ vec)
    # monotone-ish decay: no sign change, amplitude shrinks
    assert np.count_nonzero(np.diff(np.sign(proj)) != 0) == 0
    assert abs(proj[-1]) < a0


def test_constant_forcing_shifts_equilibrium():
    g = RetainedDifferenceGraph.ring(8)
    J = np.full(8, 0.3)
    s = Spine(M=1.0, D=1.0, K=1.0, graph_or_L=g, gradV=Quadratic(k=1.0),
              J=J, dtheta=1e-2, x0=np.zeros(8))
    s.evolve(8000)
    # equilibrium of quadratic well under uniform forcing: x* = J/k = 0.3
    assert np.allclose(s.x, 0.3, atol=1e-2)


def test_callable_forcing_runs():
    g = RetainedDifferenceGraph.path(10)
    J = lambda x, theta: 0.1 * np.sin(theta) * np.ones_like(x)
    s = Spine(M=1.0, D=0.1, K=1.0, graph_or_L=g, J=J, dtheta=1e-2)
    s.evolve(100)
    assert np.all(np.isfinite(s.x))


def test_scales_to_large_sparse_graph():
    g = RetainedDifferenceGraph.grid2d(200, 200)   # 40k nodes
    s = Spine(M=1.0, D=0.1, K=1.0, graph_or_L=g, gradV=ZeroPotential(),
              dtheta=1e-2, x0=_rng().standard_normal(40000) * 0.01)
    assert s.L_R.nnz < 6 * s.n           # stayed sparse
    s.evolve(20)                          # steps are O(nnz)
    assert np.all(np.isfinite(s.x))


def test_validation():
    g = RetainedDifferenceGraph.ring(4)
    with pytest.raises(ValueError):
        Spine(M=0.0, D=1.0, K=1.0, graph_or_L=g)      # M must be > 0
    with pytest.raises(ValueError):
        Spine(M=1.0, D=1.0, K=1.0, graph_or_L=g, dtheta=0)
    with pytest.raises(ValueError):
        Spine(M=1.0, D=1.0, K=1.0, graph_or_L=g, x0=np.zeros(3))  # wrong length
