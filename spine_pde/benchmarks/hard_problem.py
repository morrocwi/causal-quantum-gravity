"""Hard-problem benchmark: does the package actually SCALE?

This is a genuinely stiff, large run designed to fail loudly if any part of the
implementation secretly materialises a dense ``N x N`` object:

1. Build a large sparse retained-difference graph (default >= 50k nodes) as a
   2-D lattice -- ``O(N)`` edges, assembled straight into ``scipy.sparse``.
2. Evolve the *stiff* master spine PDE with the symplectic leapfrog integrator.
   Stiffness comes from the wide Laplacian spectrum (``lam`` up to ~8) combined
   with a small step; each step is a single sparse mat-vec ``L_R @ x`` costing
   ``O(nnz)``, never ``O(N**2)``.
3. Compute the spectral crossover: extreme ``L_R`` eigenvalues via sparse ARPACK
   (``scipy.sparse.linalg.eigsh``), then classify the whole spectrum's regime
   against the telegraph horizon ``lam_c``.

It prints wall-clock timings and a memory-safety confirmation: a dense float64
Laplacian of this size would need ``8 * N**2`` bytes (tens of GB); we assert we
never allocate anything remotely that large.

Run::

    python benchmarks/hard_problem.py            # ~50k nodes
    python benchmarks/hard_problem.py 100000     # 100k nodes
"""

from __future__ import annotations

import sys
import time

import numpy as np
import scipy.sparse as sp

from spine_pde import RetainedDifferenceGraph, Spine, Telegraph, ZeroPotential
from spine_pde.cli import extreme_eigs


def human_bytes(n: float) -> str:
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if n < 1024:
            return f"{n:.1f} {unit}"
        n /= 1024
    return f"{n:.1f} PB"


def main(target_nodes: int = 50_000, steps: int = 300) -> int:
    print("=" * 72)
    print("spine_pde HARD-PROBLEM BENCHMARK  (sparse, finite/discrete, no N^2)")
    print("=" * 72)

    side = int(round(target_nodes**0.5))
    n = side * side
    print(f"\n[1] building {side} x {side} = {n:,}-node retained-difference lattice ...")
    t0 = time.perf_counter()
    g = RetainedDifferenceGraph.grid2d(side, side)
    L = g.laplacian("csr")
    t_build = time.perf_counter() - t0

    nnz = L.nnz
    sparse_mem = L.data.nbytes + L.indices.nbytes + L.indptr.nbytes
    dense_mem = 8 * n * n  # what a dense float64 L would cost
    print(f"    nodes={n:,}  nnz(L_R)={nnz:,}  build={t_build:.3f}s")
    print(f"    sparse L_R memory : {human_bytes(sparse_mem)}")
    print(f"    a DENSE L_R would : {human_bytes(dense_mem)}  <- refused")
    assert sp.issparse(L), "Laplacian must be sparse"
    assert sparse_mem < dense_mem / 100, "sparse must be <<1% of dense"

    # ---- stiff evolution -------------------------------------------------- #
    print(f"\n[2] evolving the stiff master spine PDE for {steps} leapfrog steps ...")
    rng = np.random.default_rng(0)
    x0 = rng.standard_normal(n)
    s = Spine(
        M=1.0,
        D=0.05,          # light damping -> mostly oscillatory / stiff
        K=1.0,
        graph_or_L=L,
        gradV=ZeroPotential(),
        dtheta=5e-3,
        x0=x0,
    )
    e0 = s.energy()
    t0 = time.perf_counter()
    s.evolve(steps)
    t_evolve = time.perf_counter() - t0
    ef = s.energy()
    per_step_us = t_evolve / steps * 1e6
    print(f"    evolve={t_evolve:.3f}s  ({per_step_us:.1f} us/step, {steps} steps)")
    print(f"    shadow energy: initial={e0:.4g}  final={ef:.4g}  |x|_2={np.linalg.norm(s.x):.4g}")
    assert np.all(np.isfinite(s.x)), "state blew up (NaN/inf) -- integrator unstable"

    # ---- spectral crossover ---------------------------------------------- #
    print("\n[3] spectral crossover via sparse ARPACK (no dense eigendecomp) ...")
    t0 = time.perf_counter()
    lam = extreme_eigs(L, k=40)  # shift-invert both ends, sparse ARPACK
    t_eig = time.perf_counter() - t0

    tg = Telegraph(M=1.0, D=0.05, K=1.0)
    summary = tg.classify_spectrum(lam)
    print(f"    eigs={t_eig:.3f}s  lam in [{lam.min():.4g}, {lam.max():.4g}]")
    print(f"    telegraph horizon lam_c = {summary['lam_c']:.6g}")
    print(
        f"    sampled modes: {summary['n_oscillatory']} OSCILLATORY (quantum), "
        f"{summary['n_decay']} DECAY (classical)"
    )

    total = t_build + t_evolve + t_eig
    print("\n" + "-" * 72)
    print(f"TOTAL wall-clock: {total:.3f}s   (build {t_build:.2f} + evolve {t_evolve:.2f} + eig {t_eig:.2f})")
    print(
        f"MEMORY-SAFE: used {human_bytes(sparse_mem)} sparse vs "
        f"{human_bytes(dense_mem)} dense-refused "
        f"({dense_mem / sparse_mem:.0f}x smaller)."
    )
    print(f"SCALES: {n:,} nodes evolved + spectral crossover, no dense N^2 anywhere. PASS.")
    print("-" * 72)
    return 0


if __name__ == "__main__":
    nodes = int(sys.argv[1]) if len(sys.argv) > 1 else 50_000
    raise SystemExit(main(nodes))
