"""Quick start: build a graph, evolve the spine, read the telegraph regimes.

Run:  python examples/quickstart.py
"""

import numpy as np

from spine_pde import RetainedDifferenceGraph, Spine, Telegraph


def main() -> None:
    # 1. A retained-difference graph -> sparse Laplacian L_R.
    g = RetainedDifferenceGraph.grid2d(50, 50)          # 2500 nodes
    L = g.laplacian()
    print(f"graph: {L.shape[0]} nodes, nnz(L_R)={L.nnz}")

    # 2. Evolve the master spine PDE with a random initial condition.
    rng = np.random.default_rng(0)
    x0 = rng.standard_normal(L.shape[0]) * 0.1
    spine = Spine(M=1.0, D=0.2, K=1.0, graph_or_L=g, gradV=None, x0=x0)  # double-well default
    e_start = spine.energy()
    spine.evolve(2000)
    print(f"energy: {e_start:.4f} -> {spine.energy():.4f} (damped relaxation)")

    # 3. Telegraph regime analysis over the spectrum.
    import scipy.sparse.linalg as spla

    lam = spla.eigsh(L, k=20, which="LM", return_eigenvectors=False)
    tg = Telegraph(1.0, 0.2, 1.0)
    info = tg.classify_spectrum(lam)
    print(f"crossover lam_c = {info['lam_c']:.4f}")
    print(f"oscillatory (quantum) modes: {info['n_oscillatory']} / {lam.size}")
    print(f"decay (classical) modes:     {info['n_decay']} / {lam.size}")


if __name__ == "__main__":
    main()
