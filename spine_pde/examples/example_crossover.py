"""example_crossover.py -- the quantum <-> classical regime flip at the horizon.

Project the master spine PDE onto an ``L_R`` eigenmode ``lam`` and it becomes the
scalar telegraph oscillator ``M w'' + D w' + K lam w = 0``.  Its discriminant

    disc(lam) = D**2 - 4 M K lam

flips sign at the critical eigenvalue ``lam_c = D**2 / (4 M K)``:

    lam < lam_c  ->  disc > 0  ->  over-damped  DECAY        (classical readout)
    lam = lam_c  ->  disc = 0  ->  critically damped HORIZON  (the knife-edge)
    lam > lam_c  ->  disc < 0  ->  under-damped OSCILLATORY   (quantum readout)

We build a real retained-difference graph, read its spectrum, and sweep ``lam``
straight across ``lam_c`` to watch the regime flip.  The exact-rational path
confirms the crossover is bit-for-bit ``disc(lam_c) == 0`` -- no float slop at
the horizon.

Run:  python examples/example_crossover.py
"""

from __future__ import annotations

import numpy as np
import scipy.sparse.linalg as spla

from spine_pde import RetainedDifferenceGraph, Telegraph, exact


def main() -> None:
    M, D, K = 1.0, 1.0, 1.0
    tg = Telegraph(M, D, K)
    lam_c = tg.crossover()
    print(f"coefficients  M={M}  D={D}  K={K}")
    print(f"crossover     lam_c = D^2/(4 M K) = {lam_c:.6f}")
    print(f"mass = D/2M   = {tg.mass():.6f}   tau_c = M/D = {tg.tau_c():.6f}")
    print()

    # --- 1. sweep lam straight across the horizon ------------------------- #
    print("sweep of a single mode across the horizon:")
    print(f"  {'lam':>10}  {'disc':>12}   regime")
    for lam in np.linspace(0.5 * lam_c, 1.5 * lam_c, 7):
        disc = tg.discriminant(lam)
        print(f"  {lam:>10.4f}  {disc:>12.5f}   {tg.regime(lam)}")
    print()

    # --- 2. exact confirmation at the knife-edge -------------------------- #
    exM, exD, exK = 1, 1, 1  # ints -> exact rationals over Q
    lam_c_exact = exact.crossover(exM, exD, exK)
    print("exact-rational horizon (matches the Coq telegraph theorem):")
    print(f"  lam_c (exact)        = {lam_c_exact}   (= 1/4)")
    print(f"  disc(lam_c) (exact)  = {exact.discriminant(exM, exD, exK, lam_c_exact)}"
          "   (critical_disc_zero: == 0)")
    print(f"  regime at lam_c      = {exact.regime(exM, exD, exK, lam_c_exact)}")
    print(f"  disc(1,1,1,1) exact  = {exact.discriminant(1, 1, 1, 1)}"
          "   (underdamped_witness: == -3, quantum)")
    print()

    # --- 3. the flip over a genuine graph spectrum ------------------------ #
    g = RetainedDifferenceGraph.grid2d(60, 60)  # 3600 nodes, sparse L_R
    L = g.laplacian()
    # a spread of eigenvalues from near-zero (smooth) to the spectral top.
    lam_lo = spla.eigsh(L, k=6, which="SM", return_eigenvectors=False)
    lam_hi = spla.eigsh(L, k=6, which="LM", return_eigenvectors=False)
    spectrum = np.concatenate([lam_lo, lam_hi])
    info = tg.classify_spectrum(spectrum)
    print(f"graph: {L.shape[0]} nodes, nnz(L_R)={L.nnz}")
    print(f"  smallest lam ~ {spectrum.min():.4f} (< lam_c -> classical DECAY)")
    print(f"  largest  lam ~ {spectrum.max():.4f} (> lam_c -> quantum OSCILLATORY)")
    print(f"  oscillatory/quantum modes : {info['n_oscillatory']} / {spectrum.size}")
    print(f"  decay/classical    modes : {info['n_decay']} / {spectrum.size}")
    print("\nThe same spine reads out as classical below lam_c and quantum above it;")
    print("lam_c is the horizon / agency knife-edge where disc == 0 exactly.")


if __name__ == "__main__":
    main()
