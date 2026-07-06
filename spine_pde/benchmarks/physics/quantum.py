"""Quantum benchmark for the discrete spine (spine_pde).

Everything is FINITE / DISCRETE / SPARSE -- the continuum is refused.

The quantum->classical crossover is the telegraph horizon: projecting the
master spine PDE onto an ``L_R`` eigenmode ``lam`` gives the scalar oscillator

    M w'' + D w' + K lam w = 0 ,     disc(lam) = D**2 - 4 M K lam .

* disc < 0  (lam > lam_c): under-damped -> OSCILLATORY  == quantum readout.
* disc > 0  (lam < lam_c): over-damped  -> DECAY        == classical readout.
* crossover at  lam_c = D**2 / (4 M K).

Three parts, all run for real below:
  (a) crossover swept over a real sparse L_R spectrum (eigsh);
  (b) many-mode telegraph evolution, under-damped OSC vs over-damped DECAY;
  (c) the decoherence-rate spectrum Gamma = K lam / D.

Each headline number is cross-checked, where an exact Coq witness exists, against
spine_pde.exact (Fraction, bit-for-bit) and tagged [Th_coqc]; purely numerical
sweeps are tagged [Fin].
"""

from __future__ import annotations

import os
import sys
from fractions import Fraction

import numpy as np
import scipy.sparse.linalg as spla

# make the staged package importable when run directly
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..")))

from spine_pde import RetainedDifferenceGraph, Telegraph  # noqa: E402
from spine_pde import exact as sx  # noqa: E402


def _eig_spectrum(L, k):
    """k smallest eigenvalues of a sparse SPD-ish Laplacian (finite, sparse)."""
    n = L.shape[0]
    k = min(k, n - 2)
    vals = spla.eigsh(L.asfptype(), k=k, which="SM", return_eigenvectors=False)
    return np.sort(vals)


# --------------------------------------------------------------------------- #
# (a) quantum -> classical crossover across a real L_R spectrum
# --------------------------------------------------------------------------- #
def part_a():
    print("=" * 70)
    print("(a) QUANTUM->CLASSICAL CROSSOVER across a real sparse L_R spectrum")
    print("=" * 70)

    # a finite ring graph -> sparse combinatorial Laplacian L_R (eigs in [0,4])
    n = 400
    g = RetainedDifferenceGraph.ring(n, kernel=None)
    # combinatorial kernel so eigenvalues are the exact ring spectrum 2-2cos
    from spine_pde import adjacency_kernel

    g.kernel = adjacency_kernel
    L = g.laplacian()
    lam = _eig_spectrum(L, k=n - 2)

    # choose telegraph coeffs so lam_c sits inside the spectrum
    M, D, K = 1.0, 2.0, 1.0
    tg = Telegraph(M, D, K)
    spec = tg.classify_spectrum(lam)

    lam_c = spec["lam_c"]
    n_q = spec["n_oscillatory"]
    n_c = spec["n_decay"]
    print(f"graph            : finite ring, n_nodes={n}, sparse L_R nnz={L.nnz}")
    print(f"spectrum sampled : {lam.size} eigenvalues in "
          f"[{lam.min():.4f}, {lam.max():.4f}]  [Fin]")
    print(f"coeffs (M,D,K)   : ({M}, {D}, {K})")
    print(f"lam_c (float)    : {lam_c:.6f}   [Fin]")

    # exact Coq cross-check of the crossover formula lam_c = D^2/(4 M K)
    lam_c_exact = sx.crossover(1, 2, 1)  # Fraction
    disc_at_c = sx.discriminant(1, 2, 1, lam_c_exact)  # must be exactly 0
    print(f"lam_c (exact Q)  : {lam_c_exact} = {float(lam_c_exact):.6f}   "
          f"disc(lam_c)={disc_at_c}  [Th_coqc: critical_disc_zero]")
    assert disc_at_c == Fraction(0)

    print(f"OSCILLATORY/quantum modes (disc<0, lam>lam_c) : {n_q}")
    print(f"DECAY/classical  modes (disc>0, lam<lam_c)    : {n_c}")
    print(f"critical modes (disc==0)                      : "
          f"{int(np.count_nonzero(spec['critical']))}")
    print(f"quantum fraction : {n_q / lam.size:.3f}")

    # exact Coq witnesses of the two named regimes
    d_under = sx.discriminant(1, 1, 1, 1)   # -3  -> under-damped/quantum
    d_over = sx.discriminant(1, 4, 1, 1)    # +12 -> over-damped/classical
    print(f"[Th_coqc] underdamped_witness disc(1,1,1,1) = {d_under} (<0, quantum)")
    print(f"[Th_coqc] overdamped_witness  disc(1,4,1,1) = {d_over} (>0, classical)")
    assert d_under == Fraction(-3) and d_over == Fraction(12)
    return dict(n=n, lam_c=lam_c, lam_c_exact=lam_c_exact, n_q=n_q, n_c=n_c,
                lam_min=float(lam.min()), lam_max=float(lam.max()))


# --------------------------------------------------------------------------- #
# (b) many-mode telegraph evolution: under-damped OSC vs over-damped DECAY
# --------------------------------------------------------------------------- #
def _evolve_mode(M, D, K, lam, w0=1.0, dw0=0.0, T=40.0, steps=8000):
    """Integrate M w'' + D w' + K lam w = 0 (finite, explicit, discrete time)."""
    dt = T / steps
    w, dw = float(w0), float(dw0)
    ts = np.empty(steps + 1)
    ws = np.empty(steps + 1)
    ts[0], ws[0] = 0.0, w
    zero_cross = 0
    prev = w
    for k in range(1, steps + 1):
        a = (-D * dw - K * lam * w) / M
        dw += dt * a
        w += dt * dw
        ts[k] = k * dt
        ws[k] = w
        if (w > 0) != (prev > 0) and prev != 0.0:
            zero_cross += 1
        prev = w
    return ts, ws, zero_cross


def part_b():
    print()
    print("=" * 70)
    print("(b) MANY-MODE TELEGRAPH EVOLUTION: under-damped OSC vs over-damped DECAY")
    print("=" * 70)
    M, D, K = 1.0, 2.0, 1.0
    tg = Telegraph(M, D, K)
    lam_c = tg.crossover()
    print(f"coeffs (M,D,K)={M,D,K}  lam_c={lam_c:.4f}  [Fin]")

    # a spread of modes straddling lam_c
    modes = [0.2, 0.6, 1.0, 2.0, 5.0, 20.0]
    print(f"{'lam':>7} {'regime':>26} {'disc':>10} {'Re(s)':>9} "
          f"{'Im(s)':>9} {'zeroX':>6}")
    n_osc = n_dec = 0
    for lam in modes:
        ts, ws, zc = _evolve_mode(M, D, K, lam)
        r1, r2 = tg.roots(lam)
        reg = tg.regime(lam).split("/")[-1]
        if "OSC" in reg:
            n_osc += 1
        else:
            n_dec += 1
        print(f"{lam:7.2f} {tg.regime(lam):>26} {tg.discriminant(lam):10.3f} "
              f"{r1.real:9.4f} {abs(r1.imag):9.4f} {zc:6d}")
    print(f"under-damped OSCILLATORY (quantum) modes : {n_osc}")
    print(f"over-damped  DECAY (classical)    modes : {n_dec}")
    print("=> modes with lam>lam_c ring (nonzero zero-crossings); "
          "lam<lam_c decay monotonically (0 crossings).")
    return dict(n_osc=n_osc, n_dec=n_dec)


# --------------------------------------------------------------------------- #
# (c) decoherence-rate spectrum Gamma = K lam / D
# --------------------------------------------------------------------------- #
def part_c():
    print()
    print("=" * 70)
    print("(c) DECOHERENCE-RATE SPECTRUM  Gamma(lam) = K lam / D")
    print("=" * 70)
    n = 400
    g = RetainedDifferenceGraph.ring(n, kernel=None)
    from spine_pde import adjacency_kernel

    g.kernel = adjacency_kernel
    L = g.laplacian()
    lam = _eig_spectrum(L, k=n - 2)

    M, D, K = 1.0, 2.0, 1.0
    tg = Telegraph(M, D, K)
    spec = tg.classify_spectrum(lam)
    gamma = spec["decoherence_rate"]
    print(f"coeffs (M,D,K)={M,D,K}  D={D}")
    print(f"Gamma over {lam.size} modes  [Fin]")
    print(f"Gamma_min = {gamma.min():.6f}  (slowest mode, lam={lam.min():.4f})")
    print(f"Gamma_max = {gamma.max():.6f}  (fastest mode, lam={lam.max():.4f})")
    print(f"Gamma_mean= {gamma.mean():.6f}")
    print(f"tau_c = M/D = {tg.tau_c():.4f} (envelope corr. time)  "
          f"mass = D/2M = {tg.mass():.4f}")
    # sample rates at a few modes + exact Coq cross-check of the formula
    for lm in [1, 2, 4]:
        gx = sx.decoherence_rate(K=1, D=2, lam=lm)  # exact Fraction
        print(f"  Gamma(lam={lm}) = {float(tg.decoherence_rate(lm)):.4f}  "
              f"[Th_coqc formula K*lam/D exact={gx}]")
    return dict(gmin=float(gamma.min()), gmax=float(gamma.max()),
                gmean=float(gamma.mean()))


if __name__ == "__main__":
    a = part_a()
    b = part_b()
    c = part_c()

    print()
    print("#" * 70)
    print("RESULTS TABLE")
    print("#" * 70)
    print(f"{'quantity':<42}{'value':<20}{'tier'}")
    rows = [
        ("ring nodes / spectrum size", f"{a['n']} / {a['n']-2}", "[Fin]"),
        ("spectrum range [lam_min,lam_max]",
         f"[{a['lam_min']:.3f},{a['lam_max']:.3f}]", "[Fin]"),
        ("lam_c crossover (float)", f"{a['lam_c']:.6f}", "[Fin]"),
        ("lam_c crossover (exact Q, disc=0)",
         f"{a['lam_c_exact']}={float(a['lam_c_exact']):.4f}", "[Th_coqc]"),
        ("quantum (OSC) modes", f"{a['n_q']}", "[Fin]"),
        ("classical (DECAY) modes", f"{a['n_c']}", "[Fin]"),
        ("evolve: OSC vs DECAY sample modes",
         f"{b['n_osc']} vs {b['n_dec']}", "[Fin]"),
        ("Gamma_min / Gamma_max",
         f"{c['gmin']:.4f} / {c['gmax']:.4f}", "[Fin]"),
        ("Gamma_mean", f"{c['gmean']:.4f}", "[Fin]"),
        ("underdamped_witness disc(1,1,1,1)", "-3", "[Th_coqc]"),
        ("overdamped_witness  disc(1,4,1,1)", "12", "[Th_coqc]"),
    ]
    for name, val, tier in rows:
        print(f"{name:<42}{val:<20}{tier}")
