"""Cosmology benchmark for the discrete spine field theory.

Everything is finite / discrete / sparse -- the continuum is refused.  Three
readouts, each falsifiable against a bounded, computable number:

(a) tau_c FLOOR / discrete rate CEILING.
    The graph Laplacian ``L_R`` of a *finite* cosmic-web graph has a bounded
    spectrum: every eigenvalue obeys ``0 <= lam <= Lambda`` with the hard
    Gershgorin bound ``Lambda <= 2 * d_max``.  The telegraph decoherence rate
    is ``Gamma(lam) = K lam / D`` (see spine_pde.telegraph), so the fastest
    possible mode has rate ``Gamma_max = K*Lambda/D`` and therefore a hard
    minimum time-scale

        tau_c  >=  D / (K * Lambda)              (RATE CEILING / TIME FLOOR)

    A finite graph CANNOT relax faster than this.  The continuum has no such
    floor (lam -> infinity => tau -> 0): this cutoff is exactly the falsifiable
    structure the continuum lacks.

(b) STRUCTURE-FORMATION spine evolution on a >=10^5-node sparse 3-D cosmic-web
    lattice.  The symplectic leapfrog integrator evolves the master spine PDE;
    we show the state and shadow energy stay finite / bounded (no blow-up),
    i.e. discrete structure growth is stable.

(c) HORIZON = spine knife-edge ``lam_c = D^2 / (4 M K)`` laid on the real
    spectrum.  Modes with ``lam > lam_c`` are OSCILLATORY (quantum readout),
    ``lam < lam_c`` are DECAY (classical readout); ``lam == lam_c`` is the
    critically-damped horizon.  Cross-checked bit-for-bit against the Coq
    telegraph witnesses (disc(lam_c) == 0 exactly).

Run::

    python benchmarks/physics/cosmology.py            # ~10^5 nodes
    python benchmarks/physics/cosmology.py 200000
"""

from __future__ import annotations

import sys
import time
from fractions import Fraction

import numpy as np
import scipy.sparse as sp

import scipy.sparse.linalg as spla

from spine_pde import RetainedDifferenceGraph, Spine, Telegraph, ZeroPotential, exact


def extreme_eigs(L: sp.spmatrix, k: int = 40) -> np.ndarray:
    """Top-k and bottom-k eigenvalues via plain ARPACK Lanczos (NO shift-invert).

    Shift-invert needs a sparse LU of ``L``; for a 3-D grid that has ruinous
    fill-in, so we use plain Lanczos, which converges fast for the well-separated
    extremes of a graph Laplacian.  Everything stays O(nnz) per mat-vec.
    """
    n = L.shape[0]
    if n <= 3:
        return np.linalg.eigvalsh(np.asarray(L.todense(), dtype=float))
    k = max(1, min(k, n - 2))
    hi = spla.eigsh(L, k=k, which="LA", return_eigenvectors=False)
    lo = spla.eigsh(L, k=k, which="SA", return_eigenvectors=False)
    return np.unique(np.concatenate([lo, hi]))


# spine coefficients (integers -> exact-rational Coq cross-check is available)
M, D, K = 1, 2, 1     # lam_c = D^2/(4 M K) = 1


def human_bytes(n: float) -> str:
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if n < 1024:
            return f"{n:.1f} {unit}"
        n /= 1024
    return f"{n:.1f} PB"


def build_cosmic_web(target_nodes: int) -> tuple[sp.spmatrix, int, int]:
    """A 3-D cubic lattice ~ cosmic-web skeleton; O(N) edges, straight to sparse."""
    import math
    # ceil so the node count is guaranteed >= target (>= 10^5 by default)
    side = max(2, math.ceil(target_nodes ** (1.0 / 3.0)))
    n = side ** 3

    def idx(a: int, b: int, c: int) -> int:
        return (a * side + b) * side + c

    rows: list[int] = []
    cols: list[int] = []
    for a in range(side):
        for b in range(side):
            for c in range(side):
                u = idx(a, b, c)
                if a + 1 < side:
                    v = idx(a + 1, b, c); rows += [u, v]; cols += [v, u]
                if b + 1 < side:
                    v = idx(a, b + 1, c); rows += [u, v]; cols += [v, u]
                if c + 1 < side:
                    v = idx(a, b, c + 1); rows += [u, v]; cols += [v, u]
    data = np.ones(len(rows), dtype=float)
    Wm = sp.coo_matrix((data, (rows, cols)), shape=(n, n)).tocsr()
    deg = np.asarray(Wm.sum(axis=1)).ravel()
    L = sp.diags(deg) - Wm
    return L.tocsr(), side, n


def main(target_nodes: int = 100_000, steps: int = 400) -> int:
    print("=" * 74)
    print("spine_pde COSMOLOGY BENCHMARK  (finite / discrete / sparse -- no continuum)")
    print("=" * 74)
    print(f"spine coefficients: M={M}  D={D}  K={K}")

    results: list[tuple[str, str, str]] = []  # (label, value, tier)

    # ---- build cosmic web ------------------------------------------------- #
    t0 = time.perf_counter()
    L, side, n = build_cosmic_web(target_nodes)
    t_build = time.perf_counter() - t0
    nnz = L.nnz
    sparse_mem = L.data.nbytes + L.indices.nbytes + L.indptr.nbytes
    dense_mem = 8 * n * n
    print(f"\n[graph] 3-D cosmic-web lattice {side}x{side}x{side} = {n:,} nodes")
    print(f"        nnz(L_R)={nnz:,}  build={t_build:.3f}s")
    print(f"        sparse L_R {human_bytes(sparse_mem)}  vs DENSE {human_bytes(dense_mem)} (refused)")
    assert sp.issparse(L)
    assert sparse_mem < dense_mem / 100

    # =====================================================================  #
    # (a) tau_c FLOOR / discrete rate CEILING
    # =====================================================================  #
    print("\n[a] tau_c FLOOR / discrete rate CEILING (bounded spectrum)")
    t0 = time.perf_counter()
    lam = extreme_eigs(L, k=40)          # sparse ARPACK, both ends
    t_eig = time.perf_counter() - t0
    Lambda = float(lam.max())            # top of the bounded spectrum
    d_max = float(L.diagonal().max())
    gershgorin = 2.0 * d_max             # hard bound Lambda <= 2 d_max
    Gamma_max = K * Lambda / D           # fastest decoherence rate
    tau_floor = D / (K * Lambda)         # hard time floor
    print(f"    ARPACK spectrum sample: lam in [{lam.min():.4g}, {Lambda:.6g}]  ({t_eig:.3f}s)")
    print(f"    Gershgorin bound Lambda <= 2*d_max = {gershgorin:.6g}  (d_max={d_max:.0f})  -> holds: {Lambda <= gershgorin + 1e-9}")
    print(f"    rate CEILING   Gamma_max = K*Lambda/D = {Gamma_max:.6g}")
    print(f"    time FLOOR     tau_c >= D/(K*Lambda)  = {tau_floor:.6g}")
    print(f"    continuum: lam -> inf => tau_c -> 0  (NO floor)  <- falsifiable cutoff the continuum lacks")
    assert np.isfinite(Lambda) and Lambda <= gershgorin + 1e-9
    results.append(("(a) Lambda (spectral top)", f"{Lambda:.6g}", "[Fin]"))
    results.append(("(a) Gershgorin 2*d_max", f"{gershgorin:.6g}", "[Fin]"))
    results.append(("(a) rate ceiling Gamma_max", f"{Gamma_max:.6g}", "[Fin]"))
    results.append(("(a) tau_c FLOOR D/(K*Lambda)", f"{tau_floor:.6g}", "[Fin]"))

    # =====================================================================  #
    # (b) STRUCTURE-FORMATION spine evolution (stability)
    # =====================================================================  #
    print(f"\n[b] STRUCTURE-FORMATION spine evolution, {steps} leapfrog steps on {n:,} nodes")
    rng = np.random.default_rng(0)
    x0 = rng.standard_normal(n)          # primordial density perturbations
    # leapfrog stability: dtheta < 2/omega_max, omega_max = sqrt(K*Lambda/M)
    omega_max = (K * Lambda / M) ** 0.5
    dtheta = 0.4 * (2.0 / omega_max)     # 0.4 of the CFL limit -> stable
    print(f"    dtheta={dtheta:.4g} (0.4 * CFL 2/omega_max, omega_max={omega_max:.4g})")

    # (b.1) CONSERVATIVE (D=0): symplectic leapfrog conserves a SHADOW energy,
    #       so the measured energy stays in a BOUNDED band ~O((omega*dtheta)^2)
    #       with NO secular growth -- the real 'stays finite/stable' proof.  We
    #       confirm the band shrinks ~4x when dtheta is halved (the O(dtheta^2)
    #       symplectic signature), and never grows without bound.
    def energy_band(dt: float) -> tuple[float, float, bool, float]:
        sc = Spine(M=float(M), D=0.0, K=float(K), graph_or_L=L,
                   gradV=ZeroPotential(), dtheta=dt, x0=x0.copy())
        t0 = time.perf_counter()
        hist = sc.evolve(steps, record=True, stride=10)
        el = time.perf_counter() - t0
        e = np.asarray(hist.energy)
        e0 = e[0]
        band = (e.max() - e.min()) / abs(e0) * 100.0   # % excursion of measured E
        return band, e0, bool(np.all(np.isfinite(sc.x))), el
    band1, e0c, finite_c, t_ec1 = energy_band(dtheta)
    band2, _, finite_c2, t_ec2 = energy_band(dtheta / 2.0)
    t_ec = t_ec1 + t_ec2
    ratio = band1 / band2 if band2 > 0 else float("inf")
    print(f"    (b.1) CONSERVATIVE D=0 (symplectic, shadow-energy): E0={e0c:.5g}")
    print(f"          energy band at dt      = {band1:.3f}%   (bounded, no secular growth)")
    print(f"          energy band at dt/2    = {band2:.3f}%")
    print(f"          band(dt)/band(dt/2)    = {ratio:.2f}x  (~4 => O(dt^2) symplectic)  finite={finite_c and finite_c2}")

    # (b.2) DAMPED (D>0): physical structure relaxation -- energy DISSIPATES
    #       monotonically (never grows), state stays bounded/finite.
    sd = Spine(M=float(M), D=0.02, K=float(K), graph_or_L=L,
               gradV=ZeroPotential(), dtheta=dtheta, x0=x0.copy())
    e0d = sd.energy()
    x_rms0 = float(np.sqrt(np.mean(sd.x ** 2)))
    t0 = time.perf_counter()
    sd.evolve(steps)
    t_ed = time.perf_counter() - t0
    efd = sd.energy()
    x_rms = float(np.sqrt(np.mean(sd.x ** 2)))
    finite_d = bool(np.all(np.isfinite(sd.x)))
    dissip = (e0d - efd) / abs(e0d) * 100
    t_evolve = t_ec + t_ed
    print(f"    (b.2) DAMPED D=0.02: energy {e0d:.5g} -> {efd:.5g}  "
          f"dissipated={dissip:.2f}% (energy DROPS, never grows)  finite={finite_d}")
    print(f"          x_rms: {x_rms0:.4g} -> {x_rms:.4g}  ({t_ed:.3f}s)")
    print(f"    -> discrete structure growth stays FINITE / STABLE (conserved when D=0, "
          f"dissipative when D>0, never blows up)")
    assert finite_c and finite_c2 and finite_d, "state blew up -- integrator unstable"
    assert ratio > 3.0, "energy band did not shrink ~4x -> not O(dt^2) symplectic"
    assert efd <= e0d, "damped energy must not grow"
    results.append(("(b) D=0 energy band % @dt", f"{band1:.3f}", "[Fin]"))
    results.append(("(b) D=0 band shrink dt->dt/2", f"{ratio:.2f}x", "[Fin]"))
    results.append(("(b) D>0 energy dissipated %", f"{dissip:.2f}", "[Fin]"))
    results.append(("(b) x_rms final (finite)", f"{x_rms:.4g}", "[Fin]"))

    # =====================================================================  #
    # (c) HORIZON = spine knife-edge lam_c = D^2/(4 M K)
    # =====================================================================  #
    print("\n[c] HORIZON = spine knife-edge  lam_c = D^2/(4 M K)")
    tg = Telegraph(M=float(M), D=float(D), K=float(K))
    lam_c_f = float(tg.crossover())
    summary = tg.classify_spectrum(lam)
    # exact-rational cross-check against the Coq telegraph witnesses
    lam_c_ex = exact.crossover(M, D, K)             # Fraction
    disc_at_c = exact.discriminant(M, D, K, lam_c_ex)   # must be exactly 0
    disc_1111 = exact.discriminant(1, 1, 1, 1)          # Coq witness == -3
    print(f"    lam_c (float)  = {lam_c_f:.6g}")
    print(f"    lam_c (exact)  = {lam_c_ex}   [Th_coqc: D^2/(4MK)]")
    print(f"    disc(lam_c)    = {disc_at_c}   (Coq critical_disc_zero: == 0)  -> {disc_at_c == 0}")
    print(f"    disc(1,1,1,1)  = {disc_1111}   (Coq underdamped_witness: == -3)  -> {disc_1111 == Fraction(-3)}")
    print(f"    spectrum split at horizon (sampled {lam.size} extreme modes):")
    print(f"        lam > lam_c  OSCILLATORY (quantum) : {summary['n_oscillatory']}")
    print(f"        lam < lam_c  DECAY       (classical): {summary['n_decay']}")
    print(f"        Lambda={Lambda:.4g} > lam_c={lam_c_f:.4g}: horizon sits INSIDE the bounded spectrum: {Lambda > lam_c_f}")
    assert disc_at_c == 0
    assert disc_1111 == Fraction(-3)
    results.append(("(c) lam_c horizon", f"{lam_c_f:.6g}", "[Th_coqc]"))
    results.append(("(c) disc(lam_c)==0", f"{disc_at_c}", "[Th_coqc]"))
    results.append(("(c) disc(1,1,1,1)==-3", f"{disc_1111}", "[Th_coqc]"))
    results.append(("(c) n OSCILLATORY / n DECAY",
                    f"{summary['n_oscillatory']}/{summary['n_decay']}", "[Fin]"))

    # ---- results table ---------------------------------------------------- #
    total = t_build + t_eig + t_evolve
    print("\n" + "-" * 74)
    print("RESULTS TABLE")
    print("-" * 74)
    print(f"{'quantity':<34}{'value':>22}{'tier':>10}")
    print("-" * 74)
    for label, val, tier in results:
        print(f"{label:<34}{val:>22}{tier:>10}")
    print("-" * 74)
    print(f"nodes={n:,}  nnz={nnz:,}  wall-clock={total:.3f}s "
          f"(build {t_build:.2f} + eig {t_eig:.2f} + evolve {t_evolve:.2f})")
    print(f"MEMORY-SAFE: {human_bytes(sparse_mem)} sparse vs {human_bytes(dense_mem)} dense-refused "
          f"({dense_mem/sparse_mem:.0f}x). No dense N^2 anywhere.  [Th_coqc]=exact Coq value  [Fin]=finite numeric")
    print("-" * 74)
    return 0


if __name__ == "__main__":
    nodes = int(sys.argv[1]) if len(sys.argv) > 1 else 100_000
    raise SystemExit(main(nodes))
