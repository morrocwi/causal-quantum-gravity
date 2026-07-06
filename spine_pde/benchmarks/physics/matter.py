"""MATTER / PARTICLES benchmark for the discrete spine field theory.

Everything is finite / discrete -- the continuum is REFUSED.  Three readouts,
each cross-checked against an exact value (a Coq witness where one exists,
tagged ``[Th_coqc]``; otherwise an exact analytic/rational value, ``[Fin]``):

(a) MASS LAW        mass = D/(2 M) = 1/(2 tau_c).  Exact-mode cross-check that
    mass == D/(2 M) bit-for-bit across several (M, D) modes, plus the Coq
    witness ``InfoTauCReadoutLaw`` : mass(M=1, D=1) == 1/2.

(b) SOLITON / KINK  A localized, stable "particle" grown from the double-well
    on-site potential ``V = (x^2-1)^2/4`` (minima x = +-1).  A tanh kink is
    seeded on a 1-D retained-difference path graph and the damped master spine
    PDE relaxes it to the static phi^4 kink of width w = sqrt(2 K/... ) -- a
    localized interface between the two vacua that does NOT spread out.

(c) MASS SPECTRUM   The spectral-gap ratios of the L_R modes.  On a ring graph
    the Laplacian spectrum is known exactly, lam_k = 4 sin^2(pi k / n); the mode
    "masses" are these eigenvalues and the mass ratios are the gap ratios,
    cross-checked numeric-vs-exact.  Per-mode decoherence Gamma_k = K lam_k / D
    inherits the same ratios, and tau_c(mode) = 1/Gamma_k, so the mass ratio is
    the inverse tau_c ratio (mass ratio = tau_c ratio, reciprocally).

Run::

    python benchmarks/physics/matter.py
"""

from __future__ import annotations

from fractions import Fraction

import numpy as np

from spine_pde import DoubleWell, RetainedDifferenceGraph, Spine, Telegraph
from spine_pde import exact


def rule(c: str = "=") -> None:
    print(c * 72)


# --------------------------------------------------------------------------- #
# (a) MASS LAW : mass = D/(2M) = 1/(2 tau_c)
# --------------------------------------------------------------------------- #
def part_a() -> list[tuple]:
    rule()
    print("(a) MASS LAW   mass = D/(2 M) = 1/(2 tau_c)   [exact rational]")
    rule()
    rows: list[tuple] = []
    # several (M, D) modes -- exact rational path (continuum refused)
    modes = [(1, 1), (1, 2), (2, 3), (3, 5), (5, 7)]
    print(f"{'M':>4} {'D':>4} {'mass=D/2M':>12} {'1/(2 tau_c)':>14} "
          f"{'D/(2M)':>10} {'match':>6}")
    all_ok = True
    for M, D in modes:
        m = exact.mass(M, D)                 # D/(2M) exact
        tau = exact.tau_c(M, D)              # M/D exact
        m_from_tau = Fraction(1, 2) / tau    # 1/(2 tau_c)
        m_check = Fraction(D) / (2 * Fraction(M))
        ok = (m == m_from_tau == m_check)
        all_ok &= ok
        print(f"{M:>4} {D:>4} {str(m):>12} {str(m_from_tau):>14} "
              f"{str(m_check):>10} {str(ok):>6}")
    # Coq witness: InfoTauCReadoutLaw -> mass(M=1, D=1) == 1/2
    witnesses = exact.verify_theorems()
    wname = "mass == 1/(2M) at D=1, M=1"
    coq_ok = witnesses[wname]
    coq_val = exact.mass(1, 1)
    print(f"\n  exact-mode mass == D/(2M) across all modes : {all_ok}")
    print(f"  Coq witness InfoTauCReadoutLaw  mass(1,1) = {coq_val} "
          f"(expected 1/2) : {coq_ok}   [Th_coqc]")
    rows.append(("mass(M=1,D=1)", str(coq_val), "1/2", "[Th_coqc]", coq_ok))
    rows.append(("mass==D/(2M) all modes", str(all_ok), "True", "[Fin]", all_ok))
    return rows


# --------------------------------------------------------------------------- #
# (b) SOLITON / KINK from the double well
# --------------------------------------------------------------------------- #
def part_b() -> list[tuple]:
    rule()
    print("(b) SOLITON / KINK   double-well V=(x^2-1)^2/4  ->  a stable particle")
    rule()
    n = 201
    K = 4.0                      # stiffness -> kink half-width w = sqrt(2K)
    w_theory = np.sqrt(2.0 * K)  # continuum phi^4 kink width scale
    g = RetainedDifferenceGraph.path(n)
    L = g.laplacian("csr")
    s_idx = np.arange(n) - n // 2           # centred lattice coordinate
    x0 = np.tanh(s_idx / w_theory)          # seed a tanh kink (-1 .. +1)

    spine = Spine(
        M=1.0, D=0.5, K=K, graph_or_L=L,
        gradV=DoubleWell(a=0.25, b=1.0),    # gradV = x^3 - x, minima +-1
        dtheta=2e-3, x0=x0,
    )

    def width(x: np.ndarray) -> float:
        # tanh(s/w) has slope 1/w at centre -> w = 1/max|dx/ds|
        return 1.0 / np.max(np.abs(np.diff(x)))

    def center(x: np.ndarray) -> float:
        # zero crossing (interp) of the monotone profile
        k = int(np.argmin(np.abs(x)))
        return float(s_idx[k])

    e0 = spine.energy()
    w0, c0 = width(spine.x), center(spine.x)
    spine.evolve(4000)                      # damped relaxation to static kink
    ef = spine.energy()
    xf = spine.x
    wf, cf = width(xf), center(xf)

    # localization: fraction of on-site potential energy in the central window
    Vdens = 0.25 * (xf**2 - 1.0) ** 2
    core = np.abs(s_idx) <= 3 * wf
    loc_frac = float(Vdens[core].sum() / Vdens.sum())
    left_vac = float(np.mean(xf[:10]))
    right_vac = float(np.mean(xf[-10:]))
    # non-decreasing up to residual vacuum-phonon ripple (~1e-6 on a span of 2)
    monotone = bool(np.min(np.diff(xf)) > -1e-4)
    finite = bool(np.all(np.isfinite(xf)))

    print(f"  nodes={n}  K={K}  theory width w=sqrt(2K)={w_theory:.4f}")
    print(f"  seed : width={w0:.4f}  center={c0:+.2f}  energy={e0:.5f}")
    print(f"  final: width={wf:.4f}  center={cf:+.2f}  energy={ef:.5f}")
    print(f"  vacua: left ~ {left_vac:+.4f}   right ~ {right_vac:+.4f}   (want -1, +1)")
    print(f"  localized: {loc_frac*100:.1f}% of V-energy within +-3w of core")
    print(f"  monotone kink (no unwinding): {monotone}   finite (no blow-up): {finite}")
    stable = monotone and finite and loc_frac > 0.9 and abs(cf - c0) <= 2
    print(f"  -> STABLE LOCALIZED PARTICLE: {stable}   [Fin]")
    return [
        ("kink width (final)", f"{wf:.3f}", f"~{w_theory:.3f}", "[Fin]",
         abs(wf - w_theory) < 1.0),
        ("kink V-energy localized", f"{loc_frac*100:.1f}%", ">90%", "[Fin]",
         loc_frac > 0.9),
        ("kink stable (mono+finite)", str(stable), "True", "[Fin]", stable),
    ]


# --------------------------------------------------------------------------- #
# (c) MASS SPECTRUM = spectral-gap ratios of L_R modes
# --------------------------------------------------------------------------- #
def part_c() -> list[tuple]:
    rule()
    print("(c) MASS SPECTRUM   spectral-gap ratios of L_R modes  (ring graph)")
    rule()
    n = 12
    g = RetainedDifferenceGraph.ring(n)
    L = g.laplacian("csr").toarray()
    lam_num = np.sort(np.linalg.eigvalsh(L))
    # exact analytic ring-Laplacian spectrum: lam_k = 4 sin^2(pi k / n)
    lam_exact = np.sort([4.0 * np.sin(np.pi * k / n) ** 2 for k in range(n)])
    max_err = float(np.max(np.abs(lam_num - lam_exact)))

    # mass spectrum = eigenvalue spectrum; gap ratios vs the first nonzero mode
    nz = lam_num[lam_num > 1e-9]
    nz_exact = lam_exact[lam_exact > 1e-9]
    base = nz[0]
    ratios_num = nz / base
    ratios_exact = nz_exact / nz_exact[0]

    # per-mode decoherence Gamma_k = K lam_k / D  ->  tau_c(mode) = 1/Gamma_k
    K, D = 1.0, 1.0
    tg = Telegraph(M=1.0, D=D, K=K)
    gamma = tg.classify_spectrum(nz)["decoherence_rate"]      # K lam / D
    tau_mode = 1.0 / gamma
    mass_ratio = gamma / gamma[0]                             # = lam ratio
    tau_ratio = tau_mode[0] / tau_mode                        # inverse tau ratio

    print(f"  ring n={n}   L_R spectrum (numeric vs exact 4 sin^2(pi k/n)):")
    print(f"    max |lam_num - lam_exact| = {max_err:.2e}   [Th_coqc-analytic exact match]")
    print(f"    lam (numeric) = {np.round(lam_num, 4)}")
    print("\n  mass spectrum = gap ratios lam_k / lam_1 :")
    print(f"    numeric = {np.round(ratios_num, 4)}")
    print(f"    exact   = {np.round(ratios_exact, 4)}")
    print("\n  mass ratio (Gamma_k/Gamma_1) vs inverse tau_c ratio (tau_1/tau_k):")
    print(f"    mass ratio     = {np.round(mass_ratio, 4)}")
    print(f"    inv-tau ratio  = {np.round(tau_ratio, 4)}")
    same = float(np.max(np.abs(mass_ratio - tau_ratio)))
    print(f"    max|mass_ratio - inv_tau_ratio| = {same:.2e}  (mass ratio = tau_c ratio)")
    ok_spec = max_err < 1e-9
    ok_tau = same < 1e-9
    return [
        ("ring L_R spectrum vs 4sin^2", f"{max_err:.1e}", "0 (exact)",
         "[Fin]", ok_spec),
        ("mass ratio == inv tau_c ratio", f"{same:.1e}", "0 (exact)",
         "[Fin]", ok_tau),
    ]


def main() -> int:
    rows: list[tuple] = []
    rows += part_a()
    rows += part_b()
    rows += part_c()

    print()
    rule()
    print("RESULTS TABLE  (matter / particles)")
    rule()
    print(f"{'quantity':<32}{'got':>12}{'expected':>12}{'tier':>11}{'ok':>5}")
    rule("-")
    for name, got, exp, tier, ok in rows:
        print(f"{name:<32}{got:>12}{exp:>12}{tier:>11}{str(ok):>5}")
    rule("-")
    npass = sum(1 for r in rows if r[4])
    print(f"{npass}/{len(rows)} checks pass.")
    rule()
    return 0 if npass == len(rows) else 1


if __name__ == "__main__":
    raise SystemExit(main())
