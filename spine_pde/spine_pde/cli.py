"""Command-line interface for :mod:`spine_pde`.

Run as ``python -m spine_pde <command> ...``.  Four subcommands expose the four
pillars of the theory from the shell:

* ``crossover`` -- telegraph regime / horizon analysis for ``(M, D, K)`` and a
  spectrum of ``L_R`` eigenvalues (or the spectrum of a built-in graph).
* ``evolve``    -- integrate the master spine PDE on a built-in graph and report
  the energy trajectory.
* ``curvature`` -- exact discrete curvature readouts (Riemann / Gauss-Bonnet /
  metric ``R1212`` / Heisenberg commutator) that match the Coq theorems.
* ``spectrum``  -- extreme ``L_R`` eigenvalues of a built-in graph (sparse).

Everything is finite/discrete; there is no continuum option because the theory
refuses one.
"""

from __future__ import annotations

import argparse
import sys
from fractions import Fraction
from typing import Sequence

import numpy as np

from . import curvature as _curv
from .graph import RetainedDifferenceGraph
from .potentials import ZeroPotential
from .spine import Spine
from .telegraph import Telegraph


# --------------------------------------------------------------------------- #
# helpers
# --------------------------------------------------------------------------- #


def _build_graph(kind: str, size: int) -> RetainedDifferenceGraph:
    """Construct a built-in graph. ``size`` is total node count."""
    if kind == "ring":
        return RetainedDifferenceGraph.ring(size)
    if kind == "path":
        return RetainedDifferenceGraph.path(size)
    if kind == "grid":
        side = int(round(size**0.5))
        if side < 1:
            raise SystemExit("grid needs size >= 1")
        return RetainedDifferenceGraph.grid2d(side, side)
    raise SystemExit(f"unknown graph kind: {kind!r}")


def _rational(text: str) -> Fraction:
    """Parse a CLI scalar as an exact Fraction (accepts '3', '1/2', '0.25')."""
    return Fraction(text)


def extreme_eigs(L, k: int = 6) -> np.ndarray:
    """Smallest and largest ``L_R`` eigenvalues via sparse ARPACK.

    Uses shift-invert (``sigma``) at both ends of the spectrum because the graph
    Laplacian's eigenvalues cluster near ``0`` and near ``2*max_degree``, where
    plain ARPACK converges slowly.  Falls back to a dense solve on tiny graphs
    and to plain ``which=`` if the sparse factorisation fails.
    """
    import scipy.sparse.linalg as spla

    n = L.shape[0]
    if n <= 3:
        return np.linalg.eigvalsh(np.asarray(L.todense(), dtype=float))
    k = max(1, min(k, n - 2))
    # cheap spectral bound: lam in [0, 2*max_degree] = [0, 2*max diagonal]
    dmax = float(L.diagonal().max())
    top = 2.0 * dmax + 1.0
    try:
        lo = spla.eigsh(L, k=k, sigma=-1e-6 * (dmax + 1.0), which="LM", return_eigenvectors=False)
        hi = spla.eigsh(L, k=k, sigma=top, which="LM", return_eigenvectors=False)
    except Exception:  # pragma: no cover - robustness fallback
        lo = spla.eigsh(L, k=k, which="SA", return_eigenvectors=False)
        hi = spla.eigsh(L, k=k, which="LA", return_eigenvectors=False)
    return np.unique(np.concatenate([lo, hi]))


# backwards-compatible private alias
_extreme_eigs = extreme_eigs


# --------------------------------------------------------------------------- #
# subcommands
# --------------------------------------------------------------------------- #


def cmd_crossover(args: argparse.Namespace) -> int:
    exact = args.exact
    if exact:
        tg = Telegraph(_rational(args.M), _rational(args.D), _rational(args.K), exact=True)
    else:
        tg = Telegraph(float(args.M), float(args.D), float(args.K), exact=False)

    print(f"Telegraph analyser: M={tg.M} D={tg.D} K={tg.K} mode={'exact' if tg.exact else 'float'}")
    print(f"  crossover lam_c = {tg.crossover()}   (disc == 0, the horizon knife-edge)")
    print(f"  mass  = D/(2M)  = {tg.mass()}")
    print(f"  tau_c = M/D     = {tg.tau_c()}")

    lams: Sequence
    if args.lam:
        lams = [_rational(x) if exact else float(x) for x in args.lam]
    elif args.graph:
        L = _build_graph(args.graph, args.size).laplacian("csr")
        lams = _extreme_eigs(L)
        print(f"  (spectrum sampled from {args.graph} graph, n={L.shape[0]})")
    else:
        lams = [_rational("1") if exact else 1.0]

    print("  eigenmode analysis:")
    for lam in lams:
        disc = tg.discriminant(lam) if exact else tg.discriminant(float(lam))
        regime = tg.regime(lam) if exact else tg.regime(float(lam))
        gamma = tg.decoherence_rate(lam) if exact else tg.decoherence_rate(float(lam))
        lam_show = lam if exact else float(lam)
        print(f"    lam={lam_show!s:<18} disc={disc!s:<18} {regime:<28} Gamma={gamma}")
    return 0


def cmd_spectrum(args: argparse.Namespace) -> int:
    g = _build_graph(args.graph, args.size)
    L = g.laplacian("csr")
    print(f"{args.graph} graph: n={L.shape[0]} nodes, nnz(L_R)={L.nnz}")
    eigs = _extreme_eigs(L, k=args.k)
    print(f"  extreme eigenvalues (sparse ARPACK): {np.round(eigs, 6)}")
    print(f"  lam_min={eigs.min():.6g}  lam_max={eigs.max():.6g}")
    return 0


def cmd_evolve(args: argparse.Namespace) -> int:
    g = _build_graph(args.graph, args.size)
    rng = np.random.default_rng(args.seed)
    x0 = rng.standard_normal(g.n_nodes)
    s = Spine(
        M=args.M,
        D=args.D,
        K=args.K,
        graph_or_L=g,
        gradV=None if args.doublewell else ZeroPotential(),
        dtheta=args.dtheta,
        x0=x0,
    )
    print(repr(s))
    e0 = s.energy()
    hist = s.evolve(args.steps, record=True, stride=max(1, args.steps // 5))
    ef = s.energy()
    print(f"  steps={args.steps} dtheta={args.dtheta}")
    print(f"  energy: initial={e0:.6g}  final={ef:.6g}  drift={ef - e0:+.3g}")
    if hist is not None:
        arr = hist.as_arrays()
        for th, en in zip(arr["theta"], arr["energy"]):
            print(f"    theta={th:8.3f}   energy={en:.6g}")
    print(f"  |x|_2 final = {np.linalg.norm(s.x):.6g}")
    return 0


def cmd_curvature(args: argparse.Namespace) -> int:
    kind = args.field
    if kind == "square":
        w = lambda n: Fraction(n) ** 2  # noqa: E731
        label = "w(n) = n**2"
    elif kind == "double":
        w = lambda n: Fraction(2) ** n  # noqa: E731
        label = "w(n) = 2**n"
    elif kind == "affine":
        a, b = Fraction(args.a), Fraction(args.b)
        w = lambda n: a * Fraction(n) + b  # noqa: E731
        label = f"w(n) = {a}*n + {b}  (affine)"
    else:
        vals = [Fraction(x) for x in kind.split(",")]
        w = vals
        label = f"w = {vals}"

    j = args.node
    print(f"Discrete curvature of {label}  (exact rational, matches Coq)")
    print(f"  christoffel_fd(w, {j})            = {_curv.christoffel_fd(w, j)}")
    print(f"  riemann_fd(w, {j})               = {_curv.riemann_fd(w, j)}")
    print(f"  total_curvature(w, {args.N})     = {_curv.total_curvature(w, args.N)}")
    print(f"  gauss_bonnet_boundary(w, {args.N}) = {_curv.gauss_bonnet_boundary(w, args.N)}")
    try:
        print(f"  R1212(w, {j})  (g=diag(1,w))     = {_curv.R1212(w, j)}")
    except ZeroDivisionError:
        print(f"  R1212(w, {j})                    = undefined (w vanishes)")
    print(
        f"  commutator_curvature({args.a}, {args.b})  = "
        f"{_curv.commutator_curvature(Fraction(args.a), Fraction(args.b))}  (== a*b)"
    )
    return 0


# --------------------------------------------------------------------------- #
# parser
# --------------------------------------------------------------------------- #


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="spine_pde",
        description="Discrete tensor-PDE spine field theory (finite/discrete; continuum refused).",
    )
    sub = p.add_subparsers(dest="command", required=True)

    c = sub.add_parser("crossover", help="telegraph regime / horizon analysis")
    c.add_argument("--M", default="1", help="inertia (default 1)")
    c.add_argument("--D", default="1", help="damping (default 1)")
    c.add_argument("--K", default="1", help="graph stiffness (default 1)")
    c.add_argument("--lam", nargs="*", help="eigenvalues to classify")
    c.add_argument("--graph", choices=["ring", "path", "grid"], help="sample spectrum from a graph")
    c.add_argument("--size", type=int, default=1000, help="graph node count (default 1000)")
    c.add_argument("--exact", action="store_true", help="exact rational arithmetic")
    c.set_defaults(func=cmd_crossover)

    s = sub.add_parser("spectrum", help="extreme sparse L_R eigenvalues of a graph")
    s.add_argument("--graph", choices=["ring", "path", "grid"], default="grid")
    s.add_argument("--size", type=int, default=10000)
    s.add_argument("--k", type=int, default=6, help="eigenpairs per end")
    s.set_defaults(func=cmd_spectrum)

    e = sub.add_parser("evolve", help="integrate the master spine PDE")
    e.add_argument("--graph", choices=["ring", "path", "grid"], default="ring")
    e.add_argument("--size", type=int, default=1000)
    e.add_argument("--M", type=float, default=1.0)
    e.add_argument("--D", type=float, default=0.1)
    e.add_argument("--K", type=float, default=1.0)
    e.add_argument("--dtheta", type=float, default=1e-2)
    e.add_argument("--steps", type=int, default=200)
    e.add_argument("--seed", type=int, default=0)
    e.add_argument("--doublewell", action="store_true", help="use the double-well on-site potential")
    e.set_defaults(func=cmd_evolve)

    cu = sub.add_parser("curvature", help="exact discrete curvature readouts")
    cu.add_argument(
        "--field",
        default="square",
        help="'square' (n**2), 'double' (2**n), 'affine', or a comma list e.g. 1,2,4,8",
    )
    cu.add_argument("--node", type=int, default=0, help="node index j")
    cu.add_argument("--N", type=int, default=2, help="Gauss-Bonnet window")
    cu.add_argument("--a", default="2", help="commutator / affine slope a")
    cu.add_argument("--b", default="3", help="commutator / affine offset b")
    cu.set_defaults(func=cmd_curvature)

    return p


def main(argv: Sequence[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args) or 0)


if __name__ == "__main__":  # pragma: no cover
    sys.exit(main())
