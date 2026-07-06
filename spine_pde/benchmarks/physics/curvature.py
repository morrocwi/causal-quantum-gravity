"""Discrete-curvature physics benchmark for the ``spine_pde`` package.

Exercises the WHOLE finite/discrete curvature chain -- NO continuum, NO limit is
ever taken; every field is sampled on the integer nodes ``0, 1, 2, ...`` and every
number is an exact ``Fraction`` (or int) so Python matches the Coq theorems
bit-for-bit.

Chain covered
-------------
(a) ``riemann_fd``  -- second-difference Riemann curvature; exact cross-check
    ``riemann_fd(n -> n**2, 0) == 2``   (Coq ``curvature_nonzero_witness``).
(b) ``total_curvature`` / ``gauss_bonnet_boundary`` -- discrete Gauss-Bonnet:
    the bulk sum telescopes to the boundary; ``==4`` for ``w=n**2, N=2``
    (Coq ``total_curv_wsq_2`` / ``total_curvature_telescopes``).
(c) ``commutator_curvature(a,b) == a*b`` -- Heisenberg plaquette curvature,
    division-free (Coq ``plaquette_curvature_z``).
(d) ``R1212`` -- metric-derived Levi-Civita curvature of ``g=diag(1,w)``;
    doubling witness ``w=(1,2,4,...)`` gives ``R1212(w,0) == -1/4``
    (Coq ``curved_witness``).
(e) a larger curved-metric field: the full curvature profile across many nodes.

Run::

    python benchmarks/physics/curvature.py
"""

from __future__ import annotations

import os
import sys
from fractions import Fraction as F

# Allow running directly from the benchmarks/physics directory.
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..")))

from spine_pde.curvature import (  # noqa: E402
    R1212,
    Heisenberg,
    christoffel_fd,
    commutator_curvature,
    gauss_bonnet_boundary,
    is_flat,
    riemann_fd,
    riemann_is_second_difference,
    total_curvature,
)

Row = tuple  # (name, computed, expected, tier, ok)
results: list = []


def check(name, computed, expected, tier):
    ok = computed == expected
    results.append((name, computed, expected, tier, ok))
    flag = "OK " if ok else "XX "
    print(f"  [{flag}][{tier}] {name}: computed={computed}  expected={expected}")
    return ok


def rule(c="-"):
    print(c * 72)


def main() -> int:
    rule("=")
    print("spine_pde DISCRETE-CURVATURE BENCHMARK  (finite/exact, no continuum)")
    rule("=")

    # ------------------------------------------------------------------ #
    # (a) riemann_fd second difference on a curved metric
    # ------------------------------------------------------------------ #
    print("\n[a] riemann_fd -- second-difference Riemann curvature")
    wsq = lambda n: F(n) ** 2  # curved metric field w(n) = n^2  (exact)
    # Exact Coq cross-check: curvature of n^2 at node 0 is exactly 2.
    check("riemann_fd(n^2, 0)", riemann_fd(wsq, 0), 2, "Th_coqc")
    # Second-difference of a quadratic is the constant 2 everywhere.
    prof = [riemann_fd(wsq, j) for j in range(6)]
    check("riemann_fd(n^2, j) const-2 profile", all(v == 2 for v in prof),
          True, "Fin")
    # closed-form second-difference agrees with the recursive definition.
    check("riemann_fd == closed 2nd-diff (n^2, 3)",
          riemann_fd(wsq, 3), riemann_is_second_difference(wsq, 3), "Fin")
    # an affine (linear) field is flat.
    lin = lambda n: F(3) * n - F(1)
    check("affine field is_flat", is_flat(lin, 2), True, "Fin")
    print(f"      riemann_fd(n^2, 0..5) = {prof}")

    # ------------------------------------------------------------------ #
    # (b) Gauss-Bonnet: bulk sum telescopes to the boundary
    # ------------------------------------------------------------------ #
    print("\n[b] total_curvature -- discrete Gauss-Bonnet telescoping")
    # Exact Coq cross-check: total curvature of n^2 over [0,2) is exactly 4.
    check("total_curvature(n^2, 2)", total_curvature(wsq, 2), 4, "Th_coqc")
    # bulk sum == boundary Christoffel difference, for several N (exact identity).
    tele_ok = all(
        total_curvature(wsq, N) == gauss_bonnet_boundary(wsq, N)
        for N in range(0, 8)
    )
    check("sum == boundary (Gauss-Bonnet, N=0..7)", tele_ok, True, "Th_coqc")
    # a cubic metric to prove telescoping is not special to quadratics.
    cub = lambda n: F(n) ** 3
    check("cubic: sum==boundary (N=5)",
          total_curvature(cub, 5), gauss_bonnet_boundary(cub, 5), "Fin")
    print(f"      boundary form christoffel_fd(n^2,5)-christoffel_fd(n^2,0) "
          f"= {christoffel_fd(wsq, 5) - christoffel_fd(wsq, 0)}")

    # ------------------------------------------------------------------ #
    # (c) Heisenberg commutator curvature  z == a*b
    # ------------------------------------------------------------------ #
    print("\n[c] commutator_curvature -- Heisenberg plaquette (division-free)")
    # Exact Coq cross-check: centre of [X,Y] equals a*b exactly.
    check("commutator_curvature(3,5) == 3*5",
          commutator_curvature(3, 5), 15, "Th_coqc")
    # antisymmetry of the LOOP direction: [Y,X] centre negates [X,Y] centre.
    # (arg-swap in commutator_curvature is symmetric since a*b==b*a; the real
    #  antisymmetry lives in the group commutator's ORDER, so build it directly.)
    X, Y = Heisenberg(3, 0, 0), Heisenberg(0, 5, 0)
    fwd = X.commutator(Y).z   # == a*b == 15
    rev = Y.commutator(X).z   # reversed loop == -a*b == -15
    check("reverse antisymmetric: [Y,X].z == -[X,Y].z",
          rev, -fwd, "Fin")
    # abelian / same-direction loop is flat.
    check("same-direction flat: R(a,0) == 0",
          commutator_curvature(7, 0), 0, "Fin")
    # exact over Fractions too (no division anywhere).
    check("exact rational R(2/3, 3/4) == 1/2",
          commutator_curvature(F(2, 3), F(3, 4)), F(1, 2), "Fin")

    # ------------------------------------------------------------------ #
    # (d) metric-derived Levi-Civita R1212  == -1/4 witness
    # ------------------------------------------------------------------ #
    print("\n[d] R1212 -- Levi-Civita curvature of g = diag(1, w)")
    doubling = lambda n: F(2) ** n  # w = (1, 2, 4, 8, ...)  exact
    # Exact Coq cross-check: the curved witness is exactly -1/4.
    check("R1212(doubling, 0) == -1/4", R1212(doubling, 0), F(-1, 4), "Th_coqc")
    # a constant metric field is flat.
    const = lambda n: F(5)
    check("constant metric flat: R1212 == 0", R1212(const, 0), 0, "Fin")

    # ------------------------------------------------------------------ #
    # (e) larger curved-metric field: the full curvature profile
    # ------------------------------------------------------------------ #
    print("\n[e] larger curved metric -- curvature profile across nodes")
    # exponential-ish curved metric w(n) = (n+1)^2 + 1  (strictly positive)
    wfield = lambda n: F((n + 1) ** 2 + 1)
    profile = [(n, R1212(wfield, n)) for n in range(8)]
    for n, r in profile:
        print(f"      node {n}: w={wfield(n)!s:>3}  R1212={r}")
    # sanity: every value is an exact Fraction and finite (no continuum blow-up).
    all_exact = all(isinstance(r, (int, F)) for _, r in profile)
    check("profile all exact-rational & finite", all_exact, True, "Fin")
    # curvature decays toward flat as the metric flattens at large n.
    mags = [abs(r) for _, r in profile]
    check("|R1212| decays at large n", mags[-1] < mags[1], True, "Fin")

    # ------------------------------------------------------------------ #
    # results table
    # ------------------------------------------------------------------ #
    print()
    rule("=")
    print("RESULTS TABLE")
    rule("=")
    print(f"{'#':>2}  {'tier':<8} {'check':<42} {'value':<12} {'ok'}")
    rule("-")
    for i, (name, computed, expected, tier, ok) in enumerate(results, 1):
        val = str(computed)
        if len(val) > 11:
            val = val[:10] + "…"
        print(f"{i:>2}  {tier:<8} {name[:42]:<42} {val:<12} {'PASS' if ok else 'FAIL'}")
    rule("-")
    npass = sum(1 for r in results if r[4])
    nth = sum(1 for r in results if r[3] == "Th_coqc")
    print(f"{npass}/{len(results)} checks PASS "
          f"({nth} exact Coq-theorem cross-checks, "
          f"{len(results) - nth} finite [Fin] checks)")
    rule("=")
    return 0 if npass == len(results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
