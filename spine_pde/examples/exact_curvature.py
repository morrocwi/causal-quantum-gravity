"""Exact-mode curvature: reproduce the theorem values with rational arithmetic.

Run:  python examples/exact_curvature.py
"""

from fractions import Fraction

from spine_pde import Telegraph, curvature as cv


def main() -> None:
    wsq = lambda n: n * n  # metric field w(n) = n**2

    print("discrete Riemann of w=n**2 at 0 :", cv.riemann_fd(wsq, 0), "(theorem: 2)")
    print("Gauss-Bonnet total curv N=2     :", cv.total_curvature(wsq, 2), "(theorem: 4)")
    print("metric R1212(w=n**2, n=1)       :", cv.R1212(wsq, 1), "(exact 5/4)")

    a, b = Fraction(3, 5), Fraction(-2)
    print("Heisenberg commutator curvature :", cv.commutator_curvature(a, b), "= a*b =", a * b)

    tg = Telegraph(1, 1, 1)  # exact rational telegraph analyser
    print("disc(M=D=K=1, lam=1)            :", tg.discriminant(1), "(theorem: -3)")
    print("regime                          :", tg.regime(1))
    print("mass = D/2M                     :", tg.mass(), "  tau_c = M/D:", tg.tau_c())


if __name__ == "__main__":
    main()
