"""example_evolve.py -- under-damped oscillation vs over-damped decay.

Evolve the master spine PDE on a symmetric double well ``V = (x**2 - 1)**2 / 4``
(minima at ``x = +-1``).  We start every node displaced inside the right-hand
basin and let it settle into the ``x = +1`` readout state.

Linearising the double well about its minimum gives an effective stiffness
``V''(1) = 2``, so each node is the telegraph oscillator ``M w'' + D w' + 2 w = 0``
(the uniform initial state sits in the ``lam = 0`` graph mode, so ``L_R x = 0``
and the on-site well sets the dynamics).  The damping ``D`` decides the regime:

    D**2 <  4 M V''(1) = 8   ->  under-damped  -> OSCILLATES into the well
    D**2 >  8                ->  over-damped   -> DECAYS monotonically into the well

We run the *same* spine at low and high damping and watch the flip.

Run:  python examples/example_evolve.py
"""

from __future__ import annotations

import numpy as np

from spine_pde import DoubleWell, RetainedDifferenceGraph, Spine, Telegraph


def _count_overshoots(traj: np.ndarray, target: float) -> int:
    """Number of times the trajectory crosses its target (oscillation counter)."""
    signs = np.sign(traj - target)
    signs = signs[signs != 0]
    return int(np.count_nonzero(np.diff(signs) != 0))


def _run(D: float, n_steps: int = 4000):
    """Evolve a uniform double-well spine at damping ``D``; return node-0 trajectory."""
    g = RetainedDifferenceGraph.ring(8)            # small graph, sparse L_R
    x0 = np.full(g.n_nodes, 0.3)                    # uniform -> lam=0 mode, in +1 basin
    spine = Spine(
        M=1.0, D=D, K=1.0, graph_or_L=g,
        gradV=DoubleWell(), x0=x0, v0=np.zeros(g.n_nodes),
        dtheta=5e-3,
    )
    hist = spine.evolve(n_steps, record=True, stride=1)
    arr = hist.as_arrays()
    return arr["theta"], arr["x"][:, 0], spine


def _sparkline(theta: np.ndarray, traj: np.ndarray, target: float, width: int = 56) -> str:
    """Tiny ASCII plot of a trajectory relative to its target well."""
    idx = np.linspace(0, len(traj) - 1, width).astype(int)
    y = traj[idx]
    lo, hi = min(y.min(), target), max(y.max(), target)
    span = hi - lo or 1.0
    ramp = " .:-=+*#%@"
    rows = []
    for val in y:
        k = int((val - lo) / span * (len(ramp) - 1))
        rows.append(ramp[k])
    return "".join(rows)


def main() -> None:
    # Effective linearised stiffness of the double well at x=1: V''(1) = 2.
    tg_lin = Telegraph(1.0, 1.0, 2.0)  # K*lam replaced by V''=2 for the crossover
    D_crit = float(np.sqrt(8.0))       # D^2 = 4 M V'' = 8
    print("double well V=(x^2-1)^2/4, minima x=+-1, linearised stiffness V''(1)=2")
    print(f"critical damping D_crit = sqrt(4 M V'') = {D_crit:.4f}")
    print(f"  (mass at D_crit = D/2M = {D_crit / 2:.4f})\n")

    for label, D in (("under-damped (D=0.5)", 0.5), ("over-damped  (D=6.0)", 6.0)):
        theta, traj, spine = _run(D)
        regime = "OSCILLATORY (quantum-like)" if D < D_crit else "DECAY (classical)"
        overshoots = _count_overshoots(traj, 1.0)
        final = traj[-1]
        print(f"{label}  ->  {regime}")
        print(f"  node x: 0.30 -> {final:.4f}  (well at +1.0)   "
              f"overshoots of target: {overshoots}")
        print(f"  energy: {spine_energy_start(D):.4f} -> {spine.energy():.4f}")
        print(f"  |{_sparkline(theta, traj, 1.0)}|")
        print()

    print("Same spine, same well: low damping OSCILLATES across the +1 readout")
    print("(under-damped, many overshoots); high damping DECAYS straight into it")
    print("(over-damped, zero overshoots). The knife-edge is D_crit = sqrt(8).")


def spine_energy_start(D: float) -> float:
    """Initial total energy of the run at damping ``D`` (before evolving)."""
    g = RetainedDifferenceGraph.ring(8)
    x0 = np.full(g.n_nodes, 0.3)
    spine = Spine(M=1.0, D=D, K=1.0, graph_or_L=g, gradV=DoubleWell(),
                  x0=x0, dtheta=5e-3)
    return spine.energy()


if __name__ == "__main__":
    main()
