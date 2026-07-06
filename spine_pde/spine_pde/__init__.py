"""spine_pde -- a public reference implementation of the discrete tensor-PDE
spine field theory.

Everything is **finite / discrete**; the continuum is refused.  The package has
four pillars:

* :mod:`spine_pde.graph`      -- retained-difference graph -> sparse ``L_R``.
* :mod:`spine_pde.spine`      -- the master spine PDE, symplectic leapfrog solver.
* :mod:`spine_pde.telegraph`  -- per-mode regime / horizon analysis.
* :mod:`spine_pde.curvature`  -- discrete Riemann / Gauss-Bonnet / commutator curvature.

Two numeric modes run throughout: **EXACT** (``fractions.Fraction``, matching the
Coq theorems bit-for-bit on small problems) and **FAST** (``numpy`` / ``scipy``
sparse float64, for large / stiff / hard problems).

Quick start
-----------
>>> import numpy as np
>>> from spine_pde import RetainedDifferenceGraph, Spine, Telegraph
>>> g = RetainedDifferenceGraph.ring(1000)
>>> s = Spine(M=1.0, D=0.1, K=1.0, graph_or_L=g, x0=np.random.default_rng(0).standard_normal(1000))
>>> _ = s.evolve(100)
>>> tg = Telegraph(1, 1, 1)                 # exact rational analyser
>>> tg.discriminant(1)                      # disc(1,1,1,1) == -3
Fraction(-3, 1)
"""

from __future__ import annotations

from .graph import (
    RetainedDifferenceGraph,
    adjacency_kernel,
    gaussian_kernel,
)
from .potentials import DoubleWell, Potential, Quadratic, ZeroPotential
from .spine import Spine, SpineHistory
from .telegraph import CRITICAL, DECAY, OSCILLATORY, Telegraph
from . import curvature
from . import exact

__version__ = "0.1.0"

__all__ = [
    "__version__",
    # graph
    "RetainedDifferenceGraph",
    "gaussian_kernel",
    "adjacency_kernel",
    # potentials
    "Potential",
    "DoubleWell",
    "Quadratic",
    "ZeroPotential",
    # spine
    "Spine",
    "SpineHistory",
    # telegraph
    "Telegraph",
    "OSCILLATORY",
    "DECAY",
    "CRITICAL",
    # curvature module
    "curvature",
    # exact-rational front-end
    "exact",
]
