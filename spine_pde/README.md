# spine-pde

A public, self-contained reference implementation of the **discrete tensor-PDE
spine field theory**. Everything is **finite / discrete** — the continuum is
refused. Where the continuum would inject an infinity (a limit, a blow-up, a UV
divergence), this package keeps a finite retained-difference graph and reads the
answer off it directly.

Two numeric modes run throughout:

- **EXACT** — `fractions.Fraction` arithmetic that reproduces the underlying
  formal (Coq) theorems *bit-for-bit* on small problems.
- **FAST** — `numpy` / `scipy.sparse` `float64` for large, stiff, hard problems.
  The Laplacian is assembled sparse and every solver step is a single sparse
  mat-vec, so it scales to `10**4`–`10**5` nodes.

```bash
git clone https://github.com/morrocwi/causal-quantum-gravity.git && cd causal-quantum-gravity/spine_pde
pip install -e .          # editable install
pip install -e '.[dev]'   # + pytest + sympy
pytest                    # 43 tests, exact-mode values checked against theorems
python examples/quickstart.py   # runnable end-to-end example, see examples/
```

## The theory in four modules

| module | what it provides |
| --- | --- |
| `spine_pde.graph` | retained-difference graph → sparse Laplacian `L_R = D_W − W` |
| `spine_pde.spine` | the master spine PDE + symplectic leapfrog solver |
| `spine_pde.telegraph` | per-mode regime / horizon analysis |
| `spine_pde.curvature` | discrete Riemann / Gauss-Bonnet / metric / commutator curvature |

### 1. Retained-difference graph → `L_R`

Nodes carry states `x_i`; each retained edge `(i, j)` carries an information
difference `dI_ij` and address weight `A_ij`. A kernel `W_ij = K(dI_ij, A_ij)`
(default Gaussian: large differences are exponentially forgotten) gives the
positive-semidefinite graph Laplacian `L_R = D_W − W`.

```python
from spine_pde import RetainedDifferenceGraph
g = RetainedDifferenceGraph.grid2d(200, 200)   # 40k nodes
L = g.laplacian()                              # scipy.sparse CSR, O(n) nnz
```

### 2. Master spine PDE

    M x'' + D x' + K L_R x + gradV(x) = J − eta

evolved with the symplectic leapfrog update named in the theory:

    V[n+1] = V[n] + dtheta·( −(D/M)V[n] − (K/M) L_R x[n] − gradV(x[n])/M + (J−eta)/M )
    x[n+1] = x[n] + dtheta·V[n+1]

```python
import numpy as np
from spine_pde import Spine
s = Spine(M=1.0, D=0.2, K=1.0, graph_or_L=g,       # gradV defaults to a double well
          x0=np.random.default_rng(0).standard_normal(g.n_nodes)*0.1)
s.evolve(2000)
s.energy()          # kinetic + Dirichlet + on-site potential (shadow energy)
```

`M, D, K` may be scalars or per-node arrays (diagonal tensor). `J` and `eta` may
be arrays or callables `f(x, theta)`. `gradV` may be a built-in `Potential`
(`DoubleWell`, `Quadratic`, `ZeroPotential`) or any callable `x → force`.

### 3. Telegraph regime analysis

Projected onto an `L_R` eigenmode `lam`, the spine is a telegraph oscillator
`M w'' + D w' + K lam w = 0`.

    disc(lam) = D² − 4 M K lam            crossover  lam_c = D² / (4 M K)
    disc < 0 (lam > lam_c): under-damped / OSCILLATORY  (quantum readout)
    disc > 0 (lam < lam_c): over-damped  / DECAY        (classical readout)
    disc = 0 (lam = lam_c): critically damped — the horizon / agency knife-edge
    mass = D/(2M) = 1/(2 tau_c),  tau_c = M/D,  Gamma(lam) = K lam / D

```python
from spine_pde import Telegraph
tg = Telegraph(1, 1, 1)          # ints → EXACT rational mode
tg.discriminant(1)               # Fraction(-3, 1)
tg.regime(1)                     # 'under-damped/OSCILLATORY'
tg.classify_spectrum(lam_array)  # vectorised over a whole spectrum (FAST mode)
```

### 4. Discrete curvature

Finite differences of a 1-D metric field `w` — exact-rational capable, mirroring
the formal definitions:

```python
from spine_pde import curvature as cv
cv.riemann_fd(lambda n: n*n, 0)        # 2   (discrete Riemann of w=n²)
cv.total_curvature(lambda n: n*n, 2)   # 4   (Gauss-Bonnet telescopes to boundary)
cv.R1212(lambda n: n*n, 1)             # Fraction(5, 4)  (Levi-Civita, g=diag(1,w))
cv.commutator_curvature(3, 5)          # 15  (Heisenberg plaquette centre = a·b)
```

## Command line

Every pillar is reachable from the shell via `python -m spine_pde`:

```bash
python -m spine_pde curvature --field square --N 2      # riemann=2, GB=4, commutator=6
python -m spine_pde crossover --M 1 --D 1 --K 1 --lam 1 --exact   # disc=-3, lam_c=1/4
python -m spine_pde crossover --graph grid --size 10000          # classify a real spectrum
python -m spine_pde spectrum  --graph grid --size 10000          # extreme sparse L_R eigenvalues
python -m spine_pde evolve    --graph ring --size 2000 --steps 200
```

## Hard-problem benchmark

`benchmarks/hard_problem.py` builds a ≥50 000-node sparse lattice, evolves the
stiff spine, and computes the spectral crossover with sparse ARPACK
(shift-invert both ends) — proving the package never forms a dense `N×N` object:

```bash
python benchmarks/hard_problem.py            # ~50k nodes
python benchmarks/hard_problem.py 100000     # 100k nodes
```

It prints the wall-clock split and a memory-safety line (sparse `L_R` is ~3 MB
where a dense one would be ~19 GB — 6000× smaller, and refused).

## Audit, don't believe

The EXACT mode exists so you never have to take a number on faith. Every
exact-mode output is designed to equal a *checked Coq theorem* bit-for-bit, and
the test suite asserts exactly those values:

| readout | value | Coq theorem |
| --- | --- | --- |
| `riemann_fd(n², 0)` | `2` | `curvature_nonzero_witness` |
| `total_curvature(n², 2)` | `4` | `total_curv_wsq_2` |
| `Telegraph(1,1,1).discriminant(1)` | `-3` | telegraph `witnesses` |
| `Telegraph(M,D,K).mass()` | `D/(2M)` | telegraph mass = `1/(2 τ_c)` |
| `commutator_curvature(a, b)` | `a·b` | `plaquette_curvature_z` |
| `R1212((1,2,4,…), 0)` | `-1/4` | `curved_witness` |

Run `pytest` and read the assertions: the package *reads the answer off a finite
structure*, it does not ask you to believe a floating-point coincidence.

## The continuum is refused

There is deliberately no `h → 0`, no limit, no continuum option anywhere in the
API. The theory treats every classical infinity (a limit, a blow-up, a UV/IR
divergence) as an artefact of taking the continuum; this package stays on the
finite retained-difference graph and computes the exact discrete readout instead.

## How it stays sparse and scales

- `L_R` is built from COO triplets straight into a `scipy.sparse` CSR matrix —
  memory is O(edges), never O(n²).
- Each leapfrog step's only matrix operation is the sparse mat-vec `L_R @ x`, so
  a step costs O(nnz(L_R)). A 4-neighbour lattice has ≤5 nnz/row, i.e. O(n).
- Spectral regime analysis uses `scipy.sparse.linalg.eigsh` on `L_R` (the code
  never forms a dense Laplacian in the fast path).
- Benchmarked: a 115 600-node grid builds in ~0.2 s and runs 50 spine steps in
  ~0.2 s on a laptop.

## Layout

```
spine_pde/
  graph.py        RetainedDifferenceGraph, kernels, sparse L_R (+ exact rational)
  spine.py        Spine solver, SpineHistory
  telegraph.py    Telegraph analyser (exact + vectorised float)
  curvature.py    finite-difference / metric / commutator curvature
  potentials.py   DoubleWell, Quadratic, ZeroPotential
  exact.py        exact-rational front-end + checkable Coq witnesses (THEOREMS)
  cli.py          `python -m spine_pde` command-line interface
  __main__.py     module entry point
tests/            pytest suite (exact values checked against the theorems)
benchmarks/       hard_problem.py — large sparse scaling benchmark
examples/         quickstart.py, exact_curvature.py,
                  example_crossover.py, example_evolve.py
```

## License

MIT. Built fresh from the published equations; self-contained and public-safe.
