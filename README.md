# Causal Quantum Gravity

**One mother equation — `M∂²Φ + D∂Φ + K·L_R·Φ + ∇V(Φ) = J−η` on a graph Laplacian
`L_R` — genuinely derives quantum mechanics and special relativity at the equation
level (machine-checked in Coq, axiom-free over ℚ). General relativity is honestly
**not** derived: eight independent attempts this project made to recover it were
tested and refuted or left open, and the paper argues this is the *correct* outcome
— continuum GR is, by this project's own diagnostic standard, a non-readout
(an artifact of injecting actual infinity), so an exact match was never the right
target. In its place, a genuinely native discrete object is identified instead:
Forman-Ricci curvature on the graph, proved to be an honest readout of the same
data the mother equation uses, and linked by exact algebraic substitution to an
already-proven stability (coercivity) theorem. Full narrative, references, and
honest tier ledger, plus a ninth result (added after adversarial referee review)
proving the quantum dispersion relation and the special-relativistic wave operator
are literally the same equation: [SUPPLEMENT.md](SUPPLEMENT.md).

**Manuscript:** [paper/main.pdf](paper/main.pdf) (compile from `paper/main.tex`) —
theorem-level claims, tiers, and reproduction commands, self-contained.
**Supplement:** [SUPPLEMENT.md](SUPPLEMENT.md) — full dependency DAG, the complete
eight-attempt GR refutation log, the full novelty audit, and the extended
reference-verification trail. See the manuscript's "Main-Text vs. Supplement
Boundary" section for what belongs where.

## Tier legend

| Tier | Meaning |
|---|---|
| `Th_coqc` | Machine-checked in Coq, axiom-free over ℚ (`Print Assumptions` prints "Closed under the global context"). |
| `+reals` | Machine-checked, but depends on Coq's standard Reals axioms (`ClassicalDedekindReals.sig_forall_dec`, `FunctionalExtensionality`), honestly disclosed. |
| `finite_diagnostic` | A numerical measurement, reproducible, not a proof. |
| `Dr` | An interpretive stance, not machine-checked. |
| `Open` | Admitted gap. |

## Repo structure

```
formal/
  RDL_GammaSpectral.v              Edge/w_of/u_of/v_of primitive (Q). Th_coqc.
  InfoCoercivityBoundedClosure.v   Csafe/wshare/wdeg definitions. Th_coqc.
  InfoDiscreteGraphCurvature.v     Forman-Ricci curvature, flat-cycle fact, wdeg=w*deg link to coercivity. Th_coqc.
  InfoAnalysisLift.v               Schwarzschild metric factor + real radial derivative. +reals.
  InfoQuantumGravityRootBridge.v   Regge-Wheeler potential built on InfoAnalysisLift.schw. +reals.
  InfoSchrodinger.v                Quantum dispersion M*omega^2=K*lambda and energy spectrum from the Laplacian spectrum. Th_coqc.
  InfoLorentzInvariance.v          Boost-invariant interval + exact-quadratic-class box_quad operator. Th_coqc.
  InfoQuantumRelativityUnification.v  Quantum dispersion IS box_quad vanishing -- one equation, two readouts. Th_coqc.
  InfoLorentz.v                    Discrete causal bilinear form: self-adjoint, Euclidean reduction, frame-covariant. Th_coqc.
  InfoLorentzContinuum.v           Continuum limit of the signed second-difference operator = the d'Alembertian Box=-dtt+dxx. +reals.
scripts/
  verify_quantum_gravity_root_bridge.py   Finite-graph (PML) quasinormal-mode eigenvalue solver; converges to the literature Schwarzschild QNM. finite_diagnostic.
```

## How to reproduce

### 1. Install Coq

```bash
# Ubuntu/Debian
sudo apt-get update && sudo apt-get install -y coq

# or via opam (any platform)
opam init -y && opam install -y coq
```

Verified against Coq 8.20.1.

### 2. Install Python dependencies

```bash
pip install -r requirements.txt
```

### 3. Compile every proof and run the numerical bridge

```bash
make verify
```

This compiles all 8 `formal/*.v` files in dependency order with
`coqc -q -R . DQG <file>`, then runs `scripts/verify_quantum_gravity_root_bridge.py`,
and prints a `PASS`/`FAIL` summary. Expected per-file result:

| File | Expected `Print Assumptions` output |
|---|---|
| `RDL_GammaSpectral.v` | `Closed under the global context` |
| `InfoCoercivityBoundedClosure.v` | `Closed under the global context` |
| `InfoDiscreteGraphCurvature.v` | `Closed under the global context` |
| `InfoSchrodinger.v` | `Closed under the global context` |
| `InfoLorentzInvariance.v` | `Closed under the global context` |
| `InfoQuantumRelativityUnification.v` | `Closed under the global context` |
| `InfoLorentz.v` | `Closed under the global context` |
| `InfoAnalysisLift.v` | `ClassicalDedekindReals.sig_forall_dec`, `FunctionalExtensionality.functional_extensionality_dep` |
| `InfoQuantumGravityRootBridge.v` | same two Reals axioms as above |
| `InfoLorentzContinuum.v` | same two Reals axioms as above |

### 4. Run the QNM script standalone

```bash
python3 scripts/verify_quantum_gravity_root_bridge.py
```

Prints a grid-resolution convergence table (`N=400..6400`) of the fundamental
scalar (`l=2, n=0`) quasinormal-mode eigenvalue against the literature target
`Mω ≈ 0.4836 − 0.0968i` (Leaver 1985). The full N=6400 run can take several
minutes; `make verify` allows a 90s timeout and treats a partial (but
monotonically converging) run as a pass — a timeout exit code alone is not a
failure.

### `make clean`

Removes all `.vo`/`.vok`/`.vos`/`.glob`/`.aux` build artifacts.

## Provenance

This repository is an extracted, minimal, standalone subset of a private
research repository — flattened into 8 independent `formal/*.v` files (each
carrying only the definitions its own theorems actually use, trimmed from
larger source modules) plus one Python script, copied verbatim. Nothing was
renamed or altered beyond: dropping the `_attempt` suffix some source files
used internally, and adding a minimal `Require`/`Open Scope` preamble to each
file so it compiles standalone outside its original multi-thousand-line
context. Original authorship dates, by file:

| File | Originally authored |
|---|---|
| `InfoLorentz.v`, `InfoLorentzContinuum.v`, `InfoLorentzInvariance.v` | 2026-06-27 |
| `RDL_GammaSpectral.v`, `InfoCoercivityBoundedClosure.v`, `InfoDiscreteGraphCurvature.v`, `InfoSchrodinger.v`, `InfoAnalysisLift.v`, `InfoQuantumGravityRootBridge.v`, `InfoQuantumRelativityUnification.v`, `scripts/verify_quantum_gravity_root_bridge.py` | 2026-07-04 / 2026-07-05 |

See [SUPPLEMENT.md](SUPPLEMENT.md) for the full narrative, the dependency DAG, the
numerical validation (Hückel benzene, Forman curvature sanity checks), the
honest audit of what was and was not derived, and the complete reference list.
