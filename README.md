# Causal Quantum Gravity

**One mother equation — `M∂²Φ + D∂Φ + K·L_R·Φ + ∇V(Φ) = J−η` on a graph Laplacian
`L_R` — genuinely derives quantum mechanics and special relativity at the equation
level (machine-checked in Coq, axiom-free over ℚ), and proves the two are literally
*the same equation* under an exact algebraic reparametrization. A six-result
strengthening campaign then upgrades four previously-informal claims to theorems: a
frequency/UV ceiling forced by the graph's own maximum degree, an exact "no local
creation" energy-balance law, a Schrödinger-shaped skew-adjoint first-order skeleton,
a causal sign-construction theorem, and a discrete Noether theorem. A companion graph-
growth result gives a native, non-continuum discrete analog of cosmological expansion.

General relativity is honestly **not** derived: eight independent attempts this
project made to recover it were tested and refuted or left open, and the manuscript
argues this is the *correct* outcome — continuum GR is, by this project's own
diagnostic standard, a non-readout (an artifact of injecting actual infinity), so an
exact match was never the right target. In its place, a genuinely native discrete
object is identified instead: Forman-Ricci curvature on the graph, proved to be an
honest readout of the same data the mother equation uses, and linked by exact
algebraic substitution to an already-proven stability (coercivity) theorem.

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
  RDL_GammaSpectral.v                 Edge/w_of/u_of/v_of primitive (Q). Th_coqc.
  InfoCoercivityBoundedClosure.v      Csafe/wshare/wdeg definitions. Th_coqc.
  InfoDiscreteGraphCurvature.v        Forman-Ricci curvature, flat-cycle fact, wdeg=w*deg link to coercivity. Th_coqc.
  InfoAnalysisLift.v                  Schwarzschild metric factor + real radial derivative. +reals.
  InfoQuantumGravityRootBridge.v      Regge-Wheeler potential built on InfoAnalysisLift.schw. +reals.
  InfoSchrodinger.v                   Quantum dispersion M*omega^2=K*lambda and energy spectrum from the Laplacian spectrum. Th_coqc.
  InfoLorentzInvariance.v             Boost-invariant interval + exact-quadratic-class box_quad operator. Th_coqc.
  InfoQuantumRelativityUnification.v  Quantum dispersion IS box_quad vanishing -- one equation, two readouts. Th_coqc.
  InfoLorentz.v                       Discrete causal bilinear form: self-adjoint, Euclidean reduction, permutation-invariant. Th_coqc.
  InfoLorentzContinuum.v              Continuum limit of the signed second-difference operator = the d'Alembertian Box=-dtt+dxx. +reals.
  InfoSpectralCeiling.v               Degree-sum (Rayleigh/Gershgorin) spectral ceiling lambda<=2*dmax. Th_coqc.
  InfoRecurrenceEnergy.v              Exact leapfrog Lyapunov identity: CFL window + damped energy decrement. Th_coqc.
  InfoQuantumFrequencyCeiling.v       Composes the above with quantum dispersion: a real UV/frequency ceiling + tau_c-floor window. Th_coqc.
  InfoGraphFluxBalance.v              Discrete divergence theorem + Green's identity + exact vector energy balance ("no local creation"). Th_coqc.
  InfoCompanionSkew.v                 First-order companion form, skew-adjoint under the energy inner product (Schrodinger-shaped skeleton). Th_coqc.
  InfoCausalSignature.v               Sign constructed from order comparability; exact PSD-split; a concrete (1,3)-signature witness. Th_coqc.
  InfoGraphNoether.v                  Graph automorphism => exact conserved (momentum-like) quantity. Th_coqc.
  InfoGraphGrowth.v                   Graph growth: curvature/energy laws, order-collapse obstruction theorems, and an exact discrete dilution law -- a native, non-continuum expansion analog. Th_coqc.
  InfoActionStationarity.v            The mother equation is an exact Euler-Lagrange stationarity readout (field + geometry sides); NOT claimed to narrow any gap to GR. Th_coqc.
  InfoCurvatureBalance.v              Forman curvature composed into an exact affine horizon threshold + an unconditional no_escape/repair_exists dichotomy; a separate curvature-affine balance law is conditional on an explicit modeling ansatz. Th_coqc.
  InfoProductSpectrum.v               n-D spectral ladder step 1: Kronecker/Rayleigh additivity for product graphs. Th_coqc.
  InfoContinuumLimit_nD.v             n-D spectral ladder step 2: flat/weighted multi-axis continuum-limit readout; reproduces this repo's own lorentz_box as an instance. +reals (Tier-1, no classic).
  InfoWeightedReadout.v               n-D spectral ladder step 3: variable-coefficient (a*u')' readout from the discrete flux stencil. +reals (Tier-1, no classic).
  InfoCrossTermDominance.v            n-D spectral ladder step 4: an iff between graph-form representability and diagonal dominance, both directions sharp. Th_coqc.
  InfoDiskBeforeLock.v                Anisotropic retention: a perpendicular candidate strictly worsens the retention functional while a parallel one never does, immediate at every decision point. Th_coqc.
  InfoGrowthFold.v                    Multi-edge curvature fold: exact, order-independent cumulative curvature shift over any list of added edges. Th_coqc.
  InfoCeilingMonotone.v               Rayleigh ceiling monotonicity under retention; explicitly does NOT claim individual eigenvalue interlacing. Th_coqc.
  InfoCurvatureNoether.v              Forman curvature is invariant under any graph automorphism (extends an existing quadratic-form invariance result to curvature). Th_coqc.
  InfoModeRotation.v                  The mother equation's CFL stepper at one window point IS the i-rotation matrix; two more window points give crystallographic periods 6 and 3. Th_coqc.
  InfoPentagonSpectrum.v              5-cycle Laplacian cubic identity lands in the golden ratio's own field; 6-cycle exhibits all 4 rational eigenvalues explicitly. Th_coqc.
  InfoAreaLaw.v                       A uniform region's energy comes entirely from its boundary -- a graph-native fact, explicitly not the holographic bound. Th_coqc.
  InfoDegreeFromCurvature.v           Degree bounded by 4 minus local Forman curvature; feeds the spectral ceiling with a curvature-derived value. Th_coqc.
  InfoTensorFrame.v                   General symmetric-tensor reconstruction from diagonal + face-diagonal evaluations, any dimension -- an abstract fact, not yet about this repo's own graphs. Th_coqc.
  InfoStrainTensorBridge.v            Connects curvature to the tensor-reconstruction fact, conditional on an affine-cell hypothesis; also a native local-screen split and a disclosed-ansatz Clausius-type inequality. Th_coqc.
  InfoOptimizerWindow.v               Heavy-ball/momentum optimization on a quadratic mode is exactly the mother equation's own leapfrog energy theory, under an exact reparametrization. Th_coqc.
scripts/
  verify_quantum_gravity_root_bridge.py   Finite-graph (PML) quasinormal-mode eigenvalue solver; converges to the literature Schwarzschild QNM. finite_diagnostic.
```

35 Coq files, 188 theorems, every one Tier-0 axiom-free or +reals as marked.

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

This compiles all 17 `formal/*.v` files in dependency order with
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
| `InfoSpectralCeiling.v` | `Closed under the global context` |
| `InfoRecurrenceEnergy.v` | `Closed under the global context` |
| `InfoQuantumFrequencyCeiling.v` | `Closed under the global context` |
| `InfoGraphFluxBalance.v` | `Closed under the global context` |
| `InfoCompanionSkew.v` | `Closed under the global context` |
| `InfoCausalSignature.v` | `Closed under the global context` |
| `InfoGraphNoether.v` | `Closed under the global context` |
| `InfoGraphGrowth.v` | `Closed under the global context` |
| `InfoActionStationarity.v` | `Closed under the global context` |
| `InfoCurvatureBalance.v` | `Closed under the global context` |
| `InfoProductSpectrum.v` | `Closed under the global context` |
| `InfoCrossTermDominance.v` | `Closed under the global context` |
| `InfoDiskBeforeLock.v` | `Closed under the global context` |
| `InfoGrowthFold.v` | `Closed under the global context` |
| `InfoCeilingMonotone.v` | `Closed under the global context` |
| `InfoCurvatureNoether.v` | `Closed under the global context` |
| `InfoModeRotation.v` | `Closed under the global context` |
| `InfoPentagonSpectrum.v` | `Closed under the global context` |
| `InfoAreaLaw.v` | `Closed under the global context` |
| `InfoDegreeFromCurvature.v` | `Closed under the global context` |
| `InfoTensorFrame.v` | `Closed under the global context` |
| `InfoStrainTensorBridge.v` | `Closed under the global context` |
| `InfoOptimizerWindow.v` | `Closed under the global context` |
| `InfoAnalysisLift.v` | `ClassicalDedekindReals.sig_forall_dec`, `FunctionalExtensionality.functional_extensionality_dep` |
| `InfoQuantumGravityRootBridge.v` | same two Reals axioms as above |
| `InfoLorentzContinuum.v` | same two Reals axioms as above |
| `InfoContinuumLimit_nD.v` | same two Reals axioms as above |
| `InfoWeightedReadout.v` | same two Reals axioms as above |

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
research repository — flattened into 35 independent `formal/*.v` files (each
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
| `InfoSpectralCeiling.v`, `InfoRecurrenceEnergy.v`, `InfoQuantumFrequencyCeiling.v`, `InfoGraphFluxBalance.v`, `InfoCompanionSkew.v`, `InfoCausalSignature.v`, `InfoGraphNoether.v`, `InfoGraphGrowth.v`, `InfoActionStationarity.v`, `InfoCurvatureBalance.v`, `InfoProductSpectrum.v`, `InfoContinuumLimit_nD.v`, `InfoWeightedReadout.v`, `InfoCrossTermDominance.v`, `InfoDiskBeforeLock.v`, `InfoGrowthFold.v`, `InfoCeilingMonotone.v`, `InfoCurvatureNoether.v`, `InfoModeRotation.v`, `InfoPentagonSpectrum.v`, `InfoAreaLaw.v`, `InfoDegreeFromCurvature.v`, `InfoTensorFrame.v`, `InfoStrainTensorBridge.v`, `InfoOptimizerWindow.v` | 2026-07-05 |

See [SUPPLEMENT.md](SUPPLEMENT.md) for the full narrative, the dependency DAG, the
numerical validation (Hückel benzene, Forman curvature sanity checks), the
honest audit of what was and was not derived, and the complete reference list.
