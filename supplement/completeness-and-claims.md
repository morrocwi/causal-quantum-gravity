# Completeness Scoreboard and the Unification Claim Card

> Split out of `SUPPLEMENT.md`. Cross-references to "SUPPLEMENT.md §13/§14" now mean
> this file.

## 13. Completeness scoreboard: is this finished?

This question gets asked repeatedly, in different words, and deserves one
standing, precise answer instead of a fresh improvised one each time.
**Short answer: no, not finished — and the gap is not vague, it
decomposes into exactly six named items.** "Complete" needs a definition
first; four levels are used here, and the two branches (quantum mechanics,
general relativity) are at different levels, which is itself the
important fact — collapsing them into one "how done are we" number would
hide that.

**Level 1 — the same equation, read two ways (dispersion/wave identity).**
`Th_coqc`, **closed**, both branches. The mother equation composes into
quantum dispersion (`M·ω²=K·λ`) and into the wave/box operator
(`Box_quad`), and `InfoQuantumRelativityUnification.v` proves
these are literally the same statement, not an analogy. This is the level
at which this project's actual, checkable unification claim lives, and it
is done. **Tier-honesty pointer (added 2026-07-08 — see `SUPPLEMENT.md`
§1.1/§8 for the full statement, and `research_universal_solver`'s
2026-07-07 borrow-audit that first raised this):** "closed... done" is
accurate for the algebraic identity itself (a genuine, non-vacuous `ring`
proof) — it is NOT accurate as "QM and SR are derived from one root."
`Box_quad`'s Minkowski signature/boost constraint and `spine_residual`'s
`M,D,K` are each POSITED, not forced by the graph root (`SUPPLEMENT.md`
§1.1 traces exactly which link — `L_R` alone — is genuinely forced). Read
this level as "one real identity between two posited-but-independently-
characterized constructions," not as "QM and SR both derived, matching."

**A precise addendum on Schwarzschild specifically, because "connected to
GR" is ambiguous and this project has exactly one half of it.** The word
"connect" has two different meanings here, and only one is done.
*Structurally*, yes: dynamics around a Schwarzschild background is an
INSTANCE of the mother equation's own class — the same node-level equation
with a specific mass profile `m(i)=V(r_i)` built from the imported
Schwarzschild lift, its causal structure inherited from the same theorem
family as every other instance, and its Regge-Wheeler form on this
project's own lattice reproduces the literature quasinormal-mode
frequency numerically (`finite_diagnostic`, independently re-run:
`M·ω=0.4838−0.0958i` at N=1600 vs. the literature target
`0.4836−0.0968i`, `|diff|≈0.001` — matches
`scripts/verify_quantum_gravity_root_bridge.py`'s own claim). **A
late-time Price power-law tail is now also independently reproduced**
(`scripts/price_tail.py`, `finite_diagnostic`): time-symmetric (`ψ̇=0`)
initial data on the same potential gives local tail slopes
`−7.89 / −8.03 / −8.01` across three time windows (`t∈[250,450]`,
`[450,650]`, `[650,850]`) — steepening, not approaching the generic Price
`−(2l+3)=−7` value, so this is NOT massaged toward the textbook number. A
required control run (momentum-type data, `ψ=0, ψ̇=`Gaussian) was also run
and gives `−7.03 / −7.02 / −7.01` — the classic value — confirming the two
initial-data families are genuinely distinct (split of `1.00`, matching
the ~1-unit acceptance criterion), not a lattice or observer artifact.
Both runs and the exact reproduction recipe are pinned in
`scripts/price_tail.py`, with a passing pytest in
`scripts/test_reproduce.py`. **The causality currency is also now
independently verified**: `InfoConeInheritance.v` (3 theorems,
axiom-free) proves that a single leapfrog step of the mother equation's
own linear sector, taken over an ARBITRARY list of edges and an
ARBITRARY per-node coefficient field `m` (no sign or shape assumed), is
one-step-local — `shift_blind_step` (the result at a node is a function
purely of that node's own previous value and its edge-neighbors' current
values), `step_domain_of_dependence` (perturbing a node that shares no
edge with `i` cannot change the result at `i`), and `step_path_local_stencil`
(specialized to a path graph — the radial/1D case this bridge actually
needs — an interior node's next value depends only on
`prev(i), curr(i−1), curr(i), curr(i+1)`). Because `m` is universally
quantified, ANY nonnegative coefficient field — including a
Regge-Wheeler-shaped `V(r_i)` evaluated from the already-verified
Schwarzschild lift — automatically inherits all three facts as an
instance; this is a definitional weld, and nothing about Schwarzschild is
assumed or referenced inside `InfoConeInheritance.v` itself. **All four
bridge currencies (values, causality, spectrum, shadow) are therefore now
independently verified in this repo**, not merely reported: values at
`+reals` (`InfoAnalysisLift.v`), causality at `Th_coqc`
(`InfoConeInheritance.v`), spectrum at `finite_diagnostic`
(`verify_quantum_gravity_root_bridge.py`), and shadow at
`finite_diagnostic` (`price_tail.py`). *Generatively*, no: the profile `V(r)` is written in by hand
(imported from `f=1-2M/r` via `InfoAnalysisLift.v`), not grown by the
substrate's own dynamics — the open question is whether a bound energy
lump in this kernel can PRODUCE a `~1/r`-shaped long-range mass profile on
its own, and every result to date (the contact-only scalar channel, the
box-limited single-lump shadow, the still-unreplicated two-lump tail) says
not yet. This is exactly `OB-LONG-RANGE` (item 12 above) restated at the
Schwarzschild-specific case, not a separate gap. **The precise sentence,
worth quoting exactly because the imprecise version overclaims:** *the
mother equation now SUPPORTS Schwarzschild — proven to be in the same
class, and shown numerically to reproduce both its ringing and its
shadow on this project's own lattice — but the mother equation does not
yet PRODUCE Schwarzschild: the potential profile is still borrowed, not
grown, until the retention loop is shown to generate a `~1/r` mass
profile on its own.*

**Level 2 — full first-order dynamical structure on both arms.**
QM half: **closed**, `Th_coqc` (`InfoCompanionSkew.v`'s skew-adjoint
first-order form, with the imaginary unit forced out of the stability
window itself, not imported). GR half: **open**, named `GAP-2` — a frame
for the strain/curvature tensor exists (`InfoTensorFrame.v`), but no
evolution equation for it has been derived or mechanized. This level is
half-closed, and the two halves are not close to symmetric in difficulty.

**Level 3 — deep structure (what the equations are equations OF).**
QM half: **open** — no Born rule, no measurement, no entanglement
structure on this kernel; the CPTP/Kraus formalism lives in the separate
URCF companion work and has not been welded to this repo's own kernel.
What exists is *the equation of* QM, not *the probability structure of*
QM, and the note's own phrase for this ("dispersion-level readout") is
accurate, not softened. GR half: **open by design, not by failure** — this
project deliberately imports Jacobson's 1995 conclusion (§masschain's own
`[AX/import]` tag) rather than attempting to derive the Einstein field
equation as a theorem on this substrate; the eight refuted/abandoned
direct-derivation attempts (§5.2) are why that choice was made, not an
oversight.

**Level 4 — numerical constants from the substrate.** **Open on both
arms.** Neither `ħ` nor `G` is derived from graph-native quantities; the
weak-field coupling `1/(8π·β)` and the `α/β` ratio remain
`finite_diagnostic`, not theorems.

**The six named gaps, precisely, so "what's missing" has a checklist
instead of a mood:**

1. **`GAP-2`** — no evolution equation for the strain/curvature tensor
   `T_g`; a frame exists, dynamics do not. **First foothold, not closed**:
   `InfoTensorEvolution.v` (4 theorems, axiom-free) mechanizes the exact
   componentwise update law of the rank-one tensor `tens(x,i,j):=x(i)*x(j)`
   under a perturbation — pure algebra any evolution-equation attempt
   would need. The actual gap content (what field equation `T_g` obeys,
   covariance, conservation) is untouched.
2. **Bridge / `ansatz-T`** — the Clausius-form iff
   (`InfoStrainTensorBridge_attempt.v`) is conditional on an explicit,
   disclosed ansatz until `OB-ENTROPY-BRIDGE` (`open-problems-ledger.md`
§12 item 7) closes with a
   genuine trajectory-level bridge theorem. A numerical probe confirmed
   the shape of a lower bound in the active-phase regime only (the run had
   no quiet-phase epoch to compare against) — `finite_diagnostic`, zero
   theorems changed.
3. **Capacity-equality / `ansatz-H`** — the screen-partition boundary fact
   (§7, §arealaw) is a half-quantitative resemblance to an area law, not
   a proven equality, and is explicitly disclosed as such. A rank/
   boundary-node/cut chain inequality was confirmed numerically (200/200
   random graphs), but the corresponding theorem file has not yet passed
   this repo's own audit, and the equality case is permanently
   graph-dependent, not a universal fact.
4. **Cut-growth (Raychaudhuri slot)** — **first foothold, not closed**:
   `InfoCutGrowth.v` (5 theorems, axiom-free) mechanizes the STATIC half
   only — exact cut bookkeeping under retention growth, and
   `priced_screen_growth` (admitted strain across a screen is bounded by
   benefit granted there, edge by edge). The DYNAMIC half a
   Raychaudhuri-style argument actually needs — a rate law, focusing —
   stays fully open; Raychaudhuri (1955) is registered as the named target
   engine, not mechanized.
5. **Born-rule weld** — the URCF companion's CPTP/Kraus machinery has not
   been connected to this repo's own kernel; they are separate, unwelded
   pieces of work today. **First foothold, not closed**: `InfoModeWeights.v`
   (4 theorems, axiom-free) mechanizes the Born SHAPE — not the rule — on
   one concrete graph, the 6-cycle (the largest graph with a fully
   rational Laplacian eigenbasis): an exact, universal Parseval identity
   and exact reconstruction/completeness. It is an instance on one graph,
   not a general theorem, and explicitly claims no probability
   interpretation, no measurement postulate, and no CPTP weld.
6. **Numerical constants** — `ħ`, `G` not derived from the substrate;
   `α/β` and the weak-field `1/(8π·β)` coupling remain
   `finite_diagnostic`.

**One line, for whenever this question is asked again:** *the equations
of quantum mechanics and general relativity are genuinely connected to the
mother equation at Level 1 — real, checkable, and unmatched elsewhere in
this form — but the theories themselves are not fully connected, and the
incompleteness decomposes into exactly the six items above, not into an
unbounded fog.* Knowing precisely what is missing, rather than only
knowing that something is missing, is what distinguishes this document
from a manifesto.

## 14. The Unification Claim Card — a permanent boundary statement

This card exists so the word "unification" has one fixed, quotable
meaning in this project, checked against on every future revision rather
than re-negotiated in conversation each time. It was written the same day
this project caught itself drifting toward "quantum GR" language twice in
one exchange — the card is the fix, not a one-off correction.

**Claimed.** One equation, two exact readings: quantum dispersion is
identically the relativistic wave operator (`Th_coqc`,
`InfoQuantumRelativityUnification.v`). The Schwarzschild sector is
supported as a complete four-currency bridge — values (`+reals`),
causality (`Th_coqc`, `InfoConeInheritance.v`), spectrum
(`finite_diagnostic`, QNM), shadow (`finite_diagnostic`, Price tail) — a
bridge, not a derivation, per this project's own razor (§13).

**Explicitly NOT claimed, stated so a reader never has to infer it:**

- Derivation of quantum mechanics' probabilistic structure. No Born rule,
  no measurement postulate, no entanglement. `InfoModeWeights.v`'s
  Plancherel identity on the 6-cycle is ONE instance of a quadratic-form
  shape, not a general theory of anything.
- Derivation of Einstein's field equations. Jacobson's 1995 conclusion is
  imported by deliberate razor (this project's own choice, motivated by
  eight refuted direct-derivation attempts, §5.2), not derived.
- **Any quantization of geometry itself.** `OB-QUANTUM-GEOMETRY`
  (`open-problems-ledger.md` §12 item 13) is untouched — no file, no
  probe, not even a precise statement exists yet of what a
  quantum-superposed retention pattern would mean. This project has
  never produced, and does not claim to have produced, anything
  resembling a graviton, a wavefunction over geometries, or a quantized
  metric.
- The generative side of gravity. `OB-LONG-RANGE`
  (`open-problems-ledger.md` §12 item 12): whether
  the substrate can grow a long-range `~1/r`-shaped mass profile unaided
  remains open; the Schwarzschild bridge above uses an imported profile.

**Standing falsification invitation, added as its own target in
`AUDIT_BRIEF.md`:** anyone who can show this project's own prose,
anywhere in this document, the companion note, or a public statement,
trading on a claim that belongs in the NOT-claimed list above — treat
that as a class-C refutation, logged in `LOGBOOK.md` with credit, exactly
like a refutation of C1-C4.

---

