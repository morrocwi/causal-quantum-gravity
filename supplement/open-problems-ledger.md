# Open Problems Ledger — Causal Quantum Gravity

> Split out of `SUPPLEMENT.md` (see `SUPPLEMENT.md`'s own index) because this section
> is the most frequently updated in the whole project and had grown to dominate the
> parent document's length. Cross-references from elsewhere in this repo to
> "SUPPLEMENT.md §12/§12.1/§12.2/§12.3" now mean this file.

## 12. Open questions

1. Does the discrete-curvature ↔ dissipation link (§7) generalize to
   non-uniform edge weights, and does it predict anything falsifiable
   beyond the algebraic identity itself?
2. Can the QNM bridge (§6) be extended to gravitational (spin-2) rather
   than scalar perturbations, still without invoking a point at infinity?
3. ~~Is there a principled (non-circular) way to fix the per-node dissipation
   `D_i` for a physical horizon...~~ **Substantially closed by §9.1**: the
   frequency ceiling `Mω²≤K(2·dmax)` and the CFL stability window are now
   `Th_coqc`, forced by the graph's own maximum degree. The remaining open
   piece is narrower: whether a *physical* horizon picks out a specific
   `dmax` non-circularly, not whether a floor/ceiling exists at all.
4. Does Ollivier-Ricci curvature [Ollivier 2009] (the optimal-transport-based
   alternative to Forman-Ricci) offer a sharper or more physically
   suggestive discrete gravity readout, at the cost of needing linear
   programming rather than pure combinatorics?
5. Can a genuinely non-total (partial, multi-dimensional) causal order be
   constructed on this repo's graphs, so that §9.4's sign-construction
   theorem produces a non-degenerate indefinite signature on the repo's
   *own* causal structure, not only on a constructed example?
6. Does §9.5's Noether pairing `W` admit a principled dissipative
   correction law, or is exact conservation strictly a conservative-sector
   fact (numerically confirmed sharp, per §9.5's header)?
7. **[named: OB-ENTROPY-BRIDGE]** This project has TWO formalized notions
   both readable as "entropy," and they are deliberately two different
   objects, not a naming accident to be merged — but the theorem connecting
   them along a trajectory is missing. **Field entropy** ("descent"): the
   private repo's own official philosophy lexicon
   (`research_universal_solver/engine/lexicon.py`, the "conservation law"
   glossary entry, `Th_coqc`) reads the second law as the monotone
   energy-descent fact `dE/dt≤0`, unified with the arrow of time — this is
   about the FIELD dissipating. **Record entropy** ("count"): the
   entropy-license work (`InfoEntropyLicense.v`, merged 2026-07-05) reads
   entropy as a Bekenstein-style retained-distinction count,
   `S_loc:=s0·deg(i)` — this is about the GEOMETRY accumulating. The
   balance law is already the single-instant broker between them: `retain(e)
   ⟺ strain≤b` prices exactly the trade "pay on the field side (raise
   dissipation) to buy on the record side (write a retained distinction)" —
   a Landauer-shaped cost already present, one decision at a time, via
   `clausius_form` (whose `δE` term already is the field-entropy object,
   the strain/`Sgeo`-difference, connected to the record-entropy object
   `δS_count` at the joint stationary point). What is missing is the
   TRAJECTORY version — cumulative dissipation versus net bits inscribed
   over a whole run, not just at one instant. **A numerical probe was run
   and its own naive hypothesis was refuted, narrowing the target rather
   than closing it:** the ratio of cumulative dissipation to cumulative
   inscribed bits did NOT settle (`~62%` drift across checkpoints on a ring
   run) — cumulative field-entropy dissipated plateaus quickly (the field
   calms fast, `~0.20` from an early checkpoint onward) while inscription
   continues (`27→33` net bits over the same window), so a CUMULATIVE,
   whole-trajectory ratio cannot be the right object: late-run inscriptions
   are happening near `strain≈0`, paying almost no marginal dissipation.
   **The refined, narrower target**: an operational temperature should be
   defined MARGINALLY, only during the field's genuinely active phase, not
   averaged over the whole run — and the honest form of the bridge is
   plausibly a one-directional bound, not an iff:
   `δE_dissipated ≥ (a minimum price)·δS_count`, restricted to bits
   inscribed *against* a still-active (not-yet-settled) field, rather than
   an equality relating the full cumulative quantities. This is a real,
   useful narrowing from one probe, not a failure of the idea — the
   apparatus for both sides still exists (the damped-decrement identity;
   `entropy_step`/`clausius_form`); what changed is which quantities the
   eventual theorem should actually relate. (Bonus baseline recorded from
   the same run: the ceiling-saturation ratio `ω²M/(2K·dmax)` measured
   `~0.695` — the extremal mode sits at roughly 70% of the ceiling, not
   saturated — worth tracking as a baseline for the hunting-type-2
   saturation-surface search, §12.1.) Do not use the bare word "entropy"
   unqualified anywhere a reader could confuse the two — say "field
   entropy" / "record entropy" explicitly.
8. **[named: OB-EXPANDER]** A UNIFORM lower bound on the graph Laplacian's
   second-smallest eigenvalue (λ₂, algebraic connectivity / Fiedler 1973),
   i.e. a genuine spectral-gap/expander property, is explicitly NOT claimed
   and not currently provable by anything in this repo's existing
   "eigenpair as extensional hypothesis" framework (would need Cheeger-type
   isoperimetric machinery, which is irrational-valued and awkward over
   ℚ). More importantly: this project's own graphs (rings, lattices) are
   demonstrably NOT expanders — their λ₂→0 as the graph grows — so a
   uniform floor claim would be FALSE for graphs already used elsewhere in
   this repo if stated without this qualification. Any future "mass gap"
   framing (in the Yang-Mills sense) must stay `[Dr]` with this disclaimer
   attached explicitly; a two-agent internal review (2026-07-05) rejected
   an earlier, unqualified version of this framing for exactly this reason.
   The tractable, currently-open sub-parts (a monotone "floor never drops
   under retention" fact, and a qualitative "λ₂>0 iff connected" theorem)
   are believed low-to-moderate risk and are queued separately, distinct
   from this named uniform-bound gap. **A numerical probe measuring
   Ramanujan-graph quality** (comparing a retention-grown graph's `λ₂`
   against the Alon–Boppana expander bound, `2√(d̄−1)`) found grown graphs
   are WORSE expanders than a random graph of the same size/degree
   (measured ratio `q≈1.63` for the grown graph vs. `q≈1.23` for a random
   comparison graph — larger is worse). This is not a defect; it is the
   expected physical content of retention read correctly: an expander
   mixes information fast precisely because it has no persistent local
   structure, and this project's own retention mechanism exists to BUILD
   persistent local structure (a "well" at the birthplace of a distinction,
   local clustering) — a graph that remembered well would have to be a bad
   mixer. Recorded as a trade-off note under this same gap: **retention
   trades spectral gap (mixing speed) for locality (memory)**, a second,
   independent piece of evidence (alongside the ring/lattice non-expander
   observation above) that this project's own graphs are not, and should
   not be expected to become, expanders — reinforcing rather than
   contradicting the disclaimer already stated in this item.
9. **[named: OB-RG-FIXED-POINT]** Does iterated 2:1 block coarse-graining
   of a retention-grown graph (both field values and topology) converge to
   a universal limiting structure independent of the starting seed —  a
   discrete analogue of an RG fixed point / universality class? The
   coarse-graining map itself is not yet defined for this repo's own
   graphs, let alone proven to have a fixed point; the recommended next
   step is a numerical probe (grow several seeds, coarse-grain repeatedly,
   compare resulting degree/curvature distributions) before any theorem
   attempt, not a proof attempt directly.
10. **[named: OB-TIE-MANIFOLD]** Three independent threads, found on
    different days, all point at the same set without yet being shown to
    be the same set: the exact-tie boundary of the retention balance
    (`strain == b`, where the iff `retain(e) ⟺ strain≤b` is undecided) is
    (i) the sole channel through which the equivariance no-go (queued,
    Item 3's symmetry-breaking discussion) permits symmetry loss, (ii) the
    natural candidate for where `clausius_form`'s inequality saturates to
    an equality (the "reversible" sector of this project's own Clausius
    relation, structurally the only place `T` could be read off cleanly
    rather than merely bounded), and (iii) a candidate "lossless conversion
    channel" in the sense of static friction converting translation to
    rotation without burning energy (a rolling-without-slipping analogy):
    inscribing a distinction exactly at the tie costs no *excess*
    dissipation. Whether these three are one fact or three coincidentally
    adjacent facts is open and unexamined; the cheap next step is checking
    whether the tie set from (i)'s no-go counterexample construction is
    literally the same set as (ii)'s equality-saturation set on a concrete
    graph, before assuming they coincide.
11. **[named: OB-EFFECTIVE-INERTIA]** A three-channel probe was run to
    settle which of three ways "retention density" could couple to a
    passing signal actually gives the physically correct sign (a signal
    should slow down passing through a dense/well-remembered region, for
    the congestion reading in Reading 2 to be more than metaphor). The
    three channels tested separately: retention adding graph CHORDS
    (topology), retention raising local STIFFNESS (`K`), and retention
    raising local INERTIA (`M`). **Result: only the inertia channel gives
    the correct sign.** Adding chords (`+27%` signal speed) and raising
    stiffness (`+15%` signal speed) both make the region FASTER, not
    slower — the wrong sign, a repulsive/anti-gravity reading; only
    loading local inertia (`+23%` slower) gives the correct, attractive-
    congestion sign.
    **This is a genuine partial falsification of the existing informal
    congestion reading and is recorded as such, not softened**: Reading 2
    (§paper "Congestion") as currently stated does not specify which
    channel retention acts through, and two of the three plausible
    readings of it are demonstrably wrong-signed on this substrate. A
    universe whose retention only ever built wiring density or stiffness,
    with no coupling to inertia, would have anti-gravity, not gravity, on
    this kernel's own dynamics. Reading 2 needs a qualifying sentence
    added at its next revision: the congestion metaphor is licensed only
    through the inertia channel, not generically through "density."
    **The same result also strengthens Ansatz C**, not just weakens
    Reading 2: Ansatz C already reads a densely-retained region's trapped
    internal-mode energy as mass (`m = ħω_int/2c²`, §mass); this probe
    shows numerically that mass-loading (raising local `M`) is *also* the
    one channel that gives gravity the right sign — Ansatz C is now doing
    double duty (generating mass AND fixing gravity's sign) from the same
    single identification, which is evidence the identification is doing
    real work, not merely evidence it explains one thing.
    **Consequently, this item MERGES with the previously-separate `OPEN`
    inertia-cost question** (`mass_note.tex`'s "furthest Dr sentence,"
    cost of re-addressing a busy loop under acceleration ∝ m): both are
    now read as one theorem viewed from two sides — trapped internal-mode
    energy acting as effective inertia to a passing signal is exactly the
    mechanism that would explain both. The concrete closing step: prove
    that energy trapped in a high-frequency internal mode within a region
    acts as an effective mass `M_eff` to a low-frequency signal passing
    through that region (a two-timescale/homogenization argument, or a
    direct probe: pin a high-`ω` mode in a region, send a low-`ω` packet
    through, and check whether transit slows WITHOUT `M` being set by
    hand). Until that closing step, this stays `[Open]`, upgraded from
    `[Dr]` only in the sense that its two previously-separate open
    questions are now known to be the same question.
    **Update:** two further pieces landed, each precisely scoped, neither
    closing the full feedback loop. `InfoBackReaction.v` (5 theorems,
    axiom-free) mechanizes the exact strain-splitting identity for a
    background field plus a perturbation — the "matter acts on geometry"
    joint of the loop `stored energy -> edge strain -> retention decision
    -> geometry -> inertia -> motion`. Its header names the two joints
    that remain open: `OB-HOMOGENIZATION` (this item, above) and
    `OB-GEODESIC` (no general trajectory theorem; only a 1D numerical
    demonstration exists). `InfoShiftAverage.v` (5 theorems, axiom-free)
    then closes `OB-HOMOGENIZATION` **at one exact instance**: at the
    mother equation's stability-window center, the one-step mode map is
    the exact period-4 rotation on `Q^2` (a crystallographic-period gift
    from `InfoModeRotation.v`), so the time-average of the pointwise
    coefficient shift `3gψ²` over one period is an EXACT rational
    constant `(3g/2)(x²+y²)` — homogenization as pure algebra, no limit
    taken, because the period is exact. The general statement (an
    effective coefficient for APERIODIC backgrounds) and the weld from
    the averaged coefficient into the propagation problem both remain
    `[Open]`, stated as such in the file's own header — this closes one
    instance of the joint, not the joint in general, and not the loop.
12. **[named: OB-LONG-RANGE]** Does this kernel's gravity-like effect have
    a genuine long-range carrier, or is it contact-only? Two rounds of
    probing, both `[numeric, box-limited]`, give the current, still
    incomplete picture. Round one falsified the naive candidate cleanly,
    on two independent grounds: a mean-field argument (`⟨ψ³⟩=0` for a
    symmetric mode, so a quartic scalar has no monopole source) and a
    direct numerical leakage measurement (`~2×10⁻⁶` outside a bound
    lump's core) both show the bare scalar-amplitude channel is
    contact-only, with no `1/r²`-style far field of its own. Round two,
    designed specifically to test the channel round one's own control
    accidentally disabled (a zero-benefit parameter choice that made
    retention untested rather than falsified, corrected before rerunning),
    found something real: a bound lump measurably suppresses the local
    retention (edge-addition) rate in a surrounding bath, out to the edge
    of the simulated box (`−24%` at r=3 down to `−9%` at r=17, relative to
    a control baseline, 4 trials) — a "retention shadow" that is
    long-range in extent and correctly signed (a wider shadow means lower
    local connectivity, hence a slower local medium, hence bending toward
    the lump — the same sign every other reading in this ledger requires,
    reached by a third, independent route). **What is NOT yet
    established, stated plainly:** the decay exponent — the actual
    `1/r²` question — is not resolved; the box is small enough (41 nodes)
    and reflective enough that a genuine power law cannot yet be
    distinguished from a finite-size/boundary artifact (the same failure
    mode already caught once this project, in the heat-equilibration
    check of §12.2, and in round one of this very probe's box-edge
    profile). The concrete next step, before any exponent claim: rerun
    with a substantially larger box AND absorbing (non-reflective)
    boundary conditions, and check the shadow's shape is unchanged when
    the box size changes — if the falloff scale grows with the box, it is
    still an artifact; if it does not, it is real. A second, independent
    next step (a direct two-lump force measurement) is the more direct
    route to the actual `1/r²` question and is queued alongside it.
    **Round three, the direct two-lump force measurement, ran and was
    self-corrected within the same session it was reported — recorded
    here in its corrected form, not its first-draft form.** A first
    narrowband-bath run measured attraction between two lumps at several
    separations `d` and was initially read as confirmation; a same-session
    big-box rerun with an explicit reference-drift audit (holding lump A
    fixed, moving lump B, and separately measuring how much a single
    lump's own signal drifts with box position) found the drift itself
    (`spread ≈ 0.195`) is the SAME ORDER as the measured force signal, and
    that `U(d)` **changes sign non-monotonically with `d`**
    (`+, −, −, +, +` across `d=12..28` in the corrected run) — the
    signature of narrowband optical/acoustic binding (two scatterers in a
    bath with a dominant wavelength attract and repel in bands, `~cos(2k·d)`),
    not of a monotone Newtonian carrier. **The correct, downgraded
    reading: "two-body interaction confirmed" (existence, at very high
    significance), NOT "attraction confirmed" in the Newtonian sense** —
    the interaction exists and is real, but its shape is the optical-binding
    class, produced by the narrowband (periodic-kick) bath used in that
    run. The physics of the failure points directly at the next test: an
    optical-binding oscillation is exactly what a spectrally NARROW bath
    produces; a genuinely monotone, gravity-like tail is expected only
    from a spectrally BROAD (thermal-like) bath, where the oscillatory
    components at different wavelengths average out and only a decaying
    envelope survives — the textbook distinction between optical binding
    and a thermal Casimir-type force. A broadband-bath rerun (weak,
    white-in-time kicks instead of strong periodic ones), with the same
    drift-audit built in from the start rather than added after a false
    positive, is the next probe and the one that actually adjudicates
    `1/r²`-style monotonicity. **Standing lesson, added to this project's
    own probe-design checklist as of this finding:** every two-body
    interaction probe must print its own single-body reference drift
    alongside the interaction signal, in the same run, before any sign or
    magnitude claim — reproducibility across seeds is necessary but not
    sufficient to rule out a systematic (non-cancelling, nonlinear
    dressing) artifact.
13. **[named: OB-QUANTUM-GEOMETRY]** Untouched — no file, no probe, not
    even a prior attempt to state it precisely. Named here specifically
    because a gap that has never been named is the one most likely to be
    silently overclaimed later: after `supplement/completeness-and-claims.md`'s §13 completeness scoreboard
    established that this project unifies quantum mechanics and general
    relativity only at the level of one equation admitting two exact
    readings (dispersion and wave), a natural next question is what
    happens to that equation's own GEOMETRY side under superposition or
    fluctuation — i.e., is there any sense in which the retention pattern
    itself (not a field living on top of a fixed pattern) can be treated
    quantum-mechanically? This project's existing ledger-wave content
    (item 12's ideas, and the ordinary sense in which a field on a graph
    fluctuates) is entirely CLASSICAL: a perturbation of a fixed pattern.
    A genuine quantum-geometry statement would need an amplitude over the
    CONFIGURATION SPACE of retention patterns themselves (a graviton-like
    object), and this kernel currently has no vocabulary to even write
    that statement down, let alone prove or probe it — this is a frontier
    question, not an engineering backlog item, and should not be
    confused with one. **Update — TEST 2 of a five-test battery
    (order-memory / "seed of interference") run and independently
    verified** (`scripts/probe_order_memory.py`, `finite_diagnostic`,
    with two executed, passing pytest tests in
    `scripts/test_order_memory.py`): starting from an identical field on
    a ring graph, retaining two candidate chords `e1, e2` in opposite
    orders (A: `e1` then `e2`; B: `e2` then `e1`), evolving the SAME
    total number of leapfrog steps in each case, and comparing the final
    field state on the two paths — even though the final GRAPH (and its
    curvature, by the fold theorem, `InfoGrowthFold_attempt.v`/C55) is
    identical either way. **Result: the relative difference
    `D(T)/‖u(T)‖` does NOT decay to zero as `T` grows — it plateaus
    around `0.7–1.3` out to `T=5120`, robust across five random seeds and
    several chord distances.** This is the "gate opens" branch of the
    test's own decision rule: retention ORDER is recorded in the field
    even though it is invisible to curvature — a genuine history-connection
    curvature exists in the field sector, which is the necessary
    precondition (not yet a proof) for any phase that a
    sum-over-geometries construction for `OB-QUANTUM-GEOMETRY` would
    need. What this does NOT establish, stated plainly: no phase, no
    amplitude, no quantization — only that the classical structure a
    quantization would have to consume is present, not absent.
    **TEST 3 (tie-manifold occupancy) was attempted and is INCONCLUSIVE
    by design confound, reported honestly rather than tuned to a clean
    number** (`scripts/probe_tie_manifold_occupancy.py`): measuring
    `|strain(e)−benefit(e)|` across candidate edges is extremely
    sensitive to the retention parameters `α, β` in a way this probe has
    not yet controlled for. A first version (tracking one candidate edge
    repeatedly across many decision windows) put its diff value near
    zero at one specific `α`, but this turned out to be a near-coincidence
    of a single oscillating pair, not a population statistic — corrected
    to a proper cross-sectional design (every untried candidate, every
    window). With the corrected design and the same `α, β` used
    elsewhere in this project's probes, the population's diff values
    cluster near `+4` (far above the tie boundary, essentially never
    near-tie) rather than straddling zero — meaning these particular
    parameters simply don't put the dynamics near the tie manifold at
    all, and no thickness exponent or near-tie lifetime can be honestly
    extracted from this run. **The concrete fix, not yet done:** calibrate
    `α, β` (or use an adaptive/annealed benefit) so the population's
    median `strain−benefit` sits near zero by construction, then measure
    the SHAPE of the distribution around that point — not just retry
    parameter values hoping to land near it by luck, which is the mistake
    this attempt made and corrected mid-probe rather than reporting a
    number from it. **TEST 1 (ledger-wave dispersion, "graviton
    spectroscopy") was run and gives a clean positive, with an explicit
    disclosed caveat** (`scripts/probe_ledger_wave_dispersion.py`,
    `finite_diagnostic`, two executed passing pytest tests): this test
    necessarily introduces ONE quantity with no precedent anywhere else
    in this kernel — an edge-inertia `M_w` for a graded (continuous,
    not binary) retention weight `w_e∈[0,1]` — since the existing binary
    retention rule is instantaneous and has no inertia concept to draw
    on; this is disclosed, not hidden. Using ONLY constants already
    established elsewhere in this project's own probes (spring constant
    `κ=K=1`, damping `γ=c=0.1`) plus `M_w=1` (matching the node mass
    convention used everywhere else, not derived), the analytic
    dispersion relation for a perturbation on a ring predicts
    UNDERDAMPED (oscillatory) behavior at every tested wavenumber
    (`k=2π/16·{1..7}`), and the independent numerical simulation confirms
    this exactly: all seven modes oscillate (`5` to `25` sign changes
    over the run), matching the analytic `ω_L(k)` prediction. (Mode 8,
    the Nyquist mode, has a degenerate initial condition —
    `sin(π·i)≡0` — and is excluded, not reported as a finding.) **What
    this does NOT establish:** `M_w` is a modeling CHOICE, not a derived
    quantity — the finding is conditional ("IF edge-inertia exists at
    this natural scale, THEN a ledger-wave with real frequencies
    exists"), not unconditional; deriving `M_w` from anything else in the
    kernel is itself a new open question this test surfaces rather than
    closes. **TEST 4 (adiabatic breakdown, this project's own "Planck
    regime" search) was run and gives a precise, richer-than-expected
    structure** (`scripts/probe_adiabatic_breakdown.py`,
    `finite_diagnostic`, three executed passing pytest tests): the
    classicality of a retention decision quietly assumes its evaluation
    window `W` is much larger than the field's own oscillation period
    `T_field` — long enough to see a phase-blind, time-averaged strain
    rather than an instantaneous phase. Measuring the variance, across
    starting phase, of the window-averaged strain of a driven oscillator,
    the transition is NOT a single crossover point as naively expected:
    the variance has EXACT zeros at every half-integer multiple of
    `T_field` (an analytic property of `sin²`'s own period being half the
    field's period, verified exactly, not a numerical coincidence),
    with an envelope between those zeros that decays like `1/W²`
    (verified: peak variance ratios across `W/T_field=1.25→2.25→3.25`
    match the `1/W²` prediction to within a few percent). Strongly
    phase-dependent for `W≲T_field`, negligible (`<10⁻⁶`) by
    `W≳10·T_field`. **What this does NOT establish:** this locates where
    the field-sector's own classicality assumption would break down for
    a driven-oscillator toy model — it says nothing about whether the
    actual retention dynamics elsewhere in this kernel operates anywhere
    near this regime in practice, which would need a genuine leapfrog
    field's own natural frequency compared against its own decision
    cadence, not asserted from this idealized case. **TEST 5 (single-flip
    action quantum, "does geometry share `ħ_geom` with the field?") was
    run and is INCONCLUSIVE BY CONSTRUCTION, reported as such rather than
    presented as a finding** (`scripts/probe_single_flip_quantum.py`,
    two executed passing pytest tests confirming the algebra, not the
    physics): using `InfoShiftAverage_attempt.v`'s own exact period-4
    orbit, the field-sector action `A_loop=2(x²+y²)` is exact; a proposed
    geometry-sector "flip action" `A_flip`, built as a strain-like sum
    over the SAME orbit's own coordinates, comes out to exactly `4(x²+y²)`
    — giving `Q=A_flip/A_loop=2` exactly, for every amplitude tested. This
    constancy is **provably an algebraic artifact, not physical content**:
    both quantities are homogeneous quadratics built from the same
    4-point orbit via closely related functional forms, so a fixed ratio
    is close to inevitable regardless of what this kernel's geometry
    sector actually does. A genuinely decisive version of this test needs
    `A_flip` derived from an ACTUAL retention-decision event (a real
    strain-vs-benefit toggle during real growth dynamics), not a proxy
    sharing the field's own orbit — not attempted here, and flagged as
    the concrete next step if this test is revisited.

**Battery summary, all five tests now attempted:** TEST 2 (order-memory)
positive and robust; TEST 3 (tie-manifold occupancy) inconclusive by a
caught design confound; TEST 1 (ledger-wave dispersion) positive but
conditional on one undisclosed-elsewhere modeling choice (`M_w`); TEST 4
(adiabatic breakdown) precisely characterized, richer than expected, but
scoped to an idealized toy model; TEST 5 (single-flip action quantum)
inconclusive by its own construction. **None of the five tests
quantizes anything.** What they collectively establish is a map of where
the classical structure a quantization would have to consume is present
(TEST 2's history-connection, TEST 1's conditional oscillation) versus
where the test design itself is not yet sharp enough to say
(TESTS 3 and 5) — precisely the kind of honest, incomplete-but-precise
status this project's own completeness scoreboard and Unification
Claim Card (`supplement/completeness-and-claims.md` §13, §14) were built
to hold. `OB-QUANTUM-GEOMETRY` remains `[Open]`.

**Postscript, checked against this project's own information-philosophy
translator, not asserted from memory:** this battery's five tests were
written and reported almost entirely in borrowed physics vocabulary
("quantum," "action," "phase," "amplitude," "oscillation," "adiabatic,"
"superposition," "graviton," "momentum," "wave") rather than this
project's own δ_R/information vocabulary. Per the `philosophy-translate`
skill's own rule ("never paraphrase, always call the function"), each
term was run through the real `engine.lexicon.translate_to_philosophy`
function rather than translated by guess. Result, quoted, not
paraphrased: `action`, `phase`, `amplitude`, `oscillation`, `adiabatic`,
`superposition`, `graviton`, `momentum`, and `wave` ALL pass through
**unchanged** — none has an entry in `GLOSSARY`. Only `energy` and
`geometry` (as substrings) resolve, to definitions this project already
uses correctly elsewhere: `energy` → `info(x) = ⟨x, L_R x⟩ (R0_ENERGY)`
(`Th_coqc`), `geometry` → "the shape of the retained-information form
(⟨x,L_R x⟩ as a metric)" (`Th_coqc`, §space/geometry entry). **This
sharpens `OB-QUANTUM-GEOMETRY` beyond "no file, no probe" to something
more precise: this project's own philosophy layer, queried with its own
real translator, has no word for nine of the eleven concepts a genuine
quantum-geometry statement would need to be stated in this project's own
vocabulary at all** — not merely unproven, but unnameable in δ_R terms
as this repo currently stands. Fixing the prose above to use only
`GLOSSARY` terms is not attempted here, per the skill's own instruction
not to invent a translation where none exists; the gap itself, quoted
from the real function rather than assumed, is the more honest and more
useful thing to record.

**Two follow-up checks, same method, with a different outcome each —
both worth recording precisely rather than from memory.**

*"The spine" already covers exactly this document's own Level-1
unification claim, and needs no new coinage.* `master_equation` resolves
in `GLOSSARY` to: *"the spine:* `M∂²Φ + D∂Φ + K·L_R Φ + ∇V(Φ) = J − η`
*(There is exactly one master equation ('the spine') and every regime of
physics (classical, quantum, GR, biology, chemistry, economics...) is
that same equation read in a different basis; M/D/K/V are readout
artifacts of one information unit, not independently dimensionful.)*
`[Th_coqc]`*"* — the definition text itself already names quantum
mechanics and GR as readouts of one equation, which is precisely
`supplement/completeness-and-claims.md` §13's Level-1 claim stated in
this project's own native vocabulary rather than
borrowed physics language. (`unification` and `physical law` alone do
NOT resolve — only the exact phrase `master equation` does; a reader or
a fellow AI session reaching for "unification" as a search term should
reach for "the spine" instead.)

*"Orbit" has no entry of its own, but is not a bare gap the way the nine
terms above are — it is the closed special case of an entry that
already exists.* `orbit`, `periodic orbit`, `closed orbit`, `trajectory`,
and `cycle` all pass through untranslated (checked, not assumed), but
the concept an "orbit" names in `InfoShiftAverage_attempt.v`/TEST 5 (a
discrete evolution that returns EXACTLY to its own starting readout after
finitely many steps) is a root-of-unity closure of the SAME branch this
project already names `quantum state / wavefunction evolution`:
*"R4_EVOLVE readout, exp(−iLt) unitary branch of the spine ... under-
damped (looping) reading of the one spine on the oscillatory side of the
λ_c threshold"* `[Th_coqc]`. The correct fix, when this glossary is next
extended, is not a brand-new `orbit` entry but an added clause on the
EXISTING `quantum state / wavefunction evolution` entry naming its
periodic/closed special case — matching this project's own
minimum-parameter instinct: extend what already exists before minting
something new.

**Why the "action = 2·info" identity is scoped to the isometric orbit
specifically — an information-native explanation, not just an
observation** (`scripts/probe_action_glossary_generalization.py`,
verified geometrically, not merely asserted): the classical action of a
closed orbit is, by a standard fact of Hamiltonian mechanics, the
phase-space AREA the orbit encloses. Checked directly against the
period-4 i-rotation orbit's own four points — `(3/2,−5/7)`,
`(−5/7,−3/2)`, `(−3/2,5/7)`, `(5/7,3/2)` for one sample amplitude — all
four have EXACTLY the same `info(x,y)=x²+y²` value (`541/196`),
confirming they sit on a single circle, spaced 90° apart. **A loop
confined to one circle has its enclosed area fixed entirely by that
circle's radius — there is no other quantity the area could depend on —
which is why `action` is forced into a fixed multiple of `info` exactly
when the step conserves `info` (an isometry).** For the non-isometric
orbits (`a=1`, `a=3`), the loop visits DIFFERENT `info` values at
different points (no single circle, no single radius), so its enclosed
area depends on the whole trajectory of retained-information rather than
any one readout — there is no longer a single number for the action to
be proportional to. In this project's own vocabulary: `info` IS energy
(`R0_ENERGY`, `Th_coqc`), so an isometry here is exactly an
energy-conserving automorphism of the step, and this is the discrete
finite-orbit form of the standard classical-mechanics fact that action
variables of an integrable system are built from its own conserved
quantities — the same Noether-type phenomenon (symmetry ⟹ conserved
charge) this kernel already mechanizes elsewhere
(`InfoGraphNoether_attempt.v`, `InfoCurvatureNoether_attempt.v`,
this project's own `conservation law` glossary entry). Not a coincidence
of one small case, but not a universal fact about orbits either — a
genuine boundary condition, now named in the vocabulary this project
already has rather than left as an unexplained empirical pattern.

## 12.1 A method for finding open problems, not just open problems

A worked classical-mechanics exercise (rolling cylinder vs. hollow cylinder
down an incline, solved by energy conservation, `v=ωR` the rolling-without-
slipping lock) was used as a test case for extracting a general "what to
hunt for" checklist, on the theory that the exercise's OWN solution
structure — a dimensionless ratio (`β:=I/MR²`) deciding the outcome while
`M`, `R`, `g` all cancel — is a pattern this project's own theorems should
be re-read for, not just accumulated. Four hunting categories, each with a
named target already present in this project:

- **Dimensionless invariants hiding inside a free-parameter theorem.**
  Any Th-tier result stated with free parameters (`K`, `M`, `ħ`, `s0`, ...)
  should be re-read for the ratio that survives when they're eliminated —
  this is what "comparative, not absolute" already means for the mass
  ceiling (§masschain), and the same reading applies to `α/β` (the
  cosmological-constant ratio, §holo), `λ_max/λ₂` (once a floor exists —
  a single number that is simultaneously "mass window width," a numerical
  condition number, and the momentum-optimizer convergence rate, per the
  composition noted under OB-EXPANDER above), and the ceiling-saturation
  ratio `ω²M/(2K·dmax)` (the existing `+0.98` correlation in the mass-bound
  numerics, §mass, is a hint this ratio may itself be structurally close
  to 1, which would itself be a prediction, not just an observation).
- **Saturation manifolds — the surface where an inequality becomes an
  equality is where a named classical theory already lives.** The rolling
  problem is solved on the surface `dE/dt=0` (no slipping, no heat
  generated — energy conservation, the equality case of this project's own
  dissipation inequality). By the same reading: the Clausius relation's
  equality case is the reversible-thermodynamics sector; ceiling
  saturation is where extremal (heaviest-supportable) modes actually live;
  floor saturation (once it exists) is the Fiedler-mode boundary of
  connectivity itself. A one-page map of "which named classical theory
  lives on which saturation surface of this project's own inequalities" is
  a cheap, high-value writeup once OB-EXPANDER's floor exists.
- **Locks — conditions that collapse two free quantities into one fixed
  ratio.** `v=ωR` is what makes the rolling problem solvable at all. This
  project already has several: the CFL condition (`dt`↔`d_max`), the
  balance-law stationarity itself (`strain`↔`benefit`), the handshake
  identity (`Σdeg`↔`2·count`), and Ansatz C (`τ_c`↔`ω`, still a posited
  lock, not a derived one). `InfoCutGrowth.v` (queued, the Jacobson-import
  joint) is itself a candidate for a NEW lock — a horizon-growth "no-slip
  condition" tying cut growth to boundary flux.
- **Testing for hidden debt by translating canonical textbook problems.**
  The rolling-cylinder translation pointed back at an OPEN problem this
  project already names (the inertia-cost law) rather than manufacturing a
  new one — offered as light evidence (one data point, not a proof) that
  this project's Open-Problems list is not silently incomplete relative to
  classical mechanics. Suggested as a standing, cheap completeness check:
  translate one canonical problem at a time (a pendulum; a Kepler/inverse-
  square orbit — the riskiest one, since no long-range force exists
  anywhere in this kernel, so it will point either at joint D's weak-field
  dictionary or expose a genuinely new debt; a Carnot cycle — expected to
  land exactly on OB-ENTROPY-BRIDGE; a two-slit/two-state setup — expected
  to land on the separately-developed quantum/URCF layer) and record
  whether each one points at an existing named gap or forces a new one.

## 12.2 Three middle-school physics problems, run on this kernel

The §12.1 methodology was applied to three specific canonical problems
every student meets before university: heat equilibration ("does tea cool
faster with a wider heat-conducting wall"), free fall ("do a heavy and a
light object fall together"), and series/parallel resistor networks. All
three were run as actual numerical simulations on this repository's own
graph-Laplacian substrate — `finite_diagnostic` tier throughout, not
`Th_coqc` — and independently re-verified (not merely taken on report)
before being recorded here. All three land cleanly in the three buckets
§12.1 predicts: something the kernel already proves, something that is
this week's queued work, or a pointer at an already-named debt. None of
the three forced a new open problem.

**A. Heat equilibration = the Fiedler value, exactly, in the asymptotic
regime — with an honest caveat about what "asymptotic" excludes.** Two
cliques joined by a `k`-edge bridge (`k=1,2,4`), a unit heat spike injected
at one node, evolved under linear diffusion `du/dt = -L u` (the first-order
heat-equation reading of this project's own graph Laplacian). Independently
re-verified via eigendecomposition: in the LATE-time tail (once the fast,
non-Fiedler modes have died out), the decay rate of the deviation from
equilibrium matches `λ₂` to numerical precision (ratio `1.0000` at `k=1,2,4`
in re-verification), so the tail half-life obeys `t_half · λ₂ = ln 2`
exactly, independent of bridge width. **Caveat found during
re-verification, not in the original report: this only holds in the
asymptotic tail.** A naive "half-life measured from the initial spike"
definition is dominated by fast-decaying non-Fiedler modes and does
*not* show the invariant (re-verification found ratios of `0.04`-`0.05`,
not `\ln 2`, under that definition) — "how fast does heat cross a narrow
doorway" is a statement about the *tail* of equilibration, not the whole
approach to it. This is exactly why `λ₂`'s significance (queued as Tier A/B
of `OB-EXPANDER`, §12 item 8) is not an abstract spectral-graph-theory
curiosity: it is, quite literally, the answer to "why does tea cool slower
behind a thicker wall" once the transient has died down. The three-part
split the original report used maps directly onto existing/queued
machinery: the second law (`E` monotone, `Th_coqc` already) is the fact
that guarantees monotone approach to equilibrium at all; exact conservation
(`InfoGraphFluxBalance.v`, `Th_coqc` already) is the fact that fixes *what*
equilibrium value is approached; the *rate* is exactly the not-yet-
mechanized `λ₂` floor (Tier A/B, queued).

**B. Galileo's equal-fall claim is a corollary of substrate linearity, not
a separate physical postulate — and the claim's honest limit is the same
weak-field debt already named.** Two field packets of different amplitude
(a 3:1 ratio was used) evolved under this project's own mother-equation
dynamics (no separate "gravity" term — acceleration arises purely from the
`K`-weighted Laplacian gradient acting on the packet). Independently
re-verified on a minimal linear system (`a = -Kx`): the ratio `a/x` is
exactly `-K`, identically, regardless of amplitude, because the governing
equation is linear — a linear ODE's trajectory *shape* cannot depend on its
own amplitude, by the superposition principle. So "heavy and light objects
fall together" is not a coincidence requiring an equivalence-principle
postulate in this framework; it is what linearity of the mother equation
already forces, stated plainly: **equal-fall is a corollary of linearity,
not a separate physical input.** The one place this stays honest, not
free: the *sign* of "falling toward" (whether locally denser retention
reads as attractive, i.e. packets accelerate toward regions of lower `K`,
or repulsive) is exactly the same open weak-field dictionary question
already named as joint D under the gravity-arm closure discussion (§12
item, `mass_note.tex` §holo's `β↔1/8πG` dictionary) — this problem points
at that *same* existing debt rather than manufacturing a new one, which is
itself a small piece of evidence the open-problem ledger is not silently
incomplete.

**C. Series/parallel resistor laws are the composition laws of screen
capacity — the same object as this project's own boundary-screening
theorem, not a separate translation.** A standard two-resistor series
circuit and a two-resistor parallel circuit were built directly as
weighted graphs (edge weight = conductance) and solved via the Laplacian
pseudoinverse (`L⁺`), the standard exact method for effective resistance.
Independently re-verified: series (two unit resistors) gives effective
resistance `2.0000` (exactly `R1+R2`), parallel gives `0.5000` (exactly
`1/(1/R1+1/R2)`), and the Kirchhoff current-balance residual
(`L·v − i_injected`) is `5.6e-16` — zero to floating-point precision, i.e.
this project's own exact discrete divergence theorem
(`InfoGraphFluxBalance.v`, `Th_coqc`) *is* Kirchhoff's current law, not an
analogy to it. The genuinely new reading, not present in the original
translation exercise until checked here: series composition is exactly
two screen-partitions (§7's `gform_screen_partition`) chained end to end,
shrinking the effective cut capacity; parallel composition is two cuts
between the same two regions added side by side, increasing it. The
grade-school "resistors in series add, in parallel their reciprocals add"
rule is, read this way, the composition law for how much a boundary lets
through when two boundaries are chained versus doubled — the same object
`InfoBoundaryScreening.v`'s `Exterior`/`capacity` machinery already
formalizes, not a new one.

**What this exercise is, and is not, offered as.** All three are
`finite_diagnostic`: numerical demonstrations that a theorem-backed
substrate reproduces textbook physics under a direct, non-forced
translation, not new theorems in themselves. None of the three exposed a
gap the open-problem ledger did not already name. This is offered
honestly as two things at once: outreach material (three ordinary,
universally-recognized physics facts, reproduced from first principles on
a machine-checked substrate, understandable without weakening any of the
existing rigor), and a second data point (after the earlier rolling-
cylinder exercise, §12.1) that the completeness-audit method itself works
— it keeps finding existing debt, not manufacturing new debt, which is
itself the kind of evidence this project treats as meaningful rather than
decorative.

## 12.3 Reproducibility status of every numerical probe cited above

Every `finite_diagnostic` numerical claim in §12.2 and in the named
open-problem ledger (§12 items 7, 8, 11) now has a checked-in, runnable
script in `research_universal_solver/scripts/`, so a reader can re-run
these rather than trust the prose. **As of this entry, every claim below
also has a pytest assertion**, not just a runnable script — `pytest
scripts/test_reproduce.py` in `research_universal_solver` covers the five
`probe_*.py`-backed claims, and `pytest scripts/test_reproduce.py` in
`causal-quantum-gravity` covers the QNM frequency claim
(`supplement/completeness-and-claims.md` §13's Schwarzschild addendum) —
both suites were run and confirmed passing
before this entry was written, per this project's standing rule that no
numerical claim enters this document without an actual, executed test.
Honest status of each, not glossed:

| Claim | Script | Status |
|---|---|---|
| Heat equilibration: `t_half·λ₂=ln2` (tail), and the naive-definition counterexample | `probe_heat_equilibration.py` | **Reproduces exactly** (ratio `1.0000` at `k=1,2,4`; naive definition gives `0.04`-`0.05`, confirming the caveat) |
| Galileo equal-fall = linearity corollary | `probe_galileo_linearity.py` | **Reproduces exactly** (`a/x` ratio identical to floating-point precision across amplitudes `1, 3, 10`) |
| Series/parallel = screen-capacity composition | `probe_circuit_screening.py` | **Reproduces exactly** (`R=2.000000`, `R=0.500000`, Kirchhoff residual `5.6e-16`) |
| Gravity-sign three-channel test (§12 item 11) | `probe_gravity_sign_channels.py` | **Qualitatively confirms** (chords/stiffness wrong-signed, inertia correct-signed, all three reproduce independently) — exact percentages differ from the originally-reported `27%/15%/23%`, expected since this is an independent reconstruction of the method, not the original code |
| Ramanujan-graph expander quality (§12 item 8) | `probe_ramanujan_expander_quality.py` | **Does NOT reproduce** — this reconstruction found grown graphs are an equal-or-better expander than random in 4/5 seeds tested, the OPPOSITE of the originally-reported `q≈1.63` (grown, worse) vs. `q≈1.23` (random, better). Flagged as an open, unresolved discrepancy — NOT silently tuned to match, and NOT treated as a refutation of the original finding either, since the exact retention-growth rule and random-graph construction used here are an independent guess at the described method, not the original code. Whoever revisits `OB-EXPANDER` should treat this specific sub-claim as unconfirmed until either script is checked against the other's exact parameters. |
| OB-ENTROPY-BRIDGE cumulative-ratio probe | `probe_entropy_bridge.py` | **Inconclusive by design flaw**, already disclosed at first use: default parameters allow too few retention events (1-5 over 600 steps) for the ratio to be a fair test either way; not yet rerun with corrected parameters |
| Effective-inertia mode-locking probe (§12 item 11 mechanism demo) | *(no script checked in yet)* | **Not yet reproduced independently** — reported numbers (`+3.4%` linear control, `+32.5%/+47.3%/+69.1%` at increasing mode amplitude) have no corresponding script in this repo as of this entry; add one before citing these numbers as settled |
| Price-type late-time tail on the Schwarzschild QNM bridge (completeness-and-claims.md §13 Schwarzschild addendum) | `price_tail.py` | **Reproduces cleanly, including the required T1 control** — time-symmetric slopes `−7.89/−8.03/−8.01`, momentum-type control `−7.03/−7.02/−7.01`, family split `1.00` |

