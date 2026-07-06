# Project Logbook — Causal Quantum Gravity

> A ship's log, not a changelog. `README.md`/`SUPPLEMENT.md`/`paper/main.tex`
> describe the *current* state of the work; this file records the *journey*
> to it, in the order it happened — what was tried, what worked, what
> failed, and every decision that shaped scope, in one place. Entries are
> append-only: never rewritten to look smarter in hindsight, never deleted
> when a later entry supersedes them (mark the later entry's relationship to
> the earlier one instead). Every entry is tagged **Positive**, **Negative**,
> **Decision**, or **Mixed**, and dated to the commit (or the moment inside a
> commit) it belongs to. When continuing this project, append here before
> anywhere else — a captain's log is worthless if it stops being written the
> day things get complicated.

---

## 2026-07-05 01:28 — Initial release: Discrete Quantum Gravity from a Retained-Difference Root
**Type:** Positive · commit `85e5711`

First public cut of the standalone repository, extracted from the private
`research_universal_solver` programme. 24 Coq files, 123 theorems, all
machine-checked. Headline result at launch: one graph-Laplacian mother
equation `M∂²Φ + D∂Φ + K·L_R·Φ + ∇V(Φ) = J−η` genuinely derives a quantum
energy-dispersion relation and a discrete causal/Lorentzian bilinear form
whose continuum limit is the d'Alembertian — both from the same equation,
without importing either formula. General relativity explicitly not
derived, with the position stated as philosophical (continuum GR is a
non-readout under this project's own diagnostic), not a numerical
shortfall still being chased.

## 2026-07-05 01:32 — Fix: reproducibility protocol quoted the wrong row
**Type:** Negative → fixed · commit `6236e1c`

Caught almost immediately after release: the reproduction instructions
quoted the QNM convergence value from the `N=1600` row of the convergence
table when the actual claimed headline value was the `N=3200` row. Small,
but exactly the kind of error that erodes trust in a reproducibility
protocol the whole project's credibility rests on — fixed same session,
logged here because "we found our own reproducibility doc was wrong on day
one" is worth remembering when tempted to trust a doc without re-running it.

## 2026-07-05 01:52 — Rename to Causal Quantum Gravity
**Type:** Decision · commit `9e2d25a`

Renamed from the working title to the one carried forward. No content
change; recorded here only because it is the point after which every
external reference (SHA hashes, mass_note.tex's citation, the GitHub repo
name) is stable.

## 2026-07-05 02:26 — Referee finds the dispersion relation doesn't match Schrödinger mechanics
**Type:** Negative → led to a real theorem · commit `d748d20` (context for it)

An independent adversarial referee review of the original release correctly
flagged that the headline dispersion relation `E²M = ħ²Kλ` is *quadratic*
in `E`, and does not match non-relativistic Schrödinger mechanics, which is
first-order in `E`. This was a real gap, not a nitpick: the original framing
had left ambiguous which quantum mechanics was being claimed.

**The response, logged as the positive counterpart to this same entry:**
rather than retreat the "derived" claim, the project proved *why* the
mismatch exists — the mother equation's dispersion is the *relativistic*
(Klein–Gordon-family) dispersion, and a new file
(`InfoQuantumRelativityUnification.v`) proves this identification is
*exact*, not a resemblance: the quantum dispersion condition is literally
the vanishing condition of the same boost-invariant wave operator governing
the special-relativistic branch. One equation, two readouts, proved rather
than asserted. This is the shape this project tries to repeat every time a
referee finds a real gap: prove more, don't narrow the claim to dodge the
finding.

## 2026-07-05 02:26 — Six-result strengthening campaign + graph growth
**Type:** Positive · commit `d748d20` (57 new theorems: 44 + 13)

Same commit as the referee response above. Four previously-informal claims
promoted to theorems (frequency/UV ceiling forced by the graph's own
maximum degree; an exact "no local creation" energy-balance law; a
Schrödinger-shaped skew-adjoint first-order skeleton; a causal
sign-construction theorem with an honestly disclosed partial closure) plus
a discrete Noether theorem, plus a separate graph-growth result showing
growing the graph itself is a native, non-continuum discrete analog of
cosmological expansion — explicitly not claimed to resolve any physical
cosmological discrepancy.

## 2026-07-05 02:50 — Final adversarial review finds count/self-verification bugs
**Type:** Negative → fixed · commit `147c86f`

A review pass on the campaign above found theorem-count and file-count
mismatches between what the manuscript claimed and what the Coq sources
actually contained, plus gaps in the self-verification story. Fixed same
session. First appearance of a pattern that recurs at least three more
times in this log: **claimed counts drift from actual counts faster than
anyone expects, and only an independent recount catches it.**

## 2026-07-05 04:00 — Action stationarity, curvature-horizon structure, n-D spectral ladder
**Type:** Positive · commit `5b10f6d` (C48–C53)

Six more files. Headline results: a double-stationarity theorem showing the
field recurrence and the retention of graph edges are the two
first-variation readouts of *one* quadratic action (not two separate
postulates); an exact two-way balance between per-edge strain and an affine
function of Forman curvature, with a horizon-threshold pair
(`no_escape`/`repair_exists`) giving "local horizon" a native, checkable
meaning instead of a borrowed one; and a four-step spectral-convergence
ladder closing the flat and diagonal-metric cases of the mother equation's
n-dimensional continuum limit, narrowing the general-metric case to one
named, literature-cited gap.

## 2026-07-05 11:46 — Sync C54–C64 + the optimizer window from the private repo
**Type:** Mixed (Positive + Decision) · commit `83d7888` (11 files, 73 theorems)

Eleven more self-contained files synced from `research_universal_solver`: a
discrete disk-before-lock analog; a closed seed-to-spectral-ceiling chain; an
algebraic bridge to a separately-developed roots-of-unity/golden-ratio track
(curvature-Noether invariance, a literal `i`-rotation-matrix identity, a
pentagon-graph spectrum landing in the golden ratio's field); a graph-native
boundary-energy fact and a degree-curvature bound; a general
tensor-reconstruction fact with a curvature bridge conditional on one stated
affine-cell hypothesis; and a momentum-optimizer/kernel-energy
identification.

**The decision, logged explicitly because it was a real trade-off, not an
oversight:** `InfoPersistentWalkBridge_attempt.v` — a genuine, working result
connecting a Goldstein–Kac persistent random walk to the mother equation's
(X,V) structure — was deliberately **excluded** from this sync. It Requires
`RDL_SpineGraphCoupled.v` and `InfoPrimordialDifferenceRootIdentity_attempt.v`,
neither of which is self-contained, and pulling either in would break this
repository's stated standalone/minimal-dependency design. The alternative
(pulling in the full dependency tree) was judged a bigger scope decision
than a routine sync warrants, and was deferred rather than made silently.
Anyone tempted to "just add it later" should re-read this entry first: the
dependency tree it would bring in has never been audited for what else it
would drag along.

## 2026-07-05 12:06 — Round-4 review finds theorem-count inflation across four files
**Type:** Negative → fixed · commit `49945bd`

The pattern from 02:50 recurred, worse: four of the eleven files just synced
had their manuscript-quoted theorem counts inflated by silently counting
`Print Assumptions`-checked **Lemmas and an Example** as if they were
headline `Theorem`/`Corollary` results (`InfoCurvatureNoether.v`: quoted 7,
actually 3; `InfoDegreeFromCurvature.v`: quoted 4, actually 2;
`InfoTensorFrame.v`: quoted 8, actually 7; `InfoStrainTensorBridge.v`: quoted
12, actually 11). Corrected grand total: 35 files, **188** theorems, not 196
— independently re-derived by summing real `Theorem`/`Corollary` counts
across all 35 files by hand, not by trusting the arithmetic that produced
the wrong number in the first place.

Same review round also caught two title-level overclaims (a section named
itself after the Bekenstein–Hawking "area law" while its actual disclaimer
that it is *not* that bound lived three sentences into the body; a section
titled a result as an unconditional identity when it only holds on a
quadratic mode inside a stability window) and flagged that the Novelty Audit
and Reviewer Attack Response sections had not been extended to cover the six
newest sections at all. **Lesson repeated from 02:50, now in a form worth a
standing rule:** re-verify every per-file theorem count against the literal
Coq source at the moment it is quoted, every time — not once, not "it
matched last time so the method is fine."

## 2026-07-05 13:09 — Companion mass-synthesis note added; curvature-limited mass composed into the manuscript
**Type:** Mixed (Positive + Decision + Negative→fixed) · commit `7d19c8f`

A separate, self-contained preprint by the same author ("A Synthesis of the
Information Universe," `paper/mass_note.tex`), built directly on this
repository's own theorems pinned to a specific commit, was reviewed and
added as a companion supplement rather than merged into the main
manuscript's own claim set — **the decision being that a separately-authored
document with its own abstract, literature review, and circularity audit
should stay legible as its own artifact**, not be absorbed and lose that
structure. Before accepting anything it claimed: batch-verified every
theorem/lemma name it cites (~25 names) against the actual `formal/*.v`
files, spot-checked 4 of its 21 SHA-256 hashes by direct computation, and
hand-verified the composed algebra (spectral ceiling + degree bound →
frequency ceiling → mass bound → its contrapositive "mass forces
curvature"). All checked out.

A focused review of the *integration* (not of the note itself) then found
three real problems in how the main manuscript represented it: the new
section omitted the note's own second, independent caveat that restricting
the mass bound to a *localized* excitation's support subgraph — precisely
the physically motivating case — is only a numerical finding, not a theorem,
even granting the imported identification; a cross-reference claimed a
dependency was "disclosed" in a section that never actually raised the
question; and the boundary section claimed the main manuscript's version was
"always the narrower one," which was false specifically on the localization
point. All three fixed. Two smaller issues (two orphaned, uncited
bibliography entries) were found **inside `mass_note.tex` itself** and
deliberately **left untouched** — it is a separately-authored document, not
this repository's own manuscript, and is not this project's to silently
edit without asking first.

## 2026-07-05 14:21 — Negative-results log expanded; external-audit gate opened
**Type:** Decision · commit `15b2c1d`

Two additions, both about epistemic posture rather than new physics. First,
the compressed eight-attempt GR-derivation-failure table (§5.2 of
`SUPPLEMENT.md`) was expanded into a full write-up — hypothesis, why it
looked plausible, the test, the failure mode, and the generalizable lesson,
for each of the eight — on the reasoning that a field which mostly only
publishes what worked is short on detailed accounts of what didn't, and this
project already had the material to write one honestly. No technical fact
was changed in the expansion, only made legible.

Second, and more consequential: an explicit "external audit status" section
was opened, stating plainly that the mass-synthesis note's four contribution
claims (C1–C4, including the absence claim "no prior discrete-gravity
programme has a machine-checked kernel of any size") have been checked only
by the author and by adversarial AI review — and that neither is a
substitute for an independent human domain expert with no authorship stake.
**This is logged as a decision, not a finding**, because it is a deliberate
choice to name an unclosed gate rather than let the project's own confident
tone imply the gate is closed. The next entry in this log, whenever it
comes, should be either the record of that external review actually
happening, or an honest note that it still hasn't.

## 2026-07-05 17:03 — Six named gaps each got a first foothold; none closed, and saying otherwise was caught in real time

**Type:** Mixed (Positive result + a self-caught overclaim, corrected before
it reached any document) · commits pending

The busiest single day this project has had: five new mechanized Coq files
(`InfoCubicLinearization.v`, `InfoSpectralCeilingSharp.v`,
`InfoTensorEvolution.v`, `InfoCutGrowth.v`, `InfoModeWeights.v`, 25 theorems/
lemmas total, all axiom-free) plus four numerical probes (gravity-sign
three-channel test, the mode-locking mechanism demonstration, a Poisson-
coupling coefficient extraction, and a capacity/rank/cut chain check), each
one landing directly on one of the six gaps named in `SUPPLEMENT.md` §13's
completeness scoreboard (written earlier the same day).

**The overclaim, caught before it landed anywhere permanent:** mid-session
chat language drifted to "หกช่องแตะครบ" / "มี Th core" (roughly, "all six
boxes touched / have a theorem core") for the whole set. This is not what
happened, and the author caught it in the same conversation, unprompted,
before it reached this logbook, `SUPPLEMENT.md`, or the companion note.
The precise, corrected accounting:

- **`GAP-2`** — got an exact tensor *update law* (`InfoTensorEvolution.v`).
  The actual gap content — what field equation `T` obeys, covariance,
  conservation — is untouched. Opened the door; the room behind it is
  still empty.
- **Cut-growth** — got the *static* half (exact bookkeeping + priced
  screen growth, `InfoCutGrowth.v`). The *dynamic* half a Raychaudhuri-
  style argument actually needs (a rate law, focusing) is fully open.
- **Born-weld** — got the Born *shape* on one concrete graph (C6,
  `InfoModeWeights.v`): a quadratic-form identity, not a probability
  structure. No measurement, no CPTP weld, and it is an instance on one
  graph, not a general theorem.
- **Bridge/`ansatz-T`** — a probe confirmed the *shape* of a lower bound
  (and only for the active-phase regime; the run had no quiet-phase epoch
  to compare against). Zero theorems changed.
- **Constants** — the field-side Poisson coupling extraction is at 89%,
  not 100%; the geometry-side `G=1/(8πβ)` is still pure `Dr`; `α/β` did
  not move at all.
- **Capacity/`ansatz-H`** — the rank/boundary/cut chain was confirmed
  numerically (200/200), but the corresponding theorem sits in a file
  that has not yet passed this repo's own audit, and the equality case is
  permanently graph-dependent, not a universal fact.

Checked against the four-level completeness criterion from §13, written
the same afternoon: **no level moved.** Level 1 was already closed before
today. Level 2's GR half is still open (an update law is not an evolution
equation). Levels 3 and 4 were not touched by anything today.

**The lesson, stated once so it does not need re-deriving:** the honest
description of a day like this is *"six gaps each got a first foothold;
none of the six is closed"* — not "six gaps closed" and not "six gaps
touched" (too vague to falsify). The distinction matters because this
project's stated identity (§13) is not "every gap closed" but "every gap
has a status label that is actually true" — and a chat-language shortcut
that inflates "foothold" into "closed" is exactly the kind of drift that
would make that identity false without any single sentence in a committed
document being wrong. This is the fourth time this specific failure mode
(enthusiasm inflating a real result into more than it is) has been caught
in this project's history; the first three are named in earlier entries
and in `feedback-short-review-per-decision` in the operator's own memory
system. Also worth naming plainly, once, rather than leaving as an
implicit assumption: some of these six gaps may not be closable at all in
the form stated — the Jacobson conclusion is imported by deliberate razor,
not derived, and is not a target; capacity equality is graph-dependent by
its nature, not a temporary limitation; a full Born rule may need
structure this kernel's tier does not have room for. "Complete" here has
never meant "every gap eventually closes" — it means "every gap's status
label stays true no matter how much work lands next to it."

---

## 2026-07-05 (later same evening) — Second same-day recurrence of the foothold/closed conflation; a reviewer-pattern note

**Type:** Negative (a bias, caught and named, not yet fully eliminated) ·
commit pending, `InfoBackReaction.v` (sha256 prefix `369e17320544e147`)

Hours after the 17:03 entry above named the foothold-vs-closed distinction
explicitly, it recurred: a new file, `InfoBackReaction.v` (5 theorems,
axiom-free — the exact strain-splitting identity for a background field
plus a perturbation, the "matter acts on geometry" joint of the feedback
loop `stored energy -> edge strain -> retention decision -> geometry ->
inertia -> motion`), was summarized in chat as closing "every joint...
except one." A second-pass review of the loop's actual tier map found
this false in the same way as before: the loop has **two** open joints,
not one — `OB-HOMOGENIZATION` (the pointwise coefficient shift `3gψ²` from
`InfoCubicLinearization.v` has not been shown to average, over time, into
an effective inertia — that step is disclosed as not proven, not merely
unproven-but-assumed-fine) and `OB-GEODESIC` (no general trajectory
theorem exists; only a one-dimensional numerical demonstration does). The
file's own header was corrected before commit to state plainly: *"this
file closes ONE joint... the loop is NOT closed: two joints remain Open
and are named."* No proof content changed; only the header, and the
SHA-256 changed as a direct consequence (`7b20167f...` to `369e1732...` —
caught before the earlier hash was pinned anywhere, so no citation needed
correcting).

**The pattern, named so it can be checked for on purpose next time:**
this assistant appears to have a **systematic bias, specifically after
producing a run of consecutive positive results, toward summarizing
"most joints/gaps have an artifact" as "all but one are done."** It
happened twice in one day, on two different loops (the six-gap
completeness scoreboard, and this feedback loop specifically), and both
times the correction came from the human operator's own re-count, not
from this assistant's own review pass. **Standing mitigation, to apply
going forward and not just this once:** before writing any sentence of
the shape "N of M are done" or "only one is left," do an explicit
tier-recount against the actual `Th_coqc`/`finite_diagnostic`/`Dr`/`Open`
status of each item, out loud, before the summary sentence is written —
not after. A summary produced by memory of "how the work felt" rather
than a fresh recount is the failure mode; the recount itself is cheap and
should not be skipped under time pressure or momentum.

The probe work reported alongside this file (a two-layer falsification —
mean-field `⟨ψ³⟩=0` plus a numerical leakage measurement of `~2×10⁻⁶` —
finding the scalar channel is a contact interaction with no long-range
`1/r²` carrier) is assessed separately as sound: the retention-cascade
half of that same probe run died from a parameter choice (`α+βF=0` exactly,
zero benefit even in the control case) and was correctly disclosed as
**untested, not falsified** — this distinction was drawn correctly and is
not part of the pattern above. The resulting open question,
`OB-LONG-RANGE` (long-range gravity in this framework must be
operator-mediated — a permanent local change to `L` itself, read at a
distance through the linear channel's own Green's function — rather than
amplitude-mediated), is a real and sharp candidate, but is recorded with
an explicit qualifier: *conditional on the loop's two remaining open
joints closing as expected* — evidence-grade, not theorem-grade, until
they do.

---

## How to append to this log

- One entry per commit, or per distinct event inside a commit worth
  separating (a referee finding and the fix it produced are two entries
  even in the same commit, as in 02:26 above).
- Tag every entry: **Positive** (a result that held up), **Negative**
  (something that failed, was wrong, or was overclaimed — whether or not it
  was later fixed; say so either way), **Decision** (a scope or process
  choice with a real trade-off), or **Mixed**.
- State the *lesson*, not just the event, when there is one — a captain's
  log that only records "we hit a rock" without recording where the rock
  was is not useful to the next watch.
- Never delete or silently rewrite an entry. If a later entry corrects or
  supersedes an earlier one, say so in the later entry and leave the earlier
  one exactly as it was written.

---

## 2026-07-05 (evening) — Falsification #5: a two-lump "attraction" milestone downgraded within the same turn it was reported

**Type:** Negative (a claim self-caught before it reached any committed
document) · SUPPLEMENT.md SS12 item 12 (`OB-LONG-RANGE`)

A direct two-lump force measurement first read as "attraction confirmed"
was rerun, same session, with a bigger box and an explicit reference-drift
audit built in (hold one lump fixed, move the other, and separately
measure how much a single lump's own signal drifts with box position).
The rerun found the drift (`spread≈0.195`) is the same order as the
measured signal, and that `U(d)` changes sign non-monotonically with
separation — the signature of narrowband optical/acoustic binding, not a
monotone Newtonian carrier. The corrected reading is "two-body
interaction confirmed" (existence, high significance) with the shape
downgraded to "optical-binding class, produced by a narrowband bath," not
"attraction, Newton-like." No document had yet recorded the first,
uncorrected claim — it was caught and rewritten before ever being
committed, which is the version of this discipline that costs the least.

**The lesson, added to the standing probe-design checklist:** every
two-body interaction probe must print its own single-body reference
drift alongside the interaction signal, in the same run, before any sign
or magnitude claim. Reproducibility across seeds (small standard
deviation between runs of the same configuration) is necessary but not
sufficient — it does not rule out a systematic, non-cancelling,
nonlinear-dressing artifact that is identical across seeds but still
wrong. This is the fifth self-caught falsification recorded in this
project's history, and the second in one day (see the 17:03 and later
entries above) — the rate at which the project catches its own
overreaching claims is treated here as a health signal, not an
embarrassment.

---

## 2026-07-05 (evening) — HANDOFF_SW_BRIDGE.md's T1-T3 completed independently; T4 written with re-run numbers, not reported numbers

**Type:** Positive · `scripts/price_tail.py`, `formal/InfoConeInheritance_attempt.v`

A handoff document (`HANDOFF_SW_BRIDGE.md`) described the Schwarzschild
bridge as paying four currencies (values, causality, spectrum, shadow)
and listed required follow-up items T1-T4. Rather than accept the
handoff's own reported numbers, each item was independently executed in
this repo before being written into any permanent document, per this
project's own pytest-before-claim rule:

- **T1 (exponent-family control):** run independently. Momentum-type
  initial data gives the classic Price `-7` family (`-7.03/-7.02/-7.01`);
  time-symmetric data gives a steepening `-8` family
  (`-7.89/-8.03/-8.01`, matching the handoff's own reported
  `-7.87/-8.01/-8.09` closely); the two families split by exactly `1.00`,
  satisfying the acceptance test cleanly — not escalated.
- **T2 (ship the probe):** `scripts/price_tail.py` written, independently
  authored from the handoff's exact recipe (not copied), with a PASS/FAIL
  summary line and two executed, passing pytest tests in
  `scripts/test_reproduce.py`.
- **T3 (registry before claims):** Price (1972), Gundlach-Price-Pullin
  (1994), Ching-Leung-Suen-Young (1995), Regge-Wheeler (1957), and Leaver
  registered in `EQUATION_REGISTRY.md` before this entry — Leaver's year
  corrected from the handoff's stated 1986 to the actual 1985.
- **T4 (paragraph into SUPPLEMENT.md):** written using this repo's own
  re-run numbers, not the handoff's reported ones — the causality currency
  additionally required writing a new file, since the handoff's own
  `InfoConeInheritance.v` (cited there at sha `52f707d113a9bd43`) was
  described but never delivered to this repo. An independent file of the
  same name was authored from the handoff's description (a generic
  leapfrog step over an arbitrary edge list and per-node coefficient
  field, one-step-local, specialized to a path graph) — 3 theorems,
  axiom-free, necessarily a different hash from the cited one since it is
  a different authoring, not a copy.

**The general lesson this arc reinforces:** a handoff document, however
carefully written, is still a claim from outside this repo until it is
independently re-run inside it. Every one of T1-T3 reproduced closely but
not identically to the handoff's own numbers (expected, given independent
re-implementation) — close enough to trust the physics, different enough
to be a reminder that "verified" means executed here, not read there.

---

## 2026-07-06 — TEST 3's published "concrete next step" had already been refuted in the sibling repo; ledger corrected before anyone executed a dead plan

**Type:** Correction (documentation lag, caught at sync) ·
`supplement/open-problems-ledger.md` `OB-QUANTUM-GEOMETRY` TEST 3

This repo's open-problems ledger told the next worker exactly what to do
about TEST 3's inconclusive tie-manifold run: "calibrate `α, β` so the
population's median `strain−benefit` sits near zero by construction, then
measure the SHAPE of the distribution." In the sibling repo
(`research_universal_solver`, where all new work is developed first), that
exact fix had already been proposed, debated in a two-round cross-model
peer exchange, and **rejected without ever being run** — the counter-argument
(recorded verbatim in `probe_tie_manifold_drift.py`'s docstring) being that
parking the bulk of a generic distribution on the boundary by construction
guarantees the trivial exponent, so the calibration would have measured its
own setup, not the dynamics. The replacement probe (boundary-localized
drift, early/late epochs) then had its own first draft corrected for
survivorship bias by independent review, landing on a finding neither
debate participant predicted: **90.0% of the true window-1 candidate
population (1224/1360, 8 seeds) is born exactly at the tie boundary and
retained on the spot; the far-from-boundary population TEST 3 originally
measured is the surviving minority, a different quantity.** Near-tie
occupancy at first contact is thick, not thin.

Synced today: the ledger paragraph now records the rejected fix, the
debate, the corrected finding, and the two-quantities distinction. Probe
and its three pytest tests re-executed on this machine today (all passing)
before the numbers entered the document — "verified" means executed here,
not read there.

**The lesson:** an export repo's "next step" note is a claim with a shelf
life. When the development repo moves, a stale pointer here actively
misdirects the next contributor toward work already known to be dead —
sync discipline is part of honesty discipline, not housekeeping.
