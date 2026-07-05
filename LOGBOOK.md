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
