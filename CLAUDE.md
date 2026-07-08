# CLAUDE.md — Causal Quantum Gravity (AI agent entry point)

> For any AI agent (Claude, Codex, Gemini, or otherwise) opening this repo with no
> prior context. Read this file first, then follow the pointer below that matches
> what you're trying to do.

## What this repo is

A machine-checked (Coq, axiom-free over ℚ) research programme: one graph-Laplacian
"mother equation" whose spatial coupling term (`L_R`) is genuinely FORCED from the
graph root, and whose quantum-dispersion and special-relativistic wave-operator
readouts are proven literally the same equation under an exact algebraic
reparametrization — a real, non-vacuous `ring` identity, though one relating
posited (not root-forced) ingredients on both sides; see `SUPPLEMENT.md` §1.1/§4/§8
(added 2026-07-08) for the tier-honest scope before citing "derives QM and SR" as
an unqualified claim. General relativity is honestly **not** derived — eight
independent attempts were tried and refuted or left open, documented in full, and
the manuscript argues this is the philosophically correct outcome, not a numerical
shortfall. See `README.md`'s headline paragraphs for the actual claims before
reading anything else.

## The documents, and which one to open for what

This repo deliberately keeps documents with non-overlapping roles (`SUPPLEMENT.md`
grew large enough to split into four files as of 2026-07-06 — see **[`KGMAP.md`](KGMAP.md)**
for a one-page document graph and a "which file answers which question" table if
you want the map before the detail). Open the right one, not all of them:

- **`README.md`** — current state. Start here for "what does this repo claim, what's
  the tier legend, how do I reproduce it." Includes the full file-by-file
  `formal/*.v` inventory and `Print Assumptions` expected output.
- **`SUPPLEMENT.md`** — narrative and audit trail (§0-§11: dependency DAG, all
  branches, novelty audit §10, its external-audit gate §10.1 — still open, not
  yet independently reviewed). **Split into four files as of 2026-07-06** (see
  its own index at the top): the open-problem ledger, every NAMED open problem
  (`OB-FORMAN-RICCI`, `OB-ENTROPY-BRIDGE`, `OB-EXPANDER`, `OB-RG-FIXED-POINT`,
  `OB-TIE-MANIFOLD`, `OB-LONG-RANGE`, `OB-QUANTUM-GEOMETRY`, and more) now lives
  in [`supplement/open-problems-ledger.md`](supplement/open-problems-ledger.md)
  — this is where to look before starting new work, so you don't duplicate
  something already named and scoped. The completeness scoreboard and
  Unification Claim Card are in
  [`supplement/completeness-and-claims.md`](supplement/completeness-and-claims.md);
  references are in [`supplement/references.md`](supplement/references.md).
- **`LOGBOOK.md`** — chronological history, captain's-log style, append-only, never
  rewritten with hindsight. Open this for "how did we get here, and what did we try
  that didn't work" — it records the journey the other three documents don't (a
  referee catching a real gap and the fix that answered it; a bug that recurred
  three times before the lesson stuck; a deliberate scope decision and its
  trade-off). If you're about to repeat something, check here first.
- **`paper/main.tex`** / **`paper/mass_note.tex`** — the actual manuscript and its
  companion synthesis note (separately authored, same author, do not edit
  `mass_note.tex` without asking — it's a standalone preprint this repo hosts as a
  supplement, not this repo's own document).

## Common misreadings — check before citing (a fresh AI's checklist)

Four terms carry a meaning here that differs from the everyday/textbook sense. Check each before
repeating a claim that uses one — misreading any produces a confident, wrong summary.

1. **"Mass" (memory-before-mass).** `InfoMemoryBeforeMass.v` is the careful, well-scoped result: the
   recovery timescale `tau_c = M/D` (memory) is treated as primary, and `M` is INFERRED from it
   (`M = tau_c * D`), not the reverse — the file proves this ONLY as a discrete structural fact (two
   systems sharing `tau_c` are dynamically indistinguishable regardless of separate `M`,`D`); the
   ONTOLOGICAL claim that mass IS derived from memory stays explicitly `Dr`/`Open` in the file's own
   scope section, not proved. If you see "mass" used elsewhere as a name for a memory-derived quantity
   (e.g. a frequency `D/(2M)`), check whether that sentence means the raw parameter `M` or a
   reciprocal-of-memory reading — they are not the same thing.
2. **Infinity / zero (`I1`–`I4` / `Z1`–`Z4`, `SUPPLEMENT.md` §1.2).** The continuum/ℝ/∞ (`I1`-`I4`) and an
   injected EXACT zero (`Z1`-`Z4`, dual to the `I` catalogue) are both refused NON-readouts here —
   approached, never reached. Never read a `Print Assumptions` Closed theorem as having "solved" a
   continuum question it merely refused to pose, and never read an exact-zero claim (e.g. "X can never
   be exactly zero") as an ordinary computed `0`-value fact — check which of the two it means.
3. **Discrete time.** Every "for all time" / "global" / "persists forever" theorem here quantifies over a
   discrete step index (`nat` or an explicit finite structure) — NEVER over continuum `t : ℝ`. The jump
   to continuum time (`h→0`) is itself an `I2` injection (see above); this repo does not smuggle it in
   silently. Check whether a "global in time" claim is `forall n : nat` (Th_coqc, the common case here)
   or genuinely needs `Coq.Reals` (`+reals`, a different, much rarer tier in this repo) before citing it
   as a continuum ODE/PDE stability result.

## Tier discipline (non-negotiable, see README's "Tier legend" for the full table)

Every claim carries `Th_coqc` (axiom-free, machine-checked) / `+reals` (depends on
Coq's disclosed Reals axioms only) / `finite_diagnostic` (numerical, not proof) /
`Dr` (interpretive stance) / `Open` (named, unsolved). Never collapse these. Before
adding a claim, check whether the tier you're about to write is actually what the
underlying Coq file's `Print Assumptions` output supports — this project's single
most repeated bug (see `LOGBOOK.md`) is a theorem count or tier claim drifting from
what's actually provable.

## Reproduce before trusting anything

```
make verify   # compiles all formal/*.v, runs the QNM bridge script
```
CI (`.github/workflows/verify.yml`) runs this on every push and has been green on
every commit to date — check the Actions tab for the current state rather than
assuming.

## The sibling private repo

This repo is a curated, standalone export of a subset of theorems from
`research_universal_solver` (private). New theorems are developed and verified
THERE first, as `formal/Info*_attempt.v` files, via a 3-stage discipline (standalone
`coqc` → repo-namespace `coqc` → full `make verify-attempts`). Only after that do
they get copied here (dropping the `_attempt` suffix) as a separate, later sync
step — never written directly in this repo. Every equation this repo cites from
outside literature should already be registered, with owner and year, in that
sibling repo's `docs/root/EQUATION_REGISTRY.md` — check there before adding a new
citation from memory.
