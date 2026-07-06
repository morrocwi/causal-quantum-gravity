# AUDIT BRIEF — Adversarial Review Form for the Synthesis Note (C1–C4)

**Purpose.** This programme's external-audit gate is open. This brief gives an
auditor the four load-bearing claims *verbatim*, the exact refutation condition
for each, the artifacts needed to attack them, and the standing retraction
pledge. The intended reading mode is adversarial: try to break these.

**Pinned objects.** Repository `github.com/morrocwi/causal-quantum-gravity`
(`formal/`, `Makefile`, CI `make verify`); companion note `mass_note.pdf`
(v16-line, 26 Tier-0 files / 186 closed checks + 2 Tier-1 / 6). Six files of
this revision postdate the pinned commit; their SHA-256 prefixes are of the
delivered sources: CubicLinearization `4df87c1dd7f531e8`, SpectralCeilingSharp
`1f478ed777172de3`, TensorEvolution `b5638ddf507fa5b2`, CutGrowth
`4d46a4374296f375`, ModeWeights `9e97c7f6ad08d6cd`, BackReaction
`369e17320544e147`, ShiftAverage `a9e3890bbdb91afe`.

---

## C1 — the epistemic standard (an absence claim)

**Verbatim.** "to our knowledge the first machine-checked kernel in any
discrete-gravity programme, where competing programmes argue in prose
(machine-checked *continuum* relativity does exist — axiomatic Minkowski
spacetime in Isabelle/HOL — and is complementary rather than prior …)"

**How to refute.** Produce ONE public repository, predating this programme's
pinned commit, containing a machine-checked kernel (Coq/Isabelle/Lean/Agda or
equivalent) whose theorems constitute core dynamics or geometry laws of a
*discrete-gravity substrate* (not continuum relativity axiomatics, not verified
continuum numerics). The note's Appendix A states the search protocol used;
searching outside that protocol is exactly the point.

**Pledge.** One counterexample repository ⇒ C1 retracted verbatim in the next
revision.

## C2 — tier-factored assembly, acyclic

**Verbatim.** "the tier-factored assembly itself, with an acyclic dependency
structure audited in Section 4."

**How to refute.** Exhibit a cycle: a Dr/ansatz statement upstream of any Th
tag, or a Th proof consuming an ansatz. Attack surface: the dependency DAG
(Fig. 1), the circularity audit (a)–(e), and `Print Assumptions` on every file
(any hidden axiom breaks the tier claim mechanically).

## C3 — the welds, "none found in prior literature"

**Verbatim welds.** (i) retention balance pricing a tensor evaluation
(two-way); (ii) dissipation threshold pair as a native checkable horizon;
(iii) curvature-monotone mass cap with contrapositive (mass *forces*
curvature); (iv) cosmological term as the structurally forced affine part of
any benefit function; (v) rigidity: one global lens forces a non-constant,
curvature-dependent temperature.

**How to refute.** For any weld, cite prior work stating the *same
composition* (not the classical ingredients — those are owned and cited:
Anderson–Morley, Forman, Jacobson, Störmer–Verlet, Green–Ostrogradsky …). A
prior-art hit on any weld demotes it from contribution to import in the next
revision.

## C4 — two-arm independence

**Verbatim.** "mass and holography arrive at the precursor's two sides —
source content and equation form — independently, sharing no ansatz, so the
failure of either identification leaves the other standing."

**How to refute.** Exhibit a shared ansatz: show Ansatz C (mass–clock) used in
the holography arm, or Ansatz H/T used in the mass arm. Attack surface:
Section 3 vs Section 5 assumption lists; the DAG's two disjoint gray columns.

---

## Reproduction (all claims, offline)

```
git clone https://github.com/morrocwi/causal-quantum-gravity && cd causal-quantum-gravity
make verify          # compiles formal/, audits Print Assumptions per tier
sha256sum formal/*.v # compare 16-hex prefixes against Table 2 of the note
```

Tier meanings: `Th_coqc` = closed under the global context, no axioms;
`+reals` (= note's Tier-1) = exactly `sig_forall_dec` + functional
extensionality, no classic; `finite_diagnostic` = reproducible numerics, not
proof; `Dr` = interpretive; `Open` = admitted gap.

## Standing falsification targets beyond C1–C4

- Sharp ceiling: any exact pair violating `Qabs lam <= deg u + deg v` on any
  edge-maximizer (300-graph pre-verification supplied; break it).
- Scalar-contact result: exhibit a long-range static field from the symmetric
  quartic channel (mean-field argument + numeric leak ~2e-6 say no).
- The note's Open list (Section 7) is the programme's own attack map; any item
  there closed *against* the stated expectation is a welcomed refutation.
- **Unification boundary (C-class):** `supplement/completeness-and-claims.md`
  §14 ("The Unification Claim Card") fixes exactly what "unification" does and does not mean here.
  Find one sentence, anywhere in this repo, the companion note, or a public
  statement by its author, that trades on a claim from the card's explicit
  NOT-claimed list (QM's probabilistic structure; Einstein's field equations
  as derived rather than imported; any quantization of geometry itself,
  `OB-QUANTUM-GEOMETRY`; the generative, unaided-substrate side of gravity,
  `OB-LONG-RANGE`) as if it were established. One sentence is sufficient for
  a class-C refutation.

**Contact.** Findings via repository issues. Every accepted refutation is
logged in LOGBOOK.md with credit.
