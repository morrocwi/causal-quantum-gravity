# Knowledge Map — Causal Quantum Gravity

A one-page map of every document in this repo and how they relate, for anyone (human or AI)
opening this repo cold. Not a new source of truth — every fact below is a pointer, not a
restatement; if this map and a linked document ever disagree, the linked document wins.

## Document graph

```mermaid
graph TD
    README["README.md<br/>current state, tier legend, reproduce"]
    CLAUDE["CLAUDE.md<br/>AI agent entry point"]
    LOGBOOK["LOGBOOK.md<br/>chronological history, append-only"]
    AUDIT["AUDIT_BRIEF.md<br/>external-audit attack form (C1-C4, unification boundary)"]
    SUPP["SUPPLEMENT.md<br/>§0-11: DAG, branches, novelty audit"]
    LEDGER["supplement/open-problems-ledger.md<br/>§12: every named OB-* problem"]
    COMPLETE["supplement/completeness-and-claims.md<br/>§13-14: scoreboard + claim card"]
    REFS["supplement/references.md<br/>every external equation cited"]
    MAIN["paper/main.tex<br/>the manuscript"]
    MASSNOTE["paper/mass_note.tex<br/>companion note, separately authored"]
    EQREG["research_universal_solver/docs/root/EQUATION_REGISTRY.md<br/>canonical citation source"]

    CLAUDE -->|"points every agent to"| README
    README -->|"links to"| SUPP
    README -->|"links to"| LOGBOOK
    README -->|"links to"| MAIN
    README -->|"links to"| MASSNOTE
    README -->|"links to"| AUDIT
    SUPP -->|"index at top, split into"| LEDGER
    SUPP -->|"split into"| COMPLETE
    SUPP -->|"split into"| REFS
    LEDGER -.->|"cross-refs"| COMPLETE
    COMPLETE -.->|"cross-refs"| LEDGER
    AUDIT -->|"C1-C4 quote"| MAIN
    AUDIT -->|"unification boundary quotes"| COMPLETE
    MAIN -->|"defers detail to"| SUPP
    MAIN -.->|"composes with"| MASSNOTE
    REFS -.->|"should already exist in"| EQREG
    LOGBOOK -.->|"records decisions that changed"| LEDGER
    LOGBOOK -.->|"records decisions that changed"| COMPLETE

    classDef entry fill:#2d5,stroke:#333,stroke-width:2px
    classDef live fill:#f93,stroke:#333,stroke-width:2px
    class CLAUDE,README entry
    class LEDGER live
```

**Solid arrows** = structural (this document exists because of / is part of that one).
**Dashed arrows** = referential (this document cites or is affected by that one, without
being physically contained in it). The orange node (`open-problems-ledger.md`) is the most
frequently updated document in the whole repo — check there first before starting new work.

## Which document answers which question

| Question | Document |
|---|---|
| "What does this repo claim, at a glance?" | `README.md` |
| "I'm an AI agent, where do I start?" | `CLAUDE.md` |
| "What's the full derivation, branch by branch?" | `SUPPLEMENT.md` §0-11 |
| "Is there already a named open problem for X?" | `supplement/open-problems-ledger.md` |
| "Is the project 'done'? What exactly is missing?" | `supplement/completeness-and-claims.md` §13 |
| "What is this project claiming, and what is it explicitly NOT claiming?" | `supplement/completeness-and-claims.md` §14 |
| "Who owns equation/result X, and when was it published?" | `supplement/references.md` (this repo) + `EQUATION_REGISTRY.md` (canonical, sibling repo) |
| "How did we get here — what worked, what failed, when?" | `LOGBOOK.md` |
| "I want to try to break a specific claim" | `AUDIT_BRIEF.md` |
| "What's the actual theorem-level manuscript?" | `paper/main.tex` |
| "What's the mass-derivation companion argument?" | `paper/mass_note.tex` (do not edit without asking its author) |
| "How do I mechanize a new result and get it into this repo?" | `research_universal_solver`'s own `CLAUDE.md` (sibling private repo — new theorems are born there, synced here after) |

## Standing discipline this map does not override

- Tier discipline (`Th_coqc` / `+reals` / `finite_diagnostic` / `Dr` / `Open`) applies everywhere
  linked above — this map carries no tier itself, it is pure navigation.
- `LOGBOOK.md` is append-only; a stale cross-reference inside an old LOGBOOK entry is
  preserved on purpose, not a map error.
- If a section number cited anywhere (`§12 item 7`, `§13`, etc.) doesn't resolve where you
  expect, check `SUPPLEMENT.md`'s own index first — the split happened 2026-07-06 and old
  citations predating it may say `SUPPLEMENT.md §N` when they now mean one of the three
  `supplement/*.md` files.
