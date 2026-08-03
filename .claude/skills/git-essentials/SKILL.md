---
name: git-essentials
description: Essential git workflow for causal-quantum-gravity — load before any commit, push, branch, sync-from-sibling, or PR in this repo. Encodes the curated-export rule (theorems are never authored here), the CI-green-on-every-push discipline, the append-only LOGBOOK, and the standard branch/push/PR flow.
---

# Git essentials — causal-quantum-gravity

This repo is a **curated public export** of `research_universal_solver` (private). That fact
drives every git rule below. Load this before committing anything.

## Rule 0 — what may be committed here at all

- **Never author a new theorem (`formal/*.v`) directly in this repo.** New theorems are
  developed and verified in the sibling private repo first (as `formal/Info*_attempt.v`,
  3-stage discipline), then copied here **dropping the `_attempt` suffix** as a separate,
  later sync step. A commit here that introduces a `.v` file with no verified counterpart
  in the sibling is a process violation, not just a style issue.
- **`paper/mass_note.tex` — do not edit without asking.** It is a standalone preprint this
  repo only hosts.
- **`LOGBOOK.md` is append-only.** Never rewrite past entries with hindsight; a fix goes in
  as a *new* dated entry. A diff that modifies an old LOGBOOK entry should not be committed.

## Branching

- Work on a feature branch; never commit to the default branch directly.
- Create/switch: `git checkout -B <branch>` (or `git checkout -B <branch> origin/<default>`
  when restarting from the latest default branch).
- Fetch specific branches: `git fetch origin <branch>` — not a bare `git fetch`.

## Before every commit

1. `make verify` must pass locally — CI (`.github/workflows/verify.yml`) runs it on every
   push and has been green on every commit to date. Do not be the first red commit.
2. Check tier discipline: any claim added/changed in README/SUPPLEMENT must match what the
   underlying `Print Assumptions` actually supports (`Th_coqc` / `+reals` /
   `finite_diagnostic` / `Dr` / `Open`). The single most repeated bug in this project is a
   theorem count or tier claim drifting from what is provable — check counts before
   committing prose.
3. Any new outside-literature equation cited must already be registered in the sibling
   repo's `docs/root/EQUATION_REGISTRY.md`.
4. `git status` + `git diff --staged` review: no stray build artifacts (`.vo`, `.glob`,
   `.aux`), no accidental edits to LOGBOOK history or `mass_note.tex`.

## Commit messages

Clear and descriptive: what changed and at what tier. Example shapes:
`sync: import InfoX.v from solver (Th_coqc, Print Assumptions closed)`,
`docs: fix theorem count in README (drifted from formal/)`,
`logbook: append 2026-08-03 entry on <topic>`.

## Push and PR

- `git push -u origin <branch>`. On network failure only, retry up to 4× with backoff
  (2s, 4s, 8s, 16s).
- After pushing, open a **draft PR** if none is open for the branch. In the PR body, state
  the tier of every claim touched and whether `make verify` was run locally.
- Never force-push a shared branch; `--force-with-lease` only when restarting a designated
  branch from the default branch after its previous PR merged.

## Sync-from-sibling checklist (the one recurring git task here)

1. Confirm the source file passed all 3 stages in `research_universal_solver`.
2. Copy `formal/InfoX_attempt.v` → `formal/InfoX.v` (drop suffix), keep the in-file SCOPE
   block intact.
3. Wire it into the build; run `make verify`.
4. Update README's file-by-file inventory and expected `Print Assumptions` output.
5. Append a LOGBOOK entry; commit as one sync commit; push; draft PR.
