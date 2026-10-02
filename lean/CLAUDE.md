# Repository and working instructions

This is an experimental Lean 4 fork of the public linear-model-in-Lean project (a snapshot of `lean-statistics/linear-model-lean`), branch `quantitative`. It formalises finite-sample inference for the OLS contrast. Toolchain `leanprover/lean4:v4.30.0-rc2`; Mathlib is vendored under `.lake/packages/`.

Build with `~/.elan/bin/lake build` (the Mathlib cache is already present; do **not** run `lake exe cache get` unless a build reports missing `.olean`s). A full build takes a few minutes; prefer targeting a single library file, e.g. `~/.elan/bin/lake build Ols.FiniteN`.

## Current task

Read `CALIBRATION.md` in full first, then fill the `sorry`s in `Ols/Calibration.lean`
(Milestones A–B: the tail bound `calibrator_tail_le` and the headline `calibrate_pvalue`,
the Vovk–Wang p-to-e calibration at κ = 1/2; Milestone C only if time remains). Success =
`~/.elan/bin/lake build` clean with exactly one `sorry` warning (the pre-existing Berry–Esseen
placeholder), `#print axioms EValue.calibrate_pvalue` showing only the three standard axioms,
and `CALIBRATION_PROGRESS.md` telling the story. Commit locally after each milestone; never push.

Previous task, DONE 2026-09-23: `PROTOCOL.md` Milestones A–G (see `PROTOCOL_PROGRESS.md`).
Its Milestones H (Monte Carlo candidate certification) and I (the same calibration, now
superseded by `CALIBRATION.md`) are optional and not needed for the paper.

## Other available tasks
- Bounded-error route (`BOUNDED_ERROR.md`), two-point route (`TWO_POINT.md` Milestones A–C),
  Cantelli route (`CANTELLI.md`), Lindley/e-values (`LINDLEY_EVALUE.md`), paper alignment
  (`PAPER_ALIGNMENT.md`): all DONE; see the matching `*_PROGRESS.md` files.
- Bahadur–Savage impossibility: `BAHADUR_SAVAGE.md`, skeleton `Ols/BahadurSavage.lean`
  (may already be in progress; check `BAHADUR_SAVAGE_PROGRESS.md`).
- `FINITE_N_IMPLEMENTATION.md` is complete — see `PROGRESS.md`.

## Autonomy contract — read carefully

You are expected to work for a long time without check-ins. Follow these rules so you never need to stop for permission:

1. **Proceed without asking.** Every action needed for the task — reading files, editing `Ols/FiniteN.lean`, `Ols.lean`, `lakefile.toml`, running `lake build`, running `git add`/`git commit`/`git status`/`git diff`/`git log` — is pre-authorised. Do them; do not ask.

2. **Commit locally after each lemma builds.** When a lemma from the spec compiles cleanly, `git add -A && git commit` with a message naming the lemma. Small frequent commits are the checkpoint trail. Committing is local and always safe here.

3. **NEVER push.** Do not run `git push` to any remote under any circumstance. The push URL of `origin` is deliberately disabled and must stay so. Publishing is the user's decision alone. (This is the one hard rule; everything else is latitude.)

4. **When stuck, stage a `sorry` and move on — do not block.** If a lemma resists after a genuine effort (say ~30 minutes / several approaches), insert a clearly marked `sorry` with a `-- TODO(finite-n): <what is blocking, what you tried>` comment, append a dated line to `PROGRESS.md` (create it) describing the blocker, and continue to the next lemma. A later lemma may temporarily depend on an earlier `sorry`; that is fine mid-run. The **final** state must have no `sorry` except the pre-existing BE black box in `Clt/BerryEsseen.lean` — so return to the staged ones before declaring done. Never delete or weaken a theorem statement to make it pass; a `sorry` with a note is honest, a hollowed statement is not.

5. **Keep a running log.** Maintain `PROGRESS.md`: one dated line per lemma attempted with status (done / staged-sorry / blocked-why), and any deviations from the spec with the reason. This is how the user picks up asynchronously.

6. **Do not touch the public surface.** Leave every existing theorem statement and the single existing `sorry` unchanged. New work lives in `Ols/FiniteN.lean`. If the spec seems to require changing an existing statement, that is a signal to stop and log it in `PROGRESS.md`, then continue with what you can.

7. **No axioms, no `native_decide`, no `admit`.** Correctness is the point. If you cannot prove it honestly, stage a `sorry` (rule 4) rather than reaching for an escape hatch. Verify headline theorems with `#print axioms`.

8. **Verify behaviour, not just types.** After the main theorem builds, sanity-check the bound is non-vacuous where it should be and reduces as expected (e.g. `η → 0`, `θ → 1−2h_max`), via `#eval`/`example`s on a toy instance, and note the check in `PROGRESS.md`.

## What success looks like

`lake build` clean with exactly one `sorry` warning; theorems 8 and 9 of the spec proved; `Ols.lean` and `lakefile.toml` updated; `PROGRESS.md` and local commits telling the story. Then stop and summarise in `PROGRESS.md` — do not push, do not open anything external.
