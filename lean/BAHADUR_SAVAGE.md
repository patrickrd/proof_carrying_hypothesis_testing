# Formalisation task: the Bahadur–Savage impossibility theorem (mean version)

**For the VS Code Claude Code agent.** This file is a complete, self-contained
specification. Work in this repository (`~/linear-model-lean-quantitative`, a
home-folder clone that builds cleanly — do NOT move it under `~/Documents`, which is
iCloud-synced and corrupts `.lake`). The target file is `Ols/BahadurSavage.lean`
(a skeleton with `sorry`s already exists). Fill the `sorry`s so the file builds with
no errors and no `sorry`, then report.

## What to prove

Over the class of all probability distributions on `ℝ` with finite mean, no test of
the null "the mean is 0" has power exceeding its size: the data are useless. Formalise
the single-observation case first (Milestone A), then the n-observation case
(Milestone B). Both use the same idea.

### The statistics vocabulary, in Lean terms
- A distribution is `P : MeasureTheory.Measure ℝ` with `[IsProbabilityMeasure P]`.
- "finite mean" is `MeasureTheory.Integrable id P` (equivalently `Integrable (fun x => x) P`).
- "mean of P" is `∫ x, x ∂P` (Bochner integral); "mean 0" is `∫ x, x ∂P = 0`.
- A test is `φ : ℝ → ℝ≥0∞` (Milestone A) or `φ : (Fin n → ℝ) → ℝ≥0∞` (Milestone B),
  `Measurable φ`, with `φ x ≤ 1` everywhere. Using `ℝ≥0∞`-valued tests and the lower
  Lebesgue integral `∫⁻` avoids all Bochner-integrability side conditions in the main
  argument; the mean/null condition is the only place a signed (Bochner) integral appears.
- "level/size ≤ α" for `α : ℝ≥0∞`: `∫⁻ x, φ x ∂Q ≤ α` for every null `Q`.
- "power at P": `∫⁻ x, φ x ∂P`.

### Milestone A — single observation (do this first; it needs no product measure)

Statement to prove (see skeleton for the exact signature):

    theorem bahadurSavage_one
        {α : ℝ≥0∞} {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) (hφ1 : ∀ x, φ x ≤ 1)
        (hsize : ∀ (Q : Measure ℝ), IsProbabilityMeasure Q → Integrable id Q →
                   (∫ x, x ∂Q) = 0 → (∫⁻ x, φ x ∂Q) ≤ α)
        (P : Measure ℝ) [IsProbabilityMeasure P] (hP : Integrable id P) :
        (∫⁻ x, φ x ∂P) ≤ α

Proof steps (each is a small lemma; prove them as `private lemma`s above the theorem):

1. `mix p P a := (ENNReal.ofReal (1 - p)) • P + (ENNReal.ofReal p) • Measure.dirac a`,
   for `p : ℝ`, `0 < p`, `p < 1`, `a : ℝ`.
2. `mix` is a probability measure: total mass `ENNReal.ofReal (1-p) + ENNReal.ofReal p = 1`
   (use `Measure.add_apply`, `Measure.smul_apply`, `measure_univ`, `ENNReal.ofReal_add`,
   and `ofReal (1-p) + ofReal p = ofReal 1 = 1`).  → instance `IsProbabilityMeasure (mix …)`.
3. `id` is integrable w.r.t. `mix` (mixture of an integrable and a Dirac): use
   `Integrable.add_measure` / `integrable_smul_measure` and `integrable_dirac`.
4. mean of `mix`: `∫ x, x ∂(mix p P a) = (1-p) * (∫ x, x ∂P) + p * a`. Use
   `integral_add_measure`, `integral_smul_measure` (gives `.toReal` factors — note
   `(ENNReal.ofReal (1-p)).toReal = 1-p` since `1-p ≥ 0`), and `integral_dirac`.
5. Choose `a := -(1-p) * (∫ x, x ∂P) / p`; then the mean is `0` (field arithmetic, `p ≠ 0`).
   So `mix p P a` satisfies the three hypotheses of `hsize`, giving `∫⁻ φ ∂(mix …) ≤ α`.
6. Domination: `(ENNReal.ofReal (1-p)) • P ≤ mix p P a` (it equals `mix` minus the
   nonneg term `ofReal p • dirac a`; use `Measure.le_add_right` / `le_add_of_nonneg_right`
   at the measure level, i.e. `self_le_add_right`).
7. Monotone integral: `∫⁻ φ ∂((ofReal (1-p)) • P) ≤ ∫⁻ φ ∂(mix p P a)` via `lintegral_mono'`
   (monotone in the measure). LHS `= ENNReal.ofReal (1-p) * ∫⁻ φ ∂P` via `lintegral_smul_measure`.
8. Combine 5+7: `ENNReal.ofReal (1-p) * (∫⁻ φ ∂P) ≤ α` for every `p ∈ (0,1)`.
9. Limit `p → 0⁺`: `ENNReal.ofReal (1-p) → 1`, so `∫⁻ φ ∂P ≤ α`. Formalise with the
   sequence `p = 1/(k+2)`, `k → ∞`: define `X := ∫⁻ φ ∂P`, you have
   `ENNReal.ofReal (1 - 1/(k+2)) * X ≤ α`; the left side tends to `1 * X = X`
   (`ENNReal.Tendsto.mul_const` / `tendsto` of `ofReal (1 - 1/(k+2)) → 1`), so by
   `le_of_tendsto` (with the constant bound `α`) conclude `X ≤ α`. Handle `X` possibly `∞`:
   the inequality forces it finite unless `α = ∞` (then trivial); the tendsto argument works
   in `ℝ≥0∞` directly.

If step 9's ennreal limit is awkward, an equivalent finite route: from step 8,
`X ≤ α / ENNReal.ofReal (1-p)` for all `p`; take `iInf` over `p` and use that
`iInf_{p∈(0,1)} α / ofReal(1-p) = α`.

### Milestone B — n observations

Same statement with sample space `Fin n → ℝ`, product measures `Measure.pi (fun _ => P)`
and `Measure.pi (fun _ => mix …)`, test `φ : (Fin n → ℝ) → ℝ≥0∞`. The only new lemma:

    (ENNReal.ofReal (1-p))^n • (Measure.pi (fun _ => P)) ≤ Measure.pi (fun _ => mix p P a)

Prove by one of:
- If `Measure.pi_mono` (or a monotonicity lemma for `Measure.pi`) exists, combine it with
  the per-coordinate domination `ofReal(1-p) • P ≤ mix` and factor the scalar out with
  a `Measure.pi_smul`-type lemma; OR
- Induction on `n` reducing `Measure.pi` over `Fin (n+1)` to a binary `Measure.prod`
  (`MeasureTheory.measurePreserving_piFinSuccAbove` / `Measure.pi_succ`-style equivalence),
  using `Measure.prod_mono` (verify it exists; if not, prove `prod` monotonicity from
  `Measure.prod_apply` and `lintegral_mono'`), plus `Measure.prod_smul_left`/`prod_smul_right`.
Then repeat steps 7–9 with `(ofReal (1-p))^n` in place of `ofReal (1-p)` (its limit as
`p→0` is still `1`).

### Optional Milestone C (only if A and B are done and building)
The confidence-interval corollary and/or the two-sided / general-convex-class version.
Do NOT start C until A and B build sorry-free.

## Mathlib lemma names to look for (verify each; names drift between versions)
`Measure.add_apply`, `Measure.smul_apply`, `Measure.smul_toOuterMeasure`, `measure_univ`,
`ENNReal.ofReal_add`, `ENNReal.toReal_ofReal`, `integral_add_measure`,
`integral_smul_measure`, `integral_dirac`, `integrable_dirac`, `Integrable.add_measure`,
`lintegral_smul_measure`, `lintegral_mono'`, `lintegral_dirac'`, `self_le_add_right`,
`Measure.prod_smul_left`, `Measure.prod_smul_right`, `Measure.prod_mono`, `Measure.pi`,
`ENNReal.Tendsto.mul_const`, `le_of_tendsto`, `tendsto_const_nhds`.
Use `exact?`, `apply?`, `rw?`, and `#check` / `open ... in example` probes to find the
exact current names. If a lemma is missing, prove it as a `private lemma` rather than
abandoning the route.

## Build, verify, and iterate
- Use `~/.elan/bin/lake` (as the repo's CLAUDE.md specifies), not a bare `lake`.
- Build just this file while iterating: `~/.elan/bin/lake build Ols.BahadurSavage`.
- Build the whole project: `~/.elan/bin/lake build` (a few minutes; the Mathlib cache is
  present — do not run `lake exe cache get` unless a build reports missing `.olean`s).
- Add `import Ols.BahadurSavage` to `Ols.lean` so the file is part of the default build.
- Success criterion: `~/.elan/bin/lake build Ols.BahadurSavage` exits 0 with no `sorry`
  and no `error`. Then run `~/.elan/bin/lake build` to confirm nothing else broke.
- Check axioms at the end: add `#print axioms BahadurSavage.bahadurSavage_one` (and `…_pi`)
  and confirm only `propext, Classical.choice, Quot.sound` (no `sorryAx`).
- Respect the repo's linters (see `lakefile.toml`): no lines over the length limit,
  `·` for `cdot`, no `$`, provide file header, etc. If a linter blocks the build, fix it.

## Working protocol (autonomous)
Follow the repo's existing "Autonomy contract" in `CLAUDE.md`. In brief:
- Do NOT ask the user for permission or direction; all needed actions (reading, editing,
  `~/.elan/bin/lake build`, `git add`/`commit`/`status`/`diff`/`log`) are pre-approved in
  `.claude/settings.local.json`. Keep going until the success criterion is met.
- Commit locally after each lemma builds: `git add -A && git commit` with a message naming
  the lemma. Small frequent commits are the checkpoint trail. Local commits are always safe.
- **NEVER `git push`** to any remote, under any circumstance. This is the one hard rule.
- If a step is blocked after several genuine attempts, do NOT stop the whole task: leave
  that one piece as a clearly-commented `sorry`, record what you tried and why it is stuck
  in `BAHADUR_SAVAGE_PROGRESS.md`, and move on to the next independent piece.
- Record progress after each milestone in `BAHADUR_SAVAGE_PROGRESS.md`: what builds, what
  is sorried and why, and the `#print axioms` output.
- When A and B build sorry-free, stop and summarise in `BAHADUR_SAVAGE_PROGRESS.md`.
