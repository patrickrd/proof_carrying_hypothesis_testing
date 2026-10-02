# Formalisation task: p-to-e calibration (`calibrate_pvalue`)

**For the VS Code Claude Code agent.** Self-contained specification. Work in this repo
(`~/linear-model-lean-quantitative`, branch `quantitative`, toolchain `leanprover/lean4:v4.30.0-rc2`,
Mathlib vendored under `.lake/packages/`; build with `~/.elan/bin/lake build Ols.Calibration`,
do NOT run `lake exe cache get` unless `.olean`s are reported missing). Target file:
`Ols/Calibration.lean` (a skeleton with `sorry`s exists and is already registered in `Ols.lean`
and `lakefile.toml`). Fill the `sorry`s so the file builds with no errors and no `sorry`, run
`#print axioms` on the headline theorems, record everything in `CALIBRATION_PROGRESS.md`, commit
locally after each lemma. Never push. The autonomy contract in `CLAUDE.md` applies.

## What this is, and why it is worth doing

The ICLR paper converts every p-value in its Figure 2 into an e-value with the Vovk–Wang
calibrator at κ = 1/2,

    e = 1 / (2 √p),

and its Table 1 names the theorem `calibrate_pvalue` as the machine-checked justification. The
theorem does not exist yet, here or anywhere else (Mathlib, statlib, Degenne–Serré's e-values
repository: checked 24 Sep 2026). The mathematics is one paragraph; the proof is the layer-cake
formula plus one elementary integral. This is the **only** formalisation the paper claims and
does not have, so when this file is sorry-free every Lean name in the paper exists.

The direction e → p (`IsEVariable.markov`, `PaperAligned.IsValidEValue.test`) is already here.
This task is the direction p → e.

## The mathematics (one paragraph)

Let `p : Ω → ℝ` be a *p-variable* for a probability measure `P`: measurable, `0 ≤ p`, and
`P(p ≤ α) ≤ α` for every `α ∈ [0,1]`. Put `e ω = 1 / (2 √(p ω))`. Then `e ≥ 0` and, for every
`t > 0`, `{e > t} = {p < 1/(4t²)}` (on `p > 0`; see the edge case below), so
`P(e > t) ≤ min(1, 1/(4t²))`. By the layer-cake formula
`∫ e dP = ∫₀^∞ P(e > t) dt ≤ ∫₀^{1/2} 1 dt + ∫_{1/2}^∞ (4t²)⁻¹ dt = 1/2 + 1/2 = 1.`
The same bound shows `e` is integrable. Hence `e` is an e-variable: `IsEVariable P e` in the
sense of `Ols/EValueAlgebra.lean`.

## Definitions (already in the skeleton — keep them)

```lean
namespace EValue

/-- A p-variable for `P`: `P(p ≤ α) ≤ α` for every `α ∈ [0,1]`. -/
structure IsPVariable (P : Measure Ω) (p : Ω → ℝ) : Prop where
  measurable : Measurable p
  nonneg : ∀ ω, 0 ≤ p ω
  valid : ∀ α : ℝ, 0 ≤ α → α ≤ 1 → P.real {ω | p ω ≤ α} ≤ α

/-- The Vovk–Wang calibrator at κ = 1/2. Note `1 / (2 * √0) = 0` in Lean (division by zero),
so `calibrator 0 = 0`; see the edge case. -/
noncomputable def calibrator (x : ℝ) : ℝ := 1 / (2 * Real.sqrt x)
```

## Milestone A — the tail bound (`calibrator_tail_le`)

Target:

```lean
theorem calibrator_tail_le [IsProbabilityMeasure P] {p : Ω → ℝ} (hp : IsPVariable P p)
    {t : ℝ} (ht : 0 < t) :
    P.real {ω | t < calibrator (p ω)} ≤ min 1 (1 / (4 * t ^ 2))
```

Proof steps:
1. `P.real _ ≤ 1` always (`measureReal_le_one` or `prob_le_one`), giving the `1` branch.
2. For the other branch show the set inclusion
   `{ω | t < calibrator (p ω)} ⊆ {ω | p ω ≤ 1 / (4 * t ^ 2)}`. Take `ω` with
   `t < 1 / (2 √(p ω))`. If `p ω = 0` the calibrator is `0` (Lean's `1/0 = 0`) so `t < 0`,
   contradiction with `ht`; hence `p ω > 0`, `√(p ω) > 0`, and `t < 1/(2√p)` gives
   `2 t √p < 1`, i.e. `√p < 1/(2t)`, i.e. `p < 1/(4t²)` (square both sides, `Real.sqrt_lt'`
   or `Real.sqrt_lt_sqrt` / `Real.sq_sqrt`). Useful: `Real.sqrt_pos`, `Real.sq_sqrt`,
   `Real.sqrt_lt' (hx : 0 < y) : √x < y ↔ x < y ^ 2`, `div_lt_iff`, `lt_div_iff`.
3. If `1/(4t²) ≤ 1` apply `hp.valid` at `α = 1/(4t²)` (with `0 ≤ α`), then `measureReal_mono`
   on the inclusion. If `1/(4t²) > 1` the `min` is `1` and step 1 applies. Combine with
   `le_min` after a case split `min_eq_left/right` or prove both `≤ 1` and `≤ 1/(4t²)` where
   the latter needs the case `1/(4t²) ≤ 1`; simplest: `le_min` with the second bound proved
   by cases on `1/(4t²) ≤ 1`.
4. Measurability of the set: `hp.measurable` composed with `calibrator` (`measurable_sqrt`,
   `Measurable.div`, `Measurable.const_mul`); `measurableSet_lt`.

Estimate: 40–80 lines.

## Milestone B — integrability and the expectation bound (`calibrate_pvalue`)

Target (the headline; this exact name is cited in the paper):

```lean
theorem calibrate_pvalue [IsProbabilityMeasure P] {p : Ω → ℝ} (hp : IsPVariable P p) :
    IsEVariable P (fun ω => calibrator (p ω))
```

`IsEVariable` (in `Ols/EValueAlgebra.lean`) has three fields: `nonneg`, `integrable`,
`expect_le_one`. Proof plan:

1. `nonneg`: `calibrator x ≥ 0` for `x ≥ 0` (`div_nonneg`, `Real.sqrt_nonneg`); for `x = 0`
   it is `0`.
2. The key integral. Work in `ℝ≥0∞` first. By the layer-cake formula
   `MeasureTheory.lintegral_eq_lintegral_meas_lt`
   (`Mathlib/MeasureTheory/Integral/Layercake.lean`, statement:
   `∫⁻ ω, ENNReal.ofReal (f ω) ∂μ = ∫⁻ t in Ioi 0, μ {a | t < f a}` for `f` a.e. nonnegative
   and a.e.-measurable),
   `∫⁻ ω, ofReal (calibrator (p ω)) ∂P = ∫⁻ t in Ioi 0, P {ω | t < calibrator (p ω)}`.
   Bound the integrand pointwise on `Ioi 0` by `ENNReal.ofReal (min 1 (1/(4t²)))` using
   Milestone A (`measureReal_eq_toReal`/`ENNReal.ofReal_toReal` to move between `P.real` and
   `P`; `P {…} ≠ ⊤` since `P` is finite), then `lintegral_mono` (or `setLIntegral_mono`).
3. Evaluate `∫⁻ t in Ioi 0, ofReal (min 1 (1/(4t²))) = 1`. Split `Ioi 0 = Ioc 0 (1/2) ∪ Ioi (1/2)`
   (`lintegral_union` with `measurableSet_Ioc`, `measurableSet_Ioi`, disjointness
   `Set.Ioc_disjoint_Ioi_same` or `Ioc_union_Ioi_eq_Ioi`). On `Ioc 0 (1/2)` the min is `1`
   (since `4t² ≤ 1`), integral `= volume (Ioc 0 (1/2)) = 1/2` (`Real.volume_Ioc`). On
   `Ioi (1/2)` the min is `1/(4t²)`; convert to a real integral
   (`ofReal_integral_eq_lintegral_ofReal` needs integrability and nonnegativity) and use
   `integral_Ioi_rpow_of_lt (a := -2) (hc : 0 < 1/2)`:
   `∫ t in Ioi (1/2), t ^ (-2:ℝ) = -(1/2) ^ (-2 + 1) / (-2 + 1) = 2`, so
   `∫ t in Ioi (1/2), 1/(4t²) = (1/4) * 2 = 1/2`. Integrability from
   `integrableOn_Ioi_rpow_of_lt`. Rewrite `1/(4*t^2) = (1/4) * t ^ (-2:ℝ)` for `t > 0`
   (`Real.rpow_neg`, `Real.rpow_natCast` / `Real.rpow_two`, `inv_eq_one_div`).
   You may prefer to prove `≤ 1` rather than `= 1`; only `≤` is needed. Either way this step
   is the bulk of the work.
4. `integrable`: from step 2–3 the lintegral of `ofReal ∘ e` is `≤ 1 < ⊤`, and `e` is
   nonnegative and measurable, so `Integrable e P` by `integrable_of_lintegral_lt_top`-type
   lemmas (`MemLp`/`Integrable.of_lintegral…`; search with `exact?`:
   `(hasFiniteIntegral_iff_ofReal h_nn).2`, `Integrable.mk`, `AEStronglyMeasurable` from
   measurability).
5. `expect_le_one`: `∫ ω, e ω ∂P = (∫⁻ ω, ofReal (e ω) ∂P).toReal`
   (`integral_eq_lintegral_of_nonneg_ae`) `≤ (1 : ℝ≥0∞).toReal = 1` (`ENNReal.toReal_mono`).

Estimate: 150–250 lines. No hard mathematics; the work is coercions between `ℝ`, `ℝ≥0∞`,
`P.real` and `P`, and the improper integral.

## Milestone C — the general decreasing calibrator (OPTIONAL, only if A–B are done and time remains)

Vovk–Wang Proposition 2.1: any decreasing `f : [0,1] → [0,∞]` with `∫₀¹ f ≤ 1` calibrates.
Statement sketch: `(hf : AntitoneOn f (Icc 0 1)) (hf_int : ∫ x in Ioc 0 1, f x ≤ 1)
(hf_nn : ∀ x, 0 ≤ f x) → IsEVariable P (fun ω => f (p ω))` for `p` a p-variable with values
in `[0,1]`. Proof: layer cake again, `{f ∘ p > t} ⊆ {p < f⁻(t)}` with a generalised inverse
`f⁻(t) = sup {x ∈ [0,1] | f x > t}`, then `∫₀^∞ f⁻(t) dt = ∫₀¹ f` (the area under a decreasing
function counted the other way). This is genuinely fiddlier (generalised inverses, null sets);
do not start it unless A–B are committed and building.

## Edge cases and decisions

- **`p ω = 0`.** Lean's `1 / (2 * √0) = 0`, so the calibrator is `0` there instead of `+∞`.
  This only makes `e` smaller, so validity is unaffected and the theorem is true as stated.
  Do NOT add a hypothesis `0 < p ω`; the paper's p-values are positive but the theorem should
  not need it. Mention the convention in the docstring.
- **`p ω > 1`.** Allowed by `IsPVariable` (nothing constrains `p` above `1`); the calibrator is
  then `< 1/2` and the bound still holds. No hypothesis needed.
- Work with `P.real` (as `IsEVariable` and `IsPVariable` do) in statements; convert to
  `ℝ≥0∞` inside proofs where the layer-cake lemma lives.
- Keep `calibrator` as a plain function of `ℝ` so it can be reused for the e-value ceiling
  computations later.

## Deliverables

1. `Ols/Calibration.lean` building with no `sorry`; `calibrator_tail_le` and `calibrate_pvalue`
   proved; Milestone C only if reached.
2. `CALIBRATION_PROGRESS.md`: one dated line per lemma (done / staged-sorry / blocked-why), any
   deviation from the statements above with the reason, and the output of
   `#print axioms EValue.calibrate_pvalue` (expected `[propext, Classical.choice, Quot.sound]`).
3. Full `~/.elan/bin/lake build` clean with exactly one `sorry` warning (the pre-existing
   `Clt/BerryEsseen.lean:55`).
4. Local commits after each milestone. No push.

## Sanity check to include at the end of the file

```lean
example [IsProbabilityMeasure P] {p : Ω → ℝ} (hp : IsPVariable P p) (α : ℝ) (hα : 0 < α) :
    P.real {ω | 1 / α ≤ calibrator (p ω)} ≤ α :=
  (calibrate_pvalue hp).markov _ hα
```
(the calibrated e-value's Markov test; if `IsEVariable.markov` has a different argument order,
adapt).
