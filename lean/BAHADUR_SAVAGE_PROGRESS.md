# BAHADUR_SAVAGE_PROGRESS — `Ols/BahadurSavage.lean`

Date: 2026-09-11. Status: **Milestones A and B complete, sorry-free.** Milestone C not started
(optional; instructions say to stop after A and B).

## Milestone A — single observation (done)

- `mix_isProbabilityMeasure` — total mass `ofReal (1-p) + ofReal p = ofReal 1 = 1`.
- `mix_isFiniteMeasure` (extra) — the mixture is finite for *every* real `p`; used so that
  `smul_pow_le_prod_mix` can be stated without sign conditions on `p`, as in the skeleton.
- `integrable_id_mix` — `Integrable.add_measure`, `Integrable.smul_measure`, `integrable_dirac`.
- `integral_id_mix` — `integral_add_measure`, `integral_smul_measure`, `integral_dirac`,
  `ENNReal.toReal_ofReal`.
- `integral_id_mix_contam` — `field_simp; ring`.
- `smul_le_mix` — `Measure.le_add_right le_rfl`.
- `scaled_lintegral_le` (private) — steps 5–8 of the plan: `ofReal (1-p) * ∫⁻ φ ∂P ≤ α`.
- `tendsto_ofReal_one_sub`, `le_of_scaled_le` (private) — step 9, done on the filter
  `𝓝[>] 0` directly (no sequence): `ENNReal.tendsto_ofReal`, `ENNReal.Tendsto.mul_const`,
  `le_of_tendsto` with `Ioo_mem_nhdsGT`.
- `bahadurSavage_one` — one line from the two private lemmas.

## Milestone B — n observations (done)

Mathlib has no monotonicity lemma for `Measure.pi`, so the domination is proved in integral
form first:

- `pow_mul_lintegral_le` (private): for every measurable `f`,
  `(ofReal (1-p))^n * ∫⁻ f ∂Pⁿ ≤ ∫⁻ f ∂(mix)ⁿ`. Induction on `n`; base case `Measure.pi_of_empty`;
  step: `measurePreserving_piFinSuccAbove` (coordinate `0`) transfers both integrals to the binary
  product `P.prod Pⁿ`, Tonelli (`lintegral_prod`) reduces to iterated integrals, the inner one is
  bounded by the induction hypothesis (`gcongr` + `Measurable.lintegral_prod_right'` for
  measurability), and the outer one uses `lintegral_smul_measure` and `lintegral_mono'` with
  `smul_le_mix`.
- `smul_pow_le_prod_mix` — the skeleton's measure inequality, from the integral form applied to
  indicators (`Measure.le_iff`, `lintegral_indicator_one`).
- `prodLaw_sigmaFinite` (extra instance) so that `Measure.pi`/`prod` lemmas fire through the
  `prodLaw` wrapper.
- `tendsto_ofReal_one_sub_pow` (private) — `ENNReal.continuous_pow`.
- `bahadurSavage_pi` — `le_of_scaled_le` again, with `pow_mul_lintegral_le` applied to `φ`.

## Verification

- `~/.elan/bin/lake build Ols.BahadurSavage`: exit 0, no `sorry`, no `error`.
- `~/.elan/bin/lake build` (whole project): clean; the only `sorry` warning is the pre-existing
  Berry–Esseen placeholder (`Clt/BerryEsseen.lean:55`).
- `#print axioms`:
  - `BahadurSavage.bahadurSavage_one` : `[propext, Classical.choice, Quot.sound]`
  - `BahadurSavage.bahadurSavage_pi` : `[propext, Classical.choice, Quot.sound]`
  - `BahadurSavage.smul_pow_le_prod_mix` : `[propext, Classical.choice, Quot.sound]`
- Linters: clean (the unused hypotheses `hφ`, `hφ1`, `hp0`, `hp1` in the skeleton's fixed
  signatures are silenced with `set_option linter.unusedVariables false in` on those three
  declarations rather than by changing the specified statements).
- `lakefile.toml`: `Ols.BahadurSavage` added to the `Ols` globs; `Ols.lean` already imported it.

## Deviations from the plan

- Step 9 uses the filter `𝓝[>] 0` instead of the sequence `1/(k+2)` (shorter, no casts).
- Milestone B uses the induction/Tonelli route (the `Measure.pi_mono` route is unavailable).
- Nothing sorried; nothing pushed.
