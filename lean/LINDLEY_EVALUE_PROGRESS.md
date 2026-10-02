# LINDLEY_EVALUE_PROGRESS

Date: 2026-09-15. Status: **all four milestones complete, sorry-free** (Milestone 4 included).

## Milestone 1 — Bahadur–Savage, p-value form (`Ols/BahadurSavage.lean`, appended)

- `bahadurSavage_pvalue_pi` (null mean `0`): `bahadurSavage_pi` applied to the indicator test
  `𝟙{P ≤ α}`; `lintegral_indicator_one` turns the test's integral into the rejection probability.
- `bahadurSavage_pvalue_pi'` (general null value `μ₀`): reduction to `μ₀ = 0` by the
  translation `Q ↦ Q.map (· − μ₀)` and the centred test `P'(y) = P(y + μ₀𝟙)`. The product law
  of the shifted law is the shifted product law (`measurePreserving_pi`); the mean shifts by
  `integral_map` + `integral_add`; the round trip `Q' ↦ Q'.map (· + μ₀) = Q` is `Measure.map_map`.
  Note: inside tactic blocks with `import Mathlib` the notation `∫ x, x ∂R` failed to parse
  (`∂R` was read as an application), so the two centred-mean statements are written as
  `integral R (fun x => x)`, which elaborates to the same term.

## Milestone 2 — abstract e-values (`Ols/EValue.lean`)

- `evalue_expectation_eq_one`: `lintegral_withDensity_eq_lintegral_mul` then
  `ENNReal.mul_div_cancel` on the a.e. set `{0 < p₀ < ∞}`. (`hp0_int` is not needed for the
  proof; kept in the specified signature.) Also `isProbabilityMeasure_withDensity`.
- `evalue_markov`: `mul_meas_ge_le_lintegral₀` with `ε = 1/α`, then `ENNReal.mul_inv_cancel`
  (the case `α = ∞` is trivial).
- `posterior_eq`, `evalue_of_posterior` (general `c`; `field_simp`), `posterior_antitone_in_evalue`
  (`one_div_lt_one_div_of_lt`), and `posterior_ge_iff`: `1 − β ≤ 1/(1+κe) ↔ e ≤ β/(κ(1−β))`.

## Milestone 3 — Lindley's paradox (`Ols/Lindley.lean`)

- Definitions `v, g0, g1, pval, post` as specified (parameters `σ μ₀ l c` explicit).
- `gaussianPDFReal_symm`, `g1_nonneg`, `g1_le` (`≤ 1/(2l)` via `gaussianReal_apply_eq_integral`
  and `prob_le_one`), `g0_seq` (`g0 = √n·e^{−λ²/2}/√(2πσ²)` along `yₙ = μ₀ + λσ/√n`),
  `pval_seq` (constant along the sequence).
- `lindley`: `λ` from `tendsto_cdf_atTop` (`Tendsto.eventually_const_lt`), then an **explicit**
  `N = ⌈(A/K)²⌉₊ + 1` with `K = e^{−λ²/2}/√(2πσ²)` and `A = (1−ε)(1−c)/(2lεc)`, so that
  `g0 ≥ A` forces `post ≥ 1 − ε`; no limit argument is needed for `post → 1`.

## Milestone 4 — calibration `P = S₀(E)` (`Ols/Lindley.lean`, section `Calibration`)

- `g1_eq_g0_mul_F`: substituting `μ = μ₀ + u` (`intervalIntegral.integral_comp_add_right`),
  `p₁(y) = p₀(y)·F(y − μ₀)` with `F w l z = (1/2l)∫_{-l}^{l} e^{-u²/(2w)} e^{zu/w} du`.
- `F_eq_cosh`: symmetrising with `intervalIntegral.integral_comp_neg`,
  `F w l z = (1/2l)∫ e^{-u²/(2w)} cosh(zu/w) du`; hence `F_neg` (even) and `F_lt_F`
  (strictly increasing in `|z|`, from `Real.cosh_lt_cosh`/`cosh_le_cosh` and
  `intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt`), so
  `F_le_iff : F z₁ ≤ F z₂ ↔ |z₁| ≤ |z₂|` and `E_ge_iff`.
- `cdf_gaussianReal_neg` (`Φ(−s) = 1 − Φ(s)`, from `gaussianReal_map_neg`), `cdf_gaussianReal_zero`.
- `gaussianReal_abs_ge`: `P_{H₀}(|Ȳ − μ₀| ≥ r) = 2(1 − Φ(r/√v))` by standardising with
  `gaussianReal_map_sub_const`, `gaussianReal_map_div_const`, and the two-sided tail lemmas
  `gaussianTail.measure_le_abs_eq_tail` (`Ols/TTest.lean`) and `gaussTailProb_eq_cdf`
  (`Ols/FiniteN.lean`); `r = 0` handled separately.
- `pval_eq_survival`: assembly (`√v = σ/√n`).

## Verification

- `~/.elan/bin/lake build`: clean; the only `sorry` is the pre-existing Berry–Esseen placeholder.
- `#print axioms` — each of `BahadurSavage.bahadurSavage_pvalue_pi`, `bahadurSavage_pvalue_pi'`,
  `EValue.evalue_expectation_eq_one`, `evalue_markov`, `posterior_eq`, `evalue_of_posterior`,
  `posterior_antitone_in_evalue`, `posterior_ge_iff`, `Lindley.lindley`,
  `Lindley.pval_eq_survival`: `[propext, Classical.choice, Quot.sound]`.
- `Ols.lean` imports `Ols.EValue`, `Ols.Lindley`; both added to the `lakefile.toml` globs.

## Mathlib names that differed from the spec's guesses

- Hoeffding-style lemmas were not needed here; for `withDensity` the non-`₀` lemma
  `lintegral_withDensity_eq_lintegral_mul` sufficed (both functions measurable).
- `ENNReal.div_mul_cancel` → used `ENNReal.mul_div_cancel` (form `a * (b / a) = b`).
- `Ioi_ae_eq_Ici` (not `Ioi_ae_eq_Ici'`) under `NoAtoms`.
- `le_or_lt`/`lt_or_le` are now `le_or_gt`/`lt_or_ge`; `mul_le_mul_left'` is deprecated
  (used `gcongr`).

## Paper alignment layer (`Ols/PaperAligned.lean`, 2026-09-15) — done, sorry-free

Wrappers only; `BahadurSavage.lean`, `EValue.lean`, `Lindley.lean` untouched.

- A. `Distribution`, `Distribution.mean`, `Distribution.prob`, `ValidPValue`, `bahadur_savage`
  (wraps `bahadurSavage_pvalue_pi'`; the `ℝ≥0∞ ↔ ℝ` conversions are
  `ENNReal.le_ofReal_iff_toReal_le` / `ENNReal.toReal_le_of_le_ofReal`, with a local instance
  `IsProbabilityMeasure (prodLaw n Q)`).
- B. `pValue`, `posterior`, `eValue`, `nullProb`, `nullExp`, `IsValidEValue`, `lindley_paradox`,
  `eValue_isValidEValue`, `IsValidEValue.test`, `pValue_eq_survival`, `posterior_eq_eValue`,
  `eValue_equiv_posterior`, `no_paradox`.
- The e-value expectation is done by the real-integral route: `nullExp (eValue) = ∫ g1 = 1` via
  `integral_gaussianReal_eq_integral_smul`, then Fubini (`integrable_prod_iff'`,
  `integral_integral_swap`) and `integral_gaussianPDFReal_eq_one`; measurability of `g1` by
  `StronglyMeasurable.integral_prod_right'`, integrability of `eValue` under the null by
  `integrable_withDensity_iff_integrable_coe_smul`.

Revision (2026-09-15, per the updated `PAPER_ALIGNMENT.md`): `mean Y := (∑ᵢ Yᵢ)/n`;
`pValue σ μ₀ Y := pval σ μ₀ n (mean Y)` and `posterior σ μ₀ l c Y := post … (mean Y)` are now
over the raw sample `Y : Fin n → ℝ`; `lindley_paradox` is `∃ n Y, pValue ≤ ε ∧ posterior ≥ 1−ε`
with no `1 ≤ n` conjunct (witness: the constant sample `fun _ => ybar`, using `mean_const`);
the cross theorems relate `pValue`/`posterior` of `Y` to `eValue … (mean Y)` and keep `1 ≤ n`.
The e-value machinery (`eValue`, `IsValidEValue`, `eValue_isValidEValue`, `IsValidEValue.test`)
stays over the average `ybar`, as specified.

Deviations from the (updated) spec: none beyond what it now states — `ybar` replaces `ȳ`
(U+0233 is not a legal identifier character), `IsValidEValue` carries measurability and
integrability, and `eValue_equiv_posterior`/`no_paradox` take `0 < l` while
`posterior_eq_eValue` is proved by direct algebra without it.

`#print axioms`:
```
'PaperAligned.bahadur_savage' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperAligned.lindley_paradox' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperAligned.eValue_isValidEValue' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperAligned.IsValidEValue.test' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperAligned.pValue_eq_survival' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperAligned.posterior_eq_eValue' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperAligned.eValue_equiv_posterior' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperAligned.no_paradox' depends on axioms: [propext, Classical.choice, Quot.sound]
```
`lake build`: clean (only the pre-existing Berry–Esseen `sorry`). `Ols.PaperAligned` added to
`Ols.lean` and the lakefile globs.
