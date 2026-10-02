# CANTELLI_PROGRESS — `section Cantelli` in `Ols/FiniteN.lean`

Date: 2026-09-19. Status: **Milestones A–H complete, sorry-free.** The Chebyshev route
(`hcVplus`, `variance_event_le`, `finiteN_tail_oneSided` and corollaries) is untouched; the new
section is additive and lives at the END of the file (after `section Bridge`), because it reuses
`sum_hcM_abs_hcU_le` from `section AuxiliaryBounds`, which comes after `MainTheorems`.
`set_option linter.style.longFile` raised to 2200.

## Definitions
`cantelliC`, `aMinus`, `cantelliV0`, `cantelliS`, `cantelliQBar`, `cantelliVarianceEventBound`
exactly as specified (`g` a parameter with `hg : ∀ i, hcWeight X d a i ≤ g`).

## Milestones
- A `measureReal_le_cantelli` (no Cantelli in Mathlib; proved): reduction to `V = Var W`
  (`div_add_le_div_add`), degenerate case via `measureReal_le_of_variance_le`, otherwise Markov
  (`mul_meas_ge_le_integral_of_nonneg`) for `Y² = (b + EW − W)²`, `b = Var/(m−c)`, with
  `E Y = b`, `Var Y = Var W` (`variance_const_sub`), `E Y² = b² + Var W` (`variance_eq_sub`),
  then `field_simp`.
- B `FiniteSampleBundle.integral_hcVar_sub_ge` (from the exact mean `integral_hcVar`; termwise
  with `hvar_lb`/`hvar_ub`, `mul_le_mul_of_nonpos_left` for the negative branch).
- C `normSq_hcU_le_gmax`, `sqrt_normSq_hcU_le_gmax` (`‖u‖² ≤ g ρ²`; takes
  `hX_inv : IsUnit (Xᵀ * X).det` for the contraction step, supplied by `A.hX_inv` upstream).
- D `FiniteSampleBundle.variance_hcVar_le_cantelli` (takes `hκ : 1 ≤ A.κ` and `hB₃ : 0 ≤ A.B₃`,
  both derived in F from `0 < n`; helper `FiniteSampleBundle.B₃_nonneg`).
- E `cantelli_e1/e2/e3` (private), stated in the multiplied-out form
  `V0 ≤ V0/am²·(x+am)²`, `4x ≤ (1/am)(x+am)²`, `4√x ≤ ((3√3/4)/am^{3/2})(x+am)²`; `e3` via
  `am = 3b²`, `am^{3/2} = 3√3 b³` (`Real.rpow_add`, `Real.sqrt_eq_rpow`) and
  `(s²+3b²)² − 16sb³ = (s−b)²(s²+2sb+9b²)`.
- F `FiniteSampleBundle.cantelli_variance_event_le`: `Var ν̂ ≤ q̄(ρ²+a₋)² ≤ q̄·gap²`, Cantelli,
  cancel `gap² > 0` (`mul_div_mul_right`). Hypotheses exactly as specified (no `θ ≤ 1`, no
  leverage condition, no `hres`; `hθ0` is unused by the proof but kept).
- G `finiteN_tail_oneSided_cantelli`, `finiteN_tail_lower_cantelli`,
  `finiteN_tail_twoSided_cantelli`. The two-sided bound is stated honestly as
  `2(1 − Φ(t√θ)) + η(t√θ) + η(−t√θ) + q̄/(1+q̄)` (the lower tail carries `η(−t√θ)`, as in the
  existing file); `finiteN_tail_twoSided_cantelli'` gives the spec's `2η(t√θ)` form under
  `η(−t√θ) ≤ η(t√θ)`. `gaussianReal_cdf_neg` (`Φ(−s) = 1 − Φ(s)`) added here for the
  Gaussian symmetry.
- H `hcWeight_mul_sq_le_hcM_diag`, `one_le_hc3`, `FiniteSampleBundle.aMinus_pos_hc3`
  (`hθ0` unused by the proof but kept).

## Sanity checks (in-file `example`s, `section SanityCheck`)
Intercept-only design `X4` (4×1), `a = ![1]`, HC0, `θ = 1/2`, `s_min = s_max = 1`, `κ = 3`:
`olsWeights = 1/4`, `leverage = 1/4`, `Q_ii = 3/64`, `Q_ij = −1/64`, `cantelliC = 1/64`,
`aMinus = 1/16`, `cantelliV0 = 3/128` — all closed by `simp`/`norm_num`, matching the spec.

## Verification
- `~/.elan/bin/lake build`: clean; only the pre-existing Berry–Esseen `sorry`.
- `#print axioms`:
```
'measureReal_le_cantelli' depends on axioms: [propext, Classical.choice, Quot.sound]
'FiniteSampleBundle.cantelli_variance_event_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'finiteN_tail_oneSided_cantelli' depends on axioms: [propext, Classical.choice, Quot.sound]
'finiteN_tail_lower_cantelli' depends on axioms: [propext, Classical.choice, Quot.sound]
'finiteN_tail_twoSided_cantelli' depends on axioms: [propext, Classical.choice, Quot.sound]
'FiniteSampleBundle.aMinus_pos_hc3' depends on axioms: [propext, Classical.choice, Quot.sound]
'finiteN_tail_oneSided' depends on axioms: [propext, Classical.choice, Quot.sound]
'finiteN_tail_twoSided' depends on axioms: [propext, Classical.choice, Quot.sound]
```
- Cross-validation against `cantelli_bounds.R` was not possible from this repo (the R script and
  CSV live in the report repo); the definitions follow the spec's formulas literally.
