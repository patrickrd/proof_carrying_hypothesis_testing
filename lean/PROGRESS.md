# PROGRESS — finite-n Berry–Esseen + variance-estimation route (`Ols/FiniteN.lean`)

All dates 2026-09-10. Status legend: done / staged-sorry / blocked.

## Lemma log (spec numbering from `FINITE_N_IMPLEMENTATION.md`)

- 2026-09-10 — groundwork: `IndepCentred4` (independent centred family, 4th moments); mixed
  moments `integral_mul`, `integral_mul3`, `integral_mul4` by regrouping monomials as
  `∏ₘ εₘ^{cₘ}` and factorising by independence (`integral_prod_pow`). done.
- 2026-09-10 — Lemma 4 groundwork: `IndepCentred4.variance_linQuad` — exact variance of
  `c₀ + 2∑uᵢεᵢ + ∑Mᵢⱼεᵢεⱼ` via Mathlib covariance bilinearity (`variance_fun_sum`,
  `covariance_fun_sum_fun_sum`) and the closed-form kernel `quadCov`. done.
- 2026-09-10 — OLS layer: `contrastVar` (ν), `contrastStat` (Z), `hcVar` (ν̂), `hcStudent` (T),
  `hcM`, `hcU`, `hcRho`, `hcVplus` (V₊), `FiniteSampleBundle` (A1–A2);
  `hcVar_eq_linQuad` (`ν̂ = ρ_d² + 2uᵀε + εᵀMε`, from `sampleResidual_decomp`). done.
- 2026-09-10 — Lemma 3: `FiniteSampleBundle.integral_hcVar` (exact mean) and
  `FiniteSampleBundle.integral_hcVar_ge` (`E ν̂ ≥ (1−2h_max)ν + ρ_d²`, under `2h_max ≤ 1`,
  `dᵢ ≥ 1`). done.
- 2026-09-10 — Lemma 4: `FiniteSampleBundle.variance_hcVar`. done.
- 2026-09-10 — Corollary 5: `FiniteSampleBundle.variance_hcVar_le` (`Var ν̂ ≤ V₊`), plus
  `FiniteSampleBundle.normSq_hcU_le` (`‖u‖² ≤ C_r²∑dᵢ²γᵢ⁴`) and `sum_hcM_abs_hcU_le`
  (`∑Mᵢᵢ|uᵢ| ≤ √(∑Mᵢᵢ²)‖u‖`). `κ̄ ≥ 1` is derived (`FiniteSampleBundle.one_le_κ`), not assumed. done.
- 2026-09-10 — Lemma 1: `tail_upper_of_cdf`, `tail_lower_of_cdf`. done.
- 2026-09-10 — Lemma 2: `studentised_subset`, `studentised_tail_le`. done (see deviation 1).
- 2026-09-10 — Lemma 6: `measureReal_le_of_variance_le` (generic Chebyshev form) and
  `FiniteSampleBundle.variance_event_le`. done.
- 2026-09-10 — Lemma 7: `gaussianReal_real_Ioc_le`, `gaussian_tail_shift`,
  `gaussian_tail_shift_lower`. done.
- 2026-09-10 — Theorem 8: `finiteN_tail_oneSided`. done, `#print axioms` = propext,
  Classical.choice, Quot.sound only.
- 2026-09-10 — Corollary 9: `finiteN_tail_lower`, `finiteN_union_bound`, `finiteN_tail_twoSided`,
  `finiteN_pvalue_oneSided`, `finiteN_pvalue_twoSided`, `finiteN_ci`. done, all sorry-free.
- 2026-09-10 — Item 10: `FiniteSampleBundle.cdf_bound_BE30`, `finiteN_tail_oneSided_BE30`
  (η ≡ 30·ϱₙ). done; inherits `sorryAx` from the BE placeholder only.
- 2026-09-10 — extra: `hcStudentized_eq_hcStudent` (T is the existing `hcStudentized` statistic of
  `Ols/TTest.lean`, for `n > 0`), `finiteN_tail_oneSided_hcStudentized`. done.

## Deviations from the spec (with reasons)

1. Lemma 2 is proved directly (`studentised_subset`, ~25 lines) instead of wrapping
   `slutsky_per_n_bound_oneSided`: the existing lemma bounds the *two-sided* event
   `{z < |c_ω Z|}` by `{z/(c+ε) < |Z|}`; wrapping it would replace the one-sided Gaussian tail
   `1 − Φ` by the two-sided one and Theorem 8 would not be the stated bound. No existing
   statement was changed.
2. Corollary 9 (lower tail) is proved by mirroring the argument, not by "applying Theorem 8 to
   −a": A3 for `−Z` at `z` is `|P(Z ≥ −z) − Φ(z)|`, which is not implied by A3 for `Z` when `Z`
   has atoms. The honest lower-tail bound uses `η(−t√θ)`; the two-sided bound therefore carries
   `η(t√θ) + η(−t√θ)` (equal to `2η(t√θ)` for the constant BE instance).
3. The p-value corollaries bound the rejection event `{p(T) ≤ p(t₀)}` by the tail bound at any
   `t ∈ (0, t₀)`, i.e. `P{p(T) ≤ α} ≤ bound(t)` for all `0 < t < t₀`. The strict slack is
   forced by the same atom issue (the event is `{t₀ ≤ T}`, the tail bound is for `{t < T}`), and
   `η` need not be continuous, so the `t → t₀` limit of `pvalue_conservative` is not available.
4. A2 records `0 < s_min` explicitly (needed for `ν > 0`), and A1's `E|ε|³ < ∞` is implied by the
   `L⁴` hypothesis, so it is not a separate field. Multipliers `d` with `dᵢ ≥ 1` are theorem
   hypotheses rather than a bundle field.
5. Lemma 3's lower bound needs `2h_max ≤ 1` (otherwise `(1−2h_max)wᵢ ≥ (1−2h_max)γᵢ²` fails);
   this is implied by Theorem 8's `θ < 1 − 2h_max`, `θ > 0`.
6. `set_option linter.style.longFile 1700` in `Ols/FiniteN.lean` (the file is ~1620 lines; the
   spec asks for a single file).

## Verification

- `lake build`: clean, exactly one `sorry` warning (`Clt/BerryEsseen.lean:55`, pre-existing).
- `#print axioms`: `finiteN_tail_oneSided`, `finiteN_tail_lower`, `finiteN_tail_twoSided`,
  `finiteN_pvalue_oneSided`, `finiteN_pvalue_twoSided`, `finiteN_ci`,
  `IndepCentred4.variance_linQuad`, `FiniteSampleBundle.variance_hcVar_le` — `[propext,
  Classical.choice, Quot.sound]`. `finiteN_tail_oneSided_BE30` additionally `sorryAx`.
- Behaviour check (CLAUDE.md rule 8). Structural, in Lean: `shiftError_one` (`θ = 1` kills the
  shift term), `shiftError_zero` (`η ≡ 0` leaves only the shift term). Numerical (pure-Python
  script, cars-like design `x ∈ [4,25]`, `p = 2`, slope contrast, HC0, `σ ∈ [1, 1.5]`, Gaussian
  moments `κ̄ = 3`, `B₃ = s_max³√(8/π)`, mild misspecification, `t = 1.96`):

  | n | h_max | ϱₙ | best θ (η=0) | bound (η=0) | e_var | bound (η=30ϱₙ) |
  |---|---|---|---|---|---|---|
  | 50 | 0.078 | 0.31 | 0.19 | 0.74 | 0.41 | 9.9 (vacuous) |
  | 500 | 0.0080 | 0.097 | 0.53 | 0.19 | 0.085 | 3.1 (vacuous) |
  | 5000 | 0.0008 | 0.031 | 0.73 | 0.076 | 0.024 | 0.99 |
  | 50000 | 0.0001 | 0.0097 | 0.87 | 0.043 | 0.0079 | 0.33 |

  With `η ≡ 0` the bound is non-vacuous from `n ≈ 500` and tends to `1 − Φ(t) = 0.025`; the
  θ-sweep at `n = 500` shows the shift term `t(1−√θ)φ(t√θ)` decreasing to 0 as `θ → 1` and
  `e_var` diverging as `θ → 1 − 2h_max` (0.04 at θ=0.3, 0.12 at 0.6, 1.6 at 0.9, 47 at 0.99),
  so the optimum is interior. With the in-repo constant `η = 30ϱₙ` the bound is vacuous at
  `n = 50` and `500`, consistent with §7 of `finite_n_route.pdf`.

## Not done / open

- Nothing staged. No `sorry` outside `Clt/BerryEsseen.lean`. Nothing pushed.
