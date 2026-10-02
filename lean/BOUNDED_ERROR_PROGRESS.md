# BOUNDED_ERROR_PROGRESS — `Ols/BoundedError.lean`

Date: 2026-09-11. Status: **Milestones A, B and C complete, sorry-free.**

## Milestone A — Hoeffding (done)

- `hasSubgaussianMGF_weighted` (private): each `γᵢεᵢ` is sub-Gaussian via Mathlib's Hoeffding
  lemma `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` on `Icc (-(|γᵢ|Bᵢ)) (|γᵢ|Bᵢ)`.
- `proxy_eq` (private): the `ℝ≥0` proxy `(‖b − a‖₊/2)²` coerces to `(γᵢBᵢ)²` (no sign
  condition on `Bᵢ` is needed since `|x|² = x²`).
- `hoeffding_one_tail` (private): `HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun` on
  `Finset.univ`, independence of the weighted errors by `iIndepFun.comp`.
- `hoeffding_tail`: two-sided, via `two_sided_of_one_sided` — the lower tail is the upper tail of
  the weights `-γ` (`wsum (-γ) ε = -wsum γ ε`, and `((-γᵢ)Bᵢ)² = (γᵢBᵢ)²`), so no separate
  `HasSubgaussianMGF.neg` argument is needed.

## Milestone B — Bernstein (done)

- B1 `bennett_mgf_le`. Mathlib has no Bennett/Bernstein. The pointwise input is proved without
  any power series: `key_ineq : (3 − y) exp y ≤ 3 + 2y + y²/2` for **every** real `y`. Its
  second derivative is `1 − (1 − y) exp y ≥ 0` (a rearrangement of Mathlib's
  `Real.add_one_le_exp (−y)`), so `g'(y) = 2 + y − (2 − y) exp y` is monotone with `g'(0) = 0`,
  hence `g` is antitone on `Iic 0`, monotone on `Ici 0`, and `g ≥ g 0 = 0`
  (`monotone_of_deriv_nonneg`, `monotoneOn_of_deriv_nonneg`, `antitoneOn_of_deriv_nonpos`).
  Dividing by `3 − y > 0` gives Bennett's pointwise bound
  `exp y ≤ 1 + y + y²/(2(1 − c/3))` for `|y| ≤ c < 3` (`exp_le_of_abs_le`). Integrating
  (bounded ⇒ integrable via `memLp_top_of_bound`) and `1 + x ≤ exp x` finishes. The hypothesis
  `0 < M` of the skeleton is not needed by the proof (kept in the signature; linter silenced).
- B2 `bernstein_tail`. `mgf_wsum_le`: MGF of the sum factorises (`iIndepFun.mgf_sum`), Bennett
  per term with the common `M`, `Finset.prod_le_prod`, `Real.exp_sum`. `bernstein_one_tail`:
  Chernoff `measure_ge_le_exp_mul_mgf` at `t = u/(S + Mu/3)` (`S = ∑(γᵢsᵢ)²`), for which
  `1 − tM/3 = S/D` and the exponent is `−u²/(2D)` by `field_simp; ring`. Degenerate cases
  handled separately: `S = 0` (take `t = 3/(2M)`, which reproduces the target exactly) and
  `M ≤ 0` (then every `γᵢεᵢ` vanishes identically, so the event is `∅` or `univ`).
  Two-sided again via `−γ`.

## Milestone C — OLS contrast (done, thin)

- `contrastDiff_eq_wsum`: `contrastDiff P X y a = wsum (olsWeights X a) (centredErr P y)` (`rfl`,
  with `contrastDiff` from `Ols/FiniteN.lean`, where `contrastDiff_eq` identifies it with
  `a ⬝ᵥ (β̂ − β⋆)`).
- `hoeffding_contrast`, `bernstein_contrast`: certified p-values for `P(|aᵀ(β̂ − β⋆)| ≥ u)`
  under declared error bounds `|Yᵢ − E Yᵢ| ≤ Bᵢ` (and variance bounds for Bernstein), for
  independent measurable responses; mean-zero of the centred errors follows from boundedness.

## Verification

- `~/.elan/bin/lake build Ols.BoundedError`: exit 0, no `sorry`, no `error`, no linter warnings.
- `~/.elan/bin/lake build` (whole project): clean; the only `sorry` is the pre-existing
  Berry–Esseen placeholder (`Clt/BerryEsseen.lean:55`).
- `#print axioms` — all of `BoundedError.hoeffding_tail`, `bennett_mgf_le`, `bernstein_tail`,
  `hoeffding_contrast`, `bernstein_contrast`: `[propext, Classical.choice, Quot.sound]`.
- `lakefile.toml`: `Ols.BoundedError` added to the `Ols` globs; `Ols.lean` already imported it.
- Nothing sorried; nothing pushed.
