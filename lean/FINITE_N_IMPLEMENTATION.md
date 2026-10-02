# Implementation task: finite-n Berry–Esseen + variance-estimation route

You are implementing, in Lean 4 (this repo, Mathlib-based, toolchain `leanprover/lean4:v4.30.0-rc2`), the finite-sample bound whose mathematics is fully specified below. The companion write-up is `finite_n_route.pdf` in the sibling directory `~/Documents/svn/wps/lean_blog/` (read it if available, but this file is self-contained). Work autonomously per the rules in `CLAUDE.md`.

## Goal, in one line

Produce a machine-checked theorem: under stated numeric assumptions on the data-generating mechanism, the OLS contrast's studentised statistic `T` has a finite-`n`, fully explicit tail bound, from which conservative one-sided/two-sided p-values and confidence intervals follow — with **no** appeal to the asymptotic (portmanteau / limsup) machinery.

## Where to put the work

Create a new file `Ols/FiniteN.lean` for all new results. Do **not** modify existing public theorems; you may `import` from them. Add `import Ols.FiniteN` to `Ols.lean` and the file to the `Ols` glob in `lakefile.toml` (mirror the existing entries exactly). The one permitted `sorry` in the whole project stays where it is (`Clt/BerryEsseen.lean`, `uniformBerryEsseen_thirdMoment`); introduce no others that survive to the end (see CLAUDE.md on staging).

## Notation (matches the existing code)

- Contrast `a ≠ 0`; weights `γ i = aᵀ (XᵀX)⁻¹ xᵢ`; `H` the hat matrix, `hᵢ = H i i`, `h_max = ⨆ᵢ hᵢ`.
- `ν = ∑ᵢ γᵢ² σᵢ²` (population contrast variance, `= aᵀ Σ a`); `Z = (∑ᵢ γᵢ εᵢ)/√ν` (this is `LindebergSumTriangular` of the `olsArray`, already defined).
- multipliers `dᵢ ≥ 1` deterministic (HC0–HC3); `ν̂ = ∑ᵢ dᵢ γᵢ² ε̂ᵢ² = aᵀ V̂^HC a`; `T = aᵀ(β̂−β⋆)/√ν̂ = Z·√(ν/ν̂)`.
- residuals `ε̂ = r + (I−H)ε` where `r = μ − Xβ⋆`, `Xᵀr = 0` exactly.
- `M = (I−H) diag(dᵢγᵢ²) (I−H)`; `u = (I−H) diag(dᵢγᵢ²) r`; so `ν̂ = rᵀ diag(dγ²) r + 2uᵀε + εᵀMε`.

## Assumptions (carry all; do not specialise away misspecification)

- **A1 (frame):** `Yᵢ` independent; `X` deterministic full rank; `μ` arbitrary; `𝔼|εᵢ|³ < ∞`, `𝔼 εᵢ⁴ < ∞`.
- **A2 (numeric inputs):** constants `s_min, s_max, B₃, κ̄, C_r` with `s_min² ≤ σᵢ² ≤ s_max²`, `𝔼|εᵢ|³ ≤ B₃`, `𝔼 εᵢ⁴ ≤ κ̄ σᵢ⁴`, `|rᵢ| ≤ C_r`.
- **A3 (approximation input):** a function `η : ℝ → ℝ≥0∞` (or `ℝ → ℝ` with a nonnegativity hypothesis) with `|ℙ(Z ≤ z) − Φ(z)| ≤ η z` for all `z`. Take `η` as a **parameter** of the main theorem (do not hard-wire the constant). The instance `η z = 30 · ϱₙ` is available from `berryEsseen_triangular_thirdMoment` (via the existing `sorry`); wire it in a corollary only.

## The lemmas to prove, in dependency order

Each is stated as a target. Prefer to reuse the named existing lemma where one is given.

1. **`tail_of_cdf` (from A3; replaces portmanteau).** For all `z`: `ℙ(Z > z) ≤ 1 − Φ(z) + η z` and `ℙ(Z < −z) ≤ Φ(−z) + η(−z)`. Trivial from A3. *(One-sided variants of the existing `berryEsseen_triangular_tail_bound`; do not use `tendsto_measure_abs_gt_of_tendsto_stdGaussian` or `olsArray_tail_tendsto`.)*

2. **`studentisation_split` (per-n, one-sided).** For `t > 0`, `θ ∈ (0,1]`: `ℙ(T > t) ≤ ℙ(Z > t√θ) + ℙ(ν̂ ≤ θν)`. This is the existing **`slutsky_per_n_bound_oneSided`** with ratio parameter identified as `θ^{-1/2}`; write a thin reparametrising wrapper, do not re-prove.

3. **`nuhat_mean_lb` (NEW; algebraic groundwork in `Ols/HCSandwichConsistency.lean`).** `𝔼 ν̂ = ∑ᵢ dᵢγᵢ²(rᵢ² + ∑ⱼ(δᵢⱼ−Hᵢⱼ)²σⱼ²)`, and under A2, using `dᵢ ≥ 1` and `∑ⱼ(δᵢⱼ−Hᵢⱼ)²σⱼ² ≥ σᵢ²(1−2hᵢ)`: `𝔼 ν̂ ≥ (1−2h_max)ν + ρ_d²` with `ρ_d² = ∑ᵢ dᵢγᵢ²rᵢ² ≥ 0`.

4. **`nuhat_var_eq` (NEW; the main effort).** Exact variance of the quadratic-plus-linear form:
   `Var(ν̂) = ∑ᵢ Mᵢᵢ²(𝔼εᵢ⁴ − 3σᵢ⁴) + 2∑_{i,j} Mᵢⱼ² σᵢ²σⱼ² + 4∑ᵢ uᵢ²σᵢ² + 4∑ᵢ Mᵢᵢ uᵢ 𝔼εᵢ³`.
   Prove by expanding `ν̂ − 𝔼ν̂` and using independence (only diagonal-quartic, paired-quadratic, linear, diagonal-cubic covariances survive). This is index bookkeeping; take it slowly, lemma by lemma (e.g. isolate `𝔼[εᵢεⱼεₖεₗ]` case analysis first).

5. **`nuhat_var_ub` (NEW; from A2).** `Var(ν̂) ≤ V₊` with
   `V₊ = (κ̄−1)s_max⁴∑ᵢMᵢᵢ² + 2s_max⁴∑_{i≠j}Mᵢⱼ² + 4s_max²‖u‖² + 4B₃∑ᵢMᵢᵢ|uᵢ|`,
   and `‖u‖² ≤ C_r²∑ᵢdᵢ²γᵢ⁴`, `∑ᵢMᵢᵢ|uᵢ| ≤ (∑ᵢMᵢᵢ²)^{1/2}‖u‖`. All terms design/A2-computable.

6. **`variance_event` (NEW; Chebyshev is Mathlib `meas_ge_le_variance_div_sq`).** For `θ` with `θν < (1−2h_max)ν + ρ_d²`:
   `ℙ(ν̂ ≤ θν) ≤ V₊ / ((1−2h_max−θ)ν + ρ_d²)²`. Prove via `{ν̂ ≤ θν} ⊆ {𝔼ν̂ − ν̂ ≥ 𝔼ν̂ − θν}` then Chebyshev + lemmas 3,5.

7. **`gaussian_tail_shift` (NEW; elementary).** For `t > 0`, `θ ∈ (0,1]`: `1 − Φ(t√θ) ≤ 1 − Φ(t) + t(1−√θ)φ(t√θ)`, `φ` the normal density. Proof: `Φ(t)−Φ(t√θ) = ∫_{t√θ}^t φ ≤ (t−t√θ)φ(t√θ)` since `φ` decreasing on `[0,∞)`.

8. **`finiteN_tail_oneSided` (NEW; the theorem to freeze).** Under A1–A3, for `t > 0`, `θ ∈ (0, min(1, 1−2h_max))`:
   `ℙ(T > t) ≤ (1 − Φ(t)) + η(t√θ) + t(1−√θ)φ(t√θ) + V₊/((1−2h_max−θ)ν + ρ_d²)²`.
   Assemble 2 → 1 (at `z=t√θ`) → 7 → 6.

9. **Corollaries.** `finiteN_tail_lower` (apply 8 to contrast `−a`; only A3 two-sided form used); `finiteN_tail_twoSided` (union; the two tails **share** the single variance event, so `e_var` appears once); `finiteN_pvalue_oneSided`, `finiteN_pvalue_twoSided` (quantitative analogues of `pvalue_conservative` / `conservative_size_bound_of_oneSided` — delete the limsup layer, keep the per-n inequality); `finiteN_ci` (interval `aᵀβ̂ ± t√ν̂` covers `aᵀβ⋆` with prob ≥ `1 − twoSided bound`). The statistic is the pivot; impose no null.

10. **Instance corollary.** `finiteN_tail_oneSided_BE30`: instantiate `η z = 30 · thirdMomentRatioTriangular …` via `berryEsseen_triangular_thirdMoment`. Keep the general theorem primary; this is one specialisation.

## Definition of done

- `lake build` succeeds with **exactly one** `sorry` warning (the pre-existing BE black box).
- `Ols/FiniteN.lean` contains theorems 8 and 9 fully proved (no `sorry`, no `admit`, no `native_decide`-style escapes, no new axioms).
- A `#print axioms finiteN_tail_oneSided` shows only the standard three (`propext`, `Classical.choice`, `Quot.sound`) plus, for the `_BE30` instance only, `sorryAx` (inherited from the black box) — the general theorem must be `sorryAx`-free.
- Update `Ols.lean` and `lakefile.toml`.

## Verification loop

After each lemma: `~/.elan/bin/lake build Ols.FiniteN 2>&1 | tail -30`. If it fails, read the error, fix, rebuild. Do not proceed to the next lemma until the current one builds (a temporary `sorry` in *later* lemmas is fine while you work earlier ones — see CLAUDE.md).
