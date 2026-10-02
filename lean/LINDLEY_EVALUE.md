# Formalisation task: Lindley's paradox, its e-value resolution, and a Bahadur–Savage corollary

**For the VS Code Claude Code agent.** This file is a complete, self-contained
specification. Work in this repository (`~/linear-model-lean-quantitative`, a
home-folder clone that builds cleanly — do NOT move it under `~/Documents`, which is
iCloud-synced and corrupts `.lake`). Create the target files below, fill them so the
project builds with **no errors and no `sorry`**, then report. `import Mathlib` at the
top of each file (as the existing `Ols/*.lean` do). Match the house style of
`Ols/BahadurSavage.lean` and `Ols/BoundedError.lean`.

Do the milestones **in order**; each is independent enough to commit on its own.
Milestone 4 is the only hard one and may be left last (or skipped if time runs out —
say so in the report). Prefer proving the slightly more general statement **only where
it is no harder**: carry a general prior weight `c ∈ (0,1)` and a general null value
`μ₀` throughout (they cost nothing); keep the alternative prior *uniform* and the model
*Gaussian* (generalising those is strictly harder — see the notes).

---

## 0. The mathematics

We formalise three written claims (notation as in the paper).

**(BS, p-value form).** `Y₁,…,Yₙ` i.i.d. from `F` with finite mean `μ`; test
`H₀ : μ = μ₀`. A *valid p-value* is a statistic `P` with `ℙ_F(P ≤ α) ≤ α` for every `α`
and every `F` of mean `μ₀`. Then `ℙ_F(P ≤ α) ≤ α` for **every** finite-mean `F`, whatever
its mean. (This is the special case `φ = 𝟙{P ≤ α}` of the theorem already proved in
`Ols/BahadurSavage.lean`; it is a short corollary, not new analysis.)

**(Lindley).** Add that `Y₁,…,Yₙ` are i.i.d. `normal(μ, σ²)`, `σ²` known, `μ ∈ [μ₀−l, μ₀+l]`.
The average `Ȳ = n⁻¹∑Yᵢ` is sufficient, `Ȳ ~ normal(μ, σ²/n)`. Write `Φ` for the standard
normal c.d.f. and
```
P = 2(1 − Φ(|T|)),   T = √n (Ȳ − μ₀)/σ.
```
Put a prior with `ℙ(H₀) = c ∈ (0,1)`, `ℙ(H₁) = 1−c`, and `μ | H₁ ~ Uniform[μ₀−l, μ₀+l]`.
With `f_μ` the `normal(μ, σ²/n)` density of `Ȳ`, and
```
p₀(Ȳ) = f_{μ₀}(Ȳ),      p₁(Ȳ) = (1/2l) ∫_{μ₀−l}^{μ₀+l} f_μ(Ȳ) dμ,
```
the posterior of `H₀` is `π = c p₀ / (c p₀ + (1−c) p₁)`.
**Claim:** for every `ε ∈ (0,1)` there are `n` and data with `P ≤ ε` and `π ≥ 1−ε`.

**(E-values).** With `κ = (1−c)/c` and the Bayes factor `E = p₁/p₀`:
1. `E` is a valid e-value: `E ≥ 0` and `𝔼_{H₀}[E] = 1` (hence `≤ 1`), and any e-value is
   valid in the test sense `ℙ_{H₀}(E ≥ 1/α) ≤ α` (Markov).
2. The posterior is `π = 1/(1 + κ E)`, equivalently `E = (1/κ)(1−π)/π`. So `π` is strictly
   decreasing in `E`: you cannot have `π` near `1` and `E` large at once — no paradox.
3. `P = S₀(E)`, where `S₀(x) = ℙ(E ≥ x | H₀)`: the e-value's own p-value is the average
   p-value `P`. (True because `E` is a strictly increasing function of `|Ȳ − μ₀|`.)

**The engine (shared by Lindley and by claim 2's asymptotics).** Along the sequence
`Ȳₙ = μ₀ + λσ/√n` (fixed `λ > 0`), the standardised distance is `|T| = λ` for all `n`, so
`P` is constant; meanwhile `p₀(Ȳₙ) = √(n/(2πσ²)) e^{−λ²/2} → ∞` while `p₁(Ȳₙ) ≤ 1/(2l)`
stays bounded. Hence `π → 1` and `E = p₁/p₀ → 0`. This one limit is the whole of the
analysis.

---

## Milestone 1 — Bahadur–Savage in p-value form  (append to `Ols/BahadurSavage.lean`)

Reuse the existing `BahadurSavage.bahadurSavage_pi` (the n-observation theorem; read its
exact signature at the bottom of the file — it is stated for `φ : (Fin n → ℝ) → ℝ≥0∞`,
`φ ≤ 1`, with a *size* hypothesis over null laws of mean `0`, and `prodLaw n Q = Measure.pi (fun _ => Q)`).

Add, in the same namespace:

```lean
/-- **Bahadur–Savage, p-value form.** A valid p-value for `H₀ : mean = 0` over the
finite-mean class has power at most `α` at every finite-mean law. -/
theorem bahadurSavage_pvalue_pi {n : ℕ} {α : ℝ} (hα : 0 ≤ α)
    (P : (Fin n → ℝ) → ℝ) (hP : Measurable P)
    (hvalid : ∀ Q : Measure ℝ, IsProbabilityMeasure Q → Integrable id Q →
        (∫ x, x ∂Q) = 0 →
        prodLaw n Q {y | P y ≤ α} ≤ ENNReal.ofReal α)
    (Q : Measure ℝ) [IsProbabilityMeasure Q] (hQ : Integrable id Q) :
    prodLaw n Q {y | P y ≤ α} ≤ ENNReal.ofReal α := by
  sorry
```

**Proof.** Apply `bahadurSavage_pi` with the indicator test
`φ := fun y => Set.indicator {y | P y ≤ α} (fun _ => (1 : ℝ≥0∞)) y`.
- `Measurable φ`: `{y | P y ≤ α}` is measurable (`measurableSet_le hP measurable_const`);
  `Set.indicator` of a measurable set of a measurable function is measurable.
- `φ ≤ 1`: indicator of `1` is `0` or `1`.
- Size hypothesis of `bahadurSavage_pi`: for null `Q`,
  `∫⁻ φ ∂(prodLaw n Q) = prodLaw n Q {y | P y ≤ α}` by
  `lintegral_indicator` + `setLIntegral_const` (or `lintegral_indicator_one`); this is
  `≤ ENNReal.ofReal α` by `hvalid`.
- Conclusion: `∫⁻ φ ∂(prodLaw n Q) = prodLaw n Q {y | P y ≤ α} ≤ ENNReal.ofReal α`, again
  by rewriting the indicator integral as the measure.

**General null value `μ₀` (do this if quick, else note it in the report).** State
`bahadurSavage_pvalue_pi'` with `(∫ x, x ∂Q) = μ₀` in the hypothesis and conclusion, and
reduce to the `μ₀ = 0` case by pushing forward along `x ↦ x − μ₀`: `Q ↦ Q.map (· - μ₀)`
has mean `0` iff `Q` has mean `μ₀` (`integral_map`, translation), and the test
`P' y := P (y + μ₀·𝟙)` is valid for mean-`0` laws iff `P` is valid for mean-`μ₀` laws.
This is pure bookkeeping; if `Measure.map`/`integral_map` friction eats time, state and
prove only the `μ₀ = 0` version and record the translation as a remark.

---

## Milestone 2 — abstract e-values  (new file `Ols/EValue.lean`, `namespace EValue`)

Model-agnostic; **no Gaussian**. Fix a σ-finite base measure `ν` on a measurable space `Ω`
and two densities `p₀ p₁ : Ω → ℝ≥0∞` (measurable) that integrate to `1`
(`∫⁻ ω, p₀ ω ∂ν = 1`, likewise `p₁`). Let `P₀ := ν.withDensity p₀` (a probability measure).
Define the e-value `E := fun ω => p₁ ω / p₀ ω` (ENNReal division; `x/0 = 0`, `x/∞ = 0`).

```lean
/-- The Bayes factor `p₁/p₀` has `H₀`-expectation exactly `1`. -/
theorem evalue_expectation_eq_one
    (hp0 : Measurable p₀) (hp1 : Measurable p₁)
    (hp0_int : (∫⁻ ω, p₀ ω ∂ν) = 1) (hp1_int : (∫⁻ ω, p₁ ω ∂ν) = 1)
    (hp0_ae : ∀ᵐ ω ∂ν, p₀ ω ≠ 0 ∧ p₀ ω ≠ ∞) :
    (∫⁻ ω, (p₁ ω / p₀ ω) ∂(ν.withDensity p₀)) = 1 := by
  sorry

/-- **Validity of an e-value** (Markov). If `∫⁻ E ∂P₀ ≤ 1` then rejecting when
`E ≥ 1/α` has size `≤ α`. -/
theorem evalue_markov {Ω} {mΩ : MeasurableSpace Ω} {P₀ : Measure Ω}
    {E : Ω → ℝ≥0∞} (hE : Measurable E) (hE1 : (∫⁻ ω, E ω ∂P₀) ≤ 1)
    (α : ℝ≥0∞) (hα : α ≠ 0) :
    P₀ {ω | 1/α ≤ E ω} ≤ α := by
  sorry
```

**Proofs.**
- `evalue_expectation_eq_one`: `lintegral_withDensity_eq_lintegral_mul₀` (or
  `setLIntegral_withDensity_eq_setLIntegral_mul` on `{0 < p₀ < ∞}`) turns the LHS into
  `∫⁻ ω, (p₁ ω / p₀ ω) * p₀ ω ∂ν`. On the a.e. set `hp0_ae`, `(p₁/p₀)*p₀ = p₁`
  (`ENNReal.div_mul_cancel`); the complement is `ν`-null, so
  `∫⁻ (p₁/p₀)*p₀ ∂ν = ∫⁻ p₁ ∂ν = 1`. (Search Mathlib for the exact `withDensity`
  lemma name; both `lintegral_withDensity_eq_lintegral_mul` and the `₀` a.e.-measurable
  variant exist.)
- `evalue_markov`: `mul_meas_ge_le_lintegral₀` (in
  `Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`) gives
  `(1/α) * P₀{1/α ≤ E} ≤ ∫⁻ E ∂P₀ ≤ 1`; multiply through by `α` and simplify with
  `ENNReal` lemmas (`ENNReal.le_div_iff_mul_le`, `one_div`, `ENNReal.mul_le_mul...`).

**The posterior identity (real algebra; state over `ℝ`).** With `c ∈ (0,1)`,
`κ := (1-c)/c`, and reals `p₀ > 0`, `p₁ ≥ 0`, set `e := p₁/p₀` and
`π := c*p₀ / (c*p₀ + (1-c)*p₁)`.

```lean
theorem posterior_eq (hc0 : 0 < c) (hc1 : c < 1) (hp0 : 0 < p₀) (hp1 : 0 ≤ p₁) :
    (c*p₀) / (c*p₀ + (1-c)*p₁) = 1 / (1 + ((1-c)/c) * (p₁/p₀)) := by
  sorry   -- field_simp; ring  (denominators are positive)

theorem evalue_of_posterior (hc0 : 0 < c) (hc1 : c < 1) (hp0 : 0 < p₀) (hp1 : 0 ≤ p₁) :
    p₁/p₀ = (c/(1-c)) * (1 - ((c*p₀)/(c*p₀+(1-c)*p₁))) / ((c*p₀)/(c*p₀+(1-c)*p₁)) := by
  sorry   -- field_simp; ring
```

and the "no paradox" monotonicity, e.g.

```lean
theorem posterior_antitone_in_evalue (hκ : 0 < κ) :
    StrictAntiOn (fun e => 1/(1+κ*e)) (Set.Ici 0) := by
  sorry   -- 1+κe strictly increasing and positive on e ≥ 0
```

from which "not both large" is immediate: `π ≥ 1-β ↔ e ≤ (1/κ)·β/(1-β)`.

Keep `c` general — `c = 1/2` (κ = 1) is not one line shorter.

---

## Milestone 3 — Lindley's paradox  (new file `Ols/Lindley.lean`, `namespace Lindley`)

Fix parameters `σ : ℝ` with `0 < σ`, `μ₀ : ℝ`, `l : ℝ` with `0 < l`, `c : ℝ` with `0 < c < 1`.
Everything is a function of the sample size `n` and the observed average `Ȳ` (a real): any
`Ȳ` is realisable by data `Yᵢ := Ȳ`, so it suffices to exhibit `(n, Ȳ)`.

Let `v n : ℝ≥0 := ⟨σ^2 / n, by positivity⟩` (for `n ≥ 1`). Define, using Mathlib's
`gaussianPDFReal` and `Φ := ProbabilityTheory.cdf (gaussianReal 0 1)`:

```lean
noncomputable def g0 (n : ℕ) (y : ℝ) : ℝ := gaussianPDFReal μ₀ (v n) y
noncomputable def g1 (n : ℕ) (y : ℝ) : ℝ :=
  (1/(2*l)) * ∫ μ in Set.Icc (μ₀-l) (μ₀+l), gaussianPDFReal μ (v n) y
noncomputable def pval (n : ℕ) (y : ℝ) : ℝ := 2 * (1 - Φ (Real.sqrt n * |y - μ₀| / σ))
noncomputable def post (n : ℕ) (y : ℝ) : ℝ := (c * g0 n y) / (c * g0 n y + (1-c) * g1 n y)
```

Target:

```lean
/-- **Lindley's paradox.** A fixed significance and a near-certain posterior for `H₀`
occur together. -/
theorem lindley (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ (n : ℕ) (y : ℝ), 1 ≤ n ∧ pval n y ≤ ε ∧ post n y ≥ 1 - ε := by
  sorry
```

**Proof plan.**

1. **pdf symmetry** (small lemma): `gaussianPDFReal μ w y = gaussianPDFReal y w μ` for all
   `μ w y`. Proof: `simp only [gaussianPDFReal]`, then the exponents agree because
   `(y-μ)^2 = (μ-y)^2` (`ring_nf` / `sub_sq`, `neg_sub`).

2. **`g1` is bounded**: `0 ≤ g1 n y ≤ 1/(2*l)`. By symmetry,
   `∫ μ in Icc (μ₀-l)(μ₀+l), gaussianPDFReal μ (v n) y = ∫ μ in Icc.., gaussianPDFReal y (v n) μ`,
   which is `(gaussianReal y (v n)) (Icc (μ₀-l)(μ₀+l))` as a real
   (`gaussianReal_apply_eq_integral`), hence `≤ (gaussianReal y (v n)) univ = 1`
   (probability measure). So `g1 = (1/(2l)) · (≤1) ≤ 1/(2l)`. Nonnegativity from
   `gaussianPDFReal_nonneg`.

3. **`g0` along the sequence blows up**: for fixed `λ > 0` set `y n := μ₀ + λ*σ/√n`. Then
   `(y n - μ₀)^2 / (2*(σ^2/n)) = λ^2/2`, so
   `g0 n (y n) = Real.sqrt (n/(2*π*σ^2)) * Real.exp (-λ^2/2)` (unfold `gaussianPDFReal`,
   simplify). As `n → ∞` this `→ ∞` (`Real.sqrt` of `n·const → ∞`). Use `Filter.Tendsto … atTop atTop`.

4. **`pval` is constant on the sequence**: `√n * |y n - μ₀| / σ = λ`, so
   `pval n (y n) = 2*(1 - Φ λ)` for every `n ≥ 1`.

5. **Choose `λ`**: since `Φ = cdf (gaussianReal 0 1)` and `tendsto_cdf_atTop` gives
   `Φ λ → 1` as `λ → ∞`, `2*(1 - Φ λ) → 0`; pick `λ` with `2*(1 - Φ λ) ≤ ε` and `λ > 0`.
   (No inverse-cdf/IVT needed — just the limit and `Filter.eventually`.) Then
   `pval n (y n) ≤ ε` for all `n ≥ 1`.

6. **`post → 1`**: with steps 2–3, `post n (y n) = 1 / (1 + (1-c) g1 / (c g0)) ≥
   1 - (1-c) g1 / (c g0) ≥ 1 - ((1-c)/(2l)) / (c · g0 n (y n)) → 1`. Formally: the error
   term `((1-c)/(2l)) / (c · g0 n (y n)) → 0` because the denominator `→ ∞` (step 3);
   so `post n (y n) → 1`, giving some `N` with `post N (y N) ≥ 1 - ε`.
   (`Filter.Tendsto.const_div_atTop`, `tendsto_atTop` unfolding, or bound directly.)

7. Output `(N, y N)`: `1 ≤ N`, `pval N (y N) ≤ ε` (step 5), `post N (y N) ≥ 1-ε` (step 6).

Keep the alternative prior **uniform** and the model **Gaussian**: step 2 uses only
"mass ≤ 1" (two lines); a general prior `g` would need `∫ g(μ) f_μ(Ȳₙ) dμ → g(μ₀)`
(an approximate-identity / Lebesgue-point argument) — strictly more work for no gain here.

**Mathlib pointers.** `ProbabilityTheory.gaussianPDFReal` (`…/Gaussian/Real.lean`,
with `gaussianPDFReal_def/_pos/_nonneg`); `gaussianReal_apply_eq_integral`;
`ProbabilityTheory.cdf`, `monotone_cdf`, `tendsto_cdf_atTop`, `tendsto_cdf_atBot`
(`…/Probability/CDF.lean`). `erf` is **not** in Mathlib — do not reach for it; `pval` is
defined through `Φ` and the argument needs only `Φ`'s monotonicity and limits.

---

## Milestone 4 — `P = S₀(E)` (hardest; do last, may be skipped)

In `Ols/Lindley.lean`, with `E n y := g1 n y / g0 n y` and `S₀ n x := (gaussianReal μ₀ (v n)) {y | E n y ≥ x} |>.toReal`:

```lean
theorem pval_eq_survival (n : ℕ) (hn : 1 ≤ n) (y : ℝ) :
    pval n y = S₀ n (E n y) := by
  sorry
```

**Plan.** (a) Show `E n ·` is even about `μ₀` and **strictly increasing in `|y-μ₀|`** on
`ℝ` (or on the interval interior): `1/g0` ∝ `exp((y-μ₀)^2/(2v))` is strictly increasing in
`|y-μ₀|`; `g1` is even in `(y-μ₀)` and its dependence is dominated by `1/g0` (bound `g1`
above by `1/(2l)` and below by a positive constant on the relevant range, or differentiate).
This monotonicity is the only real work. (b) Then
`{y | E n y ≥ E n y₀} = {y | |y-μ₀| ≥ |y₀-μ₀|}`, whose `gaussianReal μ₀ (v n)` measure is
`2*(1 - Φ(√n|y₀-μ₀|/σ)) = pval n y₀` (two symmetric tails of the null normal, via `cdf`).
If the strict-monotonicity step proves stubborn, report Milestones 1–3 done and leave this
as future work — it is the calibration nicety, not the paradox itself.

---

## Reporting

When done: state which milestones are `sorry`-free (run `#print axioms` on
`bahadurSavage_pvalue_pi`, `evalue_expectation_eq_one`, `evalue_markov`, `lindley`, and
`pval_eq_survival` if attempted — each should show only `[propext, Classical.choice,
Quot.sound]`), note any milestone left open and why, and list any Mathlib lemma whose name
differed from the guesses above.
