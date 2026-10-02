/-
Copyright (c) 2026 Patrick Rubin-Delanchy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Rubin-Delanchy, Andrew Jones
AI-generated (see the top-level README); not audited by the authors.
-/
import Ols.BahadurSavage
import Ols.EValue
import Ols.Lindley

/-!
# Paper-aligned statements: Bahadur–Savage, Lindley's paradox, e-values

A thin layer re-exposing the results of `Ols/BahadurSavage.lean`, `Ols/EValue.lean` and
`Ols/Lindley.lean` under the names and notation of the paper's "Paradoxes" section, so that
the code can be lined up against the prose. Everything here is a wrapper over existing theorems.

* Bahadur–Savage is stated over the raw i.i.d. sample `Y : Fin n → ℝ` (`Distribution`,
  `ValidPValue`, `bahadur_savage`).
* Lindley's p-value and posterior are stated over the raw sample `Y : Fin n → ℝ`, through the
  sample mean `mean Y`; the e-value machinery (`eValue`, `IsValidEValue`, its validity and
  Markov test) is stated over the average `ybar : ℝ`, i.e. against the null law
  `gaussianReal μ₀ (σ²/n)` of the average, the sufficient statistic it depends on. The cross
  theorems relate the two via `mean Y`.

See `PAPER_ALIGNMENT.md`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace PaperAligned

open BahadurSavage Lindley

/-! ## A. Bahadur–Savage over the raw sample -/

/-- A distribution on `ℝ` with a finite mean. -/
structure Distribution where
  law : Measure ℝ
  isProb : IsProbabilityMeasure law
  integrable : Integrable id law

attribute [instance] Distribution.isProb

/-- The mean of a distribution. -/
noncomputable def Distribution.mean (F : Distribution) : ℝ := ∫ x, x ∂F.law

/-- The probability of an event under `n` i.i.d. draws from `F`. -/
noncomputable def Distribution.prob (F : Distribution) {n : ℕ} (A : Set (Fin n → ℝ)) : ℝ :=
  (prodLaw n F.law A).toReal

instance prodLaw_isProbabilityMeasure (n : ℕ) (Q : Measure ℝ) [IsProbabilityMeasure Q] :
    IsProbabilityMeasure (prodLaw n Q) := by
  unfold prodLaw
  infer_instance

/-- A valid p-value for `H₀ : mean = μ₀` over the class of all finite-mean distributions:
under every null distribution, `ℙ(P ≤ α) ≤ α` for every level `α ∈ [0, 1]`. -/
structure ValidPValue (n : ℕ) (μ₀ : ℝ) where
  value : (Fin n → ℝ) → ℝ
  measurable : Measurable value
  valid : ∀ F : Distribution, F.mean = μ₀ →
    ∀ α : ℝ, 0 ≤ α → α ≤ 1 → F.prob {y | value y ≤ α} ≤ α

/-- **Bahadur–Savage.** A valid p-value for the mean has power at most its level under
*every* finite-mean distribution, whatever its mean: the data are useless. -/
theorem bahadur_savage {n : ℕ} {μ₀ : ℝ} (P : ValidPValue n μ₀) (F : Distribution)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    F.prob {y | P.value y ≤ α} ≤ α := by
  have hvalid : ∀ Q : Measure ℝ, IsProbabilityMeasure Q → Integrable id Q →
      integral Q (fun x : ℝ => x) = μ₀ →
      prodLaw n Q {y | P.value y ≤ α} ≤ ENNReal.ofReal α := by
    intro Q hQ hint hmean
    haveI := hQ
    have h := P.valid ⟨Q, hQ, hint⟩ hmean α hα0 hα1
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hα0).mpr h
  have h := bahadurSavage_pvalue_pi' hα0 μ₀ P.value P.measurable hvalid F.law F.integrable
  exact ENNReal.toReal_le_of_le_ofReal hα0 h

/-- The expectation of a nonnegative statistic under `n` i.i.d. draws from `F`. -/
noncomputable def Distribution.expect (F : Distribution) {n : ℕ} (e : (Fin n → ℝ) → ℝ) : ℝ :=
  (∫⁻ y, ENNReal.ofReal (e y) ∂(prodLaw n F.law)).toReal

/-- A valid e-value for `H₀ : mean = μ₀` over the class of all finite-mean distributions: a
measurable nonnegative statistic, integrable under every null distribution, with expectation at
most `1` under every null distribution. (Integrability under the null is needed so that the
real-valued `expect ≤ 1` carries the information `∫⁻ ≤ 1`.) -/
structure ValidEValue (n : ℕ) (μ₀ : ℝ) where
  value : (Fin n → ℝ) → ℝ
  measurable : Measurable value
  nonneg : ∀ y, 0 ≤ value y
  integrable : ∀ F : Distribution, F.mean = μ₀ → Integrable value (prodLaw n F.law)
  valid : ∀ F : Distribution, F.mean = μ₀ → F.expect value ≤ 1

/-- **Bahadur–Savage, e-value form.** A valid e-value for the mean has expectation at most `1`
under *every* finite-mean distribution, whatever its mean: no bet against `H₀` has positive
expected return under any alternative. (Expectation form; see `PROTOCOL_PROGRESS.md`.) -/
theorem bahadur_savage_evalue {n : ℕ} {μ₀ : ℝ} (E : ValidEValue n μ₀) (F : Distribution) :
    F.expect E.value ≤ 1 := by
  have hvalid : ∀ Q : Measure ℝ, IsProbabilityMeasure Q → Integrable id Q →
      integral Q (fun x : ℝ => x) = μ₀ →
      (∫⁻ y, ENNReal.ofReal (E.value y) ∂(prodLaw n Q)) ≤ 1 := by
    intro Q hQ hint hmean
    haveI := hQ
    have hint' := E.integrable ⟨Q, hQ, hint⟩ hmean
    have h := E.valid ⟨Q, hQ, hint⟩ hmean
    unfold Distribution.expect at h
    rw [← ofReal_integral_eq_lintegral_ofReal hint' (ae_of_all _ E.nonneg)] at h ⊢
    rw [ENNReal.toReal_ofReal (integral_nonneg E.nonneg)] at h
    exact ENNReal.ofReal_le_one.mpr h
  have h := bahadurSavage_evalue_pi μ₀ E.measurable.ennreal_ofReal hvalid F.law F.integrable
  unfold Distribution.expect
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h)

/-! ## B. Lindley's paradox (raw sample) and e-values (sample mean) -/

/-- The sample mean `ȳ = n⁻¹ ∑ᵢ Yᵢ`. -/
noncomputable def mean {n : ℕ} (Y : Fin n → ℝ) : ℝ := (∑ i, Y i) / n

/-- The mean of a constant sample is that constant (for `n ≥ 1`). -/
lemma mean_const {n : ℕ} (hn : 1 ≤ n) (ybar : ℝ) : mean (fun _ : Fin n => ybar) = ybar := by
  have hn' : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact this.ne'
  simp only [mean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- The two-sided p-value `P = 2(1 − Φ(√n|ȳ − μ₀|/σ))` of a sample `Y`. -/
noncomputable def pValue (σ μ₀ : ℝ) {n : ℕ} (Y : Fin n → ℝ) : ℝ := pval σ μ₀ n (mean Y)

/-- The posterior probability of `H₀` given a sample `Y` (prior weight `c`, uniform
alternative on `[μ₀ − l, μ₀ + l]`). -/
noncomputable def posterior (σ μ₀ l c : ℝ) {n : ℕ} (Y : Fin n → ℝ) : ℝ :=
  post σ μ₀ l c n (mean Y)

/-- The e-value (Bayes factor) `E = p₁/p₀`. -/
noncomputable def eValue (σ μ₀ l : ℝ) (n : ℕ) (ybar : ℝ) : ℝ := E σ μ₀ l n ybar

/-- Probability of an event under `H₀` (the average is `gaussianReal μ₀ (σ²/n)`), as a real. -/
noncomputable def nullProb (σ μ₀ : ℝ) (n : ℕ) (A : Set ℝ) : ℝ :=
  (gaussianReal μ₀ (v σ n) A).toReal

/-- Expectation of a statistic of the average under `H₀`, as a real. -/
noncomputable def nullExp (σ μ₀ : ℝ) (n : ℕ) (g : ℝ → ℝ) : ℝ :=
  integral (gaussianReal μ₀ (v σ n)) g

/-- A valid e-value under `H₀`: a measurable, integrable, nonnegative statistic with
`H₀`-expectation at most `1`. (Measurability and integrability are needed for the Markov test
`IsValidEValue.test` to be meaningful.) -/
def IsValidEValue (σ μ₀ : ℝ) (n : ℕ) (e : ℝ → ℝ) : Prop :=
  Measurable e ∧ Integrable e (gaussianReal μ₀ (v σ n)) ∧ (∀ ybar, 0 ≤ e ybar) ∧
    nullExp σ μ₀ n e ≤ 1

/-- **Lindley's paradox.** For every `ε ∈ (0,1)` there are a sample size and a sample with
`P ≤ ε` and posterior probability of `H₀` at least `1 − ε`. -/
theorem lindley_paradox {σ μ₀ l c : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hc0 : 0 < c) (hc1 : c < 1)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ (n : ℕ) (Y : Fin n → ℝ), pValue σ μ₀ Y ≤ ε ∧ posterior σ μ₀ l c Y ≥ 1 - ε := by
  obtain ⟨n, ybar, hn, hp, hpost⟩ := lindley hσ hl hc0 hc1 ε hε0 hε1
  refine ⟨n, fun _ => ybar, ?_, ?_⟩
  · unfold pValue
    rw [mean_const hn]
    exact hp
  · unfold posterior
    rw [mean_const hn]
    exact hpost

/-- Joint continuity of the Gaussian density in (argument, mean). -/
private lemma continuous_pdf_pair (w : ℝ≥0) :
    Continuous fun p : ℝ × ℝ => gaussianPDFReal p.2 w p.1 := by
  unfold gaussianPDFReal
  fun_prop

/-- The Gaussian density is jointly integrable on `ℝ × [μ₀ − l, μ₀ + l]`. -/
private lemma integrable_pdf_prod {σ : ℝ} (hσ : 0 < σ) (μ₀ l : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    Integrable (fun p : ℝ × ℝ => gaussianPDFReal p.2 (v σ n) p.1)
      (volume.prod (volume.restrict (Set.Icc (μ₀ - l) (μ₀ + l)))) := by
  have hmeas := (continuous_pdf_pair (v σ n)).measurable
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (μ₀ - l) (μ₀ + l))) :=
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  refine ⟨ae_of_all _ fun μ => integrable_gaussianPDFReal μ (v σ n), ?_⟩
  have h1 : (fun μ => ∫ x, ‖gaussianPDFReal μ (v σ n) x‖) = fun _ => (1 : ℝ) := by
    funext μ
    have : (fun x => ‖gaussianPDFReal μ (v σ n) x‖) = fun x => gaussianPDFReal μ (v σ n) x := by
      funext x
      rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
    rw [this]
    exact integral_gaussianPDFReal_eq_one μ (v_ne_zero hσ hn)
  rw [h1]
  exact integrable_const _

/-- The mixture density `g1` integrates to one. -/
private lemma integral_g1 {σ : ℝ} (hσ : 0 < σ) (μ₀ : ℝ) {l : ℝ} (hl : 0 < l) {n : ℕ}
    (hn : 1 ≤ n) : ∫ y, g1 σ μ₀ l n y = 1 := by
  have hI := integrable_pdf_prod hσ μ₀ l hn
  unfold g1
  rw [integral_const_mul,
    integral_integral_swap (f := fun y μ => gaussianPDFReal μ (v σ n) y) hI]
  have h1 : ∫ μ in Set.Icc (μ₀ - l) (μ₀ + l), ∫ y, gaussianPDFReal μ (v σ n) y
      = ∫ _ in Set.Icc (μ₀ - l) (μ₀ + l), (1 : ℝ) :=
    setIntegral_congr_fun measurableSet_Icc fun μ _ =>
      integral_gaussianPDFReal_eq_one μ (v_ne_zero hσ hn)
  rw [h1, setIntegral_const, measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
  field_simp
  ring

/-- `g1` is measurable (as a parametric integral of a jointly measurable function). -/
private lemma measurable_g1 (σ μ₀ l : ℝ) (n : ℕ) : Measurable (g1 σ μ₀ l n) := by
  have hsm : StronglyMeasurable fun p : ℝ × ℝ => gaussianPDFReal p.2 (v σ n) p.1 :=
    (continuous_pdf_pair _).stronglyMeasurable
  have h := hsm.integral_prod_right' (ν := volume.restrict (Set.Icc (μ₀ - l) (μ₀ + l)))
  exact h.measurable.const_mul _

/-- `g1` is integrable. -/
private lemma integrable_g1 {σ : ℝ} (hσ : 0 < σ) (μ₀ l : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    Integrable (g1 σ μ₀ l n) volume := by
  have h := (integrable_pdf_prod hσ μ₀ l hn).integral_prod_left
  exact h.const_mul _

/-- **(1) The Bayes factor is a valid e-value:** nonnegative with `H₀`-expectation one. -/
theorem eValue_isValidEValue {σ μ₀ l : ℝ} (hσ : 0 < σ) (hl : 0 < l) {n : ℕ} (hn : 1 ≤ n) :
    IsValidEValue σ μ₀ n (eValue σ μ₀ l n) := by
  have hv := v_ne_zero hσ hn
  have hg0pos : ∀ y, 0 < g0 σ μ₀ n y := g0_pos hσ μ₀ hn
  have hsmul : (fun x => gaussianPDFReal μ₀ (v σ n) x • eValue σ μ₀ l n x) = g1 σ μ₀ l n := by
    funext x
    have := hg0pos x
    simp only [eValue, E, smul_eq_mul, g0] at this ⊢
    field_simp
  refine ⟨(measurable_g1 σ μ₀ l n).div (measurable_gaussianPDFReal _ _), ?_,
    fun y => div_nonneg (g1_nonneg σ μ₀ hl n y) (hg0pos y).le, ?_⟩
  · -- integrability under the null law `volume.withDensity g0`
    rw [gaussianReal_of_var_ne_zero _ hv]
    have hd : gaussianPDF μ₀ (v σ n)
        = fun x => ((Real.toNNReal (gaussianPDFReal μ₀ (v σ n) x) : ℝ≥0) : ℝ≥0∞) := by
      funext x
      rfl
    rw [hd, integrable_withDensity_iff_integrable_coe_smul
      (measurable_gaussianPDFReal _ _).real_toNNReal]
    have : (fun x => ((Real.toNNReal (gaussianPDFReal μ₀ (v σ n) x) : ℝ≥0) : ℝ)
        • eValue σ μ₀ l n x) = g1 σ μ₀ l n := by
      rw [← hsmul]
      funext x
      rw [Real.coe_toNNReal _ (gaussianPDFReal_nonneg _ _ _)]
    rw [this]
    exact integrable_g1 hσ μ₀ l hn
  · -- expectation one
    unfold nullExp
    rw [integral_gaussianReal_eq_integral_smul hv, hsmul, integral_g1 hσ μ₀ hl hn]

/-- **(1') A valid e-value gives a level-`α` test** (Markov): `ℙ_{H₀}(E ≥ 1/α) ≤ α`. -/
theorem IsValidEValue.test {σ μ₀ : ℝ} {n : ℕ} {e : ℝ → ℝ}
    (h : IsValidEValue σ μ₀ n e) (α : ℝ) (hα : 0 < α) :
    nullProb σ μ₀ n {ybar | 1 / α ≤ e ybar} ≤ α := by
  obtain ⟨hmeas, hint, hnn, hexp⟩ := h
  have hE : Measurable fun y => ENNReal.ofReal (e y) := hmeas.ennreal_ofReal
  have hE1 : ∫⁻ y, ENNReal.ofReal (e y) ∂(gaussianReal μ₀ (v σ n)) ≤ 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hnn)]
    exact ENNReal.ofReal_le_one.mpr hexp
  have hm := EValue.evalue_markov hE hE1 (ENNReal.ofReal α) (ENNReal.ofReal_pos.mpr hα).ne'
  have hset : {y | 1 / ENNReal.ofReal α ≤ ENNReal.ofReal (e y)} = {y | 1 / α ≤ e y} := by
    ext y
    simp only [Set.mem_setOf_eq]
    rw [one_div, one_div, ← ENNReal.ofReal_inv_of_pos hα, ENNReal.ofReal_le_ofReal_iff (hnn y)]
  rw [hset] at hm
  exact ENNReal.toReal_le_of_le_ofReal hα.le hm

/-- **(2) The e-value corresponds to the p-value:** `P = S₀(E) = ℙ_{H₀}(E ≥ E(ȳ))`. -/
theorem pValue_eq_survival {σ μ₀ l : ℝ} (hσ : 0 < σ) (hl : 0 < l) {n : ℕ} (hn : 1 ≤ n)
    (Y : Fin n → ℝ) :
    pValue σ μ₀ Y
      = nullProb σ μ₀ n {ybar' | eValue σ μ₀ l n (mean Y) ≤ eValue σ μ₀ l n ybar'} :=
  pval_eq_survival hσ μ₀ hl hn (mean Y)

/-- **(3a)** `π = 1/(1 + κE)` with `κ = (1 − c)/c`. -/
theorem posterior_eq_eValue {σ μ₀ l c : ℝ} (hσ : 0 < σ) (hc0 : 0 < c) (hc1 : c < 1)
    {n : ℕ} (hn : 1 ≤ n) (Y : Fin n → ℝ) :
    posterior σ μ₀ l c Y = 1 / (1 + ((1 - c) / c) * eValue σ μ₀ l n (mean Y)) := by
  have hp0 : 0 < g0 σ μ₀ n (mean Y) := g0_pos hσ μ₀ hn (mean Y)
  have hc1' : (1 - c) ≠ 0 := by linarith
  unfold posterior eValue post E
  have key : 1 + ((1 - c) / c) * (g1 σ μ₀ l n (mean Y) / g0 σ μ₀ n (mean Y))
      = (c * g0 σ μ₀ n (mean Y) + (1 - c) * g1 σ μ₀ l n (mean Y)) / (c * g0 σ μ₀ n (mean Y)) := by
    field_simp
  rw [key, one_div_div]

/-- **(3b)** `E = (1/κ)(1 − π)/π`: the e-value and the posterior are equivalent
(each determines the other), so a posterior near `1` and a large e-value cannot coexist. -/
theorem eValue_equiv_posterior {σ μ₀ l c : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hc0 : 0 < c)
    (hc1 : c < 1) {n : ℕ} (hn : 1 ≤ n) (Y : Fin n → ℝ) :
    eValue σ μ₀ l n (mean Y)
      = (c / (1 - c)) * (1 - posterior σ μ₀ l c Y) / posterior σ μ₀ l c Y := by
  unfold eValue posterior E post
  exact EValue.evalue_of_posterior hc0 hc1 (g0_pos hσ μ₀ hn _) (g1_nonneg σ μ₀ hl n _)

/-- **(3c) No paradox:** `π ≥ 1 − β` exactly when `E ≤ β/(κ(1 − β))`. -/
theorem no_paradox {σ μ₀ l c : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hc0 : 0 < c) (hc1 : c < 1)
    {n : ℕ} (hn : 1 ≤ n) (Y : Fin n → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    1 - β ≤ posterior σ μ₀ l c Y ↔
      eValue σ μ₀ l n (mean Y) ≤ β / (((1 - c) / c) * (1 - β)) := by
  rw [posterior_eq_eValue hσ hc0 hc1 hn]
  exact EValue.posterior_ge_iff (div_pos (by linarith) hc0)
    (div_nonneg (g1_nonneg σ μ₀ hl n _) (g0_pos hσ μ₀ hn _).le) hβ0 hβ1

end PaperAligned
