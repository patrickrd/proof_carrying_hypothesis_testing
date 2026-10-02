/-
Copyright (c) 2026 Patrick Rubin-Delanchy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Rubin-Delanchy, Andrew Jones
AI-generated (see the top-level README); not audited by the authors.
-/
import Mathlib

/-!
# Abstract e-values: expectation one, Markov validity, and the posterior identity

Model-agnostic facts about the Bayes factor `E = p₁/p₀` of two densities with respect to a
common base measure:

* `evalue_expectation_eq_one` — `E` has `H₀`-expectation exactly `1`;
* `evalue_markov` — any nonnegative statistic with `H₀`-expectation at most `1` is a valid
  test statistic: `P₀(E ≥ 1/α) ≤ α`;
* `posterior_eq`, `evalue_of_posterior` — with prior weight `c` on `H₀` and `κ = (1-c)/c`,
  the posterior of `H₀` is `π = 1/(1 + κE)`, equivalently `E = (1/κ)(1-π)/π`;
* `posterior_antitone_in_evalue`, `posterior_ge_iff` — `π` is strictly decreasing in `E`, so a
  posterior near `1` and a large e-value cannot occur together ("no paradox").

See `LINDLEY_EVALUE.md` for the context and the working protocol.
-/

open MeasureTheory
open scoped ENNReal

namespace EValue

section Densities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ν : Measure Ω} {p₀ p₁ : Ω → ℝ≥0∞}

set_option linter.unusedVariables false in
/-- The Bayes factor `p₁/p₀` has `H₀`-expectation exactly `1`. -/
theorem evalue_expectation_eq_one
    (hp0 : Measurable p₀) (hp1 : Measurable p₁)
    (hp0_int : (∫⁻ ω, p₀ ω ∂ν) = 1) (hp1_int : (∫⁻ ω, p₁ ω ∂ν) = 1)
    (hp0_ae : ∀ᵐ ω ∂ν, p₀ ω ≠ 0 ∧ p₀ ω ≠ ∞) :
    (∫⁻ ω, (p₁ ω / p₀ ω) ∂(ν.withDensity p₀)) = 1 := by
  rw [lintegral_withDensity_eq_lintegral_mul ν hp0 (hp1.div hp0), ← hp1_int]
  refine lintegral_congr_ae ?_
  filter_upwards [hp0_ae] with ω hω
  simp only [Pi.mul_apply]
  rw [ENNReal.mul_div_cancel hω.1 hω.2]

/-- `H₀` itself is a probability measure when `p₀` integrates to one. -/
theorem isProbabilityMeasure_withDensity (hp0_int : (∫⁻ ω, p₀ ω ∂ν) = 1) :
    IsProbabilityMeasure (ν.withDensity p₀) :=
  ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hp0_int]⟩

end Densities

/-- **Validity of an e-value** (Markov). If `∫⁻ E ∂P₀ ≤ 1` then rejecting when
`E ≥ 1/α` has size `≤ α`. -/
theorem evalue_markov {Ω : Type*} {mΩ : MeasurableSpace Ω} {P₀ : Measure Ω}
    {E : Ω → ℝ≥0∞} (hE : Measurable E) (hE1 : (∫⁻ ω, E ω ∂P₀) ≤ 1)
    (α : ℝ≥0∞) (hα : α ≠ 0) :
    P₀ {ω | 1 / α ≤ E ω} ≤ α := by
  rcases eq_or_ne α ∞ with hαtop | hαtop
  · rw [hαtop]
    exact le_top
  have h := (mul_meas_ge_le_lintegral₀ hE.aemeasurable (1 / α)).trans hE1
  rw [one_div] at h ⊢
  calc P₀ {ω | α⁻¹ ≤ E ω} = α * (α⁻¹ * P₀ {ω | α⁻¹ ≤ E ω}) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hα hαtop, one_mul]
    _ ≤ α * 1 := by gcongr
    _ = α := mul_one α

section Posterior

variable {c p₀ p₁ κ : ℝ}

/-- The posterior of `H₀` in terms of the e-value: `π = 1/(1 + κE)` with `κ = (1-c)/c`. -/
theorem posterior_eq (hc0 : 0 < c) (hc1 : c < 1) (hp0 : 0 < p₀) (hp1 : 0 ≤ p₁) :
    (c * p₀) / (c * p₀ + (1 - c) * p₁) = 1 / (1 + ((1 - c) / c) * (p₁ / p₀)) := by
  have h1 : 0 < c * p₀ + (1 - c) * p₁ := by
    have : 0 ≤ (1 - c) * p₁ := mul_nonneg (by linarith) hp1
    nlinarith [mul_pos hc0 hp0]
  have h2 : 0 < 1 + ((1 - c) / c) * (p₁ / p₀) := by
    have : 0 ≤ ((1 - c) / c) * (p₁ / p₀) :=
      mul_nonneg (div_nonneg (by linarith) hc0.le) (div_nonneg hp1 hp0.le)
    linarith
  field_simp

/-- The e-value in terms of the posterior: `E = (1/κ)(1-π)/π`. -/
theorem evalue_of_posterior (hc0 : 0 < c) (hc1 : c < 1) (hp0 : 0 < p₀) (hp1 : 0 ≤ p₁) :
    p₁ / p₀ = (c / (1 - c)) * (1 - ((c * p₀) / (c * p₀ + (1 - c) * p₁)))
      / ((c * p₀) / (c * p₀ + (1 - c) * p₁)) := by
  have h1 : 0 < c * p₀ + (1 - c) * p₁ := by
    have : 0 ≤ (1 - c) * p₁ := mul_nonneg (by linarith) hp1
    nlinarith [mul_pos hc0 hp0]
  have hc1' : (1 - c) ≠ 0 := by linarith
  have hD : c * p₀ + (1 - c) * p₁ ≠ 0 := h1.ne'
  have h2 : 1 - c * p₀ / (c * p₀ + (1 - c) * p₁) = (1 - c) * p₁ / (c * p₀ + (1 - c) * p₁) := by
    field_simp
    ring
  rw [h2, eq_comm, div_eq_iff (div_ne_zero (mul_ne_zero hc0.ne' hp0.ne') hD)]
  field_simp

/-- **No paradox:** the posterior `1/(1+κE)` is strictly decreasing in the e-value. -/
theorem posterior_antitone_in_evalue (hκ : 0 < κ) :
    StrictAntiOn (fun e => 1 / (1 + κ * e)) (Set.Ici 0) := by
  intro a ha b _ hab
  have ha' : 0 < 1 + κ * a := by
    have := Set.mem_Ici.mp ha
    nlinarith
  exact one_div_lt_one_div_of_lt ha' (by nlinarith)

/-- A posterior `≥ 1 - β` for `H₀` is the same as an e-value `≤ β / (κ (1 - β))`. -/
theorem posterior_ge_iff (hκ : 0 < κ) {e β : ℝ} (he : 0 ≤ e) (hβ0 : 0 < β) (hβ1 : β < 1) :
    1 - β ≤ 1 / (1 + κ * e) ↔ e ≤ β / (κ * (1 - β)) := by
  have hpos : 0 < 1 + κ * e := by nlinarith
  have hβ : 0 < κ * (1 - β) := mul_pos hκ (by linarith)
  rw [le_div_iff₀ hpos, le_div_iff₀ hβ]
  constructor <;> intro h <;> nlinarith

end Posterior

end EValue
