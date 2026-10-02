/-
Copyright (c) 2026 Patrick Rubin-Delanchy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Rubin-Delanchy, Andrew Jones
AI-generated (see the top-level README); not audited by the authors.
-/
import Mathlib

/-!
# The algebra of (real-valued) e-variables

A valid e-variable for a law `P` is a nonnegative integrable statistic with expectation at
most `1`. Three closure properties, none of which needs any dependence assumption:

* `IsEVariable.sum_smul`, `IsEVariable.average`, `IsEVariable.half_add` — convex combinations
  of e-variables of arbitrary dependence are e-variables;
* `IsEVariable.of_le` — rounding an e-variable downward preserves validity;
* `IsEVariable.markov` — `P(e ≥ c) ≤ 1/c`, the conversion of an e-value into a p-value.

See `PROTOCOL.md`.
-/

open MeasureTheory

namespace EValue

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A valid (real-valued) e-variable for the law `P`: nonnegative, integrable, expectation ≤ 1. -/
structure IsEVariable (P : Measure Ω) (e : Ω → ℝ) : Prop where
  nonneg : ∀ ω, 0 ≤ e ω
  integrable : Integrable e P
  expect_le_one : ∫ ω, e ω ∂P ≤ 1

omit [IsProbabilityMeasure P] in
/-- Convex combinations of e-variables (of arbitrary dependence) are e-variables. -/
theorem IsEVariable.sum_smul {ι : Type*} (s : Finset ι) (w : ι → ℝ) (e : ι → Ω → ℝ)
    (hw0 : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1)
    (he : ∀ i ∈ s, IsEVariable P (e i)) :
    IsEVariable P (fun ω => ∑ i ∈ s, w i * e i ω) where
  nonneg ω := Finset.sum_nonneg fun i hi => mul_nonneg (hw0 i hi) ((he i hi).nonneg ω)
  integrable := integrable_finsetSum _ fun i hi => ((he i hi).integrable).const_mul _
  expect_le_one := by
    rw [integral_finsetSum _ fun i hi => ((he i hi).integrable).const_mul _]
    simp_rw [integral_const_mul]
    calc ∑ i ∈ s, w i * ∫ ω, e i ω ∂P
        ≤ ∑ i ∈ s, w i * 1 := Finset.sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_left (he i hi).expect_le_one (hw0 i hi)
      _ = 1 := by simp [hw1]

omit [IsProbabilityMeasure P] in
/-- The equal-weight average of `k ≥ 1` e-variables is an e-variable. -/
theorem IsEVariable.average {k : ℕ} (hk : 0 < k) (e : Fin k → Ω → ℝ)
    (he : ∀ j, IsEVariable P (e j)) :
    IsEVariable P (fun ω => (∑ j, e j ω) / k) := by
  have hk' : (k : ℝ) ≠ 0 := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    exact this.ne'
  have h := IsEVariable.sum_smul (P := P) Finset.univ (fun _ => (1 : ℝ) / k) e
    (fun _ _ => by positivity) (by simp [Finset.sum_const, Finset.card_univ]; field_simp)
    (fun j _ => he j)
  convert h using 1
  funext ω
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by ring

omit [IsProbabilityMeasure P] in
/-- The average of two e-variables is an e-variable. -/
theorem IsEVariable.half_add {e₁ e₂ : Ω → ℝ} (h₁ : IsEVariable P e₁) (h₂ : IsEVariable P e₂) :
    IsEVariable P (fun ω => (e₁ ω + e₂ ω) / 2) where
  nonneg ω := by
    have := h₁.nonneg ω
    have := h₂.nonneg ω
    positivity
  integrable := (h₁.integrable.add h₂.integrable).div_const 2
  expect_le_one := by
    rw [integral_div, integral_add h₁.integrable h₂.integrable]
    linarith [h₁.expect_le_one, h₂.expect_le_one]

omit [IsProbabilityMeasure P] in
/-- Rounding an e-variable downward preserves validity. -/
theorem IsEVariable.of_le (e e' : Ω → ℝ) (he : IsEVariable P e)
    (hmeas : AEStronglyMeasurable e' P) (h0 : ∀ ω, 0 ≤ e' ω) (hle : ∀ ω, e' ω ≤ e ω) :
    IsEVariable P e' where
  nonneg := h0
  integrable := Integrable.mono' he.integrable hmeas (ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 ω)]
    exact hle ω)
  expect_le_one :=
    le_trans (integral_mono (Integrable.mono' he.integrable hmeas (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (h0 ω)]
      exact hle ω)) he.integrable hle) he.expect_le_one

omit [IsProbabilityMeasure P] in
/-- **Markov:** an e-variable exceeds `c > 0` with probability at most `1/c`. -/
theorem IsEVariable.markov (e : Ω → ℝ) (he : IsEVariable P e) {c : ℝ} (hc : 0 < c) :
    P.real {ω | c ≤ e ω} ≤ 1 / c := by
  have h := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := e) (ae_of_all _ he.nonneg)
    he.integrable c
  rw [div_eq_inv_mul, ← div_eq_inv_mul, le_div_iff₀' hc]
  exact le_trans h he.expect_le_one

/-- Sanity check: with `c = 1/α`, the e-value/p-value conversion `P(e ≥ 1/α) ≤ α`. -/
example (e : Ω → ℝ) (he : IsEVariable P e) {α : ℝ} (hα : 0 < α) :
    P.real {ω | 1 / α ≤ e ω} ≤ α := by
  have h := IsEVariable.markov e he (one_div_pos.mpr hα)
  rwa [one_div_one_div] at h

end EValue
