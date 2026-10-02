/-
Copyright (c) 2026 Patrick Rubin-Delanchy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Rubin-Delanchy, Andrew Jones
-/
import Ols.EValueAlgebra

/-!
# p-to-e calibration

A *p-variable* for `P` is a nonnegative measurable statistic `p` with `P(p ≤ α) ≤ α` for every
`α ∈ [0,1]`. The Vovk–Wang calibrator at `κ = 1/2`, `e = 1 / (2 √p)`, turns any p-variable into
an e-variable (`calibrate_pvalue`): by the layer-cake formula,
`∫ e dP = ∫₀^∞ P(e > t) dt ≤ ∫₀^∞ min(1, 1/(4t²)) dt = 1/2 + 1/2 = 1`.

Convention: Lean's `1 / (2 * √0) = 0`, so `calibrator 0 = 0` rather than `+∞`. This only makes
the e-variable smaller, so validity is unaffected and no positivity hypothesis on `p` is needed.

See `CALIBRATION.md`.
-/

open MeasureTheory Set

namespace EValue

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A p-variable for the law `P`: measurable, nonnegative, and `P(p ≤ α) ≤ α` for every
`α ∈ [0,1]`. -/
structure IsPVariable (P : Measure Ω) (p : Ω → ℝ) : Prop where
  measurable : Measurable p
  nonneg : ∀ ω, 0 ≤ p ω
  valid : ∀ α : ℝ, 0 ≤ α → α ≤ 1 → P.real {ω | p ω ≤ α} ≤ α

/-- The Vovk–Wang calibrator at `κ = 1/2`: `x ↦ 1 / (2 √x)`. Equals `0` at `x = 0` by Lean's
division convention. -/
noncomputable def calibrator (x : ℝ) : ℝ := 1 / (2 * Real.sqrt x)

lemma calibrator_nonneg {x : ℝ} : 0 ≤ calibrator x := by
  unfold calibrator
  exact div_nonneg zero_le_one (mul_nonneg (by norm_num) (Real.sqrt_nonneg x))

lemma measurable_calibrator : Measurable calibrator := by
  unfold calibrator
  fun_prop

/-- **Tail of the calibrated statistic.** For `t > 0`, `{calibrator ∘ p > t} ⊆ {p ≤ 1/(4t²)}`,
so the p-variable property gives `P(calibrator ∘ p > t) ≤ min 1 (1/(4t²))`. -/
theorem calibrator_tail_le [IsProbabilityMeasure P] {p : Ω → ℝ} (hp : IsPVariable P p)
    {t : ℝ} (ht : 0 < t) :
    P.real {ω | t < calibrator (p ω)} ≤ min 1 (1 / (4 * t ^ 2)) := by
  have hsub : {ω | t < calibrator (p ω)} ⊆ {ω | p ω ≤ 1 / (4 * t ^ 2)} := by
    intro ω hω
    rw [Set.mem_setOf_eq] at hω ⊢
    unfold calibrator at hω
    have hp0 : 0 < p ω := by
      by_contra h
      have h0 : p ω = 0 := le_antisymm (not_lt.mp h) (hp.nonneg ω)
      rw [h0, Real.sqrt_zero, mul_zero, div_zero] at hω
      linarith
    have hs : 0 < Real.sqrt (p ω) := Real.sqrt_pos.mpr hp0
    rw [lt_div_iff₀ (by positivity)] at hω
    have h1 : Real.sqrt (p ω) < 1 / (2 * t) := by
      rw [lt_div_iff₀ (by positivity)]
      linarith
    have h2 : p ω < (1 / (2 * t)) ^ 2 := (Real.sqrt_lt' (by positivity)).mp h1
    have h3 : (1 / (2 * t)) ^ 2 = 1 / (4 * t ^ 2) := by
      field_simp
      ring
    rw [h3] at h2
    exact h2.le
  have hle1 : P.real {ω | t < calibrator (p ω)} ≤ 1 :=
    le_trans (measureReal_mono (Set.subset_univ _)) (le_of_eq probReal_univ)
  refine le_min hle1 ?_
  rcases le_or_gt (1 / (4 * t ^ 2)) 1 with h | h
  · exact le_trans (measureReal_mono hsub) (hp.valid _ (by positivity) h)
  · exact le_trans hle1 h.le

/-- **Calibration (Vovk–Wang, κ = 1/2).** A valid p-variable calibrates to a valid e-variable:
`e = 1 / (2 √p)` has `P`-expectation at most `1`. -/
theorem calibrate_pvalue [IsProbabilityMeasure P] {p : Ω → ℝ} (hp : IsPVariable P p) :
    IsEVariable P (fun ω => calibrator (p ω)) := by
  have hmeas : Measurable fun ω => calibrator (p ω) := measurable_calibrator.comp hp.measurable
  have hnn : ∀ ω, 0 ≤ calibrator (p ω) := fun ω => calibrator_nonneg
  -- the layer-cake formula
  have hlayer : ∫⁻ ω, ENNReal.ofReal (calibrator (p ω)) ∂P
      = ∫⁻ t in Ioi 0, P {ω | t < calibrator (p ω)} :=
    lintegral_eq_lintegral_meas_lt P (ae_of_all _ hnn) hmeas.aemeasurable
  -- the pointwise tail bound, in `ℝ≥0∞`
  have hbound : ∀ t ∈ Ioi (0 : ℝ),
      P {ω | t < calibrator (p ω)} ≤ ENNReal.ofReal (min 1 (1 / (4 * t ^ 2))) := by
    intro t ht
    have h := calibrator_tail_le hp (Set.mem_Ioi.mp ht)
    rw [measureReal_def] at h
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _)
      (le_min zero_le_one (by positivity))).mpr h
  -- `∫₀^∞ min(1, 1/(4t²)) dt = 1/2 + 1/2 = 1`
  have hsplit : Ioi (0 : ℝ) = Ioc 0 (1 / 2) ∪ Ioi (1 / 2) :=
    (Ioc_union_Ioi_eq_Ioi (by norm_num)).symm
  have h1 : ∫⁻ t in Ioc (0 : ℝ) (1 / 2), ENNReal.ofReal (min 1 (1 / (4 * t ^ 2)))
      = ENNReal.ofReal (1 / 2) := by
    have hc : ∀ t ∈ Ioc (0 : ℝ) (1 / 2), ENNReal.ofReal (min 1 (1 / (4 * t ^ 2))) = 1 := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have h4 : 4 * t ^ 2 ≤ 1 := by nlinarith [ht.2, ht0]
      have hmin : (1 : ℝ) ≤ 1 / (4 * t ^ 2) := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      rw [min_eq_left hmin, ENNReal.ofReal_one]
    rw [setLIntegral_congr_fun measurableSet_Ioc hc, setLIntegral_const, one_mul, Real.volume_Ioc]
    norm_num
  have h2 : ∫⁻ t in Ioi (1 / 2 : ℝ), ENNReal.ofReal (min 1 (1 / (4 * t ^ 2)))
      = ENNReal.ofReal (1 / 2) := by
    have hc : ∀ t ∈ Ioi (1 / 2 : ℝ), ENNReal.ofReal (min 1 (1 / (4 * t ^ 2)))
        = ENNReal.ofReal (1 / 4 * t ^ (-2 : ℝ)) := by
      intro t ht
      have ht' : 1 / 2 < t := Set.mem_Ioi.mp ht
      have ht0 : 0 < t := by linarith
      have h4 : 1 ≤ 4 * t ^ 2 := by nlinarith
      have hmin : min 1 (1 / (4 * t ^ 2)) = 1 / (4 * t ^ 2) :=
        min_eq_right (by rw [div_le_one (by positivity)]; exact h4)
      rw [hmin, Real.rpow_neg ht0.le, Real.rpow_two]
      congr 1
      field_simp
    rw [setLIntegral_congr_fun measurableSet_Ioi hc]
    have hint : IntegrableOn (fun t : ℝ => 1 / 4 * t ^ (-2 : ℝ)) (Ioi (1 / 2)) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)).const_mul _
    have hnn' : 0 ≤ᵐ[volume.restrict (Ioi (1 / 2 : ℝ))] fun t : ℝ => 1 / 4 * t ^ (-2 : ℝ) :=
      ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
        mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith [Set.mem_Ioi.mp ht]) _)
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn', integral_const_mul,
      integral_Ioi_rpow_of_lt (by norm_num) (by norm_num)]
    congr 1
    rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
    norm_num
  have hcake : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (min 1 (1 / (4 * t ^ 2))) = 1 := by
    rw [hsplit, lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same, h1, h2,
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  have hle : ∫⁻ ω, ENNReal.ofReal (calibrator (p ω)) ∂P ≤ 1 := by
    rw [hlayer, ← hcake]
    exact setLIntegral_mono' measurableSet_Ioi hbound
  have hint_e : Integrable (fun ω => calibrator (p ω)) P := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hnn)]
    exact lt_of_le_of_lt hle ENNReal.one_lt_top
  refine ⟨hnn, hint_e, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn) hmeas.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hle)

/-- Sanity check: the calibrated e-value's Markov test, `P(1/(2√p) ≥ 1/α) ≤ α`. -/
example [IsProbabilityMeasure P] {p : Ω → ℝ} (hp : IsPVariable P p) (α : ℝ) (hα : 0 < α) :
    P.real {ω | 1 / α ≤ calibrator (p ω)} ≤ α := by
  have h := IsEVariable.markov _ (calibrate_pvalue hp) (one_div_pos.mpr hα)
  rwa [one_div_one_div] at h

end EValue
