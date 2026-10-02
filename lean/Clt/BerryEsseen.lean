/-
Copyright (c) 2026 Patrick Rubin-Delanchy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Rubin-Delanchy, Andrew Jones
-/
import Clt.LindebergCLT
import Mathlib.Probability.CDF

/-!
# Berry–Esseen bound (placeholder) and its triangular-array consequences

This file states a uniform third-moment Berry–Esseen bound as a placeholder (`sorry`), and derives
from it the finite-`n` quantitative statements used by the quantitative (finite-sample) analysis of
the OLS t-test: a Kolmogorov-distance bound for the normalised triangular-array sum
`LindebergSumTriangular`, and a two-sided tail-probability bound in the shape consumed by
`Ols/TTest.lean` (compare `AssumptionBundle.olsArray_tail_tendsto`, which provides the asymptotic
analogue).

The placeholder `uniformBerryEsseen_thirdMoment` mirrors, statement for statement, the theorem
`ProbabilityTheory.uniformBerryEsseen_thirdMoment` of the Lean 4 library
Polarnova/ProbabilityApproximation (v0.9.6, Lean v4.32.0), which is proved there sorry-free with
the explicit constant `30`, from Stein's method following Chen–Shao:
<https://github.com/Polarnova/ProbabilityApproximation>.
The intended discharge of the `sorry` is to port that proof (or depend on that library) once this
project moves to a compatible toolchain; only the statement below is relied upon.

## Main statements

· `uniformBerryEsseen_thirdMoment` — placeholder: for independent centred real random variables
  over a finite index set, with variances summing to `1` and finite third absolute moments,
  `|F(x) - Φ(x)| ≤ 30 · ∑ₖ E|Xₖ|³` for every `x`.
· `berryEsseen_triangular_thirdMoment` — the same bound for the normalised row sum
  `Sₙ/sₙ = LindebergSumTriangular X P n`, with third-moment ratio
  `γₙ = (∑ₖ E|X_{n,k}|³)/sₙ³`; derived from the placeholder by standardising the row.
· `berryEsseen_triangular_tail_bound` — finite-`n` two-sided tail bound:
  `P{z < |Sₙ/sₙ|} ≤ N(0,1){z < |x|} + 2 · 30 · γₙ`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset Set
open scoped Real Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The explicit numerical constant in the uniform third-moment Berry–Esseen bound
`uniformBerryEsseen_thirdMoment`. -/
def thirdMomentBerryEsseenConstant : ℝ := 30

/-- PLACEHOLDER (`sorry`). Uniform Berry–Esseen bound with explicit constant `30`, for an
independent family of centred real random variables over a finite index set, with unit total
variance and finite third absolute moments. Mirrors the theorem
`ProbabilityTheory.uniformBerryEsseen_thirdMoment` proved (sorry-free) in
Polarnova/ProbabilityApproximation v0.9.6. -/
theorem uniformBerryEsseen_thirdMoment {ι : Type*} [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ι → Ω → ℝ}
    (hX : ∀ k, MemLp (X k) 2 P) (hXmeas : ∀ k, Measurable (X k))
    (h_indep : iIndepFun X P) (h_mean : ∀ k, ∫ ω, X k ω ∂P = 0)
    (hvar : ∑ k, variance (X k) P = 1)
    (h3 : ∀ k, Integrable (fun ω => |X k ω| ^ 3) P) (x : ℝ) :
    |cdf (P.map fun ω ↦ ∑ k, X k ω) x - cdf (gaussianReal 0 1) x| ≤
      thirdMomentBerryEsseenConstant * ∑ k, ∫ ω, |X k ω| ^ 3 ∂P := by
  sorry

section TriangularArray

variable {X : (n : ℕ) → Fin n → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ}

/-- The standardised third-moment ratio `γₙ = (∑ₖ E|X_{n,k}|³)/sₙ³` of row `n` of a triangular
array, where `sₙ² = momentSumTriangular X P n`. -/
def thirdMomentRatioTriangular (X : (n : ℕ) → Fin n → Ω → ℝ) (P : Measure Ω) (n : ℕ) : ℝ :=
  (∑ k, ∫ ω, |X n k ω| ^ 3 ∂P) / √(momentSumTriangular X P n) ^ 3

/-- Berry–Esseen bound for the normalised triangular-array row sum `Sₙ/sₙ`: at every `x`,
`|F_{Sₙ/sₙ}(x) - Φ(x)| ≤ 30 γₙ`. Derived from `uniformBerryEsseen_thirdMoment` by standardising
the row `X_{n,·}/sₙ`. -/
theorem berryEsseen_triangular_thirdMoment
    (hX_meas : ∀ k, Measurable (X n k))
    (hX_ind : iIndepFun (X n) P)
    (hX_centred : ∀ k, P[X n k] = 0)
    (hX_MemL2 : ∀ k, MemLp (X n k) 2 P)
    (h3 : ∀ k, Integrable (fun ω => |X n k ω| ^ 3) P)
    (hmSum_pos : 0 < momentSumTriangular X P n) (x : ℝ) :
    |cdf (P.map (LindebergSumTriangular X P n)) x - cdf (gaussianReal 0 1) x| ≤
      thirdMomentBerryEsseenConstant * thirdMomentRatioTriangular X P n := by
  set s : ℝ := √(momentSumTriangular X P n) with hs_def
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hmSum_pos
  set X' : Fin n → Ω → ℝ := fun k ω => s⁻¹ * X n k ω with hX'_def
  have hX'_meas : ∀ k, Measurable (X' k) := fun k => (hX_meas k).const_mul _
  have hX'_L2 : ∀ k, MemLp (X' k) 2 P := fun k => (hX_MemL2 k).const_mul _
  have hX'_ind : iIndepFun X' P :=
    hX_ind.comp (fun _ y => s⁻¹ * y) fun _ => measurable_const_mul _
  have hX'_mean : ∀ k, ∫ ω, X' k ω ∂P = 0 := fun k => by
    simp [hX'_def, integral_const_mul, hX_centred k]
  have hX'_var : ∑ k, variance (X' k) P = 1 := by
    have hv : ∀ k, variance (X' k) P = s⁻¹ ^ 2 * P[(X n k) ^ 2] := fun k => by
      rw [hX'_def, variance_const_mul, variance_eq_sub (hX_MemL2 k), hX_centred k]
      ring
    rw [Finset.sum_congr rfl fun k _ => hv k, ← Finset.mul_sum]
    have hss : s ^ 2 = momentSumTriangular X P n := Real.sq_sqrt hmSum_pos.le
    field_simp
    linarith [hss]
  have h3' : ∀ k, Integrable (fun ω => |X' k ω| ^ 3) P := fun k => by
    have habs : (fun ω => |X' k ω| ^ 3) = fun ω => |s⁻¹| ^ 3 * |X n k ω| ^ 3 := by
      funext ω
      rw [hX'_def]
      rw [abs_mul, mul_pow]
    rw [habs]
    exact (h3 k).const_mul _
  have hsum_eq : (fun ω => ∑ k, X' k ω) = LindebergSumTriangular X P n := by
    funext ω
    simp only [hX'_def, ← Finset.mul_sum]
    rw [inv_mul_eq_div]
  have hBE := uniformBerryEsseen_thirdMoment hX'_L2 hX'_meas hX'_ind hX'_mean hX'_var h3' x
  rw [hsum_eq] at hBE
  refine hBE.trans (le_of_eq ?_)
  congr 1
  have hI : ∀ k, ∫ ω, |X' k ω| ^ 3 ∂P = s⁻¹ ^ 3 * ∫ ω, |X n k ω| ^ 3 ∂P := fun k => by
    have habs : (fun ω => |X' k ω| ^ 3) = fun ω => s⁻¹ ^ 3 * |X n k ω| ^ 3 := by
      funext ω
      rw [hX'_def, abs_mul, mul_pow, abs_of_pos (inv_pos.mpr hs_pos)]
    rw [habs, integral_const_mul]
  rw [Finset.sum_congr rfl fun k _ => hI k, ← Finset.mul_sum, thirdMomentRatioTriangular]
  rw [inv_pow, inv_mul_eq_div]

/-- Finite-`n` two-sided tail bound for the normalised triangular-array row sum: for `z > 0`,
`P{z < |Sₙ/sₙ|} ≤ N(0,1){z < |x|} + 2 · 30 · γₙ`. This is the quantitative counterpart of the
limit statement provided by the portmanteau step in `Ols/TTest.lean`
(`tendsto_measure_abs_gt_of_tendsto_stdGaussian`), with the CLT hypothesis replaced by the
Berry–Esseen bound; no limits are involved. -/
theorem berryEsseen_triangular_tail_bound
    (hX_meas : ∀ k, Measurable (X n k))
    (hX_ind : iIndepFun (X n) P)
    (hX_centred : ∀ k, P[X n k] = 0)
    (hX_MemL2 : ∀ k, MemLp (X n k) 2 P)
    (h3 : ∀ k, Integrable (fun ω => |X n k ω| ^ 3) P)
    (hmSum_pos : 0 < momentSumTriangular X P n) {z : ℝ} (hz : 0 < z) :
    P.real {ω | z < |LindebergSumTriangular X P n ω|} ≤
      (gaussianReal 0 1).real {x : ℝ | z < |x|} +
        2 * thirdMomentBerryEsseenConstant * thirdMomentRatioTriangular X P n := by
  set μ : Measure ℝ := P.map (LindebergSumTriangular X P n) with hμ_def
  have hZ_meas : Measurable (LindebergSumTriangular X P n) := by fun_prop
  haveI : IsProbabilityMeasure μ := P.isProbabilityMeasure_map hZ_meas.aemeasurable
  set γ : ℝ := thirdMomentRatioTriangular X P n with hγ_def
  set C : ℝ := thirdMomentBerryEsseenConstant with hC_def
  have hBE : ∀ x : ℝ, |cdf μ x - cdf (gaussianReal 0 1) x| ≤ C * γ := fun x =>
    berryEsseen_triangular_thirdMoment hX_meas hX_ind hX_centred hX_MemL2 h3 hmSum_pos x
  -- Rewrite the event as a set of the pushforward measure.
  have hset : {x : ℝ | z < |x|} = Iio (-z) ∪ Ioi z := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi, lt_abs, lt_neg]
    tauto
  have hmap : P.real {ω | z < |LindebergSumTriangular X P n ω|} = μ.real {x : ℝ | z < |x|} := by
    rw [hμ_def, measureReal_def, measureReal_def, Measure.map_apply hZ_meas
      (measurableSet_lt measurable_const continuous_abs.measurable)]
    rfl
  -- Upper bound each half-line of the pushforward by cdf values.
  have h_left : μ.real (Iio (-z)) ≤ cdf (gaussianReal 0 1) (-z) + C * γ := by
    have h1 : μ.real (Iio (-z)) ≤ μ.real (Iic (-z)) :=
      measureReal_mono Iio_subset_Iic_self
    have h2 : μ.real (Iic (-z)) = cdf μ (-z) := (cdf_eq_real μ (-z)).symm
    have h3' := (abs_le.mp (hBE (-z))).2
    linarith
  have h_right : μ.real (Ioi z) ≤ (1 - cdf (gaussianReal 0 1) z) + C * γ := by
    have hcompl : μ.real (Ioi z) = 1 - μ.real (Iic z) := by
      have := measureReal_compl (μ := μ) (s := Iic z) measurableSet_Iic
      simpa [compl_Iic] using this
    have h2 : μ.real (Iic z) = cdf μ z := (cdf_eq_real μ z).symm
    have h3' := (abs_le.mp (hBE z)).1
    linarith
  -- The Gaussian tail decomposes exactly.
  haveI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal (by norm_num)
  have h_gauss : (gaussianReal 0 1).real {x : ℝ | z < |x|} =
      cdf (gaussianReal 0 1) (-z) + (1 - cdf (gaussianReal 0 1) z) := by
    have hdisj : Disjoint (Iio (-z)) (Ioi z) :=
      (Iic_disjoint_Ioi (by linarith : -z ≤ z)).mono Iio_subset_Iic_self le_rfl
    have h_union : (gaussianReal 0 1).real (Iio (-z) ∪ Ioi z) =
        (gaussianReal 0 1).real (Iio (-z)) + (gaussianReal 0 1).real (Ioi z) :=
      measureReal_union hdisj measurableSet_Ioi
    have h_iio : (gaussianReal 0 1).real (Iio (-z)) = cdf (gaussianReal 0 1) (-z) := by
      rw [measureReal_congr (Iio_ae_eq_Iic (a := -z)), cdf_eq_real]
    have h_ioi : (gaussianReal 0 1).real (Ioi z) = 1 - cdf (gaussianReal 0 1) z := by
      have := measureReal_compl (μ := gaussianReal 0 1) (s := Iic z) measurableSet_Iic
      rw [cdf_eq_real]
      simpa [compl_Iic] using this
    rw [hset, h_union, h_iio, h_ioi]
  -- Assemble.
  have h_sub : μ.real {x : ℝ | z < |x|} ≤ μ.real (Iio (-z)) + μ.real (Ioi z) := by
    rw [hset]
    exact measureReal_union_le _ _
  rw [hmap]
  calc μ.real {x : ℝ | z < |x|} ≤ μ.real (Iio (-z)) + μ.real (Ioi z) := h_sub
    _ ≤ (cdf (gaussianReal 0 1) (-z) + C * γ) + ((1 - cdf (gaussianReal 0 1) z) + C * γ) :=
        add_le_add h_left h_right
    _ = (gaussianReal 0 1).real {x : ℝ | z < |x|} + 2 * C * γ := by rw [h_gauss]; ring

end TriangularArray
