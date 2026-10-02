/-
Copyright (c) 2026 Patrick Rubin-Delanchy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Rubin-Delanchy, Andrew Jones
-/
import Mathlib
import Ols.Optimality
import Ols.ProjectionCLT

/-!
# The projection parameter is the population least-squares minimiser

Without any independence assumption — second moments only — the estimand
`β⋆ = olsEstimand P X y = (XᵀX)⁻¹ Xᵀ E[y]` minimises `β ↦ E‖y − Xβ‖²`, uniquely:

* `integral_normSq_sub_mulVec` — `E‖y − Xβ‖² = ‖E y − Xβ‖² + ∑ᵢ Var(yᵢ)`;
* `olsEstimand_optimal`, `olsEstimand_unique`.

See `PROTOCOL.md`, Milestone D.
-/

open MeasureTheory ProbabilityTheory Matrix

noncomputable section

namespace Estimand

variable {n p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Bias–variance decomposition of one coordinate: `E(y − c)² = (E y − c)² + Var y`. -/
lemma integral_sq_sub_eq {y : Ω → ℝ} (hy : MemLp y 2 P) (c : ℝ) :
    ∫ ω, (y ω - c) ^ 2 ∂P = (P[y] - c) ^ 2 + variance y P := by
  have hint : Integrable y P := hy.integrable one_le_two
  have hsub : MemLp (fun ω => y ω - P[y]) 2 P := by
    simpa [Pi.sub_def] using hy.sub (memLp_const (P[y]))
  have h2 : Integrable (fun ω => (y ω - P[y]) ^ 2) P := hsub.integrable_sq
  have hzero : ∫ ω, (y ω - P[y]) ∂P = 0 := by
    rw [integral_sub hint (integrable_const _), integral_const]
    simp
  have hexp : (fun ω => (y ω - c) ^ 2)
      = fun ω => (y ω - P[y]) ^ 2 + 2 * (P[y] - c) * (y ω - P[y]) + (P[y] - c) ^ 2 := by
    funext ω
    ring
  have hlin : Integrable (fun ω => 2 * (P[y] - c) * (y ω - P[y])) P :=
    (hint.sub (integrable_const _)).const_mul _
  have hA : Integrable (fun ω => (y ω - P[y]) ^ 2 + 2 * (P[y] - c) * (y ω - P[y])) P :=
    h2.add hlin
  rw [hexp, integral_add hA (integrable_const _), integral_add h2 hlin, integral_const_mul, hzero,
    integral_const, variance_eq_integral hy.aemeasurable]
  simp
  ring

/-- **Second-moment decomposition**: `E‖y − Xβ‖² = ‖E y − Xβ‖² + ∑ᵢ Var(yᵢ)`, for every `β`.
No independence is assumed. -/
theorem integral_normSq_sub_mulVec (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → Ω → ℝ)
    (hy : ∀ i, MemLp (y i) 2 P) (β : Fin p → ℝ) :
    ∫ ω, normSq ((fun i => y i ω) - X *ᵥ β) ∂P
      = normSq (meanVec y P - X *ᵥ β) + ∑ i, variance (y i) P := by
  have hpt : ∀ ω, normSq ((fun i => y i ω) - X *ᵥ β) = ∑ i, (y i ω - (X *ᵥ β) i) ^ 2 := by
    intro ω
    rw [normSq_eq_sum_sq]
    rfl
  have hint : ∀ i, Integrable (fun ω => (y i ω - (X *ᵥ β) i) ^ 2) P := fun i => by
    simpa [Pi.sub_def] using ((hy i).sub (memLp_const ((X *ᵥ β) i))).integrable_sq
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun i _ => hint i), normSq_eq_sum_sq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_sq_sub_eq (hy i)]
  rfl

/-- **Optimality of the estimand**: `β⋆ = olsEstimand P X y` minimises `E‖y − Xβ‖²`. -/
theorem olsEstimand_optimal (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → Ω → ℝ)
    (hy : ∀ i, MemLp (y i) 2 P) (hX_inv : IsUnit (Xᵀ * X).det) (β : Fin p → ℝ) :
    ∫ ω, normSq ((fun i => y i ω) - X *ᵥ olsEstimand P X y) ∂P
      ≤ ∫ ω, normSq ((fun i => y i ω) - X *ᵥ β) ∂P := by
  rw [integral_normSq_sub_mulVec X y hy, integral_normSq_sub_mulVec X y hy]
  have h := olsEstimator_optimal X (meanVec y P) hX_inv β
  unfold olsEstimand
  linarith

/-- **Uniqueness**: the population least-squares minimiser is `β⋆`. -/
theorem olsEstimand_unique (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → Ω → ℝ)
    (hy : ∀ i, MemLp (y i) 2 P) (hX_inv : IsUnit (Xᵀ * X).det) (β : Fin p → ℝ) :
    ∫ ω, normSq ((fun i => y i ω) - X *ᵥ β) ∂P
        = ∫ ω, normSq ((fun i => y i ω) - X *ᵥ olsEstimand P X y) ∂P
      ↔ β = olsEstimand P X y := by
  rw [integral_normSq_sub_mulVec X y hy, integral_normSq_sub_mulVec X y hy, add_left_inj]
  unfold olsEstimand
  exact olsEstimator_unique X (meanVec y P) β hX_inv

end Estimand

end
