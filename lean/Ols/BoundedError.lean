/-
Copyright (c) 2026 Patrick Rubin-Delanchy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Rubin-Delanchy, Andrew Jones
AI-generated (see the top-level README); not audited by the authors.
-/
import Mathlib
import Ols.FiniteN

/-!
# The bounded-error route: Hoeffding and Bernstein p-value bounds for a linear contrast

Under the null `a^\top β^\star = 0`, the numerator of the contrast statistic is exactly the
weighted error sum `N = ∑ i, γ i * ε i` (misspecification-robust: since `X^\top r = 0`, the
mean-residual `r` never enters `N`). If the analyst declares a known error bound `|ε_i| ≤ B_i`
(Hoeffding) and, in addition, a known variance bound `Var(ε_i) ≤ s_i^2` (Bernstein), then
elementary concentration gives a certified p-value for `N`, with NO variance estimation, NO
Berry–Esseen, and NO symmetry assumption.

* Hoeffding: `P(|N| ≥ u) ≤ 2 exp(-u^2 / (2 ∑ i (γ_i B_i)^2))`.
* Bernstein: `P(|N| ≥ u) ≤ 2 exp(-u^2 / (2 (∑ i (γ_i s_i)^2 + M u / 3)))`, `M ≥ maxᵢ |γ_i| B_i`.

The Hoeffding version assembles from Mathlib's sub-Gaussian machinery
(`Mathlib/Probability/Moments/SubGaussian.lean`); the Bernstein version needs a Bennett-type
sub-gamma MGF bound, proved here (Mathlib has no Bernstein/Bennett at present). The Bennett
bound rests on the elementary pointwise inequality `(3 - y) exp y ≤ 3 + 2y + y²/2`, valid for
every real `y`, proved by two monotonicity passes (its second derivative is
`1 - (1 - y) exp y ≥ 0`, a rearrangement of `1 - y ≤ exp (-y)`); no power series is needed.

Milestone C connects this to the OLS contrast: with `γ = olsWeights X a` and
`ε = centredErr P y`, the numerator `aᵀ(β̂ − β⋆) = contrastDiff P X y a` (see `Ols/FiniteN.lean`)
is exactly `wsum γ ε`, so `hoeffding_contrast` / `bernstein_contrast` are certified p-values for a
regression coefficient under declared error bounds.

See `BOUNDED_ERROR.md` for the full proof plan and the working protocol.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace BoundedError

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The deterministic-weighted error sum `N(ω) = ∑ i, γ i * ε i ω`, whose law is the numerator
of the contrast statistic under the null. -/
noncomputable def wsum {n : ℕ} (γ : Fin n → ℝ) (ε : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i, γ i * ε i ω

lemma wsum_neg {n : ℕ} (γ : Fin n → ℝ) (ε : Fin n → Ω → ℝ) (ω : Ω) :
    wsum (-γ) ε ω = -wsum γ ε ω := by
  simp [wsum, Finset.sum_neg_distrib]

/-- Two-sided tail from the two one-sided tails, via the sign flip `γ ↦ -γ`. -/
private lemma two_sided_of_one_sided {n : ℕ} {γ : Fin n → ℝ} {ε : Fin n → Ω → ℝ} {u b : ℝ}
    [IsFiniteMeasure P]
    (h₁ : P.real {ω | u ≤ wsum γ ε ω} ≤ b) (h₂ : P.real {ω | u ≤ wsum (-γ) ε ω} ≤ b) :
    P.real {ω | u ≤ |wsum γ ε ω|} ≤ 2 * b := by
  have hsub : {ω | u ≤ |wsum γ ε ω|} ⊆ {ω | u ≤ wsum γ ε ω} ∪ {ω | u ≤ wsum (-γ) ε ω} := by
    intro ω hω
    rw [Set.mem_setOf_eq, le_abs] at hω
    rw [Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq, wsum_neg]
    exact hω
  calc P.real {ω | u ≤ |wsum γ ε ω|}
      ≤ P.real ({ω | u ≤ wsum γ ε ω} ∪ {ω | u ≤ wsum (-γ) ε ω}) := measureReal_mono hsub
    _ ≤ P.real {ω | u ≤ wsum γ ε ω} + P.real {ω | u ≤ wsum (-γ) ε ω} :=
        measureReal_union_le _ _
    _ ≤ 2 * b := by linarith

/-- Independence of the weighted errors. -/
private lemma iIndepFun_weighted {n : ℕ} (γ : Fin n → ℝ) {ε : Fin n → Ω → ℝ}
    (hindep : iIndepFun ε P) : iIndepFun (fun i ω => γ i * ε i ω) P := by
  have h := hindep.comp (fun i (x : ℝ) => γ i * x) (fun i => measurable_const_mul (γ i))
  exact h

section Hoeffding

/-- Each weighted error is sub-Gaussian with proxy `(γ i B i)^2` (Hoeffding's lemma). -/
private lemma hasSubgaussianMGF_weighted {n : ℕ} (γ B : Fin n → ℝ) (ε : Fin n → Ω → ℝ)
    [IsProbabilityMeasure P]
    (hmeas : ∀ i, Measurable (ε i)) (hmean : ∀ i, ∫ ω, ε i ω ∂P = 0)
    (hbdd : ∀ i ω, |ε i ω| ≤ B i) (i : Fin n) :
    HasSubgaussianMGF (fun ω => γ i * ε i ω)
      ((‖(|γ i| * B i) - (-(|γ i| * B i))‖₊ / 2) ^ 2) P := by
  refine hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero ((hmeas i).const_mul _).aemeasurable
    (ae_of_all _ fun ω => ?_) ?_
  · have h : |γ i * ε i ω| ≤ |γ i| * B i := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hbdd i ω) (abs_nonneg _)
    exact abs_le.mp h
  · simp [integral_const_mul, hmean i]

/-- The Hoeffding proxy, coerced to `ℝ`, is `(γ i B i)^2`. -/
private lemma proxy_eq (g b : ℝ) :
    ((((‖(|g| * b) - (-(|g| * b))‖₊ / 2) ^ 2 : ℝ≥0)) : ℝ) = (g * b) ^ 2 := by
  have h : |g| * b - (-(|g| * b)) = 2 * (|g| * b) := by ring
  rw [h]
  push_cast
  rw [Real.norm_eq_abs, div_pow, sq_abs, mul_pow, mul_pow, sq_abs]
  ring

/-- One-sided Hoeffding tail. -/
private lemma hoeffding_one_tail {n : ℕ} (γ B : Fin n → ℝ) (ε : Fin n → Ω → ℝ)
    [IsProbabilityMeasure P]
    (hmeas : ∀ i, Measurable (ε i)) (hindep : iIndepFun ε P)
    (hmean : ∀ i, ∫ ω, ε i ω ∂P = 0) (hbdd : ∀ i ω, |ε i ω| ≤ B i)
    {u : ℝ} (hu : 0 ≤ u) :
    P.real {ω | u ≤ wsum γ ε ω} ≤ Real.exp (-u ^ 2 / (2 * ∑ i, (γ i * B i) ^ 2)) := by
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (iIndepFun_weighted γ hindep)
    (s := Finset.univ)
    (fun i _ => hasSubgaussianMGF_weighted γ B ε hmeas hmean hbdd i) hu
  refine le_trans h (le_of_eq ?_)
  congr 2
  rw [NNReal.coe_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => proxy_eq (γ i) (B i)

/-- **Hoeffding's route.** For independent, mean-zero errors bounded by `|ε_i| ≤ B_i`, the
weighted sum concentrates sub-Gaussianly with proxy `∑ i (γ_i B_i)^2`. -/
theorem hoeffding_tail {n : ℕ} (γ B : Fin n → ℝ) (ε : Fin n → Ω → ℝ)
    [IsProbabilityMeasure P]
    (hmeas : ∀ i, Measurable (ε i)) (hindep : iIndepFun ε P)
    (hmean : ∀ i, ∫ ω, ε i ω ∂P = 0) (hbdd : ∀ i ω, |ε i ω| ≤ B i)
    {u : ℝ} (hu : 0 ≤ u) :
    P.real {ω | u ≤ |wsum γ ε ω|}
      ≤ 2 * Real.exp (-u ^ 2 / (2 * ∑ i, (γ i * B i) ^ 2)) := by
  refine two_sided_of_one_sided (hoeffding_one_tail γ B ε hmeas hindep hmean hbdd hu) ?_
  have h := hoeffding_one_tail (-γ) B ε hmeas hindep hmean hbdd hu
  simpa [neg_mul, neg_sq] using h

end Hoeffding

section Bernstein

/-! ### The elementary inequality behind Bennett's bound -/

/-- `(1 - y) exp y ≤ 1` for every real `y` (rearrangement of `1 - y ≤ exp (-y)`). -/
private lemma one_sub_mul_exp_le (y : ℝ) : (1 - y) * Real.exp y ≤ 1 := by
  have h := Real.add_one_le_exp (-y)
  have hpos := Real.exp_pos y
  have h2 : (1 - y) * Real.exp y ≤ Real.exp (-y) * Real.exp y :=
    mul_le_mul_of_nonneg_right (by linarith) hpos.le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h2
  exact h2

/-- The auxiliary function `g'(y) = 2 + y - (2 - y) exp y`. -/
private noncomputable def gAux1 (y : ℝ) : ℝ := 2 + y - (2 - y) * Real.exp y

/-- The auxiliary function `g(y) = 3 + 2y + y²/2 - (3 - y) exp y`. -/
private noncomputable def gAux (y : ℝ) : ℝ := 3 + 2 * y + y ^ 2 / 2 - (3 - y) * Real.exp y

private lemma hasDerivAt_gAux1 (y : ℝ) : HasDerivAt gAux1 (1 - (1 - y) * Real.exp y) y := by
  have h : HasDerivAt (fun y => 2 + y - (2 - y) * Real.exp y)
      (0 + 1 - ((0 - 1) * Real.exp y + (2 - y) * Real.exp y)) y :=
    ((hasDerivAt_const y (2 : ℝ)).add (hasDerivAt_id y)).sub
      (((hasDerivAt_const y (2 : ℝ)).sub (hasDerivAt_id y)).mul (Real.hasDerivAt_exp y))
  exact h.congr_deriv (by ring)

private lemma hasDerivAt_gAux (y : ℝ) : HasDerivAt gAux (gAux1 y) y := by
  have h : HasDerivAt (fun y => 3 + 2 * y + y ^ 2 / 2 - (3 - y) * Real.exp y)
      (0 + 2 * 1 + (2 * y ^ 1 * 1) / 2 - ((0 - 1) * Real.exp y + (3 - y) * Real.exp y)) y :=
    (((hasDerivAt_const y (3 : ℝ)).add ((hasDerivAt_id y).const_mul 2)).add
      (((hasDerivAt_id y).pow 2).div_const 2)).sub
      (((hasDerivAt_const y (3 : ℝ)).sub (hasDerivAt_id y)).mul (Real.hasDerivAt_exp y))
  exact h.congr_deriv (by simp [gAux1]; ring)

/-- `g'` is monotone, since `g'' = 1 - (1 - y) exp y ≥ 0`. -/
private lemma gAux1_monotone : Monotone gAux1 :=
  monotone_of_deriv_nonneg (fun y => (hasDerivAt_gAux1 y).differentiableAt) fun y => by
    rw [(hasDerivAt_gAux1 y).deriv]
    linarith [one_sub_mul_exp_le y]

private lemma gAux1_zero : gAux1 0 = 0 := by simp [gAux1]

private lemma gAux_zero : gAux 0 = 0 := by simp [gAux]

/-- The key inequality: `(3 - y) exp y ≤ 3 + 2y + y²/2` for every real `y`. -/
private lemma key_ineq (y : ℝ) : (3 - y) * Real.exp y ≤ 3 + 2 * y + y ^ 2 / 2 := by
  have hcont : Continuous gAux := by
    unfold gAux
    fun_prop
  have hdiff : Differentiable ℝ gAux := fun y => (hasDerivAt_gAux y).differentiableAt
  have hg : 0 ≤ gAux y := by
    rcases le_or_gt 0 y with hy | hy
    · have hmono : MonotoneOn gAux (Set.Ici 0) := by
        refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont.continuousOn
          hdiff.differentiableOn fun x hx => ?_
        rw [interior_Ici] at hx
        rw [(hasDerivAt_gAux x).deriv, ← gAux1_zero]
        exact gAux1_monotone (le_of_lt hx)
      have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy) hy
      rwa [gAux_zero] at this
    · have hanti : AntitoneOn gAux (Set.Iic 0) := by
        refine antitoneOn_of_deriv_nonpos (convex_Iic 0) hcont.continuousOn
          hdiff.differentiableOn fun x hx => ?_
        rw [interior_Iic] at hx
        rw [(hasDerivAt_gAux x).deriv, ← gAux1_zero]
        exact gAux1_monotone (le_of_lt hx)
      have := hanti (Set.mem_Iic.mpr hy.le) (Set.mem_Iic.mpr le_rfl) hy.le
      rwa [gAux_zero] at this
  simp only [gAux] at hg
  linarith

/-- Bennett's pointwise inequality: for `|y| ≤ c < 3`,
`exp y ≤ 1 + y + y² / (2 (1 - c/3))`. -/
private lemma exp_le_of_abs_le {y c : ℝ} (hy : |y| ≤ c) (hc : c < 3) :
    Real.exp y ≤ 1 + y + y ^ 2 / (2 * (1 - c / 3)) := by
  have hyc : y ≤ c := le_trans (le_abs_self y) hy
  have h3y : 0 < 3 - y := by linarith
  have h1 : Real.exp y ≤ (3 + 2 * y + y ^ 2 / 2) / (3 - y) := by
    rw [le_div_iff₀ h3y]
    linarith [key_ineq y]
  have h2 : (3 + 2 * y + y ^ 2 / 2) / (3 - y) = 1 + y + y ^ 2 / (2 * (1 - y / 3)) := by
    field_simp
    ring
  have h3 : y ^ 2 / (2 * (1 - y / 3)) ≤ y ^ 2 / (2 * (1 - c / 3)) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by linarith) (by linarith)
  linarith

/-- Integrability of a bounded measurable function on a finite measure space. -/
private lemma integrable_of_bdd [IsFiniteMeasure P] {f : Ω → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ ω, |f ω| ≤ C) : Integrable f P :=
  (memLp_top_of_bound hf.aestronglyMeasurable C (ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs]; exact hC ω)).integrable le_top

set_option linter.unusedVariables false in
/-- **Bennett sub-gamma MGF bound.** For a mean-zero variable with `|Z| ≤ M` and
`∫ Z^2 ≤ v`, and `0 ≤ t < 3 / M`, the moment-generating function satisfies
`mgf Z P t ≤ exp (t^2 v / (2 (1 - t M / 3)))`. This is the ingredient Mathlib lacks. -/
theorem bennett_mgf_le [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZmeas : Measurable Z)
    {M v : ℝ} (hM : 0 < M) (hbdd : ∀ ω, |Z ω| ≤ M) (hmean : ∫ ω, Z ω ∂P = 0)
    (hvar : ∫ ω, (Z ω) ^ 2 ∂P ≤ v) {t : ℝ} (ht0 : 0 ≤ t) (htM : t * M < 3) :
    mgf Z P t ≤ Real.exp (t ^ 2 * v / (2 * (1 - t * M / 3))) := by
  set K : ℝ := t ^ 2 / (2 * (1 - t * M / 3)) with hK_def
  have hden : 0 < 1 - t * M / 3 := by linarith
  have hK : 0 ≤ K := div_nonneg (sq_nonneg _) (by linarith)
  have hpt : ∀ ω, Real.exp (t * Z ω) ≤ 1 + t * Z ω + K * Z ω ^ 2 := by
    intro ω
    have h : |t * Z ω| ≤ t * M := by
      rw [abs_mul, abs_of_nonneg ht0]
      exact mul_le_mul_of_nonneg_left (hbdd ω) ht0
    have := exp_le_of_abs_le h htM
    have heq : (t * Z ω) ^ 2 / (2 * (1 - t * M / 3)) = K * Z ω ^ 2 := by
      rw [hK_def]
      ring
    linarith
  have hZint : Integrable Z P := integrable_of_bdd hZmeas hbdd
  have hZ2int : Integrable (fun ω => Z ω ^ 2) P :=
    integrable_of_bdd (hZmeas.pow_const 2) (C := M ^ 2) fun ω => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hbdd ω) 2
  have hexpint : Integrable (fun ω => Real.exp (t * Z ω)) P :=
    integrable_of_bdd (by fun_prop) (C := Real.exp (t * M)) fun ω => by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (hbdd ω)) ht0)
  have hlin : Integrable (fun ω => 1 + t * Z ω) P := (integrable_const 1).add (hZint.const_mul t)
  have hrhs : Integrable (fun ω => 1 + t * Z ω + K * Z ω ^ 2) P := hlin.add (hZ2int.const_mul K)
  calc mgf Z P t = ∫ ω, Real.exp (t * Z ω) ∂P := rfl
    _ ≤ ∫ ω, 1 + t * Z ω + K * Z ω ^ 2 ∂P := integral_mono hexpint hrhs hpt
    _ = 1 + t * ∫ ω, Z ω ∂P + K * ∫ ω, Z ω ^ 2 ∂P := by
        rw [integral_add hlin (hZ2int.const_mul K), integral_add (integrable_const 1)
          (hZint.const_mul t), integral_const_mul, integral_const_mul, integral_const]
        simp
    _ ≤ 1 + K * v := by
        rw [hmean, mul_zero, add_zero]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hvar hK)
    _ ≤ Real.exp (K * v) := by linarith [Real.add_one_le_exp (K * v)]
    _ = Real.exp (t ^ 2 * v / (2 * (1 - t * M / 3))) := by
        rw [hK_def]
        ring_nf

/-- The MGF of the weighted sum, bounded via Bennett's lemma applied to each term. -/
private lemma mgf_wsum_le {n : ℕ} (γ B s : Fin n → ℝ) (ε : Fin n → Ω → ℝ)
    [IsProbabilityMeasure P]
    (hmeas : ∀ i, Measurable (ε i)) (hindep : iIndepFun ε P)
    (hmean : ∀ i, ∫ ω, ε i ω ∂P = 0) (hbdd : ∀ i ω, |ε i ω| ≤ B i)
    (hvar : ∀ i, ∫ ω, (ε i ω) ^ 2 ∂P ≤ (s i) ^ 2)
    {M : ℝ} (hMpos : 0 < M) (hM : ∀ i, |γ i| * B i ≤ M) {t : ℝ} (ht0 : 0 ≤ t)
    (htM : t * M < 3) :
    mgf (wsum γ ε) P t
      ≤ Real.exp (t ^ 2 * (∑ i, (γ i * s i) ^ 2) / (2 * (1 - t * M / 3))) := by
  have hZmeas : ∀ i, Measurable (fun ω => γ i * ε i ω) := fun i => (hmeas i).const_mul _
  have hsum : wsum γ ε = ∑ i, fun ω => γ i * ε i ω := by
    funext ω
    simp [wsum, Finset.sum_apply]
  have hbennett : ∀ i, mgf (fun ω => γ i * ε i ω) P t
      ≤ Real.exp (t ^ 2 * (γ i * s i) ^ 2 / (2 * (1 - t * M / 3))) := by
    intro i
    refine bennett_mgf_le (hZmeas i) hMpos (fun ω => ?_) ?_ ?_ ht0 htM
    · rw [abs_mul]
      exact le_trans (mul_le_mul_of_nonneg_left (hbdd i ω) (abs_nonneg _)) (hM i)
    · simp [integral_const_mul, hmean i]
    · simp only [mul_pow, integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hvar i) (sq_nonneg _)
  rw [hsum, (iIndepFun_weighted γ hindep).mgf_sum hZmeas Finset.univ]
  calc ∏ i, mgf (fun ω => γ i * ε i ω) P t
      ≤ ∏ i, Real.exp (t ^ 2 * (γ i * s i) ^ 2 / (2 * (1 - t * M / 3))) :=
        Finset.prod_le_prod (fun i _ => mgf_nonneg) fun i _ => hbennett i
    _ = Real.exp (t ^ 2 * (∑ i, (γ i * s i) ^ 2) / (2 * (1 - t * M / 3))) := by
        rw [← Real.exp_sum, Finset.mul_sum, Finset.sum_div]

/-- **Bernstein mgf bound** (public form of `mgf_wsum_le`): for `0 ≤ t`, `tM < 3`,
`mgf (wsum γ ε) P t ≤ exp(t²∑(γᵢsᵢ)²/(2(1 − tM/3)))`. -/
theorem bernstein_mgf_le {n : ℕ} (γ B s : Fin n → ℝ) (ε : Fin n → Ω → ℝ)
    [IsProbabilityMeasure P]
    (hmeas : ∀ i, Measurable (ε i)) (hindep : iIndepFun ε P)
    (hmean : ∀ i, ∫ ω, ε i ω ∂P = 0) (hbdd : ∀ i ω, |ε i ω| ≤ B i)
    (hvar : ∀ i, ∫ ω, (ε i ω) ^ 2 ∂P ≤ (s i) ^ 2)
    {M : ℝ} (hMpos : 0 < M) (hM : ∀ i, |γ i| * B i ≤ M) {t : ℝ} (ht0 : 0 ≤ t)
    (htM : t * M < 3) :
    mgf (wsum γ ε) P t
      ≤ Real.exp (t ^ 2 * (∑ i, (γ i * s i) ^ 2) / (2 * (1 - t * M / 3))) :=
  mgf_wsum_le γ B s ε hmeas hindep hmean hbdd hvar hMpos hM ht0 htM

/-- One-sided Bernstein tail, for `M > 0`. -/
private lemma bernstein_one_tail {n : ℕ} (γ B s : Fin n → ℝ) (ε : Fin n → Ω → ℝ)
    [IsProbabilityMeasure P]
    (hmeas : ∀ i, Measurable (ε i)) (hindep : iIndepFun ε P)
    (hmean : ∀ i, ∫ ω, ε i ω ∂P = 0) (hbdd : ∀ i ω, |ε i ω| ≤ B i)
    (hvar : ∀ i, ∫ ω, (ε i ω) ^ 2 ∂P ≤ (s i) ^ 2)
    {M : ℝ} (hMpos : 0 < M) (hM : ∀ i, |γ i| * B i ≤ M) {u : ℝ} (hu : 0 ≤ u) :
    P.real {ω | u ≤ wsum γ ε ω}
      ≤ Real.exp (-u ^ 2 / (2 * (∑ i, (γ i * s i) ^ 2 + M * u / 3))) := by
  set S : ℝ := ∑ i, (γ i * s i) ^ 2 with hS_def
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  -- integrability of `exp (t * wsum)` for every `t ≥ 0`
  have hwmeas : Measurable (wsum γ ε) := by
    unfold wsum
    fun_prop
  have hwbdd : ∀ ω, |wsum γ ε ω| ≤ ∑ i, |γ i| * B i := fun ω => by
    unfold wsum
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hbdd i ω) (abs_nonneg _)
  have hint : ∀ t : ℝ, 0 ≤ t → Integrable (fun ω => Real.exp (t * wsum γ ε ω)) P := fun t ht =>
    integrable_of_bdd (by fun_prop) (C := Real.exp (t * ∑ i, |γ i| * B i)) fun ω => by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (hwbdd ω)) ht)
  -- Chernoff at a parameter `t ∈ [0, 3/M)`
  have hchernoff : ∀ t : ℝ, 0 ≤ t → t * M < 3 →
      P.real {ω | u ≤ wsum γ ε ω} ≤ Real.exp (-t * u + t ^ 2 * S / (2 * (1 - t * M / 3))) := by
    intro t ht htM
    calc P.real {ω | u ≤ wsum γ ε ω}
        ≤ Real.exp (-t * u) * mgf (wsum γ ε) P t := measure_ge_le_exp_mul_mgf u ht (hint t ht)
      _ ≤ Real.exp (-t * u) * Real.exp (t ^ 2 * S / (2 * (1 - t * M / 3))) :=
          mul_le_mul_of_nonneg_left
            (mgf_wsum_le γ B s ε hmeas hindep hmean hbdd hvar hMpos hM ht htM)
            (Real.exp_pos _).le
      _ = Real.exp (-t * u + t ^ 2 * S / (2 * (1 - t * M / 3))) := by rw [← Real.exp_add]
  rcases hS.eq_or_lt with hS0 | hSpos
  · -- degenerate variance: take `t = 3 / (2M)`
    have h := hchernoff (3 / (2 * M)) (by positivity) (by field_simp; linarith)
    rw [← hS0] at h ⊢
    refine le_trans h (le_of_eq ?_)
    congr 1
    rcases hu.eq_or_lt with hu0 | hu0
    · rw [← hu0]
      simp
    · have hu' : u ≠ 0 := hu0.ne'
      field_simp
      ring
  · -- the Bernstein optimiser `t = u / (S + M u / 3)`
    set D : ℝ := S + M * u / 3 with hD_def
    have hD : 0 < D := by positivity
    have ht : 0 ≤ u / D := div_nonneg hu hD.le
    have htM : u / D * M < 3 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hD, hD_def]
      linarith
    have h := hchernoff (u / D) ht htM
    refine le_trans h (le_of_eq ?_)
    congr 1
    have hne : (1 - u / D * M / 3) = S / D := by
      rw [hD_def]
      field_simp
      ring
    rw [hne]
    field_simp
    ring

/-- **Bernstein's route.** With the additional declared variance bound `Var(ε_i) ≤ s_i^2`
and a bound `M ≥ maxᵢ |γ_i| B_i`, the weighted sum obeys the Bernstein tail. -/
theorem bernstein_tail {n : ℕ} (γ B s : Fin n → ℝ) (ε : Fin n → Ω → ℝ)
    [IsProbabilityMeasure P]
    (hmeas : ∀ i, Measurable (ε i)) (hindep : iIndepFun ε P)
    (hmean : ∀ i, ∫ ω, ε i ω ∂P = 0) (hbdd : ∀ i ω, |ε i ω| ≤ B i)
    (hvar : ∀ i, ∫ ω, (ε i ω) ^ 2 ∂P ≤ (s i) ^ 2)
    {M : ℝ} (hM : ∀ i, |γ i| * B i ≤ M) {u : ℝ} (hu : 0 ≤ u) :
    P.real {ω | u ≤ |wsum γ ε ω|}
      ≤ 2 * Real.exp (-u ^ 2 / (2 * (∑ i, (γ i * s i) ^ 2 + M * u / 3))) := by
  rcases lt_or_ge 0 M with hMpos | hMnp
  · refine two_sided_of_one_sided
      (bernstein_one_tail γ B s ε hmeas hindep hmean hbdd hvar hMpos hM hu) ?_
    have h := bernstein_one_tail (-γ) B s ε hmeas hindep hmean hbdd hvar hMpos
      (fun i => by simpa using hM i) hu
    simpa [neg_mul, neg_sq] using h
  · -- degenerate case `M ≤ 0`: every weighted error vanishes identically
    have hzero : ∀ ω, wsum γ ε ω = 0 := fun ω => by
      unfold wsum
      refine Finset.sum_eq_zero fun i _ => ?_
      have h1 : |γ i * ε i ω| ≤ |γ i| * B i := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hbdd i ω) (abs_nonneg _)
      have h2 : |γ i * ε i ω| ≤ 0 := le_trans h1 (le_trans (hM i) hMnp)
      exact abs_nonpos_iff.mp h2
    simp only [hzero, abs_zero]
    rcases hu.eq_or_lt with hu0 | hu0
    · rw [← hu0]
      simp only [le_refl, Set.setOf_true, probReal_univ, zero_pow two_ne_zero, neg_zero,
        zero_div, Real.exp_zero]
      norm_num
    · have : {ω : Ω | u ≤ (0 : ℝ)} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
        exact hu0
      rw [this, measureReal_empty]
      positivity

end Bernstein

section TwoPoint

/-! ### The exact two-point (sharp Bennett) mgf bound

Among mean-zero laws with `X ≤ b` and `E X² ≤ v`, the mgf `E exp(λX)` is maximised by the
two-point law on `{b, −v/b}`; its mgf is `twoPointMgfBound λ v b` below. The proof is the
classical quadratic-majorant argument: with `c = v/b`, `h = b + c`, `u = x + c`, the pointwise
bound `exp(λu) ≤ 1 + λu + u²(e^{λh} − 1 − λh)/h²` for `u ≤ h` reduces (after the substitution
`y = λu`) to two elementary facts, the antitone gap `1 + y + y²/2 − eʸ` and the monotonicity of
`ψ(y) = (eʸ − 1 − y)/y²` on `(0, ∞)`; integrating the majorant against `X` gives the bound. -/

/-- The two-point mgf bound `G(λ, v, b) = (b/h)·e^{−λc} + (c/h)·e^{λb}`, `c = v/b`, `h = b + c`:
the mgf of the mean-zero two-point law on `{b, −v/b}` with variance `v`. -/
noncomputable def twoPointMgfBound (lam v b : ℝ) : ℝ :=
  (b / (b + v / b)) * Real.exp (-lam * (v / b)) + ((v / b) / (b + v / b)) * Real.exp (lam * b)

/-- Sanity check: `G(0, v, b) = 1`. -/
example (v b : ℝ) (hb : 0 < b) (hv : 0 ≤ v) : twoPointMgfBound 0 v b = 1 := by
  unfold twoPointMgfBound
  have : b + v / b ≠ 0 := by positivity
  simp only [neg_zero, zero_mul, Real.exp_zero, mul_one]
  field_simp

/-- `G(0, v, b) = 1`. -/
lemma twoPointMgfBound_zero {v b : ℝ} (hb : 0 < b) (hv : 0 ≤ v) : twoPointMgfBound 0 v b = 1 := by
  unfold twoPointMgfBound
  have : b + v / b ≠ 0 := by positivity
  simp only [neg_zero, zero_mul, Real.exp_zero, mul_one]
  field_simp

/-- Sanity check: `G(λ, 0, b) = 1`. -/
example (lam b : ℝ) (hb : 0 < b) : twoPointMgfBound lam 0 b = 1 := by
  unfold twoPointMgfBound
  simp [hb.ne']

/-- Sanity check: the two-point form `p·e^{λb} + (1 − p)·e^{−λv/b}` with `p = v/(b² + v)`. -/
example (lam v b : ℝ) (hb : 0 < b) (hv : 0 ≤ v) :
    twoPointMgfBound lam v b
      = (v / (b ^ 2 + v)) * Real.exp (lam * b)
        + (1 - v / (b ^ 2 + v)) * Real.exp (-lam * v / b) := by
  unfold twoPointMgfBound
  have h1 : b + v / b ≠ 0 := by positivity
  have h2 : b ^ 2 + v ≠ 0 := by positivity
  rw [show -lam * (v / b) = -lam * v / b by ring]
  field_simp
  ring

/-- `G > 0`. -/
lemma twoPointMgfBound_pos {lam v b : ℝ} (hb : 0 < b) (hv : 0 ≤ v) :
    0 < twoPointMgfBound lam v b := by
  unfold twoPointMgfBound
  have h1 : 0 < b / (b + v / b) := by positivity
  have h2 : 0 ≤ (v / b) / (b + v / b) := by positivity
  have h3 := Real.exp_pos (-lam * (v / b))
  have h4 := (Real.exp_pos (lam * b)).le
  nlinarith [mul_pos h1 h3, mul_nonneg h2 h4]

/-- The gap `1 + y + y²/2 − eʸ` is antitone (its derivative is `1 + y − eʸ ≤ 0`). -/
private lemma antitone_quadGap : Antitone fun y : ℝ => 1 + y + y ^ 2 / 2 - Real.exp y := by
  have hd : ∀ y : ℝ, HasDerivAt (fun y : ℝ => 1 + y + y ^ 2 / 2 - Real.exp y)
      (1 + y - Real.exp y) y := by
    intro y
    have h : HasDerivAt (fun y : ℝ => 1 + y + y ^ 2 / 2 - Real.exp y)
        (0 + 1 + (2 * y ^ 1 * 1) / 2 - Real.exp y) y :=
      (((hasDerivAt_const y (1 : ℝ)).add (hasDerivAt_id y)).add
        (((hasDerivAt_id y).pow 2).div_const 2)).sub (Real.hasDerivAt_exp y)
    exact h.congr_deriv (by ring)
  refine antitone_of_deriv_nonpos (fun y => (hd y).differentiableAt) fun y => ?_
  rw [(hd y).deriv]
  linarith [Real.add_one_le_exp y]

/-- `eʸ ≤ 1 + y + y²/2` for `y ≤ 0`. -/
private lemma exp_le_quad_of_nonpos {y : ℝ} (hy : y ≤ 0) :
    Real.exp y ≤ 1 + y + y ^ 2 / 2 := by
  have := antitone_quadGap hy
  simp only [Real.exp_zero] at this
  linarith

/-- `1 + y + y²/2 ≤ eʸ` for `0 ≤ y`. -/
private lemma quad_le_exp_of_nonneg {y : ℝ} (hy : 0 ≤ y) :
    1 + y + y ^ 2 / 2 ≤ Real.exp y := by
  have := antitone_quadGap hy
  simp only [Real.exp_zero] at this
  linarith

/-- The auxiliary function `N(y) = (y − 2)eʸ + y + 2`, with `N' = (y − 1)eʸ + 1`,
`N'' = y·eʸ`. -/
private noncomputable def nAux (y : ℝ) : ℝ := (y - 2) * Real.exp y + y + 2

private noncomputable def nAux1 (y : ℝ) : ℝ := (y - 1) * Real.exp y + 1

private lemma hasDerivAt_nAux1 (y : ℝ) : HasDerivAt nAux1 (y * Real.exp y) y := by
  have h : HasDerivAt (fun y : ℝ => (y - 1) * Real.exp y + 1)
      ((1 - 0) * Real.exp y + (y - 1) * Real.exp y + 0) y :=
    (((hasDerivAt_id y).sub (hasDerivAt_const y (1 : ℝ))).mul (Real.hasDerivAt_exp y)).add
      (hasDerivAt_const y (1 : ℝ))
  exact h.congr_deriv (by ring)

private lemma hasDerivAt_nAux (y : ℝ) : HasDerivAt nAux (nAux1 y) y := by
  have h : HasDerivAt (fun y : ℝ => (y - 2) * Real.exp y + y + 2)
      ((1 - 0) * Real.exp y + (y - 2) * Real.exp y + 1 + 0) y :=
    ((((hasDerivAt_id y).sub (hasDerivAt_const y (2 : ℝ))).mul (Real.hasDerivAt_exp y)).add
      (hasDerivAt_id y)).add (hasDerivAt_const y (2 : ℝ))
  exact h.congr_deriv (by simp [nAux1]; ring)

/-- `(y − 2)eʸ + y + 2 ≥ 0` for `y ≥ 0`. -/
private lemma nAux_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ nAux y := by
  have hcont1 : Continuous nAux1 := by
    unfold nAux1
    fun_prop
  have hcont : Continuous nAux := by
    unfold nAux
    fun_prop
  have h1mono : MonotoneOn nAux1 (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont1.continuousOn
      (fun x _ => (hasDerivAt_nAux1 x).differentiableAt.differentiableWithinAt) fun x hx => ?_
    rw [interior_Ici] at hx
    rw [(hasDerivAt_nAux1 x).deriv]
    exact mul_nonneg (le_of_lt hx) (Real.exp_pos x).le
  have h1zero : nAux1 0 = 0 := by simp [nAux1]
  have hmono : MonotoneOn nAux (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont.continuousOn
      (fun x _ => (hasDerivAt_nAux x).differentiableAt.differentiableWithinAt) fun x hx => ?_
    rw [interior_Ici] at hx
    rw [(hasDerivAt_nAux x).deriv, ← h1zero]
    exact h1mono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (le_of_lt hx)) (le_of_lt hx)
  have h0 : nAux 0 = 0 := by simp [nAux]
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy) hy
  rwa [h0] at this

/-- `ψ(y) = (eʸ − 1 − y)/y²`. -/
private noncomputable def psi (y : ℝ) : ℝ := (Real.exp y - 1 - y) / y ^ 2

private lemma hasDerivAt_psi {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt psi (((Real.exp y - 0 - 1) * y ^ 2 - (Real.exp y - 1 - y) * (2 * y ^ 1 * 1))
      / (y ^ 2) ^ 2) y :=
  (((Real.hasDerivAt_exp y).sub (hasDerivAt_const y (1 : ℝ))).sub (hasDerivAt_id y)).div
    ((hasDerivAt_id y).pow 2) (pow_ne_zero 2 hy)

/-- `ψ` is monotone on `(0, ∞)`. -/
private lemma psi_monotoneOn : MonotoneOn psi (Set.Ioi 0) := by
  have hcont : ContinuousOn psi (Set.Ioi 0) := by
    unfold psi
    exact ContinuousOn.div (by fun_prop) (by fun_prop) fun y hy => pow_ne_zero 2 (ne_of_gt hy)
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) hcont
    (fun x hx => ?_) fun x hx => ?_
  · rw [interior_Ioi] at hx
    exact (hasDerivAt_psi (ne_of_gt hx)).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi] at hx
    rw [(hasDerivAt_psi (ne_of_gt hx)).deriv]
    refine div_nonneg ?_ (by positivity)
    have : (Real.exp x - 0 - 1) * x ^ 2 - (Real.exp x - 1 - x) * (2 * x ^ 1 * 1)
        = x * nAux x := by
      simp only [nAux]
      ring
    rw [this]
    exact mul_nonneg (le_of_lt hx) (nAux_nonneg (le_of_lt hx))

/-- The quadratic majorant: for `λ ≥ 0`, `h > 0` and `u ≤ h`,
`exp(λu) ≤ 1 + λu + u²(e^{λh} − 1 − λh)/h²`. -/
private lemma exp_le_quadratic_majorant {lam h u : ℝ} (hlam : 0 ≤ lam) (hh : 0 < h)
    (hu : u ≤ h) :
    Real.exp (lam * u)
      ≤ 1 + lam * u + u ^ 2 * ((Real.exp (lam * h) - 1 - lam * h) / h ^ 2) := by
  rcases hlam.eq_or_lt with rfl | hlam
  · simp
  set D : ℝ := (Real.exp (lam * h) - 1 - lam * h) / h ^ 2 with hD_def
  have hD : lam ^ 2 / 2 ≤ D := by
    rw [hD_def, le_div_iff₀ (by positivity)]
    have := quad_le_exp_of_nonneg (mul_nonneg hlam.le hh.le)
    nlinarith [this]
  rcases le_or_gt u 0 with hu0 | hu0
  · -- `u ≤ 0`: the quadratic Taylor bound on the left of the tangency point
    have h1 := exp_le_quad_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hlam.le hu0 : lam * u ≤ 0)
    have h2 : (lam * u) ^ 2 / 2 ≤ u ^ 2 * D := by
      rw [mul_pow]
      nlinarith [mul_le_mul_of_nonneg_left hD (sq_nonneg u)]
    linarith
  · -- `0 < u ≤ h`: monotonicity of `ψ`
    have hy : 0 < lam * u := mul_pos hlam hu0
    have hY : 0 < lam * h := mul_pos hlam hh
    have hψ := psi_monotoneOn (Set.mem_Ioi.mpr hy) (Set.mem_Ioi.mpr hY)
      (mul_le_mul_of_nonneg_left hu hlam.le)
    simp only [psi] at hψ
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at hψ
    -- `(e^{λu} − 1 − λu) (λh)² ≤ (e^{λh} − 1 − λh) (λu)²`
    have h3 : Real.exp (lam * u) - 1 - lam * u ≤ u ^ 2 * D := by
      rw [hD_def, ← sub_nonneg]
      have hh2 : 0 < h ^ 2 := by positivity
      have key : u ^ 2 * ((Real.exp (lam * h) - 1 - lam * h) / h ^ 2)
          - (Real.exp (lam * u) - 1 - lam * u)
          = ((Real.exp (lam * h) - 1 - lam * h) * (lam * u) ^ 2
              - (Real.exp (lam * u) - 1 - lam * u) * (lam * h) ^ 2) / (lam ^ 2 * h ^ 2) := by
        field_simp
      rw [key]
      exact div_nonneg (by linarith) (by positivity)
    linarith

/-- **Sharp Bennett / two-point mgf bound.** For a mean-zero `X ≤ b` with `E X² ≤ v`,
`mgf X P λ ≤ G(λ, v, b)` for every `λ ≥ 0`. -/
theorem two_point_mgf_le [IsProbabilityMeasure P] {X : Ω → ℝ} (hXmeas : Measurable X)
    (hXint : Integrable X P) (hmean : ∫ ω, X ω ∂P = 0)
    (hX2int : Integrable (fun ω => (X ω) ^ 2) P) {v b : ℝ}
    (hvar : ∫ ω, (X ω) ^ 2 ∂P ≤ v) (hbdd : ∀ ω, X ω ≤ b) (hb : 0 < b) (hv : 0 ≤ v)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    mgf X P lam ≤ twoPointMgfBound lam v b := by
  set c : ℝ := v / b with hc_def
  set h : ℝ := b + c with hh_def
  have hc : 0 ≤ c := by positivity
  have hh : 0 < h := by positivity
  have hvc : v = b * c := by
    rw [hc_def]
    field_simp
  set D : ℝ := (Real.exp (lam * h) - 1 - lam * h) / h ^ 2 with hD_def
  have hD : 0 ≤ D :=
    div_nonneg (by linarith [Real.add_one_le_exp (lam * h)]) (by positivity)
  -- the pointwise majorant, in expanded polynomial form
  have hpt : ∀ ω, Real.exp (lam * X ω)
      ≤ Real.exp (-lam * c) * ((1 + lam * c + D * c ^ 2) + (lam + 2 * D * c) * X ω
          + D * X ω ^ 2) := by
    intro ω
    have hu : X ω + c ≤ h := by linarith [hbdd ω]
    have h1 := exp_le_quadratic_majorant hlam hh hu
    have h2 : Real.exp (lam * X ω) = Real.exp (-lam * c) * Real.exp (lam * (X ω + c)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [h2]
    have h3 : (1 + lam * c + D * c ^ 2) + (lam + 2 * D * c) * X ω + D * X ω ^ 2
        = 1 + lam * (X ω + c) + (X ω + c) ^ 2 * D := by ring
    rw [h3]
    exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
  -- integrability
  have hexpint : Integrable (fun ω => Real.exp (lam * X ω)) P :=
    integrable_of_bdd (by fun_prop) (C := Real.exp (lam * b)) fun ω => by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hbdd ω) hlam)
  have hq1 : Integrable (fun ω => (1 + lam * c + D * c ^ 2) + (lam + 2 * D * c) * X ω) P :=
    (integrable_const _).add (hXint.const_mul _)
  have hq2 : Integrable (fun ω => (1 + lam * c + D * c ^ 2) + (lam + 2 * D * c) * X ω
      + D * X ω ^ 2) P := hq1.add (hX2int.const_mul _)
  have hq : Integrable (fun ω => Real.exp (-lam * c) * ((1 + lam * c + D * c ^ 2)
      + (lam + 2 * D * c) * X ω + D * X ω ^ 2)) P := hq2.const_mul _
  -- integrate the majorant
  have hint : ∫ ω, Real.exp (-lam * c) * ((1 + lam * c + D * c ^ 2)
      + (lam + 2 * D * c) * X ω + D * X ω ^ 2) ∂P
      = Real.exp (-lam * c) * ((1 + lam * c + D * c ^ 2) + D * ∫ ω, X ω ^ 2 ∂P) := by
    rw [integral_const_mul, integral_add hq1 (hX2int.const_mul _),
      integral_add (integrable_const _) (hXint.const_mul _), integral_const, integral_const_mul,
      integral_const_mul, hmean]
    simp
  have hG : Real.exp (-lam * c) * ((1 + lam * c + D * c ^ 2) + D * v)
      = twoPointMgfBound lam v b := by
    unfold twoPointMgfBound
    rw [← hc_def, ← hh_def, hD_def, hvc]
    have hexp : Real.exp (lam * b) = Real.exp (lam * h) * Real.exp (-lam * c) := by
      rw [← Real.exp_add]
      congr 1
      rw [hh_def]
      ring
    rw [hexp]
    field_simp
    ring
  calc mgf X P lam = ∫ ω, Real.exp (lam * X ω) ∂P := rfl
    _ ≤ ∫ ω, Real.exp (-lam * c) * ((1 + lam * c + D * c ^ 2)
          + (lam + 2 * D * c) * X ω + D * X ω ^ 2) ∂P := integral_mono hexpint hq hpt
    _ = Real.exp (-lam * c) * ((1 + lam * c + D * c ^ 2) + D * ∫ ω, X ω ^ 2 ∂P) := hint
    _ ≤ Real.exp (-lam * c) * ((1 + lam * c + D * c ^ 2) + D * v) := by
        gcongr
    _ = twoPointMgfBound lam v b := hG

/-- The two-point mgf bound for the weighted sum:
`mgf (wsum γ ε) P λ ≤ ∏ᵢ G(λ, (γᵢsᵢ)², |γᵢ|Bᵢ)`. -/
lemma mgf_wsum_le_twoPoint {n : ℕ} (γ B s : Fin n → ℝ) (ε : Fin n → Ω → ℝ)
    [IsProbabilityMeasure P]
    (hmeas : ∀ i, Measurable (ε i)) (hindep : iIndepFun ε P)
    (hmean : ∀ i, ∫ ω, ε i ω ∂P = 0) (hbdd : ∀ i ω, |ε i ω| ≤ B i)
    (hvar : ∀ i, ∫ ω, (ε i ω) ^ 2 ∂P ≤ (s i) ^ 2) (hb : ∀ i, 0 < |γ i| * B i)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    mgf (wsum γ ε) P lam
      ≤ ∏ i, twoPointMgfBound lam ((γ i * s i) ^ 2) (|γ i| * B i) := by
  have hZmeas : ∀ i, Measurable (fun ω => γ i * ε i ω) := fun i => (hmeas i).const_mul _
  have hZbdd : ∀ i ω, |γ i * ε i ω| ≤ |γ i| * B i := fun i ω => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hbdd i ω) (abs_nonneg _)
  have hsum : wsum γ ε = ∑ i, fun ω => γ i * ε i ω := by
    funext ω
    simp [wsum, Finset.sum_apply]
  have hper : ∀ i, mgf (fun ω => γ i * ε i ω) P lam
      ≤ twoPointMgfBound lam ((γ i * s i) ^ 2) (|γ i| * B i) := by
    intro i
    refine two_point_mgf_le (hZmeas i) (integrable_of_bdd (hZmeas i) (hZbdd i)) ?_
      (integrable_of_bdd ((hZmeas i).pow_const 2) (C := (|γ i| * B i) ^ 2) fun ω => by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hZbdd i ω) 2) ?_
      (fun ω => le_trans (le_abs_self _) (hZbdd i ω)) (hb i) (sq_nonneg _) hlam
    · simp [integral_const_mul, hmean i]
    · simp only [mul_pow, integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hvar i) (sq_nonneg _)
  rw [hsum, (iIndepFun_weighted γ hindep).mgf_sum hZmeas Finset.univ]
  exact Finset.prod_le_prod (fun i _ => mgf_nonneg) fun i _ => hper i

set_option linter.unusedVariables false in
/-- **Two-point (sharp Bennett) tail, one-sided**, at a given `λ ≥ 0`:
`P(N ≥ u) ≤ e^{−λu} ∏ᵢ G(λ, (γᵢsᵢ)², |γᵢ|Bᵢ)`. -/
theorem two_point_one_tail {n : ℕ} (γ B s : Fin n → ℝ) (ε : Fin n → Ω → ℝ)
    [IsProbabilityMeasure P]
    (hmeas : ∀ i, Measurable (ε i)) (hindep : iIndepFun ε P)
    (hmean : ∀ i, ∫ ω, ε i ω ∂P = 0) (hbdd : ∀ i ω, |ε i ω| ≤ B i)
    (hvar : ∀ i, ∫ ω, (ε i ω) ^ 2 ∂P ≤ (s i) ^ 2) (hb : ∀ i, 0 < |γ i| * B i)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : ℝ} (hu : 0 ≤ u) :
    P.real {ω | u ≤ wsum γ ε ω}
      ≤ Real.exp (-lam * u) * ∏ i, twoPointMgfBound lam ((γ i * s i) ^ 2) (|γ i| * B i) := by
  have hwbdd : ∀ ω, |wsum γ ε ω| ≤ ∑ i, |γ i| * B i := fun ω => by
    unfold wsum
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hbdd i ω) (abs_nonneg _)
  have hint : Integrable (fun ω => Real.exp (lam * wsum γ ε ω)) P :=
    integrable_of_bdd (by unfold wsum; fun_prop) (C := Real.exp (lam * ∑ i, |γ i| * B i))
      fun ω => by
        rw [abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (hwbdd ω)) hlam)
  calc P.real {ω | u ≤ wsum γ ε ω}
      ≤ Real.exp (-lam * u) * mgf (wsum γ ε) P lam := measure_ge_le_exp_mul_mgf u hlam hint
    _ ≤ Real.exp (-lam * u) * ∏ i, twoPointMgfBound lam ((γ i * s i) ^ 2) (|γ i| * B i) :=
        mul_le_mul_of_nonneg_left
          (mgf_wsum_le_twoPoint γ B s ε hmeas hindep hmean hbdd hvar hb hlam)
          (Real.exp_pos _).le

/-- **Two-point (sharp Bennett) tail, two-sided**, at a given `λ ≥ 0`:
`P(|N| ≥ u) ≤ 2 e^{−λu} ∏ᵢ G(λ, (γᵢsᵢ)², |γᵢ|Bᵢ)`. -/
theorem two_point_tail {n : ℕ} (γ B s : Fin n → ℝ) (ε : Fin n → Ω → ℝ)
    [IsProbabilityMeasure P]
    (hmeas : ∀ i, Measurable (ε i)) (hindep : iIndepFun ε P)
    (hmean : ∀ i, ∫ ω, ε i ω ∂P = 0) (hbdd : ∀ i ω, |ε i ω| ≤ B i)
    (hvar : ∀ i, ∫ ω, (ε i ω) ^ 2 ∂P ≤ (s i) ^ 2) (hb : ∀ i, 0 < |γ i| * B i)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : ℝ} (hu : 0 ≤ u) :
    P.real {ω | u ≤ |wsum γ ε ω|}
      ≤ 2 * (Real.exp (-lam * u)
          * ∏ i, twoPointMgfBound lam ((γ i * s i) ^ 2) (|γ i| * B i)) := by
  refine two_sided_of_one_sided
    (two_point_one_tail γ B s ε hmeas hindep hmean hbdd hvar hb hlam hu) ?_
  have h := two_point_one_tail (-γ) B s ε hmeas hindep hmean hbdd hvar
    (fun i => by simpa using hb i) hlam hu
  simpa [neg_mul, neg_sq, abs_neg] using h

/-- **The two-point e-value.** For each fixed `λ ≥ 0`,
`E_λ = exp(λN) / ∏ᵢ G(λ, (γᵢsᵢ)², |γᵢ|Bᵢ)` has `H₀`-expectation at most `1`. -/
theorem two_point_evalue {n : ℕ} (γ B s : Fin n → ℝ) (ε : Fin n → Ω → ℝ)
    [IsProbabilityMeasure P]
    (hmeas : ∀ i, Measurable (ε i)) (hindep : iIndepFun ε P)
    (hmean : ∀ i, ∫ ω, ε i ω ∂P = 0) (hbdd : ∀ i ω, |ε i ω| ≤ B i)
    (hvar : ∀ i, ∫ ω, (ε i ω) ^ 2 ∂P ≤ (s i) ^ 2) (hb : ∀ i, 0 < |γ i| * B i)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    ∫ ω, Real.exp (lam * wsum γ ε ω)
      / ∏ i, twoPointMgfBound lam ((γ i * s i) ^ 2) (|γ i| * B i) ∂P ≤ 1 := by
  have hG : 0 < ∏ i, twoPointMgfBound lam ((γ i * s i) ^ 2) (|γ i| * B i) :=
    Finset.prod_pos fun i _ => twoPointMgfBound_pos (hb i) (sq_nonneg _)
  rw [integral_div, div_le_one hG]
  exact mgf_wsum_le_twoPoint γ B s ε hmeas hindep hmean hbdd hvar hb hlam

end TwoPoint

section OlsContrast

variable {n p : ℕ}

/-- The OLS contrast numerator `aᵀ(β̂ − β⋆)` is the weighted error sum with weights
`γ = olsWeights X a` and centred errors `ε = centredErr P y`. -/
lemma contrastDiff_eq_wsum (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → Ω → ℝ)
    (a : Fin p → ℝ) : contrastDiff P X y a = wsum (olsWeights X a) (centredErr P y) := rfl

/-- The centred errors are independent, measurable and mean zero when the responses are
independent, measurable and bounded around their means. -/
private lemma centredErr_props [IsProbabilityMeasure P] {y : Fin n → Ω → ℝ} {B : Fin n → ℝ}
    (hmeas : ∀ i, Measurable (y i)) (hindep : iIndepFun y P)
    (hbdd : ∀ i ω, |y i ω - P[y i]| ≤ B i) :
    (∀ i, Measurable (centredErr P y i)) ∧ iIndepFun (centredErr P y) P ∧
      ∀ i, ∫ ω, centredErr P y i ω ∂P = 0 := by
  refine ⟨fun i => (hmeas i).sub measurable_const, ?_, fun i => ?_⟩
  · have h : iIndepFun (fun i => (fun x : ℝ => x - P[y i]) ∘ y i) P :=
      hindep.comp (fun i => fun x : ℝ => x - P[y i]) (fun i => by fun_prop)
    exact h
  · have hint : Integrable (y i) P :=
      integrable_of_bdd (hmeas i) (C := B i + |P[y i]|) fun ω => by
        have := hbdd i ω
        calc |y i ω| = |(y i ω - P[y i]) + P[y i]| := by ring_nf
          _ ≤ |y i ω - P[y i]| + |P[y i]| := abs_add_le _ _
          _ ≤ B i + |P[y i]| := by linarith
    simp [centredErr, integral_sub hint (integrable_const _)]

/-- The centred errors are independent, measurable and mean zero when the responses are
independent, measurable and bounded around their means (public form of `centredErr_props`). -/
theorem centredErr_props_of_bounded [IsProbabilityMeasure P] {y : Fin n → Ω → ℝ}
    {B : Fin n → ℝ} (hmeas : ∀ i, Measurable (y i)) (hindep : iIndepFun y P)
    (hbdd : ∀ i ω, |y i ω - P[y i]| ≤ B i) :
    (∀ i, Measurable (centredErr P y i)) ∧ iIndepFun (centredErr P y) P ∧
      ∀ i, ∫ ω, centredErr P y i ω ∂P = 0 :=
  centredErr_props hmeas hindep hbdd

/-- **Certified p-value for a regression coefficient (Hoeffding).** Under declared error bounds
`|Yᵢ − E Yᵢ| ≤ Bᵢ`, the contrast numerator `aᵀ(β̂ − β⋆)` satisfies
`P(|aᵀ(β̂ − β⋆)| ≥ u) ≤ 2 exp(-u² / (2 ∑ᵢ (γᵢ Bᵢ)²))`, `γ = olsWeights X a`; no variance
estimation, no CLT, and no correctness of the mean model is needed. -/
theorem hoeffding_contrast [IsProbabilityMeasure P] (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → Ω → ℝ) (a : Fin p → ℝ) (B : Fin n → ℝ)
    (hmeas : ∀ i, Measurable (y i)) (hindep : iIndepFun y P)
    (hbdd : ∀ i ω, |y i ω - P[y i]| ≤ B i) {u : ℝ} (hu : 0 ≤ u) :
    P.real {ω | u ≤ |contrastDiff P X y a ω|}
      ≤ 2 * Real.exp (-u ^ 2 / (2 * ∑ i, (olsWeights X a i * B i) ^ 2)) := by
  obtain ⟨h1, h2, h3⟩ := centredErr_props hmeas hindep hbdd
  rw [contrastDiff_eq_wsum]
  exact hoeffding_tail (olsWeights X a) B (centredErr P y) h1 h2 h3 hbdd hu

/-- **Certified p-value for a regression coefficient (Bernstein).** As `hoeffding_contrast`, with
the additional declared variance bounds `Var(Yᵢ) ≤ sᵢ²` and `M ≥ maxᵢ |γᵢ| Bᵢ`. -/
theorem bernstein_contrast [IsProbabilityMeasure P] (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → Ω → ℝ) (a : Fin p → ℝ) (B s : Fin n → ℝ)
    (hmeas : ∀ i, Measurable (y i)) (hindep : iIndepFun y P)
    (hbdd : ∀ i ω, |y i ω - P[y i]| ≤ B i)
    (hvar : ∀ i, ∫ ω, (y i ω - P[y i]) ^ 2 ∂P ≤ (s i) ^ 2)
    {M : ℝ} (hM : ∀ i, |olsWeights X a i| * B i ≤ M) {u : ℝ} (hu : 0 ≤ u) :
    P.real {ω | u ≤ |contrastDiff P X y a ω|}
      ≤ 2 * Real.exp (-u ^ 2 / (2 * (∑ i, (olsWeights X a i * s i) ^ 2 + M * u / 3))) := by
  obtain ⟨h1, h2, h3⟩ := centredErr_props hmeas hindep hbdd
  rw [contrastDiff_eq_wsum]
  exact bernstein_tail (olsWeights X a) B s (centredErr P y) h1 h2 h3 hbdd hvar hM hu

/-- **Certified p-value for a regression coefficient (two-point / sharp Bennett).** As
`bernstein_contrast`, at a given `λ ≥ 0`, with the exact two-point mgf bound. -/
theorem two_point_contrast [IsProbabilityMeasure P] (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → Ω → ℝ) (a : Fin p → ℝ) (B s : Fin n → ℝ)
    (hmeas : ∀ i, Measurable (y i)) (hindep : iIndepFun y P)
    (hbdd : ∀ i ω, |y i ω - P[y i]| ≤ B i)
    (hvar : ∀ i, ∫ ω, (y i ω - P[y i]) ^ 2 ∂P ≤ (s i) ^ 2)
    (hb : ∀ i, 0 < |olsWeights X a i| * B i) {lam : ℝ} (hlam : 0 ≤ lam) {u : ℝ} (hu : 0 ≤ u) :
    P.real {ω | u ≤ |contrastDiff P X y a ω|}
      ≤ 2 * (Real.exp (-lam * u)
          * ∏ i, twoPointMgfBound lam ((olsWeights X a i * s i) ^ 2)
              (|olsWeights X a i| * B i)) := by
  obtain ⟨h1, h2, h3⟩ := centredErr_props hmeas hindep hbdd
  rw [contrastDiff_eq_wsum]
  exact two_point_tail (olsWeights X a) B s (centredErr P y) h1 h2 h3 hbdd hvar hb hlam hu

end OlsContrast

section EValueForms

/-! ### E-variable forms of the Hoeffding and Bernstein routes -/

/-- **Hoeffding mgf bound**: `mgf (wsum γ ε) P λ ≤ exp(λ²∑(γᵢBᵢ)²/2)`. -/
theorem hoeffding_mgf_le {n : ℕ} (γ B : Fin n → ℝ) (ε : Fin n → Ω → ℝ)
    [IsProbabilityMeasure P]
    (hmeas : ∀ i, Measurable (ε i)) (hindep : iIndepFun ε P)
    (hmean : ∀ i, ∫ ω, ε i ω ∂P = 0) (hbdd : ∀ i ω, |ε i ω| ≤ B i) (lam : ℝ) :
    mgf (wsum γ ε) P lam ≤ Real.exp (lam ^ 2 * (∑ i, (γ i * B i) ^ 2) / 2) := by
  have hsub := HasSubgaussianMGF.sum_of_iIndepFun (iIndepFun_weighted γ hindep)
    (s := Finset.univ) (fun i _ => hasSubgaussianMGF_weighted γ B ε hmeas hmean hbdd i)
  have h := hsub.mgf_le lam
  have hc : ((∑ i, ((‖(|γ i| * B i) - (-(|γ i| * B i))‖₊ / 2) ^ 2 : ℝ≥0)) : ℝ)
      = ∑ i, (γ i * B i) ^ 2 :=
    Finset.sum_congr rfl fun i _ => proxy_eq (γ i) (B i)
  rw [NNReal.coe_sum, hc] at h
  refine le_trans (le_of_eq rfl) (h.trans (le_of_eq ?_))
  congr 1
  ring

/-- **Hoeffding e-variable**: for each fixed `λ`,
`exp(λN)/exp(λ²∑(γᵢBᵢ)²/2)` has `H₀`-expectation at most `1`. -/
theorem hoeffding_evalue {n : ℕ} (γ B : Fin n → ℝ) (ε : Fin n → Ω → ℝ)
    [IsProbabilityMeasure P]
    (hmeas : ∀ i, Measurable (ε i)) (hindep : iIndepFun ε P)
    (hmean : ∀ i, ∫ ω, ε i ω ∂P = 0) (hbdd : ∀ i ω, |ε i ω| ≤ B i) (lam : ℝ) :
    ∫ ω, Real.exp (lam * wsum γ ε ω)
      / Real.exp (lam ^ 2 * (∑ i, (γ i * B i) ^ 2) / 2) ∂P ≤ 1 := by
  rw [integral_div, div_le_one (Real.exp_pos _)]
  exact hoeffding_mgf_le γ B ε hmeas hindep hmean hbdd lam

/-- **Bernstein e-variable**: for each fixed `0 ≤ λ` with `λM < 3`,
`exp(λN)/exp(λ²∑(γᵢsᵢ)²/(2(1 − λM/3)))` has `H₀`-expectation at most `1`. -/
theorem bernstein_evalue {n : ℕ} (γ B s : Fin n → ℝ) (ε : Fin n → Ω → ℝ)
    [IsProbabilityMeasure P]
    (hmeas : ∀ i, Measurable (ε i)) (hindep : iIndepFun ε P)
    (hmean : ∀ i, ∫ ω, ε i ω ∂P = 0) (hbdd : ∀ i ω, |ε i ω| ≤ B i)
    (hvar : ∀ i, ∫ ω, (ε i ω) ^ 2 ∂P ≤ (s i) ^ 2)
    {M : ℝ} (hMpos : 0 < M) (hM : ∀ i, |γ i| * B i ≤ M)
    {lam : ℝ} (hlam : 0 ≤ lam) (hlamM : lam * M < 3) :
    ∫ ω, Real.exp (lam * wsum γ ε ω)
      / Real.exp (lam ^ 2 * (∑ i, (γ i * s i) ^ 2) / (2 * (1 - lam * M / 3))) ∂P ≤ 1 := by
  rw [integral_div, div_le_one (Real.exp_pos _)]
  exact bernstein_mgf_le γ B s ε hmeas hindep hmean hbdd hvar hMpos hM hlam hlamM

end EValueForms

end BoundedError
