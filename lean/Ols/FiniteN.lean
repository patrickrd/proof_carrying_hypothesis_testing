/-
Copyright (c) 2026 Patrick Rubin-Delanchy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Rubin-Delanchy, Andrew Jones
-/
import Ols.TTest
import Clt.BerryEsseen

/-!
# Finite-sample tail bounds for the HC-studentised OLS contrast

This file proves a fully explicit finite-`n` tail bound for the studentised OLS contrast
`T = aᵀ(β̂ − β⋆)/√ν̂ = Z·√(ν/ν̂)`, replacing the asymptotic (portmanteau / limsup) machinery of
`Ols/TTest.lean` by three finite-sample inputs:

· an approximation input `η` with `|P(Z ≤ z) − Φ(z)| ≤ η z` for all `z` (Berry–Esseen shaped);
· a Chebyshev bound on the *variance event* `{ν̂ ≤ θν}`, from the exact mean and variance of the
  HC variance estimate `ν̂ = ∑ᵢ dᵢγᵢ²ε̂ᵢ²`, a linear-plus-quadratic form in the independent centred
  errors `εᵢ = yᵢ − E yᵢ`;
· an elementary Gaussian threshold shift `1 − Φ(t√θ) ≤ 1 − Φ(t) + t(1 − √θ)φ(t√θ)`.

The development is at a *fixed* sample size `n`, with a deterministic full-rank design
`X : Matrix (Fin n) (Fin p) ℝ`, independent responses `y : Fin n → Ω → ℝ` with arbitrary means
(misspecification is carried throughout), and deterministic HC multipliers `dᵢ ≥ 1`.

## Main statements

· `IndepCentred4.variance_linQuad` — exact variance of `c₀ + 2∑ᵢuᵢεᵢ + ∑ᵢⱼMᵢⱼεᵢεⱼ` for an
  independent centred family with fourth moments.
· `FiniteSampleBundle.integral_hcVar_ge` — `E ν̂ ≥ (1 − 2h_max)ν + ρ_d²` (Lemma 3).
· `FiniteSampleBundle.variance_hcVar` — the exact variance of `ν̂` (Lemma 4).
· `FiniteSampleBundle.variance_hcVar_le` — `Var ν̂ ≤ V₊`, every term of `V₊` computable from
  the design and A2 (Corollary 5).
· `FiniteSampleBundle.variance_event_le` — `P(ν̂ ≤ θν) ≤ V₊/((1 − 2h_max − θ)ν + ρ_d²)²`
  (Lemma 6).
· `gaussian_tail_shift` — the Gaussian threshold shift (Lemma 7).
· `finiteN_tail_oneSided` (Theorem 8), `finiteN_tail_lower`, `finiteN_tail_twoSided` — the
  finite-`n` tail bounds for `T`.
· `finiteN_pvalue_oneSided`, `finiteN_pvalue_twoSided`, `finiteN_ci` — p-value and confidence
  interval corollaries.
· `finiteN_tail_oneSided_BE30` — instance with `η ≡ 30·ϱₙ` from the Berry–Esseen placeholder
  (the only statement here inheriting its `sorry`).
· `hcStudentized_eq_hcStudent`, `finiteN_tail_oneSided_hcStudentized` — the statistic `T` is the
  `hcStudentized` statistic of `Ols/TTest.lean`, and Theorem 8 restated for it.
-/

set_option linter.style.longFile 2400

open MeasureTheory ProbabilityTheory Matrix Finset BigOperators Filter
open scoped Topology ENNReal

noncomputable section

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ## Independent centred families with fourth moments

Mixed moments `E[εᵢεⱼ]`, `E[εᵢεⱼεₖ]`, `E[εᵢεⱼεₖεₗ]` of an independent centred family, obtained
uniformly by regrouping a monomial as `∏ₘ εₘ^{cₘ}` (with `cₘ` the multiplicity of the index `m`)
and factorising the expectation by independence. -/

section IndependentCentredFamily

variable {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]

/-- An independent centred family `ε : Fin n → Ω → ℝ` with finite fourth moments. -/
structure IndepCentred4 (P : Measure Ω) (ε : Fin n → Ω → ℝ) : Prop where
  meas : ∀ i, Measurable (ε i)
  indep : iIndepFun ε P
  memLp_four : ∀ i, MemLp (ε i) 4 P
  mean0 : ∀ i, P[ε i] = 0

/-- A finite product of independent integrable real random variables is integrable. -/
lemma integrable_finset_prod_of_iIndepFun {ι : Type*} {X : ι → Ω → ℝ}
    (hind : iIndepFun X P) (hmeas : ∀ i, Measurable (X i))
    (hint : ∀ i, Integrable (X i) P) (s : Finset ι) :
    Integrable (fun ω => ∏ i ∈ s, X i ω) P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h1 : IndepFun (∏ j ∈ s, X j) (X a) P :=
      hind.indepFun_finsetProd_of_notMem hmeas ha
    have ih' : Integrable (∏ j ∈ s, X j) P :=
      ih.congr (ae_of_all _ fun ω => (Finset.prod_apply ω s X).symm)
    have h2 : Integrable ((∏ j ∈ s, X j) * X a) P := h1.integrable_mul ih' (hint a)
    refine h2.congr (ae_of_all _ fun ω => ?_)
    simp [Finset.prod_insert ha, Finset.prod_apply, mul_comm]

/-- The indicator `[i = m]` as a natural-number exponent. -/
def indN (i m : Fin n) : ℕ := if i = m then 1 else 0

@[simp] lemma indN_self (i : Fin n) : indN i i = 1 := by simp [indN]

lemma indN_of_ne {i m : Fin n} (h : i ≠ m) : indN i m = 0 := by simp [indN, h]

namespace IndepCentred4

variable {ε : Fin n → Ω → ℝ}

lemma integrable_pow (hε : IndepCentred4 P ε) (i : Fin n) {c : ℕ} (hc : c ≤ 4) :
    Integrable (fun ω => ε i ω ^ c) P := by
  rcases Nat.eq_zero_or_pos c with rfl | hc0
  · simp
  have hL : MemLp (ε i) c P :=
    (hε.memLp_four i).mono_exponent (by exact_mod_cast hc)
  have h := hL.integrable_norm_pow hc0.ne'
  refine h.mono' ((hε.meas i).pow_const c).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  simp [Real.norm_eq_abs]

omit [IsProbabilityMeasure P] in
lemma indep_pow (hε : IndepCentred4 P ε) (c : Fin n → ℕ) :
    iIndepFun (fun m ω => ε m ω ^ c m) P :=
  hε.indep.comp (fun m x => x ^ c m) fun m => measurable_id.pow_const (c m)

lemma integrable_prod_pow (hε : IndepCentred4 P ε) (c : Fin n → ℕ) (hc : ∀ m, c m ≤ 4) :
    Integrable (fun ω => ∏ m, ε m ω ^ c m) P :=
  integrable_finset_prod_of_iIndepFun (hε.indep_pow c) (fun m => (hε.meas m).pow_const _)
    (fun m => hε.integrable_pow m (hc m)) Finset.univ

omit [IsProbabilityMeasure P] in
/-- Factorisation of the expectation of a product of powers by independence. -/
lemma integral_prod_pow (hε : IndepCentred4 P ε) (c : Fin n → ℕ) :
    ∫ ω, ∏ m, ε m ω ^ c m ∂P = ∏ m, ∫ ω, ε m ω ^ c m ∂P :=
  (hε.indep_pow c).integral_fun_prod_eq_prod_integral
    fun m => ((hε.meas m).pow_const _).aestronglyMeasurable

lemma single_eq_prod (i : Fin n) (ω : Ω) :
    ε i ω = ∏ m, ε m ω ^ indN i m := by
  rw [Finset.prod_eq_single i]
  · simp
  · intro m _ hm
    simp [indN_of_ne (Ne.symm hm)]
  · intro h
    exact absurd (Finset.mem_univ i) h

lemma mul_eq_prod (i j : Fin n) (ω : Ω) :
    ε i ω * ε j ω = ∏ m, ε m ω ^ (indN i m + indN j m) := by
  rw [single_eq_prod (ε := ε) i, single_eq_prod (ε := ε) j, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun m _ => (pow_add _ _ _).symm

lemma mul3_eq_prod (i j k : Fin n) (ω : Ω) :
    ε i ω * ε j ω * ε k ω = ∏ m, ε m ω ^ (indN i m + indN j m + indN k m) := by
  rw [mul_eq_prod (ε := ε) i j, single_eq_prod (ε := ε) k, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun m _ => (pow_add _ _ _).symm

lemma mul4_eq_prod (i j k l : Fin n) (ω : Ω) :
    ε i ω * ε j ω * ε k ω * ε l ω
      = ∏ m, ε m ω ^ (indN i m + indN j m + indN k m + indN l m) := by
  rw [mul3_eq_prod (ε := ε) i j k, single_eq_prod (ε := ε) l, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun m _ => (pow_add _ _ _).symm

lemma integrable_mul (hε : IndepCentred4 P ε) (i j : Fin n) :
    Integrable (fun ω => ε i ω * ε j ω) P := by
  simp_rw [mul_eq_prod (ε := ε) i j]
  exact hε.integrable_prod_pow _ fun m => by unfold indN; split_ifs <;> omega

lemma integrable_mul3 (hε : IndepCentred4 P ε) (i j k : Fin n) :
    Integrable (fun ω => ε i ω * ε j ω * ε k ω) P := by
  simp_rw [mul3_eq_prod (ε := ε) i j k]
  exact hε.integrable_prod_pow _ fun m => by unfold indN; split_ifs <;> omega

lemma integrable_mul4 (hε : IndepCentred4 P ε) (i j k l : Fin n) :
    Integrable (fun ω => ε i ω * ε j ω * ε k ω * ε l ω) P := by
  simp_rw [mul4_eq_prod (ε := ε) i j k l]
  exact hε.integrable_prod_pow _ fun m => by unfold indN; split_ifs <;> omega

omit [IsProbabilityMeasure P] in
/-- A factor with multiplicity one kills the product of moments. -/
lemma prod_integral_pow_eq_zero (hε : IndepCentred4 P ε) (c : Fin n → ℕ) (m : Fin n)
    (hm : c m = 1) : ∏ m, ∫ ω, ε m ω ^ c m ∂P = 0 := by
  refine Finset.prod_eq_zero (Finset.mem_univ m) ?_
  rw [hm]
  simpa using hε.mean0 m

/-- `E[εᵢεⱼ] = δᵢⱼ σᵢ²`. -/
lemma integral_mul (hε : IndepCentred4 P ε) (i j : Fin n) :
    ∫ ω, ε i ω * ε j ω ∂P = if i = j then ∫ ω, ε i ω ^ 2 ∂P else 0 := by
  simp_rw [mul_eq_prod (ε := ε) i j]
  rw [hε.integral_prod_pow]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, Finset.prod_eq_single i]
    · simp
    · intro m _ hm
      simp [indN_of_ne (Ne.symm hm)]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · rw [if_neg hij]
    exact hε.prod_integral_pow_eq_zero _ i (by simp [indN_of_ne (Ne.symm hij)])

/-- `E[εᵢεⱼεₖ] = [i = j = k] E εᵢ³`. -/
lemma integral_mul3 (hε : IndepCentred4 P ε) (i j k : Fin n) :
    ∫ ω, ε i ω * ε j ω * ε k ω ∂P
      = if i = j ∧ j = k then ∫ ω, ε i ω ^ 3 ∂P else 0 := by
  simp_rw [mul3_eq_prod (ε := ε) i j k]
  rw [hε.integral_prod_pow]
  by_cases h : i = j ∧ j = k
  · obtain ⟨rfl, rfl⟩ := h
    rw [if_pos ⟨rfl, rfl⟩, Finset.prod_eq_single i]
    · simp
    · intro m _ hm
      simp [indN_of_ne (Ne.symm hm)]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · rw [if_neg h]
    by_cases hij : i = j
    · subst hij
      have hik : i ≠ k := fun h' => h ⟨rfl, h'⟩
      exact hε.prod_integral_pow_eq_zero _ k (by simp [indN_of_ne hik])
    · by_cases hik : i = k
      · subst hik
        exact hε.prod_integral_pow_eq_zero _ j (by simp [indN_of_ne hij])
      · exact hε.prod_integral_pow_eq_zero _ i
          (by simp [indN_of_ne (Ne.symm hij), indN_of_ne (Ne.symm hik)])

/-- `E[εᵢεⱼεₖεₗ]`, by cases on the multiplicity pattern of the four indices. -/
lemma integral_mul4 (hε : IndepCentred4 P ε) (i j k l : Fin n) :
    ∫ ω, ε i ω * ε j ω * ε k ω * ε l ω ∂P =
      if i = j then
        (if k = l then
          (if i = k then ∫ ω, ε i ω ^ 4 ∂P
            else (∫ ω, ε i ω ^ 2 ∂P) * ∫ ω, ε k ω ^ 2 ∂P)
        else 0)
      else
        (if (k = i ∧ l = j) ∨ (k = j ∧ l = i)
          then (∫ ω, ε i ω ^ 2 ∂P) * ∫ ω, ε j ω ^ 2 ∂P
          else 0) := by
  simp_rw [mul4_eq_prod (ε := ε) i j k l]
  rw [hε.integral_prod_pow]
  -- the two-distinct-indices pattern `{a, a, b, b}` (in any order) evaluates to `σₐ²σ_b²`
  have hpair : ∀ a b : Fin n, a ≠ b →
      (∀ m, indN i m + indN j m + indN k m + indN l m
        = 2 * indN a m + 2 * indN b m) →
      ∏ m, ∫ ω, ε m ω ^ (indN i m + indN j m + indN k m + indN l m) ∂P
        = (∫ ω, ε a ω ^ 2 ∂P) * ∫ ω, ε b ω ^ 2 ∂P := by
    intro a b hab hc
    simp_rw [hc]
    rw [Finset.prod_eq_mul a b hab]
    · simp [indN_of_ne hab, indN_of_ne (Ne.symm hab)]
    · intro m _ hm
      simp [indN_of_ne (Ne.symm hm.1), indN_of_ne (Ne.symm hm.2)]
    · intro h
      exact absurd (Finset.mem_univ a) h
    · intro h
      exact absurd (Finset.mem_univ b) h
  by_cases hij : i = j
  · subst hij
    by_cases hkl : k = l
    · subst hkl
      by_cases hik : i = k
      · subst hik
        simp only [if_true]
        rw [Finset.prod_eq_single i]
        · simp
        · intro m _ hm
          simp [indN_of_ne (Ne.symm hm)]
        · intro h
          exact absurd (Finset.mem_univ i) h
      · simp only [hik, if_true, if_false]
        exact hpair i k hik fun m => by unfold indN; split_ifs <;> omega
    · simp only [hkl, if_true, if_false]
      by_cases hki : k = i
      · subst hki
        have hlk : l ≠ k := fun h => hkl h.symm
        exact hε.prod_integral_pow_eq_zero _ l (by simp [indN_of_ne hkl])
      · exact hε.prod_integral_pow_eq_zero _ k
          (by simp [indN_of_ne (Ne.symm hki), indN_of_ne (Ne.symm hkl)])
  · simp only [hij, if_false]
    by_cases hm : (k = i ∧ l = j) ∨ (k = j ∧ l = i)
    · rw [if_pos hm]
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hpair k l hij fun m => by unfold indN; split_ifs <;> omega
      · exact hpair l k hij fun m => by unfold indN; split_ifs <;> omega
    · rw [if_neg hm]
      have hm1 : k = i → l ≠ j := fun hk hl => hm (Or.inl ⟨hk, hl⟩)
      have hm2 : k = j → l ≠ i := fun hk hl => hm (Or.inr ⟨hk, hl⟩)
      by_cases hki : k = i
      · subst hki
        have hlj : l ≠ j := hm1 rfl
        by_cases hlk : l = k
        · subst hlk
          exact hε.prod_integral_pow_eq_zero _ j (by simp [indN_of_ne hij])
        · exact hε.prod_integral_pow_eq_zero _ l
            (by simp [indN_of_ne (Ne.symm hlk), indN_of_ne (Ne.symm hlj)])
      · by_cases hli : l = i
        · subst hli
          have hkj : k ≠ j := fun h => hm2 h rfl
          exact hε.prod_integral_pow_eq_zero _ k
            (by simp [indN_of_ne (Ne.symm hki), indN_of_ne (Ne.symm hkj)])
        · exact hε.prod_integral_pow_eq_zero _ i
            (by simp [indN_of_ne (Ne.symm hij), indN_of_ne hki, indN_of_ne hli])

end IndepCentred4

end IndependentCentredFamily

/-! ## Variance of a linear-plus-quadratic form

For an independent centred family `ε` with fourth moments, the exact mean and variance of
`W = c₀ + 2∑ᵢuᵢεᵢ + ∑ᵢⱼMᵢⱼεᵢεⱼ` (`M` symmetric). The variance is obtained by bilinearity of the
covariance from the closed-form kernels `cov(εᵢ, εⱼ)`, `cov(εᵢ, εₖεₗ)` and `cov(εᵢεⱼ, εₖεₗ)`. -/

section LinearQuadraticForm

variable {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P] {ε : Fin n → Ω → ℝ}

/-- The linear-plus-quadratic form `W = c₀ + 2∑ᵢuᵢεᵢ + ∑ᵢⱼMᵢⱼεᵢεⱼ`. -/
def linQuad (ε : Fin n → Ω → ℝ) (c₀ : ℝ) (u : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℝ)
    (ω : Ω) : ℝ :=
  c₀ + 2 * ∑ i, u i * ε i ω + ∑ i, ∑ j, M i j * (ε i ω * ε j ω)

/-- The covariance kernel `cov(εᵢεⱼ, εₖεₗ)` of an independent centred family, as a closed form in
the second moments `σ2` and fourth moments `m4`, nested for summation over `l`, then `k`. -/
def quadCov (σ2 m4 : Fin n → ℝ) (i j k l : Fin n) : ℝ :=
  if i = j then
    (if k = l then (if i = k then m4 i - σ2 i ^ 2 else 0) else 0)
  else
    ((if l = j then (if k = i then σ2 i * σ2 j else 0) else 0)
      + (if l = i then (if k = j then σ2 i * σ2 j else 0) else 0))

/-- The double sum of the covariance kernel against a symmetric `M`. -/
lemma sum_sum_quadCov (M : Matrix (Fin n) (Fin n) ℝ) (hM : ∀ i j, M i j = M j i)
    (σ2 m4 : Fin n → ℝ) (i j : Fin n) :
    ∑ k, ∑ l, M i j * (M k l * quadCov σ2 m4 i j k l)
      = if i = j then M i i ^ 2 * (m4 i - σ2 i ^ 2) else 2 * M i j ^ 2 * (σ2 i * σ2 j) := by
  by_cases hij : i = j
  · subst hij
    have h : ∀ k l, quadCov σ2 m4 i i k l
        = if k = l then (if i = k then m4 i - σ2 i ^ 2 else 0) else 0 := by
      intro k l
      simp [quadCov]
    simp only [h, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  · have h : ∀ k l, quadCov σ2 m4 i j k l
        = (if l = j then (if k = i then σ2 i * σ2 j else 0) else 0)
          + (if l = i then (if k = j then σ2 i * σ2 j else 0) else 0) := by
      intro k l
      simp [quadCov, hij]
    simp only [h, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, hij, if_false]
    rw [hM j i]
    ring

namespace IndepCentred4

lemma memLp_two (hε : IndepCentred4 P ε) (i : Fin n) : MemLp (ε i) 2 P :=
  (hε.memLp_four i).mono_exponent (by norm_num)

lemma integrable (hε : IndepCentred4 P ε) (i : Fin n) : Integrable (ε i) P :=
  (hε.memLp_two i).integrable one_le_two

lemma memLp_two_mul (hε : IndepCentred4 P ε) (i j : Fin n) :
    MemLp (fun ω => ε i ω * ε j ω) 2 P := by
  rw [memLp_two_iff_integrable_sq ((hε.meas i).mul (hε.meas j)).aestronglyMeasurable]
  exact (hε.integrable_mul4 i j i j).congr (ae_of_all _ fun ω => by ring)

/-- `cov(εᵢ, εⱼ) = δᵢⱼσᵢ²`. -/
lemma covariance_single (hε : IndepCentred4 P ε) (i j : Fin n) :
    cov[ε i, ε j; P] = if i = j then ∫ ω, ε i ω ^ 2 ∂P else 0 := by
  rw [covariance_eq_sub (hε.memLp_two i) (hε.memLp_two j), hε.mean0 i, zero_mul, sub_zero]
  exact hε.integral_mul i j

/-- `cov(εᵢ, εₖεₗ) = [i = k = l] E εᵢ³`, nested for summation over `l`, then `k`. -/
lemma covariance_single_mul (hε : IndepCentred4 P ε) (i k l : Fin n) :
    cov[ε i, fun ω => ε k ω * ε l ω; P]
      = if k = l then (if i = k then ∫ ω, ε i ω ^ 3 ∂P else 0) else 0 := by
  rw [covariance_eq_sub (hε.memLp_two i) (hε.memLp_two_mul k l), hε.mean0 i, zero_mul,
    sub_zero]
  have h : (ε i * fun ω => ε k ω * ε l ω) = fun ω => ε i ω * ε k ω * ε l ω := by
    funext ω
    simp [mul_assoc]
  rw [h, hε.integral_mul3 i k l]
  by_cases hkl : k = l
  · subst hkl
    by_cases hik : i = k
    · subst hik
      simp
    · simp [hik]
  · have : ¬ (i = k ∧ k = l) := fun h => hkl h.2
    simp [hkl]

/-- `cov(εᵢεⱼ, εₖεₗ) = quadCov σ2 m4 i j k l`. -/
lemma covariance_mul_mul (hε : IndepCentred4 P ε) (i j k l : Fin n) :
    cov[fun ω => ε i ω * ε j ω, fun ω => ε k ω * ε l ω; P]
      = quadCov (fun m => ∫ ω, ε m ω ^ 2 ∂P) (fun m => ∫ ω, ε m ω ^ 4 ∂P) i j k l := by
  rw [covariance_eq_sub (hε.memLp_two_mul i j) (hε.memLp_two_mul k l)]
  have h : ((fun ω => ε i ω * ε j ω) * fun ω => ε k ω * ε l ω)
      = fun ω => ε i ω * ε j ω * ε k ω * ε l ω := by
    funext ω
    simp [mul_assoc]
  rw [h, hε.integral_mul4 i j k l, hε.integral_mul i j, hε.integral_mul k l]
  unfold quadCov
  by_cases hij : i = j
  · subst hij
    by_cases hkl : k = l
    · subst hkl
      by_cases hik : i = k
      · subst hik
        simp [sq]
      · simp [hik]
    · simp [hkl]
  · simp only [hij, if_false, zero_mul, sub_zero]
    by_cases h1 : k = i ∧ l = j
    · obtain ⟨rfl, rfl⟩ := h1
      simp [hij, Ne.symm hij]
    · by_cases h2 : k = j ∧ l = i
      · obtain ⟨rfl, rfl⟩ := h2
        simp [hij, Ne.symm hij]
      · have hA : ¬ (l = j ∧ k = i) := fun h => h1 ⟨h.2, h.1⟩
        have hB : ¬ (l = i ∧ k = j) := fun h => h2 ⟨h.2, h.1⟩
        rw [if_neg (not_or.mpr ⟨h1, h2⟩), ← ite_and, ← ite_and, if_neg hA, if_neg hB, add_zero]

lemma linQuad_eq (c₀ : ℝ) (u : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    linQuad ε c₀ u M = fun ω => c₀ + ((∑ i, 2 * u i * ε i ω)
      + ∑ i, ∑ j, M i j * (ε i ω * ε j ω)) := by
  funext ω
  simp only [linQuad, Finset.mul_sum, mul_assoc, add_assoc]

lemma memLp_two_linQuad (hε : IndepCentred4 P ε) (c₀ : ℝ) (u : Fin n → ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) : MemLp (linQuad ε c₀ u M) 2 P := by
  rw [linQuad_eq]
  have hL : MemLp (fun ω => ∑ i, 2 * u i * ε i ω) 2 P :=
    memLp_finsetSum _ fun i _ => (hε.memLp_two i).const_mul _
  have hQ : MemLp (fun ω => ∑ i, ∑ j, M i j * (ε i ω * ε j ω)) 2 P :=
    memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ => (hε.memLp_two_mul i j).const_mul _
  exact (memLp_const c₀).add (hL.add hQ)

omit [IsProbabilityMeasure P] in
lemma measurable_linQuad (hε : IndepCentred4 P ε) (c₀ : ℝ) (u : Fin n → ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) : Measurable (linQuad ε c₀ u M) := by
  unfold linQuad
  have := hε.meas
  fun_prop

/-- `E W = c₀ + ∑ᵢ Mᵢᵢ σᵢ²`. -/
lemma integral_linQuad (hε : IndepCentred4 P ε) (c₀ : ℝ) (u : Fin n → ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    ∫ ω, linQuad ε c₀ u M ω ∂P = c₀ + ∑ i, M i i * ∫ ω, ε i ω ^ 2 ∂P := by
  have hL : Integrable (fun ω => c₀ + 2 * ∑ i, u i * ε i ω) P :=
    (integrable_const c₀).add
      ((integrable_finsetSum _ fun i _ => (hε.integrable i).const_mul (u i)).const_mul 2)
  have hQ : Integrable (fun ω => ∑ i, ∑ j, M i j * (ε i ω * ε j ω)) P :=
    integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => (hε.integrable_mul i j).const_mul _
  have h1 : ∫ ω, ∑ i, ∑ j, M i j * (ε i ω * ε j ω) ∂P = ∑ i, M i i * ∫ ω, ε i ω ^ 2 ∂P := by
    rw [integral_finsetSum _ (fun i _ =>
      integrable_finsetSum _ fun j _ => (hε.integrable_mul i j).const_mul _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => (hε.integrable_mul i j).const_mul _)]
    simp only [integral_const_mul, hε.integral_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  have h2 : ∫ ω, c₀ + 2 * ∑ i, u i * ε i ω ∂P = c₀ := by
    rw [integral_add (integrable_const c₀)
      ((integrable_finsetSum _ fun i _ => (hε.integrable i).const_mul (u i)).const_mul 2),
      integral_const, integral_const_mul,
      integral_finsetSum _ (fun i _ => (hε.integrable i).const_mul (u i))]
    simp [integral_const_mul, hε.mean0]
  unfold linQuad
  rw [integral_add hL hQ, h1, h2]

/-- Exact variance of the linear-plus-quadratic form `W = c₀ + 2∑ᵢuᵢεᵢ + ∑ᵢⱼMᵢⱼεᵢεⱼ`:
`Var W = ∑ᵢ Mᵢᵢ²(Eεᵢ⁴ − σᵢ⁴) + 2∑_{i≠j} Mᵢⱼ²σᵢ²σⱼ² + 4∑ᵢ uᵢ²σᵢ² + 4∑ᵢ Mᵢᵢuᵢ Eεᵢ³`. -/
theorem variance_linQuad (hε : IndepCentred4 P ε) (c₀ : ℝ) (u : Fin n → ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : ∀ i j, M i j = M j i) :
    Var[linQuad ε c₀ u M; P] =
      ∑ i, M i i ^ 2 * ((∫ ω, ε i ω ^ 4 ∂P) - (∫ ω, ε i ω ^ 2 ∂P) ^ 2)
      + 2 * ∑ i, ∑ j, (if i = j then 0
          else M i j ^ 2 * ((∫ ω, ε i ω ^ 2 ∂P) * ∫ ω, ε j ω ^ 2 ∂P))
      + 4 * ∑ i, u i ^ 2 * ∫ ω, ε i ω ^ 2 ∂P
      + 4 * ∑ i, M i i * u i * ∫ ω, ε i ω ^ 3 ∂P := by
  set σ2 : Fin n → ℝ := fun m => ∫ ω, ε m ω ^ 2 ∂P with hσ2
  set m3 : Fin n → ℝ := fun m => ∫ ω, ε m ω ^ 3 ∂P with hm3
  set m4 : Fin n → ℝ := fun m => ∫ ω, ε m ω ^ 4 ∂P with hm4
  have hL2 : MemLp (fun ω => ∑ i, 2 * u i * ε i ω) 2 P :=
    memLp_finsetSum _ fun i _ => (hε.memLp_two i).const_mul _
  have hY2 : ∀ k, MemLp (fun ω => ∑ l, M k l * (ε k ω * ε l ω)) 2 P := fun k =>
    memLp_finsetSum _ fun l _ => (hε.memLp_two_mul k l).const_mul _
  have hQ2 : MemLp (fun ω => ∑ i, ∑ j, M i j * (ε i ω * ε j ω)) 2 P :=
    memLp_finsetSum _ fun i _ => hY2 i
  have hX : AEStronglyMeasurable (fun ω => (∑ i, 2 * u i * ε i ω)
      + ∑ i, ∑ j, M i j * (ε i ω * ε j ω)) P := (hL2.add hQ2).aestronglyMeasurable
  -- the linear part
  have hVL : Var[fun ω => ∑ i, 2 * u i * ε i ω; P] = 4 * ∑ i, u i ^ 2 * σ2 i := by
    rw [variance_fun_sum (X := fun i ω => 2 * u i * ε i ω)
      (fun i => (hε.memLp_two i).const_mul _)]
    simp only [covariance_const_mul_left, covariance_const_mul_right, hε.covariance_single,
      mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  -- the cross term
  have hcov : cov[fun ω => ∑ i, 2 * u i * ε i ω,
      fun ω => ∑ i, ∑ j, M i j * (ε i ω * ε j ω); P] = 2 * ∑ i, M i i * u i * m3 i := by
    have hinner : ∀ i k, cov[fun ω => 2 * u i * ε i ω,
        fun ω => ∑ l, M k l * (ε k ω * ε l ω); P]
        = ∑ l, 2 * u i * (M k l * (if k = l then (if i = k then m3 i else 0) else 0)) := by
      intro i k
      rw [covariance_fun_sum_right (fun l => (hε.memLp_two_mul k l).const_mul (M k l))
        ((hε.memLp_two i).const_mul (2 * u i))]
      simp only [covariance_const_mul_left, covariance_const_mul_right,
        hε.covariance_single_mul, hm3]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [covariance_fun_sum_fun_sum (X := fun i ω => 2 * u i * ε i ω)
      (Y := fun k ω => ∑ l, M k l * (ε k ω * ε l ω))
      (fun i => (hε.memLp_two i).const_mul _) hY2]
    simp only [hinner, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  -- the quadratic part
  have hVQ : Var[fun ω => ∑ i, ∑ j, M i j * (ε i ω * ε j ω); P]
      = ∑ i, M i i ^ 2 * (m4 i - σ2 i ^ 2)
        + 2 * ∑ i, ∑ j, (if i = j then 0 else M i j ^ 2 * (σ2 i * σ2 j)) := by
    have hinner : ∀ i k, cov[fun ω => ∑ j, M i j * (ε i ω * ε j ω),
        fun ω => ∑ l, M k l * (ε k ω * ε l ω); P]
        = ∑ j, ∑ l, M i j * (M k l * quadCov σ2 m4 i j k l) := by
      intro i k
      rw [covariance_fun_sum_fun_sum (fun j => (hε.memLp_two_mul i j).const_mul _)
        (fun l => (hε.memLp_two_mul k l).const_mul _)]
      simp only [covariance_const_mul_left, covariance_const_mul_right, hε.covariance_mul_mul,
        hσ2, hm4]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [variance_fun_sum (X := fun i ω => ∑ j, M i j * (ε i ω * ε j ω)) hY2]
    simp only [hinner]
    have hswap : ∀ i, ∑ k, ∑ j, ∑ l, M i j * (M k l * quadCov σ2 m4 i j k l)
        = ∑ j, ∑ k, ∑ l, M i j * (M k l * quadCov σ2 m4 i j k l) := fun i => Finset.sum_comm
    simp only [hswap, sum_sum_quadCov M hM σ2 m4]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsplit : ∀ j, (if i = j then M i i ^ 2 * (m4 i - σ2 i ^ 2)
        else 2 * M i j ^ 2 * (σ2 i * σ2 j))
        = (if i = j then M i i ^ 2 * (m4 i - σ2 i ^ 2) else 0)
          + 2 * (if i = j then 0 else M i j ^ 2 * (σ2 i * σ2 j)) := by
      intro j
      split_ifs <;> ring
    simp only [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Finset.mul_sum]
  rw [linQuad_eq, variance_const_add hX, variance_fun_add hL2 hQ2, hVL, hcov, hVQ]
  ring

end IndepCentred4

end LinearQuadraticForm

/-! ## The OLS contrast at a fixed sample size

Fixed design `X : Matrix (Fin n) (Fin p) ℝ`, responses `y : Fin n → Ω → ℝ`, contrast `a`,
HC multipliers `d`. Notation (matching the spec):
`γ = olsWeights X a`, `ν = ∑ᵢ γᵢ²σᵢ²`, `Z = (∑ᵢ γᵢεᵢ)/√ν`, `ν̂ = ∑ᵢ dᵢγᵢ²ε̂ᵢ²`, `T = Z·√(ν/ν̂)`,
`w = dγ²`, `M = (I−H) diag(w) (I−H)`, `u = (I−H) diag(w) r`, `ρ_d² = ∑ᵢ wᵢrᵢ²`. -/

section OlsContrast

variable {n p : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]

/-- The centred errors `εᵢ = yᵢ − E yᵢ`. -/
def centredErr (P : Measure Ω) (y : Fin n → Ω → ℝ) : Fin n → Ω → ℝ :=
  fun i ω => y i ω - P[y i]

/-- The population contrast variance `ν = ∑ᵢ γᵢ² σᵢ²`. -/
def contrastVar (P : Measure Ω) (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → Ω → ℝ)
    (a : Fin p → ℝ) : ℝ :=
  ∑ i, olsWeights X a i ^ 2 * centralMoment (y i) 2 P

/-- The contrast error `aᵀ(β̂ − β⋆) = ∑ᵢ γᵢ εᵢ`. -/
def contrastDiff (P : Measure Ω) (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → Ω → ℝ)
    (a : Fin p → ℝ) (ω : Ω) : ℝ :=
  ∑ i, olsWeights X a i * (y i ω - P[y i])

/-- The standardised contrast `Z = aᵀ(β̂ − β⋆)/√ν`. -/
def contrastStat (P : Measure Ω) (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → Ω → ℝ)
    (a : Fin p → ℝ) (ω : Ω) : ℝ :=
  contrastDiff P X y a ω / √(contrastVar P X y a)

/-- The HC variance estimate `ν̂ = ∑ᵢ dᵢ γᵢ² ε̂ᵢ²` of the contrast. -/
def hcVar (X : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ) (y : Fin n → Ω → ℝ)
    (a : Fin p → ℝ) (ω : Ω) : ℝ :=
  ∑ i, d i * olsWeights X a i ^ 2 * sampleResidual X (fun j => y j ω) i ^ 2

/-- The HC-studentised contrast `T = Z·√(ν/ν̂) = aᵀ(β̂ − β⋆)/√ν̂`. -/
def hcStudent (P : Measure Ω) (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → Ω → ℝ)
    (d : Fin n → ℝ) (a : Fin p → ℝ) (ω : Ω) : ℝ :=
  contrastStat P X y a ω * √(contrastVar P X y a / hcVar X d y a ω)

/-- The weights `wᵢ = dᵢγᵢ²`. -/
def hcWeight (X : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ) (a : Fin p → ℝ) : Fin n → ℝ :=
  fun i => d i * olsWeights X a i ^ 2

/-- `M = (I−H) diag(w) (I−H)` (as `(I−H)ᵀ diag(w) (I−H)`; `I−H` is symmetric). -/
def hcM (X : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ) (a : Fin p → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  weightedGram (complementProj X) (hcWeight X d a)

/-- `u = (I−H) diag(w) r`, `r` the mean residual. -/
def hcU (P : Measure Ω) (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → Ω → ℝ) (d : Fin n → ℝ)
    (a : Fin p → ℝ) : Fin n → ℝ :=
  complementProj X *ᵥ fun i => hcWeight X d a i * meanResidual P X y i

/-- The misspecification cushion `ρ_d² = ∑ᵢ wᵢ rᵢ²`. -/
def hcRho (P : Measure Ω) (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → Ω → ℝ) (d : Fin n → ℝ)
    (a : Fin p → ℝ) : ℝ :=
  ∑ i, hcWeight X d a i * meanResidual P X y i ^ 2

/-- The explicit variance bound
`V₊ = (κ̄−1)s_max⁴∑ᵢMᵢᵢ² + 2s_max⁴∑_{i≠j}Mᵢⱼ² + 4s_max²‖u‖² + 4B₃∑ᵢMᵢᵢ|uᵢ|`. -/
def hcVplus (P : Measure Ω) (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → Ω → ℝ) (d : Fin n → ℝ)
    (a : Fin p → ℝ) (s_max B₃ κ : ℝ) : ℝ :=
  (κ - 1) * s_max ^ 4 * ∑ i, hcM X d a i i ^ 2
    + 2 * s_max ^ 4 * ∑ i, ∑ j, (if i = j then 0 else hcM X d a i j ^ 2)
    + 4 * s_max ^ 2 * normSq (hcU P X y d a)
    + 4 * B₃ * ∑ i, hcM X d a i i * |hcU P X y d a i|

/-- The finite-sample assumptions A1–A2 at a fixed `n`. -/
structure FiniteSampleBundle (P : Measure Ω) (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → Ω → ℝ) where
  (s_min s_max B₃ κ C_r : ℝ)
  hy_meas : ∀ i, Measurable (y i)
  hy_indep : iIndepFun y P
  hy_L4 : ∀ i, MemLp (y i) 4 P
  hX_inv : IsUnit (Xᵀ * X).det
  hs_min_pos : 0 < s_min
  hvar_lb : ∀ i, s_min ^ 2 ≤ centralMoment (y i) 2 P
  hvar_ub : ∀ i, centralMoment (y i) 2 P ≤ s_max ^ 2
  h3 : ∀ i, ∫ ω, |y i ω - P[y i]| ^ 3 ∂P ≤ B₃
  h4 : ∀ i, centralMoment (y i) 4 P ≤ κ * centralMoment (y i) 2 P ^ 2
  hres : ∀ i, |meanResidual P X y i| ≤ C_r

variable {X : Matrix (Fin n) (Fin p) ℝ} {y : Fin n → Ω → ℝ} {d : Fin n → ℝ} {a : Fin p → ℝ}

omit [IsProbabilityMeasure P] in
lemma centralMoment_two_eq (i : Fin n) :
    centralMoment (y i) 2 P = ∫ ω, centredErr P y i ω ^ 2 ∂P := rfl

omit [IsProbabilityMeasure P] in
lemma centralMoment_four_eq (i : Fin n) :
    centralMoment (y i) 4 P = ∫ ω, centredErr P y i ω ^ 4 ∂P := rfl

/-- The centred errors form an independent centred family with fourth moments. -/
lemma FiniteSampleBundle.indepCentred4 (A : FiniteSampleBundle P X y) :
    IndepCentred4 P (centredErr P y) where
  meas i := (A.hy_meas i).sub measurable_const
  indep := by
    have h : iIndepFun (fun i => (fun x : ℝ => x - P[y i]) ∘ y i) P :=
      A.hy_indep.comp (fun i => fun x : ℝ => x - P[y i]) (fun i => by fun_prop)
    exact h
  memLp_four i := by
    have h := (A.hy_L4 i).sub (memLp_const (P[y i]))
    simpa [Pi.sub_def] using h
  mean0 i := by
    have hint : Integrable (y i) P := (A.hy_L4 i).integrable (by norm_num)
    simp [centredErr, integral_sub hint (integrable_const _)]

omit [IsProbabilityMeasure P] in
/-- `ν ≥ 0`. -/
lemma contrastVar_nonneg : 0 ≤ contrastVar P X y a :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)

omit [IsProbabilityMeasure P] in
/-- `ν ≥ s_min² ‖γ‖² > 0` for `a ≠ 0`. -/
lemma FiniteSampleBundle.contrastVar_pos (A : FiniteSampleBundle P X y) (ha : a ≠ 0) :
    0 < contrastVar P X y a := by
  have hγ : 0 < normSq (olsWeights X a) := normSq_olsWeights_pos X A.hX_inv a (Ne.symm ha)
  calc (0 : ℝ) < A.s_min ^ 2 * normSq (olsWeights X a) := mul_pos (pow_pos A.hs_min_pos 2) hγ
    _ = ∑ i, olsWeights X a i ^ 2 * A.s_min ^ 2 := by
        rw [normSq_eq_sum_sq, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ contrastVar P X y a :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (A.hvar_lb i) (sq_nonneg _)

omit [IsProbabilityMeasure P] in
/-- `ν > 0` forces `n > 0`. -/
lemma pos_of_contrastVar_pos (hν : 0 < contrastVar P X y a) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [contrastVar] at hν
  · exact hn

omit [IsProbabilityMeasure P] in
/-- The complement projector is entrywise symmetric. -/
lemma complementProj_apply_symm (X : Matrix (Fin n) (Fin p) ℝ) (i j : Fin n) :
    complementProj X j i = complementProj X i j := by
  have h := congrFun (congrFun (complementProj_symmetric X) i) j
  rwa [Matrix.transpose_apply] at h

omit [IsProbabilityMeasure P] in
lemma hcM_apply (i j : Fin n) :
    hcM X d a i j = ∑ k, hcWeight X d a k * (complementProj X k i * complementProj X k j) :=
  weightedGram_apply _ _ i j

omit [IsProbabilityMeasure P] in
lemma hcM_symm (i j : Fin n) : hcM X d a i j = hcM X d a j i := by
  rw [hcM_apply, hcM_apply]
  exact Finset.sum_congr rfl fun k _ => by ring

omit [IsProbabilityMeasure P] in
lemma hcU_apply (j : Fin n) :
    hcU P X y d a j
      = ∑ i, hcWeight X d a i * meanResidual P X y i * complementProj X i j := by
  simp only [hcU, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by rw [complementProj_apply_symm]; ring

omit [IsProbabilityMeasure P] in
lemma hcWeight_nonneg (hd : ∀ i, 1 ≤ d i) (i : Fin n) : 0 ≤ hcWeight X d a i :=
  mul_nonneg (le_trans zero_le_one (hd i)) (sq_nonneg _)

omit [IsProbabilityMeasure P] in
lemma hcM_diag_nonneg (hd : ∀ i, 1 ≤ d i) (i : Fin n) : 0 ≤ hcM X d a i i := by
  rw [hcM_apply]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (hcWeight_nonneg hd k) (mul_self_nonneg _)

omit [IsProbabilityMeasure P] in
lemma hcRho_nonneg (hd : ∀ i, 1 ≤ d i) : 0 ≤ hcRho P X y d a :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hcWeight_nonneg hd i) (sq_nonneg _)

omit [IsProbabilityMeasure P] in
/-- Pointwise: `ε̂ᵢ = rᵢ + ∑ⱼ (I−H)ᵢⱼ εⱼ`. -/
lemma sampleResidual_eq_meanResidual_add (i : Fin n) (ω : Ω) :
    sampleResidual X (fun j => y j ω) i
      = meanResidual P X y i + ∑ j, complementProj X i j * centredErr P y j ω := by
  rw [sampleResidual_decomp X _ (meanVec y P) i]
  have h1 : meanVec y P i - (hatMatrix X *ᵥ meanVec y P) i = meanResidual P X y i := by
    rw [meanResidual_eq_complement]
    rfl
  have h2 : (y i ω - meanVec y P i) - ∑ j, hatMatrix X i j * (y j ω - meanVec y P j)
      = ∑ j, complementProj X i j * centredErr P y j ω := by
    simp only [complementProj, Matrix.sub_apply, Matrix.one_apply, sub_mul, ite_mul, one_mul,
      zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, centredErr,
      meanVec]
  rw [h1, h2]

/-- Pure algebra: expansion of `∑ᵢ wᵢ (rᵢ + ∑ⱼ Qᵢⱼ eⱼ)²`. -/
lemma sum_weight_sq_expand (w r : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (e : Fin n → ℝ) :
    ∑ i, w i * (r i + ∑ j, Q i j * e j) ^ 2
      = ∑ i, w i * r i ^ 2 + 2 * ∑ j, (∑ i, w i * r i * Q i j) * e j
        + ∑ j, ∑ k, (∑ i, w i * (Q i j * Q i k)) * (e j * e k) := by
  have h1 : ∀ i, w i * (r i + ∑ j, Q i j * e j) ^ 2
      = w i * r i ^ 2 + ∑ j, 2 * (w i * r i * Q i j) * e j
        + ∑ j, ∑ k, w i * (Q i j * Q i k) * (e j * e k) := by
    intro i
    have e1 : ∑ j, 2 * (w i * r i * Q i j) * e j = 2 * w i * r i * ∑ j, Q i j * e j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have e2 : ∑ j, ∑ k, w i * (Q i j * Q i k) * (e j * e k)
        = w i * ((∑ j, Q i j * e j) * ∑ k, Q i k * e k) := by
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e1, e2]
    ring
  simp only [h1, Finset.sum_add_distrib]
  congr 1
  · congr 1
    rw [Finset.mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]

omit [IsProbabilityMeasure P] in
/-- `ν̂` is the linear-plus-quadratic form `ρ_d² + 2uᵀε + εᵀMε` in the centred errors. -/
lemma hcVar_eq_linQuad :
    hcVar X d y a = linQuad (centredErr P y) (hcRho P X y d a) (hcU P X y d a) (hcM X d a) := by
  funext ω
  simp only [hcVar, linQuad, sampleResidual_eq_meanResidual_add (P := P), hcRho, hcU_apply,
    hcM_apply]
  exact sum_weight_sq_expand (hcWeight X d a) (meanResidual P X y) (complementProj X)
    (fun j => centredErr P y j ω)

/-- Lemma 3 (mean): `E ν̂ = ρ_d² + ∑ⱼ Mⱼⱼ σⱼ²`. -/
lemma FiniteSampleBundle.integral_hcVar (A : FiniteSampleBundle P X y) :
    ∫ ω, hcVar X d y a ω ∂P
      = hcRho P X y d a + ∑ j, hcM X d a j j * centralMoment (y j) 2 P := by
  rw [hcVar_eq_linQuad (P := P), A.indepCentred4.integral_linQuad]
  rfl

/-- Lemma 3 (mean, lower bound): `E ν̂ ≥ (1 − 2h_max) ν + ρ_d²`, for `2h_max ≤ 1` and `dᵢ ≥ 1`. -/
theorem FiniteSampleBundle.integral_hcVar_ge (A : FiniteSampleBundle P X y)
    (hd : ∀ i, 1 ≤ d i) (hlev : 2 * maxLev X ≤ 1) :
    (1 - 2 * maxLev X) * contrastVar P X y a + hcRho P X y d a ≤ ∫ ω, hcVar X d y a ω ∂P := by
  rw [A.integral_hcVar]
  have hterm : ∀ j, (1 - 2 * maxLev X) * (olsWeights X a j ^ 2 * centralMoment (y j) 2 P)
      ≤ hcM X d a j j * centralMoment (y j) 2 P := by
    intro j
    have hσ : 0 ≤ centralMoment (y j) 2 P := integral_nonneg fun _ => sq_nonneg _
    have hw : olsWeights X a j ^ 2 ≤ hcWeight X d a j := by
      unfold hcWeight
      nlinarith [hd j, sq_nonneg (olsWeights X a j)]
    have hM : hcWeight X d a j * (1 - leverage X j) ^ 2 ≤ hcM X d a j j := by
      rw [hcM_apply]
      have hQ : complementProj X j j = 1 - leverage X j := by
        simp [complementProj, leverage]
      calc hcWeight X d a j * (1 - leverage X j) ^ 2
          = hcWeight X d a j * (complementProj X j j * complementProj X j j) := by
            rw [hQ]
            ring
        _ ≤ ∑ k, hcWeight X d a k * (complementProj X k j * complementProj X k j) :=
            Finset.single_le_sum
              (f := fun k => hcWeight X d a k * (complementProj X k j * complementProj X k j))
              (fun k _ => mul_nonneg (hcWeight_nonneg hd k) (mul_self_nonneg _))
              (Finset.mem_univ j)
    have hlev_j : leverage X j ≤ maxLev X := leverage_le_maxLev X j
    have hlev_nn : 0 ≤ leverage X j := leverage_nonneg X j
    have h1 : 1 - 2 * maxLev X ≤ (1 - leverage X j) ^ 2 := by nlinarith
    have h0 : 0 ≤ 1 - 2 * maxLev X := by linarith
    calc (1 - 2 * maxLev X) * (olsWeights X a j ^ 2 * centralMoment (y j) 2 P)
        ≤ (1 - 2 * maxLev X) * (hcWeight X d a j * centralMoment (y j) 2 P) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw hσ) h0
      _ ≤ (1 - leverage X j) ^ 2 * (hcWeight X d a j * centralMoment (y j) 2 P) :=
          mul_le_mul_of_nonneg_right h1 (mul_nonneg (hcWeight_nonneg hd j) hσ)
      _ = hcWeight X d a j * (1 - leverage X j) ^ 2 * centralMoment (y j) 2 P := by ring
      _ ≤ hcM X d a j j * centralMoment (y j) 2 P := mul_le_mul_of_nonneg_right hM hσ
  calc (1 - 2 * maxLev X) * contrastVar P X y a + hcRho P X y d a
      = hcRho P X y d a
        + ∑ j, (1 - 2 * maxLev X) * (olsWeights X a j ^ 2 * centralMoment (y j) 2 P) := by
        rw [contrastVar, Finset.mul_sum]
        ring
    _ ≤ hcRho P X y d a + ∑ j, hcM X d a j j * centralMoment (y j) 2 P :=
        add_le_add le_rfl (Finset.sum_le_sum fun j _ => hterm j)

/-- Lemma 4 (exact variance of `ν̂`). -/
theorem FiniteSampleBundle.variance_hcVar (A : FiniteSampleBundle P X y) :
    Var[hcVar X d y a; P] =
      ∑ i, hcM X d a i i ^ 2 * (centralMoment (y i) 4 P - centralMoment (y i) 2 P ^ 2)
      + 2 * ∑ i, ∑ j, (if i = j then 0
          else hcM X d a i j ^ 2 * (centralMoment (y i) 2 P * centralMoment (y j) 2 P))
      + 4 * ∑ i, hcU P X y d a i ^ 2 * centralMoment (y i) 2 P
      + 4 * ∑ i, hcM X d a i i * hcU P X y d a i * ∫ ω, centredErr P y i ω ^ 3 ∂P := by
  rw [hcVar_eq_linQuad (P := P), A.indepCentred4.variance_linQuad _ _ _ hcM_symm]
  rfl

/-- `κ̄ ≥ 1` once there is an observation (Jensen: `E ε⁴ ≥ σ⁴ > 0`). -/
lemma FiniteSampleBundle.one_le_κ (A : FiniteSampleBundle P X y) (hn : 0 < n) : 1 ≤ A.κ := by
  let i : Fin n := ⟨0, hn⟩
  have hI := A.indepCentred4
  have hε2 : MemLp (fun ω => centredErr P y i ω ^ 2) 2 P := by
    rw [memLp_two_iff_integrable_sq ((hI.meas i).pow_const 2).aestronglyMeasurable]
    exact (hI.integrable_pow i (le_refl 4)).congr (ae_of_all _ fun ω => by ring)
  have hvar := variance_nonneg (fun ω => centredErr P y i ω ^ 2) P
  rw [variance_eq_sub hε2] at hvar
  have hsq : (fun ω => centredErr P y i ω ^ 2) ^ 2 = fun ω => centredErr P y i ω ^ 4 := by
    funext ω
    simp only [Pi.pow_apply]
    ring
  rw [hsq] at hvar
  have h4 : (∫ ω, centredErr P y i ω ^ 2 ∂P) ^ 2 ≤ ∫ ω, centredErr P y i ω ^ 4 ∂P := by
    linarith
  have hσ : A.s_min ^ 2 ≤ ∫ ω, centredErr P y i ω ^ 2 ∂P := A.hvar_lb i
  have hκ := A.h4 i
  rw [centralMoment_four_eq, centralMoment_two_eq] at hκ
  have hs : 0 < A.s_min ^ 2 := pow_pos A.hs_min_pos 2
  have hpos : 0 < (∫ ω, centredErr P y i ω ^ 2 ∂P) ^ 2 := by nlinarith
  by_contra hcon
  have hlt : A.κ * (∫ ω, centredErr P y i ω ^ 2 ∂P) ^ 2
      < 1 * (∫ ω, centredErr P y i ω ^ 2 ∂P) ^ 2 :=
    mul_lt_mul_of_pos_right (lt_of_not_ge hcon) hpos
  linarith

omit [IsProbabilityMeasure P] in
/-- `|E εᵢ³| ≤ B₃`. -/
lemma FiniteSampleBundle.abs_third_moment_le (A : FiniteSampleBundle P X y) (i : Fin n) :
    |∫ ω, centredErr P y i ω ^ 3 ∂P| ≤ A.B₃ := by
  refine le_trans abs_integral_le_integral_abs ?_
  refine le_trans (le_of_eq ?_) (A.h3 i)
  exact integral_congr_ae (ae_of_all _ fun ω => by simp [centredErr, abs_pow])

/-- Corollary 5 (variance bound): `Var ν̂ ≤ V₊`. -/
theorem FiniteSampleBundle.variance_hcVar_le (A : FiniteSampleBundle P X y)
    (hd : ∀ i, 1 ≤ d i) (hκ : 1 ≤ A.κ) :
    Var[hcVar X d y a; P] ≤ hcVplus P X y d a A.s_max A.B₃ A.κ := by
  rw [A.variance_hcVar]
  unfold hcVplus
  have hσ_nn : ∀ i, 0 ≤ centralMoment (y i) 2 P := fun i => integral_nonneg fun _ => sq_nonneg _
  have hσ4 : ∀ i, centralMoment (y i) 2 P ^ 2 ≤ A.s_max ^ 4 := fun i => by
    calc centralMoment (y i) 2 P ^ 2 ≤ (A.s_max ^ 2) ^ 2 :=
          pow_le_pow_left₀ (hσ_nn i) (A.hvar_ub i) 2
      _ = A.s_max ^ 4 := by ring
  have h1 : ∑ i, hcM X d a i i ^ 2 * (centralMoment (y i) 4 P - centralMoment (y i) 2 P ^ 2)
      ≤ (A.κ - 1) * A.s_max ^ 4 * ∑ i, hcM X d a i i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hb : centralMoment (y i) 4 P - centralMoment (y i) 2 P ^ 2
        ≤ (A.κ - 1) * A.s_max ^ 4 := by
      have h := A.h4 i
      have h2 : (A.κ - 1) * centralMoment (y i) 2 P ^ 2 ≤ (A.κ - 1) * A.s_max ^ 4 :=
        mul_le_mul_of_nonneg_left (hσ4 i) (sub_nonneg.mpr hκ)
      nlinarith
    calc hcM X d a i i ^ 2 * (centralMoment (y i) 4 P - centralMoment (y i) 2 P ^ 2)
        ≤ hcM X d a i i ^ 2 * ((A.κ - 1) * A.s_max ^ 4) :=
          mul_le_mul_of_nonneg_left hb (sq_nonneg _)
      _ = (A.κ - 1) * A.s_max ^ 4 * hcM X d a i i ^ 2 := by ring
  have h2 : ∑ i, ∑ j, (if i = j then 0
        else hcM X d a i j ^ 2 * (centralMoment (y i) 2 P * centralMoment (y j) 2 P))
      ≤ A.s_max ^ 4 * ∑ i, ∑ j, (if i = j then 0 else hcM X d a i j ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs
    · simp
    · have hσσ : centralMoment (y i) 2 P * centralMoment (y j) 2 P ≤ A.s_max ^ 4 := by
        calc centralMoment (y i) 2 P * centralMoment (y j) 2 P
            ≤ A.s_max ^ 2 * A.s_max ^ 2 :=
              mul_le_mul (A.hvar_ub i) (A.hvar_ub j) (hσ_nn j) (sq_nonneg _)
          _ = A.s_max ^ 4 := by ring
      calc hcM X d a i j ^ 2 * (centralMoment (y i) 2 P * centralMoment (y j) 2 P)
          ≤ hcM X d a i j ^ 2 * A.s_max ^ 4 := mul_le_mul_of_nonneg_left hσσ (sq_nonneg _)
        _ = A.s_max ^ 4 * hcM X d a i j ^ 2 := by ring
  have h3 : ∑ i, hcU P X y d a i ^ 2 * centralMoment (y i) 2 P
      ≤ A.s_max ^ 2 * normSq (hcU P X y d a) := by
    rw [normSq_eq_sum_sq, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    calc hcU P X y d a i ^ 2 * centralMoment (y i) 2 P ≤ hcU P X y d a i ^ 2 * A.s_max ^ 2 :=
          mul_le_mul_of_nonneg_left (A.hvar_ub i) (sq_nonneg _)
      _ = A.s_max ^ 2 * hcU P X y d a i ^ 2 := by ring
  have h4 : ∑ i, hcM X d a i i * hcU P X y d a i * ∫ ω, centredErr P y i ω ^ 3 ∂P
      ≤ A.B₃ * ∑ i, hcM X d a i i * |hcU P X y d a i| := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hM := hcM_diag_nonneg (X := X) (a := a) hd i
    have h3 := A.abs_third_moment_le i
    calc hcM X d a i i * hcU P X y d a i * ∫ ω, centredErr P y i ω ^ 3 ∂P
        ≤ hcM X d a i i * |hcU P X y d a i * ∫ ω, centredErr P y i ω ^ 3 ∂P| := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (le_abs_self _) hM
      _ = hcM X d a i i * (|hcU P X y d a i| * |∫ ω, centredErr P y i ω ^ 3 ∂P|) := by
          rw [abs_mul]
      _ ≤ hcM X d a i i * (|hcU P X y d a i| * A.B₃) := by
          gcongr
      _ = A.B₃ * (hcM X d a i i * |hcU P X y d a i|) := by ring
  nlinarith [h1, h2, h3, h4]

end OlsContrast

/-! ## Tails from the distribution function, the studentisation split, the variance event,
and the Gaussian threshold shift -/

section TailLemmas

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- `P(Z ≤ z)` is the distribution function of the law of `Z`. -/
lemma cdf_map_eq_real {Z : Ω → ℝ} (hZ : Measurable Z) (z : ℝ) :
    cdf (P.map Z) z = P.real {ω | Z ω ≤ z} := by
  haveI : IsProbabilityMeasure (P.map Z) := P.isProbabilityMeasure_map hZ.aemeasurable
  rw [cdf_eq_real, measureReal_def, measureReal_def, Measure.map_apply hZ measurableSet_Iic]
  rfl

/-- Lemma 1 (upper tail): `P(Z > z) ≤ 1 − Φ(z) + η z`. -/
lemma tail_upper_of_cdf {Z : Ω → ℝ} (hZ : Measurable Z) {η : ℝ → ℝ}
    (hη : ∀ z, |cdf (P.map Z) z - cdf (gaussianReal 0 1) z| ≤ η z) (z : ℝ) :
    P.real {ω | z < Z ω} ≤ 1 - cdf (gaussianReal 0 1) z + η z := by
  have hcompl : P.real {ω | z < Z ω} = 1 - P.real {ω | Z ω ≤ z} := by
    have h := measureReal_compl (μ := P) (s := {ω | Z ω ≤ z}) (measurableSet_le hZ measurable_const)
    rw [Set.compl_setOf] at h
    simp only [not_le] at h
    rw [h, probReal_univ]
  have h := (abs_le.mp (hη z)).1
  rw [hcompl, ← cdf_map_eq_real hZ]
  linarith

/-- Lemma 1 (lower tail): `P(Z < −z) ≤ Φ(−z) + η(−z)`. -/
lemma tail_lower_of_cdf {Z : Ω → ℝ} (hZ : Measurable Z) {η : ℝ → ℝ}
    (hη : ∀ z, |cdf (P.map Z) z - cdf (gaussianReal 0 1) z| ≤ η z) (z : ℝ) :
    P.real {ω | Z ω < -z} ≤ cdf (gaussianReal 0 1) (-z) + η (-z) := by
  have hmono : P.real {ω | Z ω < -z} ≤ P.real {ω | Z ω ≤ -z} :=
    measureReal_mono (Set.setOf_subset_setOf.mpr fun ω h => le_of_lt h)
  have h := (abs_le.mp (hη (-z))).2
  rw [cdf_map_eq_real hZ] at h
  linarith

omit [IsProbabilityMeasure P] in
/-- Lemma 2 (studentisation split, event form): for `T = Z·√(ν/V)`, `t > 0`, `θ > 0`, `ν ≥ 0`,
`{T > t} ⊆ {Z > t√θ} ∪ {V ≤ θν}`. -/
lemma studentised_subset {Z V : Ω → ℝ} {ν t θ : ℝ} (ht : 0 < t) (hθ : 0 < θ) (hν : 0 ≤ ν) :
    {ω | t < Z ω * √(ν / V ω)} ⊆ {ω | t * √θ < Z ω} ∪ {ω | V ω ≤ θ * ν} := by
  intro ω hω
  rw [Set.mem_setOf_eq] at hω
  rw [Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq]
  by_contra hcon
  rw [not_or, not_lt, not_le] at hcon
  obtain ⟨hZ, hV⟩ := hcon
  have hVpos : 0 < V ω := lt_of_le_of_lt (mul_nonneg hθ.le hν) hV
  have hs_nn : 0 ≤ √(ν / V ω) := Real.sqrt_nonneg _
  have hZpos : 0 < Z ω := by
    by_contra hZ0
    rw [not_lt] at hZ0
    nlinarith
  have hθs : 0 < √θ := Real.sqrt_pos.mpr hθ
  have hratio : ν / V ω ≤ 1 / θ := by
    rw [div_le_div_iff₀ hVpos hθ]
    linarith
  have hsqrt : √(ν / V ω) ≤ 1 / √θ := by
    calc √(ν / V ω) ≤ √(1 / θ) := Real.sqrt_le_sqrt hratio
      _ = 1 / √θ := by rw [Real.sqrt_div' _ hθ.le, Real.sqrt_one]
  have h1 : Z ω * √(ν / V ω) ≤ Z ω * (1 / √θ) := mul_le_mul_of_nonneg_left hsqrt hZpos.le
  have h2 : t < Z ω * (1 / √θ) := lt_of_lt_of_le hω h1
  rw [mul_one_div, lt_div_iff₀ hθs] at h2
  linarith

/-- Lemma 2 (studentisation split): `P(T > t) ≤ P(Z > t√θ) + P(V ≤ θν)`. -/
lemma studentised_tail_le {Z V : Ω → ℝ} {ν t θ : ℝ} (ht : 0 < t) (hθ : 0 < θ) (hν : 0 ≤ ν) :
    P.real {ω | t < Z ω * √(ν / V ω)}
      ≤ P.real {ω | t * √θ < Z ω} + P.real {ω | V ω ≤ θ * ν} :=
  le_trans (measureReal_mono (studentised_subset ht hθ hν)) (measureReal_union_le _ _)

/-- Lemma 6 (generic Chebyshev form): if `m ≤ E W`, `Var W ≤ V` and `c < m`, then
`P(W ≤ c) ≤ V / (m − c)²`. -/
lemma measureReal_le_of_variance_le {W : Ω → ℝ} (hW : MemLp W 2 P) {m c V : ℝ}
    (hm : m ≤ P[W]) (hV : Var[W; P] ≤ V) (hc : c < m) :
    P.real {ω | W ω ≤ c} ≤ V / (m - c) ^ 2 := by
  have hpos : 0 < m - c := sub_pos.mpr hc
  have hsub : {ω | W ω ≤ c} ⊆ {ω | m - c ≤ |W ω - P[W]|} := by
    intro ω hω
    rw [Set.mem_setOf_eq] at hω ⊢
    rw [abs_sub_comm]
    calc m - c ≤ P[W] - W ω := by linarith
      _ ≤ |P[W] - W ω| := le_abs_self _
  have hcheb := meas_ge_le_variance_div_sq hW hpos
  calc P.real {ω | W ω ≤ c} ≤ P.real {ω | m - c ≤ |W ω - P[W]|} := measureReal_mono hsub
    _ ≤ Var[W; P] / (m - c) ^ 2 := by
        rw [measureReal_def]
        exact ENNReal.toReal_le_of_le_ofReal
          (div_nonneg (variance_nonneg _ _) (sq_nonneg _)) hcheb
    _ ≤ V / (m - c) ^ 2 := div_le_div_of_nonneg_right hV (sq_nonneg _)

/-- The standard normal density decreases in `|x|`. -/
lemma gaussianPDFReal_le_of_abs_le {c x : ℝ} (hc : 0 ≤ c) (h : c ≤ |x|) :
    gaussianPDFReal 0 1 x ≤ gaussianPDFReal 0 1 c := by
  have hx2 : c ^ 2 ≤ x ^ 2 := by
    calc c ^ 2 ≤ |x| ^ 2 := pow_le_pow_left₀ hc h 2
      _ = x ^ 2 := sq_abs x
  simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (inv_nonneg.mpr (Real.sqrt_nonneg _))
  linarith

/-- `N(0,1)(Ioc a b) ≤ (b − a) φ(c)` whenever `c ≤ |x|` on `Ioc a b` and `c ≥ 0`. -/
lemma gaussianReal_real_Ioc_le {a b c : ℝ} (hab : a ≤ b) (hc : 0 ≤ c)
    (h : ∀ x ∈ Set.Ioc a b, c ≤ |x|) :
    (gaussianReal 0 1).real (Set.Ioc a b) ≤ (b - a) * gaussianPDFReal 0 1 c := by
  have hint : (gaussianReal 0 1).real (Set.Ioc a b)
      = ∫ x in Set.Ioc a b, gaussianPDFReal 0 1 x := by
    rw [measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero, ENNReal.toReal_ofReal]
    exact integral_nonneg fun x => gaussianPDFReal_nonneg _ _ _
  rw [hint]
  calc ∫ x in Set.Ioc a b, gaussianPDFReal 0 1 x
      ≤ ∫ _ in Set.Ioc a b, gaussianPDFReal 0 1 c :=
        setIntegral_mono_on (integrable_gaussianPDFReal 0 1).integrableOn
          (integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
          measurableSet_Ioc fun x hx => gaussianPDFReal_le_of_abs_le hc (h x hx)
    _ = (b - a) * gaussianPDFReal 0 1 c := by
        rw [setIntegral_const, measureReal_def, Real.volume_Ioc,
          ENNReal.toReal_ofReal (sub_nonneg.mpr hab), smul_eq_mul]

/-- Lemma 7 (upper): `1 − Φ(t√θ) ≤ 1 − Φ(t) + t(1 − √θ)φ(t√θ)`. -/
lemma gaussian_tail_shift {t θ : ℝ} (ht : 0 < t) (hθ1 : θ ≤ 1) :
    1 - cdf (gaussianReal 0 1) (t * √θ)
      ≤ 1 - cdf (gaussianReal 0 1) t + t * (1 - √θ) * gaussianPDFReal 0 1 (t * √θ) := by
  have hs1 : √θ ≤ 1 := Real.sqrt_le_one.mpr hθ1
  have hs0 : 0 ≤ √θ := Real.sqrt_nonneg θ
  have hle : t * √θ ≤ t := by nlinarith
  have hdiff : cdf (gaussianReal 0 1) t - cdf (gaussianReal 0 1) (t * √θ)
      = (gaussianReal 0 1).real (Set.Ioc (t * √θ) t) := by
    rw [cdf_eq_real, cdf_eq_real,
      ← measureReal_diff (Set.Iic_subset_Iic.mpr hle) measurableSet_Iic]
    congr 1
    ext x
    simp only [Set.mem_diff, Set.mem_Iic, Set.mem_Ioc, not_le]
    tauto
  have hb := gaussianReal_real_Ioc_le hle (mul_nonneg ht.le hs0) fun x hx => by
    rw [abs_of_pos (lt_of_le_of_lt (mul_nonneg ht.le hs0) hx.1)]
    exact hx.1.le
  have hlen : t - t * √θ = t * (1 - √θ) := by ring
  rw [hlen] at hb
  linarith

/-- Lemma 7 (lower): `Φ(−t√θ) ≤ Φ(−t) + t(1 − √θ)φ(t√θ)`. -/
lemma gaussian_tail_shift_lower {t θ : ℝ} (ht : 0 < t) (hθ1 : θ ≤ 1) :
    cdf (gaussianReal 0 1) (-(t * √θ))
      ≤ cdf (gaussianReal 0 1) (-t) + t * (1 - √θ) * gaussianPDFReal 0 1 (t * √θ) := by
  have hs1 : √θ ≤ 1 := Real.sqrt_le_one.mpr hθ1
  have hs0 : 0 ≤ √θ := Real.sqrt_nonneg θ
  have hle : -t ≤ -(t * √θ) := by nlinarith
  have hdiff : cdf (gaussianReal 0 1) (-(t * √θ)) - cdf (gaussianReal 0 1) (-t)
      = (gaussianReal 0 1).real (Set.Ioc (-t) (-(t * √θ))) := by
    rw [cdf_eq_real, cdf_eq_real,
      ← measureReal_diff (Set.Iic_subset_Iic.mpr hle) measurableSet_Iic]
    congr 1
    ext x
    simp only [Set.mem_diff, Set.mem_Iic, Set.mem_Ioc, not_le]
    tauto
  have hb := gaussianReal_real_Ioc_le hle (mul_nonneg ht.le hs0) fun x hx => by
    have hx0 : x ≤ 0 := le_trans hx.2 (by nlinarith)
    rw [abs_of_nonpos hx0]
    linarith [hx.2]
  have hlen : -(t * √θ) - -t = t * (1 - √θ) := by ring
  rw [hlen] at hb
  linarith

/-- The two-sided Gaussian tail in terms of the distribution function. -/
lemma gaussTailProb_eq_cdf {t : ℝ} (ht : 0 ≤ t) :
    gaussTailProb t = cdf (gaussianReal 0 1) (-t) + (1 - cdf (gaussianReal 0 1) t) := by
  haveI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal (by norm_num)
  have h0 : gaussTailProb t = (gaussianReal 0 1).real {x : ℝ | t < |x|} := rfl
  have hset : {x : ℝ | t < |x|} = Set.Iio (-t) ∪ Set.Ioi t := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi, lt_abs, lt_neg]
    tauto
  have hdisj : Disjoint (Set.Iio (-t)) (Set.Ioi t) :=
    (Set.Iic_disjoint_Ioi (by linarith : -t ≤ t)).mono Set.Iio_subset_Iic_self le_rfl
  have h_union : (gaussianReal 0 1).real (Set.Iio (-t) ∪ Set.Ioi t)
      = (gaussianReal 0 1).real (Set.Iio (-t)) + (gaussianReal 0 1).real (Set.Ioi t) :=
    measureReal_union hdisj measurableSet_Ioi
  have h_iio : (gaussianReal 0 1).real (Set.Iio (-t)) = cdf (gaussianReal 0 1) (-t) := by
    rw [measureReal_congr (Iio_ae_eq_Iic (a := -t)), cdf_eq_real]
  have h_ioi : (gaussianReal 0 1).real (Set.Ioi t) = 1 - cdf (gaussianReal 0 1) t := by
    have := measureReal_compl (μ := gaussianReal 0 1) (s := Set.Iic t) measurableSet_Iic
    rw [cdf_eq_real]
    simpa [Set.compl_Iic] using this
  rw [h0, hset, h_union, h_iio, h_ioi]

/-- The standard normal distribution function is strictly increasing. -/
lemma strictMono_cdf_gaussianReal : StrictMono (cdf (gaussianReal 0 1)) := by
  intro a b hab
  rw [cdf_eq_real, cdf_eq_real]
  have hsub : Set.Iic a ∪ Set.Ioo a b ⊆ Set.Iic b := by
    intro x hx
    rcases hx with hx | hx
    · exact le_trans hx hab.le
    · exact hx.2.le
  have hdisj : Disjoint (Set.Iic a) (Set.Ioo a b) :=
    (Set.Iic_disjoint_Ioi le_rfl).mono le_rfl Set.Ioo_subset_Ioi_self
  have hpos : 0 < (gaussianReal 0 1).real (Set.Ioo a b) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (gaussianReal_Ioo_pos hab).ne' (measure_ne_top _ _)
  calc (gaussianReal 0 1).real (Set.Iic a)
      < (gaussianReal 0 1).real (Set.Iic a) + (gaussianReal 0 1).real (Set.Ioo a b) :=
        lt_add_of_pos_right _ hpos
    _ = (gaussianReal 0 1).real (Set.Iic a ∪ Set.Ioo a b) :=
        (measureReal_union hdisj measurableSet_Ioo).symm
    _ ≤ (gaussianReal 0 1).real (Set.Iic b) := measureReal_mono hsub

end TailLemmas

/-! ## Main theorems -/

section MainTheorems

variable {n p : ℕ} {P : Measure Ω} [IsProbabilityMeasure P] {X : Matrix (Fin n) (Fin p) ℝ}
  {y : Fin n → Ω → ℝ} {d : Fin n → ℝ} {a : Fin p → ℝ}

/-- The variance-event bound `e_var(θ) = V₊ / ((1 − 2h_max − θ)ν + ρ_d²)²`. -/
def hcVarianceEventBound (P : Measure Ω) (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → Ω → ℝ)
    (d : Fin n → ℝ) (a : Fin p → ℝ) (s_max B₃ κ θ : ℝ) : ℝ :=
  hcVplus P X y d a s_max B₃ κ /
    ((1 - 2 * maxLev X - θ) * contrastVar P X y a + hcRho P X y d a) ^ 2

/-- The one-sided approximation-plus-shift error `η(t√θ) + t(1 − √θ)φ(t√θ)`. -/
def shiftError (η : ℝ → ℝ) (t θ : ℝ) : ℝ :=
  η (t * √θ) + t * (1 - √θ) * gaussianPDFReal 0 1 (t * √θ)

/-- Sanity check: at `θ = 1` the shift term vanishes and only the approximation input remains. -/
lemma shiftError_one (η : ℝ → ℝ) (t : ℝ) : shiftError η t 1 = η t := by
  simp [shiftError]

/-- Sanity check: with a vanishing approximation input the one-sided bound is
`1 − Φ(t)` plus the shift and variance terms only. -/
lemma shiftError_zero (t θ : ℝ) :
    shiftError (fun _ => 0) t θ = t * (1 - √θ) * gaussianPDFReal 0 1 (t * √θ) := by
  simp [shiftError]

omit [IsProbabilityMeasure P] in
lemma measurable_contrastDiff (hy : ∀ i, Measurable (y i)) :
    Measurable (contrastDiff P X y a) := by
  unfold contrastDiff
  fun_prop

omit [IsProbabilityMeasure P] in
lemma measurable_contrastStat (hy : ∀ i, Measurable (y i)) :
    Measurable (contrastStat P X y a) :=
  (measurable_contrastDiff hy).div_const _

lemma FiniteSampleBundle.measurable_hcVar (A : FiniteSampleBundle P X y) :
    Measurable (hcVar X d y a) := by
  rw [hcVar_eq_linQuad (P := P)]
  exact A.indepCentred4.measurable_linQuad _ _ _

lemma FiniteSampleBundle.memLp_two_hcVar (A : FiniteSampleBundle P X y) :
    MemLp (hcVar X d y a) 2 P := by
  rw [hcVar_eq_linQuad (P := P)]
  exact A.indepCentred4.memLp_two_linQuad _ _ _

/-- Lemma 6 (variance event): for `0 < θ < 1 − 2h_max`,
`P(ν̂ ≤ θν) ≤ V₊ / ((1 − 2h_max − θ)ν + ρ_d²)²`. -/
theorem FiniteSampleBundle.variance_event_le (A : FiniteSampleBundle P X y)
    (hd : ∀ i, 1 ≤ d i) (ha : a ≠ 0) {θ : ℝ} (hθ0 : 0 < θ) (hθh : θ < 1 - 2 * maxLev X) :
    P.real {ω | hcVar X d y a ω ≤ θ * contrastVar P X y a}
      ≤ hcVarianceEventBound P X y d a A.s_max A.B₃ A.κ θ := by
  have hν := A.contrastVar_pos (a := a) ha
  have hn := pos_of_contrastVar_pos hν
  have hlev : 2 * maxLev X ≤ 1 := by linarith
  have hm := A.integral_hcVar_ge (d := d) (a := a) hd hlev
  have hV := A.variance_hcVar_le (d := d) (a := a) hd (A.one_le_κ hn)
  have hρ := hcRho_nonneg (P := P) (X := X) (y := y) (d := d) (a := a) hd
  have hc : θ * contrastVar P X y a
      < (1 - 2 * maxLev X) * contrastVar P X y a + hcRho P X y d a := by nlinarith
  have h := measureReal_le_of_variance_le A.memLp_two_hcVar hm hV hc
  refine le_trans h (le_of_eq ?_)
  unfold hcVarianceEventBound
  congr 1
  ring

/-- **Theorem 8** (one-sided finite-`n` tail bound). Under A1–A3, for `t > 0` and
`0 < θ ≤ 1` with `θ < 1 − 2h_max`,
`P(T > t) ≤ (1 − Φ(t)) + η(t√θ) + t(1 − √θ)φ(t√θ) + V₊/((1 − 2h_max − θ)ν + ρ_d²)²`. -/
theorem finiteN_tail_oneSided (A : FiniteSampleBundle P X y) (hd : ∀ i, 1 ≤ d i) (ha : a ≠ 0)
    {η : ℝ → ℝ}
    (hη : ∀ z, |cdf (P.map (contrastStat P X y a)) z - cdf (gaussianReal 0 1) z| ≤ η z)
    {t θ : ℝ} (ht : 0 < t) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθh : θ < 1 - 2 * maxLev X) :
    P.real {ω | t < hcStudent P X y d a ω} ≤
      (1 - cdf (gaussianReal 0 1) t) + shiftError η t θ
        + hcVarianceEventBound P X y d a A.s_max A.B₃ A.κ θ := by
  have hZ : Measurable (contrastStat P X y a) := measurable_contrastStat A.hy_meas
  have hsplit := studentised_tail_le (P := P) (Z := contrastStat P X y a) (V := hcVar X d y a)
    (ν := contrastVar P X y a) (θ := θ) ht hθ0 contrastVar_nonneg
  have h1 := tail_upper_of_cdf hZ hη (t * √θ)
  have h7 := gaussian_tail_shift ht hθ1
  have h6 := A.variance_event_le hd ha hθ0 hθh
  unfold hcStudent shiftError
  linarith

/-- **Corollary 9** (lower tail): `P(T < −t) ≤ Φ(−t) + η(−t√θ) + t(1 − √θ)φ(t√θ) + e_var`. -/
theorem finiteN_tail_lower (A : FiniteSampleBundle P X y) (hd : ∀ i, 1 ≤ d i) (ha : a ≠ 0)
    {η : ℝ → ℝ}
    (hη : ∀ z, |cdf (P.map (contrastStat P X y a)) z - cdf (gaussianReal 0 1) z| ≤ η z)
    {t θ : ℝ} (ht : 0 < t) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθh : θ < 1 - 2 * maxLev X) :
    P.real {ω | hcStudent P X y d a ω < -t} ≤
      cdf (gaussianReal 0 1) (-t) + η (-(t * √θ))
        + t * (1 - √θ) * gaussianPDFReal 0 1 (t * √θ)
        + hcVarianceEventBound P X y d a A.s_max A.B₃ A.κ θ := by
  have hZ : Measurable (contrastStat P X y a) := measurable_contrastStat A.hy_meas
  have hset : {ω | hcStudent P X y d a ω < -t}
      = {ω | t < (-contrastStat P X y a ω) * √(contrastVar P X y a / hcVar X d y a ω)} := by
    ext ω
    simp only [Set.mem_setOf_eq, hcStudent, neg_mul]
    constructor <;> intro h <;> linarith
  have hsplit := studentised_tail_le (P := P) (Z := fun ω => -contrastStat P X y a ω)
    (V := hcVar X d y a) (ν := contrastVar P X y a) (θ := θ) ht hθ0 contrastVar_nonneg
  have hset2 : {ω | t * √θ < -contrastStat P X y a ω}
      = {ω | contrastStat P X y a ω < -(t * √θ)} := by
    ext ω
    simp only [Set.mem_setOf_eq, lt_neg]
  have h1 := tail_lower_of_cdf hZ hη (t * √θ)
  have h7 := gaussian_tail_shift_lower ht hθ1
  have h6 := A.variance_event_le hd ha hθ0 hθh
  rw [hset]
  rw [hset2] at hsplit
  linarith

omit [IsProbabilityMeasure P] in
/-- The event `{|T| > t}` lies in the union of the two `Z`-tails and the variance event. -/
lemma abs_hcStudent_subset {t θ : ℝ} (ht : 0 < t) (hθ0 : 0 < θ) :
    {ω | t < |hcStudent P X y d a ω|} ⊆
      {ω | t * √θ < contrastStat P X y a ω} ∪ {ω | contrastStat P X y a ω < -(t * √θ)}
        ∪ {ω | hcVar X d y a ω ≤ θ * contrastVar P X y a} := by
  intro ω hω
  rw [Set.mem_setOf_eq, lt_abs] at hω
  rcases hω with h | h
  · have := studentised_subset (Z := contrastStat P X y a) (V := hcVar X d y a)
      (ν := contrastVar P X y a) (θ := θ) ht hθ0 contrastVar_nonneg h
    rcases this with h' | h'
    · exact Or.inl (Or.inl h')
    · exact Or.inr h'
  · have h' : t < (-contrastStat P X y a ω) * √(contrastVar P X y a / hcVar X d y a ω) := by
      rw [neg_mul]
      exact h
    have := studentised_subset (Z := fun ω => -contrastStat P X y a ω) (V := hcVar X d y a)
      (ν := contrastVar P X y a) (θ := θ) ht hθ0 contrastVar_nonneg h'
    rcases this with h'' | h''
    · have h3 : t * √θ < -contrastStat P X y a ω := h''
      have h4 : contrastStat P X y a ω < -(t * √θ) := lt_neg.mp h3
      exact Or.inl (Or.inr h4)
    · exact Or.inr h''

/-- Union bound for any event inside the two `Z`-tails and the variance event; the two tails
share the single variance event. -/
theorem finiteN_union_bound (A : FiniteSampleBundle P X y) (hd : ∀ i, 1 ≤ d i) (ha : a ≠ 0)
    {η : ℝ → ℝ}
    (hη : ∀ z, |cdf (P.map (contrastStat P X y a)) z - cdf (gaussianReal 0 1) z| ≤ η z)
    {t θ : ℝ} (ht : 0 < t) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθh : θ < 1 - 2 * maxLev X)
    {E : Set Ω}
    (hE : E ⊆ {ω | t * √θ < contrastStat P X y a ω}
      ∪ {ω | contrastStat P X y a ω < -(t * √θ)}
      ∪ {ω | hcVar X d y a ω ≤ θ * contrastVar P X y a}) :
    P.real E ≤ gaussTailProb t + η (t * √θ) + η (-(t * √θ))
      + 2 * (t * (1 - √θ) * gaussianPDFReal 0 1 (t * √θ))
      + hcVarianceEventBound P X y d a A.s_max A.B₃ A.κ θ := by
  have hZ : Measurable (contrastStat P X y a) := measurable_contrastStat A.hy_meas
  have hmono := measureReal_mono (μ := P) hE
  have hu1 := measureReal_union_le (μ := P)
    ({ω | t * √θ < contrastStat P X y a ω} ∪ {ω | contrastStat P X y a ω < -(t * √θ)})
    {ω | hcVar X d y a ω ≤ θ * contrastVar P X y a}
  have hu2 := measureReal_union_le (μ := P) {ω | t * √θ < contrastStat P X y a ω}
    {ω | contrastStat P X y a ω < -(t * √θ)}
  have h1 := tail_upper_of_cdf hZ hη (t * √θ)
  have h1' := tail_lower_of_cdf hZ hη (t * √θ)
  have h7 := gaussian_tail_shift ht hθ1
  have h7' := gaussian_tail_shift_lower ht hθ1
  have h6 := A.variance_event_le hd ha hθ0 hθh
  rw [gaussTailProb_eq_cdf ht.le]
  linarith

/-- **Corollary 10** (two-sided tail):
`P(|T| > t) ≤ N(0,1){|x| > t} + η(t√θ) + η(−t√θ) + 2t(1 − √θ)φ(t√θ) + e_var`. -/
theorem finiteN_tail_twoSided (A : FiniteSampleBundle P X y) (hd : ∀ i, 1 ≤ d i) (ha : a ≠ 0)
    {η : ℝ → ℝ}
    (hη : ∀ z, |cdf (P.map (contrastStat P X y a)) z - cdf (gaussianReal 0 1) z| ≤ η z)
    {t θ : ℝ} (ht : 0 < t) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθh : θ < 1 - 2 * maxLev X) :
    P.real {ω | t < |hcStudent P X y d a ω|} ≤
      gaussTailProb t + η (t * √θ) + η (-(t * √θ))
        + 2 * (t * (1 - √θ) * gaussianPDFReal 0 1 (t * √θ))
        + hcVarianceEventBound P X y d a A.s_max A.B₃ A.κ θ :=
  finiteN_union_bound A hd ha hη ht hθ0 hθ1 hθh (abs_hcStudent_subset ht hθ0)

/-- The one-sided (upper-tail) Gaussian p-value `p₊(t) = 1 − Φ(t)`. -/
def oneSidedPValue (t : ℝ) : ℝ := 1 - cdf (gaussianReal 0 1) t

/-- **Corollary 11** (one-sided p-value): rejecting when `p₊(T) ≤ p₊(t₀)` has probability at
most the one-sided bound at any `t ∈ (0, t₀)`. -/
theorem finiteN_pvalue_oneSided (A : FiniteSampleBundle P X y) (hd : ∀ i, 1 ≤ d i) (ha : a ≠ 0)
    {η : ℝ → ℝ}
    (hη : ∀ z, |cdf (P.map (contrastStat P X y a)) z - cdf (gaussianReal 0 1) z| ≤ η z)
    {t₀ t θ : ℝ} (ht : 0 < t) (htt : t < t₀) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hθh : θ < 1 - 2 * maxLev X) :
    P.real {ω | oneSidedPValue (hcStudent P X y d a ω) ≤ oneSidedPValue t₀} ≤
      (1 - cdf (gaussianReal 0 1) t) + shiftError η t θ
        + hcVarianceEventBound P X y d a A.s_max A.B₃ A.κ θ := by
  refine le_trans (measureReal_mono ?_) (finiteN_tail_oneSided A hd ha hη ht hθ0 hθ1 hθh)
  intro ω hω
  simp only [Set.mem_setOf_eq, oneSidedPValue] at hω ⊢
  have h : t₀ ≤ hcStudent P X y d a ω :=
    strictMono_cdf_gaussianReal.le_iff_le.mp (by linarith)
  linarith

/-- **Corollary 11** (two-sided p-value): rejecting when `twoSidedPValue T ≤ gaussTailProb t₀`
has probability at most the two-sided bound at any `t ∈ (0, t₀)`. -/
theorem finiteN_pvalue_twoSided (A : FiniteSampleBundle P X y) (hd : ∀ i, 1 ≤ d i) (ha : a ≠ 0)
    {η : ℝ → ℝ}
    (hη : ∀ z, |cdf (P.map (contrastStat P X y a)) z - cdf (gaussianReal 0 1) z| ≤ η z)
    {t₀ t θ : ℝ} (ht : 0 < t) (htt : t < t₀) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hθh : θ < 1 - 2 * maxLev X) :
    P.real {ω | twoSidedPValue (hcStudent P X y d a ω) ≤ gaussTailProb t₀} ≤
      gaussTailProb t + η (t * √θ) + η (-(t * √θ))
        + 2 * (t * (1 - √θ) * gaussianPDFReal 0 1 (t * √θ))
        + hcVarianceEventBound P X y d a A.s_max A.B₃ A.κ θ := by
  refine le_trans (measureReal_mono ?_) (finiteN_tail_twoSided A hd ha hη ht hθ0 hθ1 hθh)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  have hp : twoSidedPValue (hcStudent P X y d a ω) = gaussTailProb |hcStudent P X y d a ω| := rfl
  rw [hp] at hω
  have h : t₀ ≤ |hcStudent P X y d a ω| := by
    by_contra hcon
    rw [not_le] at hcon
    have := gaussTailProb_strictAntiOn (Set.mem_Ici.mpr (abs_nonneg _))
      (Set.mem_Ici.mpr (by linarith : (0 : ℝ) ≤ t₀)) hcon
    linarith
  linarith

omit [IsProbabilityMeasure P] in
/-- `aᵀ(β̂ − β⋆) = ∑ᵢ γᵢ εᵢ`: the contrast error is the weighted sum of the centred errors. -/
lemma contrastDiff_eq (ω : Ω) :
    contrastDiff P X y a ω
      = a ⬝ᵥ (olsEstimator X (fun i => y i ω) - olsEstimand P X y) := by
  have h : olsEstimator X (fun i => y i ω) - olsEstimand P X y
      = (Xᵀ * X)⁻¹ *ᵥ (Xᵀ *ᵥ fun i => y i ω - P[y i]) := by
    simp only [olsEstimator, olsEstimand, ← Matrix.mulVec_sub]
    congr 1
  rw [h, Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.mulVec_transpose,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_nonsing_inv,
    Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [contrastDiff, olsWeights, dotProduct, Matrix.mulVec_mulVec]

omit [IsProbabilityMeasure P] in
/-- The `|T|`-event in terms of the contrast error and `ν̂`: on `{ν̂ > θν}`,
`t√ν̂ < |aᵀ(β̂ − β⋆)|` implies `t < |T|`. -/
lemma ci_event_subset (hν : 0 < contrastVar P X y a) {t θ : ℝ} (hθ0 : 0 < θ) :
    {ω | t * √(hcVar X d y a ω) < |contrastDiff P X y a ω|} ⊆
      {ω | t < |hcStudent P X y d a ω|} ∪ {ω | hcVar X d y a ω ≤ θ * contrastVar P X y a} := by
  intro ω hω
  rw [Set.mem_setOf_eq] at hω
  rw [Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq]
  by_cases hV : hcVar X d y a ω ≤ θ * contrastVar P X y a
  · exact Or.inr hV
  · left
    rw [not_le] at hV
    have hVpos : 0 < hcVar X d y a ω := lt_trans (mul_pos hθ0 hν) hV
    have hsν : 0 < √(contrastVar P X y a) := Real.sqrt_pos.mpr hν
    have hsV : 0 < √(hcVar X d y a ω) := Real.sqrt_pos.mpr hVpos
    have hT : |hcStudent P X y d a ω| = |contrastDiff P X y a ω| / √(hcVar X d y a ω) := by
      unfold hcStudent contrastStat
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_div hν.le, abs_div,
        abs_of_pos hsν]
      field_simp
    rw [hT, lt_div_iff₀ hsV]
    exact hω

/-- **Corollary 11** (confidence interval): `aᵀβ̂ ± t√ν̂` covers `aᵀβ⋆` with probability at
least `1 − (two-sided bound)`. -/
theorem finiteN_ci (A : FiniteSampleBundle P X y) (hd : ∀ i, 1 ≤ d i) (ha : a ≠ 0)
    {η : ℝ → ℝ}
    (hη : ∀ z, |cdf (P.map (contrastStat P X y a)) z - cdf (gaussianReal 0 1) z| ≤ η z)
    {t θ : ℝ} (ht : 0 < t) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθh : θ < 1 - 2 * maxLev X) :
    1 - (gaussTailProb t + η (t * √θ) + η (-(t * √θ))
        + 2 * (t * (1 - √θ) * gaussianPDFReal 0 1 (t * √θ))
        + hcVarianceEventBound P X y d a A.s_max A.B₃ A.κ θ)
      ≤ P.real {ω | |a ⬝ᵥ (olsEstimator X (fun i => y i ω) - olsEstimand P X y)|
          ≤ t * √(hcVar X d y a ω)} := by
  have hν := A.contrastVar_pos (a := a) ha
  have hD : Measurable (contrastDiff P X y a) := measurable_contrastDiff A.hy_meas
  have hVm : Measurable (hcVar X d y a) := A.measurable_hcVar
  have hE : {ω | |a ⬝ᵥ (olsEstimator X (fun i => y i ω) - olsEstimand P X y)|
      ≤ t * √(hcVar X d y a ω)}
      = {ω | t * √(hcVar X d y a ω) < |contrastDiff P X y a ω|}ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt, contrastDiff_eq]
  have hmeas : MeasurableSet {ω | t * √(hcVar X d y a ω) < |contrastDiff P X y a ω|} :=
    measurableSet_lt (by fun_prop) hD.abs
  rw [hE, measureReal_compl hmeas, probReal_univ]
  have hsub := ci_event_subset (P := P) (X := X) (y := y) (d := d) (a := a) (t := t) hν hθ0
  have hsub' := abs_hcStudent_subset (P := P) (X := X) (y := y) (d := d) (a := a) ht hθ0
  have hbound := finiteN_union_bound A hd ha hη ht hθ0 hθ1 hθh
    (E := {ω | t * √(hcVar X d y a ω) < |contrastDiff P X y a ω|}) (by
      intro ω hω
      rcases hsub hω with h | h
      · exact hsub' h
      · exact Or.inr h)
  linarith

end MainTheorems

/-! ## Instance: the Berry–Esseen input `η ≡ 30·ϱₙ` -/

section BerryEsseenInstance

variable {p : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : (n : ℕ) → Matrix (Fin n) (Fin p) ℝ} {y : (n : ℕ) → Fin n → Ω → ℝ}

omit [IsProbabilityMeasure P] in
/-- `Z` is the normalised row sum of the OLS array. -/
lemma LindebergSumTriangular_olsArray_eq (n : ℕ) (a : Fin p → ℝ) :
    LindebergSumTriangular (olsArray P X y a) P n = contrastStat P (X n) (y n) a := by
  funext ω
  simp only [LindebergSumTriangular, olsArray, contrastStat, contrastDiff, contrastVar,
    momentSum_olsArray_eq]

/-- A3 with `η ≡ 30·ϱₙ`, from the Berry–Esseen placeholder. -/
theorem FiniteSampleBundle.cdf_bound_BE30 {n : ℕ} (A : FiniteSampleBundle P (X n) (y n))
    {a : Fin p → ℝ} (ha : a ≠ 0) (z : ℝ) :
    |cdf (P.map (contrastStat P (X n) (y n) a)) z - cdf (gaussianReal 0 1) z| ≤
      thirdMomentBerryEsseenConstant * thirdMomentRatioTriangular (olsArray P X y a) P n := by
  rw [← LindebergSumTriangular_olsArray_eq]
  have hI := A.indepCentred4
  have hmeas : ∀ k, Measurable (olsArray P X y a n k) := fun k =>
    ((hI.meas k).const_mul _)
  have hind : iIndepFun (olsArray P X y a n) P :=
    hI.indep.comp (fun k z => olsWeights (X n) a k * z) fun k => measurable_const.mul measurable_id
  have hcent : ∀ k, P[olsArray P X y a n k] = 0 := fun k => by
    have : olsArray P X y a n k = fun ω => olsWeights (X n) a k * centredErr P (y n) k ω := rfl
    rw [this, integral_const_mul, hI.mean0 k, mul_zero]
  have hL2 : ∀ k, MemLp (olsArray P X y a n k) 2 P := fun k => (hI.memLp_two k).const_mul _
  have h3 : ∀ k, Integrable (fun ω => |olsArray P X y a n k ω| ^ 3) P := fun k => by
    have hL3 : MemLp (centredErr P (y n) k) 3 P :=
      (hI.memLp_four k).mono_exponent (by norm_num)
    have h := (hL3.integrable_norm_pow (by norm_num)).const_mul (|olsWeights (X n) a k| ^ 3)
    refine h.congr (ae_of_all _ fun ω => ?_)
    simp only [olsArray, Real.norm_eq_abs, abs_mul, mul_pow]
    rfl
  have hpos : 0 < momentSumTriangular (olsArray P X y a) P n := by
    rw [momentSum_olsArray_eq]
    exact A.contrastVar_pos ha
  exact berryEsseen_triangular_thirdMoment hmeas hind hcent hL2 h3 hpos z

/-- **Instance corollary** of Theorem 8 with `η ≡ 30·ϱₙ` (inherits the Berry–Esseen `sorry`). -/
theorem finiteN_tail_oneSided_BE30 {n : ℕ} (A : FiniteSampleBundle P (X n) (y n))
    {d : Fin n → ℝ} (hd : ∀ i, 1 ≤ d i) {a : Fin p → ℝ} (ha : a ≠ 0)
    {t θ : ℝ} (ht : 0 < t) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθh : θ < 1 - 2 * maxLev (X n)) :
    P.real {ω | t < hcStudent P (X n) (y n) d a ω} ≤
      (1 - cdf (gaussianReal 0 1) t)
        + thirdMomentBerryEsseenConstant * thirdMomentRatioTriangular (olsArray P X y a) P n
        + t * (1 - √θ) * gaussianPDFReal 0 1 (t * √θ)
        + hcVarianceEventBound P (X n) (y n) d a A.s_max A.B₃ A.κ θ := by
  have h := finiteN_tail_oneSided A hd ha
    (η := fun _ => thirdMomentBerryEsseenConstant
      * thirdMomentRatioTriangular (olsArray P X y a) P n)
    (fun z => A.cdf_bound_BE30 ha z) ht hθ0 hθ1 hθh
  unfold shiftError at h
  linarith

end BerryEsseenInstance

/-! ## Design-computable bounds on the `u`-terms of `V₊`, and the link to `hcStudentized` -/

section AuxiliaryBounds

variable {n p : ℕ} {P : Measure Ω} [IsProbabilityMeasure P] {X : Matrix (Fin n) (Fin p) ℝ}
  {y : Fin n → Ω → ℝ} {d : Fin n → ℝ} {a : Fin p → ℝ}

omit [IsProbabilityMeasure P] in
/-- `‖u‖² ≤ C_r² ∑ᵢ dᵢ²γᵢ⁴` (contraction of `I − H` and `|rᵢ| ≤ C_r`). -/
lemma FiniteSampleBundle.normSq_hcU_le (A : FiniteSampleBundle P X y) :
    normSq (hcU P X y d a) ≤ A.C_r ^ 2 * ∑ i, d i ^ 2 * olsWeights X a i ^ 4 := by
  unfold hcU
  refine le_trans (complementProj_mulVec_normSq_le X A.hX_inv _) ?_
  rw [normSq_eq_sum_sq, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hr : meanResidual P X y i ^ 2 ≤ A.C_r ^ 2 := by
    calc meanResidual P X y i ^ 2 = |meanResidual P X y i| ^ 2 := (sq_abs _).symm
      _ ≤ A.C_r ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (A.hres i) 2
  unfold hcWeight
  calc (d i * olsWeights X a i ^ 2 * meanResidual P X y i) ^ 2
      = (d i ^ 2 * olsWeights X a i ^ 4) * meanResidual P X y i ^ 2 := by ring
    _ ≤ (d i ^ 2 * olsWeights X a i ^ 4) * A.C_r ^ 2 :=
        mul_le_mul_of_nonneg_left hr (by positivity)
    _ = A.C_r ^ 2 * (d i ^ 2 * olsWeights X a i ^ 4) := by ring

omit [IsProbabilityMeasure P] in
/-- `∑ᵢ Mᵢᵢ|uᵢ| ≤ (∑ᵢ Mᵢᵢ²)^{1/2} ‖u‖` (Cauchy–Schwarz). -/
lemma sum_hcM_abs_hcU_le :
    ∑ i, hcM X d a i i * |hcU P X y d a i|
      ≤ √(∑ i, hcM X d a i i ^ 2) * √(normSq (hcU P X y d a)) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => hcM X d a i i)
    (fun i => |hcU P X y d a i|)
  simp only [sq_abs] at h
  rw [normSq_eq_sum_sq, ← Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  exact le_trans (le_abs_self _) (Real.abs_le_sqrt h)

omit [IsProbabilityMeasure P] in
/-- The sandwich `aᵀSₙ⁻¹(weightedGram X w)Sₙ⁻¹a` equals `n² ∑ᵢ wᵢγᵢ²`. -/
lemma scalarSandwich_weightedGram_eq (X : Matrix (Fin n) (Fin p) ℝ) (hn : 0 < n)
    (hX_inv : IsUnit (Xᵀ * X).det) (w : Fin n → ℝ) (a : Fin p → ℝ) :
    scalarSandwich (sampleGram X) (weightedGram X w) a
      = (n : ℝ) ^ 2 * ∑ i, w i * olsWeights X a i ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hinv : (sampleGram X)⁻¹ = (n : ℝ) • (Xᵀ * X)⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [sampleGram, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.nonsing_inv_mul _ hX_inv]
    have : (n : ℝ) * (1 / n) = 1 := by field_simp
    rw [this, one_smul]
  rw [scalarSandwich, normSq'_conj _ _ (sampleGram_inv_transpose X), weightedGram_normSq'_eq, hinv,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, mul_pow]
  simp only [olsWeights, Matrix.mulVec]
  ring

omit [IsProbabilityMeasure P] in
/-- `N̄ = aᵀSₙ⁻¹MₙSₙ⁻¹a = n·ν`. -/
lemma scalarSandwich_varGram_eq (hn : 0 < n) (hX_inv : IsUnit (Xᵀ * X).det) :
    scalarSandwich (sampleGram X) (varGram P X y) a = n * contrastVar P X y a := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [varGram, scalarSandwich_weightedGram_eq X hn hX_inv, contrastVar, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

omit [IsProbabilityMeasure P] in
/-- `D̂ = aᵀSₙ⁻¹M̂ₙSₙ⁻¹a = n·ν̂`. -/
lemma scalarSandwich_hcGram_eq (hn : 0 < n) (hX_inv : IsUnit (Xᵀ * X).det) (ω : Ω) :
    scalarSandwich (sampleGram X) (hcGram X d fun i => y i ω) a = n * hcVar X d y a ω := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [hcGram, scalarSandwich_weightedGram_eq X hn hX_inv, hcVar, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

end AuxiliaryBounds

section Bridge

variable {p : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : (n : ℕ) → Matrix (Fin n) (Fin p) ℝ} {y : (n : ℕ) → Fin n → Ω → ℝ}

omit [IsProbabilityMeasure P] in
/-- The HC-studentised statistic of `Ols/TTest.lean` is `T = Z·√(ν/ν̂)`. -/
theorem hcStudentized_eq_hcStudent (d : (n : ℕ) → Fin n → ℝ) (a : Fin p → ℝ) {n : ℕ}
    (hn : 0 < n) (hX_inv : IsUnit ((X n)ᵀ * X n).det) :
    hcStudentized P X y d a n = hcStudent P (X n) (y n) (d n) a := by
  funext ω
  have hn' : (n : ℝ) ≠ 0 := by positivity
  simp only [hcStudentized, hcStudent, scalarSandwich_varGram_eq hn hX_inv,
    scalarSandwich_hcGram_eq hn hX_inv]
  rw [mul_div_mul_left _ _ hn', mul_comm, LindebergSumTriangular_olsArray_eq]

/-- Theorem 8 for the statistic `hcStudentized` of `Ols/TTest.lean`. -/
theorem finiteN_tail_oneSided_hcStudentized {n : ℕ} (A : FiniteSampleBundle P (X n) (y n))
    (d : (n : ℕ) → Fin n → ℝ) (hd : ∀ i, 1 ≤ d n i) {a : Fin p → ℝ} (ha : a ≠ 0)
    {η : ℝ → ℝ}
    (hη : ∀ z, |cdf (P.map (contrastStat P (X n) (y n) a)) z - cdf (gaussianReal 0 1) z| ≤ η z)
    {t θ : ℝ} (ht : 0 < t) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθh : θ < 1 - 2 * maxLev (X n)) :
    P.real {ω | t < hcStudentized P X y d a n ω} ≤
      (1 - cdf (gaussianReal 0 1) t) + shiftError η t θ
        + hcVarianceEventBound P (X n) (y n) (d n) a A.s_max A.B₃ A.κ θ := by
  have hn : 0 < n := pos_of_contrastVar_pos (A.contrastVar_pos ha)
  rw [hcStudentized_eq_hcStudent d a hn A.hX_inv]
  exact finiteN_tail_oneSided A hd ha hη ht hθ0 hθ1 hθh

end Bridge

/-! ## The Cantelli route: a misspecification-free variance-event bound

The Chebyshev bound `FiniteSampleBundle.variance_event_le` needs a declared misspecification
tolerance `C_r`, the leverage condition `θ < 1 − 2h_max`, and is two-sided. Here the mean gap
`E ν̂ − θν ≥ ρ² + a₋(θ)` and the variance bound `V₀ + 4s_max²gρ² + 4B₃S√g·ρ` are maximised
term by term over the single scalar `ρ² = hcRho ≥ 0` through which the model error enters,
giving a bound free of `r`, and Cantelli's (one-sided Chebyshev) inequality replaces
Chebyshev. The only condition is `a₋(θ) > 0`, which for the HC3 multipliers holds for every
`θ ∈ (0, 1)` (`aMinus_pos_hc3`). -/

section Cantelli

variable {n p : ℕ} {P : Measure Ω} [IsProbabilityMeasure P] {X : Matrix (Fin n) (Fin p) ℝ}
  {y : Fin n → Ω → ℝ} {d : Fin n → ℝ} {a : Fin p → ℝ}

/-- `c_j(θ) = Q_jj − θγ_j²`. -/
def cantelliC (X : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ) (a : Fin p → ℝ) (θ : ℝ)
    (j : Fin n) : ℝ :=
  hcM X d a j j - θ * olsWeights X a j ^ 2

/-- `a₋(θ) = s_min²·∑_{c_j ≥ 0} c_j + s_max²·∑_{c_j < 0} c_j`. -/
def aMinus (X : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ) (a : Fin p → ℝ)
    (s_min s_max θ : ℝ) : ℝ :=
  ∑ j, (if 0 ≤ cantelliC X d a θ j then s_min ^ 2 * cantelliC X d a θ j
        else s_max ^ 2 * cantelliC X d a θ j)

/-- `V₀ = s_max⁴{(κ−1)∑ᵢQᵢᵢ² + 2∑_{i≠j}Qᵢⱼ²}` (the `r`-free part of `V₊`). -/
def cantelliV0 (X : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ) (a : Fin p → ℝ)
    (s_max κ : ℝ) : ℝ :=
  (κ - 1) * s_max ^ 4 * ∑ i, hcM X d a i i ^ 2
    + 2 * s_max ^ 4 * ∑ i, ∑ j, (if i = j then 0 else hcM X d a i j ^ 2)

/-- `S = √(∑ᵢQᵢᵢ²)`. -/
def cantelliS (X : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ) (a : Fin p → ℝ) : ℝ :=
  √(∑ i, hcM X d a i i ^ 2)

/-- The analytic `q̄(θ)`; `g` is any upper bound on the weights `wᵢ`. -/
def cantelliQBar (X : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ) (a : Fin p → ℝ)
    (s_min s_max B₃ κ g θ : ℝ) : ℝ :=
  cantelliV0 X d a s_max κ / aMinus X d a s_min s_max θ ^ 2
    + s_max ^ 2 * g / aMinus X d a s_min s_max θ
    + (3 * √3 / 4) * B₃ * cantelliS X d a * √g
        / aMinus X d a s_min s_max θ ^ (3 / 2 : ℝ)

/-- The variance-event bound `q̄/(1 + q̄)`. -/
def cantelliVarianceEventBound (X : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ)
    (a : Fin p → ℝ) (s_min s_max B₃ κ g θ : ℝ) : ℝ :=
  cantelliQBar X d a s_min s_max B₃ κ g θ / (1 + cantelliQBar X d a s_min s_max B₃ κ g θ)

/-! ### Milestone A: Cantelli's inequality -/

/-- `x ↦ x/(x + s)` is nondecreasing for `x ≥ 0`, `s > 0`. -/
private lemma div_add_le_div_add {x x' s : ℝ} (hx : 0 ≤ x) (hxx : x ≤ x') (hs : 0 < s) :
    x / (x + s) ≤ x' / (x' + s) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **Cantelli's inequality** (one-sided Chebyshev): if `m ≤ E W`, `Var W ≤ V` and `c < m`,
then `P(W ≤ c) ≤ V / (V + (m − c)²)`. -/
lemma measureReal_le_cantelli {W : Ω → ℝ} (hW : MemLp W 2 P) {m c V : ℝ}
    (hm : m ≤ P[W]) (hV : Var[W; P] ≤ V) (hc : c < m) :
    P.real {ω | W ω ≤ c} ≤ V / (V + (m - c) ^ 2) := by
  have hpos : 0 < m - c := sub_pos.mpr hc
  have hs : 0 < (m - c) ^ 2 := by positivity
  set V' : ℝ := Var[W; P] with hV'_def
  have hV'0 : 0 ≤ V' := variance_nonneg _ _
  -- reduce to `V = Var W`
  suffices h : P.real {ω | W ω ≤ c} ≤ V' / (V' + (m - c) ^ 2) from
    le_trans h (div_add_le_div_add hV'0 hV hs)
  rcases hV'0.eq_or_lt with hV'z | hV'pos
  · -- degenerate variance: Chebyshev already gives `0`
    have h := measureReal_le_of_variance_le hW hm le_rfl hc
    rw [← hV'_def] at h
    rw [← hV'z] at h ⊢
    simpa using h
  · -- Markov for the square of the shifted variable `Y = b + E W − W`, `b = V'/(m − c)`
    set b : ℝ := V' / (m - c) with hb_def
    have hb : 0 < b := div_pos hV'pos hpos
    have hWint : Integrable W P := hW.integrable one_le_two
    set Y : Ω → ℝ := fun ω => b + P[W] - W ω with hY_def
    have hY2 : MemLp Y 2 P := (memLp_const _).sub hW
    have hYmean : P[Y] = b := by
      simp only [hY_def]
      rw [integral_sub (integrable_const _) hWint, integral_const]
      simp
    have hYvar : Var[Y; P] = V' := by
      simp only [hY_def]
      exact variance_const_sub hW.aestronglyMeasurable _
    have hYsq : ∫ ω, Y ω ^ 2 ∂P = b ^ 2 + V' := by
      have h := variance_eq_sub hY2
      rw [hYvar, hYmean] at h
      have : ∫ ω, Y ω ^ 2 ∂P = P[Y ^ 2] := rfl
      rw [this]
      linarith
    have hsub : {ω | W ω ≤ c} ⊆ {ω | (b + (m - c)) ^ 2 ≤ Y ω ^ 2} := by
      intro ω hω
      rw [Set.mem_setOf_eq] at hω ⊢
      have hY : b + (m - c) ≤ Y ω := by
        simp only [hY_def]
        linarith
      exact pow_le_pow_left₀ (by linarith) hY 2
    have hY2int : Integrable (fun ω => Y ω ^ 2) P := hY2.integrable_sq
    have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := fun ω => Y ω ^ 2)
      (ae_of_all _ fun ω => sq_nonneg _) hY2int ((b + (m - c)) ^ 2)
    have hε : 0 < (b + (m - c)) ^ 2 := by positivity
    calc P.real {ω | W ω ≤ c} ≤ P.real {ω | (b + (m - c)) ^ 2 ≤ Y ω ^ 2} := measureReal_mono hsub
      _ ≤ (b ^ 2 + V') / (b + (m - c)) ^ 2 := by
          rw [le_div_iff₀ hε, ← hYsq]
          linarith [hmarkov]
      _ = V' / (V' + (m - c) ^ 2) := by
          rw [hb_def]
          field_simp

/-! ### Milestone B: the mean gap -/

/-- `E ν̂ − θν ≥ ρ² + a₋(θ)`. -/
lemma FiniteSampleBundle.integral_hcVar_sub_ge (A : FiniteSampleBundle P X y) {θ : ℝ} :
    hcRho P X y d a + aMinus X d a A.s_min A.s_max θ
      ≤ ∫ ω, hcVar X d y a ω ∂P - θ * contrastVar P X y a := by
  rw [A.integral_hcVar, contrastVar, Finset.mul_sum, add_sub_assoc, ← Finset.sum_sub_distrib]
  refine add_le_add le_rfl (Finset.sum_le_sum fun j _ => ?_)
  have hc : hcM X d a j j * centralMoment (y j) 2 P
      - θ * (olsWeights X a j ^ 2 * centralMoment (y j) 2 P)
      = cantelliC X d a θ j * centralMoment (y j) 2 P := by
    unfold cantelliC
    ring
  rw [hc]
  split_ifs with h
  · calc A.s_min ^ 2 * cantelliC X d a θ j = cantelliC X d a θ j * A.s_min ^ 2 := by ring
      _ ≤ cantelliC X d a θ j * centralMoment (y j) 2 P :=
          mul_le_mul_of_nonneg_left (A.hvar_lb j) h
  · rw [not_le] at h
    calc A.s_max ^ 2 * cantelliC X d a θ j = cantelliC X d a θ j * A.s_max ^ 2 := by ring
      _ ≤ cantelliC X d a θ j * centralMoment (y j) 2 P :=
          mul_le_mul_of_nonpos_left (A.hvar_ub j) h.le

/-! ### Milestone C: `‖u‖² ≤ g·ρ²` -/

omit [IsProbabilityMeasure P] in
/-- `‖u‖² ≤ g·ρ²` for any bound `g` on the weights. -/
lemma normSq_hcU_le_gmax (hX_inv : IsUnit (Xᵀ * X).det) (hd : ∀ i, 1 ≤ d i) {g : ℝ}
    (hg : ∀ i, hcWeight X d a i ≤ g) :
    normSq (hcU P X y d a) ≤ g * hcRho P X y d a := by
  unfold hcU
  refine le_trans (complementProj_mulVec_normSq_le X hX_inv _) ?_
  rw [normSq_eq_sum_sq, hcRho, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  calc (hcWeight X d a i * meanResidual P X y i) ^ 2
      = hcWeight X d a i * (hcWeight X d a i * meanResidual P X y i ^ 2) := by ring
    _ ≤ g * (hcWeight X d a i * meanResidual P X y i ^ 2) :=
        mul_le_mul_of_nonneg_right (hg i) (mul_nonneg (hcWeight_nonneg hd i) (sq_nonneg _))

omit [IsProbabilityMeasure P] in
/-- `‖u‖ ≤ √g·√ρ²`. -/
lemma sqrt_normSq_hcU_le_gmax (hX_inv : IsUnit (Xᵀ * X).det) (hd : ∀ i, 1 ≤ d i) {g : ℝ}
    (hg : ∀ i, hcWeight X d a i ≤ g) :
    √(normSq (hcU P X y d a)) ≤ √g * √(hcRho P X y d a) := by
  rw [← Real.sqrt_mul' _ (hcRho_nonneg hd)]
  exact Real.sqrt_le_sqrt (normSq_hcU_le_gmax hX_inv hd hg)

/-! ### Milestone D: the variance bound with explicit `ρ` -/

omit [IsProbabilityMeasure P] in
/-- `0 ≤ B₃` once there is an observation. -/
lemma FiniteSampleBundle.B₃_nonneg (A : FiniteSampleBundle P X y) (hn : 0 < n) : 0 ≤ A.B₃ :=
  le_trans (integral_nonneg fun _ => pow_nonneg (abs_nonneg _) 3) (A.h3 ⟨0, hn⟩)

omit [IsProbabilityMeasure P] in
lemma cantelliV0_nonneg {s_max κ : ℝ} (hκ : 1 ≤ κ) : 0 ≤ cantelliV0 X d a s_max κ := by
  unfold cantelliV0
  have h1 : 0 ≤ ∑ i, hcM X d a i i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h2 : 0 ≤ ∑ i, ∑ j, (if i = j then (0 : ℝ) else hcM X d a i j ^ 2) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
  have hs : 0 ≤ s_max ^ 4 := by positivity
  have hκ' : 0 ≤ κ - 1 := by linarith
  positivity

omit [IsProbabilityMeasure P] in
lemma cantelliS_nonneg : 0 ≤ cantelliS X d a := Real.sqrt_nonneg _

/-- `Var ν̂ ≤ V₀ + 4s_max²·g·ρ² + 4B₃·S·√g·√ρ²`. -/
theorem FiniteSampleBundle.variance_hcVar_le_cantelli (A : FiniteSampleBundle P X y)
    (hd : ∀ i, 1 ≤ d i) (hκ : 1 ≤ A.κ) (hB₃ : 0 ≤ A.B₃) {g : ℝ}
    (hg : ∀ i, hcWeight X d a i ≤ g) :
    Var[hcVar X d y a; P]
      ≤ cantelliV0 X d a A.s_max A.κ
        + 4 * A.s_max ^ 2 * g * hcRho P X y d a
        + 4 * A.B₃ * cantelliS X d a * √g * √(hcRho P X y d a) := by
  rw [A.variance_hcVar]
  unfold cantelliV0
  have hσ_nn : ∀ i, 0 ≤ centralMoment (y i) 2 P := fun i => integral_nonneg fun _ => sq_nonneg _
  have hσ4 : ∀ i, centralMoment (y i) 2 P ^ 2 ≤ A.s_max ^ 4 := fun i => by
    calc centralMoment (y i) 2 P ^ 2 ≤ (A.s_max ^ 2) ^ 2 :=
          pow_le_pow_left₀ (hσ_nn i) (A.hvar_ub i) 2
      _ = A.s_max ^ 4 := by ring
  have h1 : ∑ i, hcM X d a i i ^ 2 * (centralMoment (y i) 4 P - centralMoment (y i) 2 P ^ 2)
      ≤ (A.κ - 1) * A.s_max ^ 4 * ∑ i, hcM X d a i i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hb : centralMoment (y i) 4 P - centralMoment (y i) 2 P ^ 2
        ≤ (A.κ - 1) * A.s_max ^ 4 := by
      have h := A.h4 i
      have h2 : (A.κ - 1) * centralMoment (y i) 2 P ^ 2 ≤ (A.κ - 1) * A.s_max ^ 4 :=
        mul_le_mul_of_nonneg_left (hσ4 i) (sub_nonneg.mpr hκ)
      nlinarith
    calc hcM X d a i i ^ 2 * (centralMoment (y i) 4 P - centralMoment (y i) 2 P ^ 2)
        ≤ hcM X d a i i ^ 2 * ((A.κ - 1) * A.s_max ^ 4) :=
          mul_le_mul_of_nonneg_left hb (sq_nonneg _)
      _ = (A.κ - 1) * A.s_max ^ 4 * hcM X d a i i ^ 2 := by ring
  have h2 : ∑ i, ∑ j, (if i = j then 0
        else hcM X d a i j ^ 2 * (centralMoment (y i) 2 P * centralMoment (y j) 2 P))
      ≤ A.s_max ^ 4 * ∑ i, ∑ j, (if i = j then 0 else hcM X d a i j ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs
    · simp
    · have hσσ : centralMoment (y i) 2 P * centralMoment (y j) 2 P ≤ A.s_max ^ 4 := by
        calc centralMoment (y i) 2 P * centralMoment (y j) 2 P
            ≤ A.s_max ^ 2 * A.s_max ^ 2 :=
              mul_le_mul (A.hvar_ub i) (A.hvar_ub j) (hσ_nn j) (sq_nonneg _)
          _ = A.s_max ^ 4 := by ring
      calc hcM X d a i j ^ 2 * (centralMoment (y i) 2 P * centralMoment (y j) 2 P)
          ≤ hcM X d a i j ^ 2 * A.s_max ^ 4 := mul_le_mul_of_nonneg_left hσσ (sq_nonneg _)
        _ = A.s_max ^ 4 * hcM X d a i j ^ 2 := by ring
  have h3 : ∑ i, hcU P X y d a i ^ 2 * centralMoment (y i) 2 P
      ≤ A.s_max ^ 2 * (g * hcRho P X y d a) := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (normSq_hcU_le_gmax A.hX_inv hd hg)
      (sq_nonneg _))
    rw [normSq_eq_sum_sq, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    calc hcU P X y d a i ^ 2 * centralMoment (y i) 2 P ≤ hcU P X y d a i ^ 2 * A.s_max ^ 2 :=
          mul_le_mul_of_nonneg_left (A.hvar_ub i) (sq_nonneg _)
      _ = A.s_max ^ 2 * hcU P X y d a i ^ 2 := by ring
  have h4 : ∑ i, hcM X d a i i * hcU P X y d a i * ∫ ω, centredErr P y i ω ^ 3 ∂P
      ≤ A.B₃ * (cantelliS X d a * (√g * √(hcRho P X y d a))) := by
    have h4a : ∑ i, hcM X d a i i * hcU P X y d a i * ∫ ω, centredErr P y i ω ^ 3 ∂P
        ≤ A.B₃ * ∑ i, hcM X d a i i * |hcU P X y d a i| := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have hM := hcM_diag_nonneg (X := X) (a := a) hd i
      have h3 := A.abs_third_moment_le i
      calc hcM X d a i i * hcU P X y d a i * ∫ ω, centredErr P y i ω ^ 3 ∂P
          ≤ hcM X d a i i * |hcU P X y d a i * ∫ ω, centredErr P y i ω ^ 3 ∂P| := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left (le_abs_self _) hM
        _ = hcM X d a i i * (|hcU P X y d a i| * |∫ ω, centredErr P y i ω ^ 3 ∂P|) := by
            rw [abs_mul]
        _ ≤ hcM X d a i i * (|hcU P X y d a i| * A.B₃) := by
            gcongr
        _ = A.B₃ * (hcM X d a i i * |hcU P X y d a i|) := by ring
    refine le_trans h4a (mul_le_mul_of_nonneg_left ?_ hB₃)
    refine le_trans sum_hcM_abs_hcU_le ?_
    exact mul_le_mul_of_nonneg_left (sqrt_normSq_hcU_le_gmax A.hX_inv hd hg) (Real.sqrt_nonneg _)
  nlinarith [h1, h2, h3, h4]

/-! ### Milestone E: the per-term maxima over `ρ²` -/

private lemma cantelli_e1 {V0 x am : ℝ} (hV0 : 0 ≤ V0) (hx : 0 ≤ x) (ham : 0 < am) :
    V0 ≤ V0 / am ^ 2 * (x + am) ^ 2 := by
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have : am ^ 2 ≤ (x + am) ^ 2 := pow_le_pow_left₀ ham.le (by linarith) 2
  nlinarith

private lemma cantelli_e2 {x am : ℝ} (ham : 0 < am) :
    4 * x ≤ 1 / am * (x + am) ^ 2 := by
  rw [one_div, inv_mul_eq_div, le_div_iff₀ ham]
  nlinarith [sq_nonneg (x - am)]

private lemma cantelli_e3 {x am : ℝ} (hx : 0 ≤ x) (ham : 0 < am) :
    4 * √x ≤ (3 * √3 / 4) / am ^ (3 / 2 : ℝ) * (x + am) ^ 2 := by
  obtain ⟨b, hb, rfl⟩ : ∃ b : ℝ, 0 < b ∧ am = 3 * b ^ 2 :=
    ⟨√(am / 3), Real.sqrt_pos.mpr (by positivity), by
      rw [Real.sq_sqrt (by positivity)]
      ring⟩
  set s : ℝ := √x with hs_def
  have hs : 0 ≤ s := Real.sqrt_nonneg x
  have hx_eq : x = s ^ 2 := (Real.sq_sqrt hx).symm
  have h32 : (3 * b ^ 2) ^ (3 / 2 : ℝ) = 3 * √3 * b ^ 3 := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by positivity), Real.rpow_one,
      ← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num), Real.sqrt_sq hb.le]
    ring
  have key : 16 * s * b ^ 3 ≤ (s ^ 2 + 3 * b ^ 2) ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg (s - b)) (by positivity : 0 ≤ s ^ 2 + 2 * s * b + 9 * b ^ 2)]
  rw [h32, hx_eq, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have h3 : 0 < √3 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 3 * √3)]

/-! ### Milestone F: the variance-event bound -/

omit [IsProbabilityMeasure P] in
/-- `q̄ ≥ 0`. -/
lemma cantelliQBar_nonneg {s_min s_max B₃ κ g θ : ℝ} (hκ : 1 ≤ κ) (hB₃ : 0 ≤ B₃) (hg : 0 ≤ g)
    (hA : 0 < aMinus X d a s_min s_max θ) :
    0 ≤ cantelliQBar X d a s_min s_max B₃ κ g θ := by
  unfold cantelliQBar
  have h0 := cantelliV0_nonneg (X := X) (d := d) (a := a) (s_max := s_max) hκ
  have hS := cantelliS_nonneg (X := X) (d := d) (a := a)
  have h32 : 0 < aMinus X d a s_min s_max θ ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hA _
  positivity

set_option linter.unusedVariables false in
/-- **The Cantelli variance-event bound**, free of the misspecification tolerance and of any
leverage condition: for `θ > 0` with `a₋(θ) > 0`,
`P(ν̂ ≤ θν) ≤ q̄(θ)/(1 + q̄(θ))`. -/
theorem FiniteSampleBundle.cantelli_variance_event_le (A : FiniteSampleBundle P X y)
    (hd : ∀ i, 1 ≤ d i) (ha : a ≠ 0) {θ g : ℝ} (hθ0 : 0 < θ)
    (hg : ∀ i, hcWeight X d a i ≤ g) (hA : 0 < aMinus X d a A.s_min A.s_max θ) :
    P.real {ω | hcVar X d y a ω ≤ θ * contrastVar P X y a}
      ≤ cantelliVarianceEventBound X d a A.s_min A.s_max A.B₃ A.κ g θ := by
  have hν := A.contrastVar_pos (a := a) ha
  have hn := pos_of_contrastVar_pos hν
  have hκ := A.one_le_κ hn
  have hB₃ := A.B₃_nonneg hn
  have hg0 : 0 ≤ g := le_trans (hcWeight_nonneg hd ⟨0, hn⟩) (hg _)
  have hρ := hcRho_nonneg (P := P) (X := X) (y := y) (d := d) (a := a) hd
  set ρ : ℝ := hcRho P X y d a with hρ_def
  set am : ℝ := aMinus X d a A.s_min A.s_max θ with ham_def
  set q : ℝ := cantelliQBar X d a A.s_min A.s_max A.B₃ A.κ g θ with hq_def
  set V0 : ℝ := cantelliV0 X d a A.s_max A.κ with hV0_def
  set S : ℝ := cantelliS X d a with hS_def
  have hV0 : 0 ≤ V0 := cantelliV0_nonneg hκ
  have hS : 0 ≤ S := cantelliS_nonneg
  have hq : 0 ≤ q := cantelliQBar_nonneg hκ hB₃ hg0 hA
  -- F1: the mean gap
  set gap : ℝ := ∫ ω, hcVar X d y a ω ∂P - θ * contrastVar P X y a with hgap_def
  have hgap : ρ + am ≤ gap := A.integral_hcVar_sub_ge
  have hgap_pos : 0 < gap := by linarith
  -- F2: `Var ν̂ ≤ q̄ (ρ² + a₋)²`
  have hV := A.variance_hcVar_le_cantelli (d := d) (a := a) hd hκ hB₃ hg
  have t1 : V0 ≤ V0 / am ^ 2 * (ρ + am) ^ 2 := cantelli_e1 hV0 hρ hA
  have t2 : 4 * A.s_max ^ 2 * g * ρ ≤ A.s_max ^ 2 * g / am * (ρ + am) ^ 2 := by
    have := mul_le_mul_of_nonneg_left (cantelli_e2 (x := ρ) hA)
      (by positivity : 0 ≤ A.s_max ^ 2 * g)
    calc 4 * A.s_max ^ 2 * g * ρ = A.s_max ^ 2 * g * (4 * ρ) := by ring
      _ ≤ A.s_max ^ 2 * g * (1 / am * (ρ + am) ^ 2) := this
      _ = A.s_max ^ 2 * g / am * (ρ + am) ^ 2 := by ring
  have t3 : 4 * A.B₃ * S * √g * √ρ
      ≤ (3 * √3 / 4) * A.B₃ * S * √g / am ^ (3 / 2 : ℝ) * (ρ + am) ^ 2 := by
    have := mul_le_mul_of_nonneg_left (cantelli_e3 hρ hA)
      (by positivity : 0 ≤ A.B₃ * S * √g)
    calc 4 * A.B₃ * S * √g * √ρ = A.B₃ * S * √g * (4 * √ρ) := by ring
      _ ≤ A.B₃ * S * √g * ((3 * √3 / 4) / am ^ (3 / 2 : ℝ) * (ρ + am) ^ 2) := this
      _ = (3 * √3 / 4) * A.B₃ * S * √g / am ^ (3 / 2 : ℝ) * (ρ + am) ^ 2 := by ring
  have hq_expand : q * (ρ + am) ^ 2
      = V0 / am ^ 2 * (ρ + am) ^ 2 + A.s_max ^ 2 * g / am * (ρ + am) ^ 2
        + (3 * √3 / 4) * A.B₃ * S * √g / am ^ (3 / 2 : ℝ) * (ρ + am) ^ 2 := by
    rw [hq_def]
    unfold cantelliQBar
    ring
  have hVq : Var[hcVar X d y a; P] ≤ q * (ρ + am) ^ 2 := by linarith
  -- F3: `(ρ² + a₋)² ≤ gap²`
  have hVgap : Var[hcVar X d y a; P] ≤ q * gap ^ 2 :=
    le_trans hVq (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hgap 2) hq)
  -- F4: Cantelli
  have h := measureReal_le_cantelli A.memLp_two_hcVar (m := ∫ ω, hcVar X d y a ω ∂P)
    (c := θ * contrastVar P X y a) le_rfl hVgap (by linarith)
  refine le_trans h (le_of_eq ?_)
  unfold cantelliVarianceEventBound
  rw [← hq_def, ← hgap_def]
  have hgap2 : gap ^ 2 ≠ 0 := by positivity
  rw [show q * gap ^ 2 + gap ^ 2 = (1 + q) * gap ^ 2 by ring, mul_div_mul_right _ _ hgap2]

/-! ### Milestone G: the tail theorems -/

/-- **One-sided tail, Cantelli route.** For `t > 0`, `θ > 0` with `a₋(θ) > 0`:
`P(T > t) ≤ (1 − Φ(t√θ)) + η(t√θ) + q̄/(1 + q̄)`. No leverage condition, no
misspecification tolerance. -/
theorem finiteN_tail_oneSided_cantelli (A : FiniteSampleBundle P X y) (hd : ∀ i, 1 ≤ d i)
    (ha : a ≠ 0) {η : ℝ → ℝ}
    (hη : ∀ z, |cdf (P.map (contrastStat P X y a)) z - cdf (gaussianReal 0 1) z| ≤ η z)
    {t θ g : ℝ} (ht : 0 < t) (hθ0 : 0 < θ) (hg : ∀ i, hcWeight X d a i ≤ g)
    (hA : 0 < aMinus X d a A.s_min A.s_max θ) :
    P.real {ω | t < hcStudent P X y d a ω} ≤
      (1 - cdf (gaussianReal 0 1) (t * √θ)) + η (t * √θ)
        + cantelliVarianceEventBound X d a A.s_min A.s_max A.B₃ A.κ g θ := by
  have hZ : Measurable (contrastStat P X y a) := measurable_contrastStat A.hy_meas
  have hsplit := studentised_tail_le (P := P) (Z := contrastStat P X y a) (V := hcVar X d y a)
    (ν := contrastVar P X y a) (θ := θ) ht hθ0 contrastVar_nonneg
  have h1 := tail_upper_of_cdf hZ hη (t * √θ)
  have h6 := A.cantelli_variance_event_le hd ha hθ0 hg hA
  unfold hcStudent
  linarith

/-- **Lower tail, Cantelli route:** `P(T < −t) ≤ Φ(−t√θ) + η(−t√θ) + q̄/(1 + q̄)`. -/
theorem finiteN_tail_lower_cantelli (A : FiniteSampleBundle P X y) (hd : ∀ i, 1 ≤ d i)
    (ha : a ≠ 0) {η : ℝ → ℝ}
    (hη : ∀ z, |cdf (P.map (contrastStat P X y a)) z - cdf (gaussianReal 0 1) z| ≤ η z)
    {t θ g : ℝ} (ht : 0 < t) (hθ0 : 0 < θ) (hg : ∀ i, hcWeight X d a i ≤ g)
    (hA : 0 < aMinus X d a A.s_min A.s_max θ) :
    P.real {ω | hcStudent P X y d a ω < -t} ≤
      cdf (gaussianReal 0 1) (-(t * √θ)) + η (-(t * √θ))
        + cantelliVarianceEventBound X d a A.s_min A.s_max A.B₃ A.κ g θ := by
  have hZ : Measurable (contrastStat P X y a) := measurable_contrastStat A.hy_meas
  have hset : {ω | hcStudent P X y d a ω < -t}
      = {ω | t < (-contrastStat P X y a ω) * √(contrastVar P X y a / hcVar X d y a ω)} := by
    ext ω
    simp only [Set.mem_setOf_eq, hcStudent, neg_mul]
    constructor <;> intro h <;> linarith
  have hsplit := studentised_tail_le (P := P) (Z := fun ω => -contrastStat P X y a ω)
    (V := hcVar X d y a) (ν := contrastVar P X y a) (θ := θ) ht hθ0 contrastVar_nonneg
  have hset2 : {ω | t * √θ < -contrastStat P X y a ω}
      = {ω | contrastStat P X y a ω < -(t * √θ)} := by
    ext ω
    simp only [Set.mem_setOf_eq, lt_neg]
  have h1 := tail_lower_of_cdf hZ hη (t * √θ)
  have h6 := A.cantelli_variance_event_le hd ha hθ0 hg hA
  rw [hset]
  rw [hset2] at hsplit
  linarith

/-- Symmetry of the standard normal distribution function: `Φ(−s) = 1 − Φ(s)`. -/
lemma gaussianReal_cdf_neg (s : ℝ) :
    cdf (gaussianReal 0 1) (-s) = 1 - cdf (gaussianReal 0 1) s := by
  haveI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal one_ne_zero
  have hmap : (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg, neg_zero]
  rw [cdf_eq_real, cdf_eq_real]
  have h1 : (gaussianReal 0 1).real (Set.Iic (-s)) = (gaussianReal 0 1).real (Set.Ici s) := by
    rw [measureReal_def, measureReal_def]
    congr 1
    conv_lhs => rw [← hmap]
    rw [Measure.map_apply measurable_neg measurableSet_Iic]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_Ici, neg_le_neg_iff]
  rw [h1, ← measureReal_congr (Ioi_ae_eq_Ici (a := s))]
  have := measureReal_compl (μ := gaussianReal 0 1) (s := Set.Iic s) measurableSet_Iic
  rw [Set.compl_Iic, probReal_univ] at this
  exact this

/-- **Two-sided tail, Cantelli route:** the two one-sided splits share the single variance
event, so `P(|T| > t) ≤ 2(1 − Φ(t√θ)) + η(t√θ) + η(−t√θ) + q̄/(1 + q̄)`. -/
theorem finiteN_tail_twoSided_cantelli (A : FiniteSampleBundle P X y) (hd : ∀ i, 1 ≤ d i)
    (ha : a ≠ 0) {η : ℝ → ℝ}
    (hη : ∀ z, |cdf (P.map (contrastStat P X y a)) z - cdf (gaussianReal 0 1) z| ≤ η z)
    {t θ g : ℝ} (ht : 0 < t) (hθ0 : 0 < θ) (hg : ∀ i, hcWeight X d a i ≤ g)
    (hA : 0 < aMinus X d a A.s_min A.s_max θ) :
    P.real {ω | t < |hcStudent P X y d a ω|} ≤
      2 * (1 - cdf (gaussianReal 0 1) (t * √θ)) + η (t * √θ) + η (-(t * √θ))
        + cantelliVarianceEventBound X d a A.s_min A.s_max A.B₃ A.κ g θ := by
  have hZ : Measurable (contrastStat P X y a) := measurable_contrastStat A.hy_meas
  have hmono := measureReal_mono (μ := P)
    (abs_hcStudent_subset (P := P) (X := X) (y := y) (d := d) (a := a) ht hθ0)
  have hu1 := measureReal_union_le (μ := P)
    ({ω | t * √θ < contrastStat P X y a ω} ∪ {ω | contrastStat P X y a ω < -(t * √θ)})
    {ω | hcVar X d y a ω ≤ θ * contrastVar P X y a}
  have hu2 := measureReal_union_le (μ := P) {ω | t * √θ < contrastStat P X y a ω}
    {ω | contrastStat P X y a ω < -(t * √θ)}
  have h1 := tail_upper_of_cdf hZ hη (t * √θ)
  have h1' := tail_lower_of_cdf hZ hη (t * √θ)
  have h6 := A.cantelli_variance_event_le hd ha hθ0 hg hA
  have hsym := gaussianReal_cdf_neg (t * √θ)
  linarith

/-- The two-sided bound with a symmetric approximation input: `2(1 − Φ(t√θ)) + 2η(t√θ) + …`. -/
theorem finiteN_tail_twoSided_cantelli' (A : FiniteSampleBundle P X y) (hd : ∀ i, 1 ≤ d i)
    (ha : a ≠ 0) {η : ℝ → ℝ}
    (hη : ∀ z, |cdf (P.map (contrastStat P X y a)) z - cdf (gaussianReal 0 1) z| ≤ η z)
    {t θ g : ℝ} (ht : 0 < t) (hθ0 : 0 < θ) (hg : ∀ i, hcWeight X d a i ≤ g)
    (hA : 0 < aMinus X d a A.s_min A.s_max θ) (hηsym : η (-(t * √θ)) ≤ η (t * √θ)) :
    P.real {ω | t < |hcStudent P X y d a ω|} ≤
      2 * (1 - cdf (gaussianReal 0 1) (t * √θ)) + 2 * η (t * √θ)
        + cantelliVarianceEventBound X d a A.s_min A.s_max A.B₃ A.κ g θ := by
  have h := finiteN_tail_twoSided_cantelli A hd ha hη ht hθ0 hg hA
  linarith

/-! ### Milestone H: HC3 needs no condition at all -/

omit [IsProbabilityMeasure P] in
/-- The `i = j` term of the Gram sum: `wⱼ(1 − hⱼ)² ≤ Qⱼⱼ`. -/
lemma hcWeight_mul_sq_le_hcM_diag (hd : ∀ i, 1 ≤ d i) (j : Fin n) :
    hcWeight X d a j * (1 - leverage X j) ^ 2 ≤ hcM X d a j j := by
  rw [hcM_apply]
  have hQ : complementProj X j j = 1 - leverage X j := by
    simp [complementProj, leverage]
  calc hcWeight X d a j * (1 - leverage X j) ^ 2
      = hcWeight X d a j * (complementProj X j j * complementProj X j j) := by
        rw [hQ]
        ring
    _ ≤ ∑ k, hcWeight X d a k * (complementProj X k j * complementProj X k j) :=
        Finset.single_le_sum
          (f := fun k => hcWeight X d a k * (complementProj X k j * complementProj X k j))
          (fun k _ => mul_nonneg (hcWeight_nonneg hd k) (mul_self_nonneg _))
          (Finset.mem_univ j)

omit [IsProbabilityMeasure P] in
/-- The HC3 multipliers `(1 − hⱼ)⁻²` are at least one. -/
lemma one_le_hc3 (hlev : ∀ j, leverage X j < 1) (j : Fin n) :
    1 ≤ (1 - leverage X j)⁻¹ ^ 2 := by
  have hpos : 0 < 1 - leverage X j := by linarith [hlev j]
  have h1 : 1 ≤ (1 - leverage X j)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hpos, one_mul]
    linarith [leverage_nonneg X j]
  exact one_le_pow₀ h1

omit [IsProbabilityMeasure P] in
set_option linter.unusedVariables false in
/-- For the HC3 multipliers, `a₋(θ) > 0` for every `θ ∈ (0, 1)`, whatever the leverages. -/
lemma FiniteSampleBundle.aMinus_pos_hc3 (A : FiniteSampleBundle P X y) (ha : a ≠ 0)
    (hlev : ∀ j, leverage X j < 1) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hd3 : ∀ j, d j = (1 - leverage X j)⁻¹ ^ 2) :
    0 < aMinus X d a A.s_min A.s_max θ := by
  have hd : ∀ j, 1 ≤ d j := fun j => by rw [hd3 j]; exact one_le_hc3 hlev j
  -- `Qⱼⱼ ≥ γⱼ²`, hence `cⱼ ≥ (1 − θ)γⱼ² ≥ 0`
  have hc : ∀ j, (1 - θ) * olsWeights X a j ^ 2 ≤ cantelliC X d a θ j := by
    intro j
    have hpos : (1 - leverage X j) ≠ 0 := by linarith [hlev j]
    have h := hcWeight_mul_sq_le_hcM_diag (X := X) (a := a) hd j
    have hw : hcWeight X d a j * (1 - leverage X j) ^ 2 = olsWeights X a j ^ 2 := by
      unfold hcWeight
      rw [hd3 j]
      field_simp
    rw [hw] at h
    unfold cantelliC
    nlinarith [h]
  have hγ : 0 < normSq (olsWeights X a) := normSq_olsWeights_pos X A.hX_inv a (Ne.symm ha)
  have hsmin : 0 < A.s_min ^ 2 := pow_pos A.hs_min_pos 2
  have h1θ : 0 < 1 - θ := by linarith
  calc (0 : ℝ) < (1 - θ) * A.s_min ^ 2 * normSq (olsWeights X a) := by positivity
    _ = ∑ j, A.s_min ^ 2 * ((1 - θ) * olsWeights X a j ^ 2) := by
        rw [normSq_eq_sum_sq, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ aMinus X d a A.s_min A.s_max θ := by
        unfold aMinus
        refine Finset.sum_le_sum fun j _ => ?_
        have hcj : 0 ≤ cantelliC X d a θ j := le_trans (by positivity) (hc j)
        rw [if_pos hcj]
        exact mul_le_mul_of_nonneg_left (hc j) hsmin.le

end Cantelli

/-! ### Sanity checks: the intercept-only design with four observations -/

section SanityCheck

/-- The intercept-only design with four observations. -/
noncomputable def X4 : Matrix (Fin 4) (Fin 1) ℝ := Matrix.of fun _ _ => 1

lemma X4_gram : (X4ᵀ * X4) = Matrix.of fun _ _ => (4 : ℝ) := by
  ext i j
  simp [X4, Matrix.mul_apply]

lemma X4_gram_inv : (X4ᵀ * X4)⁻¹ = Matrix.of fun _ _ => (1 / 4 : ℝ) := by
  rw [X4_gram, Matrix.inv_def]
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.adjugate_fin_one]

lemma olsWeights_X4 (i : Fin 4) : olsWeights X4 ![1] i = 1 / 4 := by
  unfold olsWeights
  rw [X4_gram_inv]
  simp [X4, Matrix.mulVec, dotProduct]

lemma leverage_X4 (i : Fin 4) : leverage X4 i = 1 / 4 := by
  unfold leverage hatMatrix
  rw [X4_gram_inv]
  simp [X4, Matrix.mul_apply]

lemma hcM_X4 (i j : Fin 4) :
    hcM X4 (fun _ => 1) ![1] i j = if i = j then 3 / 64 else -(1 / 64) := by
  rw [hcM_apply]
  have hQ : ∀ k l : Fin 4, complementProj X4 k l = if k = l then 3 / 4 else -(1 / 4) := by
    intro k l
    unfold complementProj hatMatrix
    rw [X4_gram_inv]
    simp [X4, Matrix.mul_apply, Matrix.one_apply]
    split_ifs <;> norm_num
  simp only [hQ, hcWeight, olsWeights_X4]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_four] <;> norm_num

/-- `c_j(1/2) = 1/64` (HC0, `s_min = s_max = 1`). -/
example : cantelliC X4 (fun _ => 1) ![1] (1 / 2) 0 = 1 / 64 := by
  simp [cantelliC, hcM_X4, olsWeights_X4]
  norm_num

/-- `a₋(1/2) = 1/16`. -/
example : aMinus X4 (fun _ => 1) ![1] 1 1 (1 / 2) = 1 / 16 := by
  simp [aMinus, cantelliC, hcM_X4, olsWeights_X4]
  norm_num

/-- `V₀ = 3/128` with `κ = 3`. -/
example : cantelliV0 X4 (fun _ => 1) ![1] 1 3 = 3 / 128 := by
  simp [cantelliV0, hcM_X4, Fin.sum_univ_four]
  norm_num

end SanityCheck

end
