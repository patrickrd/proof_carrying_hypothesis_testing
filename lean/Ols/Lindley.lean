/-
Copyright (c) 2026 Patrick Rubin-Delanchy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Rubin-Delanchy, Andrew Jones
AI-generated (see the top-level README); not audited by the authors.
-/
import Mathlib
import Ols.FiniteN

/-!
# Lindley's paradox

`Y₁,…,Yₙ` i.i.d. `normal(μ, σ²)` with `σ²` known; test `H₀ : μ = μ₀` against
`μ | H₁ ~ Uniform[μ₀ − l, μ₀ + l]`, prior weight `c ∈ (0,1)` on `H₀`. With `Ȳ` the sufficient
average, the two-sided p-value is `P = 2(1 − Φ(√n |Ȳ − μ₀|/σ))` and the posterior of `H₀` is
`π = c p₀(Ȳ)/(c p₀(Ȳ) + (1−c) p₁(Ȳ))`, where `p₀` is the `normal(μ₀, σ²/n)` density and `p₁`
the uniform mixture of the `normal(μ, σ²/n)` densities over the prior.

**Lindley's paradox** (`lindley`): for every `ε ∈ (0,1)` there are `n` and data with `P ≤ ε`
and `π ≥ 1 − ε`. The engine is the sequence `Ȳₙ = μ₀ + λσ/√n`: along it `√n|Ȳₙ − μ₀|/σ = λ`
so `P` is constant, while `p₀(Ȳₙ) = √n · e^{−λ²/2}/√(2πσ²) → ∞` and `p₁(Ȳₙ) ≤ 1/(2l)` stays
bounded, so `π → 1`. The proof below picks `λ` from `Φ(λ) → 1` and then an explicit `n`.

See `LINDLEY_EVALUE.md` for the context and the working protocol.
-/

open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal Topology

namespace Lindley

/-- The variance `σ²/n` of the average, as a nonnegative real. -/
noncomputable def v (σ : ℝ) (n : ℕ) : ℝ≥0 := ⟨σ ^ 2 / n, by positivity⟩

/-- The null density `p₀(y)` of `Ȳ ~ normal(μ₀, σ²/n)`. -/
noncomputable def g0 (σ μ₀ : ℝ) (n : ℕ) (y : ℝ) : ℝ := gaussianPDFReal μ₀ (v σ n) y

/-- The alternative density `p₁(y)`: the uniform mixture over `μ ∈ [μ₀ − l, μ₀ + l]`. -/
noncomputable def g1 (σ μ₀ l : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  (1 / (2 * l)) * ∫ μ in Set.Icc (μ₀ - l) (μ₀ + l), gaussianPDFReal μ (v σ n) y

/-- The two-sided p-value `2(1 − Φ(√n |y − μ₀|/σ))`. -/
noncomputable def pval (σ μ₀ : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  2 * (1 - cdf (gaussianReal 0 1) (Real.sqrt n * |y - μ₀| / σ))

/-- The posterior probability of `H₀`. -/
noncomputable def post (σ μ₀ l c : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  (c * g0 σ μ₀ n y) / (c * g0 σ μ₀ n y + (1 - c) * g1 σ μ₀ l n y)

lemma coe_v (σ : ℝ) (n : ℕ) : ((v σ n : ℝ≥0) : ℝ) = σ ^ 2 / n := rfl

lemma v_ne_zero {σ : ℝ} (hσ : 0 < σ) {n : ℕ} (hn : 1 ≤ n) : v σ n ≠ 0 := by
  intro h
  have h' : ((v σ n : ℝ≥0) : ℝ) = 0 := by rw [h]; rfl
  rw [coe_v] at h'
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have : 0 < σ ^ 2 / (n : ℝ) := by positivity
  linarith

/-- Symmetry of the Gaussian density in mean and argument. -/
lemma gaussianPDFReal_symm (μ : ℝ) (w : ℝ≥0) (y : ℝ) :
    gaussianPDFReal μ w y = gaussianPDFReal y w μ := by
  simp only [gaussianPDFReal]
  congr 2
  ring

lemma g0_pos {σ : ℝ} (hσ : 0 < σ) (μ₀ : ℝ) {n : ℕ} (hn : 1 ≤ n) (y : ℝ) :
    0 < g0 σ μ₀ n y :=
  gaussianPDFReal_pos _ _ _ (v_ne_zero hσ hn)

/-- `0 ≤ p₁`. -/
lemma g1_nonneg (σ μ₀ : ℝ) {l : ℝ} (hl : 0 < l) (n : ℕ) (y : ℝ) : 0 ≤ g1 σ μ₀ l n y :=
  mul_nonneg (by positivity) (integral_nonneg fun μ => gaussianPDFReal_nonneg _ _ _)

/-- `p₁ ≤ 1/(2l)`: the mixture density is bounded by the prior density. -/
lemma g1_le {σ : ℝ} (hσ : 0 < σ) (μ₀ : ℝ) {l : ℝ} (hl : 0 < l) {n : ℕ} (hn : 1 ≤ n)
    (y : ℝ) : g1 σ μ₀ l n y ≤ 1 / (2 * l) := by
  unfold g1
  have hsymm : (fun μ => gaussianPDFReal μ (v σ n) y) = fun μ => gaussianPDFReal y (v σ n) μ :=
    funext fun μ => gaussianPDFReal_symm μ _ y
  rw [hsymm]
  have hI : ∫ μ in Set.Icc (μ₀ - l) (μ₀ + l), gaussianPDFReal y (v σ n) μ ≤ 1 := by
    have h1 : ENNReal.ofReal (∫ μ in Set.Icc (μ₀ - l) (μ₀ + l), gaussianPDFReal y (v σ n) μ)
        = gaussianReal y (v σ n) (Set.Icc (μ₀ - l) (μ₀ + l)) :=
      (gaussianReal_apply_eq_integral y (v_ne_zero hσ hn) _).symm
    have h2 : gaussianReal y (v σ n) (Set.Icc (μ₀ - l) (μ₀ + l)) ≤ 1 := prob_le_one
    rw [← h1] at h2
    exact ENNReal.ofReal_le_one.mp h2
  calc (1 / (2 * l)) * ∫ μ in Set.Icc (μ₀ - l) (μ₀ + l), gaussianPDFReal y (v σ n) μ
      ≤ (1 / (2 * l)) * 1 := mul_le_mul_of_nonneg_left hI (by positivity)
    _ = 1 / (2 * l) := mul_one _

/-- Along `yₙ = μ₀ + λσ/√n` the null density is `√n · e^{−λ²/2}/√(2πσ²)`. -/
lemma g0_seq {σ : ℝ} (hσ : 0 < σ) (μ₀ : ℝ) {n : ℕ} (hn : 1 ≤ n) (lam : ℝ) :
    g0 σ μ₀ n (μ₀ + lam * σ / Real.sqrt n)
      = Real.sqrt n / Real.sqrt (2 * π * σ ^ 2) * Real.exp (-lam ^ 2 / 2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn'
  have hs2 : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hn'.le
  simp only [g0, gaussianPDFReal, coe_v]
  have h1 : -(μ₀ + lam * σ / Real.sqrt n - μ₀) ^ 2 / (2 * (σ ^ 2 / n)) = -lam ^ 2 / 2 := by
    rw [show μ₀ + lam * σ / Real.sqrt n - μ₀ = lam * σ / Real.sqrt n by ring, div_pow, hs2]
    field_simp
  have h2 : (Real.sqrt (2 * π * (σ ^ 2 / n)))⁻¹ = Real.sqrt n / Real.sqrt (2 * π * σ ^ 2) := by
    rw [show 2 * π * (σ ^ 2 / (n : ℝ)) = (2 * π * σ ^ 2) / n by ring, Real.sqrt_div' _ hn'.le,
      inv_div]
  rw [h1, h2]

/-- Along `yₙ = μ₀ + λσ/√n` the standardised distance is `λ`, so the p-value is constant. -/
lemma pval_seq {σ : ℝ} (hσ : 0 < σ) (μ₀ : ℝ) {n : ℕ} (hn : 1 ≤ n) {lam : ℝ} (hlam : 0 < lam) :
    pval σ μ₀ n (μ₀ + lam * σ / Real.sqrt n) = 2 * (1 - cdf (gaussianReal 0 1) lam) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn'
  unfold pval
  congr 3
  rw [show μ₀ + lam * σ / Real.sqrt n - μ₀ = lam * σ / Real.sqrt n by ring,
    abs_of_pos (by positivity)]
  field_simp

/-- **Lindley's paradox.** A fixed significance and a near-certain posterior for `H₀`
occur together. -/
theorem lindley {σ μ₀ l c : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hc0 : 0 < c) (hc1 : c < 1)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ (n : ℕ) (y : ℝ), 1 ≤ n ∧ pval σ μ₀ n y ≤ ε ∧ post σ μ₀ l c n y ≥ 1 - ε := by
  -- choose the standardised distance `λ` so that the p-value is at most `ε`
  obtain ⟨lam, hlam, hΦ⟩ : ∃ lam : ℝ, 0 < lam ∧ 1 - ε / 2 < cdf (gaussianReal 0 1) lam := by
    have h := ((tendsto_cdf_atTop (μ := gaussianReal 0 1)).eventually_const_lt
      (by linarith : 1 - ε / 2 < 1)).and (eventually_gt_atTop 0)
    obtain ⟨lam, h1, h2⟩ := h.exists
    exact ⟨lam, h2, h1⟩
  -- the growth constant of the null density and the required size of `p₀`
  set K : ℝ := Real.exp (-lam ^ 2 / 2) / Real.sqrt (2 * π * σ ^ 2) with hK_def
  have hK : 0 < K := by positivity
  set A : ℝ := (1 - ε) * (1 - c) / (2 * l * ε * c) with hA_def
  have hA : 0 ≤ A := div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  -- an explicit sample size with `K √N ≥ A`
  set N : ℕ := ⌈(A / K) ^ 2⌉₊ + 1 with hN_def
  have hN1 : 1 ≤ N := Nat.le_add_left 1 _
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN1
  have hsqrtN : A / K ≤ Real.sqrt N := by
    have h1 : (A / K) ^ 2 ≤ (N : ℝ) := by
      rw [hN_def]
      push_cast
      linarith [Nat.le_ceil ((A / K) ^ 2)]
    calc A / K = Real.sqrt ((A / K) ^ 2) := (Real.sqrt_sq (div_nonneg hA hK.le)).symm
      _ ≤ Real.sqrt N := Real.sqrt_le_sqrt h1
  refine ⟨N, μ₀ + lam * σ / Real.sqrt N, hN1, ?_, ?_⟩
  · rw [pval_seq hσ μ₀ hN1 hlam]
    linarith
  · have hg0 : g0 σ μ₀ N (μ₀ + lam * σ / Real.sqrt N) = K * Real.sqrt N := by
      rw [g0_seq hσ μ₀ hN1 lam, hK_def]
      ring
    have hg0A : A ≤ g0 σ μ₀ N (μ₀ + lam * σ / Real.sqrt N) := by
      rw [hg0]
      calc A = K * (A / K) := by field_simp
        _ ≤ K * Real.sqrt N := mul_le_mul_of_nonneg_left hsqrtN hK.le
    have hg0pos := g0_pos hσ μ₀ hN1 (μ₀ + lam * σ / Real.sqrt N)
    have hg1 := g1_le hσ μ₀ hl hN1 (μ₀ + lam * σ / Real.sqrt N)
    have hg1nn := g1_nonneg σ μ₀ hl N (μ₀ + lam * σ / Real.sqrt N)
    set G0 := g0 σ μ₀ N (μ₀ + lam * σ / Real.sqrt N) with hG0
    set G1 := g1 σ μ₀ l N (μ₀ + lam * σ / Real.sqrt N) with hG1
    have hden : 0 < c * G0 + (1 - c) * G1 := by
      have : 0 ≤ (1 - c) * G1 := mul_nonneg (by linarith) hg1nn
      nlinarith [mul_pos hc0 hg0pos]
    unfold post
    rw [← hG0, ← hG1, ge_iff_le, le_div_iff₀ hden]
    -- `(1-ε)(1-c) G1 ≤ (1-ε)(1-c)/(2l) = ε c A ≤ ε c G0`
    have hAe : (1 - ε) * (1 - c) / (2 * l) = ε * c * A := by
      rw [hA_def]
      field_simp
    have h1 : (1 - ε) * (1 - c) * G1 ≤ (1 - ε) * (1 - c) / (2 * l) := by
      have := mul_le_mul_of_nonneg_left hg1 (mul_nonneg (by linarith : (0:ℝ) ≤ 1 - ε)
        (by linarith : (0:ℝ) ≤ 1 - c))
      rw [mul_one_div] at this
      exact this
    have h2 : ε * c * A ≤ ε * c * G0 := mul_le_mul_of_nonneg_left hg0A (by positivity)
    nlinarith [h1, h2, hAe]

/-! ## Calibration: the e-value's own p-value is `P`

With `E = p₁/p₀` and `S₀(x) = P_{H₀}(E ≥ x)`, we show `P(y) = S₀(E(y))`. The key fact is that
`E` is a strictly increasing function of `|y − μ₀|`: substituting `μ = μ₀ + u` in `p₁` gives
`p₁(y) = p₀(y) · F(y − μ₀)` with `F(z) = (1/2l) ∫_{-l}^{l} e^{-u²/(2v)} e^{zu/v} du`, and
symmetrising, `F(z) = (1/2l) ∫_{-l}^{l} e^{-u²/(2v)} cosh(zu/v) du`, which is strictly increasing
in `|z|`. -/

section Calibration

/-- The Gaussian kernel `e^{-u²/(2w)}`. -/
noncomputable def wker (w u : ℝ) : ℝ := Real.exp (-u ^ 2 / (2 * w))

/-- `F w l z = (1/2l) ∫_{-l}^{l} e^{-u²/(2w)} e^{zu/w} du`; the e-value is `F v l (y − μ₀)`. -/
noncomputable def F (w l z : ℝ) : ℝ :=
  (1 / (2 * l)) * ∫ u in (-l)..l, wker w u * Real.exp (z * u / w)

/-- The e-value (Bayes factor) `E = p₁/p₀`. -/
noncomputable def E (σ μ₀ l : ℝ) (n : ℕ) (y : ℝ) : ℝ := g1 σ μ₀ l n y / g0 σ μ₀ n y

/-- The null survival function of the e-value, `S₀(x) = P_{H₀}(E ≥ x)`. -/
noncomputable def S₀ (σ μ₀ l : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ((gaussianReal μ₀ (v σ n)) {y | x ≤ E σ μ₀ l n y}).toReal

lemma coe_v_pos {σ : ℝ} (hσ : 0 < σ) {n : ℕ} (hn : 1 ≤ n) : 0 < ((v σ n : ℝ≥0) : ℝ) := by
  rw [coe_v]
  have : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

lemma wker_pos (w u : ℝ) : 0 < wker w u := Real.exp_pos _

lemma continuous_wker_mul (w z : ℝ) :
    Continuous fun u => wker w u * Real.exp (z * u / w) := by
  unfold wker
  fun_prop

lemma continuous_wker_cosh (w z : ℝ) :
    Continuous fun u => wker w u * Real.cosh (z * u / w) := by
  unfold wker
  fun_prop

/-- Factorisation `p₁(y) = p₀(y) · F(y − μ₀)`. -/
lemma g1_eq_g0_mul_F {σ : ℝ} (hσ : 0 < σ) (μ₀ : ℝ) {l : ℝ} (hl : 0 < l) {n : ℕ} (hn : 1 ≤ n)
    (y : ℝ) : g1 σ μ₀ l n y = g0 σ μ₀ n y * F (v σ n) l (y - μ₀) := by
  have hw : 0 < ((v σ n : ℝ≥0) : ℝ) := coe_v_pos hσ hn
  unfold g1 F
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  have hsub : ∫ u in (-l)..l, gaussianPDFReal (u + μ₀) (v σ n) y
      = ∫ μ in (-l + μ₀)..(l + μ₀), gaussianPDFReal μ (v σ n) y :=
    intervalIntegral.integral_comp_add_right (fun μ => gaussianPDFReal μ (v σ n) y) μ₀
  rw [show μ₀ - l = -l + μ₀ by ring, show μ₀ + l = l + μ₀ by ring, ← hsub]
  have hpt : ∀ u, gaussianPDFReal (u + μ₀) (v σ n) y
      = g0 σ μ₀ n y * (wker (v σ n) u * Real.exp ((y - μ₀) * u / (v σ n))) := by
    intro u
    simp only [g0, gaussianPDFReal, wker, mul_assoc, ← Real.exp_add]
    congr 2
    field_simp
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- Symmetrisation: `F(z) = (1/2l) ∫_{-l}^{l} e^{-u²/(2w)} cosh(zu/w) du`. -/
lemma F_eq_cosh (w l z : ℝ) :
    F w l z = (1 / (2 * l)) * ∫ u in (-l)..l, wker w u * Real.cosh (z * u / w) := by
  unfold F
  congr 1
  have h1 : ∫ u in (-l)..l, wker w u * Real.exp (z * u / w)
      = ∫ u in (-l)..l, wker w u * Real.exp (-(z * u / w)) := by
    have h := intervalIntegral.integral_comp_neg (a := -l) (b := l)
      (f := fun u => wker w u * Real.exp (z * u / w))
    simp only [neg_neg] at h
    rw [← h]
    congr 1
    funext u
    simp only [wker, neg_sq, mul_neg, neg_div]
  have h2 : ∫ u in (-l)..l, wker w u * Real.cosh (z * u / w)
      = ∫ u in (-l)..l, (wker w u * Real.exp (z * u / w)
          + wker w u * Real.exp (-(z * u / w))) / 2 := by
    congr 1
    funext u
    rw [Real.cosh_eq]
    ring
  have hi1 := (continuous_wker_mul w z).intervalIntegrable (μ := volume) (-l) l
  have hcont2 : Continuous fun u => wker w u * Real.exp (-(z * u / w)) := by
    unfold wker
    fun_prop
  have hi2 := hcont2.intervalIntegrable (μ := volume) (-l) l
  rw [h2, intervalIntegral.integral_div, intervalIntegral.integral_add hi1 hi2, ← h1]
  ring

/-- `F` is even. -/
lemma F_neg (w l z : ℝ) : F w l (-z) = F w l z := by
  rw [F_eq_cosh, F_eq_cosh]
  congr 1
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [neg_mul, neg_div, Real.cosh_neg]

/-- `F` is strictly increasing in `|z|`. -/
lemma F_lt_F {w l : ℝ} (hw : 0 < w) (hl : 0 < l) {z₁ z₂ : ℝ} (h : |z₁| < |z₂|) :
    F w l z₁ < F w l z₂ := by
  rw [F_eq_cosh, F_eq_cosh]
  refine mul_lt_mul_of_pos_left ?_ (by positivity)
  refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by linarith) (continuous_wker_cosh w z₁).continuousOn
    (continuous_wker_cosh w z₂).continuousOn (fun u _ => ?_)
    ⟨l, Set.right_mem_Icc.mpr (by linarith), ?_⟩
  · refine mul_le_mul_of_nonneg_left ?_ (wker_pos _ _).le
    rw [Real.cosh_le_cosh, abs_div, abs_div, abs_mul, abs_mul]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h.le (abs_nonneg _))
      (abs_nonneg _)
  · refine mul_lt_mul_of_pos_left ?_ (wker_pos _ _)
    rw [Real.cosh_lt_cosh, abs_div, abs_div, abs_mul, abs_mul, abs_of_pos hl, abs_of_pos hw]
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right h hl) hw

/-- `F z₁ ≤ F z₂ ↔ |z₁| ≤ |z₂|`. -/
lemma F_le_iff {w l : ℝ} (hw : 0 < w) (hl : 0 < l) (z₁ z₂ : ℝ) :
    F w l z₁ ≤ F w l z₂ ↔ |z₁| ≤ |z₂| := by
  constructor
  · intro hF
    by_contra hcon
    rw [not_le] at hcon
    exact absurd hF (not_le.mpr (F_lt_F hw hl hcon))
  · intro hz
    rcases hz.lt_or_eq with hlt | heq
    · exact (F_lt_F hw hl hlt).le
    · rcases abs_eq_abs.mp heq with rfl | rfl
      · exact le_rfl
      · rw [F_neg]

/-- The e-value is `F v l (y − μ₀)`. -/
lemma E_eq_F {σ : ℝ} (hσ : 0 < σ) (μ₀ : ℝ) {l : ℝ} (hl : 0 < l) {n : ℕ} (hn : 1 ≤ n) (y : ℝ) :
    E σ μ₀ l n y = F (v σ n) l (y - μ₀) := by
  unfold E
  rw [g1_eq_g0_mul_F hσ μ₀ hl hn, mul_div_cancel_left₀ _ (g0_pos hσ μ₀ hn y).ne']

/-- The rejection region of the e-value is a two-sided tail in `|y − μ₀|`. -/
lemma E_ge_iff {σ : ℝ} (hσ : 0 < σ) (μ₀ : ℝ) {l : ℝ} (hl : 0 < l) {n : ℕ} (hn : 1 ≤ n)
    (y₀ y : ℝ) : E σ μ₀ l n y₀ ≤ E σ μ₀ l n y ↔ |y₀ - μ₀| ≤ |y - μ₀| := by
  rw [E_eq_F hσ μ₀ hl hn, E_eq_F hσ μ₀ hl hn]
  exact F_le_iff (coe_v_pos hσ hn) hl _ _

/-- Symmetry of the standard normal distribution function: `Φ(−s) = 1 − Φ(s)`. -/
lemma cdf_gaussianReal_neg (s : ℝ) :
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

/-- `Φ(0) = 1/2`. -/
lemma cdf_gaussianReal_zero : cdf (gaussianReal 0 1) 0 = 1 / 2 := by
  have h := cdf_gaussianReal_neg 0
  rw [neg_zero] at h
  linarith

/-- The two-sided null tail: `P_{H₀}(|Ȳ − μ₀| ≥ r) = 2(1 − Φ(r/√v))` for `r ≥ 0`. -/
lemma gaussianReal_abs_ge {μ₀ : ℝ} {w : ℝ≥0} (hw : w ≠ 0) {r : ℝ} (hr : 0 ≤ r) :
    ((gaussianReal μ₀ w) {y | r ≤ |y - μ₀|}).toReal
      = 2 * (1 - cdf (gaussianReal 0 1) (r / Real.sqrt w)) := by
  have hw' : 0 < (w : ℝ) := lt_of_le_of_ne w.coe_nonneg (fun h => hw (NNReal.coe_eq_zero.mp h.symm))
  have hsw : 0 < Real.sqrt (w : ℝ) := Real.sqrt_pos.mpr hw'
  -- standardisation `y ↦ (y − μ₀)/√w` sends `gaussianReal μ₀ w` to `gaussianReal 0 1`
  have hstd : (gaussianReal μ₀ w).map (fun y => (y - μ₀) / Real.sqrt w) = gaussianReal 0 1 := by
    have h1 : (fun y : ℝ => (y - μ₀) / Real.sqrt w) = (· / Real.sqrt w) ∘ (· - μ₀) := rfl
    rw [h1, ← Measure.map_map (measurable_div_const _) (measurable_sub_const μ₀),
      gaussianReal_map_sub_const, gaussianReal_map_div_const, sub_self, zero_div]
    congr 1
    apply NNReal.coe_injective
    simp only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_mk, Real.sq_sqrt w.coe_nonneg]
    exact div_self hw'.ne'
  have hset : {y : ℝ | r ≤ |y - μ₀|}
      = (fun y => (y - μ₀) / Real.sqrt w) ⁻¹' {t : ℝ | r / Real.sqrt w ≤ |t|} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_preimage, abs_div, abs_of_pos hsw]
    exact (div_le_div_iff_of_pos_right hsw).symm
  have hmeasT : Measurable fun y : ℝ => (y - μ₀) / Real.sqrt w := by fun_prop
  have hmeasS : MeasurableSet {t : ℝ | r / Real.sqrt w ≤ |t|} :=
    measurableSet_le measurable_const measurable_abs
  rw [hset, ← Measure.map_apply hmeasT hmeasS, hstd]
  set s : ℝ := r / Real.sqrt w with hs_def
  have hs : 0 ≤ s := div_nonneg hr hsw.le
  rcases hs.eq_or_lt with hs0 | hspos
  · rw [← hs0]
    have huniv : {t : ℝ | (0 : ℝ) ≤ |t|} = Set.univ := Set.eq_univ_of_forall fun t => abs_nonneg t
    rw [huniv, measure_univ, ENNReal.toReal_one, cdf_gaussianReal_zero]
    norm_num
  · have h1 : gaussianReal 0 1 {t : ℝ | s ≤ |t|} = gaussianTail.tail s :=
      gaussianTail.measure_le_abs_eq_tail hspos
    rw [h1]
    have h2 : (gaussianTail.tail s).toReal = gaussTailProb s := rfl
    rw [h2, gaussTailProb_eq_cdf hs, cdf_gaussianReal_neg]
    ring

/-- **Calibration:** the e-value's own p-value `S₀(E(y))` is the average p-value `P(y)`. -/
theorem pval_eq_survival {σ : ℝ} (hσ : 0 < σ) (μ₀ : ℝ) {l : ℝ} (hl : 0 < l) {n : ℕ} (hn : 1 ≤ n)
    (y : ℝ) : pval σ μ₀ n y = S₀ σ μ₀ l n (E σ μ₀ l n y) := by
  unfold S₀
  have hset : {y' : ℝ | E σ μ₀ l n y ≤ E σ μ₀ l n y'} = {y' : ℝ | |y - μ₀| ≤ |y' - μ₀|} := by
    ext y'
    simp only [Set.mem_setOf_eq]
    exact E_ge_iff hσ μ₀ hl hn y y'
  rw [hset, gaussianReal_abs_ge (v_ne_zero hσ hn) (abs_nonneg _)]
  unfold pval
  congr 3
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [coe_v, show σ ^ 2 / (n : ℝ) = σ ^ 2 / n by rfl, Real.sqrt_div' _ hn'.le,
    Real.sqrt_sq hσ.le]
  field_simp

end Calibration

end Lindley
