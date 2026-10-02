/-
Copyright (c) 2026 Patrick Rubin-Delanchy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Rubin-Delanchy, Andrew Jones
AI-generated (see the top-level README); not audited by the authors.
-/
import Mathlib
import Ols.EValueAlgebra
import Ols.BoundedError

/-!
# The protocol as a Lean type

A scientist posts a design `X`, a contrast `a` and a null value `v` (`Posting`) together with an
assumption class `𝒜` (a predicate on models `(P, y)`). An AI submits a `Bet`: an e-variable of
the data vector together with a proof that it is valid under every law in the class satisfying
`H₀ : aᵀβ⋆ = v`. `Bet.guarantee` is the protocol's promise, proved once: for every such law and
every `c > 0`, the payout exceeds `c` with probability at most `1/c`.

`twoPointBet` and `gridBet` instantiate the bounded-error class of the paper's Section 5 with
the exact two-point e-variables of `Ols/BoundedError.lean` and their `±λ` grid average.

See `PROTOCOL.md`, Milestone E.
-/

open MeasureTheory ProbabilityTheory Matrix BoundedError

namespace Protocol

variable {Ω : Type*} [MeasurableSpace Ω] {n p : ℕ}

/-! ### The posting, the class, the bet -/

/-- The scientist's posting: design, contrast, null value. -/
structure Posting (n p : ℕ) where
  X : Matrix (Fin n) (Fin p) ℝ
  hX : IsUnit (Xᵀ * X).det
  a : Fin p → ℝ
  v : ℝ

/-- An assumption class: a predicate on models `(P, y)`. The bookmaker may post any predicate. -/
abbrev AssumptionClass (Ω : Type*) [MeasurableSpace Ω] (n : ℕ) : Type _ :=
  Measure Ω → (Fin n → Ω → ℝ) → Prop

/-- The null hypothesis `H₀ : aᵀβ⋆ = v` for the model `(P, y)`. -/
def NullHolds (post : Posting n p) (P : Measure Ω) (y : Fin n → Ω → ℝ) : Prop :=
  post.a ⬝ᵥ olsEstimand P post.X y = post.v

/-- A bet against `H₀`: an e-variable of the data, valid under every law in the class that
satisfies `H₀`. The AI provides `e` and the proof `valid`. -/
structure Bet (post : Posting n p) (𝒜 : AssumptionClass Ω n) where
  e : (Fin n → ℝ) → ℝ
  nonneg : ∀ y, 0 ≤ e y
  measurable : Measurable e
  valid : ∀ (P : Measure Ω) (y : Fin n → Ω → ℝ), IsProbabilityMeasure P →
    (∀ i, Measurable (y i)) → 𝒜 P y → NullHolds post P y →
    EValue.IsEVariable P (fun ω => e (fun i => y i ω))

/-- **Guarantee of the protocol.** For every model in the class satisfying `H₀`, and every
`c > 0`, the payout exceeds `c` with probability at most `1/c`. -/
theorem Bet.guarantee {post : Posting n p} {𝒜 : AssumptionClass Ω n} (b : Bet post 𝒜)
    (P : Measure Ω) (y : Fin n → Ω → ℝ) [IsProbabilityMeasure P]
    (hy : ∀ i, Measurable (y i)) (hA : 𝒜 P y) (h0 : NullHolds post P y) {c : ℝ} (hc : 0 < c) :
    P.real {ω | c ≤ b.e (fun i => y i ω)} ≤ 1 / c :=
  EValue.IsEVariable.markov _ (b.valid P y inferInstance hy hA h0) hc

/-! ### The bounded-error class and the two-point bet -/

/-- Independent outcomes with declared error bound `Bᵢ` and standard-deviation bound `sᵢ`. -/
def boundedErrorClass (B s : Fin n → ℝ) : AssumptionClass Ω n := fun P y =>
  iIndepFun y P ∧ (∀ i ω, |y i ω - P[y i]| ≤ B i) ∧
    (∀ i, ∫ ω, (y i ω - P[y i]) ^ 2 ∂P ≤ (s i) ^ 2)

/-- `∑ᵢ γᵢ wᵢ = aᵀ β̂(w)` with `γ = olsWeights X a`. -/
lemma sum_olsWeights_mul (X : Matrix (Fin n) (Fin p) ℝ) (a : Fin p → ℝ) (w : Fin n → ℝ) :
    ∑ i, olsWeights X a i * w i = a ⬝ᵥ olsEstimator X w := by
  unfold olsEstimator
  rw [Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.mulVec_transpose,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_nonsing_inv,
    Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [olsWeights, dotProduct, Matrix.mulVec_mulVec]

/-- Under `H₀`, the weighted error sum is `aᵀβ̂(y) − v`. -/
lemma wsum_eq_sub_v (post : Posting n p) (P : Measure Ω) (y : Fin n → Ω → ℝ)
    (h0 : NullHolds post P y) (ω : Ω) :
    wsum (olsWeights post.X post.a) (centredErr P y) ω
      = post.a ⬝ᵥ olsEstimator post.X (fun i => y i ω) - post.v := by
  have h : wsum (olsWeights post.X post.a) (centredErr P y) ω
      = ∑ i, olsWeights post.X post.a i * y i ω
        - ∑ i, olsWeights post.X post.a i * meanVec y P i := by
    simp only [wsum, centredErr, mul_sub, Finset.sum_sub_distrib]
    rfl
  rw [h, sum_olsWeights_mul, sum_olsWeights_mul, ← h0]
  rfl

lemma olsWeights_neg (X : Matrix (Fin n) (Fin p) ℝ) (a : Fin p → ℝ) :
    olsWeights X (-a) = -olsWeights X a := by
  funext i
  simp [olsWeights, Matrix.mulVec_neg]

/-- The contrast map `w ↦ aᵀβ̂(w)` is measurable. -/
lemma measurable_contrast (X : Matrix (Fin n) (Fin p) ℝ) (a : Fin p → ℝ) :
    Measurable fun w : Fin n → ℝ => a ⬝ᵥ olsEstimator X w := by
  have h : (fun w : Fin n → ℝ => a ⬝ᵥ olsEstimator X w)
      = fun w => ∑ i, olsWeights X a i * w i := funext fun w => (sum_olsWeights_mul X a w).symm
  rw [h]
  exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).const_mul _

/-- The two-point normalising constant `∏ᵢ G(λ, (γᵢsᵢ)², |γᵢ|Bᵢ)`. -/
noncomputable def twoPointDen (post : Posting n p) (B s : Fin n → ℝ) (lam : ℝ) : ℝ :=
  ∏ i, twoPointMgfBound lam ((olsWeights post.X post.a i * s i) ^ 2)
    (|olsWeights post.X post.a i| * B i)

lemma twoPointDen_pos (post : Posting n p) (B s : Fin n → ℝ) (lam : ℝ)
    (hb : ∀ i, 0 < |olsWeights post.X post.a i| * B i) : 0 < twoPointDen post B s lam :=
  Finset.prod_pos fun i _ => twoPointMgfBound_pos (hb i) (sq_nonneg _)

/-- The two-point bet at a fixed `λ ≥ 0`:
`e(w) = exp(λ(aᵀβ̂(w) − v)) / ∏ᵢ G(λ, (γᵢsᵢ)², |γᵢ|Bᵢ)`. -/
noncomputable def twoPointBet (post : Posting n p) (B s : Fin n → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (hb : ∀ i, 0 < |olsWeights post.X post.a i| * B i) :
    Bet post (boundedErrorClass (Ω := Ω) B s) where
  e := fun w => Real.exp (lam * (post.a ⬝ᵥ olsEstimator post.X w - post.v))
    / twoPointDen post B s lam
  nonneg _ := div_nonneg (Real.exp_pos _).le (twoPointDen_pos post B s lam hb).le
  measurable :=
    (Real.measurable_exp.comp
      (measurable_const.mul ((measurable_contrast post.X post.a).sub measurable_const))).div_const _
  valid := by
    intro P y hP hy hA h0
    haveI := hP
    obtain ⟨hind, hbdd, hvar⟩ := hA
    obtain ⟨h1, h2, h3⟩ := centredErr_props_of_bounded hy hind hbdd
    have hfun : (fun ω => Real.exp (lam * (post.a ⬝ᵥ olsEstimator post.X (fun i => y i ω)
        - post.v)) / twoPointDen post B s lam)
        = fun ω => Real.exp (lam * wsum (olsWeights post.X post.a) (centredErr P y) ω)
          / twoPointDen post B s lam := by
      funext ω
      rw [wsum_eq_sub_v post P y h0 ω]
    rw [hfun]
    have hden := twoPointDen_pos post B s lam hb
    have hwbdd : ∀ ω, |wsum (olsWeights post.X post.a) (centredErr P y) ω|
        ≤ ∑ i, |olsWeights post.X post.a i| * B i := fun ω => by
      unfold wsum
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hbdd i ω) (abs_nonneg _)
    have hwmeas : Measurable (wsum (olsWeights post.X post.a) (centredErr P y)) := by
      unfold wsum
      exact Finset.measurable_sum _ fun i _ => (h1 i).const_mul _
    have hmeasE : Measurable fun ω =>
        Real.exp (lam * wsum (olsWeights post.X post.a) (centredErr P y) ω)
          / twoPointDen post B s lam :=
      (Real.measurable_exp.comp (hwmeas.const_mul lam)).div_const _
    refine ⟨fun ω => div_nonneg (Real.exp_pos _).le hden.le, ?_, ?_⟩
    · -- integrability from boundedness
      refine (memLp_top_of_bound hmeasE.aestronglyMeasurable
        (Real.exp (lam * ∑ i, |olsWeights post.X post.a i| * B i) / twoPointDen post B s lam)
        (ae_of_all _ fun ω => ?_)).integrable le_top
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.exp_pos _).le hden.le)]
      refine div_le_div_of_nonneg_right ?_ hden.le
      exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (hwbdd ω)) hlam)
    · exact two_point_evalue (olsWeights post.X post.a) B s (centredErr P y) h1 h2 h3 hbdd hvar
        hb hlam

/-- The mirrored posting `(X, −a, −v)`: the lower tail of the contrast. -/
def Posting.neg (post : Posting n p) : Posting n p := ⟨post.X, post.hX, -post.a, -post.v⟩

lemma NullHolds.neg {post : Posting n p} {P : Measure Ω} {y : Fin n → Ω → ℝ}
    (h0 : NullHolds post P y) : NullHolds post.neg P y := by
  unfold NullHolds at h0 ⊢
  simp only [Posting.neg, neg_dotProduct, h0]

lemma hb_neg {post : Posting n p} {B : Fin n → ℝ}
    (hb : ∀ i, 0 < |olsWeights post.X post.a i| * B i) :
    ∀ i, 0 < |olsWeights post.neg.X post.neg.a i| * B i := fun i => by
  simp only [Posting.neg, olsWeights_neg, Pi.neg_apply, abs_neg]
  exact hb i

/-- The paper's grid average of the `±λⱼ` two-point bets, with weights `1/(2k)`. -/
noncomputable def gridBet (post : Posting n p) (B s : Fin n → ℝ) {k : ℕ} (hk : 0 < k)
    (lam : Fin k → ℝ) (hlam : ∀ j, 0 ≤ lam j)
    (hb : ∀ i, 0 < |olsWeights post.X post.a i| * B i) :
    Bet post (boundedErrorClass (Ω := Ω) B s) where
  e := fun w => (∑ j, ((twoPointBet (Ω := Ω) post B s (lam j) (hlam j) hb).e w
      + (twoPointBet (Ω := Ω) post.neg B s (lam j) (hlam j) (hb_neg hb)).e w)) / (2 * k)
  nonneg w := by
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    refine div_nonneg (Finset.sum_nonneg fun j _ => add_nonneg ?_ ?_) (by positivity)
    · exact (twoPointBet (Ω := Ω) post B s (lam j) (hlam j) hb).nonneg w
    · exact (twoPointBet (Ω := Ω) post.neg B s (lam j) (hlam j) (hb_neg hb)).nonneg w
  measurable := by
    have h : ∀ j : Fin k, Measurable fun w : Fin n → ℝ =>
        (twoPointBet (Ω := Ω) post B s (lam j) (hlam j) hb).e w
          + (twoPointBet (Ω := Ω) post.neg B s (lam j) (hlam j) (hb_neg hb)).e w := fun j =>
      ((twoPointBet (Ω := Ω) post B s (lam j) (hlam j) hb).measurable).add
        (twoPointBet (Ω := Ω) post.neg B s (lam j) (hlam j) (hb_neg hb)).measurable
    exact (Finset.measurable_sum
      (f := fun j w => (twoPointBet (Ω := Ω) post B s (lam j) (hlam j) hb).e w
        + (twoPointBet (Ω := Ω) post.neg B s (lam j) (hlam j) (hb_neg hb)).e w) Finset.univ
      fun j _ => h j).div_const _
  valid := by
    intro P y hP hy hA h0
    haveI := hP
    have h := EValue.IsEVariable.average hk
      (fun j ω => ((twoPointBet (Ω := Ω) post B s (lam j) (hlam j) hb).e (fun i => y i ω)
        + (twoPointBet (Ω := Ω) post.neg B s (lam j) (hlam j) (hb_neg hb)).e (fun i => y i ω)) / 2)
      fun j => EValue.IsEVariable.half_add
        ((twoPointBet (Ω := Ω) post B s (lam j) (hlam j) hb).valid P y hP hy hA h0)
        ((twoPointBet (Ω := Ω) post.neg B s (lam j) (hlam j) (hb_neg hb)).valid P y hP hy hA h0.neg)
    convert h using 1
    funext ω
    rw [Finset.sum_div, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

/-! ### Sanity checks -/

/-- At `λ = 0` the two-point bet is the trivial bet `e ≡ 1`. -/
example (post : Posting n p) (B s : Fin n → ℝ)
    (hb : ∀ i, 0 < |olsWeights post.X post.a i| * B i) (w : Fin n → ℝ) :
    (twoPointBet (Ω := Ω) post B s 0 le_rfl hb).e w = 1 := by
  simp only [twoPointBet, twoPointDen, zero_mul, Real.exp_zero]
  rw [Finset.prod_eq_one fun i _ => twoPointMgfBound_zero (hb i) (sq_nonneg _), div_one]

/-- `Bet.guarantee` at `c = 20`: the payout exceeds `20` with probability at most `1/20`. -/
example {post : Posting n p} {𝒜 : AssumptionClass Ω n} (b : Bet post 𝒜)
    (P : Measure Ω) (y : Fin n → Ω → ℝ) [IsProbabilityMeasure P]
    (hy : ∀ i, Measurable (y i)) (hA : 𝒜 P y) (h0 : NullHolds post P y) :
    P.real {ω | 20 ≤ b.e (fun i => y i ω)} ≤ 1 / 20 :=
  b.guarantee P y hy hA h0 (by norm_num)

end Protocol
