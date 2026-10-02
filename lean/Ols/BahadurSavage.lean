/-
Copyright (c) 2026 Patrick Rubin-Delanchy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Rubin-Delanchy, Andrew Jones
-/
import Mathlib

/-!
# The Bahadur–Savage impossibility theorem (mean version)

Over the class of all probability distributions on `ℝ` with finite mean, no test of the
null hypothesis "the mean is zero" has power exceeding its size: any test that keeps its
rejection probability at most `α` under every mean-zero law also has rejection probability
at most `α` under *every* finite-mean law. This is the "first wall" of the certification
programme: with no assumptions beyond a finite mean, nothing about the mean is testable.

Reference: R. R. Bahadur and L. J. Savage, "The nonexistence of certain statistical
procedures in nonparametric problems", Ann. Math. Statist. 27 (1956) 1115–1122.

This file formalises the mean version over the class of *all* finite-mean laws, which is a
clean instance of their result. Tests are `ℝ≥0∞`-valued and integrals are lower Lebesgue
integrals `∫⁻`, which removes Bochner-integrability side conditions from the main argument;
the mean condition is the only place a signed integral appears.

The argument: contaminate `P` with a point mass, `mix p P a = (1-p)·P + p·δ_a`, choosing `a`
so that the mixture has mean zero. The size constraint applies to the mixture, which dominates
`(1-p)·P`; letting `p → 0⁺` gives the bound at `P`. For `n` observations the product of the
mixtures dominates `(1-p)ⁿ` times the product of `P` (proved by induction via Tonelli).

See `BAHADUR_SAVAGE.md` for the full proof plan and the working protocol.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BahadurSavage

/-- The contamination mixture `(1-p)·P + p·δ_a`, the device that drags the mean of `P` to a
target while staying arbitrarily close to `P` as `p → 0`. -/
noncomputable def mix (p : ℝ) (P : Measure ℝ) (a : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (1 - p)) • P + (ENNReal.ofReal p) • Measure.dirac a

/-- The contamination point that sends the mixture's mean to zero. -/
noncomputable def contamPoint (p : ℝ) (P : Measure ℝ) : ℝ :=
  -(1 - p) * (∫ x, x ∂P) / p

section OneObservation

variable {p : ℝ} {P : Measure ℝ}

/-- The mixture is a probability measure when `0 < p < 1`. -/
instance mix_isProbabilityMeasure (hp0 : 0 < p) (hp1 : p < 1) (P : Measure ℝ)
    [IsProbabilityMeasure P] (a : ℝ) : IsProbabilityMeasure (mix p P a) := by
  constructor
  rw [mix, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ, measure_univ,
    smul_eq_mul, smul_eq_mul, mul_one, mul_one, ← ENNReal.ofReal_add (by linarith) hp0.le]
  simp

/-- The mixture is a finite measure for every real `p` (no sign condition needed). -/
lemma mix_isFiniteMeasure (p : ℝ) (P : Measure ℝ) [IsFiniteMeasure P] (a : ℝ) :
    IsFiniteMeasure (mix p P a) := by
  constructor
  rw [mix, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _),
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩

set_option linter.unusedVariables false in
/-- `id` is integrable with respect to the mixture. -/
lemma integrable_id_mix (hp0 : 0 < p) (hp1 : p < 1) [IsProbabilityMeasure P]
    (hP : Integrable id P) (a : ℝ) : Integrable id (mix p P a) := by
  unfold mix
  refine Integrable.add_measure (hP.smul_measure ENNReal.ofReal_ne_top) ?_
  exact (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top

/-- The mean of the mixture. -/
lemma integral_id_mix (hp0 : 0 < p) (hp1 : p < 1) [IsProbabilityMeasure P]
    (hP : Integrable id P) (a : ℝ) :
    (∫ x, x ∂(mix p P a)) = (1 - p) * (∫ x, x ∂P) + p * a := by
  have h1 : Integrable id ((ENNReal.ofReal (1 - p)) • P) := hP.smul_measure ENNReal.ofReal_ne_top
  have h2 : Integrable id ((ENNReal.ofReal p) • Measure.dirac a) :=
    (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
  change ∫ x, id x ∂(mix p P a) = _
  rw [mix, integral_add_measure h1 h2, integral_smul_measure, integral_smul_measure,
    integral_dirac, ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal hp0.le,
    smul_eq_mul, smul_eq_mul]
  rfl

/-- With the contamination point, the mixture has mean zero. -/
lemma integral_id_mix_contam (hp0 : 0 < p) (hp1 : p < 1) [IsProbabilityMeasure P]
    (hP : Integrable id P) :
    (∫ x, x ∂(mix p P (contamPoint p P))) = 0 := by
  rw [integral_id_mix hp0 hp1 hP, contamPoint]
  field_simp
  ring

/-- The mixture dominates `(1-p)` times `P`, as measures. -/
lemma smul_le_mix (a : ℝ) : (ENNReal.ofReal (1 - p)) • P ≤ mix p P a :=
  Measure.le_add_right le_rfl

/-- The scaled-integral bound at a fixed contamination level `p ∈ (0, 1)`. -/
private lemma scaled_lintegral_le
    {α : ℝ≥0∞} {φ : ℝ → ℝ≥0∞}
    (hsize : ∀ Q : Measure ℝ, IsProbabilityMeasure Q → Integrable id Q →
        (∫ x, x ∂Q) = 0 → (∫⁻ x, φ x ∂Q) ≤ α)
    [IsProbabilityMeasure P] (hP : Integrable id P) (hp0 : 0 < p) (hp1 : p < 1) :
    ENNReal.ofReal (1 - p) * (∫⁻ x, φ x ∂P) ≤ α := by
  have hQ := hsize (mix p P (contamPoint p P)) (mix_isProbabilityMeasure hp0 hp1 P _)
    (integrable_id_mix hp0 hp1 hP _) (integral_id_mix_contam hp0 hp1 hP)
  calc ENNReal.ofReal (1 - p) * (∫⁻ x, φ x ∂P)
      = ∫⁻ x, φ x ∂((ENNReal.ofReal (1 - p)) • P) := by rw [lintegral_smul_measure, smul_eq_mul]
    _ ≤ ∫⁻ x, φ x ∂(mix p P (contamPoint p P)) := lintegral_mono' (smul_le_mix _) le_rfl
    _ ≤ α := hQ

/-- `ENNReal.ofReal (1 - p) → 1` as `p → 0⁺`. -/
private lemma tendsto_ofReal_one_sub :
    Tendsto (fun p : ℝ => ENNReal.ofReal (1 - p)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have h : Tendsto (fun p : ℝ => 1 - p) (𝓝[>] (0 : ℝ)) (𝓝 (1 - 0)) :=
    (tendsto_const_nhds.sub tendsto_id).mono_left nhdsWithin_le_nhds
  simpa using ENNReal.tendsto_ofReal h

/-- Passing to the limit `p → 0⁺` in `c(p) * X ≤ α` with `c(p) → 1` gives `X ≤ α`. -/
private lemma le_of_scaled_le {α X : ℝ≥0∞} {c : ℝ → ℝ≥0∞}
    (hc : Tendsto c (𝓝[>] (0 : ℝ)) (𝓝 1))
    (h : ∀ p : ℝ, 0 < p → p < 1 → c p * X ≤ α) : X ≤ α := by
  have hlim : Tendsto (fun p => c p * X) (𝓝[>] (0 : ℝ)) (𝓝 X) := by
    simpa using ENNReal.Tendsto.mul_const hc (Or.inl one_ne_zero)
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with p hp
  exact h p hp.1 hp.2

set_option linter.unusedVariables false in
/-- **Bahadur–Savage, single observation.** Any test with size at most `α` over the mean-zero
finite-mean laws has power at most `α` at every finite-mean law: the data are useless. -/
theorem bahadurSavage_one
    {α : ℝ≥0∞} {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) (hφ1 : ∀ x, φ x ≤ 1)
    (hsize : ∀ Q : Measure ℝ, IsProbabilityMeasure Q → Integrable id Q →
        (∫ x, x ∂Q) = 0 → (∫⁻ x, φ x ∂Q) ≤ α)
    (P : Measure ℝ) [IsProbabilityMeasure P] (hP : Integrable id P) :
    (∫⁻ x, φ x ∂P) ≤ α :=
  le_of_scaled_le tendsto_ofReal_one_sub fun p hp0 hp1 => scaled_lintegral_le hsize hP hp0 hp1

end OneObservation

section ManyObservations

/-- The iid product law of `n` observations from `P`. -/
noncomputable def prodLaw (n : ℕ) (P : Measure ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => P)

instance prodLaw_sigmaFinite (n : ℕ) (P : Measure ℝ) [SigmaFinite P] :
    SigmaFinite (prodLaw n P) := by
  unfold prodLaw
  infer_instance

/-- Product domination, integral form: for every measurable `f`,
`(1-p)ⁿ ∫⁻ f ∂Pⁿ ≤ ∫⁻ f ∂(mix)ⁿ`. Induction on `n`, splitting off the first coordinate with
`measurePreserving_piFinSuccAbove` and applying Tonelli. -/
private lemma pow_mul_lintegral_le (p : ℝ) (P : Measure ℝ) [IsProbabilityMeasure P] (a : ℝ) :
    ∀ n : ℕ, ∀ f : (Fin n → ℝ) → ℝ≥0∞, Measurable f →
      (ENNReal.ofReal (1 - p)) ^ n * (∫⁻ x, f x ∂(prodLaw n P))
        ≤ ∫⁻ x, f x ∂(prodLaw n (mix p P a)) := by
  haveI : IsFiniteMeasure (mix p P a) := mix_isFiniteMeasure p P a
  haveI : SigmaFinite (mix p P a) := inferInstance
  intro n
  induction n with
  | zero =>
    intro f hf
    simp only [prodLaw, pow_zero, one_mul]
    rw [Measure.pi_of_empty (fun _ => P), Measure.pi_of_empty (fun _ => mix p P a)]
  | succ n ih =>
    intro f hf
    set c : ℝ≥0∞ := ENNReal.ofReal (1 - p) with hc_def
    have hP := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => P) 0
    have hM := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => mix p P a) 0
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0 with he_def
    -- transfer both integrals to the binary product
    have hg : Measurable (f ∘ e.symm) := hf.comp e.symm.measurable
    have h1 : ∫⁻ x, f x ∂(prodLaw (n + 1) P)
        = ∫⁻ z, (f ∘ e.symm) z ∂(P.prod (prodLaw n P)) := by
      simp only [prodLaw]
      rw [← hP.lintegral_comp hg]
      congr 1
      funext x
      simp
    have h2 : ∫⁻ x, f x ∂(prodLaw (n + 1) (mix p P a))
        = ∫⁻ z, (f ∘ e.symm) z ∂((mix p P a).prod (prodLaw n (mix p P a))) := by
      simp only [prodLaw]
      rw [← hM.lintegral_comp hg]
      congr 1
      funext x
      simp
    rw [h1, h2, lintegral_prod _ hg.aemeasurable, lintegral_prod _ hg.aemeasurable]
    have hinner : Measurable fun x => ∫⁻ y, (f ∘ e.symm) (x, y) ∂(prodLaw n P) :=
      hg.lintegral_prod_right'
    calc c ^ (n + 1) * ∫⁻ x, ∫⁻ y, (f ∘ e.symm) (x, y) ∂(prodLaw n P) ∂P
        = c * ∫⁻ x, c ^ n * ∫⁻ y, (f ∘ e.symm) (x, y) ∂(prodLaw n P) ∂P := by
          rw [lintegral_const_mul _ hinner]
          ring
      _ ≤ c * ∫⁻ x, ∫⁻ y, (f ∘ e.symm) (x, y) ∂(prodLaw n (mix p P a)) ∂P := by
          gcongr with x
          exact ih (fun y => (f ∘ e.symm) (x, y)) (hg.comp measurable_prodMk_left)
      _ = ∫⁻ x, ∫⁻ y, (f ∘ e.symm) (x, y) ∂(prodLaw n (mix p P a)) ∂(c • P) := by
          rw [lintegral_smul_measure, smul_eq_mul]
      _ ≤ ∫⁻ x, ∫⁻ y, (f ∘ e.symm) (x, y) ∂(prodLaw n (mix p P a)) ∂(mix p P a) :=
          lintegral_mono' (smul_le_mix a) le_rfl

/-- Product domination: the product of the mixtures dominates `(1-p)ⁿ` times the product of
`P`. This is the only lemma the n-observation case adds to the single-observation one. -/
lemma smul_pow_le_prod_mix (n : ℕ) {p : ℝ} {P : Measure ℝ} [IsProbabilityMeasure P] (a : ℝ) :
    (ENNReal.ofReal (1 - p)) ^ n • prodLaw n P ≤ prodLaw n (mix p P a) := by
  rw [Measure.le_iff]
  intro s hs
  rw [Measure.smul_apply, smul_eq_mul, ← lintegral_indicator_one hs, ← lintegral_indicator_one hs]
  exact pow_mul_lintegral_le p P a n _ (measurable_const.indicator hs)

/-- `(ENNReal.ofReal (1 - p))ⁿ → 1` as `p → 0⁺`. -/
private lemma tendsto_ofReal_one_sub_pow (n : ℕ) :
    Tendsto (fun p : ℝ => (ENNReal.ofReal (1 - p)) ^ n) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have h := ((ENNReal.continuous_pow n).tendsto 1).comp tendsto_ofReal_one_sub
  simpa [Function.comp_def] using h

set_option linter.unusedVariables false in
/-- **Bahadur–Savage, `n` observations.** The impossibility for a test based on `n` iid
observations. -/
theorem bahadurSavage_pi
    {n : ℕ} {α : ℝ≥0∞} {φ : (Fin n → ℝ) → ℝ≥0∞} (hφ : Measurable φ) (hφ1 : ∀ x, φ x ≤ 1)
    (hsize : ∀ Q : Measure ℝ, IsProbabilityMeasure Q → Integrable id Q →
        (∫ x, x ∂Q) = 0 → (∫⁻ x, φ x ∂(prodLaw n Q)) ≤ α)
    (P : Measure ℝ) [IsProbabilityMeasure P] (hP : Integrable id P) :
    (∫⁻ x, φ x ∂(prodLaw n P)) ≤ α := by
  refine le_of_scaled_le (tendsto_ofReal_one_sub_pow n) fun p hp0 hp1 => ?_
  have hQ := hsize (mix p P (contamPoint p P)) (mix_isProbabilityMeasure hp0 hp1 P _)
    (integrable_id_mix hp0 hp1 hP _) (integral_id_mix_contam hp0 hp1 hP)
  exact le_trans (pow_mul_lintegral_le p P (contamPoint p P) n φ hφ) hQ

/-- **Bahadur–Savage, `n` observations, unbounded test.** The hypothesis `φ ≤ 1` of
`bahadurSavage_pi` is not needed: the same argument bounds the expectation of any
nonnegative statistic. -/
theorem bahadurSavage_pi_unbounded
    {n : ℕ} {α : ℝ≥0∞} {φ : (Fin n → ℝ) → ℝ≥0∞} (hφ : Measurable φ)
    (hsize : ∀ Q : Measure ℝ, IsProbabilityMeasure Q → Integrable id Q →
        (∫ x, x ∂Q) = 0 → (∫⁻ x, φ x ∂(prodLaw n Q)) ≤ α)
    (P : Measure ℝ) [IsProbabilityMeasure P] (hP : Integrable id P) :
    (∫⁻ x, φ x ∂(prodLaw n P)) ≤ α := by
  refine le_of_scaled_le (tendsto_ofReal_one_sub_pow n) fun p hp0 hp1 => ?_
  have hQ := hsize (mix p P (contamPoint p P)) (mix_isProbabilityMeasure hp0 hp1 P _)
    (integrable_id_mix hp0 hp1 hP _) (integral_id_mix_contam hp0 hp1 hP)
  exact le_trans (pow_mul_lintegral_le p P (contamPoint p P) n φ hφ) hQ

end ManyObservations

end BahadurSavage

namespace BahadurSavage

section PValueForm

/-- The rejection event of a p-value at level `α`, as an `ℝ≥0∞`-valued indicator test. -/
private lemma lintegral_indicator_reject {n : ℕ} {α : ℝ} {P : (Fin n → ℝ) → ℝ}
    (hP : Measurable P) (μ : Measure (Fin n → ℝ)) :
    ∫⁻ y, Set.indicator {y | P y ≤ α} (fun _ => (1 : ℝ≥0∞)) y ∂μ = μ {y | P y ≤ α} :=
  lintegral_indicator_one (measurableSet_le hP measurable_const)

set_option linter.unusedVariables false in
/-- **Bahadur–Savage, p-value form.** A valid p-value for `H₀ : mean = 0` over the
finite-mean class has power at most `α` at every finite-mean law. -/
theorem bahadurSavage_pvalue_pi {n : ℕ} {α : ℝ} (hα : 0 ≤ α)
    (P : (Fin n → ℝ) → ℝ) (hP : Measurable P)
    (hvalid : ∀ Q : Measure ℝ, IsProbabilityMeasure Q → Integrable id Q →
        (∫ x, x ∂Q) = 0 →
        prodLaw n Q {y | P y ≤ α} ≤ ENNReal.ofReal α)
    (Q : Measure ℝ) [IsProbabilityMeasure Q] (hQ : Integrable id Q) :
    prodLaw n Q {y | P y ≤ α} ≤ ENNReal.ofReal α := by
  have hmeas : MeasurableSet {y : Fin n → ℝ | P y ≤ α} := measurableSet_le hP measurable_const
  have hφ : Measurable (Set.indicator {y : Fin n → ℝ | P y ≤ α} (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hmeas
  have hφ1 : ∀ y, Set.indicator {y : Fin n → ℝ | P y ≤ α} (fun _ => (1 : ℝ≥0∞)) y ≤ 1 :=
    fun y => Set.indicator_le_self' (fun _ _ => zero_le_one) y
  have h := bahadurSavage_pi hφ hφ1 (fun R hR hint hmean => by
    rw [lintegral_indicator_reject hP]
    exact hvalid R hR hint hmean) Q hQ
  rwa [lintegral_indicator_reject hP] at h

/-- The coordinatewise shift `y ↦ y + μ₀` on `Fin n → ℝ`. -/
private def shiftFun (n : ℕ) (μ₀ : ℝ) : (Fin n → ℝ) → (Fin n → ℝ) := fun y i => y i + μ₀

private lemma measurable_shiftFun (n : ℕ) (μ₀ : ℝ) : Measurable (shiftFun n μ₀) := by
  unfold shiftFun
  fun_prop

/-- The product of shifted laws is the shifted product law. -/
private lemma prodLaw_map_add (n : ℕ) (μ₀ : ℝ) (R : Measure ℝ) [IsProbabilityMeasure R] :
    prodLaw n (R.map (· + μ₀)) = (prodLaw n R).map (shiftFun n μ₀) := by
  have hmp : ∀ _ : Fin n, MeasurePreserving (· + μ₀) R (R.map (· + μ₀)) := fun _ =>
    ⟨measurable_add_const μ₀, rfl⟩
  exact (measurePreserving_pi (fun _ => R) (fun _ => R.map (· + μ₀)) hmp).map_eq.symm

set_option linter.unusedVariables false in
/-- **Bahadur–Savage, p-value form, general null value `μ₀`.** -/
theorem bahadurSavage_pvalue_pi' {n : ℕ} {α : ℝ} (hα : 0 ≤ α) (μ₀ : ℝ)
    (P : (Fin n → ℝ) → ℝ) (hP : Measurable P)
    (hvalid : ∀ Q : Measure ℝ, IsProbabilityMeasure Q → Integrable id Q →
        (∫ x, x ∂Q) = μ₀ →
        prodLaw n Q {y | P y ≤ α} ≤ ENNReal.ofReal α)
    (Q : Measure ℝ) [IsProbabilityMeasure Q] (hQ : Integrable id Q) :
    prodLaw n Q {y | P y ≤ α} ≤ ENNReal.ofReal α := by
  have hmeasS : MeasurableSet {y : Fin n → ℝ | P y ≤ α} := measurableSet_le hP measurable_const
  -- the centred test and the centred law
  set P' : (Fin n → ℝ) → ℝ := fun y => P (shiftFun n μ₀ y) with hP'_def
  have hP' : Measurable P' := hP.comp (measurable_shiftFun n μ₀)
  have hpre : ∀ R : Measure ℝ, IsProbabilityMeasure R →
      prodLaw n (R.map (· + μ₀)) {y | P y ≤ α} = prodLaw n R {y | P' y ≤ α} := by
    intro R _
    rw [prodLaw_map_add, Measure.map_apply (measurable_shiftFun n μ₀) hmeasS]
    rfl
  set Q' : Measure ℝ := Q.map (· - μ₀) with hQ'_def
  haveI : IsProbabilityMeasure Q' :=
    Q.isProbabilityMeasure_map (measurable_sub_const μ₀).aemeasurable
  have hQ' : Integrable id Q' := by
    rw [hQ'_def, integrable_map_measure aestronglyMeasurable_id
      (measurable_sub_const μ₀).aemeasurable]
    exact (hQ.sub (integrable_const μ₀))
  have hQback : Q'.map (· + μ₀) = Q := by
    rw [hQ'_def, Measure.map_map (measurable_add_const μ₀) (measurable_sub_const μ₀)]
    have : ((· + μ₀) ∘ (· - μ₀) : ℝ → ℝ) = id := by
      funext x
      simp
    rw [this, Measure.map_id]
  have hvalid' : ∀ R : Measure ℝ, IsProbabilityMeasure R → Integrable id R →
      integral R (fun x : ℝ => x) = 0 → prodLaw n R {y | P' y ≤ α} ≤ ENNReal.ofReal α := by
    intro R hR hint hmean
    rw [← hpre R hR]
    haveI : IsProbabilityMeasure (R.map (· + μ₀)) :=
      R.isProbabilityMeasure_map (measurable_add_const μ₀).aemeasurable
    refine hvalid _ inferInstance ?_ ?_
    · rw [integrable_map_measure aestronglyMeasurable_id (measurable_add_const μ₀).aemeasurable]
      exact hint.add (integrable_const μ₀)
    · have hI : Integrable (fun x : ℝ => x) R := hint
      have hshift : integral R (fun x : ℝ => x + μ₀) = μ₀ := by
        rw [integral_add hI (integrable_const μ₀), integral_const]
        simp [hmean]
      rw [integral_map (f := fun x : ℝ => x) (measurable_add_const μ₀).aemeasurable
        aestronglyMeasurable_id]
      exact hshift
  have h := bahadurSavage_pvalue_pi hα P' hP' hvalid' Q' hQ'
  rwa [← hpre Q' inferInstance, hQback] at h

end PValueForm

section EValueForm

/-- **Bahadur–Savage, e-value form.** If `E` is an e-variable for `H₀ : mean = μ₀` under every
finite-mean null law, then its expectation is at most `1` under EVERY finite-mean law, whatever
its mean: no bet against `H₀` has positive expected return under any alternative. -/
theorem bahadurSavage_evalue_pi {n : ℕ} (μ₀ : ℝ) {E : (Fin n → ℝ) → ℝ≥0∞} (hE : Measurable E)
    (hvalid : ∀ Q : Measure ℝ, IsProbabilityMeasure Q → Integrable id Q →
        (∫ x, x ∂Q) = μ₀ → (∫⁻ y, E y ∂(prodLaw n Q)) ≤ 1)
    (P : Measure ℝ) [IsProbabilityMeasure P] (hP : Integrable id P) :
    (∫⁻ y, E y ∂(prodLaw n P)) ≤ 1 := by
  -- the centred statistic and the centred law
  set E' : (Fin n → ℝ) → ℝ≥0∞ := fun y => E (shiftFun n μ₀ y) with hE'_def
  have hE' : Measurable E' := hE.comp (measurable_shiftFun n μ₀)
  have hpre : ∀ R : Measure ℝ, IsProbabilityMeasure R →
      ∫⁻ y, E y ∂(prodLaw n (R.map (· + μ₀))) = ∫⁻ y, E' y ∂(prodLaw n R) := by
    intro R _
    rw [prodLaw_map_add, lintegral_map hE (measurable_shiftFun n μ₀)]
  set P' : Measure ℝ := P.map (· - μ₀) with hP'_def
  haveI : IsProbabilityMeasure P' :=
    P.isProbabilityMeasure_map (measurable_sub_const μ₀).aemeasurable
  have hP' : Integrable id P' := by
    rw [hP'_def, integrable_map_measure aestronglyMeasurable_id
      (measurable_sub_const μ₀).aemeasurable]
    exact (hP.sub (integrable_const μ₀))
  have hPback : P'.map (· + μ₀) = P := by
    rw [hP'_def, Measure.map_map (measurable_add_const μ₀) (measurable_sub_const μ₀)]
    have : ((· + μ₀) ∘ (· - μ₀) : ℝ → ℝ) = id := by
      funext x
      simp
    rw [this, Measure.map_id]
  have hvalid' : ∀ R : Measure ℝ, IsProbabilityMeasure R → Integrable id R →
      integral R (fun x : ℝ => x) = 0 → (∫⁻ y, E' y ∂(prodLaw n R)) ≤ 1 := by
    intro R hR hint hmean
    rw [← hpre R hR]
    haveI : IsProbabilityMeasure (R.map (· + μ₀)) :=
      R.isProbabilityMeasure_map (measurable_add_const μ₀).aemeasurable
    refine hvalid _ inferInstance ?_ ?_
    · rw [integrable_map_measure aestronglyMeasurable_id (measurable_add_const μ₀).aemeasurable]
      exact hint.add (integrable_const μ₀)
    · have hI : Integrable (fun x : ℝ => x) R := hint
      have hshift : integral R (fun x : ℝ => x + μ₀) = μ₀ := by
        rw [integral_add hI (integrable_const μ₀), integral_const]
        simp [hmean]
      rw [integral_map (f := fun x : ℝ => x) (measurable_add_const μ₀).aemeasurable
        aestronglyMeasurable_id]
      exact hshift
  have h := bahadurSavage_pi_unbounded hE' hvalid' P' hP'
  rwa [← hpre P' inferInstance, hPback] at h

end EValueForm

end BahadurSavage
