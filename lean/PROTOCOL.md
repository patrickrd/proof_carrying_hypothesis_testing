# Formalisation task: closing the gaps between the ICLR paper and the Lean project

**For the VS Code Claude Code agent.** Self-contained specification, same conventions as
`BOUNDED_ERROR.md`, `TWO_POINT.md`, `LINDLEY_EVALUE.md` and `PAPER_ALIGNMENT.md`. Work in this
repo (`~/linear-model-lean-quantitative`; home-folder clone; do NOT move it under `~/Documents`).
Read `CLAUDE.md` (autonomy contract: proceed without asking, commit locally after each lemma,
NEVER push, stage a `sorry` with a `-- TODO(protocol): …` note when stuck, no axioms /
`native_decide` / `admit`, verify headline results with `#print axioms`). Record progress in
`PROTOCOL_PROGRESS.md` (create it): one dated line per lemma with status and any deviation.

Do the milestones **in order**. A–C are small and independent; D is a self-contained piece of
measure theory; E depends on A and C; F is small; G is verification only. Each milestone is a
sensible commit. `import Mathlib` at the top of every new file, as the existing `Ols/*.lean` do.
Register every new file in `Ols.lean` and in the `globs` list of `lakefile.toml`. Do not change
any existing theorem statement (rule 6 of `CLAUDE.md`); where this spec says "expose" a private
lemma, add a new public theorem next to it rather than editing the private one.

## Why: what the paper now claims

`ICLR_submission/main_AI.tex` (23 Sep 2026) describes a protocol in which a scientist posts a
design `X`, a contrast `a`, a value `v`, a model for `Y₁,…,Yₙ` and an assumption class `𝒜`; an AI
returns an e-variable `e : ℝⁿ → [0,∞)` and a Lean proof that `E_P[e(Y)] ≤ 1` for every law `P`
in `𝒜` satisfying `H₀ : aᵀβ⋆ = v`; the kernel checks; the data are revealed; `e(y)` is the
output. The paper's prose additionally asserts: (i) e-variables of arbitrary dependence may be
averaged; (ii) rounding a valid e-variable downward preserves validity; (iii) the reported
e-values are grid averages of `±λ` two-point e-variables; (iv) `β⋆ = argmin_β E‖Y − Xβ‖²`,
defined without independence; (v) Bahadur–Savage in betting form: over the class of all
finite-mean laws no bet has positive expected return under any alternative. Items (i)–(v) are
not yet theorems in this repo; this task adds them, plus a `Posting`/`Bet` structure so that
the box in the paper is literally a Lean type.

Names already cited in the paper and present (do not rename): `finiteN_tail_twoSided_cantelli`
(FiniteN), `eValue_isValidEValue`, `pValue_eq_survival`, `eValue_equiv_posterior`,
`bahadur_savage`, `lindley_paradox` (PaperAligned), `hoeffding_tail`, `bernstein_tail`,
`two_point_tail`, `two_point_evalue`, `hoeffding_contrast`, `bernstein_contrast`
(BoundedError). Also present and to be re-used: `wsum`, `twoPointMgfBound`, `centredErr`,
`contrastDiff`, `contrastDiff_eq_wsum`, `olsWeights`, `olsEstimator`, `olsEstimand`, `meanVec`,
`olsEstimator_optimal`, `olsEstimator_unique`, `BahadurSavage.prodLaw`,
`BahadurSavage.bahadurSavage_pi`, `EValue.evalue_markov`, `PaperAligned.Distribution`.

Conventions (Mathlib): types/structures `UpperCamelCase`; `Prop`-valued predicates
`UpperCamelCase`, usually `Is…`; data definitions `lowerCamelCase`; theorems `snake_case`.

---

## Milestone A — algebra of e-variables (new file `Ols/EValueAlgebra.lean`, `namespace EValue`)

Throughout: `{Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]`.
Real-valued statements only (the paper's e-variables are real); the `ℝ≥0∞` versions in
`Ols/EValue.lean` are not to be touched.

**A1. Definition.**
```lean
/-- A valid (real-valued) e-variable for the law `P`: nonnegative, integrable, expectation ≤ 1. -/
structure IsEVariable (P : Measure Ω) (e : Ω → ℝ) : Prop where
  nonneg : ∀ ω, 0 ≤ e ω
  integrable : Integrable e P
  expect_le_one : ∫ ω, e ω ∂P ≤ 1
```

**A2. Convex combinations.**
```lean
theorem IsEVariable.sum_smul {ι : Type*} (s : Finset ι) (w : ι → ℝ) (e : ι → Ω → ℝ)
    (hw0 : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1)
    (he : ∀ i ∈ s, IsEVariable P (e i)) :
    IsEVariable P (fun ω => ∑ i ∈ s, w i * e i ω)
```
Proof: nonnegativity termwise; integrability by `Integrable.finset_sum` and
`Integrable.const_mul`; `integral_finset_sum`, `integral_const_mul`, then
`∑ wᵢ ∫eᵢ ≤ ∑ wᵢ · 1 = 1` by `Finset.sum_le_sum` and `hw1`. No dependence assumption anywhere —
that is the point (the paper: "e-values of arbitrary dependence may be combined by averaging").

Corollary, the equal-weight average used in the paper (`k ≥ 1` components):
```lean
theorem IsEVariable.average {k : ℕ} (hk : 0 < k) (e : Fin k → Ω → ℝ)
    (he : ∀ j, IsEVariable P (e j)) :
    IsEVariable P (fun ω => (∑ j, e j ω) / k)
```

**A3. Downward rounding.**
```lean
theorem IsEVariable.of_le (e e' : Ω → ℝ) (he : IsEVariable P e)
    (hmeas : AEStronglyMeasurable e' P) (h0 : ∀ ω, 0 ≤ e' ω) (hle : ∀ ω, e' ω ≤ e ω) :
    IsEVariable P e'
```
Proof: `Integrable.mono' he.integrable hmeas (ae_of_all _ (fun ω => by
rw [Real.norm_eq_abs, abs_of_nonneg (h0 ω)]; exact hle ω))`, then `integral_mono` and
`he.expect_le_one`. (This backs the paper's remark that an implementation may round `e` down.)

**A4. Markov, real form.**
```lean
theorem IsEVariable.markov (e : Ω → ℝ) (he : IsEVariable P e) {c : ℝ} (hc : 0 < c) :
    P.real {ω | c ≤ e ω} ≤ 1 / c
```
Proof: `MeasureTheory.mul_meas_ge_le_integral_of_nonneg` (check the exact name/form in the
vendored Mathlib: it gives `ε * μ.real {x | ε ≤ f x} ≤ ∫ f` for `0 ≤ f`, `Integrable f`), then
divide by `c` and use `expect_le_one`. Sanity check: with `c = 1/α` this is
`P.real {1/α ≤ e} ≤ α`, the p-value conversion the paper states.

---

## Milestone B — e-variable forms of the Hoeffding and Bernstein routes (`Ols/BoundedError.lean`)

Add a new `section EValueForms` at the end of the file (before `end BoundedError`), in the
style of `two_point_evalue`. Setting exactly as in `hoeffding_tail`/`bernstein_tail`
(`γ B s : Fin n → ℝ`, `ε : Fin n → Ω → ℝ`, `hmeas`, `hindep : iIndepFun ε P`, `hmean`, `hbdd`,
`hvar`).

**B1. Hoeffding.** For `0 ≤ lam`:
```lean
theorem hoeffding_evalue … {lam : ℝ} (hlam : 0 ≤ lam) :
    ∫ ω, Real.exp (lam * wsum γ ε ω)
      / Real.exp (lam ^ 2 * (∑ i, (γ i * B i) ^ 2) / 2) ∂P ≤ 1
```
Proof: the numerator's integral is `mgf (wsum γ ε) P lam`. The file's private
`hasSubgaussianMGF_weighted` gives each `γ i * ε i` as sub-Gaussian with proxy
`((‖b − (−b)‖₊/2)^2)`, `b = |γ i| * B i`, which `proxy_eq` rewrites to `(γ i * B i)^2`;
`HasSubgaussianMGF.sum_of_iIndepFun` (or the name used inside `hoeffding_one_tail` via
`measure_sum_ge_le_of_iIndepFun`; grep Mathlib's `SubGaussian.lean` for the sum lemma) gives
`HasSubgaussianMGF (wsum) (∑ proxies)`, and `HasSubgaussianMGF.mgf_le` gives
`mgf ≤ exp (c * t^2 / 2)`. Then `integral_div`, `div_le_one` (the denominator is `exp _ > 0`).
Since `hoeffding_one_tail` is private you cannot call it, but you can copy its two-line
construction of the sub-Gaussian sum.

**B2. Bernstein.** For `0 ≤ lam`, `M > 0` with `∀ i, |γ i| * B i ≤ M` and `lam * M < 3`:
```lean
theorem bernstein_evalue … {M : ℝ} (hMpos : 0 < M) (hM : ∀ i, |γ i| * B i ≤ M)
    {lam : ℝ} (hlam : 0 ≤ lam) (hlamM : lam * M < 3) :
    ∫ ω, Real.exp (lam * wsum γ ε ω)
      / Real.exp (lam ^ 2 * (∑ i, (γ i * s i) ^ 2) / (2 * (1 - lam * M / 3))) ∂P ≤ 1
```
Proof: this is exactly the private `mgf_wsum_le` divided through. Since it is private, add
immediately after it a public restatement
```lean
theorem bernstein_mgf_le … : mgf (wsum γ ε) P t ≤ Real.exp (t ^ 2 * (∑ i, (γ i * s i) ^ 2) / (2 * (1 - t * M / 3))) :=
  mgf_wsum_le γ B s ε hmeas hindep hmean hbdd hvar hMpos hM ht htM
```
(a private lemma may be used inside its own file), then `integral_div`, `div_le_one`.

Both theorems: `#print axioms` must show only `propext, Classical.choice, Quot.sound`.

---

## Milestone C — Bahadur–Savage for e-variables (`Ols/BahadurSavage.lean` + `Ols/PaperAligned.lean`)

**C1.** `bahadurSavage_pi` carries a hypothesis `hφ1 : ∀ x, φ x ≤ 1` that its proof does not use
(see `BAHADUR_SAVAGE_PROGRESS.md`). Add, in `section ManyObservations` right after it, the
version without that hypothesis, with the same four-line proof:
```lean
theorem bahadurSavage_pi_unbounded
    {n : ℕ} {α : ℝ≥0∞} {φ : (Fin n → ℝ) → ℝ≥0∞} (hφ : Measurable φ)
    (hsize : ∀ Q : Measure ℝ, IsProbabilityMeasure Q → Integrable id Q →
        (∫ x, x ∂Q) = 0 → (∫⁻ x, φ x ∂(prodLaw n Q)) ≤ α)
    (P : Measure ℝ) [IsProbabilityMeasure P] (hP : Integrable id P) :
    (∫⁻ x, φ x ∂(prodLaw n P)) ≤ α
```
(Same proof body as `bahadurSavage_pi`; if the private helpers are in a different section,
place the new theorem where they are in scope.)

**C2. The e-variable statement** (new `section EValueForm` in the `BahadurSavage` namespace,
general null value `μ₀` as in `bahadurSavage_pvalue_pi'`; mirror how that theorem shifts by
`μ₀`):
```lean
/-- **Bahadur–Savage, e-value form.** If `E` is an e-variable for `H₀ : mean = μ₀` under every
finite-mean null law, then its expectation is at most `1` under EVERY finite-mean law, whatever
its mean: no bet against `H₀` has positive expected return under any alternative. -/
theorem bahadurSavage_evalue_pi {n : ℕ} (μ₀ : ℝ) {E : (Fin n → ℝ) → ℝ≥0∞} (hE : Measurable E)
    (hvalid : ∀ Q : Measure ℝ, IsProbabilityMeasure Q → Integrable id Q →
        (∫ x, x ∂Q) = μ₀ → (∫⁻ y, E y ∂(prodLaw n Q)) ≤ 1)
    (P : Measure ℝ) [IsProbabilityMeasure P] (hP : Integrable id P) :
    (∫⁻ y, E y ∂(prodLaw n P)) ≤ 1
```
Proof: `bahadurSavage_pi_unbounded` with `α = 1`, after the `μ₀`-shift used by
`bahadurSavage_pvalue_pi'` (translate by `μ₀` coordinatewise; reuse whatever that proof does —
read it first).

**C3. Paper-aligned wrapper** (`Ols/PaperAligned.lean`, section A, next to `ValidPValue`):
```lean
/-- The expectation of a nonnegative statistic under `n` i.i.d. draws from `F`. -/
noncomputable def Distribution.expect (F : Distribution) {n : ℕ} (e : (Fin n → ℝ) → ℝ) : ℝ :=
  (∫⁻ y, ENNReal.ofReal (e y) ∂(prodLaw n F.law)).toReal

/-- A valid e-value for `H₀ : mean = μ₀` over the class of all finite-mean distributions. -/
structure ValidEValue (n : ℕ) (μ₀ : ℝ) where
  value : (Fin n → ℝ) → ℝ
  measurable : Measurable value
  nonneg : ∀ y, 0 ≤ value y
  valid : ∀ F : Distribution, F.mean = μ₀ → F.expect value ≤ 1

/-- **Bahadur–Savage, e-value form.** -/
theorem bahadur_savage_evalue {n : ℕ} {μ₀ : ℝ} (E : ValidEValue n μ₀) (F : Distribution) :
    F.expect E.value ≤ 1
```
Proof: unfold `expect`; `ENNReal.toReal_le_of_le_ofReal`-style bookkeeping to pass between
`toReal ≤ 1` and `lintegral ≤ 1` (the lintegral is finite whenever `≤ 1`); apply
`bahadurSavage_evalue_pi` with `E := fun y => ENNReal.ofReal (value y)`
(`hE.ennreal_ofReal`). The `hvalid` hypothesis comes from `E.valid` packaged as a
`Distribution` (`⟨Q, hQ, hint⟩`), exactly as `bahadur_savage` does for `ValidPValue`.

NOTE for the paper (record in `PROTOCOL_PROGRESS.md`, do not act): this is the *expectation*
form. The prose currently says "no bet can pay more than its stake under any outcome"
(pointwise); over i.i.d. product laws the pointwise form is not what this theorem gives. The
paper will be aligned to the expectation form.

---

## Milestone D — the projection parameter is the population least-squares minimiser (new file `Ols/Estimand.lean`)

Imports: `Ols.Optimality`, `Ols.ProjectionCLT`. Setting: `{Ω} [MeasurableSpace Ω] (P : Measure Ω)
[IsProbabilityMeasure P] (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → Ω → ℝ)` with
`hy : ∀ i, MemLp (y i) 2 P` (second moments only — **no independence hypothesis anywhere in
this file**; that is the paper's claim "the projection parameter is defined without assuming
independence").

First locate `normSq` as used by `olsEstimator_optimal` (grep `normSq` in `Ols/Optimality.lean`
or its imports) and use the same function.

**D1. Second-moment decomposition.** For every `β : Fin p → ℝ`:
```lean
theorem integral_normSq_sub_mulVec (hy : ∀ i, MemLp (y i) 2 P) (β : Fin p → ℝ) :
    ∫ ω, normSq ((fun i => y i ω) - X *ᵥ β) ∂P
      = normSq (meanVec y P - X *ᵥ β) + ∑ i, variance (y i) P
```
Proof: `normSq` is a finite sum of squares; per coordinate
`(yᵢ − mᵢ)² = (yᵢ − μᵢ)² + 2(yᵢ − μᵢ)(μᵢ − mᵢ) + (μᵢ − mᵢ)²` with `μᵢ = P[y i]`, `mᵢ = (X *ᵥ β) i`;
integrate (`integral_finset_sum`, `integral_add`, `integral_const_mul`, `integral_const`); the
cross term vanishes by `integral_sub`/`hmean`; the first term is `variance (y i) P` by
`variance_def'`/`MemLp.variance_eq` (check the current Mathlib name; `ProbabilityTheory.variance`
with `MemLp _ 2` hypotheses). Integrability of each piece from `MemLp … 2` via
`MemLp.integrable_sq` and `MemLp.integrable` (`one_le_two`).

**D2. Optimality of the estimand.** With `hX_inv : IsUnit (Xᵀ * X).det`:
```lean
theorem olsEstimand_optimal (hy : ∀ i, MemLp (y i) 2 P) (hX_inv : IsUnit (Xᵀ * X).det)
    (β : Fin p → ℝ) :
    ∫ ω, normSq ((fun i => y i ω) - X *ᵥ olsEstimand P X y) ∂P
      ≤ ∫ ω, normSq ((fun i => y i ω) - X *ᵥ β) ∂P
```
Proof: rewrite both sides with D1; the variance sum is common; `olsEstimand P X y =
olsEstimator X (meanVec y P)` by definition (`rfl`/`unfold`), so the remaining inequality is
`olsEstimator_optimal X (meanVec y P) hX_inv β`.

**D3. Uniqueness** (same shape, from `olsEstimator_unique`):
```lean
theorem olsEstimand_unique (hy : …) (hX_inv : …) (β : Fin p → ℝ) :
    ∫ ω, normSq ((fun i => y i ω) - X *ᵥ β) ∂P
      = ∫ ω, normSq ((fun i => y i ω) - X *ᵥ olsEstimand P X y) ∂P ↔ β = olsEstimand P X y
```

`#print axioms olsEstimand_optimal` must not mention any independence lemma (it cannot; just
confirm the axiom list is the standard three).

---

## Milestone E — the protocol as a Lean type (new file `Ols/Protocol.lean`, `namespace Protocol`)

Imports: `Ols.EValueAlgebra`, `Ols.BoundedError`, `Ols.FiniteN` (for `centredErr`,
`contrastDiff`, `olsWeights`). Keep `Ω` general, as every finite-sample theorem in the repo
does; a "model" is `(P : Measure Ω, y : Fin n → Ω → ℝ)`.

**E1. Posting** — what the scientist publishes (numeric objects; the class is a predicate):
```lean
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
```

**E2. Bet** — what the AI submits; `e` is a function of the data vector only:
```lean
/-- A bet against `H₀`: an e-variable of the data, valid under every law in the class that
satisfies `H₀`. The AI provides `e` and the proof `valid`. -/
structure Bet (post : Posting n p) (𝒜 : AssumptionClass Ω n) where
  e : (Fin n → ℝ) → ℝ
  nonneg : ∀ y, 0 ≤ e y
  measurable : Measurable e
  valid : ∀ (P : Measure Ω) (y : Fin n → Ω → ℝ), IsProbabilityMeasure P →
    (∀ i, Measurable (y i)) → 𝒜 P y → NullHolds post P y →
    EValue.IsEVariable P (fun ω => e (fun i => y i ω))
```

**E3. The protocol theorem** (proved once, by the bookmaker; Milestone A4):
```lean
/-- **Guarantee of the protocol.** For every model in the class satisfying `H₀`, and every
`c > 0`, the payout exceeds `c` with probability at most `1/c`. -/
theorem Bet.guarantee (b : Bet post 𝒜) (P : Measure Ω) (y : Fin n → Ω → ℝ)
    [IsProbabilityMeasure P] (hy : ∀ i, Measurable (y i)) (hA : 𝒜 P y)
    (h0 : NullHolds post P y) {c : ℝ} (hc : 0 < c) :
    P.real {ω | c ≤ b.e (fun i => y i ω)} ≤ 1 / c
```

**E4. The bounded-error class and the two-point bet** (the paper's Section 5 route as an
instance). The class:
```lean
/-- Independent outcomes with declared error bound `Bᵢ` and standard-deviation bound `sᵢ`. -/
def boundedErrorClass (B s : Fin n → ℝ) : AssumptionClass Ω n := fun P y =>
  iIndepFun y P ∧ (∀ i ω, |y i ω - P[y i]| ≤ B i) ∧
    (∀ i, ∫ ω, (y i ω - P[y i]) ^ 2 ∂P ≤ (s i) ^ 2)
```
A linear-algebra lemma first (pure `Matrix` algebra; `olsWeights X a = X *ᵥ ((Xᵀ*X)⁻¹ *ᵥ a)`,
`olsEstimator X w = (Xᵀ*X)⁻¹ *ᵥ (Xᵀ *ᵥ w)`):
```lean
lemma sum_olsWeights_mul (X : Matrix (Fin n) (Fin p) ℝ) (a : Fin p → ℝ) (w : Fin n → ℝ) :
    ∑ i, olsWeights X a i * w i = a ⬝ᵥ olsEstimator X w
```
(`Matrix.dotProduct_mulVec`, `Matrix.vecMul_transpose`, `Matrix.mulVec_mulVec`; the Gram
inverse is symmetric: `(Xᵀ*X)⁻¹ᵀ = (Xᵀ*X)⁻¹` via `Matrix.transpose_nonsing_inv` and
`Matrix.transpose_mul`.) Consequently, under `NullHolds`,
`wsum (olsWeights X a) (centredErr P y) ω = a ⬝ᵥ olsEstimator X (fun i => y i ω) - v`
(lemma `contrastDiff_eq_sub_v`, from `contrastDiff_eq_wsum`, `sum_olsWeights_mul` applied to
`fun i => y i ω` and to `meanVec y P`, and `olsEstimand = olsEstimator X (meanVec y P)`).

The two-point bet at a fixed `lam ≥ 0`, with `hb : ∀ i, 0 < |olsWeights post.X post.a i| * B i`:
```lean
noncomputable def twoPointBet (post : Posting n p) (B s : Fin n → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (hb : ∀ i, 0 < |olsWeights post.X post.a i| * B i) :
    Bet post (boundedErrorClass (Ω := Ω) B s) where
  e := fun w => Real.exp (lam * (post.a ⬝ᵥ olsEstimator post.X w - post.v))
      / ∏ i, twoPointMgfBound lam ((olsWeights post.X post.a i * s i) ^ 2)
                                  (|olsWeights post.X post.a i| * B i)
  nonneg := …   -- exp > 0, product > 0 (`twoPointMgfBound_pos`)
  measurable := …  -- `by fun_prop` after unfolding, or `Measurable.div_const` of a continuous map
  valid := …   -- rewrite `e ∘ data` as `exp (lam * wsum …) / ∏ …` via `contrastDiff_eq_sub_v`,
               -- then `two_point_evalue` (needs `centredErr_props` for hmeas/hindep/hmean, as in
               -- `hoeffding_contrast`); integrability from boundedness (`integrable_of_bdd`,
               -- |wsum| ≤ ∑ |γᵢ| Bᵢ) — package as `IsEVariable`
```
And the paper's grid average (both signs; `lam : Fin k → ℝ`, all `≥ 0`, weights `1/(2k)`):
```lean
noncomputable def gridBet (post) (B s) {k : ℕ} (hk : 0 < k) (lam : Fin k → ℝ) (hlam : ∀ j, 0 ≤ lam j)
    (hb : …) : Bet post (boundedErrorClass B s)
```
with `e := fun w => (∑ j, (twoPointBet … (lam j)).e w + (twoPointBet' … (lam j)).e w) / (2k)`
where the primed bet uses `-post.a` (or equivalently `−lam` with the mirrored bound; note
`twoPointMgfBound` depends on `γ` only through `|γᵢ|` and `γᵢ²`, so the denominator is unchanged
under `a ↦ −a`; the `NullHolds` for `−a` is `−v`). Validity by `IsEVariable.sum_smul` (A2).
If the sign-mirroring bookkeeping gets long, deliver `gridBet` for the one-sided family first
and log the two-sided version as the remaining step.

**E5. Sanity examples** (rule 8): an `example` that `twoPointBet` at `lam = 0` has `e ≡ 1`
(`twoPointMgfBound 0 v b = 1`), and that `Bet.guarantee` with `c = 20` yields `≤ 1/20`.

---

## Milestone F — the two-point contrast corollary (`Ols/BoundedError.lean`, `section OlsContrast`)

`TWO_POINT.md` Milestone D, still open. Mirror `bernstein_contrast` exactly:
```lean
theorem two_point_contrast [IsProbabilityMeasure P] (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → Ω → ℝ) (a : Fin p → ℝ) (B s : Fin n → ℝ)
    (hmeas : ∀ i, Measurable (y i)) (hindep : iIndepFun y P)
    (hbdd : ∀ i ω, |y i ω - P[y i]| ≤ B i)
    (hvar : ∀ i, ∫ ω, (y i ω - P[y i]) ^ 2 ∂P ≤ (s i) ^ 2)
    (hb : ∀ i, 0 < |olsWeights X a i| * B i) {lam : ℝ} (hlam : 0 ≤ lam) {u : ℝ} (hu : 0 ≤ u) :
    P.real {ω | u ≤ |contrastDiff P X y a ω|}
      ≤ 2 * Real.exp (-lam * u) * ∏ i, twoPointMgfBound lam ((olsWeights X a i * s i) ^ 2) (|olsWeights X a i| * B i)
```
Proof: `centredErr_props`, `contrastDiff_eq_wsum`, `two_point_tail`.

---

## Milestone G — verification only (no new code unless something is missing)

Run and record in `PROTOCOL_PROGRESS.md` the `#print axioms` output of:
- `hc2_studentized_twoSample_eq_welch` (`Ols/Welch.lean`) — the paper says the Welch t-test
  is the HC2-studentised contrast on the one-hot design; confirm sorry-free and quote the
  statement's hypotheses (`2 ≤ m`, `2 ≤ k`).
- `hc0_sandwich_consistent`, `hc1_…`, `hc2_…`, `hc3_…` (`Ols/HCSandwichConsistency.lean`) —
  the paper says HC0–HC3 are covered.
- `finiteN_tail_twoSided_cantelli` and `FiniteSampleBundle.aMinus_pos_hc3` — the
  misspecification-free Cantelli route; confirm no `C_r`/tolerance field is among their
  hypotheses (the paper appendix still mentions one and will be corrected).
If any of these carries `sorryAx` other than through `Clt/BerryEsseen.lean`, say so; do not fix
existing files.

---

## Milestone H — certifying the Monte Carlo exhibit (added 24 Sep 2026)

The paper's MC column is an adversarial search over the "best-chance" class
𝒜_bc = { independent errors, equal variances σ², E|ε/σ|³ ≤ √(8/π), E(ε/σ)⁴ ≤ 3, |r_i| ≤ σ/2 }
for the HC0-studentised statistic T; each tabulated number is the exceedance frequency
P̂(|T| ≥ t₀) of one explicit member of the class ("the candidate"), on B fresh draws.
The search itself is NOT to be formalised. Two things are:

### H1 — each candidate is a member of the class (exact arithmetic)

Candidates are saved by `~/Documents/svn/wps/lean_blog/mc_search/driver2.py` as
`laws/laws_<dataset>_mode<m>_<init>.npy`, one row per observation: 89 masses on the atom grid
`make_grid()` of `search.py` (dyadic-rational floats, so exactly representable in `ℚ`), then
the misspecification vector `r` (in σ units). Each row has at most 5 non-zero masses (an LP
vertex). A small Python export step (to write) must, per candidate:
1. keep the ≤5 atoms with positive mass, as exact rationals (`fractions.Fraction(float)`);
2. re-solve the three equalities Σp = 1, Σp·x = 0, Σp·x² = 1 exactly in `ℚ` for three of the
   masses, the others fixed (the LP solution satisfies them to 1e-16, so the repair is tiny);
   fail if any repaired mass is negative;
3. check Σp·|x|³ ≤ 15957/10000 and Σp·x⁴ ≤ 3 in exact arithmetic, with the margin
   (15957/10000)² < 8/π (Mathlib: `Real.pi_lt_d4`-type bounds; 2.5463 < 8/3.1416 = 2.5465);
4. for `r`: mode-0 candidates have r = 0 (nothing to check). For the one tabulated mode-2
   candidate (cars, `mode2_zi`, max|r| = 0.28) project the float `r` exactly onto ker(Xᵀ) in
   `ℚ` (r' = r − X(XᵀX)⁻¹Xᵀr with `X` the exported design as rationals) and check
   |r'_i| ≤ 1/2 for all i. Do NOT use the mode-2 candidates for GISTEMP (max|r| = 1.83) or
   Hubble1929 (0.94): they lie outside the class and their numbers must not be tabulated;
5. emit a Lean file `Ols/MCCandidates/<dataset>.lean` containing the data as `List (List (ℚ × ℚ))`
   (atoms, masses) and, where relevant, `r : List ℚ`.

Lean side (new file `Ols/MCCandidate.lean`):
```lean
/-- One observation's error law: finitely many atoms with masses. -/
structure AtomLaw where
  atoms : List (ℚ × ℚ)          -- (x, p)

/-- Membership of a standardised law in the best-chance moment class. -/
def AtomLaw.inMomentClass (L : AtomLaw) : Bool :=
  L.atoms.all (fun a => 0 ≤ a.2) &&
  (L.atoms.map (·.2)).sum == 1 &&
  (L.atoms.map (fun a => a.2 * a.1)).sum == 0 &&
  (L.atoms.map (fun a => a.2 * a.1 ^ 2)).sum == 1 &&
  (L.atoms.map (fun a => a.2 * |a.1| ^ 3)).sum ≤ 15957 / 10000 &&
  (L.atoms.map (fun a => a.2 * a.1 ^ 4)).sum ≤ 3

def candidateInClass (c : List AtomLaw) (r : List ℚ) : Bool :=
  c.all AtomLaw.inMomentClass && r.all (fun ri => |ri| ≤ 1 / 2)
```
plus a bridge theorem (prose-level statement of the paper's class) showing that
`inMomentClass = true` implies the real-valued moment conditions with the `√(8/π)` bound:
`(15957/10000 : ℝ) ≤ Real.sqrt (8 / Real.pi)` from `Real.pi_lt_d4` (or the sharper
`Real.pi_lt_3141593`). Then, per dataset, `theorem cars_candidate_ok : candidateInClass carsLaws carsR = true := by decide`.
Use `decide` (kernel evaluation of `ℚ` arithmetic), NOT `native_decide` (extra axiom): the
paper says only Lean's three standard axioms are used. If `decide` is too slow at n = 1175
(Reinhart–Rogoff) or n = 3492 (SH0ES), split the list into chunks with one lemma per chunk.
The `Xᵀr' = 0` condition for cars is a second `Bool` check on rationals (`X` has 50×2 entries).

### H2 — the marker's confidence limit is a theorem of the routes already formalised

The MC marker of each row is k exceedances in B draws of the candidate; the paper wants a
95% lower confidence limit on the candidate's true exceedance probability c. A binomial
count is a weighted sum of independent, bounded, mean-zero errors, so `bernstein_tail`
(and `two_point_one_tail`, sharper) apply with γ_j = 1, B_j = 1, s_j² = c(1−c) ≤ c, u = k − Bc:
```lean
/-- If the true exceedance probability is at most `cL`, seeing `k` or more exceedances in
`B` draws has probability at most `0.05`. `ξ j` are the exceedance indicators. -/
theorem mc_marker_certified {B : ℕ} (ξ : Fin B → Ω → ℝ) [IsProbabilityMeasure P]
    (hmeas : ∀ j, Measurable (ξ j)) (hindep : iIndepFun ξ P)
    (h01 : ∀ j ω, ξ j ω = 0 ∨ ξ j ω = 1) {c : ℝ} (hc : ∀ j, ∫ ω, ξ j ω ∂P = c)
    {k : ℕ} {cL : ℝ} (hcL : c ≤ cL) (hk : (k - B * cL) ^ 2 / (2 * (B * cL + (k - B * cL) / 3)) ≥ 4)
    (hkc : B * cL ≤ k) :
    P.real {ω | (k : ℝ) ≤ ∑ j, ξ j ω} ≤ 1 / 20
```
Proof sketch: apply `bernstein_tail` to ε_j = ξ_j − c with B_j = 1, s_j = 1 (variance
c(1−c) ≤ 1 — or s_j² = c for a sharper bound), M = 1, u = k − Bc ≥ k − B·cL ≥ 0; the bound is
2·exp(−u²/(2(Σs_j² + u/3))); monotonicity in c (numerator decreasing, denominator increasing
for c ≤ k/B) reduces to the hypothesis `hk` at cL; then 2·exp(−4) ≤ 1/20 from
`Real.exp_one_gt_d9` (exp 1 > 2.7182818283, so exp 4 > 54 > 40). Do the two-sided bound first;
the one-sided `two_point_one_tail` version (exact Chernoff for a Bernoulli) is the sharper
"chernoff_cert" column below and can follow.

Certified limits to be reproduced (k, B from `mc_search/all_results.csv`, mode 0 unless
stated; computed 24 Sep 2026 in R):

| dataset | k | B | p̂ = k/B | Clopper–Pearson 95% | Bernstein-certified | Chernoff-certified |
|---|---|---|---|---|---|---|
| cars (mode 2 zi) | 2031 | 4e6 | 5.08e-4 | 4.89e-4 | 4.78e-4 | 4.81e-4 |
| Boston | 43 | 5e5 | 8.6e-5 | 6.56e-5 | 5.50e-5 | 5.78e-5 |
| Card–Krueger | 23568 | 5e5 | 4.71e-2 | 4.66e-2 | 4.63e-2 | 4.64e-2 |
| Reinhart–Rogoff | 4 | 5e5 | 8.0e-6 | 2.73e-6 | 9.92e-7 | 1.73e-6 |
| streptomycin | 20091 | 2e6 | 1.00e-2 | 9.93e-3 | 9.85e-3 | 9.87e-3 |
| anorexia | 42807 | 4e6 | 1.07e-2 | 1.06e-2 | 1.06e-2 | 1.06e-2 |
| GISTEMP | 7 | 4e6 | 1.75e-6 | 8.21e-7 | 4.66e-7 | 5.87e-7 |

Each row then becomes a numeric corollary of `mc_marker_certified` with its (k, B, cL) as
rationals, proved by `norm_num`. Rows with k = 0 (Galton, Mincer, Moore, Chinchilla, Hubble
creationist, SH0ES at 5e5 draws) certify nothing and stay "none found".

## Milestone I — p-to-e calibration (added 24 Sep 2026; needed by the paper's Table 1 and Figure 2)

The paper converts p-values to e-values with the Vovk–Wang calibrator at κ = 1/2, e = 1/(2√p),
and Table 1 names the theorem `calibrate_pvalue` as if it existed. It does not: nothing in this
project, in Degenne–Serré's e-values repository, in statlib, or in Mathlib proves the p-to-e
direction (the e-to-p direction is `IsEVariable.markov` / `IsValidEValue.test`). Write it in
`Ols/EValueAlgebra.lean` (namespace `EValue`), sorry-free, standard axioms only.

### I1 — the specific calibrator (this is what the paper uses)

```lean
/-- A p-variable: `P(p ≤ α) ≤ α` for every `α ∈ [0,1]`. -/
def IsPVariable (P : Measure Ω) (p : Ω → ℝ) : Prop :=
  Measurable p ∧ (∀ ω, 0 ≤ p ω) ∧ ∀ α : ℝ, 0 ≤ α → α ≤ 1 → P.real {ω | p ω ≤ α} ≤ α

/-- The κ = 1/2 Vovk–Wang calibrator. -/
noncomputable def calibrator (p : ℝ) : ℝ := 1 / (2 * Real.sqrt p)

/-- **Calibration.** A valid p-variable calibrates to an e-variable. -/
theorem calibrate_pvalue [IsProbabilityMeasure P] {p : Ω → ℝ} (hp : IsPVariable P p) :
    IsEVariable P (fun ω => calibrator (p ω))
```
`IsEVariable` is the Milestone A structure (nonneg, integrable, integral ≤ 1). Proof: layer cake
(`MeasureTheory.lintegral_eq_lintegral_meas_lt` or the `∫⁻ f = ∫⁻ t, μ {f > t}` form) applied
to `f = calibrator ∘ p`; for `t > 0`, `{calibrator (p ω) > t} = {p ω < 1/(4t²)}`, whose measure
is `≤ min 1 (1/(4t²))` by `hp`; and `∫₀^∞ min 1 (1/(4t²)) dt = 1/2 + 1/2 = 1`. Integrability
follows from the same bound. Watch `p ω = 0` (calibrator = +∞ in ℝ≥0∞ terms; in ℝ, `1/0 = 0`):
either work in `ℝ≥0∞` throughout, or add `hp0 : ∀ ω, 0 < p ω` and note the p-values in the paper
are positive (Gaussian tails, Cantelli bounds), or handle the null set `{p = 0}` via `hp` at α = 0.

### I2 — the tail form for the asymptotic column (optional; the paper does NOT claim an
asymptotic e-value, Table 1 says N/A)

If wanted later: from `hc0_pvalue_conservative` (`Ols/TTest.lean`,
`limsup P{p(t̂ₙ) ≤ α} ≤ α`) derive `limsup P{calibrator (p(t̂ₙ)) ≥ c} ≤ 1/c` for `c ≥ 1/4`, by
`{calibrator p ≥ c} = {p ≤ 1/(4c²)}`. Do NOT attempt `limsup E[calibrator ∘ pₙ] ≤ 1`: it is false
in general (the calibrator is unbounded near 0; convergence in distribution gives no uniform
integrability).

### I3 — general calibrators (not needed for the paper)

Vovk–Wang Proposition 2.1: any decreasing `f : [0,1] → [0,∞]` with `∫₀¹ f ≤ 1` calibrates. Only
if I1 is done and time remains; needs a generalised inverse.

Add `calibrate_pvalue` to the `#print axioms` list in the Report section.

## Report

When done (or when stopping), `PROTOCOL_PROGRESS.md` must contain: per-milestone status;
`#print axioms` for `IsEVariable.sum_smul`, `IsEVariable.of_le`, `IsEVariable.markov`,
`hoeffding_evalue`, `bernstein_evalue`, `bahadurSavage_evalue_pi`, `bahadur_savage_evalue`,
`olsEstimand_optimal`, `Bet.guarantee`, `twoPointBet` (its `valid` field, via a named theorem
if easier), `two_point_contrast`, `mc_marker_certified`, every `*_candidate_ok`, and `calibrate_pvalue`; the Milestone G outputs; deviations with reasons; and the
result of a full `~/.elan/bin/lake build` (expected: clean, exactly one `sorry` warning, the
pre-existing `Clt/BerryEsseen.lean:55`). Commit locally after each milestone. Do not push.
