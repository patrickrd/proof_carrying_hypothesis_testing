# PAPER_ALIGNMENT — reader-facing statements for the ICLR "Paradoxes" section

## Goal

Add a **thin, sorry-free layer** that re-exposes the three results already proved
(Bahadur–Savage, Lindley, e-values) under names and notation that match the paper
(`ICLR_submission/main.tex`), so a reader who does not know Lean can line the code up
against the prose. Everything here is a **wrapper** over existing theorems — no new
mathematics, and the existing files are **not modified**.

Put all of it in **one new file `Ols/PaperAligned.lean`**:

```lean
import Ols.BahadurSavage
import Ols.EValue
import Ols.Lindley
open MeasureTheory ProbabilityTheory
namespace PaperAligned
```

Check the namespaces of the wrapped lemmas first and qualify as needed
(`EValue.evalue_markov`, `Lindley.pval_eq_survival`, etc. — grep for `namespace`).

## Naming conventions (Mathlib) — follow these exactly

| Kind | Convention | Names to use here |
|---|---|---|
| Types / structures / classes | `UpperCamelCase` | `Distribution`, `ValidPValue` |
| Properties (functions **to `Prop`**) | `UpperCamelCase`, usually `Is…` | `IsValidEValue` |
| Data definitions (return a value) | `lowerCamelCase` | `pValue`, `posterior`, `eValue`, `nullProb`, `nullExp`, `Distribution.mean`, `Distribution.prob` |
| Theorems / lemmas (proofs) | **`snake_case`** | `bahadur_savage`, `lindley_paradox`, `pValue_eq_survival`, … |

A `snake_case` theorem name may embed a `lowerCamelCase`/`UpperCamelCase` token from a
definition it mentions (e.g. `pValue_eq_survival`, `eValue_isValidEValue`); that is normal.

**`eq` vs `equiv`.** Two theorems relate the e-value and the posterior. Name the
π-as-a-function-of-E direction `posterior_eq_eValue` (it *is* a literal equation
`π = 1/(1+κE)`). Name the direction the paper cites — `E = (1/κ)(1−π)/π` —
`eValue_equiv_posterior`: the name deliberately says **equiv**, because `E` and `π`
are *equivalent* (each determines the other), not equal. The statement is still an
`=` between `E` and a formula in `π`; only the name changes.

## Existing lemmas to wrap (do NOT edit these files)

- `Ols/BahadurSavage.lean`
  - `prodLaw (n : ℕ) (P : Measure ℝ) : Measure (Fin n → ℝ)` — the i.i.d. product law.
  - `bahadurSavage_pvalue_pi'` — general null value `μ₀`: for a measurable `P`, if
    `prodLaw n Q {y | P y ≤ α} ≤ ENNReal.ofReal α` for every probability `Q` with
    `Integrable id Q` and mean `μ₀`, then the same holds for **every** such `Q`.
- `Ols/EValue.lean`
  - `evalue_expectation_eq_one` — `∫⁻ (p₁/p₀) ∂(ν.withDensity p₀) = 1`.
  - `evalue_markov` — `P₀ {ω | 1/α ≤ E ω} ≤ α` for `∫⁻ E ∂P₀ ≤ 1` (`E : Ω → ℝ≥0∞`).
  - `posterior_eq` — `(c p₀)/(c p₀+(1−c)p₁) = 1/(1 + ((1−c)/c)·(p₁/p₀))`.
  - `evalue_of_posterior` — `p₁/p₀ = (c/(1−c))·(1−π)/π`.
  - `posterior_ge_iff` — `1−β ≤ 1/(1+κe) ↔ e ≤ β/(κ(1−β))`.
- `Ols/Lindley.lean`
  - defs `g0, g1, pval, post, E, S₀` (parameters `σ μ₀ l c` explicit; `g0 = gaussianPDFReal μ₀ (v σ n)`).
  - `lindley` — `∃ (n) (y : ℝ), 1 ≤ n ∧ pval σ μ₀ n y ≤ ε ∧ post σ μ₀ l c n y ≥ 1 − ε`.
  - `pval_eq_survival` — `pval σ μ₀ n y = S₀ σ μ₀ l n (E σ μ₀ l n y)`.
  - helpers: `g0_pos`, `g1_nonneg`, `E_eq_F`, `E_ge_iff`, `coe_v`, `v_ne_zero`.

## Frame decision (read before writing)

- **Bahadur–Savage stays over the raw i.i.d. sample** `Y : Fin n → ℝ` — that is where the
  i.i.d. structure matters, and `bahadurSavage_pvalue_pi'` is already stated over `prodLaw`.
- **Lindley's p-value and posterior are over the raw sample** `Y : Fin n → ℝ`, defined through
  the sample mean (`pValue σ μ₀ Y := pval σ μ₀ n (mean Y)`, likewise `posterior`). `lindley_paradox`
  is stated over `Y` with **no `1 ≤ n`** conjunct — it is an existential and the proof supplies a
  concrete `n ≥ 1` internally (witness with the constant sample `fun _ => ybar`, whose mean is `ybar`).
- **The e-value machinery stays over the sample mean** `ybar : ℝ` (null law of the average
  `gaussianReal μ₀ (v σ n)`): `eValue`, `IsValidEValue`, `eValue_isValidEValue`, `IsValidEValue.test`.
  Its validity/expectation genuinely needs the average's sampling law; lifting it to the raw vector
  `Y` would require Gaussian additivity (mean of i.i.d. normals is normal) and is **out of scope**.
- The cross theorems (`pValue_eq_survival`, `posterior_eq_eValue`, `eValue_equiv_posterior`,
  `no_paradox`) relate the `Y`-level `pValue`/`posterior` to the `ybar`-level `eValue` via `mean Y`,
  and **retain `1 ≤ n` as a hypothesis** (positive variance is genuinely needed there).

## Target declarations (exact signatures)

### A. Bahadur–Savage (raw sample)

```lean
structure Distribution where
  law        : Measure ℝ
  isProb     : IsProbabilityMeasure law
  integrable : Integrable id law

attribute [instance] Distribution.isProb   -- or `haveI := F.isProb` inside proofs

noncomputable def Distribution.mean (F : Distribution) : ℝ := ∫ x, x ∂F.law

noncomputable def Distribution.prob (F : Distribution) {n : ℕ} (A : Set (Fin n → ℝ)) : ℝ :=
  (prodLaw n F.law A).toReal

structure ValidPValue (n : ℕ) (μ₀ : ℝ) where
  value      : (Fin n → ℝ) → ℝ
  measurable : Measurable value
  valid      : ∀ F : Distribution, F.mean = μ₀ →
                 ∀ α : ℝ, 0 ≤ α → α ≤ 1 → F.prob {y | value y ≤ α} ≤ α

theorem bahadur_savage {n : ℕ} {μ₀ : ℝ} (P : ValidPValue n μ₀) (F : Distribution)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    F.prob {y | P.value y ≤ α} ≤ α
```

*Proof.* Apply `bahadurSavage_pvalue_pi'` with `P.value`, `P.measurable`, and the validity
hypothesis obtained from `P.valid`. Two elementary conversions between `ℝ≥0∞` and `ℝ`:
- to *feed* `bahadurSavage_pvalue_pi'`, turn `P.valid`'s real bound `F'.prob {…} ≤ α` into
  `prodLaw n Q {…} ≤ ENNReal.ofReal α` (the measure is finite, so `μ = ENNReal.ofReal μ.toReal`);
  every probability `Q` with `Integrable id Q` and mean `μ₀` is `(⟨Q, ‹_›, ‹_›⟩ : Distribution).law`;
- to *read off* the conclusion, `.toReal` both sides (`ENNReal.toReal_le_toReal`, finiteness of a
  probability measure, and `(ENNReal.ofReal α).toReal = α` since `0 ≤ α`).

### B. Lindley (raw sample `Y`) + e-values (sample mean `ybar`)

```lean
noncomputable def mean {n : ℕ} (Y : Fin n → ℝ) : ℝ := (∑ i, Y i) / n
noncomputable def pValue (σ μ₀ : ℝ) {n : ℕ} (Y : Fin n → ℝ) : ℝ := pval σ μ₀ n (mean Y)
noncomputable def posterior (σ μ₀ l c : ℝ) {n : ℕ} (Y : Fin n → ℝ) : ℝ := post σ μ₀ l c n (mean Y)
noncomputable def eValue (σ μ₀ l : ℝ) (n : ℕ) (ybar : ℝ) : ℝ := E σ μ₀ l n ybar  -- over the average

/-- probability of an event, and expectation of a statistic, under H₀ (the average is
    `gaussianReal μ₀ (v σ n)`), as ordinary reals. -/
noncomputable def nullProb (σ μ₀ : ℝ) (n : ℕ) (A : Set ℝ) : ℝ :=
  (gaussianReal μ₀ (v σ n) A).toReal
noncomputable def nullExp (σ μ₀ : ℝ) (n : ℕ) (g : ℝ → ℝ) : ℝ :=
  ∫ ybar, g ybar ∂ gaussianReal μ₀ (v σ n)

/-- a valid e-value under H₀: measurable, integrable, nonnegative, with expectation at most 1.
    Measurability and integrability are REQUIRED — without them `IsValidEValue.test` is false
    (a non-measurable / non-integrable `e` has Bochner integral `0 ≤ 1`, yet `{1/α ≤ e}` can have
    full outer measure). `eValue_isValidEValue` establishes all four parts for the Bayes factor. -/
def IsValidEValue (σ μ₀ : ℝ) (n : ℕ) (e : ℝ → ℝ) : Prop :=
  Measurable e ∧ Integrable e (gaussianReal μ₀ (v σ n)) ∧
    (∀ ybar, 0 ≤ e ybar) ∧ nullExp σ μ₀ n e ≤ 1

theorem lindley_paradox {σ μ₀ l c : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hc0 : 0 < c) (hc1 : c < 1)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ (n : ℕ) (Y : Fin n → ℝ), pValue σ μ₀ Y ≤ ε ∧ posterior σ μ₀ l c Y ≥ 1 - ε
-- Proof: obtain ⟨n, ybar, hn, hp, hpost⟩ from `lindley`; witness with `n` and `fun _ => ybar`.
-- `mean (fun _ => ybar) = ybar` (uses `hn : 1 ≤ n` internally), so `pValue`/`posterior` reduce
-- to `pval`/`post`. No `1 ≤ n` is exposed in the statement.

-- (1) the Bayes factor is a valid e-value, and it gives a level-α test
theorem eValue_isValidEValue {σ μ₀ l : ℝ} (hσ : 0 < σ) (hl : 0 < l) {n : ℕ} (hn : 1 ≤ n) :
    IsValidEValue σ μ₀ n (eValue σ μ₀ l n)
theorem IsValidEValue.test {σ μ₀ : ℝ} {n : ℕ} {e : ℝ → ℝ}
    (h : IsValidEValue σ μ₀ n e) (α : ℝ) (hα : 0 < α) :
    nullProb σ μ₀ n {ybar | 1 / α ≤ e ybar} ≤ α

-- (2) it corresponds to the p-value:  P = S₀(E) = ℙ(E ≥ E(ybar) | H₀)
theorem pValue_eq_survival {σ μ₀ l : ℝ} (hσ : 0 < σ) (hl : 0 < l) {n : ℕ} (hn : 1 ≤ n)
    (Y : Fin n → ℝ) :
    pValue σ μ₀ Y = nullProb σ μ₀ n {ybar' | eValue σ μ₀ l n (mean Y) ≤ eValue σ μ₀ l n ybar'}
-- restate `pval_eq_survival`; `S₀ σ μ₀ l n x = (gaussianReal μ₀ (v σ n) {y | x ≤ E …}).toReal`
-- is `nullProb σ μ₀ n {ybar' | x ≤ eValue …}` by definition.

-- (3) it satisfies  π = 1/(1 + κE)  and  E = (1/κ)(1 − π)/π,  so no paradox  (κ = (1-c)/c)
theorem posterior_eq_eValue {σ μ₀ l c : ℝ} (hσ : 0 < σ) (hc0 : 0 < c) (hc1 : c < 1)
    {n : ℕ} (hn : 1 ≤ n) (Y : Fin n → ℝ) :
    posterior σ μ₀ l c Y = 1 / (1 + ((1 - c) / c) * eValue σ μ₀ l n (mean Y))
theorem eValue_equiv_posterior {σ μ₀ l c : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hc0 : 0 < c) (hc1 : c < 1)
    {n : ℕ} (hn : 1 ≤ n) (Y : Fin n → ℝ) :
    eValue σ μ₀ l n (mean Y)
      = (c / (1 - c)) * (1 - posterior σ μ₀ l c Y) / posterior σ μ₀ l c Y
theorem no_paradox {σ μ₀ l c : ℝ} (hσ : 0 < σ) (hl : 0 < l) (hc0 : 0 < c) (hc1 : c < 1)
    {n : ℕ} (hn : 1 ≤ n) (Y : Fin n → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    1 - β ≤ posterior σ μ₀ l c Y ↔ eValue σ μ₀ l n (mean Y) ≤ β / (((1 - c) / c) * (1 - β))
```

Per-item proof notes (all with `p₀ = g0 σ μ₀ n ybar > 0` via `g0_pos hσ μ₀ hn`, `p₁ = g1 σ μ₀ l n ybar ≥ 0`):
- `eValue_isValidEValue`: nonnegativity is `g1_nonneg`/`g0_pos` (`E = g1/g0 ≥ 0`). For the
  expectation, the cleanest route is **directly** `nullExp σ μ₀ n (eValue σ μ₀ l n) = ∫ g1 = 1`:
  `gaussianReal μ₀ (v σ n) = volume.withDensity g0` (Mathlib's `gaussianReal` definition), so
  `∫ (g1/g0) ∂(volume.withDensity g0) = ∫ (g1/g0)·g0 ∂volume = ∫ g1 ∂volume`
  (`integral_withDensity_eq_integral_mul` / `…smul`), and `∫ g1 = 1` because `g1` is the uniform
  average over `[μ₀−l, μ₀+l]` of `gaussianPDFReal μ (v σ n)`, each of which integrates to `1`
  (Fubini + `integral_gaussianPDFReal_eq_one`). Then `≤ 1` follows. *(Fallback if this is hard:
  keep `IsValidEValue` with the `ℝ≥0∞` expectation `∫⁻ … ≤ 1` and wrap `evalue_expectation_eq_one`
  directly — note the frame change in the progress file.)*
- `IsValidEValue.test`: `evalue_markov` with `P₀ = gaussianReal μ₀ (v σ n)` and `E = ENNReal.ofReal ∘ e`
  (from `h`: `h.1` measurability, `h.2.1` integrability, `h.2.2.1` nonnegativity, `h.2.2.2` the
  `nullExp ≤ 1` bound — all four are needed to convert the real expectation and apply Markov),
  then `.toReal`.
- `posterior_eq_eValue`: proved by **direct algebra** (`post` unfolds to `(c·g0)/(c·g0+(1−c)·g1)`);
  needs **no** `0 < l` hypothesis. Do not wrap `posterior_eq`.
- `eValue_equiv_posterior`: `evalue_of_posterior` at `c, p₀, p₁`. **Requires `0 < l`**: for `l < 0`
  the mixture density `g1` is negative and the identity fails.
- `no_paradox`: `posterior_ge_iff` with `κ = (1−c)/c > 0` and `e = eValue …`, using
  `posterior_eq_eValue` to rewrite the LHS into `1/(1+κe)`. **Also requires `0 < l`.**

## Honest costs (the only real work)

1. **`ℝ≥0∞ ↔ ℝ` conversions.** `Distribution.prob`, `nullProb`, and `IsValidEValue.test` cross
   between measures/`ℝ≥0∞` and real probabilities via `.toReal`; each needs finiteness of a
   probability measure and `ENNReal.toReal_le_toReal`. Routine but a few lines each.
2. **The e-value expectation** (`eValue_isValidEValue`): either the real-integral route
   `nullExp = ∫ g1 = 1` above, or the `ℝ≥0∞` fallback. This is the one place with a small amount
   of genuine analysis; everything else is a definitional restatement or algebra.

No step should need a `sorry`. If the expectation proves stubborn, ship the rest and leave a
clearly-marked `sorry` **only** in `eValue_isValidEValue`, reporting it explicitly.

## Requirements

- New file only: `Ols/PaperAligned.lean`. Do not modify `BahadurSavage.lean`, `EValue.lean`,
  `Lindley.lean`.
- Build must succeed and be **sorry-free** (`lake build Ols.PaperAligned`).
- Run `#print axioms bahadur_savage`, `#print axioms lindley_paradox`,
  `#print axioms eValue_isValidEValue`, `#print axioms pValue_eq_survival`,
  `#print axioms eValue_equiv_posterior`, `#print axioms no_paradox` and paste the output —
  expect only `propext`, `Classical.choice`, `Quot.sound`.
- Append a short section to `LINDLEY_EVALUE_PROGRESS.md` recording what was proved, any name or
  frame deviations, and the axiom output.
