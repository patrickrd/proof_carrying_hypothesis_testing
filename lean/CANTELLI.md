# Formalisation task: misspecification-free variance-event bound (Cantelli route)

**For the VS Code Claude Code agent.** Self-contained specification, same conventions as
`BOUNDED_ERROR.md` and `TWO_POINT.md`. Work in this repo (`~/linear-model-lean-quantitative`;
home-folder clone; do NOT move it under `~/Documents`; do NOT `git push`). Target file:
`Ols/FiniteN.lean` — add a new `section Cantelli` after `section MainTheorems` (the
definitions `hcVar`, `contrastVar`, `hcRho`, `hcM`, `hcU`, `hcWeight`, `olsWeights`,
`maxLev`, `leverage`, and the lemmas named below must be REUSED, so extend the file rather
than creating a new one; raise `set_option linter.style.longFile` as needed). Fill until the
file builds with no errors and no new `sorry`, then report and write `CANTELLI_PROGRESS.md`.

## What this is, and why it is worth doing

The existing `FiniteSampleBundle.variance_event_le` (Lemma 6) bounds the variance event
`P(ν̂ ≤ θν)` by Chebyshev, with three defects the new derivation removes:

1. it needs a declared misspecification tolerance `C_r` with `|rᵢ| ≤ C_r` (bundle field
   `hres`), because the mean-model error `r` enters the variance bound `V₊`;
2. it needs the leverage condition `θ < 1 − 2·maxLev X`, an artefact of the linearisation
   `(1 − hᵢ)² ≥ 1 − 2hᵢ`, which voids the method entirely on high-leverage designs
   (our SH0ES dataset has `h_max = 0.526`);
3. it uses two-sided Chebyshev where the event is one-sided.

The new bound fixes all three. The model error `r` enters the exact mean and variance of
`ν̂` only through the single scalar `ρ² = hcRho ≥ 0`, and in opposite directions: the
variance bound grows like `ρ²`, the squared mean-gap like `ρ⁴`. Taking the worst case over
`ρ ≥ 0` therefore yields a bound free of `r` — no tolerance, no `hres`. The leverage
condition is replaced by the weaker requirement `aMinus θ > 0` (defined below), which for
the HC3 multipliers holds for EVERY `θ ∈ (0,1)` whatever the leverages. Cantelli's
inequality (one-sided Chebyshev) replaces Chebyshev. Numerically (R implementation
`cantelli_bounds.R`, output `cantelli_results.csv`, in the report repo) the resulting
p-value bound improves on the old one on every one of 17 dataset rows, typically by ~2×,
and produces a finite answer on SH0ES where the old bound returns nothing.

Only the ANALYTIC form is to be formalised: the term-by-term maximisation over `ρ`
(a closed-form `q̄`), not the one-dimensional numerical supremum. The analytic form
overstates the supremum by at most a factor of three and costs 8–15% in the final
p-value on our datasets.

## Notation dictionary (paper → Lean)

| paper | Lean |
|---|---|
| `D²` (= `ν̂`) | `hcVar X d y a` |
| `ν = Var(T_raw) = ∑γᵢ²σᵢ²` | `contrastVar P X y a` |
| `γᵢ` | `olsWeights X a i` |
| `wᵢ = γᵢ²dᵢ` | `hcWeight X d a i` |
| `Q = (I−H)·diag(w)·(I−H)` | `hcM X d a` |
| `u = (I−H)·diag(w)·r` | `hcU P X y d a` |
| `ρ² = ∑ᵢwᵢrᵢ²` | `hcRho P X y d a` |
| `hᵢ` | `leverage X i` |
| `σᵢ² = Var(yᵢ)` | `centralMoment (y i) 2 P` |
| `E|εᵢ|³ ≤ B₃` | bundle field `h3` |
| `Eεᵢ⁴ ≤ κσᵢ⁴` | bundle field `h4` |

The bundle fields `C_r` and `hres` are NOT used anywhere in this task; every new statement
must be provable for a bundle whose `C_r` is arbitrary.

## New definitions

Add, in `section Cantelli` (same `variable` conventions as `MainTheorems`):

    /-- `c_j(θ) = Q_jj − θγ_j²`. -/
    def cantelliC (X : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ) (a : Fin p → ℝ)
        (θ : ℝ) (j : Fin n) : ℝ :=
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
            / aMinus X d a s_min s_max θ ^ (3/2 : ℝ)

    /-- The variance-event bound `q̄/(1 + q̄)`. -/
    def cantelliVarianceEventBound (…same args…) : ℝ :=
      cantelliQBar … / (1 + cantelliQBar …)

Design choice: `g` (paper `g_max = maxᵢ γᵢ²dᵢ`) is a PARAMETER with hypothesis
`hg : ∀ i, hcWeight X d a i ≤ g`, not a `Finset.sup'` — this avoids nonemptiness plumbing,
and every statement is monotone in `g`. Callers instantiate `g` with the max.

## The mathematics, in full

Throughout: bundle `A : FiniteSampleBundle P X y`, `hd : ∀ i, 1 ≤ d i`, `ha : a ≠ 0`,
`hθ0 : 0 < θ`, `hA : 0 < aMinus X d a A.s_min A.s_max θ`, `hg : ∀ i, hcWeight X d a i ≤ g`.
No leverage hypothesis; no `hres`; `θ ≤ 1` is NOT needed anywhere.

### Milestone A — Cantelli's inequality (generic)

    lemma measureReal_le_cantelli {W : Ω → ℝ} (hW : MemLp W 2 P) {m c V : ℝ}
        (hm : m ≤ P[W]) (hV : Var[W; P] ≤ V) (hc : c < m) :
        P.real {ω | W ω ≤ c} ≤ V / (V + (m - c) ^ 2)

Mathlib may already contain Cantelli (search: `cantelli`, `meas_le_sub`,
one-sided Chebyshev); if so, wrap it. Otherwise prove it next to
`measureReal_le_of_variance_le`, whose proof is the template. Fully explicit proof:

**A1.** Reduce to `V' := Var[W; P]`: it suffices to prove the bound with `V'` in place of
`V`, because `x ↦ x/(x + s²)` is nondecreasing for `x ≥ 0` when `s² > 0` (prove inline:
cross-multiply, `nlinarith`), and `(m−c)² > 0`.

**A2.** If `V' = 0`: Chebyshev already gives
`P(W ≤ c) ≤ P(|W − E W| ≥ m − c) ≤ V'/(m−c)² = 0`, and `0 = V'/(V' + (m−c)²)`; reuse the
`measureReal_le_of_variance_le` chain.

**A3.** If `V' > 0`: set `b := V'/(m−c) > 0` and `Y ω := b + P[W] − W ω`, so `E Y = b`,
`E Y² = b² + V'`. On `{W ≤ c}` one has `Y ≥ b + (m − c) > 0`, hence `Y² ≥ (b + (m−c))²`,
hence

    {ω | W ω ≤ c} ⊆ {ω | (b + (m-c))^2 ≤ (Y ω)^2}.

Markov for the nonnegative function `Y²` (Mathlib: the same lemma that powers
`meas_ge_le_variance_div_sq`; search `mul_meas_ge_le_integral`, `measure_ge_le_integral`,
or apply `meas_ge_le_variance_div_sq` to a shifted variable — note `Var Y = Var W`) gives

    P.real {…} ≤ (b² + V') / (b + (m−c))².

**A4.** Algebra: with `b = V'/(m−c)`,
`(b² + V')/(b + (m−c))² = V'/(V' + (m−c)²)` (clear denominators, `field_simp; ring`).

### Milestone B — the mean gap: `E ν̂ − θν ≥ ρ² + a₋(θ)`

    lemma integral_hcVar_sub_ge (A : FiniteSampleBundle P X y) (hd : ∀ i, 1 ≤ d i)
        {θ : ℝ} :
        hcRho P X y d a + aMinus X d a A.s_min A.s_max θ
          ≤ ∫ ω, hcVar X d y a ω ∂P - θ * contrastVar P X y a

Proof. `FiniteSampleBundle.integral_hcVar` (already in the file) gives the EXACT mean
`E ν̂ = ρ² + ∑ⱼ Qⱼⱼσⱼ²`, and `contrastVar = ∑ⱼ γⱼ²σⱼ²` by definition, so

    E ν̂ − θν − ρ² = ∑ⱼ (Qⱼⱼ − θγⱼ²)·σⱼ² = ∑ⱼ cantelliC θ j · σⱼ².

Bound the sum term by term (`Finset.sum_le_sum`): if `c_j ≥ 0`, then
`c_j·σⱼ² ≥ c_j·s_min²` by `A.hvar_lb`; if `c_j < 0`, then `c_j·σⱼ² ≥ c_j·s_max²` by
`A.hvar_ub` (multiplying an inequality by a negative number reverses it). The right-hand
sides are exactly the summands of `aMinus`.

### Milestone C — the `r`-dependence of `‖u‖`: `‖u‖² ≤ g·ρ²`

    lemma normSq_hcU_le_gmax (hd : ∀ i, 1 ≤ d i) (hg : ∀ i, hcWeight X d a i ≤ g) :
        normSq (hcU P X y d a) ≤ g * hcRho P X y d a

Proof. Mirror the existing `normSq_hcU_le` (which proves `‖u‖² ≤ C_r²·∑dᵢ²γᵢ⁴`): it
already contains the contraction step `‖(I−H)v‖² ≤ ‖v‖²` for `v = diag(w)·r`; reuse that
step verbatim, then instead of bounding `rᵢ²` by `C_r²` bound one factor of the weight:

    ‖diag(w)·r‖² = ∑ᵢ wᵢ²rᵢ² ≤ g·∑ᵢ wᵢrᵢ² = g·hcRho,

using `wᵢ ≥ 0` (`hcWeight_nonneg hd`) and `wᵢ ≤ g`. Corollary (via `Real.sqrt` algebra):
`‖u‖ ≤ √g·√ρ²`, i.e. `√(normSq (hcU …)) ≤ √g * √(hcRho …)`.

### Milestone D — the variance bound with explicit `ρ`

    lemma variance_hcVar_le_cantelli (A : FiniteSampleBundle P X y)
        (hd : ∀ i, 1 ≤ d i) (hκ : 1 ≤ A.κ) (hg : ∀ i, hcWeight X d a i ≤ g) :
        Var[hcVar X d y a; P]
          ≤ cantelliV0 X d a A.s_max A.κ
            + 4 * A.s_max ^ 2 * g * hcRho P X y d a
            + 4 * A.B₃ * cantelliS X d a * √g * √(hcRho P X y d a)

Proof. Mirror `variance_hcVar_le`: the exact variance `FiniteSampleBundle.variance_hcVar`
has three parts (quadratic, linear, covariance). The quadratic part is bounded by
`cantelliV0` exactly as it is bounded by the first two terms of `hcVplus` today (same
steps, `A.h4`, `A.hvar_ub`, `hκ`). The linear part is `4·∑ᵢuᵢ²σᵢ² ≤ 4·s_max²·‖u‖²
≤ 4·s_max²·g·ρ²` by Milestone C. The covariance part is bounded, as today, by
`4·∑ᵢ Qᵢᵢ·|uᵢ|·B₃` and then Cauchy–Schwarz `∑ᵢQᵢᵢ|uᵢ| ≤ S·‖u‖` — this is the existing
lemma `sum_hcM_abs_hcU_le`; finish with `‖u‖ ≤ √g·√ρ²` (Milestone C corollary).
(`√(hcRho) ≥ 0` and `hcRho ≥ 0` come from `hcRho_nonneg hd`.)

### Milestone E — three elementary real inequalities (the per-term maxima over `ρ`)

Private lemmas, pure real arithmetic; `x` plays `ρ²`, `am` plays `a₋(θ)`.
For all `x ≥ 0`, `am > 0`:

    e1 : V0 ≥ 0 → V0 / (x + am)^2 ≤ V0 / am^2
    e2 : 4 * x ≤ (x + am)^2 / am                    -- i.e. 4x/(x+am)² ≤ 1/am
    e3 : 16 * √x * am^(3/2:ℝ) ≤ 3 * √3 * (x + am)^2 -- i.e. √x/(x+am)² ≤ (3√3/16)/am^{3/2}

`e1`: `(x+am)² ≥ am²`, `div_le_div_of_nonneg_left`. `e2`: `(x − am)² ≥ 0`, `nlinarith`.
`e3`: substitute `s := √x ≥ 0` and `b := √(am/3) > 0` (so `x = s²`, `am = 3b²`,
`am^{3/2} = 3√3·b³`); the claim becomes `16·s·b³ ≤ (s² + 3b²)²`, which holds because

    (s² + 3b²)² − 16sb³ = (s − b)² · (s² + 2sb + 9b²) ≥ 0

(verify the factorisation by `ring_nf`; nonnegativity of the second factor from `s,b ≥ 0`;
finish by `nlinarith [sq_nonneg (s - b), sq_nonneg (s + b), mul_pos, …]` with the product
as a hint). Handle the `Real.rpow`/`Real.sqrt` conversions (`am^(3/2:ℝ) = am·√am`,
`√(s²) = s` for `s ≥ 0`) before the algebra.

### Milestone F — the variance-event bound

    theorem cantelli_variance_event_le (A : FiniteSampleBundle P X y)
        (hd : ∀ i, 1 ≤ d i) (ha : a ≠ 0) {θ g : ℝ} (hθ0 : 0 < θ)
        (hg : ∀ i, hcWeight X d a i ≤ g)
        (hA : 0 < aMinus X d a A.s_min A.s_max θ) :
        P.real {ω | hcVar X d y a ω ≤ θ * contrastVar P X y a}
          ≤ cantelliVarianceEventBound X d a A.s_min A.s_max A.B₃ A.κ g θ

Proof skeleton (this is the whole point — the misspecification disappears here). Write
`ρ² := hcRho ≥ 0`, `am := aMinus > 0`, `q̄ := cantelliQBar`, `m := E ν̂`, `c := θν`,
`gap := m − c`.

**F1.** `gap ≥ ρ² + am > 0` (Milestone B; `hA`, `hcRho_nonneg`). In particular `c < m`.

**F2.** `Var ν̂ ≤ q̄·(ρ² + am)²`. Expand `q̄·(ρ² + am)²` into three products and compare
with the three terms of Milestone D term by term, using Milestone E with `x := ρ²`:

    cantelliV0 ≤ (V0/am²)·(ρ² + am)²                     -- e1, rearranged
    4·s_max²·g·ρ² ≤ (s_max²·g/am)·(ρ² + am)²             -- e2
    4·B₃·S·√g·√ρ² ≤ ((3√3/4)·B₃·S·√g/am^{3/2})·(ρ² + am)² -- e3

(each of `V0`, `s_max²g`, `B₃S√g` is nonnegative: `cantelliV0` needs `hκ := A.one_le_κ`
— note `one_le_κ` needs `0 < n`, available from `pos_of_contrastVar_pos
(A.contrastVar_pos ha)` — and squares/`Real.sqrt_nonneg` elsewhere).

**F3.** `Var ν̂ ≤ q̄·gap²`: from F2 and `(ρ² + am)² ≤ gap²` (F1, both sides ≥ 0).

**F4.** Apply Milestone A with `V := q̄·gap²`:

    P(ν̂ ≤ θν) ≤ q̄·gap² / (q̄·gap² + gap²) = q̄/(1 + q̄),

the last step cancelling `gap² > 0` (`field_simp`; `q̄ ≥ 0` from F2 side conditions or
directly from its three nonnegative terms; `1 + q̄ > 0`).

`MemLp (hcVar …) 2 P` is the existing `A.memLp_two_hcVar`.

### Milestone G — the tail theorems

    theorem finiteN_tail_oneSided_cantelli (A : FiniteSampleBundle P X y)
        (hd : ∀ i, 1 ≤ d i) (ha : a ≠ 0) {η : ℝ → ℝ}
        (hη : ∀ z, |cdf (P.map (contrastStat P X y a)) z - cdf (gaussianReal 0 1) z| ≤ η z)
        {t θ g : ℝ} (ht : 0 < t) (hθ0 : 0 < θ)
        (hg : ∀ i, hcWeight X d a i ≤ g)
        (hA : 0 < aMinus X d a A.s_min A.s_max θ) :
        P.real {ω | t < hcStudent P X y d a ω} ≤
          (1 - cdf (gaussianReal 0 1) (t * √θ)) + η (t * √θ)
            + cantelliVarianceEventBound X d a A.s_min A.s_max A.B₃ A.κ g θ

Proof: exactly the proof of `finiteN_tail_oneSided` with two changes: the split
`studentised_tail_le` and the numerator step `tail_upper_of_cdf … (t * √θ)` are reused
verbatim; Milestone F replaces `variance_event_le`; and there is NO `gaussian_tail_shift`
step — the Gaussian term stays at `t√θ` (this is both simpler and tighter than the old
`(1 − Φ(t)) + shift` packaging). Note the old hypotheses `hθ1 : θ ≤ 1` and
`hθh : θ < 1 − 2·maxLev X` are GONE; that is the point.

Also provide, mirroring the existing file structure:
`finiteN_tail_lower_cantelli` (lower tail, same statement for `−t`) and
`finiteN_tail_twoSided_cantelli`:

    P(t < |T|) ≤ 2(1 − Φ(t√θ)) + 2η(t√θ) + cantelliVarianceEventBound …

(the variance event is counted ONCE — both one-sided splits land on the same event
`{ν̂ ≤ θν}`; follow how `finiteN_tail_twoSided` assembles its two halves).

### Milestone H — HC3 needs no condition at all

    lemma aMinus_pos_hc3 (A : FiniteSampleBundle P X y) (ha : a ≠ 0)
        (hlev : ∀ j, leverage X j < 1) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
        (hd3 : ∀ j, d j = (1 - leverage X j)⁻¹ ^ 2) :
        0 < aMinus X d a A.s_min A.s_max θ

Proof. First `cantelliC θ j ≥ (1 − θ)·γⱼ² ≥ 0` for every `j`: inside the existing proof
of `integral_hcVar_ge` is the step `hcWeight X d a j * (1 − leverage X j)² ≤ hcM X d a j j`
(keeping only the `i = j` term of the Gram sum) — extract it as a standalone lemma
`hcWeight_mul_sq_le_hcM_diag` if it is not one already. With `hd3`,
`wⱼ(1−hⱼ)² = γⱼ²·dⱼ·(1−hⱼ)² = γⱼ²` (needs `1 − hⱼ ≠ 0` from `hlev`), so
`Qⱼⱼ ≥ γⱼ²` and `cⱼ = Qⱼⱼ − θγⱼ² ≥ (1−θ)γⱼ² ≥ 0`. Hence every `if` in `aMinus` takes the
`s_min²` branch and

    aMinus ≥ (1−θ)·s_min²·∑ⱼγⱼ² = (1−θ)·s_min²·normSq (olsWeights X a) > 0

by `A.hs_min_pos`, `hθ1`, and `normSq_olsWeights_pos X A.hX_inv a (Ne.symm ha)`.
(Also `1 ≤ d j` holds for HC3 — worth a two-line lemma `one_le_hc3` from `0 < 1 − hⱼ ≤ 1`,
using `0 ≤ leverage X j`, which should exist or follow from `hcM_diag_nonneg`-style
arguments.)

## Sanity checks (numeric, to include as `example`s where `norm_num` can close them)

Intercept-only design, `n = 4`, `X = !![1;1;1;1]` (4×1), `a = ![1]`, HC0 (`d = 1`),
`θ = 1/2`, `s_min = s_max = 1`, `κ = 3`: then `γᵢ = 1/4`, `hᵢ = 1/4`, `Qᵢᵢ = 3/64`,
`Qᵢⱼ = −1/64 (i≠j)`, and one can check by `norm_num` (if stated over `ℚ`-valued rationals
or with explicit `Finset` sums):

    cantelliC _ _ _ (1/2) j = 1/64,  aMinus = 1/16,  cantelliV0 = 3/128,
    first term of q̄ = 6,  second term (with g = 1/16) = 1.

(The third term involves `√3` and `B₃`; skip it in the `example`.) Cross-validation
against R (`cantelli_results.csv` in the report repo): with `B₃ = √(8/π)` (i.e.
`b₃s_max³` in the paper's scale-free form), Galton slope≠0 HC0 gives analytic p ≈ 0.0427,
cars ≈ 0.455, SH0ES ≈ 0.539 — the R script is the ground truth these definitions must
match; if a formalised definition disagrees with `cantelli_bounds.R`, STOP and report
rather than adapting the definition.

## Scope and non-goals

- Do NOT modify or delete the existing Chebyshev route (`hcVplus`,
  `variance_event_le`, `finiteN_tail_oneSided` and its corollaries); the new section is
  additive, and the paper cites both.
- NOT in scope: the numerical `sup_ρ` version; mixture e-values; any change to
  `FiniteSampleBundle` (in particular do not remove `C_r`/`hres` — just leave them unused
  by the new theorems).
- The Berry–Esseen input `η` remains an input, exactly as in the existing theorems.
- Axioms check at the end: `#print axioms finiteN_tail_twoSided_cantelli` should report
  `[propext, Classical.choice, Quot.sound]` only (plus whatever the `BE30` placeholder
  drags in ONLY if you also instantiate an `_BE30` variant, which is optional).
