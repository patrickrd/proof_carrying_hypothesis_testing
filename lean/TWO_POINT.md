# Formalisation task: the exact two-point (Bentkus/Bennett) tail for the bounded-error route

**For the VS Code Claude Code agent.** Self-contained specification, same conventions as
`BOUNDED_ERROR.md`. Work in this repo (`~/linear-model-lean-quantitative`; home-folder clone;
do NOT move it under `~/Documents`). Target file: `Ols/BoundedError.lean` — add a new
`section TwoPoint` after `section Bernstein` (the file's `private` helpers `wsum_neg`,
`two_sided_of_one_sided`, `iIndepFun_weighted`, `integrable_of_bdd` are file-scoped and must be
reused, so extend the file rather than creating a new one). Fill until the file builds with no
errors and no `sorry`, then report.

## What this is, and why it is worth doing

`bernstein_tail` bounds the mgf of each weighted error by the sub-gamma expression
`exp(t²v/(2(1−tM/3)))`. That relaxation is loose: among mean-zero laws with `X ≤ b` and
`E X² ≤ v`, the law that MAXIMISES `E exp(λX)` for every `λ ≥ 0` is the two-point law
supported on `{b, −v/b}`, and its mgf is available in closed form. Replacing the sub-gamma
step by this exact maximum (Bennett's lemma in sharp form; the Chernoff-of-two-point bound
behind Bentkus 2002 and Kuchibhotla–Zheng arXiv:2006.05022 §3.3) tightens the certified
p-values by many orders of magnitude at large signals (on our datasets: Galton slope≠0
1e-12 → 1e-18, Mincer 1e-4 → 1e-10, GISTEMP 1e-9 → 1e-22, Chinchilla 1e-13 → 1e-61), keeps
the e-value form, and — unlike Bernstein — needs no constraint of the form `tM < 3`: the
bound is finite for every `λ ≥ 0`. NOT in scope: the full Bentkus (2002) inequality with the
extra polynomial factor inside the tail; that is a research-level induction. Only the exact
Chernoff of the two-point law is to be formalised.

## The mathematics, in full

Throughout `λ ≥ 0`. For `v ≥ 0 < b` write

    c := v / b,   h := b + c,   G(λ, v, b) := (b/h) * exp(−λc) + (c/h) * exp(λb).

Note `G(λ, 0, b) = 1` and `G(0, v, b) = 1`; both degenerate cases are genuine instances of
the lemma below (no special-casing in the statement; the proof may treat `λ = 0` separately).

### Milestone A — the core lemma `two_point_mgf_le`

For a real random variable `X` on a probability space with
`Measurable X`, `Integrable X P`, `∫ X = 0`, `Integrable (fun ω => (X ω)^2) P`,
`∫ X² ≤ v`, `∀ ω, X ω ≤ b`, `0 < b`, `0 ≤ v`, and `0 ≤ λ`:

    mgf X P λ ≤ G(λ, v, b).

(Only the upper bound `X ≤ b` is used; the two-sided application below supplies `|X| ≤ b`
and applies the lemma to `±X`.)

Proof, fully explicit. If `λ = 0` both sides are `1`. For `λ > 0`:

**A1 (the quadratic majorant).** Define

    C_q := (exp(λb) − exp(−λc) * (1 + λh)) / h²,
    q(x) := exp(−λc) * (1 + λ*(x + c)) + C_q * (x + c)².

Three algebraic identities to verify (`field_simp`/`ring` with `0 < h`):
`q(−c) = exp(−λc)`, `q'(−c) = λ * exp(−λc)` (i.e. `q` is tangent to `exp(λ·)` at `−c`),
and `q(b) = exp(λb)`.

**A2 (nonnegativity of the two curvature quantities).** With `y := λh > 0`:
- `C_q ≥ 0` ⟺ `exp(y) ≥ 1 + y`: `Real.add_one_le_exp`.
- `2*C_q ≥ λ² * exp(−λc)` ⟺ `exp(y) ≥ 1 + y + y²/2`. Mathlib may lack this exact
  inequality; if `exact?` finds nothing, prove it as a `private lemma` by the same
  derivative technique used for `key_ineq` in this file (lines ~137–203: define the gap
  function, compute `HasDerivAt`, conclude by monotonicity from the derivative's sign —
  here two nested applications of `Real.add_one_le_exp`, since
  d/dy (exp y − 1 − y − y²/2) = exp y − 1 − y ≥ 0 and the gap vanishes at 0).

**A3 (pointwise domination): for all `x ≤ b`, `exp(λx) ≤ q(x)`.**
Let `g(x) := q(x) − exp(λx)`. Then `g(−c) = 0`, `g'(−c) = 0`, `g(b) = 0` (from A1), and
`g''(x) = 2*C_q − λ² * exp(λx)`, a strictly decreasing function of `x`. By A2,
`g''(−c) ≥ 0`. Let `x₀ := (1/λ) * Real.log (2*C_q / λ²)` (well defined: `C_q > 0` for
`λ > 0` by the strict form `Real.add_one_lt_exp`), so `g'' ≥ 0` on `(−∞, x₀]` and
`g'' ≤ 0` on `[x₀, ∞)`, and `−c ≤ x₀` (this is exactly A2). Then:
- on `(−∞, −c]`: `g'` is monotone increasing (nonneg. second derivative) with
  `g'(−c) = 0`, hence `g' ≤ 0` there, hence `g` is antitone, hence
  `g(x) ≥ g(−c) = 0`.
- on `[−c, min x₀ b]`: `g'` increasing from `g'(−c) = 0`, hence `g' ≥ 0`, hence `g`
  monotone, hence `g ≥ g(−c) = 0`.
- if `x₀ < b`, on `[x₀, b]`: `g'' ≤ 0`, so `g` is concave there
  (`concaveOn_of_deriv2_nonpos` or the `InnerProductSpace`-free variant — search); a
  concave function on an interval is ≥ the minimum of its endpoint values
  (find the Mathlib form, e.g. via `ConcaveOn` and `min_le`/`le_on_segment`-style lemmas,
  or prove directly from the secant inequality); both endpoint values are ≥ 0
  (`g(x₀) ≥ 0` from the previous bullet, `g(b) = 0`), hence `g ≥ 0`.
Monotonicity from derivative signs: `monotoneOn_of_deriv_nonneg` /
`antitoneOn_of_deriv_nonpos` (`Mathlib/Analysis/Calculus/MeanValue.lean`); differentiability
is `fun_prop`-level (`exp`, polynomials).

**A4 (integrate).** `exp (λ * X ω) ≤ exp (λb)` and `> 0`, so `fun ω => exp (λ * X ω)` is
integrable by `integrable_of_bdd`. `q ∘ X` is integrable (affine + quadratic in `X`, both
integrable by hypothesis). Integrating A3:

    mgf X P λ = ∫ exp (λ X) ≤ ∫ q(X)
             = exp(−λc) * (1 + λ*(∫X + c)) + C_q * (∫X² + 2c∫X + c²)
             ≤ exp(−λc) * (1 + λc) + C_q * (v + c²)          [∫X = 0, ∫X² ≤ v, C_q ≥ 0]

**A5 (closed form).** `v = bc` gives `v + c² = c*h`, and

    exp(−λc)*(1+λc) + C_q*c*h = (b/h)*exp(−λc) + (c/h)*exp(λb) = G(λ, v, b)

— pure algebra (`field_simp; ring` with `0 < h`); expand `C_q` and use
`(1+λc) − (c/h)*(1+λh) = b/h`.

### Milestone B — assembly `two_point_one_tail`, `two_point_tail`

Setting (identical to `bernstein_tail`): `γ B s : Fin n → ℝ`, `ε : Fin n → Ω → ℝ`,
`iIndepFun ε P`, each `ε i` measurable, mean zero, `|ε i ω| ≤ B i`, `∫ ε_i² ≤ (s i)^2`.
Write `b i := |γ i| * B i` and `v i := (γ i * s i)^2`. Add the hypothesis
`hb : ∀ i, 0 < |γ i| * B i` (equivalently `γ i ≠ 0` and `B i > 0`; for the OLS application
the weights are nonzero for any nondegenerate contrast — an optional wrapper dropping
zero-weight coordinates via `Finset.filter` can be added later, and is NOT required).

1. Per `i`: `X_i := fun ω => γ i * ε i ω` has `X_i ≤ b i` and `−X_i ≤ b i`
   (`abs_le`, `abs_mul`), `∫ X_i = 0`, `∫ X_i² = γ i ^ 2 * ∫ ε_i² ≤ v i`, and is bounded
   hence `Integrable` (with its square). Milestone A gives, for `0 ≤ λ`:
   `mgf (X_i) P λ ≤ G(λ, v i, b i)`.
2. Product: exactly as in `mgf_wsum_le`, `(iIndepFun_weighted γ hindep).mgf_sum` gives
   `mgf (wsum γ ε) P λ = ∏ i, mgf (X_i) P λ ≤ ∏ i, G(λ, v i, b i)` (each factor ≥ 0;
   in fact `G ≥ (b/h) * exp(−λc) > 0` — record this as a small lemma `G_pos`, needed
   again in Milestone C).
3. Chernoff at the GIVEN `λ` (no optimisation in Lean — the numeric `λ` is chosen by the
   scripts outside and supplied as an argument): `measure_ge_le_exp_mul_mgf` gives

       theorem two_point_one_tail … (hλ : 0 ≤ λ) (hu : 0 ≤ u) :
         P.real {ω | u ≤ wsum γ ε ω}
           ≤ exp (−λ * u) * ∏ i, G(λ, (γ i * s i)^2, |γ i| * B i)

   (integrability of `exp (λ * wsum)` from `|wsum| ≤ ∑ |γ i| * B i` and
   `integrable_of_bdd`).
4. Two-sided, exactly the `two_sided_of_one_sided` pattern used by `bernstein_tail`:
   apply step 3 to `−γ` (`wsum_neg`; note `G` depends on `γ` only through `|γ i|` and
   `γ i ^ 2`, so the product is unchanged), giving

       theorem two_point_tail … :
         P.real {ω | u ≤ |wsum γ ε ω|}
           ≤ 2 * exp (−λ * u) * ∏ i, G(λ, (γ i * s i)^2, |γ i| * B i).

Define `G` as a plain `def twoPointMgfBound (λ v b : ℝ) : ℝ := …` at the top of the
section so the statements stay readable.

### Milestone C — the e-value form `two_point_evalue`

Define `E_λ(ω) := exp (λ * wsum γ ε ω) / ∏ i, G(λ, v i, b i)`. Theorem: under the
hypotheses of Milestone B and `0 ≤ λ`,

    ∫ ω, E_λ ω ∂P ≤ 1.

Proof: the integral is `mgf (wsum γ ε) P λ / ∏ G` (pull the positive constant out), and
Milestone B step 2 bounds the numerator by the denominator; positivity of the product from
`G_pos`. This is the exact analogue of the e-value remark for Bernstein: for each FIXED
`λ`, `E_λ` is an e-value; combined with `evalue_markov` in `Ols/EValue.lean` it returns
the tail bound. Keep the statement in `wsum` form; a contrast-level corollary mirroring
`bernstein_contrast` (Milestone D, optional) is thin and follows `centredErr_props` +
`contrastDiff_eq_wsum` verbatim.

## Sanity checks to include as `example`s (cheap, catch sign errors early)
- `G(0, v, b) = 1` and `G(λ, 0, b) = 1` (with `0 < b`).
- Two-point law consistency: with `p := v/(b²+v)`, `G(λ,v,b) = p*exp(λb) + (1−p)*exp(−λ*v/b)`
  (`field_simp; ring`); this is the form quoted in the applied documents.
- Monotonicity is NOT needed anywhere; do not chase it.

## Mathlib lemma names to look for (verify each; names drift)
`Real.add_one_le_exp`, `Real.add_one_lt_exp`, `ProbabilityTheory.mgf`,
`iIndepFun.mgf_sum` (already used at line ~294), `measure_ge_le_exp_mul_mgf`
(already used at line ~331), `monotoneOn_of_deriv_nonneg`, `antitoneOn_of_deriv_nonpos`,
`StrictAntiOn`/`strictAntiOn_of_deriv_neg`, `concaveOn_of_deriv2_nonpos` (or
`ConcaveOn` via `AntitoneOn` of `deriv`), `Real.exp_pos`, `Real.exp_le_exp`,
`Real.log_le_iff_le_exp`, `HasDerivAt.exp`, `HasDerivAt.const_mul`, `Integrable.add`,
`Integrable.const_mul`, `integral_add`, `integral_const_mul`. In-file (reuse, do not
duplicate): `wsum`, `wsum_neg`, `two_sided_of_one_sided`, `iIndepFun_weighted`,
`integrable_of_bdd`, and the `key_ineq` block as the template for the `exp y ≥ 1+y+y²/2`
derivative argument. If a needed Mathlib lemma is absent, prove it as a `private lemma`
rather than abandoning the route.

## Build, verify, iterate
- `~/.elan/bin/lake build Ols.BoundedError`; whole project `~/.elan/bin/lake build`.
- Success: builds with no `sorry`/`error`; `#print axioms BoundedError.two_point_tail` and
  `#print axioms BoundedError.two_point_evalue` show only
  `propext, Classical.choice, Quot.sound`; the previously existing theorems
  (`hoeffding_tail`, `bernstein_tail`) still build and their axiom prints are unchanged.

## Working protocol (autonomous) — follow the repo's Autonomy contract in `CLAUDE.md`
- Do NOT ask for permission or direction; keep going until success.
- Commit locally after each lemma builds (message naming the lemma). **NEVER `git push`.**
- Milestone A is the substantive part; B and C are assembly. If a piece is blocked after
  several genuine attempts, leave a clearly-commented `sorry`, record what you tried in
  `TWO_POINT_PROGRESS.md`, and move to the next independent piece.
- Record progress (what builds, what is sorried and why, `#print axioms`) in
  `TWO_POINT_PROGRESS.md`. When A–C build sorry-free, stop and summarise there.
