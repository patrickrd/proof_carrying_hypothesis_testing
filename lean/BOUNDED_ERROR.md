# Formalisation task: the bounded-error route (Hoeffding + Bernstein p-value bounds)

**For the VS Code Claude Code agent.** Self-contained specification. Work in this repo
(`~/linear-model-lean-quantitative`, a home-folder clone that builds cleanly — do NOT move it
under `~/Documents`, which is iCloud-synced and corrupts `.lake`). Target file:
`Ols/BoundedError.lean` (a skeleton with `sorry`s exists). Fill the `sorry`s so the file builds
with no errors and no `sorry`, then report.

## What this is, and why it is worth doing

Under the null `a^\top β^\star = 0`, the contrast numerator equals the weighted error sum
`N = ∑ i, γ_i ε_i` **exactly** — the mean-residual `r` drops out because `X^\top r = 0`, so the
result is misspecification-robust with no extra work. If the analyst *declares* a known error
bound `|ε_i| ≤ B_i` (and, for the sharper version, a known variance bound `Var(ε_i) ≤ s_i^2`),
elementary concentration certifies a p-value for `N` with no variance estimation, no
Berry–Esseen, and no symmetry. Unlike the other two routes in this project (which need a
Berry–Esseen placeholder `sorry`, or an unformalised Hanson–Wright inequality), this route can
be proved outright. Milestone A is essentially assembly from Mathlib; Milestone B needs one
classical lemma (Bennett) that Mathlib lacks.

## Milestone A — Hoeffding (`hoeffding_tail`); do this first

Target (see skeleton for the exact signature):

    P.real {ω | u ≤ |wsum γ ε ω|} ≤ 2 * exp (-u^2 / (2 * ∑ i, (γ i * B i)^2))

under: `iIndepFun ε P`, each `ε_i` measurable and mean zero, `|ε_i ω| ≤ B_i`, `0 ≤ u`.

Mathlib gives this almost for free. Key results, all in
`Mathlib/Probability/Moments/SubGaussian.lean`, namespace `ProbabilityTheory`:
- `HasSubgaussianMGF (X) (c) (μ)` — the measure-level sub-Gaussian structure (proxy `c : ℝ≥0`).
- `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` — **Hoeffding's lemma**: a mean-zero `X`
  with values in `Icc a b` is sub-Gaussian with proxy `(b - a)^2 / 4`. (Find its exact name and
  signature with `exact?`/`#check`; there is a measure-level version and a kernel version — use
  the measure one, or convert via `HasSubgaussianMGF_iff_kernel`.)
- `measure_sum_ge_le_of_iIndepFun (h_indep) (h_subG : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ)
  (hε : 0 ≤ ε) : μ.real {ω | ε ≤ ∑ i ∈ s, X i ω} ≤ exp (-ε^2 / (2 * ∑ i ∈ s, c i))` — Hoeffding
  for sums (one-sided).
- `HasSubgaussianMGF.neg`, `HasSubgaussianMGF.measure_ge_le` — for the other tail.

Proof steps:
1. Set `Z i := fun ω => γ i * ε i ω`. Then `Z i ω ∈ Icc (-(|γ i| * B i)) (|γ i| * B i)` (from
   `|ε_i| ≤ B_i`) and `∫ Z i = γ i * ∫ ε i = 0`. So `HasSubgaussianMGF (Z i) (c i) P` with
   `c i = (2 * |γ i| * B i)^2 / 4 = (γ i * B i)^2` (in `ℝ≥0`; note `(γ i * B i)^2 = (|γ i| B i)^2`).
   Get this from Hoeffding's lemma. Watch the `ℝ≥0` coercion: the proxy is a `NNReal`, and
   `∑ i, c i` must match the real `∑ i, (γ i * B i)^2` after coercion (`NNReal.coe_sum`, and
   `(γ i * B i)^2 ≥ 0`).
2. `iIndepFun Z P` from `hindep` composed with `fun x => γ i * x` (`iIndepFun.comp` with
   `measurable_const_mul`; each `fun_prop`).
3. One tail: `measure_sum_ge_le_of_iIndepFun` on `s = Finset.univ` gives
   `P.real {ω | u ≤ ∑ i, Z i ω} ≤ exp (-u^2 / (2 * ∑ i, (γ i B i)^2))`.
   `∑ i, Z i ω = wsum γ ε ω` by `wsum` unfolding.
4. Other tail: apply the same to `-Z i` (each is sub-Gaussian by `neg`, same proxy), giving
   `P.real {ω | u ≤ -(wsum γ ε ω)} ≤ (same)`.
5. Two-sided: `{ω | u ≤ |wsum γ ε ω|} ⊆ {ω | u ≤ wsum γ ε ω} ∪ {ω | u ≤ -(wsum γ ε ω)}`
   (from `le_abs`), then `measureReal_union_le` (or `measure_union_le` + `toReal`), and add the
   two bounds to get the factor `2`.

Estimate: 150–300 lines, mostly coercion and set-algebra plumbing; no hard mathematics.

## Milestone B — Bernstein (`bennett_mgf_le` then `bernstein_tail`)

Mathlib has no Bernstein/Bennett/sub-exponential machinery (checked), so prove the one MGF
lemma, then assemble.

### B1. `bennett_mgf_le`: for `|Z| ≤ M`, `∫ Z = 0`, `∫ Z^2 ≤ v`, `0 ≤ t`, `t M < 3`:
`mgf Z P t ≤ exp (t^2 v / (2 (1 - t M / 3)))`.

Proof outline:
- Pointwise: for `|x| ≤ M` and `t ≥ 0`, `exp (t x) ≤ 1 + t x + (t x)^2 · φ(t M)` is not the
  cleanest; instead use the standard bound `exp y - 1 - y ≤ (y^2 / 2) · ∑_{k≥0} (tM)^k/... `.
  The clean route: `exp (t x) ≤ 1 + t x + x^2 · (exp (t M) - 1 - t M) / M^2` for `|x| ≤ M`
  (Bennett's pointwise inequality; the function `x ↦ (exp(tx) - 1 - tx)/x^2` is increasing, so
  maximised at `x = M`). Prove this pointwise inequality (a one-variable calculus/convexity fact;
  may need a short `Mathlib` search for `Real.add_one_le_exp`, `Real.exp` monotonicity, or a
  direct series argument via `Real.exp_eq_exp_ℝ`/`NormedSpace.exp` series bounds).
- Integrate: `mgf Z P t = ∫ exp (t Z) ≤ ∫ (1 + t Z + Z^2 (exp(tM)-1-tM)/M^2)
   = 1 + t·0 + (∫ Z^2)(exp(tM)-1-tM)/M^2 ≤ 1 + v (exp(tM)-1-tM)/M^2 ≤ exp (v(exp(tM)-1-tM)/M^2)`
  (last step `1 + y ≤ exp y`). Integrability of `exp (t Z)` is immediate from boundedness.
- Reduce `exp(tM) - 1 - tM ≤ (tM)^2 / (2 (1 - tM/3))` for `0 ≤ tM < 3` (standard sub-gamma
  bound; prove from the series `∑_{k≥2} (tM)^k/k! ≤ (tM)^2/2 · ∑_{k≥0} (tM/3)^k`, using
  `k! ≥ 2 · 3^{k-2}`). Then `v(exp(tM)-1-tM)/M^2 ≤ t^2 v / (2(1 - tM/3))`, giving the claim.

Estimate: 250–450 lines. This is the substantive part. It is classical and self-contained;
there is no research gap. If the pointwise Bennett inequality is hard to find/prove cleanly,
an acceptable fallback is the weaker sub-Gaussian-with-variance bound `mgf ≤ exp(t^2 v /
(2(1 - tM/3)))` via the same series with looser constants — keep the sub-gamma shape.

### B2. `bernstein_tail`: assemble.
1. `Z i := fun ω => γ i * ε i ω`; `|Z i ω| ≤ |γ i| B i ≤ M`; `∫ Z i = 0`;
   `∫ (Z i)^2 = γ i^2 ∫ ε_i^2 ≤ (γ i s i)^2`.
2. `bennett_mgf_le` per `i` with `M` (the common bound) gives, for `0 ≤ t`, `t M < 3`,
   `mgf (Z i) P t ≤ exp (t^2 (γ i s i)^2 / (2 (1 - t M / 3)))` (use `|γ i| B i ≤ M` and
   monotonicity to replace the per-`i` scale by the common `M`).
3. Independence → the MGF of the sum factorises: `mgf (wsum γ ε) P t = ∏ i, mgf (Z i) P t`
   (`mgf` of a sum of independent variables; find the Mathlib lemma, e.g. via `iIndepFun` and
   `mgf_sum`/`indepFun`-MGF product — search `mgf` + `iIndepFun`). Hence
   `mgf (wsum γ ε) P t ≤ exp (t^2 (∑ i (γ i s i)^2) / (2 (1 - t M / 3)))`.
4. Chernoff: `measure_ge_le_exp_mul_mgf` (in `Mathlib/Probability/Moments/Basic.lean`) gives
   `P.real {u ≤ wsum} ≤ exp (-t u) · mgf (wsum) P t`. Plug the specific
   `t = u / (∑ i (γ i s i)^2 + M u / 3)` (check `0 ≤ t` and `t M < 3`), and simplify the
   exponent to `-u^2 / (2 (∑ i (γ i s i)^2 + M u / 3))` by algebra (this is the standard
   Bernstein optimiser; verify the identity rather than doing a calculus `inf`).
5. Two-sided via `-Z`, exactly as in Milestone A step 5.

## Milestone C (optional; only after A and B build sorry-free)
Connect `wsum` to the OLS contrast. In `Ols/FiniteN.lean` (or `Ols/TTest.lean`) the numerator
`a^\top(β̂ − β^\star) = ∑ i, olsWeights X a i · (Y i − μ i)` under the null (the exact,
misspecification-robust identity). State a corollary: with `γ i = olsWeights X a i` and
`ε i = Y i − μ i`, `hoeffding_tail`/`bernstein_tail` bound `P(|a^\top(β̂ − β^\star)| ≥ u)`, i.e.
give a certified p-value for the regression coefficient. Import `Ols.FiniteN`; reuse its
`olsWeights` and whichever lemma states the identity (search for the projection identity /
`contrastStat`). Keep this thin.

## Mathlib lemma names to look for (verify each; names drift)
`ProbabilityTheory.HasSubgaussianMGF`, `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`,
`measure_sum_ge_le_of_iIndepFun`, `HasSubgaussianMGF.neg`, `HasSubgaussianMGF.measure_ge_le`,
`HasSubgaussianMGF_iff_kernel`, `iIndepFun.comp`, `measurable_const_mul`, `NNReal.coe_sum`,
`measureReal_union_le`, `le_abs`, `Real.add_one_le_exp`, `mgf`, `mgf_sum` / MGF of independent
sums, `measure_ge_le_exp_mul_mgf` (Chernoff, `Probability/Moments/Basic.lean`),
`integrable_of_bounded`/`MemLp` for `exp (t Z)`. Use `exact?`, `apply?`, `#check`,
`open ... in example` to pin exact names; if a needed lemma is absent, prove it as a
`private lemma` rather than abandoning the route.

## Build, verify, iterate
- Use `~/.elan/bin/lake` (per the repo CLAUDE.md), not bare `lake`.
- Iterate: `~/.elan/bin/lake build Ols.BoundedError`. Whole project: `~/.elan/bin/lake build`
  (a few minutes; the Mathlib cache is present — do not run `lake exe cache get` unless a build
  reports missing `.olean`s).
- Add `import Ols.BoundedError` to `Ols.lean` so it is in the default build.
- Success: `~/.elan/bin/lake build Ols.BoundedError` exits 0 with no `sorry`/`error`; then a full
  `~/.elan/bin/lake build` still passes; then `#print axioms BoundedError.hoeffding_tail` and
  `#print axioms BoundedError.bernstein_tail` show only `propext, Classical.choice, Quot.sound`
  (no `sorryAx`). Respect the `lakefile.toml` linters.

## Working protocol (autonomous) — follow the repo's Autonomy contract in `CLAUDE.md`
- Do NOT ask for permission or direction; all needed actions are pre-approved in
  `.claude/settings.local.json`. Keep going until success.
- Commit locally after each lemma builds (`git add -A && git commit`, message naming the lemma).
- **NEVER `git push`** — the one hard rule.
- If a piece is blocked after several genuine attempts, leave it as a clearly-commented `sorry`,
  record what you tried in `BOUNDED_ERROR_PROGRESS.md`, and move on to the next independent piece.
  Milestone A does not depend on B; do A fully first so there is always a complete result.
- Record progress (what builds, what is sorried and why, `#print axioms`) in
  `BOUNDED_ERROR_PROGRESS.md`. When A and B build sorry-free, stop and summarise there.
