# TWO_POINT_PROGRESS — `section TwoPoint` in `Ols/BoundedError.lean`

Date: 2026-09-16. Status: **Milestones A, B, C complete, sorry-free.** Existing theorems
(`hoeffding_tail`, `bernstein_tail`) untouched; their axiom prints are unchanged.

## Definitions
- `twoPointMgfBound lam v b := (b/h)·e^{−λc} + (c/h)·e^{λb}`, `c = v/b`, `h = b + c` (the
  spec's `G`). Sanity `example`s: `G(0,v,b) = 1`, `G(λ,0,b) = 1`, and the two-point form
  `p·e^{λb} + (1−p)·e^{−λv/b}`, `p = v/(b²+v)`. `twoPointMgfBound_pos`: `G > 0`.

## Milestone A — `two_point_mgf_le` (done)
Route differs from the spec's A3 (no concavity step, no `x₀`, no second derivative of the gap).
With `u = x + c` and `D = (e^{λh} − 1 − λh)/h²`, the majorant is `e^{−λc}(1 + λu + D u²)` and
the pointwise bound `exp(λu) ≤ 1 + λu + D u²` for `u ≤ h` (`exp_le_quadratic_majorant`) is
proved from two elementary facts:
- `antitone_quadGap`: `y ↦ 1 + y + y²/2 − eʸ` is antitone (`antitone_of_deriv_nonpos`,
  derivative `1 + y − eʸ ≤ 0` by `Real.add_one_le_exp`). This gives both
  `eʸ ≤ 1 + y + y²/2` for `y ≤ 0` (used for `u ≤ 0`) and `1 + y + y²/2 ≤ eʸ` for `y ≥ 0`
  (the spec's A2, i.e. `λ²/2 ≤ D`).
- `psi_monotoneOn`: `ψ(y) = (eʸ − 1 − y)/y²` is monotone on `(0,∞)`; its derivative has
  numerator `y·N(y)` with `N(y) = (y−2)eʸ + y + 2 ≥ 0` for `y ≥ 0` (`nAux_nonneg`, two
  `monotoneOn_of_deriv_nonneg` passes since `N'' = y eʸ`). For `0 < u ≤ h` this gives
  `ψ(λu) ≤ ψ(λh)`, i.e. the majorant.
Integration (`integral_mono`, `integral_add`, `integral_const_mul`, `integrable_of_bdd`) and
the closed form `e^{−λc}(1 + λc + D(v + c²)) = G` (`field_simp; ring` with
`e^{λb} = e^{λh}e^{−λc}`). `λ = 0` is handled inside the pointwise lemma only.

## Milestone B — `mgf_wsum_le_twoPoint`, `two_point_one_tail`, `two_point_tail` (done)
Per-coordinate application with `X_i = γᵢεᵢ ≤ |γᵢ|Bᵢ`, `∫X_i² ≤ (γᵢsᵢ)²`; product via
`iIndepFun.mgf_sum`; Chernoff `measure_ge_le_exp_mul_mgf` at the given `λ`; two-sided via
`two_sided_of_one_sided` with `−γ` (`G` depends on `γ` only through `|γᵢ|`, `γᵢ²`).
Hypothesis `hb : ∀ i, 0 < |γ i| * B i` as specified; `hu : 0 ≤ u` is kept in the signatures
though Chernoff does not need it (linter silenced on `two_point_one_tail`).

## Milestone C — `two_point_evalue` (done)
`∫ exp(λN)/∏G ≤ 1` by `integral_div`, `div_le_one` (product positive via
`twoPointMgfBound_pos`, `Finset.prod_pos`) and Milestone B's mgf bound.

## Verification
- `~/.elan/bin/lake build`: clean; only the pre-existing Berry–Esseen `sorry`.
- `#print axioms`:
```
'BoundedError.two_point_mgf_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'BoundedError.two_point_one_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
'BoundedError.two_point_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
'BoundedError.two_point_evalue' depends on axioms: [propext, Classical.choice, Quot.sound]
'BoundedError.hoeffding_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
'BoundedError.bernstein_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
```
- Milestone D (contrast-level corollary) not started (optional).
