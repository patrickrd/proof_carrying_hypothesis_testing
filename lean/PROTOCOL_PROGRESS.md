# PROTOCOL_PROGRESS — closing the gaps between the ICLR paper and the Lean project

Date: 2026-09-23. Status: **Milestones A–G complete, sorry-free** (full `lake build` clean; the
only `sorry` warning is the pre-existing `Clt/BerryEsseen.lean:55`).

## Per-milestone log
- 2026-09-23 A — `Ols/EValueAlgebra.lean` (namespace `EValue`): `IsEVariable`,
  `IsEVariable.sum_smul`, `IsEVariable.average`, `IsEVariable.half_add` (extra, used by `gridBet`),
  `IsEVariable.of_le`, `IsEVariable.markov`; sanity `example` `P(e ≥ 1/α) ≤ α`. done.
- 2026-09-23 B — `Ols/BoundedError.lean`, `section EValueForms`: `hoeffding_mgf_le`,
  `hoeffding_evalue`, `bernstein_evalue`; public `bernstein_mgf_le` next to the private
  `mgf_wsum_le`; public `centredErr_props_of_bounded` next to the private `centredErr_props`;
  named `twoPointMgfBound_zero`. done.
- 2026-09-23 C — `BahadurSavage.bahadurSavage_pi_unbounded` (same four-line proof, no `φ ≤ 1`),
  `BahadurSavage.bahadurSavage_evalue_pi` (μ₀-shift mirrored from `bahadurSavage_pvalue_pi'`),
  `PaperAligned.Distribution.expect`, `PaperAligned.ValidEValue`, `PaperAligned.bahadur_savage_evalue`.
  done. DEVIATION: `ValidEValue` has an extra field
  `integrable : ∀ F, F.mean = μ₀ → Integrable value (prodLaw n F.law)`. Without it the real-valued
  `valid : F.expect value ≤ 1` is uninformative when the lintegral is infinite (`toReal ∞ = 0`),
  and `bahadurSavage_evalue_pi` cannot be fed. NOTE for the paper: this is the *expectation* form
  ("no bet has positive expected return under any alternative"), not a pointwise statement.
- 2026-09-23 D — `Ols/Estimand.lean` (namespace `Estimand`): `integral_sq_sub_eq`,
  `integral_normSq_sub_mulVec`, `olsEstimand_optimal`, `olsEstimand_unique`; second moments
  only, no independence anywhere in the file. done.
- 2026-09-23 E — `Ols/Protocol.lean` (namespace `Protocol`): `Posting`, `AssumptionClass`,
  `NullHolds`, `Bet`, `Bet.guarantee`, `boundedErrorClass`, `sum_olsWeights_mul`, `wsum_eq_sub_v`
  (the spec's `contrastDiff_eq_sub_v`), `olsWeights_neg`, `measurable_contrast`, `twoPointDen`,
  `twoPointBet`, `Posting.neg`, `NullHolds.neg`, `hb_neg`, `gridBet` (two-sided `±λ` grid, weights
  `1/(2k)`, validity by `IsEVariable.average` + `IsEVariable.half_add`); sanity `example`s
  (`twoPointBet` at `λ = 0` is `e ≡ 1`; `Bet.guarantee` at `c = 20`). done.
- 2026-09-23 F — `BoundedError.two_point_contrast`. done.
- 2026-09-23 G — verification only (below). done.

## `#print axioms` (headline results)
```
'EValue.IsEVariable.sum_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'EValue.IsEVariable.of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'EValue.IsEVariable.markov' depends on axioms: [propext, Classical.choice, Quot.sound]
'BoundedError.hoeffding_evalue' depends on axioms: [propext, Classical.choice, Quot.sound]
'BoundedError.bernstein_evalue' depends on axioms: [propext, Classical.choice, Quot.sound]
'BahadurSavage.bahadurSavage_evalue_pi' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperAligned.bahadur_savage_evalue' depends on axioms: [propext, Classical.choice, Quot.sound]
'Estimand.olsEstimand_optimal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Protocol.Bet.guarantee' depends on axioms: [propext, Classical.choice, Quot.sound]
'Protocol.twoPointBet' depends on axioms: [propext, Classical.choice, Quot.sound]
'Protocol.gridBet' depends on axioms: [propext, Classical.choice, Quot.sound]
'BoundedError.two_point_contrast' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Milestone G outputs
```
'hc2_studentized_twoSample_eq_welch' depends on axioms: [propext, Classical.choice, Quot.sound]
'hc0_sandwich_consistent' depends on axioms: [propext, Classical.choice, Quot.sound]
'hc1_sandwich_consistent' depends on axioms: [propext, Classical.choice, Quot.sound]
'hc2_sandwich_consistent' depends on axioms: [propext, Classical.choice, Quot.sound]
'hc3_sandwich_consistent' depends on axioms: [propext, Classical.choice, Quot.sound]
'finiteN_tail_twoSided_cantelli' depends on axioms: [propext, Classical.choice, Quot.sound]
'FiniteSampleBundle.aMinus_pos_hc3' depends on axioms: [propext, Classical.choice, Quot.sound]
```
`hc2_studentized_twoSample_eq_welch` hypotheses: `2 ≤ m`, `2 ≤ k`, `v : Fin (m + k) → ℝ`.
`finiteN_tail_twoSided_cantelli` hypotheses: bundle `A`, `∀ i, 1 ≤ d i`, `a ≠ 0`, the A3 input
`η`, `0 < t`, `0 < θ`, `∀ i, hcWeight X d a i ≤ g`, `0 < aMinus …` — no `C_r`/tolerance field is
used (the bundle's `C_r`/`hres` fields exist but are not hypotheses of the statement).
`aMinus_pos_hc3` hypotheses: `a ≠ 0`, `∀ j, leverage X j < 1`, `0 < θ < 1`, `d j = (1 − hⱼ)⁻²`.

## Registration
`Ols.lean` imports `Ols.EValueAlgebra`, `Ols.Estimand`, `Ols.Protocol`; all three added to the
`lakefile.toml` globs. No existing theorem statement was changed.
