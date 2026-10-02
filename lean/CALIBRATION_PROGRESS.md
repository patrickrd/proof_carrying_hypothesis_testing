# CALIBRATION_PROGRESS — `Ols/Calibration.lean`

Date: 2026-09-24. Status: **Milestones A and B complete, sorry-free.** Milestone C (general
decreasing calibrator) not started (optional).

## Lemma log
- 2026-09-24 `calibrator_tail_le` — done. Set inclusion `{t < 1/(2√p)} ⊆ {p ≤ 1/(4t²)}` (the
  edge case `p = 0` gives `calibrator 0 = 0 < t`, impossible), then `hp.valid` when
  `1/(4t²) ≤ 1` and the trivial bound `≤ 1` otherwise (`measureReal_mono`, `probReal_univ`).
- 2026-09-24 `calibrate_pvalue` — done. Layer cake `lintegral_eq_lintegral_meas_lt`, the tail
  bound moved to `ℝ≥0∞` by `ENNReal.le_ofReal_iff_toReal_le`, the integral
  `∫₀^∞ min(1, 1/(4t²)) dt` split at `1/2` (`Ioc_union_Ioi_eq_Ioi`, `lintegral_union`): the
  first piece is `volume (Ioc 0 (1/2)) = 1/2` (`setLIntegral_const`, `Real.volume_Ioc`), the
  second is `(1/4)∫_{1/2}^∞ t^{-2} dt = 1/2` (`ofReal_integral_eq_lintegral_ofReal`,
  `integrableOn_Ioi_rpow_of_lt`, `integral_Ioi_rpow_of_lt`, `Real.rpow_neg_one`); the two halves
  add to exactly `1`. Integrability from `hasFiniteIntegral_iff_ofReal`; expectation from
  `integral_eq_lintegral_of_nonneg_ae` and `ENNReal.toReal_le_of_le_ofReal`.
- 2026-09-24 sanity `example` (the calibrated e-value's Markov test `P(1/(2√p) ≥ 1/α) ≤ α`)
  — done, via `IsEVariable.markov` (argument order `(e) (he) (hc)`).

No deviation from the specified statements; no positivity hypothesis on `p` was needed (Lean's
`calibrator 0 = 0` convention, as anticipated in the spec).

## `#print axioms`
```
'EValue.calibrator_tail_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'EValue.calibrate_pvalue' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build
Full `~/.elan/bin/lake build`: clean; the only `sorry` warning is the pre-existing
`Clt/BerryEsseen.lean:55`.
