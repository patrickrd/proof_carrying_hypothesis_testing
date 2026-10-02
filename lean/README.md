# The Linear Model in Lean

Theory of the Linear Model, including the t-test, formalised in Lean 4 with Mathlib: OLS optimality, OLS CLT, HC variance estimation, and asymptotically valid inference under heteroscedasticity and misspecification.

## Motivation

This repository aims to formalise the core theory supporting the linear model, in its typical operational use across science, medicine and economics.

Linear regression refers to a collection of statistical tools, designed to understand the mechanism by which variables predict an outcome, built around the linear model

$$y = \mathbf{X}\beta + \varepsilon,$$

where $\beta \in \mathbb{R}^p$ is a vector of unknown coefficients, $y \in \mathbb{R}^n$ represents a collection of observed outcomes, $\mathbf{X} \in \mathbb{R}^{n \times p}$ holds the values of the corresponding predictor variables, and $\varepsilon \in \mathbb{R}^{n}$ represents the prediction errors.

Two common applications of this model are trend estimation (where $\mathbf{X}$ represents time) and the t-test (where $\mathbf{X}$ represents grouping), certainly the most frequently performed statistical procedure in science.

This work is part of a wider research question of how to make Statistics performed by AI somehow trustworthy. This broader question has shaped some design decisions:

- We have implemented a model-robust theory (also known as assumption-lean), in which the linear model is not assumed to hold: an assumption which is hard to verify, especially automatically.
- The theory is structured to highlight clear points of contact with the data, to support model-checking and sensitivity analysis.
- Complete machine-checked proofs: No sorries, axioms or other gaps in the public release (lean-statistics/linear-model-lean). The files added in this repository are AI-generated and unaudited (see the top-level README) and contain one `sorry`, in `Clt/BerryEsseen.lean`.

## Project status
Inference is asymptotically valid (coverage at least nominal) under heteroscedasticity and misspecification, and exact under correct specification. A positive interpretation of this result is that the *worst case scenario* for coverage is a *correctly specified model*. 

### Currently formalised

| Result | Lean file | Theorem |
|---|---|---|
| OLS optimality (least-squares and population L2 solutions, assumption-lean) | `Ols/Optimality.lean`, `Ols/ProjectionCLT.lean` | `olsEstimator_optimal`, `olsEstimator_unique`, `olsEstimand` |
| OLS CLT (assumption-lean, growing n, fixed p) | `Ols/Assumptions.lean` | `AssumptionBundle.central_limit_OLS_projection'` |
| HC consistency (HC0–3 sandwich-variance limits, assumption-lean) | `Ols/HCSandwichConsistency.lean` | `hcGram_sandwich_consistent`, `hc0_sandwich_consistent`, `hc1_sandwich_consistent`, `hc2_sandwich_consistent`, `hc3_sandwich_consistent` |
| Conservative inference (asymptotically conservative tests; exact under correct specification) | `Ols/TTest.lean` | `hcGram_conservative_test` |
| Conservative p-values, with application to the Welch t-test (CLT + HC2) | `Ols/TTest.lean`, `Ols/Welch.lean` | `hcGram_pvalue_conservative_of_level`, `hc0_pvalue_conservative`–`hc3_pvalue_conservative`, `hc2_studentized_twoSample_eq_welch` |
| Assumption bundle supporting the above | `Ols/Assumptions.lean` | `AssumptionBundle` |

### In progress (contributions welcome)

- Finite-sample exact theory under Gaussian errors: the $\chi^2$, $t$ and $F$ sampling distributions of the classical normal linear model. Complete and machine-checked; held back to keep this first release assumption-lean throughout.
- Growing-dimension asymptotics: the OLS CLT and HC variance estimators with the number of predictors $p$ growing with $n$. Core results in place; the supporting assumptions are being finalised.
- Model-checking and diagnostics: leverage and Cook's distance, supporting the points of contact with the data described above. At the design stage.

### Planned (contributions welcome)

- A multivariate central limit theorem, to state the OLS CLT for vector contrasts rather than a single scalar contrast, building on the community effort in Mathlib.
- ANOVA and F-tests in the assumption-lean framing.
- Model selection.
- Cluster-robust variance estimators (CR0–CR3).
- Random design (predictors treated as random rather than fixed).

## Related work

The asymptotic over-estimation of the variance under misspecification, and the validity of confidence intervals and hypothesis tests as a result, are known in adjacent forms: in misspecified generalised linear models (Fahrmeir 1990), in i.i.d. resampling inference (Liu and Singh 1995), for fixed regressors in econometrics (Abadie, Imbens and Zheng 2014), and for independent non-identically distributed data (Kuchibhotla, Brown and Buja 2018), with analogous phenomena well-known in the causal inference literature (Neyman 1923; Abadie et al. 2020). To our knowledge, a uniform treatment of HC0–HC3 under a deterministic design is not in the literature.

### Assumption-lean (model-robust) regression

- Buja, Brown, Berk, George, Pitkin, Traskin, Zhang and Zhao (2019), Models as Approximations I: Consequences Illustrated with Linear Regression, Statistical Science 34(4), 523–544.
- Buja, Brown, Kuchibhotla, Berk, George and Zhao (2019), Models as Approximations II: A Model-Free Theory of Parametric Regression, Statistical Science 34(4), 545–565.
- Berk, Buja, Brown, George, Kuchibhotla, Su and Zhao (2021), Assumption Lean Regression, The American Statistician 75(1), 76–84. (source of the term)
- Vansteelandt and Dukes (2022), Assumption-Lean Inference for Generalised Linear Model Parameters, Journal of the Royal Statistical Society Series B 84(3), 657–685.
- White (1980b), Using Least Squares to Approximate Unknown Regression Functions, International Economic Review 21, 149–170. (the optimal-linear-projection target)
- Lin (2013), Agnostic Notes on Regression Adjustments to Experimental Data: Reexamining Freedman's Critique, Annals of Applied Statistics 7(1), 295–318.

### Heteroscedasticity-consistent (sandwich) variance

- Eicker (1963), Asymptotic Normality and Consistency of the Least Squares Estimators for Families of Linear Regressions, Annals of Mathematical Statistics 34, 447–456; Eicker (1967), Limit Theorems for Regressions with Unequal and Dependent Errors, Proceedings of the Fifth Berkeley Symposium I, 59–82.
- Huber (1967), The Behavior of Maximum Likelihood Estimates Under Nonstandard Conditions, Proceedings of the Fifth Berkeley Symposium I, 221–233. (origin of the sandwich)
- White (1980a), A Heteroskedasticity-Consistent Covariance Matrix Estimator and a Direct Test for Heteroskedasticity, Econometrica 48, 817–838. (HC0)
- MacKinnon and White (1985), Some Heteroskedasticity-Consistent Covariance Matrix Estimators with Improved Finite Sample Properties, Journal of Econometrics 29, 305–325. (HC1, HC2, HC3)
- Welch (1947), The Generalization of 'Student's' Problem when Several Different Population Variances are Involved, Biometrika 34, 28–35. (the two-group HC2 test reproduces this)
- Freedman (2006), On the So-Called "Huber Sandwich Estimator" and "Robust Standard Errors", The American Statistician 60, 299–302. (a sceptical counterpoint)

### Conservativeness under misspecification

- Fahrmeir (1990), Maximum Likelihood Estimation in Misspecified Generalized Linear Models, Statistics 21(4), 487–502.
- Liu and Singh (1995), Using i.i.d. Bootstrap Inference for General Non-i.i.d. Models, Journal of Statistical Planning and Inference 43, 67–75.
- Abadie, Imbens and Zheng (2014), Inference for Misspecified Models With Fixed Regressors, Journal of the American Statistical Association 109(508), 1601–1614.
- Kuchibhotla, Brown and Buja (2018), Model-free Study of Ordinary Least Squares Linear Regression, arXiv:1809.10538.
- Kuchibhotla, Brown, Buja and Cai (2019), All of Linear Regression, arXiv:1910.06386.

### Inference for projection parameters under misspecification

- Kuchibhotla, Rinaldo and Wasserman (2021), Berry–Esseen Bounds for Projection Parameters and Partial Correlations with Increasing Dimension, arXiv:2007.09751. (the closest analogue: non-asymptotic normal approximation for the sandwich-standardised projection-parameter estimator, under random design)
- Chang, Kuchibhotla and Rinaldo (2023), Inference for Projection Parameters in Linear Regression: beyond $d = o(n^{1/2})$, arXiv:2307.00795.

### Provenance

- Began as a fork of RemyDegenne/CLT and builds on the [CLT in Mathlib](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/CentralLimitTheorem.html).
- The OLS CLT is stated in terms of a chosen projection (a scalar contrast $a^\top\beta$), pending the multivariate CLT in progress in the community, to build on that work.
- The Lindeberg CLT on which the OLS CLT relies is released separately in its own repository: [CLT-lindeberg](https://github.com/patrickrd/CLT-lindeberg).

## Building

Fetch the prebuilt Mathlib cache and build:

```sh
lake exe cache get
lake build
```

This expects the Lean toolchain pinned in `lean-toolchain` (currently `leanprover/lean4:v4.30.0-rc2`); `elan` will select it automatically.

## Dependencies

- Lean toolchain: `leanprover/lean4:v4.30.0-rc2` (pinned in `lean-toolchain`).
- Mathlib, pinned in `lake-manifest.json` (commit `1b6244ba2a57456b4206043ea8907b7a0180a670`).
- `checkdecls` (PatrickMassot/checkdecls).

## Responsible use and limitations

This is a research artefact. It has not been validated for clinical, legal, financial, or policy decisions. The proofs are machine-checked and depend only on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`), with no sorries in the public release; the files added here contain one `sorry` (`Clt/BerryEsseen.lean`). Correctness nonetheless rests on the theorem statements faithfully capturing the intended mathematics, and on trust in Lean's kernel and the Mathlib library.

## Use of AI

Parts of this formalisation were developed with the assistance of AI tools, principally Claude (Opus). In the public release, all definitions, theorem statements, and proofs were reviewed by the authors, who are responsible for the correctness of the work. The files added in this repository have not been audited. Our use of AI is obviously consistent with the wider research question of how to make Statistics performed by AI somehow trustworthy.

## Citing this work

A report describing this work is in preparation; please cite it once available.

## Acknowledgements and funding

We thank the authors of the upstream CLT project, the Mathlib community, and Rajarshi Mukherjee, Arun Kuchibhotla for helpful discussions.

This work was supported by the EPSRC NeST programme grant ([nest-programme.ac.uk](https://nest-programme.ac.uk)).

## Licence

Released under the Apache License 2.0 (see `LICENSE`).
