# Proof-carrying hypothesis testing: code and materials

The base of this code is the public release at lean-statistics/linear-model-lean of 31 July, which is fully human-audited. Everything here is AI-generated, not human-audited, and is made public only for reproducibility purposes. When fully audited, the code will be transferred to lean-statistics.

Paper: Rubin-Delanchy and Jones, "Proof-carrying hypothesis testing: certified statistical inference by AI" (submitted to arXiv on 25 September 2026).

## Contents
- `PCHT.pdf`: the paper.
- `lean/`: the Lean project: the public release at https://github.com/lean-statistics/linear-model-lean plus the files added for this paper (Ols/BoundedError.lean, FiniteN.lean, Protocol.lean, Calibration.lean, Estimand.lean, PaperAligned.lean, BahadurSavage.lean and their specification files). Builds with `lake build`; toolchain in `lean-toolchain`. One `sorry`: `Clt/BerryEsseen.lean`, the Berry-Esseen constant.
- `symmetric_bounds.R`, `dataset_bounds.R`, `conservative_bounds.R`, `results_v3b.R`, `cantelli_bounds.R`: the finite-sample p-values and e-values and the asymptotic and normal-approximation columns. Run in that order from this directory; `cantelli_bounds.R` before `results_v3b.R`.
- `export_designs.R`, `mc_search/`: the Monte Carlo search (`search.py`, `driver2.py`, `designs.py`; `shoes_continue.py` for SH0ES), the candidate found for every dataset (`laws/`), the evaluation results (`results/`, `all_results.csv`, `mc_summary.csv`), and `verify_candidate.py`.
- `results_v3c.csv`: the table of numbers behind Figure 2. Assembled from `results_v3b.csv`, `cantelli_results.csv` and `mc_search/results/` (see "Assembly").
- `ENVIRONMENT.txt`, `mc_search/ENVIRONMENT.txt`: software versions used.
Figure-drawing code is not included.

## Data
Loaded by the scripts:
- cars: `data(cars)`
- Hubble: `library(gamair); data(hubble)`; observations 3 and 15 omitted, following Wood (2017) section 1.1.2
- Galton: `library(HistData); data(Galton)`
- Boston: `library(MASS); data(Boston)`
- Mincer: `library(wooldridge); data(wage1)`
- streptomycin: `library(medicaldata); strep_tb`
- anorexia: `MASS::anorexia`
- SH0ES: `shoes_analysis.R` lines 7-10 (PantheonPlusSH0ES DataRelease, SH0ES_Data, three FITS files)
- Card-Krueger: `public.dat` from https://davidcard.berkeley.edu/data_sets/njmin.zip (unzip; read with `read.fwf` as in `symmetric_bounds.R`)
- Reinhart-Rogoff: https://gist.github.com/vincentarelbundock/5409893/raw/a623f2f3bae027a0e51dd01ac5b70d44d909a7b9/RR-processed.csv (Herndon-Ash-Pollin processed data, Arel-Bundock mirror)
- GISTEMP: https://data.giss.nasa.gov/gistemp/tabledata_v4/GLB.Ts+dSST.csv, Land-Ocean Global Means. NASA revises the table monthly; the paper used the version downloaded 2026-09-10, included here as `dataset_story_data/gistemp_global.csv` (US government data, public domain)
- Moore: https://ourworldindata.org/grapher/transistors-per-microprocessor.csv (Our World in Data, CC BY)
- Chinchilla: https://raw.githubusercontent.com/epoch-research/analyzing-chinchilla/main/data/svg_extracted_data.csv (Epoch AI)
Checked 2026-10-02: the Card-Krueger, Reinhart-Rogoff, Moore and Chinchilla downloads are byte-identical to the files the paper used.
Place downloaded files in `dataset_story_data/` under the names used in `symmetric_bounds.R` (`public.dat`, `RR-processed.csv`, `gistemp_global.csv`, `moore.csv`, `chinchilla_epoch.csv`).

## Reported p-values
Not computed by the scripts. As stated in Appendix E of the paper:
- cars 1.5e-12: r-statistics.co linear regression tutorial; University of Sheffield MAS61004, section 4.3
- Hubble (creationist contrast) 3.9e-150: Wood (2017), section 1.1.3
- Galton, slope = 0, 1.7e-49: a public RPubs analysis (prints t = 15.711, p < 2e-16; 1.7e-49 is the untruncated tail)
- Galton, slope = 1: none printed; computed
- Boston 4.25e-6: James et al. (2013), ISLR, p. 114
- Mincer 8.8e-32: Wooldridge, Introductory Econometrics, Example 4.1 (printed t = 12.56; tail beyond printed precision)
- Card-Krueger 0.05: Card and Krueger (1994), Table 4 (2.33, SE 1.19)
- Reinhart-Rogoff: Herndon, Ash and Pollin (2014), Table 4 (printed coefficient and SE; Gaussian tail 1.5e-10)
- streptomycin 0.01: MRC (1948), BMJ, p. 771, "less than one in a hundred"
- anorexia, GISTEMP, Moore, Chinchilla: none printed; computed
- SH0ES 5.7e-7: Riess et al. (2022), five-sigma statement

## Assembly of results_v3c.csv
Columns from `results_v3b.csv` (bounds, e-values, asymptotic), `cantelli_results.csv` (`hc0_analytic` as `normapx`), and `mc_search/results/` (`mc`, `mc_lower95`, `mc_nexc`). Choices: GISTEMP `mc` from the mode-0 run (1.75e-6; the summary file's 2.25e-6 came from a candidate outside the class); SH0ES `mc` from `shoes_continue.py` (2 exceedances in 2e7 draws).

## Monte Carlo
Each plotted Monte Carlo value is the exceedance probability of a saved candidate under a fixed seed. To check a candidate:
```
cd mc_search; python verify_candidate.py GISTEMP 0 skew 4000000
```
prints feasibility (mean 0, variance 1, third and fourth moment caps, |r| within the box) and reproduces the exceedance count in `results/`.

## Licence
Apache 2.0 (`LICENSE`), for the Lean code, the R and Python code and the files in this repository.
