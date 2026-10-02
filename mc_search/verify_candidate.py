"""Verify a saved Monte Carlo candidate: check it lies in the declared class and recompute the
exceedance probability by plain Monte Carlo with the same seed as the original hard evaluation.

usage: python verify_candidate.py DATASET MODE INIT [DRAWS]   e.g.  GISTEMP 0 skew 4000000
Reads laws/laws_{DATASET}_mode{MODE}_{INIT}.npy (columns: n error laws on the atom grid, last column r)
and the design from designs.py. Prints feasibility (mean 0, variance 1, third and fourth moment caps,
|r| within the box), the exceedance count, the point estimate and the Clopper-Pearson 95% lower limit.
"""
import sys, numpy as np
from designs import designs
from search import Search, cp_lower, RBOX

nm, mode, init = sys.argv[1], int(sys.argv[2]), sys.argv[3]
draws = int(float(sys.argv[4])) if len(sys.argv) > 4 else 4000000
X, y, a, t0 = designs()[nm]
L = np.load(f"laws/laws_{nm}_mode{mode}_{init}.npy")
S = Search(X, a, t0, B=1, mis=(mode != 0), seed=1, rbox=(None if mode == 0 else RBOX))
S.P = L[:, :-1]; S.r = L[:, -1]
res = S.hard(draws, seed=99)
print(f"{nm} mode{mode} {init}: n={len(X)} t0={t0:.4f} feasible={res['feas']} max|r|={res['maxr']:.3f} "
      f"exceedances={res['nexc']}/{res['B']} p={res['p']:.4e} lower95={cp_lower(res['nexc'], res['B']):.4e} maxT={res['maxT']:.2f}")
