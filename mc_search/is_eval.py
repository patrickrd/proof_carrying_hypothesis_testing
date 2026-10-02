"""Importance-sampling re-evaluation of a saved MC-search candidate (24 Sep 2026).

For a candidate (laws P on the atom grid, misspecification vector r) saved by driver2.py,
estimate  P(|T| >= t0)  under that candidate to far below the 1/B resolution of plain
Monte Carlo, by exponential tilting of each observation's law towards the tail:
    p_i^theta(x)  proportional to  P_i(x) exp(theta * g_i * x),
    likelihood ratio  w = exp(-theta * N + sum_i log M_i(theta g_i)),  N = sum_i g_i eps_i.
The two tails are estimated separately (theta > 0 for {T >= t0, N > 0}, theta < 0 for the
other) so that the weights stay bounded on the event counted.  theta is chosen so that the
tilted mean of N equals the observed contrast error u = t0 * sd(N).

Usage:  python is_eval.py SH0ES [draws_per_tail]
"""
import sys, time, numpy as np
from designs import designs
from search import make_grid, B3MAX, K4MAX

nm = sys.argv[1]; draws = int(float(sys.argv[2])) if len(sys.argv) > 2 else 400000
X, y, a, t0 = designs()[nm]; n = len(X)
XtXi = np.linalg.inv(X.T @ X); wt = X @ XtXi @ a; w2 = wt**2
IH = np.eye(n) - X @ XtXi @ X.T
G = make_grid(); sdN = np.sqrt(w2.sum()); u = t0 * sdN
print(f"{nm}: n={n} t0={t0:.4f} sd(N)={sdN:.4g} u={u:.4g}  Gaussian reference 2*Phibar(t0)={2*__import__('scipy.stats').stats.norm.sf(t0):.3e}")

def tilted(P, theta):
    """tilted masses and log normalisers for tilt parameter theta (applied as theta*g_i)."""
    Z = theta * wt[:, None] * G[None, :]; c = Z.max(1, keepdims=True)   # shift for stability
    L = P * np.exp(Z - c)
    M = L.sum(1); return L / M[:, None], np.log(M) + c[:, 0]

def mean_N(P, theta):
    Q, _ = tilted(P, theta); return (wt * (Q @ G)).sum()

def solve_theta(P, target):
    target = min(target, 0.95 * (np.abs(wt) * G.max()).sum())   # cannot tilt beyond the grid's reach
    lo, hi = 0.0, 1.0
    while mean_N(P, hi) < target: hi *= 2
    for _ in range(60):
        mid = (lo + hi) / 2
        if mean_N(P, mid) < target: lo = mid
        else: hi = mid
    return (lo + hi) / 2

def estimate(P, r, theta, sign, draws, seed, block=4000):
    """IS estimate of P(T >= t0, sign*N > 0) using tilt theta (same sign as `sign`)."""
    rng = np.random.default_rng(seed)
    Q, logM = tilted(P, theta); cw = np.cumsum(Q, 1); cw[:, -1] = 1.0
    s1 = s2 = 0.0; done = 0; mxw = 0.0
    while done < draws:
        b = min(block, draws - done); U = rng.random((n, b))
        E = np.empty((n, b))
        for i in range(n): E[i] = G[np.searchsorted(cw[i], U[i], side="right").clip(0, len(G) - 1)]
        R = IH @ E + r[:, None]; N = wt @ E; D2 = w2 @ (R**2)
        T = np.abs(N) / np.sqrt(np.maximum(D2, 1e-300))
        ind = (T >= t0) & (sign * N > 0)
        w = np.exp(-theta * N + logM.sum()) * ind
        s1 += w.sum(); s2 += (w**2).sum(); done += b; mxw = max(mxw, w.max())
    p = s1 / draws; se = np.sqrt(max(s2 / draws - p**2, 0) / draws)
    return p, se, mxw

for mode in (0, 2):
    for init in ("skew", "zi"):
        L = np.load(f"laws/laws_{nm}_mode{mode}_{init}.npy"); P = L[:, :-1]; r = L[:, -1]
        m1 = P @ G; m2 = P @ G**2; m3 = P @ np.abs(G)**3; m4 = P @ G**4
        feas = (np.abs(m1) < 1e-6).all() and (np.abs(m2 - 1) < 1e-6).all() and (m3 <= B3MAX + 1e-6).all() and (m4 <= K4MAX + 1e-6).all()
        t = time.time(); tot = 0.0; var = 0.0; parts = []
        for sign in (+1, -1):
            # tilt so that the tilted mean of sign*N equals u
            Ps = P if sign > 0 else P[:, ::-1]           # reflect the grid for the lower tail
            theta = solve_theta(Ps, u) * sign
            p, se, mxw = estimate(P, r, theta, sign, draws, seed=7 + sign)
            parts.append((sign, theta, p, se, mxw)); tot += p; var += se**2
        print(f"mode={mode} init={init:4s} feasible={feas} max|r|={np.abs(r).max():.3f}  "
              f"P(|T|>=t0) = {tot:.3e} +- {np.sqrt(var):.1e}   "
              f"[upper tail {parts[0][2]:.3e} (theta={parts[0][1]:.3f}), lower tail {parts[1][2]:.3e} (theta={parts[1][1]:.3f})]  "
              f"max weight {max(parts[0][4], parts[1][4]):.2e}  {time.time()-t:.0f}s", flush=True)
