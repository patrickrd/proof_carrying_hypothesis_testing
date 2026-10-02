"""Coordinate-ascent adversarial search for the certifiability limit
   c(A) = sup_{P in A} P(|T| >= t0),  T = HC0-studentised contrast,
   A: independent errors, mean 0, variance 1, E|e|^3 <= b3, E e^4 <= k4,
      optionally r = (I-H) z with max|r_i| <= RBOX.
Laws live on a fixed atom grid G; each observation has a mass vector over G.
With all other laws (and r) fixed, the objective is LINEAR in observation i's masses,
so the best law for i is an LP over the grid (5 constraints -> <= 5 atoms).
Objective during the search is smoothed: E plogis((|T|-t)/h); the final number is the
hard exceedance on fresh draws.  Every reported number is a feasible lower bound on c.
"""
import numpy as np, sys, time
from scipy.optimize import linprog
from scipy.special import expit

B3MAX = np.sqrt(8/np.pi); K4MAX = 3.0; RBOX = 0.5

def make_grid(m=45, xmax=7.0):
    u = np.linspace(0, 1, m)[1:]
    g = xmax * u**1.6
    return np.concatenate([-g[::-1], [0.0], g])

class Search:
    def __init__(self, X, a, t0, B, mis, seed=1, grid=None, rbox=RBOX):
        X = np.asarray(X, float); n = len(X); self.rbox = rbox
        XtXi = np.linalg.inv(X.T @ X)
        self.wt = X @ XtXi @ a; self.w2 = self.wt**2
        self.IH = np.eye(n) - X @ XtXi @ X.T
        self.n = n; self.t0 = t0; self.B = B; self.mis = mis
        self.G = make_grid() if grid is None else grid
        self.q = (self.w2[:,None] * self.IH**2).sum(0)   # q_i = sum_j w_j c_ij^2
        self.rng = np.random.default_rng(seed)
        self.P = None; self.r = np.zeros(n); self.z = np.zeros(n)

    # ---- laws -> draws ----
    def sample_row(self, i, U):
        cw = np.cumsum(self.P[i]); cw[-1] = 1.0
        return self.G[np.searchsorted(cw, U, side="right").clip(0, len(self.G)-1)]

    def refresh(self):
        """new common random numbers; rebuild E, R, N, D2"""
        self.U = self.rng.random((self.n, self.B))
        self.E = np.empty((self.n, self.B))
        for i in range(self.n): self.E[i] = self.sample_row(i, self.U[i])
        self.R = self.IH @ self.E + self.r[:,None]
        self.N = self.wt @ self.E
        self.D2 = self.w2 @ (self.R**2)

    def smooth_obj(self, t, h):
        T = np.abs(self.N)/np.sqrt(np.maximum(self.D2, 1e-300))
        return expit((T - t)/h).mean()

    # ---- LP for one observation ----
    def lp(self, g):
        G = self.G
        A_eq = np.vstack([np.ones_like(G), G, G**2]); b_eq = [1, 0, 1]
        A_ub = np.vstack([np.abs(G)**3, G**4]); b_ub = [B3MAX, K4MAX]
        res = linprog(-g, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=(0, None), method="highs")
        if res.status != 0: return None
        p = np.maximum(res.x, 0); return p/p.sum()

    def update_obs(self, i, t, h):
        c = self.IH[:, i]; q = self.q[i]; ei = self.E[i]
        s_full = (self.w2 * c) @ self.R                     # sum_j w_j R_j c_j  (R includes r)
        s = s_full - ei*q                                   # without observation i's error
        N0 = self.N - self.wt[i]*ei
        D0 = self.D2 - 2*ei*s - ei**2*q
        x = self.G[:,None]
        T = np.abs(N0[None,:] + self.wt[i]*x) / np.sqrt(np.maximum(D0[None,:] + 2*x*s[None,:] + x**2*q, 1e-300))
        g = expit((T - t)/h).mean(1)                        # g(x) for each grid atom
        p = self.lp(g)
        if p is None: return
        self.P[i] = p
        enew = self.sample_row(i, self.U[i]); d = enew - ei
        self.E[i] = enew; self.R += np.outer(c, d); self.N += self.wt[i]*d
        self.D2 = self.w2 @ (self.R**2) if (i % 50 == 49) else self.D2 + 2*d*s + d**2*q
        # exact recompute every 50 to stop drift; incremental formula: D2(new) = D0 + 2 enew s + enew^2 q

    def update_r(self, i, t, h, m=25):
        """line search r -> r + alpha c_i within the box; z bookkeeping not needed (r stays in range(I-H))"""
        c = self.IH[:, i]; q = self.q[i]
        # feasible alpha interval: |r_j + alpha c_j| <= RBOX for all j
        s = (self.w2 * c) @ self.R
        def evalf(al):
            al = np.asarray(al, float)[:,None]
            T = np.abs(self.N)[None,:] / np.sqrt(np.maximum(self.D2[None,:] + 2*al*s[None,:] + al**2*q, 1e-300))
            return expit((T - t)/h).mean(1)
        if self.rbox is None:
            # unbounded r (only X'r = 0): coarse symmetric log grid, then linear refinement
            lg = np.concatenate([-np.logspace(-3, 3, 31)[::-1], [0.0], np.logspace(-3, 3, 31)])
            f = evalf(lg); f0 = f[31]                     # value at alpha = 0
            if f.max() <= f0 * (1 + 1e-9): return       # flat or no improvement: stay put
            k = int(np.argmax(f))
            lo = lg[max(0, k-1)]; hi = lg[min(len(lg)-1, k+1)]
            al = np.linspace(lo, hi, m); f = evalf(al); k = int(np.argmax(f)); alpha = al[k]
            if f[k] <= f0 * (1 + 1e-9): return
        else:
            lo, hi = -np.inf, np.inf
            for cj, rj in zip(c, self.r):
                if abs(cj) < 1e-12: continue
                a1, a2 = (-self.rbox - rj)/cj, (self.rbox - rj)/cj
                lo = max(lo, min(a1, a2)); hi = min(hi, max(a1, a2))
            if not np.isfinite(lo) or hi <= lo: return
            al = np.linspace(lo, hi, m); f = evalf(al); k = int(np.argmax(f)); alpha = al[k]
        if alpha == 0: return
        self.r += alpha*c; self.R += alpha*c[:,None]; self.D2 = self.D2 + 2*alpha*s + alpha**2*q

    def sweep(self, t, h, order=None):
        order = self.rng.permutation(self.n) if order is None else order
        for i in order:
            self.update_obs(i, t, h)
            if self.mis: self.update_r(i, t, h)
        self.D2 = self.w2 @ (self.R**2)

    # ---- initialisation ----
    def init(self, kind):
        n = len(self.G); self.P = np.zeros((self.n, n))
        if kind == "skew":
            p = 0.28
            for i in range(self.n):
                s = 1.0 if self.wt[i] >= 0 else -1.0
                x1, x2 = s*np.sqrt((1-p)/p), -s*np.sqrt(p/(1-p))
                self.P[i, np.argmin(np.abs(self.G-x1))] += p; self.P[i, np.argmin(np.abs(self.G-x2))] += 1-p
        elif kind == "zi":
            q = 0.55; x = 1/np.sqrt(1-q)
            for i in range(self.n):
                self.P[i, np.argmin(np.abs(self.G))] += q
                self.P[i, np.argmin(np.abs(self.G-x))] += (1-q)/2; self.P[i, np.argmin(np.abs(self.G+x))] += (1-q)/2
        elif kind == "normal":
            from scipy.stats import norm
            edges = np.concatenate([[-np.inf], (self.G[1:]+self.G[:-1])/2, [np.inf]])
            p = np.diff(norm.cdf(edges)); self.P[:] = p/p.sum()
        # project each row onto the constraint set via LP (max overlap with itself)
        for i in range(self.n):
            pp = self.lp(self.P[i]);
            if pp is not None: self.P[i] = pp
        self.r[:] = 0

    # ---- moments / feasibility ----
    def moments(self):
        G = self.G
        m1 = self.P @ G; m2 = self.P @ G**2; m3 = self.P @ np.abs(G)**3; m4 = self.P @ G**4
        return m1, m2, m3, m4

    # ---- hard evaluation on fresh draws ----
    def hard(self, Bh, seed=99, chunk_elt=2e7):
        rng = np.random.default_rng(seed); block = max(10000, int(chunk_elt/self.n))
        done = 0; exc = 0; mx = 0.0
        cw = np.cumsum(self.P, 1); cw[:,-1] = 1.0
        while done < Bh:
            b = min(block, Bh-done); U = rng.random((self.n, b))
            E = np.empty((self.n, b))
            for i in range(self.n): E[i] = self.G[np.searchsorted(cw[i], U[i], side="right").clip(0, len(self.G)-1)]
            R = self.IH @ E + self.r[:,None]; N = self.wt @ E; D2 = self.w2 @ (R**2)
            T = np.abs(N)/np.sqrt(np.maximum(D2, 1e-300))
            exc += int((T >= self.t0).sum()); mx = max(mx, T.max()); done += b
        m1, m2, m3, m4 = self.moments()
        feas = (np.abs(m1) < 1e-6).all() and (np.abs(m2-1) < 1e-6).all() and (m3 <= B3MAX+1e-6).all() and (m4 <= K4MAX+1e-6).all() and (self.rbox is None or np.abs(self.r).max() <= self.rbox+1e-9)
        return dict(p=exc/Bh, nexc=exc, B=Bh, maxT=mx, feas=bool(feas), m3=m3.max(), m4=m4.max(), maxr=np.abs(self.r).max())

def cp_lower(k, n, alpha=0.05):
    from scipy.stats import beta
    return 0.0 if k == 0 else beta.ppf(alpha, k, n-k+1)

def run(name, X, a, t0, mis, init, B, sweeps, Bh, log, seed=1):
    S = Search(X, a, t0, B, mis, seed=seed); S.init(init)
    ladder = [t for t in [1.96, 3, 4, 6, 9] if t < t0] + [round(t0, 2)]
    S.refresh()
    for t in ladder:
        for h in [max(0.3, t/8)] + ([max(0.15, t/16)] if t == ladder[-1] else []):
            for s in range(sweeps):
                S.refresh(); f0 = S.smooth_obj(t, h); S.sweep(t, h); f1 = S.smooth_obj(t, h)
                log(f"  {name} mis={mis} {init:6s} t={t:6.2f} h={h:5.2f} sweep {s+1}: smooth {f0:.4e} -> {f1:.4e}")
    hv = S.hard(Bh)
    hv.update(dataset=name, mis=mis, init=init, t0=t0, lower95=cp_lower(hv["nexc"], hv["B"]))
    return hv, S
