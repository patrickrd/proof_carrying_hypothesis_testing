"""Resumable driver: one job = (dataset, mis, init). State checkpointed after every (t,h) stage."""
import sys, time, csv, os, pickle, numpy as np
from designs import designs
from search import Search, cp_lower

mode = int(sys.argv[1]); mis = int(mode > 0); rbox = None if mode == 2 else 0.5; names = sys.argv[2].split(","); budget = float(sys.argv[3]) if len(sys.argv) > 3 else 560
T0 = time.time()
D = designs(); out = f"results/res_mode{mode}_{'_'.join(names)}.csv"; logf = open(f"log_mode{mode}_{'_'.join(names)}.txt", "a")
def log(s): logf.write(s+"\n"); logf.flush()
done_rows = set()
if os.path.exists(out):
    for row in csv.DictReader(open(out)): done_rows.add((row["dataset"], row["init"]))

for nm in names:
    X, y, a, t0 = D[nm]; n = len(X)
    big = n > 300
    B = 100000 if n <= 100 else 40000 if n <= 300 else 10000
    Bh = 4000000 if n <= 100 else 2000000 if n <= 300 else 500000
    sweeps = 2 if big else 3
    ladder = ([t for t in [1.96, 3, 4, 6, 9] if t < t0] if not big else [t for t in [1.96, 4] if t < t0]) + [round(t0, 2)]
    stages = [(t, max(0.3, t/8)) for t in ladder] + [(ladder[-1], max(0.15, ladder[-1]/16))]
    for init in ["skew", "zi"]:
        if (nm, init) in done_rows: continue
        ck = f"ck/ck_{nm}_mode{mode}_{init}.pkl"
        if os.path.exists(ck):
            st = pickle.load(open(ck, "rb")); S = st["S"]; k0 = st["stage"]
        else:
            S = Search(X, a, t0, B, mis, seed=1, rbox=rbox); S.init(init); k0 = 0
        for k in range(k0, len(stages)):
            if time.time() - T0 > budget: log(f"budget reached before stage {k} of {nm} {init}"); sys.exit(0)
            t, h = stages[k]
            for s in range(sweeps):
                S.refresh(); f0 = S.smooth_obj(t, h); S.sweep(t, h); f1 = S.smooth_obj(t, h)
                log(f"  {nm} mode={mode} {init:5s} t={t:6.2f} h={h:5.2f} sweep {s+1}: {f0:.3e} -> {f1:.3e}  [{int(time.time()-T0)}s]")
            S.U = S.E = S.R = None  # drop big arrays before pickling
            pickle.dump({"S": S, "stage": k+1}, open(ck, "wb"))
        if time.time() - T0 > budget: log(f"budget reached before hard eval of {nm} {init}"); sys.exit(0)
        hv = S.hard(Bh)
        new = not os.path.exists(out)
        with open(out, "a", newline="") as f:
            w = csv.writer(f)
            if new: w.writerow(["dataset","n","t0","mode","init","p","lower95","nexc","B","feas","maxT","m3","m4","maxr","secs"])
            w.writerow([nm, n, t0, mode, init, f"{hv['p']:.4e}", f"{cp_lower(hv['nexc'], Bh):.4e}", hv["nexc"], Bh, hv["feas"],
                        f"{hv['maxT']:.2f}", f"{hv['m3']:.3f}", f"{hv['m4']:.3f}", f"{hv['maxr']:.3f}", int(time.time()-T0)])
        np.save(f"laws/laws_{nm}_mode{mode}_{init}.npy", np.column_stack([S.P, S.r]))
        log(f"### done {nm} mode={mode} {init}: p={hv['p']:.3e} nexc={hv['nexc']}")
log("all jobs done")
