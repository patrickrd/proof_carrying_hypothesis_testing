"""Continue the SH0ES mode-0 'skew' search from its checkpoint (more sweeps at the final
stage) and then evaluate the candidate with many more draws than driver2.py's 5e5,
logging a cumulative count and Clopper-Pearson 95% lower limit after each 1e6-draw chunk.
Started 24 Sep 2026.  Usage: python shoes_continue.py [chunks of 1e6]"""
import pickle, time, sys, numpy as np
from search import Search, cp_lower
from designs import designs
chunks = int(sys.argv[1]) if len(sys.argv) > 1 else 20
X, y, a, t0 = designs()["SH0ES"]; T0 = time.time()
st = pickle.load(open("ck/ck_SH0ES_mode0_skew.pkl", "rb")); S = st["S"]; S.B = 10000
log = open("shoes_continue_log.txt", "a")
def L(s): log.write(s + "\n"); log.flush()
L(f"resumed from stage {st['stage']}; t0={t0:.4f}; n={S.n}")
t = round(t0, 2)
for h, nsw in [(0.46, 6), (0.23, 4)]:
    for s in range(nsw):
        S.refresh(); f0 = S.smooth_obj(t, h); S.sweep(t, h); f1 = S.smooth_obj(t, h)
        L(f"  h={h:.2f} sweep {s+1}: {f0:.3e} -> {f1:.3e}  [{int(time.time()-T0)}s]")
        S.U = S.E = S.R = None; pickle.dump({"S": S, "stage": 99}, open("ck/ck_SH0ES_mode0_skew_cont.pkl", "wb"))
np.save("laws/laws_SH0ES_mode0_skew_cont.npy", np.column_stack([S.P, S.r]))
exc = 0; done = 0; mx = 0.0
for c in range(chunks):
    hv = S.hard(1000000, seed=1000 + c)
    exc += hv["nexc"]; done += hv["B"]; mx = max(mx, hv["maxT"])
    L(f"hard eval chunk {c+1}: cumulative {exc} exceedances in {done} draws; p={exc/done:.3e}; "
      f"CP lower95={cp_lower(exc, done):.3e}; maxT so far {mx:.2f}; feasible={hv['feas']}  [{int(time.time()-T0)}s]")
L("done")
