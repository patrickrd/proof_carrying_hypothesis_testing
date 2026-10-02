"""Designs exported from R (export_designs.R): X, y, a, meta(t0, v0) per exhibit row."""
import numpy as np, pandas as pd, os, glob
DD = os.path.join(os.path.dirname(os.path.abspath(__file__)), "designs")
def designs():
    D = {}
    for mf in sorted(glob.glob(os.path.join(DD, "*_meta.csv"))):
        nm = os.path.basename(mf)[:-9]
        meta = pd.read_csv(mf).iloc[0]
        X = pd.read_csv(os.path.join(DD, nm+"_X.csv")).values.astype(float)
        y = pd.read_csv(os.path.join(DD, nm+"_y.csv")).y.values.astype(float)
        a = pd.read_csv(os.path.join(DD, nm+"_a.csv")).a.values.astype(float)
        D[nm] = (X, y, a, float(meta.t0))
    return D
if __name__ == "__main__":
    for k,(X,y,a,t0) in designs().items(): print(f"{k:24s} n={len(X):5d} p={X.shape[1]:2d} t0={t0:.4f}")
