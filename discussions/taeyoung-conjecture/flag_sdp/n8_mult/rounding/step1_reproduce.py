"""Step 1: reproduce the logged CERT value from the snapshot checkpoint."""
import numpy as np
import common

cl, coef, SQ, metaQ, pl, res = common.load_everything()
Qp, Rp = res["Qproj"], res["Rproj"]
print("logged c_certified =", res["c_certified"])

# PSD sanity of the projected iterate
minev_Q = min(np.linalg.eigvalsh((Q + Q.T) / 2).min() for Q in Qp)
minev_R = min(np.linalg.eigvalsh((R + R.T) / 2).min() for R in Rp)
print(f"min eig over Qproj blocks: {minev_Q:.3e}, Rproj: {minev_R:.3e}")

slack = common.slacks_float(coef, SQ, pl["MultS"], Qp, Rp)
print(f"recomputed min slack = {slack.min():.12e} at H={slack.argmin()}")
print(f"match logged: {abs(slack.min() - res['c_certified']):.3e}")

# how many near-active constraints?
for th in (1e-7, 1e-6, 1e-5, 1e-4):
    print(f"slacks < {th:g}: {(slack < th).sum()}")

np.save(common.os.path.join(common.DATA, "slack_float.npy"), slack)
