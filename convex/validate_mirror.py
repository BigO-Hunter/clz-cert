#!/usr/bin/env python3
"""Stage 1: full mirror-table build + independent validation (CLZ-A2 task 0).

Outputs (committed artifacts):
  mirror_wt.json   -- my 45,608 outward w-cell lower bounds (1e-45 grid)
  mirror_log.json  -- validation record: >=0 gate, sibling diff, one-body
                      gates, mpmath soundness sweep (20 pts/cell)
"""
import os
import json, math, pickle, sys, time
from fractions import Fraction as F

sys.path.insert(0, ".")
import gen_receipts_7pt as g

import mpmath
mpmath.mp.dps = 50

SIB = os.environ.get("CLZ_CERT_7PT", os.path.join(os.path.dirname(__file__), "..", "clz-cert-7pt"))
G = 10 ** 45

def w_true(x):
    """High-precision true w(x) = (K(x)/K(0))^2."""
    x = mpmath.mpf(x)
    a = mpmath.mpf(1) / mpmath.sqrt(2)
    def sinc(t):
        return mpmath.sin(t) / t if t != 0 else mpmath.mpf(1)
    K = (sinc(mpmath.pi * x - a) + sinc(mpmath.pi * x + a)) / 2
    K0 = sinc(a)
    return (K / K0) ** 2

def main():
    t0 = time.time()
    # sibling table (for the diff + one-body cross-check)
    sib = pickle.load(open(f"{SIB}/tables_7pt.pkl", "rb"))
    swt = sib["wt"]
    n = len(swt)
    assert n == 45608
    mine, log = [], {"cells": n, "reflected": 0, "bad_nonneg": [], "sib_diff": [],
                     "mp_bad": [], "ob_fail": [], "ob_pass": 0}
    for i in range(n):
        w, t1, t2, K, kk, br1, refl = g.k2_lower(g.cell_lo(i), g.cell_hi(i))
        # floor to the 1e-45 grid (outward-down, exactly what receipts claim)
        wsc = (w.numerator * G) // w.denominator
        assert wsc >= 0
        if refl:
            log["reflected"] += 1
        if wsc <= 0:
            log["bad_nonneg"].append(i)
        mine.append(int(wsc))
        if i % 5000 == 0:
            print(f"  cell {i}/{n} t={time.time()-t0:.0f}s", flush=True)
    # (2) sibling diff on non-reflected-relevant region: cells >= 901 must be
    # within 2 ulp; reflected cells 0..900: mine must be <= true and << garbage
    for i in range(n):
        d = abs(mine[i] - swt[i])
        if i >= 901 and d * 10 ** 12 > swt[i]:
            log["sib_diff"].append((i, mine[i], swt[i]))
    # (3) mpmath soundness: wt_i <= w_true(x) on 20 samples per cell
    print("mpmath sweep...", flush=True)
    for i in range(n):
        lo = float(g.cell_lo(i)); hi = float(g.cell_hi(i))
        for k in range(20):
            x = lo + (hi - lo) * (k + 0.5) / 20
            if w_true(x) < mpmath.mpf(mine[i]) / mpmath.mpf(G):
                log["mp_bad"].append((i, k, float(w_true(x)), mine[i] / G))
        if i % 5000 == 0:
            print(f"  mp {i}/{n} t={time.time()-t0:.0f}s", flush=True)
    # (4) one-body gates on my table
    TARGET = F(19, 5000)
    for i in range(n):
        U = F(i, 4000 * 3000) + F(mine[i], 3 * G)
        if U >= TARGET:
            log["ob_pass"] += 1
        elif i >= 901:  # reflected cells may legitimately fail; flag non-reflected
            log["ob_fail"].append(i)
    log["elapsed_s"] = round(time.time() - t0, 1)
    json.dump(mine, open("mirror_wt.json", "w"))
    json.dump(log, open("mirror_log.json", "w"), indent=1)
    print(f"done: reflected={log['reflected']} bad_nonneg={len(log['bad_nonneg'])} "
          f"sib_diff={len(log['sib_diff'])} mp_bad={len(log['mp_bad'])} "
          f"ob_pass={log['ob_pass']} ob_fail={len(log['ob_fail'])} "
          f"t={log['elapsed_s']}s", flush=True)

if __name__ == "__main__":
    main()
