#!/usr/bin/env python3
"""CLZ-A2 Task 0 — table hygiene check for the CLZ-C wt table.

The sibling lane's `gen_7pt.py` computes sinc over a `_sinc_piece` whose
`S_reduce`/`S_div` call straddles 0 when the top interval of a j-piece crosses
zero (the reflected cells, where t1 = pi*x - a < 0).  Their table records
`wt[900] = 7.5788e74` -- garbage-HIGH -- and `wt[898]`, `wt[899]` far too low.

This script recomputes w from the DEFINITION at 50 digits:

    w(x) = kk(x)^2,  kk = K/K(0),  K(x) = (sinc(pi*x - a) + sinc(pi*x + a))/2,
    a = 1/sqrt(2),   sinc t = sin t / t.

Verdicts recorded in CERT_REPORT: (a) my mirror (gen_receipts_7pt.py, which
splits every j-piece at j*pi and uses the near-1 bracket for reflected cells)
is clean; (b) the sibling's garbage is sound for their certificate only
because every sum-range in their box cover is >= 120 cells wide, so a
garbage-HIGH cell can never be the min of a range -- it WOULD be unsound for
a single-cell range, hence worth fixing on their side.
"""
import json
import os
import pickle
import sys
from fractions import Fraction as F

import mpmath as mp

mp.mp.dps = 50
PI = mp.pi
A = 1 / mp.sqrt(2)


def sinc(t):
    if t == 0:
        return mp.mpf(1)
    return mp.sin(t) / t


def wfun(x):
    x = mp.mpf(x)
    K0 = (sinc(-A) + sinc(A)) / 2
    return mp.re(((sinc(PI * x - A) + sinc(PI * x + A)) / 2 / K0) ** 2)


def main():
    cells = [898, 899, 900, 901, 902]
    sib = pickle.load(open(os.path.join(os.environ.get("CLZ_CERT_7PT", os.path.join(os.path.dirname(__file__), "..", "clz-cert-7pt")), "tables_7pt.pkl"), "rb"))["wt"]
    mine = json.load(open("mirror_wt.json"))
    print(f"{'cell':>5} {'sibling wt':>24} {'my mirror':>22} {'true w (min over cell)':>26}")
    bad = 0
    for i in cells:
        lo, hi = mp.mpf(i) / 4000, mp.mpf(i + 1) / 4000
        vals = [wfun(lo + (hi - lo) * k / 64) for k in range(65)]
        true_min = min(vals)
        s = F(sib[i], 10 ** 45)          # the sibling stores integers over 10^45
        m = F(mine[i], 10 ** 45)
        flag = "" if float(s) <= float(true_min) * 1.0000001 else "  <-- loose (sound) / garbage"
        if s > 1:                        # not even a probability: garbage
            flag = "  <-- GARBAGE-HIGH (straddle bug)"
        if flag:
            bad += 1
        print(f"{i:>5} {float(s):>24.6e} {float(m):>22.12f} {float(true_min):>26.12f}{flag}")
    print()
    print(f"sibling cells above the true cell minimum: {bad}")
    print("wt[900] true w =", mp.nstr(wfun(mp.mpf(900) / 4000), 20))
    ok = True
    for i in cells:
        lo, hi = mp.mpf(i) / 4000, mp.mpf(i + 1) / 4000
        tmin = min(wfun(lo + (hi - lo) * k / 64) for k in range(65))
        ok = ok and float(F(mine[i], 10 ** 45)) <= float(tmin)
    print("my mirror is a lower bound at every listed cell:", ok)


if __name__ == "__main__":
    main()
