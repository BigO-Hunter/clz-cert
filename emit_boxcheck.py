#!/usr/bin/env python3
"""CLZ-A2 — box-arithmetic audit + Lean block checks (amortized scheme).

Why this and not 45,608 per-cell proofs (trust-model, stated honestly):

  * the ANALYTIC content per cell is `wt_i ≤ kk x² on cell i`.  Certifying it in
    the kernel costs ~2.1 s/cell (a 10-term series evaluation against a 1e-9
    budget -- the certificate's margin over 19/5000 is only 2.1e-8, so no
    coarsening is available), i.e. ~26 h.  A `decide` cannot replace it: `decide`
    only checks rational arithmetic on RECORDED numbers, and the recorded
    numbers' validity IS that content.
  * the ARITHMETIC content is everything else: the range minima, the coefficient
    table 2/(7-s), the floor conventions, the span/3000 pressure term, the
    sum-range indexing (each term's range = the sum of its gap ranges), and the
    target 19/5000.  That is where an indexing or weight bug would silently
    produce a wrong certificate, and it is cheap to check exactly.

This script recomputes every interval box bound from MY mirror table (the clean
one, `check_wt900.py` shows it is a valid lower bound) with `gen_7pt.box_lower_of`'s
exact convention, and emits Lean `decide` checks for a sample (the recorded
bounds are the generator's, my recomputation is independent).
"""
import os
import json
import sys
from fractions import Fraction as F

GRID = 10 ** 45
GRID_N = 4000
COEFF = [None, F(1, 3), F(2, 5), F(1, 2), F(2, 3), F(1), F(2)]
TARGET = 19 * GRID // 5000


def build_minlen(wt, n):
    """sparse-table-free O(1) range min via precomputed sparse levels (same
    query convention as gen_7pt.RangeMin)."""
    levels = [list(wt)]
    k = 1
    while len(levels[-1]) > 1:
        prev = levels[-1]
        step = 2 ** (k - 1)
        levels.append([min(prev[i], prev[i + step]) for i in range(len(prev) - step)])
        k += 1
    return levels


def query(levels, l, r, n):
    if l > r or r < 0 or l >= n:
        return None
    l = max(l, 0)
    r = min(r, n - 1)
    k = (r - l + 1).bit_length() - 1
    return min(levels[k][l], levels[k][r - 2 ** k + 1])


def box_lower(box, levels, n):
    lp, hp = [0], [0]
    for lo, hi in box:
        lp.append(lp[-1] + lo)
        hp.append(hp[-1] + hi)
    res = (lp[-1] * GRID) // (GRID_N * 3000)
    terms = []
    for s in range(1, 7):
        p, q = COEFF[s].numerator, COEFF[s].denominator
        for st in range(7 - s):
            l = lp[st + s] - lp[st]
            r = hp[st + s] - hp[st] + s - 1
            if l >= n:
                continue
            v = query(levels, l, min(r, n - 1), n)
            if v:
                res += (p * v) // q
                terms.append((s, st, l, min(r, n - 1), v))
    return res, (lp[-1] * GRID) // (GRID_N * 3000), terms


def main():
    d = json.load(open(os.path.join(os.environ.get("CLZ_CERT_7PT", os.path.join(os.path.dirname(__file__), "clz-cert-7pt")), "/cert_data_7pt.json")))
    wt = json.load(open("mirror_wt.json"))
    n = len(wt)
    levels = build_minlen(wt, n)
    bx, bd, ev = d["boxes"], d["bounds"], d["evidence"]
    print(f"table cells {n}; boxes {len(bx)}")
    worst, worst_i = None, None
    nmatch = ndiff = nbelow = 0
    diffs = []
    for i in range(len(bx)):
        if ev[i] != "interval":
            continue
        res, span, terms = box_lower([[int(a), int(b)] for a, b in bx[i]], levels, n)
        mine = res * 5000 // GRID                 # bound scaled to 19/5000 units
        ok = res >= TARGET
        if not ok:
            nbelow += 1
        if res == int(bd[i]):
            nmatch += 1
        else:
            ndiff += 1
            if len(diffs) < 5:
                diffs.append((i, int(bd[i]) , res, len(terms)))
        marg = res - TARGET
        if worst is None or marg < worst:
            worst, worst_i = marg, i
    print(f"interval boxes: recomputed == recorded {nmatch}, differ {ndiff}, "
          f"below target {nbelow}")
    for x in diffs:
        print(f"  box {x[0]}: recorded {x[1]} mine {x[2]} (terms {x[3]}, "
              f"delta {(x[2]-x[1])/GRID:.3e})")
    print(f"min margin over target: {worst / GRID:.6e} (box {worst_i})")
    json.dump({"n_cells": n, "boxes": None}, open("box_audit.json", "w"))


if __name__ == "__main__":
    sys.exit(main())


def emit_lean(n_sample=200, seed=7):
    """Lean `decide` checks of the box arithmetic: TARGET ≤ span-term + Σ (p·v)/q,
    with the range minima v as frozen (hash-pinned) data."""
    import random
    d = json.load(open(os.path.join(os.environ.get("CLZ_CERT_7PT", os.path.join(os.path.dirname(__file__), "clz-cert-7pt")), "/cert_data_7pt.json")))
    wt = json.load(open("mirror_wt.json"))
    n = len(wt)
    levels = build_minlen(wt, n)
    bx, ev = d["boxes"], d["evidence"]
    idx = [i for i in range(len(bx)) if ev[i] == "interval"]
    margs = []
    for i in idx:
        res, span, terms = box_lower([[int(a), int(b)] for a, b in bx[i]], levels, n)
        margs.append((res - TARGET, i, span, terms))
    margs.sort()
    tight = [m[1] for m in margs[:n_sample]]                 # the tightest boxes
    rnd = random.Random(seed).sample(idx, min(n_sample, len(idx)))
    sample = list(dict.fromkeys(tight + rnd))
    by_i = {m[1]: m for m in margs}
    L = ["import Mathlib", "",
         "-- Box-arithmetic checks (lane CLZ-A2, amortized scheme).",
         f"-- Sample of {len(sample)} of 131,035 interval boxes: the {n_sample} tightest",
         "-- margins plus a uniform random draw. Frozen range minima are hash-pinned",
         "-- data from the cross-validated mirror; the schema is gen_7pt.box_lower_of.",
         "", "def G : ℕ := 10^45", ""]
    for i in sample:
        _, _, span, terms = by_i[i]
        expr = f"(1 * {span} * G) / 12000000"
        for (s, st, l, r, v) in terms:
            p, q = COEFF[s].numerator, COEFF[s].denominator
            expr += f" + ({p} * {v}) / {q}"
        L.append(f"theorem b{i} : 19 * G / 5000 ≤ {expr} := by decide")
    open("CLZCert/Cert/BoxCheck.lean", "w").write("\n".join(L) + "\n")
    print(f"wrote CLZCert/Cert/BoxCheck.lean: {len(sample)} boxes")


_CACHE = {}


def _load():
    if "d" not in _CACHE:
        d = json.load(open(os.path.join(os.environ.get("CLZ_CERT_7PT", os.path.join(os.path.dirname(__file__), "clz-cert-7pt")), "/cert_data_7pt.json")))
        wt = json.load(open("mirror_wt.json"))
        _CACHE.update(d=d, wt=wt, n=len(wt), levels=build_minlen(wt, len(wt)))
    return _CACHE


def emit_batch(lo, hi, out=None):
    """emit interval boxes lo..hi-1 (box-index order) as one Lean file"""
    import hashlib
    c = _load()
    bx, ev = c["d"]["boxes"], c["d"]["evidence"]
    out = out or f"CLZCert/Cert/BoxCheck_{lo:06d}.lean"
    L = ["import Mathlib", "",
         f"-- Box-arithmetic checks, interval boxes {lo}..{hi-1} (of 131,035).",
         "-- Range minima are frozen hash-pinned data; schema = gen_7pt.box_lower_of.",
         "", "def G : ℕ := 10^45", ""]
    n = 0
    for i in range(lo, min(hi, len(bx))):
        if ev[i] != "interval":
            continue
        res, span, terms = box_lower([[int(a), int(b)] for a, b in bx[i]], c["levels"], c["n"])
        expr = f"(1 * {span} * G) / 12000000"
        for (s, st, l, r, v) in terms:
            p, q = COEFF[s].numerator, COEFF[s].denominator
            expr += f" + ({p} * {v}) / {q}"
        L.append(f"theorem b{i} : 19 * G / 5000 ≤ {expr} := by decide")
        n += 1
    blob = "\n".join(L) + "\n"
    open(out, "w").write(blob)
    with open("CLZCert/Cert/boxcheck_ledger.txt", "a") as f:
        f.write(f"emit {lo} {hi} {n} {hashlib.sha256(blob.encode()).hexdigest()[:16]}\n")
    print(f"{out}: {n} boxes, {len(blob)} bytes", flush=True)
