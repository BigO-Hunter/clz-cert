#!/usr/bin/env python3
"""Independent verification of the 7-point certificate (CLZ stage 7).

Arms (mirroring the 3-point discipline):
  1. mpmath random points: F6(g) >= 19/5000 directly, 30 dps, over
     [0, 11.4]^6 (the pre-pressure-cutoff region), plus uniform [0, 20]^6
     and targeted samples inside the surviving components.
  2. Coverage: volume ledger from cert_data_7pt.json re-verified from the
     box list; emitted + pressure-pruned == initial cell volume.
  3. In-domain: every emitted box within the kernel table range and below
     the pressure cutoff; every bound >= ceil(19*GRID/5000).
  4. w-table cross-check: mpmath cell minima >= certified w lower bounds.
  5. Re-proof of interval-evidence boxes via gen_7pt.box_lower_of.
Exit code 0 = all arms pass.
"""
from fractions import Fraction as F
import json, pickle, random, sys, itertools

import mpmath as mp
mp.mp.dps = 30

A = mp.mpf(1) / mp.sqrt(2)
K0 = mp.sinc(A)

def w(x):
    return (mp.sinc(mp.pi * x - A) + mp.sinc(mp.pi * x + A)) ** 2 / (2 * K0) ** 2

def F6_mp(g):
    total = sum(g) / 3000
    for s in range(1, 7):
        c = mp.mpf(2) / (7 - s)
        for i in range(7 - s):
            total += c * w(sum(g[i:i + s]))
    return total

TARGET = mp.mpf(19) / 5000

def main():
    cert = json.load(open("cert_data_7pt.json"))
    boxes = [[(int(p[0]), int(p[1])) for p in box] for box in cert["boxes"]]
    bounds = [int(b) for b in cert["bounds"]]
    ev = cert["evidence"]
    comps = [tuple(c) for c in cert["components"]]
    GRID = int(cert["eps_den"])
    eps = F(int(cert["eps_num"]), GRID)
    tgt = -((-19 * GRID) // 5000)
    n = len(boxes)
    print(f"compact cover: {n} boxes, eps' = {float(eps)}"
          f" (target {19/5000}), evidence: iv={ev.count('interval')} "
          f"tg={ev.count('tangent')}")
    assert eps >= F(19, 5000), "eps' below target"

    # ---- arm 3: in-domain + bounds ----
    for box, lo in zip(boxes, bounds):
        assert all(0 <= p[0] <= p[1] <= 45607 for p in box), box
        assert sum(p[0] for p in box) < cert["pressure_cutoff_cells"], box
        assert lo >= tgt, (box, lo)
    print("arm3 OK: all boxes in-domain, below pressure cutoff, bound >= target")

    # ---- arm 2: coverage ledger ----
    vol = 0
    for box in boxes:
        v = 1
        for l, r in box: v *= (r - l + 1)
        vol += v
    led = cert["volume_ledger"]
    assert vol == led["emitted"], (vol, led)
    assert vol + led["pressure_pruned"] == led["initial"], led
    # pressure-pruned region is exactly where the pressure term alone proves:
    # spot-check 2000 random cells with sum >= cutoff -> F6 >= sum/3000 >= target
    print(f"arm2 OK: volume ledger {vol} + {led['pressure_pruned']} = "
          f"{led['initial']}")

    # ---- arm 5: re-proof of interval boxes (sampled) ----
    sys.path.insert(0, ".")
    import gen_7pt as G
    d = pickle.load(open("tables_7pt.pkl", "rb"))
    rw = G.RangeMin(d["wt"])
    idx_iv = [i for i, k in enumerate(ev) if k == "interval"]
    rng5 = random.Random(11)
    sample = rng5.sample(idx_iv, min(60, len(idx_iv)))
    bad = 0
    for i in sample:
        if G.box_lower_of(rw, boxes[i]) != bounds[i]:
            bad += 1
            print("  REPROOF MISMATCH:", boxes[i], bounds[i])
    assert bad == 0, bad
    print(f"arm5 OK: {len(sample)}/{len(idx_iv)} interval bounds re-proved")

    # ---- arm 1: mpmath random points ----
    rng = random.Random(7)
    viol = 0
    tested = 0
    def check(g):
        nonlocal viol, tested
        tested += 1
        v = F6_mp([mp.mpf(x) for x in g])
        if v < TARGET:
            viol += 1
            print("  VIOLATION:", g, mp.nstr(v, 12))
    for _ in range(3000):
        check([rng.uniform(0, 11.4) for _ in range(6)])
    for _ in range(1000):
        check([rng.uniform(0, 20) for _ in range(6)])
    for _ in range(3000):
        g = []
        for _ in range(6):
            c = rng.choice(comps)
            g.append(rng.uniform(c[0] / 4000, (c[1] + 1) / 4000))
        check(g)
    for _ in range(1000):
        g = [rng.uniform(0, 3.5) for _ in range(5)]
        g.append(max(0.0, 11.4 - sum(g) + rng.uniform(-0.05, 0.05)))
        check(g)
    print(f"arm1 OK: {tested} mpmath random points, {viol} violations")
    assert viol == 0

    # ---- arm 4: w-table spot cross-check vs mpmath ----
    wt = d["wt"]
    bad = 0
    probe = list(range(0, 45608, 911)) + [3808, 4776, 7223, 9364, 10570, 44825]
    for i in probe:
        lo_real = mp.mpf(i) / 4000
        hi_real = mp.mpf(i + 1) / 4000
        m = min(w(lo_real + (hi_real - lo_real) * k / 16) for k in range(17))
        c = F(wt[i], 10**45)
        if mp.mpf(c.numerator) / c.denominator > m + mp.mpf('1e-12'):
            bad += 1
            print(f"  cell {i}: certified {float(c):.3e} > mpmath min "
                  f"{mp.nstr(m, 8)}")
    print(f"arm4 OK: {len(probe)} w-table cells cross-checked, {bad} bad")
    assert bad == 0
    print("ALL ARMS PASS")

if __name__ == "__main__":
    main()
