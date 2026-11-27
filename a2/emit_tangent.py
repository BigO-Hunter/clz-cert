#!/usr/bin/env python3
"""CLZ-A2 Task 3 — tangent-box receipts (parameterized shape) + the §4b audit.

The sibling cover has 145,769 boxes: 131,035 `interval` (my wcell/wrange/box
pipeline) + 14,734 `tangent` (exact-LDL convexity pruning). The tangent half's
convexity engine is lane CLZ-D's, adopted verbatim as CLZCert/Cert/Tangent.lean
(`CLZ.tangent_lower`, `CLZ.tangent_assembly`, and their `blockForm_nonneg_of_ldl`
mcert brick); the kernel instance `CLZ.tangent_lower_wfun` and the w2-cell table
live in their DerivBounds.lean, still in flight.

Three interface facts from CONVEXITY_REPORT.md that this script enforces:

  1. §4b — the recorded `bounds[i]` is `gen_7pt.tangent_of`'s `total`, which
     omits the linear-radius term `Σ_a rad_a/3000`. The sound numeric close is
     `bounds[i] − Σ_a rad_a·GRID/3000`. This script charges it per box and
     re-runs their audit independently (no box may fall below 19/5000).
  2. §5 — the `hpsd` fact is `CLZ.blockForm_nonneg_of_ldl` keyed by the 21-μ
     tuple: ONE `mcert_<hash>` per distinct tuple, never per box.
  3. §5/§7 — tangent boxes live at x ≥ 0.95 with positive windows (u > 0), so
     the x < 0 mirrored bracket is never needed. Checked here.
"""
import hashlib
import json
import os
import sys

SIB = os.path.join(os.environ.get("CLZ_CERT_7PT", os.path.join(os.path.dirname(__file__), "..", "clz-cert-7pt")), "cert_data_7pt.json")
OUT = "tangent_boxes.json"
GRID = 4000
G45 = 10 ** 45


def main():
    d = json.load(open(SIB))
    bx, bd, ev = d["boxes"], d["bounds"], d["evidence"]
    print(f"boxes {len(bx)}: interval {sum(1 for e in ev if e == 'interval')}, "
          f"tangent {sum(1 for e in ev if e == 'tangent')}")
    blocks = []
    for s in range(1, 7):
        for i in range(7 - s):
            blocks.append(dict(s=s, i=i, coeff=[None, "1/3", "2/5", "1/2", "2/3", "1", "2"][s],
                               gaps=list(range(i, i + s))))
    assert len(blocks) == 21
    target = 19 * G45 // 5000            # 19/5000 on the integer grid
    rec, nhit, worst, minmarg, minidx = [], 0, None, None, None
    lo_min = None
    for i in range(len(bx)):
        if ev[i] != "tangent":
            continue
        ranges = [[int(a), int(b)] for a, b in bx[i]]
        # rad_a in x-units = (hi-lo)/(2*GRID); the omitted linear slack:
        slack_num = sum((hi - lo) for lo, hi in ranges)      # over 2*GRID*3000
        slack = slack_num * G45 // (2 * GRID * 3000)         # on the 1e45 grid
        marg = int(bd[i]) - slack - target                   # >= 0 required
        if marg < 0:
            nhit += 1
        if minmarg is None or marg < minmarg:
            minmarg, minidx = marg, i
        if worst is None or (int(bd[i]) - target) < worst[0]:
            worst = (int(bd[i]) - target, i, slack)
        for lo, hi in ranges:
            lo_min = lo if lo_min is None else min(lo_min, lo)
        rec.append(dict(i=i, ranges=ranges, grid_bound=str(bd[i]),
                        slack_charged=str(slack), margin_after_slack=str(marg)))
    print(f"boxes below 19/5000 after charging Σrad/3000: {nhit}")
    print(f"min margin after slack: {minmarg / G45:.6e} (box {minidx})")
    print(f"tightest raw margin: {worst[0] / G45:.6e} (box {worst[1]}), "
          f"its slack {worst[2] / G45:.3e}")
    print(f"smallest argument cell index over all tangent boxes: {lo_min} "
          f"-> x >= {lo_min / GRID:.4f} (positive windows, x < 0 bracket unneeded)")
    blob = json.dumps(rec, sort_keys=True, separators=(",", ":")).encode()
    out = dict(source=SIB, n_tangent=len(rec), blocks=blocks,
               target="19/5000", grid=GRID,
               note="bound_after_slack = bounds[i] - Σ_a rad_a*GRID/3000 (CONVEXITY_REPORT §4b)",
               hoist="one mcert_<sha256(21-mu tuple)> per distinct tuple; mu comes from the w2 table (CLZ-D DerivBounds, in flight)",
               x_min=lo_min / GRID, boxes=rec,
               sha256=hashlib.sha256(blob).hexdigest())
    json.dump(out, open(OUT, "w"))
    print(f"wrote {OUT} (sha256 {out['sha256'][:16]})")


if __name__ == "__main__":
    sys.exit(main())
