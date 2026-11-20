#!/usr/bin/env python3
"""Compact cover for the 7-point stage (writes cert_data_7pt.json).

Top-down re-search with the same certified prunes as the raw run: a node
is EMITTED when its interval bound or its certified tangent bound reaches
ceil(19*GRID/5000); otherwise it splits on the widest coordinate. Since
subdivision only raises the bounds (monotone range minima), this
terminates at least as fast as the raw run and emits boxes at the
coarsest provable granularity. Every emitted box carries direct evidence
(interval: bound, or tangent: exact-LDL convexity + tangent value),
so cert_data_7pt.json is self-contained.

Cross-check ledger: total cell volume of the emitted boxes must equal
the initial 729-box product volume (exact partition).
"""
from fractions import Fraction as F
import json, pickle, time, gzip, itertools

def main():
    t0 = time.time()
    import gen_7pt as G
    d = pickle.load(open("tables_7pt.pkl", "rb"))
    wt, w2, comps = d["wt"], d["w2"], d["comps"]
    rw = G.RangeMin(wt)
    rw2 = G.RangeMin(w2[G.W2_START:], offset=G.W2_START)
    tgt = -((-19 * G.GRID) // 5000)

    emitted = []
    stats = dict(nodes=0, interval=0, tangent=0)
    vol_pruned = 0
    stack = [(tuple(parts), 0) for parts in itertools.product(comps, repeat=6)]
    print(f"coarse search over {len(stack)} initial boxes", flush=True)
    while stack:
        box, depth = stack.pop()
        stats["nodes"] += 1
        if stats["nodes"] % 20000 == 0:
            print(f"  nodes={stats['nodes']} pending={len(stack)} "
                  f"emitted={len(emitted)} [iv {stats['interval']} "
                  f"tg {stats['tangent']}] t={time.time()-t0:.0f}s", flush=True)
        if sum(p[0] for p in box) >= G.PRESSURE_CUTOFF_CELLS:
            v = 1
            for l, r in box: v *= (r - l + 1)
            vol_pruned += v
            continue    # pressure-proven; nothing to emit
        lo = G.box_lower_of(rw, box)
        if lo >= tgt:
            stats["interval"] += 1
            emitted.append((box, lo, "interval")); continue
        tl = G.tangent_of(rw2, box)
        if tl is not None and tl >= tgt:
            stats["tangent"] += 1
            emitted.append((box, tl, "tangent")); continue
        widths = [hi - lo for lo, hi in box]
        if max(widths) == 0:
            print("COMPACT FAILED at single cell:", box, flush=True)
            json.dump({"status": "failed", "box": list(box)}, open(
                "compact_stats.json", "w"))
            return 1
        c = max(range(6), key=widths.__getitem__)
        l, r = box[c]; mid = (l + r) // 2
        a = list(box); b = list(box)
        a[c] = (l, mid); b[c] = (mid + 1, r)
        stack.append((tuple(a), depth + 1)); stack.append((tuple(b), depth + 1))

    # volume ledger: emitted + pressure-pruned = exact partition of initial
    vol = 0
    for box, _, _ in emitted:
        v = 1
        for l, r in box: v *= (r - l + 1)
        vol += v
    vol_init = 0
    for parts in itertools.product(comps, repeat=6):
        v = 1
        for l, r in parts: v *= (r - l + 1)
        vol_init += v
    assert vol + vol_pruned == vol_init, (vol, vol_pruned, vol_init)

    lo_iv = min((e for _, e, k in emitted if k == "interval"), default=0)
    lo_tg = min((e for _, e, k in emitted if k == "tangent"), default=None)
    out = {
        "stage": "CLZ 7-point: F6(g1..g6) >= 19/5000 for all gaps >= 0",
        "claim": "kappa_star >= (1345000*H0 - 2680)/1340003 = 0.6730085...",
        "target_num": 19, "target_den": 5000,
        "eps_num": str(min(e for _, e, _ in emitted)),
        "eps_den": str(G.GRID),
        "eps_interval_min": str(lo_iv),
        "grid": G.GRID_N, "pressure_cutoff_cells": G.PRESSURE_CUTOFF_CELLS,
        "w2_start": G.W2_START,
        "components": [list(c) for c in comps],
        "coeffs": [None, "1/3", "2/5", "1/2", "2/3", "1", "2"],
        "initial_boxes": 729,
        "nboxes": len(emitted),
        "volume_ledger": {"emitted": vol, "pressure_pruned": vol_pruned,
                          "initial": vol_init},
        "stats": stats,
        "boxes": [[[str(x) for x in p] for p in box]
                  for box, lo, ev in emitted],
        "bounds": [str(lo) for _, lo, _ in emitted],
        "evidence": [k for _, _, k in emitted],
    }
    json.dump(out, open("cert_data_7pt.json", "w"))
    with gzip.open("boxes_7pt.pkl.gz", "wb", compresslevel=6) as f:
        pickle.dump(emitted, f, protocol=4)
    import os
    print(f"DONE: {len(emitted)} compact boxes [iv {stats['interval']} "
          f"tg {stats['tangent']}], min bound="
          f"{float(F(min(e for _, e, _ in emitted), G.GRID)):.12f}, "
          f"json {os.path.getsize('cert_data_7pt.json')/1e6:.1f}MB, "
          f"t={time.time()-t0:.0f}s", flush=True)
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
