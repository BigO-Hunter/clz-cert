import gen_cert as g, time, sys
from fractions import Fraction as F
orig = g.k2_cached
count = [0]
def counted(lo, hi):
    count[0] += 1
    if count[0] % 20000 == 0:
        print(f"  k2 evals: {count[0]}  cache: {len(g._CACHE)}  t={time.time()-T0:.0f}s", flush=True)
    return orig(lo, hi)
T0 = time.time()
g.k2_cached = counted
g.box_bound.__globals__['k2_cached'] = counted
boxes = g.cover2(F(2213813, 10**10))
emin = min(b[4] for b in boxes)
print(f"DONE boxes={len(boxes)} evals={count[0]} t={time.time()-T0:.0f}s emin={float(emin)*1e6:.4f}e-6 need>=221.3813", flush=True)
