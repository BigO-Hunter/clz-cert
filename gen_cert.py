#!/usr/bin/env python3
"""CLZ 3-point certificate generator (exact rational interval arithmetic).

Architecture (mirrors the Lean consumer 1:1):
  - certified rational enclosures: pi, 1/sqrt2, a/pi
  - sin bound on any rational argument interval via j-reduction (arg = pi*(j+s),
    s in [-1/2,1/2]) + sinc-free alternating series with first-omitted-term tail
  - K(x) = 1/2(sinc(pi x - a) + sinc(pi x + a)) interval; k = K/K(0)
  - certificate: coarse 16x16 grid on [0,4]^2 (triangle selected Lean-side);
    per box the three argument intervals get adaptive 1-D leaf trees; box bound
    = min_u + min_v + min_uv over leaves; global eps' = min over boxes.
Every emitted literal is an exact Fraction; the same numbers are re-verified
in Lean by decide/norm_num (outward snapping to a 1e-45 grid keeps them finite).
Cross-check (report): mpmath 50 dps confirms containment.
"""
from fractions import Fraction as F
import math, json, time, sys

# ---------- certified enclosures (re-proved in Lean from series) ----------
PLO = F(314159265358979323846264338327950288, 10**35)
PHI = F(314159265358979323846264338327950289, 10**35)
S2LO = F(1414213562373095048801688724209698, 10**33)
S2HI = F(1414213562373095048801688724209699, 10**33)
ALO, AHI = F(1,1)/S2HI, F(1,1)/S2LO          # 1/sqrt2
APLO, APHI = ALO/PHI, AHI/PLO                # a/pi

GRID = 10**45
def snap(a):
    lo = F(a[0].numerator * GRID // a[0].denominator, GRID)
    hi = F(-((-a[1].numerator * GRID) // a[1].denominator), GRID)
    return (lo, hi)

# ---- fast scaled-interval core: endpoints are ints scaled by GRID ----
def fsc(x: F) -> int:   # Fraction -> scaled int, rounding UP (outward for hi)
    return -((-x.numerator * GRID) // x.denominator)
def fscd(x: F) -> int:  # rounding DOWN (outward for lo)
    return x.numerator * GRID // x.denominator
def g2f(x: int) -> F: return F(x, GRID)

PLOs, PHIs = fscd(PLO), fsc(PHI)      # pi enclosure, scaled
ALOs, AHIs = fscd(ALO), fsc(AHI)      # 1/sqrt2 enclosure, scaled
S2LOs = fscd(S2LO); S2HIs = fsc(S2HI)
APLOs = fscd(APLO); APHIs = fsc(APHI)

def S_add(a, b): return a[0]+b[0], a[1]+b[1]
def S_mul(a, b):
    c = [a[0]*b[0], a[0]*b[1], a[1]*b[0], a[1]*b[1]]
    return min(c)//GRID, -((-max(c))//GRID)
def S_scal(c: int, a): return c*a[0]//GRID if c > 0 else -( (-c*a[1])//GRID ), (c*a[1])//GRID if c > 0 else -((-c*a[0])//GRID)
def S_pow(a, n):
    r = (GRID, GRID)
    for _ in range(n): r = S_mul(r, a)
    return r
def S_div(a, b):
    # q = x/y for x in a, y in b (b straddles 0 never happens at call sites);
    # brute-force 4 candidates with outward floor/ceil rounding
    cands = []
    for x in a:
        n = x*GRID
        for y in b:
            cands.append((n//y, -((-n)//y)))
    return min(c[0] for c in cands), max(c[1] for c in cands)

SIN_KEEP = 10
FACT = [math.factorial(2*k+1) for k in range(SIN_KEEP+2)]
def S_series_sin(T, keep):
    """sin bound on scaled interval T via alternating series + first-omitted tail."""
    tot_lo = tot_hi = 0
    for k in range(keep):
        d = FACT[k]
        lo, hi = S_pow(T, 2*k+1)
        tlo = lo//d if lo >= 0 else -((-lo)//d)      # outward: floor / ceil(-)
        thi = hi//d if hi >= 0 else -((-hi)//d)
        if k % 2 == 0: tot_lo += tlo; tot_hi += thi
        else: tot_lo -= thi; tot_hi -= tlo
    m = max(abs(T[0]), abs(T[1]))
    mm = S_pow((-m, m), 2*keep+1)
    mm2 = max(abs(mm[0]), abs(mm[1]))
    chi = -((-mm2)//FACT[keep])                       # ceil: outward tail bound
    return tot_lo - chi, tot_hi + chi

def S_reduce(T):
    """T scaled -> list of (j, s-interval, t-subinterval) with T = union of
    t-subintervals, t-sub = pi*(j+s), s in [-1/2,1/2] (exact partition)."""
    import math as _m
    mid = (T[0] + T[1]) // 2
    j0 = int(_m.floor(mid / _m.pi / GRID))
    slo0 = T[0]*GRID//PHIs if T[0] >= 0 else T[0]*GRID//PLOs
    shi0 = -((-T[1]*GRID)//PLOs) if T[1] >= 0 else -((-T[1]*GRID)//PHIs)
    H = GRID//2
    pieces = []
    j = j0 - 2
    while True:
        slo = max(slo0 - j*GRID, -H)
        shi = min(shi0 - j*GRID, H)
        if slo <= shi:
            tlo_w = (2*j-1)*PLOs//2
            thi_w = -((-((2*j+1)*PHIs))//2)
            tsub = (max(T[0], tlo_w), min(T[1], thi_w))
            if tsub[0] <= tsub[1]:
                pieces.append((j, (slo, shi), tsub))
        if j >= j0 + 2: break
        j += 1
    return pieces

def _sinc_piece(T):
    if T[0] <= 0 <= T[1]:
        T2 = max(abs(T[0]), abs(T[1]))
        assert T2 <= GRID, "zero-crossing arg piece too wide"
        lb = GRID - T2*T2*10//57
        return lb, min(GRID, lb + 2*T2*T2//GRID)
    out_lo = out_hi = None
    for j, s, tsub in S_reduce(T):
        p4 = (s[0]*PLOs, s[0]*PHIs, s[1]*PLOs, s[1]*PHIs)
        Tpi = (min(p4)//GRID, -((-max(p4))//GRID))
        sb = S_series_sin(Tpi, SIN_KEEP)
        if j % 2: sb = (-sb[1], -sb[0])
        lo, hi = S_div(sb, tsub)
        out_lo = lo if out_lo is None else min(out_lo, lo)
        out_hi = hi if out_hi is None else max(out_hi, hi)
    return out_lo, out_hi

def S_sinc(T):
    if not (T[0] <= 0 <= T[1]) and (T[1] - T[0]) <= 64*GRID:
        return _sinc_piece(T)
    # split in t-space until every piece is acceptable
    pieces = [T]
    out_lo, out_hi = None, None
    while pieces:
        p = pieces.pop()
        crossing = p[0] <= 0 <= p[1]
        wide = (p[1] - p[0]) > 64*GRID
        if crossing and max(abs(p[0]), abs(p[1])) > GRID:
            m = (p[0] + p[1])//2
            pieces.append((p[0], m)); pieces.append((m, p[1]))
            continue
        if wide:
            m = (p[0] + p[1])//2
            pieces.append((p[0], m)); pieces.append((m, p[1]))
            continue
        lo, hi = _sinc_piece(p)
        out_lo = lo if out_lo is None else min(out_lo, lo)
        out_hi = hi if out_hi is None else max(out_hi, hi)
    return out_lo, out_hi

def S_K(X):
    t1lo = X[0]*PLOs//GRID - AHIs
    t1hi = -((-X[1]*PHIs)//GRID) - ALOs
    t2lo = X[0]*PLOs//GRID + ALOs
    t2hi = -((-X[1]*PHIs)//GRID) + AHIs
    s1 = S_sinc((t1lo, t1hi))
    s2 = S_sinc((t2lo, t2hi))
    return (s1[0]+s2[0])//2, -((-(s1[1]+s2[1]))//2)

# K(0) = sinc(a)
S_K0 = S_sinc((ALOs, AHIs))   # K(0) = 1/2[sinc(-a)+sinc(a)] = sinc(a)

def S_k2(X):
    kk = S_div(S_K(X), S_K0)
    # FIXED (R-clz S_k2 bug, found by sibling lane CLZ-C): the square's lower
    # endpoint is S_mul(kk,kk)[0] in BOTH branches; the old code returned [1]
    # (the upper endpoint) on the negative branch, overstating w there.
    if kk[0] >= 0 or kk[1] <= 0:
        return S_mul(kk, kk)[0]
    return 0

def k2_lb(xint):
    """public: rational interval -> lower bound of k^2 as Fraction (grid)."""
    X = (fscd(xint[0]) - 1, fsc(xint[1]) + 1)  # widen 2 grid units outward
    return F(S_k2(X), GRID)

# ---------- certificate ----------
RES_FLOOR = F(1, 131072)
_CACHE = {}
def k2_cached(lo: F, hi: F):
    key = (lo, hi)
    r = _CACHE.get(key)
    if r is None:
        r = k2_lb((lo, hi)); _CACHE[key] = r
    return r

def box_bound(u0, u1, v0, v1):
    return (k2_cached(u0, u1) + k2_cached(v0, v1) + k2_cached(u0+v0, u1+v1))

def cover2(target, maxdepth=48):
    """2D recursive subdivision of [0,4]^2; returns (boxes, stats)."""
    boxes = []
    sys.setrecursionlimit(100000)
    def rec(u0, u1, v0, v1, depth):
        if u0 + v0 > 4:  # box disjoint from the closed triangle
            return
        b = box_bound(u0, u1, v0, v1)
        if b >= target or depth >= maxdepth or (u1-u0) < RES_FLOOR or (v1-v0) < RES_FLOOR:
            boxes.append((u0, u1, v0, v1, b))
            return
        if u1 - u0 >= v1 - v0:
            m = (u0 + u1)/2
            rec(u0, m, v0, v1, depth+1); rec(m, u1, v0, v1, depth+1)
        else:
            m = (v0 + v1)/2
            rec(u0, u1, v0, m, depth+1); rec(u0, u1, m, v1, depth+1)
    G = 16; step = F(4, G)
    for i in range(G):
        for j in range(G):
            u0, u1, v0, v1 = i*step, (i+1)*step, j*step, (j+1)*step
            if u0 + v0 >= 4: continue
            rec(u0, u1, v0, v1, 0)
    return boxes


if __name__ == "__main__":
    t0 = time.time()
    print("K0 =", float(g2f(S_K0[0])), float(g2f(S_K0[1])), flush=True)
    import sys
    sys.setrecursionlimit(1000000)
    _orig_bb = box_bound
    _n = [0]
    def box_bound(u0, u1, v0, v1):  # noqa: F811 - progress wrapper
        _n[0] += 1
        if _n[0] % 50000 == 0:
            print(f"  bound-evals {_n[0]} t={time.time()-t0:.0f}s cache={len(_CACHE)}", flush=True)
        return _orig_bb(u0, u1, v0, v1)
    boxes = cover2(F(2213813, 10**10))
    emin = min(b[4] for b in boxes)
    print(f"boxes={len(boxes)} evals={_n[0]} time={time.time()-t0:.1f}s", flush=True)
    print("certified eps' =", emin, flush=True)
    print("  =", float(emin)*1e6, "e-6   (threshold for 6725198/1e7: 221.3812e-6)", flush=True)
    json.dump({
        "eps_num": str(emin.numerator), "eps_den": str(emin.denominator),
        "nboxes": len(boxes),
        "K0": [str(g2f(S_K0[0])), str(g2f(S_K0[1]))],
        "boxes": [[str(x) for x in b[:5]] for b in boxes],
    }, open("cert_data.json", "w"))
    print("wrote cert_data.json", flush=True)
