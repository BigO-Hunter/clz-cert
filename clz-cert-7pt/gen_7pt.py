#!/usr/bin/env python3
"""CLZ 7-point certificate generator (exact rational interval arithmetic).

Target (Jo / ainta zeta-simple-zeros, board row 2):
  F6(g1..g6) = sum_i g_i/3000
             + sum_{s=1..6} (2/(7-s)) * sum_{i=1..7-s} w(g_i+...+g_{i+s-1})
  >= 19/5000   for all g_i >= 0,   where w = k^2, k = K/K(0),
  K = 1/2[sinc(pi x - 1/sqrt2) + sinc(pi x + 1/sqrt2)].

Algorithm = Jo's verifier (docs/verifier.md "7-point search") with every
enclosure EXACT rational (scaled by GRID=1e-45):
  `tables`: certified w-lower cell table on [0, 45608/4000], certified
      w''-lower cell table on [0.95, ...], one-body pruning
      U(g) = g/3000 + w(g)/3 < 19/5000 -> surviving components.
  `search`: 6-D bisection over the component product:
      (a) pressure prune: sum g_lo >= 45600 cells -> sum/3000 >= 19/5000,
      (b) interval prune: box lower bound (21 range minima, all rounded
          down) >= target,
      (c) tangent prune: convexity via exact LDL on the lower-bound
          Hessian (Loewner-sound: true Hessian - lower matrix is a sum
          of PSD rank-1 terms), then f(mid)-sum|grad|*r >= target.
LAW (3-point 34.7M-box bug): prune boxes outside the domain BEFORE any
min-reduction; here the same class is the pressure cutoff + one-body
pruning, both applied before the 6-D product is formed.
"""
from fractions import Fraction as F
import math, json, time, sys, pickle, itertools

# ---------- certified enclosures (identical constants to gen_cert.py) ----------
PLO = F(314159265358979323846264338327950288, 10**35)
PHI = F(314159265358979323846264338327950289, 10**35)
S2LO = F(1414213562373095048801688724209698, 10**33)
S2HI = F(1414213562373095048801688724209699, 10**33)
ALO, AHI = F(1, 1) / S2HI, F(1, 1) / S2LO          # 1/sqrt2

GRID = 10**45
def fsc(x):   return -((-x.numerator * GRID) // x.denominator)   # round up
def fscd(x):  return x.numerator * GRID // x.denominator         # round down

PLOs, PHIs = fscd(PLO), fsc(PHI)
ALOs, AHIs = fscd(ALO), fsc(AHI)

def S_add(a, b): return a[0] + b[0], a[1] + b[1]
def S_mul(a, b):
    c = (a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])
    return min(c) // GRID, -((-max(c)) // GRID)
def S_scal(c, a):
    if c >= 0: return c * a[0], c * a[1]
    return c * a[1], c * a[0]
def S_pow(a, n):
    r = (GRID, GRID)
    for _ in range(n): r = S_mul(r, a)
    return r
def S_div(a, b):
    cands = []
    for x in a:
        n = x * GRID
        for y in b:
            cands.append((n // y, -((-n) // y)))
    return min(c[0] for c in cands), max(c[1] for c in cands)

SIN_KEEP = 10
FACT = [math.factorial(k) for k in range(2 * SIN_KEEP + 3)]

def _series(T, kind, keep):
    """Alternating-series bound: sin (kind=0, powers 2k+1) / cos (kind=1,
    powers 2k) on scaled interval T, first-omitted-term tail."""
    tot_lo = tot_hi = 0
    for k in range(keep):
        d = FACT[2 * k + 1 - kind]
        lo, hi = S_pow(T, 2 * k + 1 - kind)
        tlo = lo // d if lo >= 0 else -((-lo) // d)
        thi = hi // d if hi >= 0 else -((-hi) // d)
        if k % 2 == 0: tot_lo += tlo; tot_hi += thi
        else: tot_lo -= thi; tot_hi -= tlo
    m = max(abs(T[0]), abs(T[1]))
    p = 2 * keep + 1 - kind
    mm = S_pow((-m, m), p)
    chi = -((-max(abs(mm[0]), abs(mm[1]))) // FACT[p])
    return tot_lo - chi, tot_hi + chi

def S_reduce(T):
    """Scaled T -> [(j, s-interval, t-sub)], T = union of tsubs,
    tsub = pi*(j+s), s in [-1/2,1/2]."""
    mid = (T[0] + T[1]) // 2
    j0 = int(math.floor(mid / math.pi / GRID))
    slo0 = T[0] * GRID // PHIs if T[0] >= 0 else T[0] * GRID // PLOs
    shi0 = -((-T[1] * GRID) // PLOs) if T[1] >= 0 else -((-T[1] * GRID) // PHIs)
    H = GRID // 2
    pieces = []
    j = j0 - 2
    while True:
        slo = max(slo0 - j * GRID, -H)
        shi = min(shi0 - j * GRID, H)
        if slo <= shi:
            tlo_w = (2 * j - 1) * PLOs // 2
            thi_w = -((-((2 * j + 1) * PHIs)) // 2)
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
        lb = GRID - T2 * T2 * 10 // 57
        return lb, min(GRID, lb + 2 * T2 * T2 // GRID)
    out = None
    for j, s, tsub in S_reduce(T):
        p4 = (s[0] * PLOs, s[0] * PHIs, s[1] * PLOs, s[1] * PHIs)
        Tpi = (min(p4) // GRID, -((-max(p4)) // GRID))
        sb = _series(Tpi, 0, SIN_KEEP)
        if j % 2: sb = (-sb[1], -sb[0])
        lo, hi = S_div(sb, tsub)
        out = (lo, hi) if out is None else (min(out[0], lo), max(out[1], hi))
    return out

def S_sinc(T):
    if not (T[0] <= 0 <= T[1]) and (T[1] - T[0]) <= 64 * GRID:
        return _sinc_piece(T)
    pieces = [T]; out = None
    while pieces:
        p = pieces.pop()
        crossing = p[0] <= 0 <= p[1]
        wide = (p[1] - p[0]) > 64 * GRID
        if (crossing and max(abs(p[0]), abs(p[1])) > GRID) or wide:
            m = (p[0] + p[1]) // 2
            pieces.append((p[0], m)); pieces.append((m, p[1]))
            continue
        lo, hi = _sinc_piece(p)
        out = (lo, hi) if out is None else (min(out[0], lo), max(out[1], hi))
    return out

def _sincD_piece(T, order):
    """sinc', sinc'' on scaled interval T avoiding 0.
    u = pi*(j+s):  sinc' = (-1)^j [u cos(pi s) - sin(pi s)]/u^2
                   sinc''= (-1)^j [sin(pi s)(2-u^2)/u^3 - 2 cos(pi s)/u^2]"""
    assert not (T[0] <= 0 <= T[1]), "derivative across removable singularity"
    out = None
    for j, s, u in S_reduce(T):
        p4 = (s[0] * PLOs, s[0] * PHIs, s[1] * PLOs, s[1] * PHIs)
        Spi = (min(p4) // GRID, -((-max(p4)) // GRID))
        sb = _series(Spi, 0, SIN_KEEP)
        cb = _series(Spi, 1, SIN_KEEP)
        if order == 1:
            num = S_add(S_mul(u, cb), (-sb[1], -sb[0]))
            den = S_mul(u, u)
        else:
            u2 = S_mul(u, u)
            t1 = S_div(S_mul(sb, S_add((2 * GRID, 2 * GRID),
                                       (-u2[1], -u2[0]))), S_mul(u2, u))
            t2 = S_div((-cb[1], -cb[0]), u2)
            num = S_add(t1, S_scal(2, t2)); den = (GRID, GRID)
        lo, hi = S_div(num, den)
        if j % 2: lo, hi = -hi, -lo
        out = (lo, hi) if out is None else (min(out[0], lo), max(out[1], hi))
    return out

def _sincD(T, order):
    if (T[1] - T[0]) <= 64 * GRID:
        return _sincD_piece(T, order)
    pieces = [T]; out = None
    while pieces:
        p = pieces.pop()
        if (p[1] - p[0]) > 64 * GRID:
            m = (p[0] + p[1]) // 2
            pieces.append((p[0], m)); pieces.append((m, p[1]))
            continue
        lo, hi = _sincD_piece(p, order)
        out = (lo, hi) if out is None else (min(out[0], lo), max(out[1], hi))
    return out

def K_ints(X, derivs=True):
    """K, K', K'' enclosures on scaled interval X (u = pi x +- a).
    derivs=False skips K',K'' (they hit the removable singularity when
    u crosses 0, which S_sinc alone handles fine)."""
    xlo_pi = X[0] * PLOs // GRID
    xhi_pi = -((-X[1] * PHIs) // GRID)
    u1 = (xlo_pi - AHIs, xhi_pi - ALOs)
    u2 = (xlo_pi + ALOs, xhi_pi + AHIs)
    K = S_add(S_sinc(u1), S_sinc(u2))
    K = (K[0] // 2, -((-K[1]) // 2))
    if not derivs:
        return K, None, None
    Kp = S_mul(S_add(_sincD(u1, 1), _sincD(u2, 1)), (PLOs, PHIs))
    Kp = (Kp[0] // 2, -((-Kp[1]) // 2))
    PIsq = S_mul((PLOs, PHIs), (PLOs, PHIs))
    Kpp = S_mul(S_add(_sincD(u1, 2), _sincD(u2, 2)), PIsq)
    Kpp = (Kpp[0] // 2, -((-Kpp[1]) // 2))
    return K, Kp, Kpp

S_K0 = S_sinc((ALOs, AHIs))     # K(0) = sinc(a)

def w_lower(X):
    K, _, _ = K_ints(X, derivs=False)
    k = S_div(K, S_K0)
    if k[0] > 0 or k[1] < 0:
        # min k^2 = (endpoint closest to 0)^2 = min of the products
        return max(S_mul(k, k)[0], 0)
    return 0

def w_lower2(X):
    K, Kp, Kpp = K_ints(X)
    num = S_add(S_mul(Kp, Kp), S_mul(K, Kpp))
    val = S_div(num, S_mul(S_K0, S_K0))
    return 2 * val[0]

def w_point(X):
    """(w, w', w'') enclosures on a narrow scaled interval X."""
    K, Kp, Kpp = K_ints(X)
    K02 = S_mul(S_K0, S_K0)
    w = S_div(S_mul(K, K), K02)
    wp = S_div(S_scal(2, S_mul(K, Kp)), K02)
    wpp = S_div(S_scal(2, S_add(S_mul(Kp, Kp), S_mul(K, Kpp))), K02)
    return w, wp, wpp

# ---------- parameters ----------
GRID_N = 4000
PRESSURE_CUTOFF_CELLS = 45_600
COEFF = [None, F(1, 3), F(2, 5), F(1, 2), F(2, 3), F(1), F(2)]  # 2/(7-s)
TARGET = F(19, 5000)
W2_START = 3_800

def build_tables():
    t0 = time.time()
    n = PRESSURE_CUTOFF_CELLS + 8
    wt = []
    for i in range(n):
        X = (fscd(F(i, GRID_N)) - 2, fsc(F(i + 1, GRID_N)) + 2)
        wt.append(w_lower(X))
        if (i + 1) % 4000 == 0:
            print(f"  w cells {i+1}/{n} t={time.time()-t0:.0f}s", flush=True)
    print(f"w table done t={time.time()-t0:.0f}s", flush=True)
    surv = []
    for i in range(PRESSURE_CUTOFF_CELLS):
        if F(i, GRID_N * 3000) + F(wt[i], 3 * GRID) < TARGET:
            surv.append(i)
    comps = []
    for i in surv:
        if not comps or i > comps[-1][1] + 1: comps.append([i, i])
        else: comps[-1][1] = i
    comps = [tuple(c) for c in comps]
    print("surviving components:", comps, flush=True)
    w2 = [0] * n
    for i in range(W2_START, n):
        X = (fscd(F(i, GRID_N)) - 2, fsc(F(i + 1, GRID_N)) + 2)
        w2[i] = w_lower2(X)
        if i % 4000 == 0:
            print(f"  w'' cells {i}/{n} t={time.time()-t0:.0f}s", flush=True)
    print(f"tables done t={time.time()-t0:.0f}s", flush=True)
    with open("tables_7pt.pkl", "wb") as f:
        pickle.dump({"wt": wt, "w2": w2, "comps": comps}, f, protocol=4)
    print("pickled tables_7pt.pkl", flush=True)

class RangeMin:
    def __init__(self, arr, offset=0):
        self.off = offset; self.n = len(arr)
        self.levels = [list(arr)]
        k = 1
        while len(self.levels[-1]) > 1:
            prev = self.levels[-1]; step = 2 ** (k - 1)
            self.levels.append([min(prev[i], prev[i + step])
                                for i in range(len(prev) - step)])
            k += 1
    def query(self, l, r):
        """min over inclusive cell range [l, r]; None if empty."""
        l -= self.off; r -= self.off
        if l > r or r < 0 or l >= self.n: return None
        l = max(l, 0); r = min(r, self.n - 1)
        k = (r - l + 1).bit_length() - 1
        return min(self.levels[k][l], self.levels[k][r - 2 ** k + 1])

def box_lower_of(rw, box):
    PD = GRID_N * 3000
    lp = [0]; hp = [0]
    for lo, hi in box:
        lp.append(lp[-1] + lo); hp.append(hp[-1] + hi)
    res = (lp[-1] * GRID) // PD
    for s in range(1, 7):
        p, q = COEFF[s].numerator, COEFF[s].denominator
        for st in range(7 - s):
            l = lp[st + s] - lp[st]
            r = hp[st + s] - hp[st] + s - 1
            if l >= rw.n: continue
            v = rw.query(l, min(r, rw.n - 1))
            if v: res += (p * v) // q
    return res

def ldl_pd(M):
    L = [[F(0)] * 6 for _ in range(6)]; D = [F(0)] * 6
    for c in range(6):
        piv = M[c][c]
        for p in range(c):
            piv -= L[c][p] * L[c][p] * D[p]
        if piv <= 0: return False
        D[c] = piv; L[c][c] = F(1)
        for r in range(c + 1, 6):
            v = M[r][c]
            for p in range(c):
                v -= L[r][p] * L[c][p] * D[p]
            L[r][c] = v / piv
    return True

def tangent_of(rw2, box):
    """Certified tangent lower bound (scaled int) or None."""
    lp = [0]; hp = [0]
    for lo, hi in box:
        lp.append(lp[-1] + lo); hp.append(hp[-1] + hi)
    mids = [F(lo + hi + 1, 2 * GRID_N) for lo, hi in box]
    rads = [F(hi - lo + 1, 2 * GRID_N) for lo, hi in box]
    M = [[F(0)] * 6 for _ in range(6)]
    for s in range(1, 7):
        for st in range(7 - s):
            l = lp[st + s] - lp[st]
            r = hp[st + s] - hp[st] + s - 1
            v2 = rw2.query(l, r)
            if v2 is None: return None
            sc = COEFF[s] * F(v2, GRID)
            for a in range(st, st + s):
                for b in range(st, st + s):
                    M[a][b] += sc
    Mf = [[float(x) for x in row] for row in M]
    Lf = [[0.0] * 6 for _ in range(6)]; Df = [0.0] * 6
    ok = True
    for c in range(6):
        piv = Mf[c][c]
        for p in range(c): piv -= Lf[c][p] * Lf[c][p] * Df[p]
        if piv <= 1e-12: ok = False; break
        Df[c] = piv; Lf[c][c] = 1.0
        for r in range(c + 1, 6):
            v = Mf[r][c]
            for p in range(c): v -= Lf[r][p] * Lf[c][p] * Df[p]
            Lf[r][c] = v / piv
    if not ok or not ldl_pd(M): return None
    ssum = F(0)
    for m in mids: ssum += m
    total = fscd(ssum / 3000)
    gradmag = [F(0)] * 6
    for s in range(1, 7):
        c = COEFF[s]
        for st in range(7 - s):
            ssum = F(0)
            for t in range(st, st + s): ssum += mids[t]
            Pt = (fscd(ssum) - 2, fsc(ssum) + 2)
            w, wp, _ = w_point(Pt)
            wlo = max(w[0], 0)
            total += (c.numerator * wlo) // c.denominator
            wm = c * F(max(abs(wp[0]), abs(wp[1])), GRID)
            for a in range(st, st + s):
                gradmag[a] += wm
    for a in range(6):
        r = rads[a]
        total -= -((-gradmag[a].numerator * r.numerator) //
                   (gradmag[a].denominator * r.denominator))
    return total

def run_search(node_report=20000):
    t0 = time.time()
    d = pickle.load(open("tables_7pt.pkl", "rb"))
    wt, w2, comps = d["wt"], d["w2"], d["comps"]
    rw = RangeMin(wt)
    rw2 = RangeMin(w2[W2_START:], offset=W2_START)
    tgt = -((-19 * GRID) // 5000)     # ceil(19*GRID/5000)
    PD = GRID_N * 3000

    def kernel_min(l, r):
        if l >= rw.n: return 0
        return rw.query(l, min(r, rw.n - 1))

    def box_lower(box):
        return box_lower_of(rw, box)

    def tangent(box):
        """Certified tangent lower bound (scaled int) or None."""
        return tangent_of(rw2, box)

    stats = dict(nodes=0, splits=0, maxdepth=0, pressure=0, interval=0,
                 tangent=0, initial=len(comps) ** 6)
    boxes = []
    stack = [(tuple(parts), 0) for parts in itertools.product(comps, repeat=6)]
    print(f"initial boxes: {len(stack)}  comps={comps}", flush=True)

    while stack:
        box, depth = stack.pop()
        stats["nodes"] += 1
        stats["maxdepth"] = max(stats["maxdepth"], depth)
        if stats["nodes"] % node_report == 0:
            print(f"  nodes={stats['nodes']} pending={len(stack)} "
                  f"d={stats['maxdepth']} t={time.time()-t0:.0f}s "
                  f"[pr {stats['pressure']} iv {stats['interval']} "
                  f"tg {stats['tangent']}]", flush=True)
        if sum(p[0] for p in box) >= PRESSURE_CUTOFF_CELLS:
            stats["pressure"] += 1; continue
        lo = box_lower(box)
        if lo >= tgt:
            stats["interval"] += 1
            boxes.append((box, lo)); continue
        tl = tangent(box)
        if tl is not None and tl >= tgt:
            stats["tangent"] += 1; continue
        widths = [hi - lo for lo, hi in box]
        if max(widths) == 0:
            print("FAILED terminal cell:", box, flush=True)
            json.dump({"status": "failed", "box": list(box), "lower": lo,
                       **stats}, open("search_stats.json", "w"))
            sys.exit(1)
        stats["splits"] += 1
        c = max(range(6), key=widths.__getitem__)
        l, r = box[c]; mid = (l + r) // 2
        a = list(box); b = list(box)
        a[c] = (l, mid); b[c] = (mid + 1, r)
        stack.append((tuple(a), depth + 1)); stack.append((tuple(b), depth + 1))

    stats["elapsed"] = time.time() - t0
    stats["terminal"] = len(boxes)
    emin = min((b for _, b in boxes), default=0)
    print(f"DONE nodes={stats['nodes']} boxes={len(boxes)} "
          f"eps'={float(F(emin, GRID)):.12f} (target {float(TARGET)}) "
          f"t={stats['elapsed']:.0f}s", flush=True)
    json.dump({"status": "ok", "eps_num": str(emin), "eps_den": str(GRID),
               **stats}, open("search_stats.json", "w"))
    with open("boxes_7pt.pkl", "wb") as f:
        pickle.dump(boxes, f, protocol=4)
    return boxes, stats

if __name__ == "__main__":
    stage = sys.argv[1] if len(sys.argv) > 1 else "tables"
    sys.setrecursionlimit(100000)
    if stage == "tables":
        build_tables()
    elif stage == "search":
        run_search()
    elif stage == "test":
        # quick self-checks before the long run
        print("K0 =", float(F(S_K0[0], GRID)), float(F(S_K0[1], GRID)))
        for x, expect in [(1.0, None), (0.5, None)]:
            X = (fscd(F(x).limit_denominator(10**6)) - 2,
                 fsc(F(x).limit_denominator(10**6)) + 2)
            K, Kp, Kpp = K_ints(X)
            print(f"x={x}: K~{float(F((K[0]+K[1])//2, GRID)):.6f} "
                  f"K'~{float(F((Kp[0]+Kp[1])//2, GRID)):.6f} "
                  f"K''~{float(F((Kpp[0]+Kpp[1])//2, GRID)):.6f}")
        print("w cell[4000] ([1.0,1.00025]) =", float(F(w_lower(
            (fscd(F(4000, GRID_N)) - 2, fsc(F(4001, GRID_N)) + 2)), GRID)),
            "(expect ~0.0028)")
