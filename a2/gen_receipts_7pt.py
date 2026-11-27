#!/usr/bin/env python3
"""7-pt receipt emitter: reads the sibling lane's cert_data_7pt.json +
tables_7pt.pkl (READ-ONLY) and emits Lean receipt files into ./CLZCert/Cert/.

Stages:
  cells  [a b)  -- wcell_i theorems (45,608 table cells)
  queries       -- segment-tree wrange theorems over the 13,500 distinct
                   sum-ranges of the interval boxes (+ one-body ranges)
  boxes  [a b)  -- per-box assemblies (interval-evidence boxes)
  combos        -- per-initial-combo dispatch subtrees + top dispatch +
                   pressure + one-body + discharge (needs all previous)
Mirror discipline: every emitted real literal is derived OUTWARD with the
Lean-visible 20-digit constants (pi, 1/sqrt2, Kfn0 interval) on the 1e-45
grid; each cell receipt is verified against the sibling's table value and
each box bound against 19/5000 -- a failed verification STOPS that stage.
"""
from fractions import Fraction as F
import math, json, pickle, sys, os

SIB = os.environ.get("CLZ_CERT_7PT", os.path.join(os.path.dirname(__file__), "..", "clz-cert-7pt"))
OUT = "CLZCert/Cert"
G45 = 10 ** 45
GN = 4000
TARGET = F(19, 5000)

# Lean-visible constants (20-digit)
PLO = F(314159265358979323846, 10 ** 20)
PHI = F(314159265358979323847, 10 ** 20)
ALO = F(7071067811865475244, 10 ** 19)
AHI = F(7071067811865475245, 10 ** 19)
K0LO = F(int("918725369860555949800554150691128408603149501"), G45)
K0HI = F(int("918725369865574401307762900255801616701254273"), G45)
CHIG = (PHI / 2) ** 21 / F(math.factorial(21))
PI_UB_HALF = PHI / 2

def slo(x): return F(x.numerator * G45 // x.denominator, G45)
def shi(x): return F(-((-x.numerator * G45) // x.denominator), G45)

def dec(x):
    """exact terminating decimal string for x (den only 2s and 5s)"""
    d = x.denominator
    k = 0
    while d % 2 == 0: d //= 2; k += 1
    while d % 5 == 0: d //= 5; k += 1
    assert d == 1, f"non-terminating {x}"
    num = x.numerator * (10 ** k) // x.denominator
    if k == 0:
        return str(num)
    s = str(abs(num)).rjust(k + 1, "0")
    return ("-" if num < 0 else "") + s[:-k] + "." + s[-k:]

# ---- outward interval core (mirrors the Lean linarith/lemma steps) ----
def I_mul(a, b):  # both nonneg-or-any, outward
    c = (a[0]*b[0], a[0]*b[1], a[1]*b[0], a[1]*b[1])
    return slo(min(c)), shi(max(c))

def sandwich_bounds(s0, s1):
    """P, Q certified bounds of sin(pi*w) for w in [s0, s1], |s| <= 1/2.
    Returns exact Fractions."""
    assert -F(1,2) <= s0 <= s1 <= F(1,2), (s0, s1)
    if s0 >= 0:
        TL = lambda m: (PLO * s0) ** m
        TU = lambda m: (PHI * s1) ** m
    elif s1 <= 0:
        TL = lambda m: (PHI * s0) ** m
        TU = lambda m: (PLO * s1) ** m
    else:
        raise AssertionError("straddling window must be split")
    P = F(0); Q = F(0)
    for k in range(10):
        c = F((-1) ** k, math.factorial(2 * k + 1))
        m = 2 * k + 1
        if k % 2 == 0:
            P += c * TL(m); Q += c * TU(m)
        else:
            P += c * TU(m); Q += c * TL(m)
    return P - CHIG, Q + CHIG

def sinc_bracket_piece(j, s0, s1, tlo, thi):
    """sinc bounds over the piece t in [tlo,thi] = pi*(j+[s0,s1]).
    Returns (lo, hi, P, Q) exact/outward."""
    P, Q = sandwich_bounds(s0, s1)
    if j % 2:
        P, Q = -Q, -P
    cands = [P / thi, P / tlo, Q / thi, Q / tlo]
    return slo(min(cands)), shi(max(cands)), P, Q

def decompose(t0, t1):
    """[t0,t1] -> list of (j, s0, s1, tlo, thi) non-straddling pieces
    (all exact Fractions, outward)."""
    pieces = []
    j0 = int((float(t0) / float(math.pi)) // 1) - 2
    j = j0
    while True:
        clo = (F(2 * j - 1, 2)) * math.pi if False else F(2 * j - 1) / 2 * PLO
        chi = F(2 * j + 1) / 2 * PHI
        lo = max(t0, clo); hi = min(t1, chi)
        if lo <= hi:
            # straddle check against j*pi
            jpi_lo = F(j) * PLO; jpi_hi = F(j) * PHI
            if lo < jpi_hi and hi > jpi_lo:
                # split at j*pi: sub [lo, j*pi_lo], [j*pi_hi, hi]
                a1 = min(lo, jpi_lo); b1 = jpi_lo
                a2 = jpi_hi; b2 = max(hi, jpi_hi)
                if a1 <= b1:
                    s0 = slo(a1 / PHI - j); s1 = shi(b1 / PLO - j)
                    s0 = max(s0, -F(1,2)); s1 = min(s1, F(1,2))
                    if s0 <= s1:
                        pieces.append((j, s0, s1, slo(a1), shi(b1)))
                if a2 <= b2:
                    s0 = slo(a2 / PHI - j); s1 = shi(b2 / PLO - j)
                    s0 = max(s0, F(0)); s1 = min(s1, F(1,2))
                    if s0 <= s1:
                        pieces.append((j, s0, s1, slo(a2), shi(b2)))
            else:
                s0 = slo(lo / PHI - j); s1 = shi(hi / PLO - j)
                s0 = max(s0, -F(1, 2)); s1 = min(s1, F(1, 2))
                if s0 <= s1:
                    pieces.append((j, s0, s1, slo(lo), shi(hi)))
        if chi > t1 and j > j0 + 1: break
        if j > j0 + 40: break
        j += 1
    return pieces

def sinc_interval(t0, t1):
    """sinc bounds over [t0,t1] (t0 > 0), outward; merges pieces."""
    lo = None; hi = None
    for (j, s0, s1, tlo, thi) in decompose(t0, t1):
        plo_, phi_, P, Q = sinc_bracket_piece(j, s0, s1, tlo, thi)
        lo = plo_ if lo is None else min(lo, plo_)
        hi = phi_ if hi is None else max(hi, phi_)
    return lo, hi

def k2_lower(x0, x1):
    """kk^2 lower bound over x in [x0,x1] (x0 >= 0), outward; returns
    (w, KL, KH, KKl, KKh, brackets) for emission."""
    t1lo = slo(x0 * PLO) - AHI
    t1hi = shi(x1 * PHI) - ALO
    t2lo = slo(x0 * PLO) + ALO
    t2hi = shi(x1 * PHI) + AHI
    reflected = t1lo < 0
    if reflected:
        # |t1| <= M: reflected cells have |t1| <= a < 1, so sinc is covered
        # by the near-1 bracket on [0,M] in one shot. (The earlier far-piece
        # split bracketed P/t as an INDEPENDENT product, losing the t = pi*s
        # coupling: at cell 900 it gave sinc in [0.5,2.0] instead of ~1 --
        # sound but 0.43-wide; the near-1 bracket is tight. Task-0 note: the
        # sibling's wt[900]=7.58e74 is garbage-HIGH (S_reduce straddle bug),
        # the pre-fix mirror here was garbage-LOW (0.42 vs true ~0.854);
        # true w(cell 900) ~= 0.854.)
        M = max(-t1lo, t1hi, F(0))
        assert M <= 1, f"reflected cell wider than 1: {float(M)}"
        near_lo = 1 - M ** 2 / 6 - M ** 4 / 120
        lo1 = near_lo; hi1 = F(1)
        K1 = (lo1, hi1)
        br1 = ("reflected", M)
    else:
        lo1, hi1 = sinc_interval(t1lo, t1hi)
        br1 = ("direct",)
        assert lo1 is not None
    lo2, hi2 = sinc_interval(t2lo, t2hi)
    KLo = slo((lo1 + lo2) / 2); KHi = shi((hi1 + hi2) / 2)
    # kk = K / K0 in [K0LO, K0HI]
    cands = [KLo / K0LO, KLo / K0HI, KHi / K0LO, KHi / K0HI]
    kkl = slo(min(cands)); kkh = shi(max(cands))
    if kkl >= 0:
        w = kkl * kkl
    elif kkh <= 0:
        w = kkh * kkh
    else:
        w = F(0)
    return max(w, F(0)), (t1lo, t1hi), (t2lo, t2hi), (KLo, KHi), (kkl, kkh), br1, reflected

# ---------- load data ----------
def load():
    d = json.load(open(os.path.join(SIB, "cert_data_7pt.json")))
    t = pickle.load(open(os.path.join(SIB, "tables_7pt.pkl"), "rb"))
    return d, t

CELL_DEC = None  # decimal cache for cell bounds

def cell_lo(i): return F(i, GN) - F(2, G45)
def cell_hi(i): return F(i + 1, GN) + F(2, G45)

# ---------- Lean emission: one sinc_bracket piece block ----------
COEF_TXT = {1: "1/3", 2: "2/5", 3: "1/2", 4: "2/3", 5: "1", 6: "2"}

def emit_term_facts(ind, wv, s0, s1, P, Q, tlo, thi, j):
    """emits the hser proof block; returns list of lines"""
    L = []
    p = ind
    s0d, s1d = dec(s0), dec(s1)
    if s0 >= 0:
        lb, lbn = "((3.14159265358979323846:ℝ) * " + s0d + ")", "plo0"
        ub, ubn = "((3.14159265358979323847:ℝ) * " + s1d + ")", "phi1"
        lnn, unn = "plo*↑s0", "phi*↑s1"
    else:
        lb, ub = "((3.14159265358979323847:ℝ) * " + s0d + ")", "((3.14159265358979323846:ℝ) * " + s1d + ")"
        lnn, unn = "phi*↑s0", "plo*↑s1"
    L.append(f"{p}have hπw : ({lb}) ≤ π * {wv} ∧ π * {wv} ≤ ({ub}) := by")
    if s0 >= 0:
        L.append(f"{p}  constructor")
        L.append(f"{p}  · exact le_trans (mul_le_mul_of_nonneg_right (le_of_lt pi_lb) (by norm_num)) (mul_le_mul_of_nonneg_right {wv+'h0'} (by nlinarith [pi_lb]))")
        L.append(f"{p}  · exact mul_le_mul_of_nonneg_right {wv+'h1'} (by nlinarith [pi_lb])")
    else:
        L.append(f"{p}  constructor")
        L.append(f"{p}  · exact le_trans (mul_le_mul_of_nonneg_right {wv+'h0'} (by nlinarith [pi_ub])) (mul_le_mul_of_nonpos_right (le_of_lt pi_ub) (by nlinarith [pi_ub]))")
        L.append(f"{p}  · exact mul_le_mul_of_nonneg_right {wv+'h1'} (by nlinarith [pi_lb])")
    # 10 term facts
    for k in range(10):
        m = 2 * k + 1
        L.append(f"{p}have t{m} : ({lb})^{m} ≤ (π * {wv})^{m} ∧ (π * {wv})^{m} ≤ ({ub})^{m} :=")
        L.append(f"{p}  ⟨pow_le_pow_left₀ (by nlinarith [pi_lb]) hπw.1 {m}, pow_le_pow_left₀ (by nlinarith [pi_lb]) hπw.2 {m}⟩")
    L.append(f"{p}have habs : |{wv}| ≤ 1/2 := by rw [abs_le]; constructor <;> linarith")
    L.append(f"{p}have hsw := sin_series_sandwich (π * {wv}) (by rw [abs_mul, abs_of_nonneg (le_of_lt pi_lb)]; nlinarith [habs, pi_ub])")
    # hP9 / hQ9 numeric identities
    pos_terms, neg_terms = [], []
    for k in range(10):
        m = 2 * k + 1
        num = lb if k % 2 == 0 else ub
        term = f"({num})^{m}/{math.factorial(m)}"
        (pos_terms if k % 2 == 0 else neg_terms).append(term)
    expr_lo = " + ".join(pos_terms) if pos_terms else "0"
    expr_hi = " + ".join(neg_terms) if neg_terms else "0"
    L.append(f"{p}have hP9 : ({dec(P)}) ≤ {expr_lo} - ({expr_hi}) - chiG := by")
    L.append(f"{p}  simp only [chiG]; norm_num")
    L.append(f"{p}have hQ9 : {expr_lo} - ({expr_hi}) + chiG ≤ ({dec(Q)}) := by")
    L.append(f"{p}  simp only [chiG]; norm_num")
    low_in = [f"t{2*k+1}.1" for k in range(0, 10, 2)] + [f"t{2*k+1}.2" for k in range(1, 10, 2)]
    up_in = [f"t{2*k+1}.2" for k in range(0, 10, 2)] + [f"t{2*k+1}.1" for k in range(1, 10, 2)]
    L.append(f"{p}constructor")
    L.append(f"{p}  · linarith [hsw.1, hP9, {', '.join(low_in)}]")
    L.append(f"{p}  · linarith [hsw.2, hQ9, {', '.join(up_in)}]")
    return L

def emit_piece_bracket(ind, tvar, j, s0, s1, tl_dec, th_dec, P, Q, lo, hi, tl_expr, th_expr, first_is_symbolic):
    """emits a sinc_bracket application block; returns lines (the have is
    named by caller). tl/th given as expressions (strings)."""
    L = []
    p = ind
    jd = f"({j} : ℤ)"
    s0d, s1d = dec(s0), dec(s1)
    # htl0
    L.append(f"{p}(htl0 := by")
    L.append(f"{p}  have hr : ((3.14159265358979323846:ℝ) * ({tl_dec})) > ((0.7071067811865475245:ℝ)) := by norm_num")
    L.append(f"{p}  linarith)")
    # hmem
    L.append(f"{p}(hmem := by")
    L.append(f"{p}  intro t ha hb")
    L.append(f"{p}  constructor")
    if s0 >= 0:
        L.append(f"{p}  · rw [le_div_iff₀ (by nlinarith [pi_lb])]")
        L.append(f"{p}    have h1 : (({F(j)+F(s0,1)} : ℤ) : ℝ)?? ")
    L.append("PLACEHOLDER")
    return L
