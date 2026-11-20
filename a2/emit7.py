#!/usr/bin/env python3
"""7-pt Lean receipt emitter (lane CLZ-A2). Stage driver:

  python3 emit7.py wcell  [start stop batch]   # wcell theorems -> Cert/Wcell_*.lean
  python3 emit7.py smoke                       # 6 sample cells -> Cert/SmokeW.lean

Mirror discipline: every real literal is derived OUTWARD from the Lean-visible
20-digit constants on the 1e-45 grid; each cell claim is verified in exact
arithmetic before emission -- a failed gate STOPS that stage.
"""
import json, math, os, sys, time
from fractions import Fraction as F

sys.path.insert(0, ".")
import gen_receipts_7pt as g

SIB = "/Users/dmitri.arkhipov/bigo-campaign/clz-cert-7pt"
CERT = "CLZCert/Cert"
GN = g.GN
G45 = g.G45

PLOs = "3.14159265358979323846"
PHIs = "3.14159265358979323847"
ALOs = "0.7071067811865475244"
AHIs = "0.7071067811865475245"
K0LO = F("0.918725369860555949800554150691128408603149501")
K0HI = F("0.918725369865574401307762900255801616701254273")
K0LOs = "0.918725369860555949800554150691128408603149501"
K0HIs = "0.918725369865574401307762900255801616701254273"
K0LOs = "0.918725369860555949800554150691128408603149501"

def rl(x):
    """real literal from exact Fraction (terminating decimal)."""
    return f"({g.dec(x)}:ℝ)"

def jr(j):
    """the integer j as Lean (J:Z) literal and real cast."""
    return f"({j}:ℤ)", f"(({j}:ℤ):ℝ)"

# ---------- t-interval pieces (direct path) ----------

def direct_pieces(t0, t1):
    """Outward sinc bracket pieces covering [t0,t1] (t0 > 0).

    P,Q are the UNFLIPPED series bounds of sin(pi*u) on the window; the
    (-1)^j parity flip belongs to the hdiv numerator only."""
    out = []
    for (j, s0, s1, tlo, thi) in g.decompose(t0, t1):
        P, Q = g.sandwich_bounds(s0, s1)
        if j % 2:
            Pn, Qn = -Q, -P
        else:
            Pn, Qn = P, Q
        cands = [Pn / thi, Pn / tlo, Qn / thi, Qn / tlo]
        lo, hi = g.slo(min(cands)), g.shi(max(cands))
        assert lo <= hi
        out.append(dict(j=j, s0=s0, s1=s1, P=P, Q=Q, tlo=tlo, thi=thi, lo=lo, hi=hi))
    assert out, (float(t0), float(t1))
    return out

def cell_t12(i):
    """outward t1 = pi*x - a, t2 = pi*x + a intervals over cell i."""
    lo, hi = g.cell_lo(i), g.cell_hi(i)
    t1lo = g.slo(lo * g.PLO) - g.AHI
    t1hi = g.shi(hi * g.PHI) - g.ALO
    t2lo = g.slo(lo * g.PLO) + g.ALO
    t2hi = g.shi(hi * g.PHI) + g.AHI
    return (t1lo, t1hi), (t2lo, t2hi)

# ---------- emitted proof blocks ----------

def emit_mem(ind, JZ, JR, j, s0, s1, tlo, thi, tag):
    """membership lemma have: s0 <= (t - j*pi)/pi <= s1 for t in [tlo,thi]."""
    assert (s0 + j) * g.PHI <= tlo and thi <= (s1 + j) * g.PLO, "mem outward facts"
    L = []
    p = ind
    s0d, s1d, tlod, thid = g.dec(s0), g.dec(s1), g.dec(tlo), g.dec(thi)
    L.append(f"{p}have h{tag}c1 : (({s0d}:ℝ) + {JZ}) * ({PHIs}:ℝ) ≤ ({tlod}:ℝ) := by norm_num")
    L.append(f"{p}have h{tag}c2 : ({thid}:ℝ) ≤ (({s1d}:ℝ) + {JZ}) * ({PLOs}:ℝ) := by norm_num")
    L.append(f"{p}have h{tag}m : ∀ t : ℝ, ({tlod}:ℝ) ≤ t → t ≤ ({thid}:ℝ) →")
    L.append(f"{p}    ({s0d}:ℝ) ≤ (t - {JR} * π) / π ∧ (t - {JR} * π) / π ≤ ({s1d}:ℝ) := by")
    L.append(f"{p}  intro t hta htb")
    L.append(f"{p}  have hrw : (t - {JR} * π) / π = t / π - {JR} := by field_simp")
    L.append(f"{p}  constructor")
    L.append(f"{p}  · rw [hrw]")
    L.append(f"{p}    have hk : (({s0d}:ℝ) + {JZ}) ≤ t / π := by")
    L.append(f"{p}      rw [le_div_iff₀ Real.pi_pos]")
    L.append(f"{p}      rcases le_or_gt 0 (({s0d}:ℝ) + {JZ}) with hh | hh")
    L.append(f"{p}      · calc (({s0d}:ℝ) + {JZ}) * π ≤ (({s0d}:ℝ) + {JZ}) * ({PHIs}:ℝ) :=")
    L.append(f"{p}          mul_le_mul_of_nonneg_left CLZ.pi_ub.le hh")
    L.append(f"{p}        _ ≤ ({tlod}:ℝ) := h{tag}c1")
    L.append(f"{p}        _ ≤ t := hta")
    L.append(f"{p}      · have hneg : (({s0d}:ℝ) + {JZ}) * π < 0 := mul_neg_of_neg_of_pos hh Real.pi_pos")
    L.append(f"{p}        linarith")
    L.append(f"{p}    linarith")
    L.append(f"{p}  · rw [hrw]")
    L.append(f"{p}    have hk : t / π ≤ (({s1d}:ℝ) + {JZ}) := by")
    L.append(f"{p}      rw [div_le_iff₀ Real.pi_pos]")
    L.append(f"{p}      have hsp : (0:ℝ) < (({s1d}:ℝ) + {JZ}) := by norm_num")
    L.append(f"{p}      calc t ≤ ({thid}:ℝ) := htb")
    L.append(f"{p}        _ ≤ (({s1d}:ℝ) + {JZ}) * ({PLOs}:ℝ) := h{tag}c2")
    L.append(f"{p}        _ ≤ (({s1d}:ℝ) + {JZ}) * π :=")
    L.append(f"{p}          mul_le_mul_of_nonneg_left CLZ.pi_lb.le hsp.le")
    L.append(f"{p}    linarith")
    return L

SIN9_EXP = ("(π * u) - (π * u)^3/6 + (π * u)^5/120 - (π * u)^7/5040 + (π * u)^9/362880"
            " - (π * u)^11/39916800 + (π * u)^13/6227020800 - (π * u)^15/1307674368000"
            " + (π * u)^17/355687428096000 - (π * u)^19/121645100408832000")

def emit_ser(ind, s0, s1, P, Q, tag):
    """hser have: for u in [s0,s1], P <= sin(pi*u) <= Q. (CLZ-A2 final: all
    decimated constants emitted as Z-cast ratios with numeral denominators,
    which linarith folds; no Real-decimal powers/equalities in norm_num.)"""
    L = []
    p = ind
    GW = 10 ** 140
    GP = 10 ** 120
    s0d, s1d = g.dec(s0), g.dec(s1)
    Pd = F(P.numerator * GP // P.denominator, GP)
    Qd = F(-((-Q.numerator * GP // Q.denominator)), GP)
    assert Pd <= P and Q <= Qd
    pos = s0 >= 0
    assert pos or (s1 <= 0), "window straddles 0"
    if pos:
        lbc, ubc = f"({g.dec(g.PLO * s0)}:\u211d)", f"({g.dec(g.PHI * s1)}:\u211d)"
        l1 = f"(by rw [show ({lbc}:\u211d) = ({PLOs}:\u211d) * ({s0d}:\u211d) from by norm_num]; exact CLZ.Cert.pi_mul_lb u ({s0d}:\u211d) ({PLOs}:\u211d) (by norm_num) hu1 (by norm_num) (by norm_num))"
        u1 = f"(by rw [show ({ubc}:\u211d) = ({PHIs}:\u211d) * ({s1d}:\u211d) from by norm_num]; exact CLZ.Cert.pi_mul_ub u ({s1d}:\u211d) ({PHIs}:\u211d) (by linarith [hu1]) hu2 (by norm_num))"
    else:
        lbc, ubc = f"({g.dec(g.PHI * s0)}:\u211d)", f"({g.dec(g.PLO * s1)}:\u211d)"
        l1 = f"(by rw [show ({lbc}:\u211d) = ({PHIs}:\u211d) * ({s0d}:\u211d) from by norm_num]; exact CLZ.Cert.pi_mul_lb_neg u ({s0d}:\u211d) ({PHIs}:\u211d) (by norm_num) hu1 (by norm_num))"
        u1 = f"(by rw [show ({ubc}:\u211d) = ({PLOs}:\u211d) * ({s1d}:\u211d) from by norm_num]; exact CLZ.Cert.pi_mul_ub_neg u ({s1d}:\u211d) ({PLOs}:\u211d) (by norm_num) hu2 (by norm_num))"
    be = (g.PLO if pos else g.PHI) * s0
    bo = (g.PHI if pos else g.PLO) * s1
    chiG = (g.PHI / 2) ** 21 / F(math.factorial(21))
    valP, valQ = F(0), F(0)
    for k in range(10):
        m = 2 * k + 1
        if k % 2 == 0:
            valP += be ** m / math.factorial(m)
            valQ += bo ** m / math.factorial(m)
        else:
            valP -= bo ** m / math.factorial(m)
            valQ -= be ** m / math.factorial(m)
    assert valP - chiG == P and valQ + chiG == Q
    wlo, whi = {}, {}
    for k in range(10):
        m = 2 * k + 1
        l_m, u_m = be ** m, bo ** m
        l_d = F(l_m.numerator * GW // l_m.denominator, GW)
        u_d = F(-((-u_m.numerator * GW // u_m.denominator)), GW)
        assert l_d <= l_m and u_m <= u_d
        wlo[m], whi[m] = l_d, u_d
    cumP, cumQ = F(0), F(0)
    cumP_k, cumQ_k = [], []
    for k in range(10):
        m = 2 * k + 1
        tp = F(wlo[m].numerator * GW // (wlo[m].denominator * math.factorial(m)), GW)
        tq = F(-((-whi[m].numerator * GW // (whi[m].denominator * math.factorial(m)))), GW)
        if k % 2 == 0:
            cumP += tp
            cumQ += tq
        else:
            cumP -= tq
            cumQ -= tp
        cumP_k.append(cumP)
        cumQ_k.append(cumQ)
    SdecP = F((valP - chiG).numerator * GP // (valP - chiG).denominator, GP)
    SdecQ = F(-((-((valQ + chiG).numerator * GP // (valQ + chiG).denominator))), GP)
    assert Pd <= SdecP, float(Pd - SdecP)
    assert SdecQ <= Qd, float(SdecQ - Qd)
    assert SdecP + chiG <= cumP_k[9], float(cumP_k[9] - chiG - SdecP)
    assert cumQ_k[9] <= SdecQ + chiG, float(SdecQ + chiG - cumQ_k[9])
    poly = SIN9_EXP
    p2 = ind + "  "
    q2 = p2 + "  "
    P0, Q0 = be.numerator, be.denominator
    R0, S0 = bo.numerator, bo.denominator

    def rz(x):
        """Z-cast ratio literal with numeral denominator (linarith-foldable)."""
        return f"((({x.numerator}:\u2124):\u211d) / ({x.denominator}:\u211d))"

    Pd_r, Qd_r = rz(Pd), rz(Qd)
    L.append(f"{p}have h{tag}e : \u2200 u : \u211d, ({s0d}:\u211d) \u2264 u \u2192 u \u2264 ({s1d}:\u211d) \u2192 {Pd_r} \u2264 sin (\u03c0*u) \u2227 sin (\u03c0*u) \u2264 {Qd_r} := by")
    L.append(f"{p2}intro u hu1 hu2")
    L.append(f"{p2}have h{tag}w : ({lbc}) \u2264 \u03c0 * u \u2227 \u03c0 * u \u2264 ({ubc}) := \u27e8{l1}, {u1}\u27e9")
    L.append(f"{p2}have h{tag}abs : |\u03c0 * u| \u2264 ({PHIs}:\u211d)/2 := by")
    L.append(f"{q2}rw [abs_le]")
    L.append(f"{q2}have hn1 : ((-{PHIs}:\u211d)/2:\u211d) \u2264 ({lbc}) := by norm_num")
    L.append(f"{q2}have hn2 : ({ubc}) \u2264 (({PHIs}:\u211d)/2:\u211d) := by norm_num")
    L.append(f"{q2}exact \u27e8by linarith [h{tag}w.1, hn1], by linarith [h{tag}w.2, hn2]\u27e9")
    mono_by = (f"(by have h2 : (\u03c0*u)^2 = |\u03c0*u|^2 := (sq_abs (\u03c0*u)).symm; rw [h2]; "
               f"exact le_trans (pow_le_pow_left\u2080 (abs_nonneg (\u03c0*u)) h{tag}abs 2) (by norm_num))")
    L.append(f"{p2}have h{tag}mono := CLZ.Cert.pow2_le_factorial_sq (\u03c0 * u) {mono_by}")
    if pos:
        L.append(f"{p2}have h{tag}chi : (\u03c0*u)^21/((21).factorial:\u211d) \u2264 chiG := by")
        L.append(f"{q2}have h1 : (\u03c0*u)^21 \u2264 |\u03c0*u|^21 := by rw [\u2190 abs_pow]; exact le_abs_self _")
        L.append(f"{q2}have h2 : |\u03c0*u|^21 \u2264 (({PHIs}:\u211d)/2)^21 := pow_le_pow_left\u2080 (abs_nonneg (\u03c0*u)) h{tag}abs 21")
        L.append(f"{q2}have h12 : (\u03c0*u)^21 \u2264 (({PHIs}:\u211d)/2)^21 := le_trans h1 h2")
        L.append(f"{q2}simp only [chiG]")
        L.append(f"{q2}exact div_le_div\u2080 (by positivity) h12 (by norm_num) (le_refl _)")
        L.append(f"{p2}have h{tag}p0 : (0:\u211d) \u2264 ({lbc}) := by norm_num")
        L.append(f"{p2}have h{tag}sw := CLZ.Cert.sin_series_sandwich_pos (\u03c0 * u) (by linarith [h{tag}w.1, h{tag}p0]) h{tag}mono chiG h{tag}chi")
    else:
        L.append(f"{p2}have h{tag}chi : (-(\u03c0*u))^21/((21).factorial:\u211d) \u2264 chiG := by")
        L.append(f"{q2}have h0 : 0 \u2264 -(\u03c0*u) := by linarith [h{tag}w.2]")
        L.append(f"{q2}have h1 : |-(\u03c0*u)| \u2264 (({PHIs}:\u211d)/2:\u211d) := by rw [abs_neg]; exact h{tag}abs")
        L.append(f"{q2}rw [abs_of_nonneg h0] at h1")
        L.append(f"{q2}have h2 : (-(\u03c0*u))^21 \u2264 (({PHIs}:\u211d)/2)^21 := pow_le_pow_left\u2080 h0 h1 21")
        L.append(f"{q2}simp only [chiG]")
        L.append(f"{q2}exact div_le_div\u2080 (by positivity) h2 (by norm_num) (le_refl _)")
        L.append(f"{p2}have h{tag}n0 : ({ubc}) \u2264 0 := by norm_num")
        L.append(f"{p2}have h{tag}sw := CLZ.Cert.sin_series_sandwich_neg (\u03c0 * u) (by linarith [h{tag}w.2, h{tag}n0]) h{tag}mono chiG h{tag}chi")
    L.append(f"{p2}have h{tag}b1 : ({lbc}) = ((({P0}:\u2124):\u211d) / (({Q0}:\u2124):\u211d)) := by norm_num")
    L.append(f"{p2}have h{tag}b2 : ({ubc}) = ((({R0}:\u2124):\u211d) / (({S0}:\u2124):\u211d)) := by norm_num")
    L.append(f"{p2}have h{tag}r1 : ((({P0}:\u2124):\u211d) / (({Q0}:\u2124):\u211d)) \u2264 \u03c0 * u := by rw [\u2190 h{tag}b1]; exact h{tag}w.1")
    L.append(f"{p2}have h{tag}r2 : \u03c0 * u \u2264 ((({R0}:\u2124):\u211d) / (({S0}:\u2124):\u211d)) := by rw [\u2190 h{tag}b2]; exact h{tag}w.2")
    for k in range(10):
        m = 2 * k + 1
        Pm, Qm = (be ** m).numerator, (be ** m).denominator
        Rm, Sm = (bo ** m).numerator, (bo ** m).denominator
        N1, D1 = wlo[m].numerator, wlo[m].denominator
        N2, D2 = whi[m].numerator, whi[m].denominator
        if m == 1:
            L.append(f"{p2}have w{tag}1a : {rz(wlo[1])} \u2264 \u03c0*u := h{tag}r1")
            L.append(f"{p2}have w{tag}1b : \u03c0*u \u2264 {rz(whi[1])} := h{tag}r2")
            continue
        L.append(f"{p2}have hbz{tag}{m} : ({N1}:\u2124) * ({Q0}^{m}:\u2124) \u2264 ({P0}^{m}:\u2124) * ({D1}:\u2124) := by norm_num")
        L.append(f"{p2}have hfe{tag}{m} : {rz(wlo[m])} \u2264 ((({P0}:\u2124):\u211d)^{m}) / ((({Q0}:\u2124):\u211d)^{m}) := by")
        L.append(f"{q2}rw [div_le_div_iff\u2080 (by norm_num) (by norm_num)]")
        L.append(f"{q2}exact_mod_cast hbz{tag}{m}")
        L.append(f"{p2}have hrw{tag}{m} : ((({P0}:\u2124):\u211d)^{m}) / ((({Q0}:\u2124):\u211d)^{m}) = ((({P0}:\u2124):\u211d) / (({Q0}:\u2124):\u211d))^{m} := by rw [div_pow]")
        L.append(f"{p2}have hbz2{tag}{m} : ({R0}^{m}:\u2124) * ({D2}:\u2124) \u2264 ({N2}:\u2124) * ({S0}^{m}:\u2124) := by norm_num")
        L.append(f"{p2}have hfe2{tag}{m} : ((({R0}:\u2124):\u211d)^{m}) / ((({S0}:\u2124):\u211d)^{m}) \u2264 {rz(whi[m])} := by")
        L.append(f"{q2}rw [div_le_div_iff\u2080 (by norm_num) (by norm_num)]")
        L.append(f"{q2}exact_mod_cast hbz2{tag}{m}")
        L.append(f"{p2}have hrw2{tag}{m} : ((({R0}:\u2124):\u211d) / (({S0}:\u2124):\u211d))^{m} = ((({R0}:\u2124):\u211d)^{m}) / ((({S0}:\u2124):\u211d)^{m}) := by rw [div_pow]")
        L.append(f"{p2}have w{tag}{m}a : {rz(wlo[m])} \u2264 (\u03c0*u)^{m} :=")
        L.append(f"{p2}  le_trans hfe{tag}{m} (le_trans (hrw{tag}{m}).le (CLZ.Cert.pow_odd_mono _ _ {m} (by norm_num) h{tag}r1))")
        L.append(f"{p2}have w{tag}{m}b : (\u03c0*u)^{m} \u2264 {rz(whi[m])} :=")
        L.append(f"{p2}  le_trans (le_trans (CLZ.Cert.pow_odd_mono _ _ {m} (by norm_num) h{tag}r2) (hrw2{tag}{m}).le) hfe2{tag}{m}")
    L.append(f"{p2}have h{tag}chain : sin9 (\u03c0 * u) = {poly} := by rfl")
    for k in range(10):
        m = 2 * k + 1
        wb = f"w{tag}{m}a" if k % 2 == 0 else f"w{tag}{m}b"
        polypart = " + ".join(
            (f"(\u03c0*u)^{2*j+1}/{math.factorial(2*j+1)}" if (2*j+1) > 1 else "(\u03c0*u)")
            for j in range(k + 1))
        prevref = f"h{tag}c{k-1}, " if k > 0 else ""
        L.append(f"{p2}have h{tag}c{k} : {rz(cumP_k[k])} \u2264 {polypart} := by linarith [{prevref}{wb}]")
        L.append(f"{p2}have h{tag}d{k} : {polypart} \u2264 {rz(cumQ_k[k])} := by linarith [{f'h{tag}d{k-1}, ' if k > 0 else ''}{wb}]")
    L.append(f"{p2}have h{tag}SP : {rz(SdecP)} + chiG \u2264 {poly} := by")
    L.append(f"{q2}have hc : {rz(SdecP)} + chiG \u2264 {rz(cumP_k[9])} := by norm_num")
    L.append(f"{q2}linarith [h{tag}c9, hc]")
    L.append(f"{p2}have h{tag}SQ : {poly} \u2264 {rz(SdecQ)} + chiG := by")
    L.append(f"{q2}have hc : {rz(cumQ_k[9])} \u2264 {rz(SdecQ)} + chiG := by norm_num")
    L.append(f"{q2}linarith [h{tag}d9, hc]")
    L.append(f"{p2}have h{tag}P : {Pd_r} \u2264 {rz(SdecP)} := by norm_num")
    L.append(f"{p2}have h{tag}Q : {rz(SdecQ)} \u2264 {Qd_r} := by norm_num")
    L.append(f"{p2}exact \u27e8by linarith [h{tag}sw.1, h{tag}chain, h{tag}SP, h{tag}P], by linarith [h{tag}sw.2, h{tag}chain, h{tag}SQ, h{tag}Q]\u27e9")
    return L

def emit_div(ind, JZ, JR, j, s0, s1, P, Q, tlo, thi, lo, hi, tag):
    """hdiv have: lo <= (-1)^j * sin(pi*((t-j*pi)/pi))/t <= hi on [tlo,thi]."""
    L = []
    p = ind
    tlod, thid, lod, hid = g.dec(tlo), g.dec(thi), g.dec(lo), g.dec(hi)
    odd = j % 2 != 0
    Pn, Qn = (-Q, -P) if odd else (P, Q)
    Pnd, Qnd = g.dec(g.slo(Pn)), g.dec(g.shi(Qn))
    assert g.slo(min([Pn/thi, Pn/tlo, Qn/thi, Qn/tlo])) == lo
    assert g.shi(max([Pn/thi, Pn/tlo, Qn/thi, Qn/tlo])) == hi
    sign_lit = "1" if not odd else "-1"
    # corner facts first (pure literals)
    L.append(f"{p}have h{tag}1 : ({lod}:\u211d) \u2264 ({Pnd}:\u211d) / ({thid}:\u211d) := by norm_num")
    L.append(f"{p}have h{tag}2 : ({lod}:\u211d) \u2264 ({Pnd}:\u211d) / ({tlod}:\u211d) := by norm_num")
    L.append(f"{p}have h{tag}3 : ({Qnd}:\u211d) / ({tlod}:\u211d) \u2264 ({hid}:\u211d) := by norm_num")
    L.append(f"{p}have h{tag}4 : ({Qnd}:\u211d) / ({thid}:\u211d) \u2264 ({hid}:\u211d) := by norm_num")
    L.append(f"{p}have h{tag}z : ((-1:\u211d)^{JZ}:\u211d) = ({sign_lit}:\u211d) := by norm_num")
    L.append(f"{p}have h{tag}n : \u2200 t : \u211d, ({tlod}:\u211d) \u2264 t \u2192 t \u2264 ({thid}:\u211d) \u2192 ({lod}:\u211d) \u2264 ((-1:\u211d)^{JZ}) * sin (\u03c0 * ((t - {JR} * \u03c0) / \u03c0)) / t \u2227 ((-1:\u211d)^{JZ}) * sin (\u03c0 * ((t - {JR} * \u03c0) / \u03c0)) / t \u2264 ({hid}:\u211d) := by")
    L.append(f"{p}  intro t hta htb")
    L.append(f"{p}  have hu := h{tag}m t hta htb")
    L.append(f"{p}  have hs := h{tag}e _ hu.1 hu.2")
    if not odd:
        L.append(f"{p}  rw [h{tag}z, one_mul]")
        L.append(f"{p}  exact CLZ.Cert.corner_div_bracket t _ _ _ ({tlod}:\u211d) ({thid}:\u211d) ({Pnd}:\u211d) ({Qnd}:\u211d) (by norm_num) hta htb \u27e8hs.1, hs.2\u27e9 h{tag}1 h{tag}2 h{tag}3 h{tag}4")
    else:
        L.append(f"{p}  have hrw : ((-1:\u211d)^{JZ}) * sin (\u03c0 * ((t - {JR} * \u03c0) / \u03c0)) = - sin (\u03c0 * ((t - {JR} * \u03c0) / \u03c0)) := by rw [h{tag}z, neg_one_mul]")
        L.append(f"{p}  rw [hrw]")
        L.append(f"{p}  exact CLZ.Cert.corner_div_bracket t _ _ _ ({tlod}:\u211d) ({thid}:\u211d) ({Pnd}:\u211d) ({Qnd}:\u211d) (by norm_num) hta htb \u27e8by linarith [hs.2], by linarith [hs.1]\u27e9 h{tag}1 h{tag}2 h{tag}3 h{tag}4")
    return L

def emit_shift(ind, j, tag, tlod, thid):
    """hsinj have: sin t = (-1)^j * sin(pi*((t-j*pi)/pi))."""
    JZ, JR = jr(j)
    if j >= 0:
        return [f"{ind}have h{tag}s : ∀ t : ℝ, ({tlod}:ℝ) ≤ t → t ≤ ({thid}:ℝ) → sin t = ((-1:ℝ)^{JZ}) * sin (π * ((t - {JR} * π) / π)) :=",
                f"{ind}  fun t _ _ => CLZ.Cert.sin_shift_posZ t {JZ} (by norm_num)"]
    n = -j
    L = [f"{ind}have h{tag}s : ∀ t : ℝ, ({tlod}:ℝ) ≤ t → t ≤ ({thid}:ℝ) → sin t = ((-1:ℝ)^{JZ}) * sin (π * ((t - {JR} * π) / π)) :=",
         f"{ind}  fun t _ _ => by",
         f"{ind}    have hz : ((-1:ℝ)^{JZ}:ℝ) = ((-1:ℝ)^(({n}:ℕ))) := by norm_num",
         f"{ind}    have hc : t - {JR} * π = t + (({n}:ℕ):ℝ) * π := by ring",
         f"{ind}    rw [hz, hc]",
         f"{ind}    exact CLZ.Cert.sin_shift_neg t {n}"]
    return L

SER = None  # optional slim replacement for emit_ser (set by slim.py)
WPAD = 0    # soundness pad on the table value (slim sets 1e-12: snapped
            # piece arithmetic loses ~1e-16, budget is 2.1e-8 over 21 terms)

def emit_piece(ind, tag, pc):
    """all the piece haves for one sinc_bracket piece."""
    j = pc["j"]
    JZ, JR = jr(j)
    L = []
    L += emit_mem(ind, JZ, JR, j, pc["s0"], pc["s1"], pc["tlo"], pc["thi"], tag)
    L += emit_shift(ind, j, tag, g.dec(pc["tlo"]), g.dec(pc["thi"]))
    L += (SER or emit_ser)(ind, pc["s0"], pc["s1"], pc["P"], pc["Q"], tag)
    L += emit_div(ind, JZ, JR, j, pc["s0"], pc["s1"], pc["P"], pc["Q"],
                  pc["tlo"], pc["thi"], pc["lo"], pc["hi"], tag)
    return L

def emit_direct_bracket(ind, name, pieces, tvar="t", t0d=None, t1d=None, pi_expr=None):
    """have {name} : lo <= sinc {pi_expr} ∧ sinc {pi_expr} <= hi — direct path."""
    L = []
    lo = g.slo(min(p["lo"] for p in pieces))
    hi = g.shi(max(p["hi"] for p in pieces))
    if len(pieces) == 1:
        pc = pieces[0]
        JZ, JR = jr(pc["j"])
        L += emit_piece(ind, name, pc)
        tlod, thid = g.dec(pc["tlo"]), g.dec(pc["thi"])
        s0d, s1d, Pd, Qd = g.dec(pc["s0"]), g.dec(pc["s1"]), g.dec(g.slo(pc["P"])), g.dec(g.shi(pc["Q"]))
        lod, hid = g.dec(pc["lo"]), g.dec(pc["hi"])
        L.append(f"{ind}have h{name} : ({lod}:ℝ) ≤ sinc {pi_expr} ∧ sinc {pi_expr} ≤ ({hid}:ℝ) :=")
        L.append(f"{ind}  CLZ.sinc_bracket ({tlod}:ℝ) ({thid}:ℝ) {JZ} ({s0d}:ℝ) ({s1d}:ℝ)")
        L.append(f"{ind}    ({Pd}:ℝ) ({Qd}:ℝ) ({lod}:ℝ) ({hid}:ℝ)")
        L.append(f"{ind}    (by norm_num) h{name}m h{name}s h{name}e h{name}n {pi_expr} {t0d} {t1d}")
        mem = f"have hm{name} : ({tlod}:ℝ) ≤ {pi_expr} ∧ {pi_expr} ≤ ({thid}:ℝ) := ⟨{t0d}, {t1d}⟩"
        L.insert(0, mem)
        return L, (lo, hi)
    # multi-piece (rare): per-piece haves + rcases at the boundary
    assert len(pieces) == 2, len(pieces)
    L0, L1 = pieces
    assert L0["thi"] == L1["tlo"], "pieces must tile"
    for k, pc in ((0, L0), (1, L1)):
        L += emit_piece(ind, f"{name}p{k}", pc)
    lod, hid = g.dec(lo), g.dec(hi)
    bd = g.dec(L0["thi"])
    l0d, h0d = g.dec(L0["lo"]), g.dec(L0["hi"])
    l1d, h1d = g.dec(L1["lo"]), g.dec(L1["hi"])
    a0, a1 = f"({g.dec(L0['tlo'])}:ℝ)", f"({g.dec(L0['thi'])}:ℝ)"
    b0, b1x = f"({g.dec(L1['tlo'])}:ℝ)", f"({g.dec(L1['thi'])}:ℝ)"
    L.append(f"have hm{name}0 : {a0} ≤ {pi_expr} ∧ {pi_expr} ≤ {a1} := ⟨{t0d}, by linarith [{t1d}]⟩")
    L.append(f"have hm{name}1 : {b0} ≤ {pi_expr} ∧ {pi_expr} ≤ {b1x} := ⟨by linarith [{t0d}], {t1d}⟩")
    L.append(f"{ind}have h{name} : ({lod}:ℝ) ≤ sinc {pi_expr} ∧ sinc {pi_expr} ≤ ({hid}:ℝ) := by")
    L.append(f"{ind}  rcases le_or_lt {pi_expr} ({bd}:ℝ) with hb | hb")
    L.append(f"{ind}  · have h0 := CLZ.sinc_bracket {a0} {a1} ({L0['j']}:ℤ) ({g.dec(L0['s0'])}:ℝ) ({g.dec(L0['s1'])}:ℝ) ({g.dec(L0['P'])}:ℝ) ({g.dec(L0['Q'])}:ℝ) ({l0d}:ℝ) ({h0d}:ℝ)")
    L.append(f"{ind}      (by norm_num) h{name}p0m h{name}p0s h{name}p0e h{name}p0n {pi_expr} hm{name}0.1 hb")
    L.append(f"{ind}    exact ⟨by linarith [h0.1], by linarith [h0.2]⟩")
    L.append(f"{ind}  · have h1 := CLZ.sinc_bracket {b0} {b1x} ({L1['j']}:ℤ) ({g.dec(L1['s0'])}:ℝ) ({g.dec(L1['s1'])}:ℝ) ({g.dec(L1['P'])}:ℝ) ({g.dec(L1['Q'])}:ℝ) ({l1d}:ℝ) ({h1d}:ℝ)")
    L.append(f"{ind}      (by norm_num) h{name}p1m h{name}p1s h{name}p1e h{name}p1n {pi_expr} hm{name}1.1 (by linarith [hb])")
    L.append(f"{ind}    exact ⟨by linarith [h1.1], by linarith [h1.2]⟩")
    return L, (lo, hi)

def emit_reflected_bracket(ind, name, t1lo, t1hi, lo1, hi1, pi_expr, mem_lo, mem_hi):
    """reflected K1 bracket via sinc_bracket_even_cover + sinc_near1."""
    M = max(-t1lo, t1hi, F(0))
    Md = g.dec(M)
    L = []
    near_lo = 1 - M**2/6 - M**4/120
    assert g.slo(near_lo) == lo1 and hi1 == 1, (float(lo1), float(hi1))
    lod = g.dec(lo1)
    t1d, t2d = g.dec(t1lo), g.dec(t1hi)
    L.append(f"{ind}have h{name}cv1 : (-({Md}:ℝ)) ≤ ({t1d}:ℝ) := by norm_num")
    L.append(f"{ind}have h{name}cv2 : ({t2d}:ℝ) ≤ ({Md}:ℝ) := by norm_num")
    L.append(f"{ind}have h{name}nr : ({lod}:ℝ) ≤ (1:ℝ) - ({Md}:ℝ)^2/6 - ({Md}:ℝ)^4/120 := by norm_num")
    L.append(f"{ind}have h{name} : ({lod}:ℝ) ≤ sinc {pi_expr} ∧ sinc {pi_expr} ≤ (1:ℝ) :=")
    L.append(f"{ind}  CLZ.Cert.sinc_bracket_even_cover ({t1d}:ℝ) ({t2d}:ℝ) ({Md}:ℝ) ({lod}:ℝ) (1:ℝ)")
    L.append(f"{ind}    (by intro t hta htb; rw [abs_le]; exact ⟨by linarith [h{name}cv1], by linarith [h{name}cv2]⟩)")
    L.append(f"{ind}    (by")
    L.append(f"{ind}      intro w hw1 hw2")
    L.append(f"{ind}      have hs := CLZ.Cert.sinc_near1 ({Md}:ℝ) w hw1 hw2 (by norm_num)")
    L.append(f"{ind}      exact ⟨by linarith [hs.1, h{name}nr], hs.2⟩)")
    L.append(f"{ind}    {pi_expr} {mem_lo} {mem_hi}")
    return L, (lo1, hi1)

def bracket_bounds(i):
    """(t1 int, t2 int, reflected?, t1 pieces, K1, t2 pieces, K2) for cell i."""
    (t1lo, t1hi), (t2lo, t2hi) = cell_t12(i)
    refl = t1lo < 0
    if refl:
        M = max(-t1lo, t1hi, F(0))
        assert M <= 1
        lo1 = g.slo(1 - M**2/6 - M**4/120); hi1 = F(1)
        K1 = (lo1, hi1)
        p1 = None
    else:
        p1 = direct_pieces(t1lo, t1hi)
        K1 = (g.slo(min(p["lo"] for p in p1)), g.shi(max(p["hi"] for p in p1)))
    p2 = direct_pieces(t2lo, t2hi)
    K2 = (g.slo(min(p["lo"] for p in p2)), g.shi(max(p["hi"] for p in p2)))
    return (t1lo, t1hi), (t2lo, t2hi), refl, p1, K1, p2, K2

def emit_wcell(i, wt, ser=None):
    global SER
    if ser is not None:
        SER = ser
    """the full wcell_i theorem text."""
    lo, hi = g.cell_lo(i), g.cell_hi(i)
    W = g.slo(F(wt[i], G45) - WPAD)
    (t1lo, t1hi), (t2lo, t2hi), refl, p1, K1, p2, K2 = bracket_bounds(i)
    KL = g.slo((K1[0] + K2[0]) / 2)
    KH = g.shi((K1[1] + K2[1]) / 2)
    cands = [KL / K0HI, KL / K0LO, KH / K0HI, KH / K0LO]
    kl, kh = g.slo(min(cands)), g.shi(max(cands))
    if kl >= 0:
        w = kl * kl
    elif kh <= 0:
        w = kh * kh
    else:
        w = F(0)
    w = max(w, F(0))
    assert w >= W, f"cell {i}: mirrored {float(w)} < table {float(W)}"
    L = []
    hyp = "(0:ℝ) ≤ x" if i == 0 else f"({g.dec(lo)}:ℝ) ≤ x"
    L.append(f"theorem wcell_{i} : ∀ x : ℝ, {hyp} → x ≤ ({g.dec(hi)}:ℝ) → ({g.dec(W)}:ℝ) ≤ kk x ^ 2 := by")
    L.append("  intro x hx1 hx2")
    if i != 0:
        L.append(f"  have pm1 : ({PLOs}:ℝ) * ({g.dec(lo)}:ℝ) ≤ π * x :=")
        L.append(f"    CLZ.Cert.pi_mul_lb x ({g.dec(lo)}:ℝ) ({PLOs}:ℝ) (by norm_num) hx1 (by norm_num) (by norm_num)")
    L.append(f"  have pm2 : π * x ≤ ({PHIs}:ℝ) * ({g.dec(hi)}:ℝ) :=")
    L.append(f"    CLZ.Cert.pi_mul_ub x ({g.dec(hi)}:ℝ) ({PHIs}:ℝ) (by linarith [hx1]) hx2 (by norm_num)")
    # t1 = pi*x - a
    if i == 0:
        L.append("  have hp0 : (0:ℝ) ≤ π * x := mul_nonneg Real.pi_pos.le hx1")
        L.append(f"  have hpc0 : ({PLOs}:ℝ) * ({g.dec(lo)}:ℝ) ≤ 0 := by norm_num")
        L.append(f"  have hclo1 : ({g.dec(t1lo)}:ℝ) ≤ -(0.7071067811865475245:ℝ) := by norm_num")
        L.append(f"  have hchi1 : ({PHIs}:ℝ) * ({g.dec(hi)}:ℝ) - (0.7071067811865475244:ℝ) ≤ ({g.dec(t1hi)}:ℝ) := by norm_num")
        L.append(f"  have hm1 : ({g.dec(t1lo)}:ℝ) ≤ π * x - CLZ.a ∧ π * x - CLZ.a ≤ ({g.dec(t1hi)}:ℝ) :=")
        L.append("    ⟨by linarith [hp0, CLZ.Cert.a_hi, hclo1], by linarith [pm2, CLZ.Cert.a_lo, hchi1]⟩")
    else:
        L.append(f"  have hclo1 : ({g.dec(t1lo)}:ℝ) ≤ ({PLOs}:ℝ) * ({g.dec(lo)}:ℝ) - (0.7071067811865475245:ℝ) := by norm_num")
        L.append(f"  have hchi1 : ({PHIs}:ℝ) * ({g.dec(hi)}:ℝ) - (0.7071067811865475244:ℝ) ≤ ({g.dec(t1hi)}:ℝ) := by norm_num")
        L.append(f"  have hm1 : ({g.dec(t1lo)}:ℝ) ≤ π * x - CLZ.a ∧ π * x - CLZ.a ≤ ({g.dec(t1hi)}:ℝ) :=")
        L.append("    ⟨by linarith [pm1, CLZ.Cert.a_hi, hclo1], by linarith [pm2, CLZ.Cert.a_lo, hchi1]⟩")
    # t2 = pi*x + a
    L.append(f"  have hclo2 : ({g.dec(t2lo)}:ℝ) ≤ ({PLOs}:ℝ) * ({g.dec(lo)}:ℝ) + (0.7071067811865475244:ℝ) := by norm_num")
    L.append(f"  have hchi2 : ({PHIs}:ℝ) * ({g.dec(hi)}:ℝ) + (0.7071067811865475245:ℝ) ≤ ({g.dec(t2hi)}:ℝ) := by norm_num")
    L.append(f"  have hm2 : ({g.dec(t2lo)}:ℝ) ≤ π * x + CLZ.a ∧ π * x + CLZ.a ≤ ({g.dec(t2hi)}:ℝ) :=")
    if i == 0:
        L.append("    ⟨by linarith [hp0, hpc0, CLZ.Cert.a_lo, hclo2], by linarith [pm2, CLZ.Cert.a_hi, hchi2]⟩")
    else:
        L.append("    ⟨by linarith [pm1, CLZ.Cert.a_lo, hclo2], by linarith [pm2, CLZ.Cert.a_hi, hchi2]⟩")
    # brackets
    if refl:
        blk, _ = emit_reflected_bracket("  ", "b1", t1lo, t1hi, K1[0], K1[1], "(π * x - CLZ.a)", "hm1.1", "hm1.2")
        L += blk
    else:
        blk, _ = emit_direct_bracket("  ", "b1", p1, pi_expr="(π * x - CLZ.a)",
                                     t0d="hm1.1", t1d="hm1.2")
        blk = [l for l in blk if not l.startswith("have hmb1")]
        L += blk
    blk, _ = emit_direct_bracket("  ", "b2", p2, pi_expr="(π * x + CLZ.a)",
                                 t0d="hm2.1", t1d="hm2.2")
    blk = [l for l in blk if not l.startswith("have hmb2")]
    L += blk
    # K interval
    L.append(f"  have hKsum1 : ({g.dec(KL)}:ℝ) ≤ (({g.dec(K1[0])}:ℝ) + ({g.dec(K2[0])}:ℝ))/2 := by norm_num")
    L.append(f"  have hKsum2 : (({g.dec(K1[1])}:ℝ) + ({g.dec(K2[1])}:ℝ))/2 ≤ ({g.dec(KH)}:ℝ) := by norm_num")
    L.append(f"  have hK1 : ({g.dec(KL)}:ℝ) ≤ Kfn x := by")
    L.append("    simp only [Kfn]")
    L.append("    linarith [hb1.1, hb2.1, hKsum1]")
    L.append(f"  have hK2 : Kfn x ≤ ({g.dec(KH)}:ℝ) := by")
    L.append("    simp only [Kfn]")
    L.append("    linarith [hb1.2, hb2.2, hKsum2]")
    # kk close
    L.append("  have hk0p : (0:ℝ) < Kfn 0 := by linarith [CLZ.Cert.Kfn0_lb]")
    if w == 0:
        L.append("  exact sq_nonneg _")
        return "\n".join(L) + "\n"
    if kl >= 0:
        L.append(f"  have hklp : (0:ℝ) ≤ ({g.dec(kl)}:ℝ) := by norm_num")
        L.append(f"  have hkk : ({g.dec(kl)}:ℝ) ≤ kk x := by")
        L.append("    simp only [kk]")
        L.append("    rw [le_div_iff₀ hk0p]")
        L.append(f"    calc ({g.dec(kl)}:ℝ) * Kfn 0 ≤ ({g.dec(kl)}:ℝ) * ({K0HIs}:ℝ) :=")
        L.append("        mul_le_mul_of_nonneg_left CLZ.Cert.Kfn0_ub hklp")
        L.append(f"      _ ≤ ({g.dec(KL)}:ℝ) := by norm_num")
        L.append("      _ ≤ Kfn x := hK1")
        L.append(f"  exact le_trans (by norm_num : ({g.dec(W)}:ℝ) ≤ ({g.dec(kl)}:ℝ)^2) (pow_le_pow_left₀ hklp hkk 2)")
    else:
        L.append(f"  have hkhn : ({g.dec(kh)}:ℝ) ≤ 0 := by norm_num")
        L.append(f"  have hkk : kk x ≤ ({g.dec(kh)}:ℝ) := by")
        L.append("    simp only [kk]")
        L.append("    rw [div_le_iff₀ hk0p]")
        L.append(f"    calc Kfn x ≤ ({g.dec(KH)}:ℝ) := hK2")
        L.append(f"      _ ≤ ({g.dec(kh)}:ℝ) * ({K0HIs}:ℝ) := by norm_num")
        L.append(f"      _ ≤ ({g.dec(kh)}:ℝ) * Kfn 0 := by nlinarith [CLZ.Cert.Kfn0_ub, hkhn]")
        L.append(f"  have h1 : ({g.dec(W)}:ℝ) ≤ ({g.dec(kh)}:ℝ)^2 := by norm_num")
        L.append("  nlinarith [h1, hkk, hkhn]")
    return "\n".join(L) + "\n"

# ---------- stage drivers ----------

def load_mirror():
    return json.load(open("mirror_wt.json"))

def write_file(path, body, header="import CLZCert.Cert.Const\nimport CLZCert.Cert.Glue\n\nnamespace CLZ.Cert\nopen Real\n"):
    with open(path, "w") as f:
        f.write(header)
        f.write(body)
        f.write("\nend CLZ.Cert\n")

def stage_wcell(start, stop, batch=500):
    wt = load_mirror()
    os.makedirs(CERT, exist_ok=True)
    import hashlib
    man = {}
    manp = os.path.join(CERT, "wcell_manifest.json")
    if os.path.exists(manp):
        man = json.load(open(manp))
    t0 = time.time()
    for blk in range(start, stop, batch):
        b = blk // batch
        fn = os.path.join(CERT, f"Wcell_{b:03d}.lean")
        if blk in man and man[blk]["stop"] == min(blk + batch, stop) and os.path.exists(fn):
            continue
        body = []
        for i in range(blk, min(blk + batch, stop)):
            body.append(emit_wcell(i, wt))
        write_file(fn, "\n".join(body))
        sha = hashlib.sha256(open(fn, "rb").read()).hexdigest()
        man[blk] = dict(file=fn, sha=sha, start=blk, stop=min(blk + batch, stop))
        json.dump(man, open(manp, "w"), indent=0)
        print(f"  wcell block {b}: cells {blk}..{min(blk+batch,stop)-1} t={time.time()-t0:.0f}s", flush=True)

def stage_smoke():
    wt = load_mirror()
    os.makedirs(CERT, exist_ok=True)
    body = []
    for i in (0, 1, 450, 900, 901, 3808, 5000, 4228, 44827, 45607):
        body.append(emit_wcell(i, wt))
    write_file(os.path.join(CERT, "SmokeW.lean"), "\n".join(body))
    print("smoke file written: CLZCert/Cert/SmokeW.lean (10 cells)")

if __name__ == "__main__":
    st = sys.argv[1] if len(sys.argv) > 1 else "smoke"
    if st == "smoke":
        stage_smoke()
    elif st == "wcell":
        a = int(sys.argv[2]) if len(sys.argv) > 2 else 0
        b = int(sys.argv[3]) if len(sys.argv) > 3 else 45608
        stage_wcell(a, b)
    else:
        sys.exit(f"unknown stage {st}")

