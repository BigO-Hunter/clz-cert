#!/usr/bin/env python3
"""7-pt Lean receipt emitter (lane CLZ-A2). Stage driver:

  python3 emit7.py wcell  [start stop]   # 45,608 wcell theorems -> Cert/Wcell_*.lean
  python3 emit7.py wrange                # segment-tree min nodes    -> Cert/Wrange_*.lean
  python3 emit7.py ob                    # one-body cells + spans    -> Cert/Ob.lean
  python3 emit7.py boxes [start stop]    # 131,035 interval boxes    -> Cert/Boxes_*.lean
  python3 emit7.py combos [start stop]   # 729 combo dispatch trees  -> Cert/Combo_*.lean
  python3 emit7.py top                   # Tangent.lean + Top.lean + Assembly7pt swap

Mirror discipline: every real literal is derived OUTWARD from the Lean-visible
20-digit constants on the 1e-45 grid; each cell/box claim is verified in exact
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
K0LOs = "0.918725369860555949800554150691128408603149501"
K0HIs = "0.918725369865574401307762900255801616701254273"
K0LO, K0HI = g.K0LO, g.K0HI
CHI_TERM = "chiG"

def rl(x):
    """real literal from exact Fraction (must be a terminating decimal)."""
    return f"({g.dec(x)}:ℝ)"

# ---------- t-interval pieces (direct path) ----------

def direct_pieces(t0, t1):
    """Outward sinc bracket pieces covering [t0,t1] (t0 > 0)."""
    out = []
    for (j, s0, s1, tlo, thi) in g.decompose(t0, t1):
        P, Q = g.sandwich_bounds(s0, s1)
        if j % 2:
            P, Q = -Q, -P
        cands = [P / thi, P / tlo, Q / thi, Q / tlo]
        lo, hi = g.slo(min(cands)), g.shi(max(cands))
        assert lo <= hi
        out.append(dict(j=j, s0=s0, s1=s1, P=P, Q=Q, tlo=tlo, thi=thi, lo=lo, hi=hi))
    assert out, (t0, t1)
    return out

def cell_t1_t2(i):
    """outward t1 = pi*x - a, t2 = pi*x + a intervals over cell i."""
    lo, hi = g.cell_lo(i), g.cell_hi(i)
    t1lo = g.slo(lo * g.PLO) - g.AHI
    t1hi = g.shi(hi * g.PHI) - g.ALO
    t2lo = g.slo(lo * g.PLO) + g.ALO
    t2hi = g.shi(hi * g.PHI) + g.AHI
    return (t1lo, t1hi), (t2lo, t2hi)

# ---------- emitted proof blocks ----------

def emit_hmem(ind, JR, s0, s1, tlo, thi, tag):
    """membership: s0 <= (t - j*pi)/pi <= s1 for t in [tlo,thi]."""
    L = []
    p = ind
    s0d, s1d = g.dec(s0), g.dec(s1)
    tlod, thid = g.dec(tlo), g.dec(thi)
    # outward facts: (s0+j)*PHI <= tlo  and  thi <= (s1+j)*PLO
    a = s0 + F(j_str_to_j(JR))
    f1 = (s0 + jv) * g.PHI <= tlo
    f2 = thi <= (s1 + jv) * g.PLO
    assert f1 and f2, (f1, f2)
    L.append(f"{p}have h{tag}c1 : (({s0d}:ℝ) + {JR}) * ({PHIs}:ℝ) ≤ ({tlod}:ℝ) := by norm_num")
    L.append(f"{p}have h{tag}c2 : ({thid}:ℝ) ≤ (({s1d}:ℝ) + {JR}) * ({PLOs}:ℝ) := by norm_num")
    L.append(f"{p}have h{tag}m : ∀ t : ℝ, ({tlod}:ℝ) ≤ t → t ≤ ({thid}:ℝ) →")
    L.append(f"{p}    ({s0d}:ℝ) ≤ (t - {JR} * π) / π ∧ (t - {JR} * π) / π ≤ ({s1d}:ℝ) := by")
    L.append(f"{p}  intro t hta htb")
    L.append(f"{p}  have hrw : (t - {JR} * π) / π = t / π - {JR} := by field_simp; ring")
    L.append(f"{p}  constructor")
    L.append(f"{p}  · rw [hrw, le_div_iff₀ Real.pi_pos]")
    L.append(f"{p}    rcases le_or_gt 0 (({s0d}:ℝ) + {JR}) with hh | hh")
    L.append(f"{p}    · calc (({s0d}:ℝ) + {JR}) * π ≤ (({s0d}:ℝ) + {JR}) * ({PHIs}:ℝ) :=")
    L.append(f"{p}        mul_le_mul_of_nonneg_right CLZ.pi_ub.le hh")
    L.append(f"{p}      _ ≤ ({tlod}:ℝ) := h{tag}c1")
    L.append(f"{p}      _ ≤ t := hta")
    L.append(f"{p}    · have hneg : (({s0d}:ℝ) + {JR}) * π < 0 := mul_neg_of_neg_of_pos hh Real.pi_pos")
    L.append(f"{p}      linarith")
    L.append(f"{p}  · rw [hrw, div_le_iff₀ Real.pi_pos]")
    L.append(f"{p}    have hsp : (0:ℝ) < (({s1d}:ℝ) + {JR}) := by norm_num")
    L.append(f"{p}    calc t ≤ ({thid}:ℝ) := htb")
    L.append(f"{p}      _ ≤ (({s1d}:ℝ) + {JR}) * ({PLOs}:ℝ) := h{tag}c2")
    L.append(f"{p}      _ ≤ (({s1d}:ℝ) + {JR}) * π :=")
    L.append(f"{p}        mul_le_mul_of_nonneg_right CLZ.pi_lb.le hsp.le")
    return L, dict(c1=f"h{tag}c1", c2=f"h{tag}c2")

def j_str_to_j(s):
    return int(s.strip("()").split(":")[0])
