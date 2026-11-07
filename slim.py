#!/usr/bin/env python3
"""Slim wcell emitter (CLZ-A2).

Two changes vs emit7.emit_ser, both for kernel cost:
  * every literal is snapped OUTWARD onto an 1e-18 grid (g.G45 = 10**18), so
    linarith/norm_num see ~18-digit numerals instead of 45-460 digit ones.
    Sound: the certificate's slack budget is 2.1e-8, each snap costs 1e-18.
  * the 72-line per-term Z-cast block is replaced by 9 generic pow_odd_mono
    facts plus ONE norm_num polynomial fact, and the proved
    `sin_series_sandwich` supplies the tail (the old emit_ser joined the
    series terms with "+" only -- dropping the alternating signs, which made
    its cumulative facts false).
"""
import json, math, os, sys, time
from fractions import Fraction as F

sys.path.insert(0, ".")
import gen_receipts_7pt as g
import emit7 as e7

S = 10 ** 18                          # emit literals on the 1e-18 outward grid


def sl(x):
    return F(x.numerator * S // x.denominator, S)


def sh(x):
    return F(-((-x.numerator * S) // x.denominator), S)


GN = g.GN
CH = F(2, 10 ** 15)                   # tail slack used by the emitted arithmetic (> chiG)
_orig_sandwich = g.sandwich_bounds


def sandwich_slim(s0, s1):
    """same series, but bases snapped OUTWARD onto the 1e-18 grid and a 2e-15
    tail constant, so P,Q are exact decimal literals the Lean chain can use."""
    P, Q = _orig_sandwich(s0, s1)
    d = CH - (g.PHI / 2) ** 21 / F(math.factorial(21))
    return g.slo(P - d), g.shi(Q + d)


g.sandwich_bounds = sandwich_slim
e7.WPAD = F(1, 10 ** 12)
PLOs = "3.14159265358979323846"
PHIs = "3.14159265358979323847"
ODD = [3, 5, 7, 9, 11, 13, 15, 17, 19]
CHI = (g.PHI / 2) ** 21 / F(math.factorial(21))


def emit_ser_slim(ind, s0, s1, P, Q, tag):
    pos = s0 >= 0
    assert pos or (s1 <= 0), "window straddles 0"
    be = (g.PLO if pos else g.PHI) * s0   # lower bound of pi*u (exact product)
    bo = (g.PHI if pos else g.PLO) * s1   # upper bound
    belo, bohi = sl(be), sh(bo)     # snapped OUTWARD, same atoms as poly
    bed, bod = g.dec(belo), g.dec(bohi)
    bedx, bodx = g.dec(be), g.dec(bo)
    s0d, s1d = g.dec(s0), g.dec(s1)
    Pl, Ql = P, Q
    Pd, Qd = g.dec(Pl), g.dec(Ql)

    def poly(lo, hi):
        out = []
        for k in range(10):
            m = 2 * k + 1
            v = lo if k % 2 == 0 else hi
            term = f"({g.dec(v)})" if m == 1 else f"({g.dec(v)})^{m}/{math.factorial(m)}"
            out.append((" + " if k % 2 == 0 else " - ") + term)
        r = "".join(out)
        return r[3:] if r.startswith(" + ") else r

    def val(lo, hi):
        t = F(0)
        for k in range(10):
            m = 2 * k + 1
            v = lo if k % 2 == 0 else hi
            t += (v ** m / math.factorial(m)) * (1 if k % 2 == 0 else -1)
        return t

    E = F(1, 10 ** 15)                 # the sandwich15 tail constant
    assert CHI < CH
    assert Pl + E <= val(belo, bohi), float(val(belo, bohi) - Pl - E)
    assert val(bohi, belo) + E <= Ql, float(Ql - val(bohi, belo) - E)

    L = []
    p = ind
    L.append(f"{p}have h{tag}e : ∀ u : ℝ, ({s0d}:ℝ) ≤ u → u ≤ ({s1d}:ℝ) → ({Pd}:ℝ) ≤ sin (π*u) ∧ sin (π*u) ≤ ({Qd}:ℝ) := by")
    L.append(f"{p}  intro u hu1 hu2")
    L.append(f"{p}  have h{tag}x0 : ({bedx}:ℝ) ≤ π * u := by")
    L.append(f"{p}    rw [show ({bedx}:ℝ) = ({PLOs if pos else PHIs}:ℝ) * ({s0d}:ℝ) from by norm_num]")
    if pos:
        L.append(f"{p}    exact CLZ.Cert.pi_mul_lb u ({s0d}:ℝ) ({PLOs}:ℝ) (by norm_num) hu1 (by norm_num) (by norm_num)")
    else:
        L.append(f"{p}    exact CLZ.Cert.pi_mul_lb_neg u ({s0d}:ℝ) ({PHIs}:ℝ) (by norm_num) hu1 (by norm_num)")
    L.append(f"{p}  have h{tag}x1 : π * u ≤ ({bodx}:ℝ) := by")
    L.append(f"{p}    rw [show ({bodx}:ℝ) = ({PHIs if pos else PLOs}:ℝ) * ({s1d}:ℝ) from by norm_num]")
    if pos:
        L.append(f"{p}    exact CLZ.Cert.pi_mul_ub u ({s1d}:ℝ) ({PHIs}:ℝ) (by linarith [hu1]) hu2 (by norm_num)")
    else:
        L.append(f"{p}    exact CLZ.Cert.pi_mul_ub_neg u ({s1d}:ℝ) ({PLOs}:ℝ) (by norm_num) hu2 (by norm_num)")
    assert -F("1.570796326794896619235") <= belo and bohi <= F("1.570796326794896619235")
    L.append(f"{p}  have h{tag}abs : |π * u| ≤ ((3.14159265358979323847:ℝ)/2) := by")
    L.append(f"{p}    rw [abs_le]")
    L.append(f"{p}    exact ⟨by linarith [h{tag}x0], by linarith [h{tag}x1]⟩")
    L.append(f"{p}  have h{tag}sw := CLZ.Cert.sin_series_sandwich15 (π * u) h{tag}abs")
    # snapped inward bounds for the monomial bases
    L.append(f"{p}  have h{tag}l0 : ({bed}:ℝ) ≤ π * u := le_trans (by norm_num) h{tag}x0")
    L.append(f"{p}  have h{tag}l1 : π * u ≤ ({bod}:ℝ) := le_trans h{tag}x1 (by norm_num)")
    for m in ODD:
        L.append(f"{p}  have t{tag}{m} : ({bed})^{m} ≤ (π*u)^{m} ∧ (π*u)^{m} ≤ ({bod})^{m} :=")
        L.append(f"{p}    ⟨CLZ.Cert.pow_odd_mono _ _ {m} (by norm_num) h{tag}l0, CLZ.Cert.pow_odd_mono _ _ {m} (by norm_num) h{tag}l1⟩")
    # one norm_num per direction: pad the (decimated) target by 1e-15 = chiG bound
    L.append(f"{p}  have h{tag}PQ : ({Pd}:ℝ) + (0.000000000000001:ℝ) ≤ {poly(belo, bohi)} ∧ {poly(bohi, belo)} + (0.000000000000001:ℝ) ≤ ({Qd}:ℝ) := by")
    L.append(f"{p}    constructor <;> norm_num")
    ins = ", ".join(f"t{tag}{m}.1" for m in ODD) + ", " + ", ".join(f"t{tag}{m}.2" for m in ODD)
    L.append(f"{p}  simp only [CLZ.Cert.sin9] at h{tag}sw ⊢")
    L.append(f"{p}  constructor")
    L.append(f"{p}  · linarith [h{tag}sw.1, h{tag}PQ.1, {ins}]")
    L.append(f"{p}  · linarith [h{tag}sw.2, h{tag}PQ.2, {ins}]")
    return L


def stage(start, stop, batch=64):
    """emit cells [start,stop) as batch files with a sha-pinned manifest"""
    import hashlib
    wt = e7.load_mirror()
    os.makedirs(e7.CERT, exist_ok=True)
    man = {}
    mp = os.path.join(e7.CERT, "slim_manifest.json")
    if os.path.exists(mp):
        man = json.load(open(mp))
    t0 = time.time()
    for blk in range(start, stop, batch):
        hi = min(blk + batch, stop)
        fn = os.path.join(e7.CERT, f"Slim_{blk:05d}.lean")
        if os.path.exists(fn) and str(blk) in man and man[str(blk)].get("stop") == hi:
            continue
        body = "".join(e7.emit_wcell(i, wt, ser=emit_ser_slim) + "\n" for i in range(blk, hi))
        e7.write_file(fn, "set_option maxHeartbeats 2000000\n\n" + body)
        man[str(blk)] = dict(file=fn, start=blk, stop=hi,
                             sha=hashlib.sha256(open(fn, "rb").read()).hexdigest())
        json.dump(man, open(mp, "w"), indent=0)
        print(f"  block {blk}..{hi-1} t={time.time()-t0:.0f}s", flush=True)


def main():
    global CH
    if sys.argv[1] == "stage":
        stage(int(sys.argv[2]), int(sys.argv[3]),
              int(sys.argv[4]) if len(sys.argv) > 4 else 64)
        return
    if sys.argv[1] == "cheap":
        CH = F(1, 10 ** 12)          # 1e-12 tail: still 4 orders under budget
        e7.WPAD = F(1, 10 ** 11)
    i = int(sys.argv[2]) if len(sys.argv) > 2 else 5000
    wt = e7.load_mirror()
    body = e7.emit_wcell(i, wt, ser=emit_ser_slim)
    e7.write_file("CLZCert/Cert/T1.lean", body)
    print(f"cell {i}: {len(body)} chars")


if __name__ == "__main__":
    main()
