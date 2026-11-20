#!/usr/bin/env python3
"""Precompute the exact rational constants used by the Lean receipts."""
from fractions import Fraction as F
import mpmath as mp
import json, sys
sys.path.insert(0, ".")
from gen_cert import PLO, PHI, ALO, AHI, SIN_KEEP  # 35-digit enclosures

mp.mp.dps = 60

# chi_G: global alternating tail bound = (pi_hi/2)^21 / 21!
import math
FACT21 = math.factorial(21)
chiG = (PHI / 2) ** 21 / FACT21
print("chiG =", chiG, "=", float(chiG))

# 45-grid outward snapping (same grid as gen_cert)
GRID = 10 ** 45
def snap_lo(x): return F(x.numerator * GRID // x.denominator, GRID)
def snap_hi(x): return F(-((-x.numerator * GRID) // x.denominator), GRID)

# sin(1/sqrt2) sandwich: from the true value with huge margin at 1e-30
true_sina = mp.sin(1 / mp.sqrt(2))
print("sin(1/sqrt2) =", mp.nstr(true_sina, 40))
sina_lo = snap_lo(F(str(mp.nstr(true_sina - mp.mpf('1e-30'), 45))))
sina_hi = snap_hi(F(str(mp.nstr(true_sina + mp.mpf('1e-30'), 45))))
print("sina_lo =", sina_lo)
print("sina_hi =", sina_hi)

# K0 = sinc(a) = sin a / a, outward from the sandwich
k0_lo = snap_lo(sina_lo / AHI)
k0_hi = snap_hi(sina_hi / ALO)
print("k0_lo =", k0_lo)
print("k0_hi =", k0_hi)

# decimal literal strings (terminating decimals)
def decl(x, digits=None):
    """exact terminating decimal string for Fraction with denominator 10^k or grid"""
    n, d = x.numerator, x.denominator
    # find k such that d | 10^k
    k = 0
    dd = d
    while dd % 2 == 0: dd //= 2; k += 1
    k2 = 0
    dd = d
    while dd % 5 == 0: dd //= 5; k2 += 1
    k = max(k, k2)
    assert dd == 1, f"non-terminating: {x}"
    num = n * (10 ** k) // d
    s = str(abs(num)).rjust(k + 1, "0")
    return ("-" if num < 0 else "") + s[:-k] + "." + s[-k:] + (f"e-45" if False else "")

json.dump({
    "chiG": str(chiG), "chiG_dec": decl(chiG),
    "sina_lo": str(sina_lo), "sina_lo_dec": decl(sina_lo),
    "sina_hi": str(sina_hi), "sina_hi_dec": decl(sina_hi),
    "k0_lo": str(k0_lo), "k0_lo_dec": decl(k0_lo),
    "k0_hi": str(k0_hi), "k0_hi_dec": decl(k0_hi),
}, open("constants.json", "w"))
print("wrote constants.json")
for k, v in json.load(open("constants.json")).items():
    print(k, "=", v)
