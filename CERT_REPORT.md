# CERT_REPORT — CLZ 3-point certificate (status 2026-11-06, session 2)

## CORRECTED RECORD (post S_k2 fix, session 3 — 7pt-lane agent)

**WOUND (found by sibling lane CLZ-C):** gen_cert.py `S_k2` returned the
k²-interval's UPPER endpoint on the negative-k branch, overstating w on
negative-k boxes. The landed cert_data.json was accordingly UNSOUND
(preserved verbatim as `cert_data_3pt_landed_unsound.json`; sibling's
re-bounding of those 319 boxes: eps collapses to 0.531e-6, 49/319 below
the requirement).

**FIX:** `S_k2` now returns `S_mul(kk,kk)[0]` in both branches. Re-run
(this clone, this session): fresh cover, **14,967 boxes, 0.9 s**,
**eps' = 221.38139380359024e-6** (cert_data.json now holds the post-fix
cover).

**Consequences:**
- eps' ≥ 221.3812e-6 (the threshold for the headline constant
  6725198/10⁷) with margin 9.4e-11 — the headline ARITHMETIC survives
  the fix at certificate level e₀ = 2213813/10¹⁰.
- eps' < 2215072/10¹⁰ (the Assembly's stated axiom level; shortfall
  1.258e-10). `ThreePointCert (2215072/10¹⁰)` is therefore NOT
  discharged by the honest post-fix data. The 3-point Assembly needs
  re-levelling to e₀ = 2213813/10¹⁰ (B₀ = (H₀−e₀/4)/(1−e₀/2) at that
  level still gives ≥ 6725198/10⁷); that is the 3-point lane's call.
- No 3-pt receipts were emitted against the unsound data. Lean work in
  this clone continues on the 7-POINT certificate (which was built
  post-fix and is unaffected).

## 7-POINT stage (this lane's active work)
Target: `SevenPointCert (19/5000)` in Assembly7pt.lean (the seven-point lane
`clz-cert-7pt/`, vendored in this repo; its data cert_data_7pt.json:
145,769 boxes = 131,035 interval + 14,734 exact-LDL-convexity tangent,
eps' = 0.0038000211759 ≥ 19/5000, margin 2.1e-8). This lane emits the
per-box receipts: w-cell table receipts (45,608 sinc_bracket
instantiations over the 1/4000-cell table) + segment-tree range lemmas
(13,500 distinct sum-ranges) + per-box assemblies + pressure/one-body
receipts + 6-D dispatch. The 14,734 tangent-evidence boxes need a
certified-convexity layer (sinc'/sinc'' brackets + per-box PSD-Hessian
+ tangent-plane lemma) — status reported honestly at session end.
