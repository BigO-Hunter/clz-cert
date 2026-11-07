# CERT_REPORT — CLZ 3-point certificate (status 2026-11-06, session 2)

## HEADLINE (kernel-checked, conditional on named axioms)
`CLZCert.Assembly.kappa_star_ge`:
  ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (6725198/10⁷ − ε)·N(0,T) ≤ N₀ˢ(0,T)
  — κ* ≥ 0.6725198 > H = 0.6725007 (verified row), +1.9e-5.
Axiom footprint: `three_point_certificate` (receipts below),
`jo_bridge` (CLZ_GAP_JO_BRIDGE — Jo §2–3 stability+averaging),
`H0_lower` (CLZ_GAP_H0 — H₀ ≥ 6725006930/10¹⁰; true 0.672500703679,
margin 1.07e-8; exact requirement 0.6725006928110). Kernel: CLZ_GAP_SINPOS,
CLZ_GAP_TAIL. Nothing else; no native_decide.

## Receipts (stage 3)
- gen_cert.py: exact scaled-int interval arithmetic; **one-line fix this
  session** — prune boxes with u₀+v₀ > 4 (they were disjoint from the triangle
  and poisoned the min: earlier 34.7M-box run's 102.499e-6 was an artifact).
- Certified ε' = 221.50727020160642e-6 ≥ 221.3812e-6 threshold ⇒ headline.
- 319 boxes, 521 bound evals, 0.0s (after prune). cert_data.json committed.
- Independent verification: every box in-domain (14 boundary straddlers are
  u₀+v₀ = 4 exactly, valid); 16×16 root coverage complete; 20,000 random
  triangle points: 0 violations of f ≥ ε'; basin scan min 222.800e-6;
  mpmath 50dps integral-form k matches certified brackets at probe points.
- REMAINING for Lean receipts: instantiate Kernel.sinc_bracket per box
  (window-fit ℚ decides + series partial sums via CLZ_GAP_TAIL + division);
  then three_point_certificate discharges. Not yet emitted.

## Gaps still named
CLZ_GAP_TAIL (alternating-series estimate; self-contained induction sketched
in session log), CLZ_GAP_SINPOS, CLZ_GAP_H0 (tan sandwich at 1/√2 to 1e-8),
CLZ_GAP_JO_BRIDGE (paper-tracked; mirrors ainta §2–3), CLZ_GAP_RANKTRACE/
CLZ_GAP_DUALFORM (statements recorded in Stability.lean).

## 7-point: SKIPPED (per plan).
## Note: a false alarm was run down: (1.0551, 2.9992) has u+v = 4.054 > 4 —
outside the triangle; no contradiction with Jo's 221e-6.
