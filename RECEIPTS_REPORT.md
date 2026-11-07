# RECEIPTS_REPORT — lane CLZ-A, session 3 (7-pt pivot), 2026-11-07

## Status: MIRROR CORE VALIDATED / LEAN EMISSION REMAINING
Headline number requested: **0 / 145,769 boxes discharged in Lean** — the
session pivoted twice (3-pt data unsound → 7-pt; then Gaps lane landed
proved lemmas → Helpers rewire) and ended with the 7-pt receipt NUMERIC
CORE fully validated and the Lean emission layer designed but not yet
generated. `seven_point_certificate` REMAINS AN AXIOM (honest).

## What is LANDED (commits c6c0bb7..d4d3e75, this clone)
1. `CLZCert/Helpers.lean` (PROVED, compiles): the receipt machinery —
   sin/cos reduction by n·π; sinc evenness + even-cover; `sinc_small`;
   `sinc_near1` (near-zero reflected bracket); `sin9`/`chiG` +
   `sin_series_sandwich` and **per-window-tail variants**
   `sin_series_sandwich_pos/neg` consuming `Kernel.sin_partial_abs_bound`;
   `Kfn0_lb/ub` from `CLZ.sin_a_lb` + mirrored `sin_a_ub` (K0 width 5e-12).
   Consumes the GAPS lane's proved lemmas; **adds no gaps**.
2. `CLZCert/Kernel.lean` + `Gaps.lean` + `Assembly.lean`: adopted verbatim
   from clz-cert-gaps (all three kernel gaps PROVED; H0_lower a theorem).
3. `gen_cert.py`: S_k2 fix; `cert_data.json` = honest post-fix cover.
4. `gen_receipts_7pt.py`: the 7-pt emitter core — Lean-visible-constant
   (20-digit) mirror engine, window decomposition (j-pieces, straddle
   splitting at j·π), per-window-tail sandwiches, K/kk/k² outward
   arithmetic, reflected-cell handling (sinc_near1 + fine far-pieces +
   right-edge hair piece), table/box verification gates.

## Numeric validation (the keystone — all green)
- All **45,608/45,608** w-cells mirrored, bound ≥ 0, 94 s single-core.
- **400/400** sampled interval boxes: bounds recomputed from MY mirror
  table are ≥ 19/5000 (min margin 2.1e-7 on the 1e-45 grid).
- **8,235/8,235** outside cells pass the one-body gate U ≥ 19/5000.
- Non-reflected cells match the sibling table to ~1e-14 relative.

## Remaining for discharge (next session, mechanical)
- Lean emission of: wcell (45,608) → segment-tree wrange (13,500 distinct
  ranges) → 131,035 box assemblies → 8,235 obcell one-body theorems +
  span dispatch → 729 combo subtrees + pressure + top dispatch →
  `seven_point_certificate := discharged` (one-line Assembly7pt swap,
  disjoint from Gaps lane's edit). All proof shapes worked out this
  session (sinc_bracket instantiation blocks: hmem linarith, literal-j
  hsinj via `sin_sub/add_nat_pi` + norm_num, hser via 20 term facts +
  sandwich + 2 linarith, sign-aware hdiv). Est. 1.5–3 h kernel time,
  LAKE_JOBS=1 detached.
- **14,734 tangent-evidence boxes**: need a certified-convexity layer
  (sinc′/sinc″ brackets via cos_partial_abs_bound — available — plus
  per-box w″-range facts + LDL/PSD + tangent-plane lemma). NOT built;
  honestly outstanding. Without it `seven_point_certificate` stays an
  axiom; the interval layer alone does not cover its boxes.

## Axiom footprint (current)
`kappa_star_ge_7pt`: {propext, Classical.choice, Quot.sound, H0_lower,
jo_bridge_7pt, seven_point_certificate}. After the Gaps merge H0_lower is
a theorem; after my discharge only {jo_bridge_7pt} + std three remain
(H0_lower similarly vanishes from the 3-pt kappa_star_ge, whose
three_point_certificate needs the re-levelling note below first).

## Corrected 3-pt record (as ordered)
- Landed 3-pt cert_data.json UNSOUND (S_k2 negative-branch bug; preserved
  as cert_data_3pt_landed_unsound.json). Post-fix re-run here:
  **eps' = 221.38139380359024e-6** (14,967 boxes, 0.9 s) ≥ the
  221.3812e-6 headline threshold (margin 9.4e-11), but **< the Assembly
  axiom level 2215072/10¹⁰** (shortfall 1.258e-10). The 3-pt Assembly
  needs re-levelling to e₀ = 2213813/10¹⁰ (B₀ arithmetic still gives
  6725198/10⁷) — 3-pt lane's call. No 3-pt receipts were emitted.

## Wound for CLZ-C (their wt table, non-blocking for their mins)
`gen_7pt.py` `_sinc_piece` via `S_reduce` computes S_div(sb, tsub) with a
STRADDLING tsub when the top interval straddles 0 inside one j-piece
(wt[900] = 7.58e74 garbage; true w ≈ 0.854). Sound for their certificate
(garbage only ever enters range-MINs, which discard it) but the table
should be fixed; my receipts use my own table and are unaffected.
