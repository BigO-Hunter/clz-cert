# STAGE7_REPORT — CLZ 7-point certificate (2026-11-06, lane CLZ-C)

## HEADLINE
The 7-point stage **CERTIFIED**: F₆(g₁,…,g₆) ≥ 19/5000 for all gaps ≥ 0,
exact rational interval arithmetic, ⇒ κ* ≥ (1,345,000·H₀ − 2,680)/1,340,003
≥ **6730085/10⁷ = 0.6730085** (board row 2, Jo/ainta), conditional on the
same-named axiom set as the 3-point assembly:
`seven_point_certificate` (receipts = cert_data_7pt.json),
`jo_bridge_7pt` (Jo docs/proof.md §4, gap CLZ_GAP_JO_BRIDGE),
`H0_lower` (SHARED with the 3-point; level 6725006930/10¹⁰).
`CLZCert.Assembly7pt.kappa_star_ge_7pt` PROVED (no new gaps; ℚ/ℝ core by
nlinarith from H0_lower).

## Task 1 — the 7-point configuration (extracted from Jo's repo)
- Domain: [0,∞)⁶ (six consecutive gaps); kernel w = k², k = K/K(0),
  K = ½[sinc(πx−1/√2) + sinc(πx+1/√2)] — the SAME kernel as the 3-point.
- Claim (Jo docs/proof.md (4.1)–(4.2)):
  F₆ = Σgᵢ/3000 + Σ_{s=1..6} (2/(7−s))·Σ_{i=1..7−s} w(Σ_{j=i}^{i+s−1} gⱼ)
  ≥ 19/5000  (21 pair-distance terms).
- Jo's recipe (verifier.md + verify_seven.py): grid G=4000, pressure cutoff
  Σg ≥ 45600 cells (=11.4), one-body pruning U(g)=g/3000+w(g)/3 < 19/5000,
  surviving components → 6-D product → bisection with interval + certified-
  convexity tangent pruning. His run: 3 components, 729 initial boxes, 708k
  nodes, 137 s (Arb 128-bit + binary64).
- Assembly target arithmetic (exact): κ* ≥ 0.6730085 requires
  H₀ ≥ 1809026818051/2690000000000 = 0.672500675855…;
  the 3-point H0_lower level (0.6725006930) covers it, margin 1.7e-8.
  **No new H0 gap; no new axioms.**

## Task 2 — the cover (gen_7pt.py + cert_data_7pt.json)
Jo's algorithm re-implemented in EXACT rational interval arithmetic
(scaled by 10⁻⁴⁵; same certified core as the 3-point gen_cert.py, extended
to sinc′/sinc″ alternating series for the tangent machinery). Prune law
respected: one-body + pressure pruning BEFORE the 6-D product / any
min-reduction.
- w-cell table over [0, 45608/4000], w″-lower table over [0.95, …].
- Surviving components (exact): (3808,4778) (7221,9364) (10570,44827)
  — within ±1-2 cells of Jo's Arb-derived components (cross-validation).
- Search: 294,769 nodes, 145,769 terminal boxes (131,035 interval-evidence
  + 14,734 tangent-evidence via exact-LDL convexity); tables 111 s,
  search 491 s, compact 831 s (all detached, single-process).
- **Certified eps′ = 0.0038000211759127863 ≥ 19/5000** (margin 2.1e-8).
- Independent verification (verify_7pt.py, ALL ARMS PASS):
  8,000 mpmath random points (uniform cube, [0,20]⁶, component-targeted,
  pressure-surface band): 0 violations of F₆ ≥ 19/5000;
  volume ledger: emitted + pressure-pruned = initial cell volume (exact);
  in-domain + bound rechecks; 60 interval bounds re-proved;
  w-table spot cross-check vs mpmath minima.

## Task 3 — the assembly variant
`CLZCert/Assembly7pt.lean`: reuses the Interface layer, H0 and H0_lower
from Assembly.lean verbatim; new axioms only `seven_point_certificate`
(19/5000) and `jo_bridge_7pt`; `kappa_star_ge_7pt` PROVED:
  ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (6730085/10⁷ − ε)·N(0,T) ≤ N₀ˢ(0,T).

## WOUND FOUND (3-point lane action needed): S_k2 negative-branch bug
gen_cert.py `S_k2` returns `S_mul(kk,kk)[1]` (the UPPER endpoint of k²)
when the k-interval is negative — overstating w on negative-k boxes. The
correct lower bound is `S_mul(kk,kk)[0]` in BOTH branches (square of the
endpoint closest to 0). Recomputing the LANDED 3-point cert_data.json with
the fix: eps′ drops 221.507e-6 → 0.531e-6; 49/319 boxes fall below the
221.3812e-6 requirement ⇒ **the landed 3-point certificate (6725198/10⁷)
is UNSOUND as certified**. The mathematics is unharmed (Jo's own Arb
verifier proves eps₄ ≥ 221e-6 independently; our 20k-point checks agree) —
the generator must be fixed and the cover re-run at the 3-point stage
(not this lane's clone). The 7-point stage was built AFTER the fix and is
unaffected (its wt[4555] etc. now sit ≤ true cell minima).

## Economy
Tables 111 s, search 491 s, compact 831 s — all detached, single-process;
tables pickled once and reused; Lean build: Assembly7pt compiles clean,
`#print axioms CLZ.kappa_star_ge_7pt` = [propext, CLZ.H0_lower,
CLZ.jo_bridge_7pt, Classical.choice, Quot.sound] — standard three + the
two named gaps only, no native_decide.

## What is next
- Lean build of Assembly7pt (kappa_star_ge_7pt green).
- 3-point lane: apply the S_k2 fix + re-run gen_cert.py (report above).
- Receipt instantiation in Lean (per-box sinc brackets) — same "in flight"
  status as the 3-point; evidence layer: cert_data_7pt.json +
  boxes_7pt.pkl.gz (full per-box bounds).
