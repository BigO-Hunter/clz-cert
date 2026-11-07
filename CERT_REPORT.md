# CERT_REPORT — CLZ 3-point certificate (staged status, 2026-11-06)

## Verdicts
- BASE (stage 1): DONE. zeta23 = anthropics/formal-math (Lean Verified, board row 3);
  exact interface inlined in CLZCert/Assembly.lean (def layer verbatim from
  ChallengeDeps.lean). Toolchain mismatch deliberate: our tree = v4.34.1 +
  shared Mathlib d13f23b7 (12s builds); Theorem D enters as named hypothesis.
- STABILITY (stage 2): Psi + Psi_nonneg + Psi_ge_support PROVED (Stability.lean);
  Hermitian trace core (2.1)/(3.4) recorded exactly as CLZ_GAP_RANKTRACE /
  CLZ_GAP_DUALFORM, consumed via the single parameterized `jo_bridge`.
- CERTIFICATE (stage 3): generator DONE + committed (exact scaled-int interval
  arithmetic; angle-reduced series; cross-checked vs mpmath 50dps at 17 probe
  points, all contained, widths ~1e-30 at points). LEAN RECEIPTS PENDING: the
  2D adaptive cover certified only eps' = 102.499e-6 (< target 221.3813e-6) at
  34.7M boxes — box bound = sum of per-axis range minima loses cross-terms.
  Next lever (next session): Jo's recipe — fixed grid G, per-cell series bounds,
  sparse-table range minima + his one-body pruning structure; then emit
  per-box sinc_bracket receipts (Kernel.sinc_bracket already PROVED as the
  consumer contract).
- ASSEMBLY (stage 4): kappa_star_ge PROVED (Assembly.lean, kernel-checked):
  forall eps>0 exists T0, (6725197/10^7 − eps)·N ≤ N0s — beats H = 0.6725007.
  Inputs: jo_bridge (CLZ_GAP_JO_BRIDGE), H0_lower ≥ 6725006040/10^10
  (CLZ_GAP_H0; exact requirement H0 ≥ C(1−e0/2)+e0/4 = 0.67250060368…,
  true H0 = 0.67250070368 — margin 1.0e-7).
- 7-POINT (stage 5): SKIPPED per plan (stage 1 receipt set not landed).

## axcheck
Assembly: statements use axioms jo_bridge, H0_lower (both CLZ_GAP-tagged);
kappa_star_ge's proof is axiom-free over those + Mathlib. Kernel: pi_gt_d20/
pi_lt_d20 (Mathlib), sqrt2/a bounds proved by squaring; named gaps
CLZ_GAP_SINPOS, CLZ_GAP_TAIL. No native_decide; no new axioms beyond the
named interface.

## Ground truth (mpmath, 50 dps)
H0 = 0.672500703679411645734…; B(e0) at e0 = 221.3813e-6 → 0.6725198…
headline needs certified eps' ≥ 221.3812e-6; Jo's 221e-6 → 0.6725197671…
(floors to 6725197/10^7). True min f* ≈ 222.149e-6 at (u,v) ≈ (1.05308, 2.01204).
