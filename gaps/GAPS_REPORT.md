# GAPS_REPORT — lane CLZ-B (the three kernel gaps), 2026-11-06

Working clone: `clz-cert-gaps` (fresh clone of clz-cert @ bcddb76).
Commits: `8aa2507` (Kernel gaps), `H0 commit` (Gaps.lean + Assembly swap).
Build: `lake build` fully green; LAKE_JOBS=1, LEAN_NUM_THREADS=1; Mathlib
oleans per lake-manifest.json (rev d13f23b7; `lake exe cache get`).

## Per-gap verdicts

### 1. CLZ_GAP_TAIL — PROVED (restated; the original statement was false)
- Kernel.lean: `CLZ.alt_partial_bound`, `CLZ.alternating_tail_range`,
  `CLZ.alternating_tail`.
- **Restatement note**: the original statement
  `|(∑' k, (-1)^k * b k) - ∑_{range N} (-1)^k * b k| ≤ b N` is FALSE as
  written: for a merely conditionally convergent series (e.g. `b k =
  1 + 1/(k+1)`) the tsum does not exist (HasSum over the finite-set net
  fails), so `tsum` defaults to 0 and the bound fails. Restated with the
  necessary hypothesis `(hsumm : Summable fun k => (-1)^k * b k)` — same
  conclusion. Consumers unaffected: per-box receipts use finite partial
  sums, for which the companion `alternating_tail_range` (proved, no
  summability needed) is the right interface:
  `∀ n ≥ N, |S_n − S_N| ≤ b N`.
- Proof: pointwise two-invariant induction on even/odd partial sums —
  `0 ≤ E_j ≤ O_j ≤ c 0` propagates since `E_{j+1} = O_j − c(2j+1)` and
  `O_{j+1} = O_j − c(2j+1) + c(2j+2) ≤ O_j`; then N-shift by
  `sum_range_add_sum_Ico` + sign-shift reindexing; then ε-quantifier closure
  against the HasSum limit.

### 2. CLZ_GAP_SINPOS — PROVED
- Kernel.lean: `CLZ.a_sin_ne : sin a ≠ 0` — via `0 < a < π` and
  `sin_pos_of_pos_of_lt_pi` (no series needed). Quantitative companion
  `CLZ.sin_a_pos : 0 < sin a` in Gaps.lean.

### 3. CLZ_GAP_H0 — PROVED (full statement, tan-sandwich route)
- Gaps.lean (new file): `CLZ.H0_tan_sandwich :
  (6725006930:ℝ)/10^10 ≤ 2 − 1/(sqrt 2 * Real.tan (1/sqrt 2) /
  (1 + 1/sqrt 2 * Real.tan (1/sqrt 2)))` — statement-wise the exact old
  `axiom H0_lower` (H0 = 2 − 1/cMT unfolded).
- Route: algebra gives H0 = 3/2 − 1/(√2·tan a) (1/cMT = 1/(√2 t) + 1/2);
  alternating partial-sum enclosures on a ∈ [xl, xh]
  (xl = 7071067811865475244/10¹⁹, xh = …245/10¹⁹, from a_lb/a_ub):
  `sin_a_lb`, `cos_a_ub` (exact ℚ literals); tan a ≥ sin_lb/cos_ub
  (`tan_a_lb`, div_le_div₀); exact-ℚ close `h0_num` (norm_num):
  √2_lb·sin_lb/cos_ub ≥ 1/(3/2 − 6725006930/10¹⁰) — margin 1.56e-8 on the
  √2·tan product (≥ 1.2084602421 vs needed 1.2084602265).
- Workhorse lemmas (Kernel.lean, PROVED, reusable by CLZ-A receipts):
  `sin_partial_abs_bound`, `cos_partial_abs_bound` — |sin x − partial| ≤
  x^(2n+3)/(2n+3)!, |cos x − partial| ≤ x^(2n+2)/(2n+2)! for x ≥ 0 with
  x² ≤ 6 / x² ≤ 2.

### 4. AXCHECK — final footprint
- `#print axioms CLZ.kappa_star_ge` →
  **[propext, CLZ.jo_bridge, Classical.choice, Quot.sound]**
  = stdlib + `jo_bridge` ONLY.
- All gap lemmas (`H0_tan_sandwich`, `sin_a_lb`, `cos_a_ub`, `tan_a_lb`,
  `alternating_tail`, `alternating_tail_range`, `sin/cos_partial_abs_bound`,
  `a_sin_ne`, `alt_partial_bound`): stdlib only.
- `three_point_certificate` is CLZ-A's lane (receipts instantiating
  `Kernel.sinc_bracket` — my `alternating_tail_range` +
  sin/cos partial bounds are the interfaces its per-box ℚ data needs; both
  are proved, so receipt instantiation has no remaining kernel blocker).

## Assembly.lean change (merge note for coordinator)
- ONE semantic change: `axiom H0_lower` → `theorem H0_lower … :=
  by unfold H0 cMT; exact CLZ.H0_tan_sandwich`; import line now
  `import CLZCert.Gaps`. If CLZ-A also edits Assembly (certificate
  discharge), the merge is line-disjoint (different axiom lines).

## Landmines hit (for the record)
- `.lake/packages` must contain BUILT Mathlib oleans: run `lake exe cache get`
  after checkout (CI's lean-action supplies them via the mathlib cache);
  empty package clones → "unknown module prefix Mathlib".
- Factorial postfix `!` is SCOPED notation here: `open scoped Nat` required
  per file; `(e:ℕ)!` does not parse — write `((e)! : ℝ)`.
- `HasSum.congr` / `tsum_conr` / `mul_sum` / `abs_add` / `pow_le_pow_left`
  do not exist in this Mathlib (use `simpa only [mul_div_assoc]` via
  HasSum, `Finset.mul_sum` is `Finset.mul_sum`-less — `sum_sign_shift`
  induction instead, `abs_add_le`, `pow_le_pow_left₀`); `div_lt_one` and
  `div_le_div_iff₀` are IFFs; `mul_le_mul` arg order (h₁ h₂ c0 b0);
  `Nat.Even` unfolds to `j + j`; `rwa` fails when the rewrite leaves `< ε/2`
  vs `< ε`.
