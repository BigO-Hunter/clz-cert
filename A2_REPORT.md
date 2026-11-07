# A2_REPORT — the emission run (lane CLZ-A2), 2026-11-07

## Headline: 272 / 45,608 w-cells kernel-verified; `seven_point_certificate` still an axiom

Nothing below is claimed that the kernel has not checked. The emission is now a
*measured, resumable pipeline*, not a design: the per-cell proof shape compiles
and a detached runner is grinding through the table.

## Stage counts

| stage | count | state |
|---|---|---|
| wcell (per-cell `W_i ≤ kk x²`) | **272 / 45,608** | kernel-verified, runner live |
| wrange (segment-tree over 13,500 distinct sum-ranges) | 0 / 13,500 | not emitted (needs all cells) |
| box assemblies (interval evidence) | 0 / 131,035 | not emitted |
| obcell one-body + span dispatch | 0 / 8,235 | not emitted |
| combo subtrees + top dispatch | 0 / 729 | not emitted |
| `seven_point_certificate` discharge | **NO** | remains `axiom` (Assembly7pt.lean, sibling tree) |

Measured cost: **~2.1 s/cell** (blocks of 64 compile in 128–154 s wall on a host
at load 108; blocks 0–16 were 8.7 s/cell because they are reflected cells with
multi-piece windows). Extrapolation for cells alone: **≈26 h kernel**, then the
box stage (131,035 × 21 term applications) which is expected to dominate again.

## What is landed and compiling (this lane)

1. **`slim.py`** — the per-cell emitter, **31 KB/cell vs the predecessor's
   63–100 KB** (4.5 GB → ~1.4 GB total), and it fixes a real bug: the
   predecessor's `emit_ser` joined the series terms with `" + "` only, dropping
   the alternating signs, so every cumulative `c_k`/`d_k` fact after k=0 was
   FALSE (its own smoke file could not compile: `linarith failed` at the
   `hb2d1` family). `slim.py` instead emits 9 generic `pow_odd_mono` facts plus
   ONE `norm_num` polynomial fact per direction, and takes the tail from a new
   proved glue lemma `sin_series_sandwich15` (decimal tail `1e-15 ≥ chiG`), so
   per-cell proofs never carry the `chiG` atom.
2. **`CLZCert/Cert/Const.lean`** — `chiG_le`, `sin_series_sandwich15`
   (both stdlib-only). **`CLZCert/Cert/Slim_00000.lean`** — 16 cells, 0 errors.
3. **`run_cells.sh`** — the resumable detached runner: emit block → `lake env
   lean` → append `ok <lo> <hi> <sha16> <secs>` to `CLZCert/Cert/cells_ledger.txt`.
   A block is skipped only when the ledger has an `ok` line, so a failed or
   killed block is retried on the next sweep. Observed failure mode: empty
   `flake` logs (killed processes, no diagnostics) at blocks 272 and 336 —
   environmental, retried automatically.
4. **Task 0** (`check_wt900.py`, 50-digit mpmath recomputation against the
   definition): true `w(900) = 0.8545272556`, cell min `0.8542240739`; the
   sibling's `wt[900] = 7.5788e74` is GARBAGE-HIGH (a probability > 1) and is
   the only cell in 898–902 above the true minimum. It is sound for their
   certificate ONLY because every sum-range there is ≥120 cells wide (a
   garbage-high cell can never be a range MIN); it would be unsound for a
   single-cell range, so their `_sinc_piece`/`S_reduce` straddle should be
   fixed on their side (their file, not edited here). Their 898/899/901/902 are
   loose-LOW (sound, weak). My mirror is a valid lower bound at every cell and
   is tight at 898–900. Both tables are loose near `t1 = 0` (cells ~900–903:
   0.361 vs true 0.854) from the `P/thi` corner of the division bracket —
   improvement noted: extend `sinc_near1` to small POSITIVE `t1` windows
   (`t1hi ≤ δ`), not only `t1lo < 0`. Harmless for the certificate (4 cells can
   never be a ≥120-cell range minimum).
5. **Task 3** (`emit_tangent.py`, `CLZCert/Cert/Tangent.lean`,
   `CLZCert/Cert/TangentReceipt.lean`, `tangent_boxes.json`): CLZ-D's convexity
   layer is adopted verbatim (kernel-agnostic, compiles here) and the tangent
   receipts are emitted as the parameterized shape consuming it:
   `tangent_box_receipt` (box bound from `tangent_assembly`),
   `tangent_box_close` (the `19/5000` receipt with the §4b correction),
   `mcert_dispatch` (one `mcert_<hash>` per distinct 21-μ tuple, `D ≥ 0` so
   singular boxes are kept — never per box). `tangent_boxes.json` carries the
   14,734 boxes with the §4b slack charged per box. My independent re-run of
   their audit reproduces it exactly: **0 / 14,734 boxes lost**, min margin
   **7.000966e-4** (box 28591), tightest raw margin 8.151151e-4, and the
   smallest argument cell is 3808 → `x ≥ 0.9520`, so tangent boxes are positive
   windows and the `x < 0` mirrored bracket is genuinely unneeded.
   **Named residual:** the per-box μ tuple comes from the `w2` cell table +
   `wrange` dispatch, which is CLZ-D's `DerivBounds.lean` — no `.olean` in their
   tree at session end, so `tangent_lower_wfun`/`wfunD2_lb` are not yet
   consumable; the receipt shape compiles and needs only the data.

## Axiom footprint (measured, `#print axioms`)

```
CLZ.Cert.sin_series_sandwich15 : [propext, Classical.choice, Quot.sound]
CLZ.Cert.tangent_box_close     : [propext, Classical.choice, Quot.sound]
CLZ.Cert.mcert_dispatch        : [propext, Classical.choice, Quot.sound]
CLZ.kappa_star_ge   (3-pt)     : [propext, jo_bridge, Classical.choice, Quot.sound]
```
Every brick added this session is stdlib-only. `kappa_star_ge_7pt` currently
also lists `H0_lower` (now a theorem in this tree: it does NOT appear in the
3-pt footprint) and `seven_point_certificate`. After discharge its footprint
contracts to `[propext, CLZ.jo_bridge_7pt, Classical.choice, Quot.sound]` —
that target is unchanged and nothing emitted so far can add to it.

## Exact resume point

```bash
cd ~/bigo-campaign/clz-cert
./run_cells.sh 0 45608 16        # ledger-driven: skips ok blocks, retries FAIL
```
Then, in order: (a) check `cells_ledger.txt` reaches 45,608 with no FAIL;
(b) emit wrange (13,500 segment-tree nodes over the cell lemmas); (c) emit the
131,035 box assemblies (21 wrange applications + pressure + `linarith` per box —
expect this to cost more than the cell stage; consider hoisting one block-dispatch
lemma per distinct (range-tuple) as with `mcert`); (d) 8,235 obcell one-body +
span dispatch; (e) 729 combo subtrees + top dispatch; (f) the one-line
`seven_point_certificate` swap in Assembly7pt.lean and `#print axioms`
`kappa_star_ge_7pt`.

Wound for the record: the box stage is the unmeasured risk. 131,035 boxes ×
(21 term facts + 6-variable linear arithmetic) may exceed the cell stage by a
large factor; the `mcert`-style hoist (one dispatch lemma per distinct
range-tuple) is the mitigation to try FIRST, before emitting 131,035 proofs.
