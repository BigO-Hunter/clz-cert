# clz-cert

Lean certificate apparatus for the **critical-line-zeros (κ\*) race**: certified lower
bounds on the share of nontrivial Riemann zeta zeros that are simple AND on the critical
line, built over the `zeta23` corpus (anthropics/formal-math).

> **Board state (Nov 26, 2026): race OPEN — this lane's bound is SUPERSEDED.**
> Current leader: **H. M. Bui + 2 more, κ\* ≥ 0.703703** (Claimed, Nov 20). This repo's
> certified bounds — κ\* ≥ 0.6730085 (7-point) and κ\* ≥ 0.6725198 (3-point) — sit below
> that claim and below the published frontier κ\* ≥ 0.6735382 (Knausgård,
> arXiv:2610.08965). The 7-point value was already published by ainta
> (zeta-simple-zeros, Aug 11, 2026). The lane's own audit (`frontier/VERDICT.md`,
> Nov 7) concluded **WAIT: do not file 0.6730085 — re-target or pivot.** Preserved as a
> verified baseline apparatus, not a competitive entry.

## Results

- **3-point certificate** (root): k(u)²+k(v)²+k(u+v)² ≥ ε₄ on u,v ≥ 0, u+v ≤ 4, with
  certified ε₄ = 221.38139380359024·10⁻⁶ (14,967 boxes, exact rational interval
  arithmetic) ⇒ κ\* ≥ 6725198/10⁷ = 0.6725198, conditional on the named certificate
  axioms. The originally landed cover was found **UNSOUND** (an `S_k2` endpoint bug);
  it is preserved verbatim as `cert_data_3pt_landed_unsound.json`, with the fix and its
  consequences in `CERT_REPORT.md`. The corrected root `cert_data.json` is not yet
  landed — regenerate it with `python3 gen_cert.py`.
- **7-point certificate** (`clz-cert-7pt/`): F₆(g₁,…,g₆) ≥ 19/5000 for all gaps ≥ 0,
  certified ε′ = 0.0038000211759127863 (145,769 boxes) ⇒ κ\* ≥ 6730085/10⁷ = 0.6730085.
  `CLZCert.Assembly7pt.kappa_star_ge_7pt` is proved; independent verification
  (`verify_7pt.py`): **ALL ARMS PASS** — 60/131035 interval bounds re-proved, the volume
  ledger matched exactly, 8000 mpmath random points had zero violations, and all 57
  w-table cross-checks passed.

Both assemblies take the zeta23 Montgomery–Taylor bound H₀ = 0.6725007… as a
parameterized hypothesis (deliberate toolchain mismatch — see `BASE.md`); the certificate
axioms are the only nonstandard assumptions and are named in the axcheck
(`CLZCert/Cert/Ax.lean`).

## Contents

- Root — the corrected three-point apparatus: `CLZCert/` (Kernel, Stability, Gaps,
  Assembly, Cert receipts), the `gen_cert.py` cover generator, and the reports
  (`CERT_REPORT.md`, `RECEIPTS_REPORT.md`, `A2_REPORT.md`, `BASE.md`).
- `frontier/` — the true κ\* frontier table and the WAIT verdict (Nov 7), with sources.
- `a2/` — the amortized box-arithmetic rework (w-cell receipts, boxcheck runners).
- `convex/` — the tangent-bound audit: certified-convexity layer for the 14,734
  tangent-evidence boxes.
- `gaps/` — all three kernel gaps proved.
- `clz-cert-7pt/` — the completed seven-point certificate and its independent verifier.

Each curated lane carries a `PROVENANCE.md` naming its source commit and curation rule.

## Reproduce / verify

Lean (root package; CI builds it on every push — `.github/workflows/lean.yml`,
lean-action with the Mathlib cache):

```bash
lake exe cache get   # built Mathlib oleans (rev pinned in lake-manifest.json)
lake build           # Lean v4.34.1 (lean-toolchain)
```

Certificate data (Python 3, stdlib + mpmath):

```bash
python3 gen_cert.py                 # 3-point cover -> cert_data.json (~1 s)
python3 clz-cert-7pt/verify_7pt.py  # 7-point independent audit (dataset note below)
```

The ~1.9 GB `tables_7pt.pkl` w-cell table is not vendored. Scripts that regenerate or
audit the seven-point lane accept `CLZ_CERT_7PT=/path/to/clz-cert-7pt`; the in-repo
`clz-cert-7pt/` is the default. The three-point certificate and `frontier/` do not
require that dataset.

## Next steps for a continuer

1. Land the corrected root `cert_data.json` and re-level the 3-point Assembly to
   e₀ = 2213813/10¹⁰: the honest post-fix cover does not discharge
   `ThreePointCert (2215072/10¹⁰)` (shortfall 1.258·10⁻¹⁰) — see `CERT_REPORT.md`.
2. Complete the 7-point Lean receipts: the certified-convexity layer for the tangent
   boxes (`convex/`), then w-cell + segment-tree + per-box assemblies (`a2/`; exact
   resume point in `A2_REPORT.md`).
3. To compete in the race: beat the claimed leader κ\* ≥ 0.703703, or the full-Lean bar
   ≈ 0.6734–0.6735. `frontier/FRONTIER.md` is the map; stronger certificates (more
   points, sharper kernels) are the open direction.

## License

Licensed under the Copy-Free/Stays-Free (CFSF) License — see [LICENSE](LICENSE). CFSF:
copy-free (use for any purpose) and stays-free (nobody may fence this work). Vendored
third-party material keeps its upstream license — see [NOTICE](NOTICE.md). This work is
AI-assisted; disclosed.

Part of [BigO-Hunter](https://github.com/BigO-Hunter) — independent verification and packaging for [Big O Speedrun](https://bigospeedrun.com) · [org profile](https://github.com/BigO-Hunter/.github) · [bigo-hunter.github.io](https://bigo-hunter.github.io).