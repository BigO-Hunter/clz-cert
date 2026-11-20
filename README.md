# clz-cert

Critical-line-zeros (CLZ) certificate lane: a 3-point certificate apparatus over the `zeta23` corpus (anthropics/formal-math, Lean v4.33.0-rc2 / Mathlib 51e6992e), with the corrected post-S_k2 record.

Status: the originally landed `cert_data.json` was found UNSOUND (sibling-lane audit: `S_k2` returned the wrong endpoint on the negative-k branch); it is preserved verbatim as `cert_data_3pt_landed_unsound.json`, with the corrected record in `CERT_REPORT.md` and the dependency/credit map in `BASE.md`.

## Why this repo is up

Public evidence for the critical-line-zeros certificate lane: the corrected post-S_k2 record with the unsound landed artifact preserved verbatim — the audit trail is the public good.

[BigO-Hunter](https://github.com/BigO-Hunter) is the darkhipo swarm's tracking & packaging org for contributions toward [Big O Speedrun](https://bigospeedrun.com) — a companion, never the project. Org story: [profile](https://github.com/BigO-Hunter/.github) · [bigo-hunter.github.io](https://bigo-hunter.github.io).

## What work can be done here

Open work: land the corrected cert_data.json; extend to the 7-point lane; rerun the gen_cert.py audits (see CERT_REPORT.md).

## License

Licensed under the Copy-Free/Stays-Free (CFSF) License — see [LICENSE](LICENSE). CFSF: copy-free (use for any purpose) and stays-free (nobody may fence this work). The name is unclaimed in software licensing (checked 2026-11-09) and is deliberately not "Copyfree" — the Copyfree Initiative's certification mark — since CFSF's anti-enclosure condition is excluded by their standard.  Vendored third-party material keeps its upstream license — see [NOTICE](NOTICE.md).

## Umbrella layout and optional seven-point data

The repository root remains the corrected three-point certificate apparatus. `frontier/` contains the complete original `clz-frontier` repository at source commit `5b7f276b5b41893b989cb4128faa79dd2f902285`, merged with full history: the true κ* frontier table and the WAIT verdict that prevents filing below the live bar.

The optional seven-point dataset is approximately 1.9 GB and is not vendored. Scripts that regenerate or audit it accept `CLZ_CERT_7PT=/path/to/clz-cert-7pt`; the three-point certificate and `frontier/` material do not require that dataset.

## Curated local certificate lanes

- `a2/`: the amortized box-arithmetic rework, curated from local `clz-cert` at `368d4f06cf36`.
- `convex/`: the CLZ-D tangent-bound audit, curated from local `clz-cert-convex` at `f5bbeac23ab3`.
- `gaps/`: all three kernel gaps proved, curated from local `clz-cert-gaps` at `f2b0587921d2`.
- `clz-cert-7pt/`: the completed seven-point certificate and independent verification, curated from local `9981db6ba9e3`, including `cert_data_7pt.json`, `tables_7pt.pkl` and `boxes_7pt.pkl.gz`.

These are final committed-tree snapshots rather than full-history imports; each carries a `PROVENANCE.md` naming its exact source commit and curation rule. The seven-point scripts' default `clz-cert-7pt` path now exists in this umbrella, so `CLZ_CERT_7PT` is only needed for external regeneration data.

### Seven-point verification receipt

The included `clz-cert-7pt/verify_7pt.py` was run after adding the required `tables_7pt.pkl` byte-for-byte. Result: `ALL ARMS PASS` — 60/131035 interval bounds re-proved, the volume ledger matched, 8000 mpmath random points had zero violations, and all 57 w-table cross-checks passed. The compact cover has 145769 boxes with eps' = 0.0038000211759127863 against the 0.0038 target.

### Seven-point verification receipt

The included `clz-cert-7pt/verify_7pt.py` was run after adding the required `tables_7pt.pkl` byte-for-byte. Result: `ALL ARMS PASS` — 60/131035 interval bounds re-proved, the volume ledger matched, 8000 mpmath random points had zero violations, and all 57 w-table cross-checks passed. The compact cover has 145769 boxes with eps' = 0.0038000211759127863 against the 0.0038 target.
