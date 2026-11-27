# clz-cert

Critical-line-zeros (CLZ) certificate umbrella: a 3-point certificate apparatus over
the `zeta23` corpus (anthropics/formal-math, Lean v4.33.0-rc2 / Mathlib 51e6992e),
with the corrected post-S_k2 record, the κ* frontier table, and curated certificate
lanes.

Status: the originally landed `cert_data.json` was found UNSOUND (sibling-lane audit: `S_k2` returned the wrong endpoint on the negative-k branch); it is preserved verbatim as `cert_data_3pt_landed_unsound.json`, with the corrected record in `CERT_REPORT.md` and the dependency/credit map in `BASE.md`.

## Layout

- Root — the corrected three-point certificate apparatus.
- `frontier/` — the true κ* frontier table and the WAIT verdict that prevents filing
  below the live bar (from `clz-frontier` @ `5b7f276b5b41893b989cb4128faa79dd2f902285`).
- `a2/` — the amortized box-arithmetic rework.
- `convex/` — the CLZ-D tangent-bound audit.
- `gaps/` — all three kernel gaps proved.
- `clz-cert-7pt/` — the completed seven-point certificate and independent verification,
  including `cert_data_7pt.json`, `tables_7pt.pkl` and `boxes_7pt.pkl.gz`.

Each curated lane carries a `PROVENANCE.md` naming its exact source commit and
curation rule.

The optional seven-point dataset (~1.9 GB) is not vendored. Scripts that regenerate
or audit it accept `CLZ_CERT_7PT=/path/to/clz-cert-7pt`; the in-repo `clz-cert-7pt/`
is the default, so the variable is only needed for external regeneration data. The
three-point certificate and `frontier/` do not require that dataset.

### Seven-point verification receipt

`clz-cert-7pt/verify_7pt.py` was run after adding the required `tables_7pt.pkl`
byte-for-byte. Result: **ALL ARMS PASS** — 60/131035 interval bounds re-proved, the
volume ledger matched, 8000 mpmath random points had zero violations, and all 57
w-table cross-checks passed. The compact cover has 145769 boxes with
eps' = 0.0038000211759127863 against the 0.0038 target.

## What work can be done here

Open work: land the corrected cert_data.json; extend to the 7-point lane; rerun the gen_cert.py audits (see CERT_REPORT.md).

## License

Licensed under the Copy-Free/Stays-Free (CFSF) License — see [LICENSE](LICENSE). CFSF: copy-free (use for any purpose) and stays-free (nobody may fence this work). Vendored third-party material keeps its upstream license — see [NOTICE](NOTICE.md).

Part of [BigO-Hunter](https://github.com/BigO-Hunter) — independent verification and packaging for [Big O Speedrun](https://bigospeedrun.com) · [org profile](https://github.com/BigO-Hunter/.github) · [bigo-hunter.github.io](https://bigo-hunter.github.io).
