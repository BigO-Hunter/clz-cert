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
