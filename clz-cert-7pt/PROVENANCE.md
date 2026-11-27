# Provenance — clz-cert-7pt

Source: the `clz-cert-7pt` campaign working clone at `9981db6ba9e3888404ff4121b0391b9aa4117923`.

This is a curated final committed-tree snapshot, not a full-history merge. The local repository's git/build history is approximately 1.8 GB, so history was not imported. Build outputs, logs, caches and files over 50 MB were excluded. Copied 23 tracked files. Oversize omissions: none.

The snapshot includes the certificate/proof sources and, for clz-cert-7pt, the final certificate data (`cert_data_7pt.json`, `boxes_7pt.pkl.gz`) rather than only the report. The ~1.9 GB `tables_7pt.pkl` w-cell table is not vendored; scripts that need it accept `CLZ_CERT_7PT=/path/to/clz-cert-7pt`.


tables_7pt.pkl was untracked in the source checkout and is not vendored here (~1.9 GB); verify_7pt.py requires it — point `CLZ_CERT_7PT` at a directory holding it. The vendored `cert_data_7pt.json` and `boxes_7pt.pkl.gz` carry the certificate itself.
