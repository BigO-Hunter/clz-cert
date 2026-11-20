#!/bin/bash
# Sweep the cell stage until the ledger holds 45,608 verified cells.
# run_cells.sh skips blocks with an `ok` line, so each pass retries the FAILs.
cd "$HOME/bigo-campaign/clz-cert" || exit 1
for pass in 1 2 3 4 5 6; do
  ./run_cells.sh 0 45608 16
  n=$(awk '$1=="ok"{s+=$3-$2} END{print s+0}' CLZCert/Cert/cells_ledger.txt)
  f=$(grep -c "^FAIL" CLZCert/Cert/cells_ledger.txt)
  echo "pass $pass: $n/45608 cells ok, $f FAIL lines" >> CLZCert/Cert/cells_ledger.txt
  [ "$n" -ge 45608 ] && break
done
