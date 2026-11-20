#!/bin/bash
# CLZ-A2 wcell emission runner: emit -> kernel-check -> ledger -> repeat.
# Resumable: a block is skipped when the ledger already has an "ok" line for it.
# Usage: ./run_cells.sh [start] [stop] [batch]
cd "$(dirname "$0")" || exit 1
START=${1:-0}
STOP=${2:-45608}
BATCH=${3:-64}
LEDGER=CLZCert/Cert/cells_ledger.txt
touch "$LEDGER"
export LAKE_JOBS=1 LEAN_NUM_THREADS=1
for ((b=START; b<STOP; b+=BATCH)); do
  hi=$((b+BATCH)); [ $hi -gt $STOP ] && hi=$STOP
  if grep -q "^ok $b " "$LEDGER"; then continue; fi
  python3 slim.py stage "$b" "$hi" "$BATCH" >> "$LEDGER.emit" 2>&1 || { echo "EMITFAIL $b" >> "$LEDGER"; continue; }
  f=$(printf "CLZCert/Cert/Slim_%05d.lean" "$b")
  t0=$(date +%s)
  if lake env lean "$f" > "/tmp/cells_$b.err" 2>&1; then
    printf "ok %s %s %s %ss\n" "$b" "$hi" "$(shasum -a 256 "$f" | cut -c1-16)" "$(( $(date +%s) - t0 ))" >> "$LEDGER"
  else
    printf "FAIL %s %s %ss\n" "$b" "$hi" "$(( $(date +%s) - t0 ))" >> "$LEDGER"
    cp "/tmp/cells_$b.err" "CLZCert/Cert/fail_$b.log"
  fi
done
echo "runner done" >> "$LEDGER"
