#!/bin/bash
# Emit + kernel-check the box arithmetic for all interval boxes, batch by batch.
# Ledger-driven (boxcheck_ledger.txt: one "ok <lo> <hi> <secs>" line per batch).
cd "$HOME/bigo-campaign/clz-cert" || exit 1
export LAKE_JOBS=1 LEAN_NUM_THREADS=1
LED=CLZCert/Cert/boxcheck_ledger.txt
touch "$LED"
for ((b=0; b<145769; b+=2000)); do
  hi=$((b+2000))
  grep -q "^ok $b " "$LED" && continue
  f=$(printf "CLZCert/Cert/BoxCheck_%06d.lean" "$b")
  python3 -c "import emit_boxcheck as e; e.emit_batch($b, $hi)" >> "$LED.emit" 2>&1 || { echo "EMITFAIL $b" >> "$LED"; continue; }
  t0=$(date +%s)
  if lake env lean "$f" > "/tmp/bc_$b.err" 2>&1; then
    n=$(grep -c "^theorem" "$f")
    printf "ok %s %s %s boxes %ss\n" "$b" "$hi" "$n" "$(( $(date +%s) - t0 ))" >> "$LED"
  else
    printf "FAIL %s %s %ss\n" "$b" "$hi" "$(( $(date +%s) - t0 ))" >> "$LED"
    cp "/tmp/bc_$b.err" "CLZCert/Cert/bcfail_$b.log"
  fi
done
echo "boxcheck runner done" >> "$LED"
