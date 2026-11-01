#!/usr/bin/env bash
# Build the upper-bound base targets, then one listed production target per call.
# Run from the repository root. Requires Bash, Lake, systemd user scopes,
# GNU time, nice, free and awk. MEMCAP defaults to 12G; swap is disabled per scope.
# Lake may build dependencies concurrently within a target. This loop does not
# guarantee a single Lean process or establish axiom/fidelity verification.
# Existing compatible artifacts may be reused by Lake; no cache hit is promised.
set -u
LOG="${1:?usage: negsign_gate_driver.sh <logfile>}"
CAP="${MEMCAP:-12G}"
MANIFEST="scripts/negsign_prod_module_order.txt"
if [[ ! -r "$MANIFEST" || ! -s "$MANIFEST" ]]; then
  echo "Missing or empty module manifest: $MANIFEST" >&2; exit 64
fi
mapfile -t modules < "$MANIFEST" || exit 64
for m in "${modules[@]}"; do
  if [[ ! "$m" =~ ^[A-Za-z0-9_]+$ ]]; then
    echo "Invalid module name in $MANIFEST: $m" >&2; exit 64
  fi
done
echo "# gate driver start $(date -u +%FT%TZ) tip=$(git rev-parse HEAD) cap=$CAP" >> "$LOG"
echo "## phase 1: base library" >> "$LOG"
systemd-run --user --scope -q -p MemoryMax="$CAP" -p MemorySwapMax=0 nice -n 10 \
  lake build KsIndexLean.AlphaTrialTableData KsIndexLean.NegSignRationalTails \
    KsIndexLean.NegSignDecomposition KsIndexLean.NegSignTailIntervals \
    KsIndexLean.NegSignEndpointBridge KsIndexLean.AlphaRemarkEndpoints >> "$LOG" 2>&1 \
  || { echo "PHASE1 FAIL $(date -u +%FT%TZ)" >> "$LOG"; exit 1; }
echo "## phase 2: production modules, serialized" >> "$LOG"
# Sample available system memory every 20 seconds for the log.
( while true; do echo "MEMWATCH $(date -u +%T) $(free -m | awk '/^Mem:/{print $3" used MB, "$7" avail MB"}')" >> "$LOG"; sleep 20; done ) &
WATCHPID=$!
trap 'kill $WATCHPID 2>/dev/null' EXIT
for m in "${modules[@]}"; do
  /usr/bin/time -f "$m %e s %M KB exit=%x" -o /tmp/negsign_t.$$ \
    systemd-run --user --scope -q -p MemoryMax="$CAP" -p MemorySwapMax=0 nice -n 10 \
    lake build "KsIndexLean.$m" > /dev/null 2>&1
  rc=$?
  cat /tmp/negsign_t.$$ >> "$LOG"
  if [ $rc -ne 0 ]; then echo "FAIL $m rc=$rc $(date -u +%FT%TZ)" >> "$LOG"; exit 2; fi
done
rm -f /tmp/negsign_t.$$
echo "# gate driver COMPLETE $(date -u +%FT%TZ)" >> "$LOG"
