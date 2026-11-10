#!/usr/bin/env bash
# Copyright 2026 Benjamin Stanley Frohman. Apache-2.0.
# 1) Reject forbidden tokens in the Lean sources.
# 2) Re-elaborate the audit file and require that every theorem depends only
#    on Lean's three standard axioms (propext, Classical.choice, Quot.sound).
set -euo pipefail
cd "$(dirname "$0")/.."

echo "== forbidden-token scan =="
if grep -rnE '\b(sorry|admit|native_decide|implemented_by)\b|^\s*(axiom|unsafe|opaque)\b' \
     --include='*.lean' MetriplecticNS.lean MetriplecticNS scripts/PrintAxioms.lean \
   | grep -v 'Zero-sorry' \
   | grep -v 'no sorry' \
   | grep -v 'standard axioms'; then
  echo "FAIL: forbidden token found"; exit 1
fi
echo "OK: no sorry/admit/axiom/native_decide/opaque/unsafe in MetriplecticNS.lean, MetriplecticNS/*.lean"

echo "== #print axioms =="
out="$(lake env lean scripts/PrintAxioms.lean 2>&1)"
echo "$out"
expected=$(grep -c '^#print axioms' scripts/PrintAxioms.lean)
got=$(printf '%s\n' "$out" | grep -cE "depends on axioms|does not depend on any axioms" || true)
if [ "$got" -ne "$expected" ]; then
  echo "FAIL: expected $expected axiom reports, got $got"; exit 1
fi
bad=$(printf '%s' "$out" | tr '\n' ' ' | grep -oE 'depends on axioms: \[[^]]*\]' \
      | sed -E 's/.*\[(.*)\]/\1/' | tr ',' '\n' | tr -d ' ' | sed '/^$/d' \
      | grep -vxE 'propext|Classical\.choice|Quot\.sound' || true)
if printf '%s\n' "$out" | grep -qiE "error|sorryAx"; then
  echo "FAIL: errors or sorryAx in axiom audit"; exit 1
fi
if [ -n "$bad" ]; then
  echo "FAIL: non-standard axioms: $bad"; exit 1
fi
echo "OK: all $expected declarations use only propext, Classical.choice, Quot.sound"
