#!/usr/bin/env bash
# Build everything and require the main theorems to use only the standard axioms.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build
out=$(lake env lean Verification/Axioms.lean 2>&1)
printf '%s\n' "$out"
if printf '%s\n' "$out" | grep -q 'sorryAx'; then echo "verify: an open proof (sorryAx) remains" >&2; exit 2; fi
if printf '%s\n' "$out" | grep -E "depends on axioms" | grep -vE "\[propext, Classical.choice, Quot.sound\]" | grep -q .; then
  echo "verify: a non-standard axiom appears" >&2; exit 2; fi
echo "verify: OK"
