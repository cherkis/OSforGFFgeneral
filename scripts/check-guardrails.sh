#!/usr/bin/env bash
# Source-level guardrail check (build-independent), complementing the compile-time guard in
# OSforGFF/Guardrails.lean. Flags anything introduced since the baseline tag
# `pre-unfreeze-baseline`. Runnable manually or via the Stop hook.
#
#   exit 0  → clean (or warnings only)
#   exit 2  → hard violation (new axiom / escape hatch); intended to BLOCK when used as a Stop hook.
set -uo pipefail

REPO="${1:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"   # default: the OSforGFF4D repo
cd "$REPO" 2>/dev/null || { echo "guardrails: repo not found: $REPO"; exit 0; }
BASE="pre-unfreeze-baseline"
git rev-parse -q --verify "refs/tags/$BASE" >/dev/null 2>&1 || { echo "guardrails: baseline tag '$BASE' missing; skipping"; exit 0; }

# Added lines vs baseline, excluding diff headers and the guardrail file itself
# (which legitimately mentions `axiom`/`sorry`).
added() {
  git diff "$BASE" -- OSforGFF ':(exclude)OSforGFF/Guardrails.lean' 2>/dev/null \
    | grep -E '^\+' | grep -Ev '^\+\+\+'
}

fail=0
newax=$(added | grep -E '^\+[[:space:]]*axiom[[:space:]]' || true)
hatch=$(added | grep -E 'native_decide|[^[:alnum:]_]unsafe[^[:alnum:]_]|@\[implemented_by|@\[extern' || true)
sorries=$(added | grep -E '(:=|[^[:alnum:]_]by[^[:alnum:]_]|;)[[:space:]]*sorry[^[:alnum:]_]|[^[:alnum:]_]admit[^[:alnum:]_]|sorryAx' || true)

if [ -n "$newax" ];  then echo "✗ BLOCK: new axiom(s) in source (baseline declares none):" >&2; echo "$newax" >&2; fail=1; fi
if [ -n "$hatch" ];  then echo "✗ BLOCK: escape hatch introduced (native_decide/unsafe/implemented_by/extern):" >&2; echo "$hatch" >&2; fail=1; fi
if [ -n "$sorries" ]; then echo "⚠ WARN: new sorry/admit in source — the build's #print axioms guard is the hard gate:"; echo "$sorries"; fi

if [ "$fail" -ne 0 ]; then
  echo "✗ guardrail BLOCK — resolve before continuing." >&2
  exit 2
fi
[ -z "$sorries" ] && echo "✓ guardrails: clean (no new axiom/sorry/escape-hatch)"
exit 0
