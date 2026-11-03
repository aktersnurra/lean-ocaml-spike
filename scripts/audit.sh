#!/usr/bin/env bash
# Gate 3 audits:
#  1. Proof axioms: every theorem/definition in domain/Spike/Audit.lean depends only on
#     {propext, Quot.sound} (no sorryAx, no Classical.choice, no ofReduceBool).
#     (Spike/Codec/Derive.lean and Spike/Codec/OCaml.lean are metaprograms: they run at
#     elaboration time and are never extracted, so they are not in the list below.)
#  2. Extracted core stays free of `partial`, `implemented_by`, `extern`, `Float`,
#     `native_decide` and `unsafe`.
#  3. Runtime axiom surface: the OCaml-side axioms the extracted modules actually reference
#     are exactly the documented set (scripts/runtime-axioms.txt).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"; cd "$ROOT"
export PATH="$HOME/.elan/bin:$PATH"
fail=0

echo "== proof axioms =="
out="$(cd domain && lake env lean Spike/Audit.lean 2>&1 | grep -E "axioms|does not depend")"
echo "$out"
bad="$(echo "$out" | grep "depends on axioms" | sed 's/.*\[\(.*\)\]/\1/' | tr ',' '\n' | tr -d ' ' | grep -vxE 'propext|Quot.sound' || true)"
[ -z "$bad" ] || { echo "FAIL: disallowed axioms: $bad"; fail=1; }
[ "$(echo "$out" | wc -l)" -ge 10 ] || { echo "FAIL: audit printed fewer lines than expected"; fail=1; }

echo "== forbidden constructs in the extracted core =="
if grep -nE '\b(partial|implemented_by|extern|Float|native_decide|unsafe)\b' \
     domain/Spike/Gate1.lean domain/Spike/Wire.lean domain/Spike/Order.lean domain/Spike/Gate2.lean \
     domain/Spike/Codec.lean domain/Spike/Api.lean \
     | grep -vE '^\S+:[0-9]+:\s*(--|/-|No `partial`|or anything)' ; then
  echo "FAIL: forbidden construct found"; fail=1
else echo "none"; fi

echo "== runtime axioms referenced by extracted code =="
got="$(cat domain/build/gate1.mlf domain/build/gate2.mlf domain/build/api.mlf | grep -o 'global \$Axioms \$[A-Za-z0-9_]*' | sed 's/.*\$//' | sort -u)"
echo "$got"
if ! diff <(echo "$got") <(grep -v '^#' scripts/runtime-axioms.txt | sed '/^$/d' | sort -u); then
  echo "FAIL: runtime axiom set differs from scripts/runtime-axioms.txt"; fail=1
fi
[ $fail = 0 ] && echo "== audit PASSED ==" || { echo "== audit FAILED =="; exit 1; }
