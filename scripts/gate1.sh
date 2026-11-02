#!/usr/bin/env bash
# Gate 1a: trivial pure Lean function -> lambda-box -> Malfunction -> native -> called from OCaml,
# linked with plain `ocamlfind ocamlopt` as the upstream benchmarks do.
# Gate 1b (Dune executable) is `scripts/gate1b.sh`.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
# shellcheck disable=SC1091
. versions.env
BUILD="$ROOT/domain/build"
OCAMLOPT="opam exec --switch=$MALFUNCTION_SWITCH -- ocamlfind ocamlopt -package zarith"

scripts/extract.sh

echo "== 5. Link with ocamlfind ocamlopt =="
mkdir -p "$ROOT/bin"
cp "$ROOT/app/main.ml" "$BUILD/gate1_main.ml"
(
  cd "$BUILD"
  $OCAMLOPT -I . -linkpkg decidable.cmx eq.cmx LeanArray.cmx nat.cmx int.cmx axioms.cmx \
    gate1.cmx gate1_main.ml -o "$ROOT/bin/gate1"
)

echo "== 6. Smoke test (gate1 n = 2n + 1, including a bignum) =="
check() { got="$("$ROOT/bin/gate1" "$1")"; [ "$got" = "$2" ] || { echo "FAIL: gate1 $1 = $got, want $2"; exit 1; }; echo "ok: gate1 $1 = $got"; }
check 0 1
check 5 11
check 1267650600228229401496703205376 2535301200456458802993406410753   # 2^100 -> 2^101 + 1

echo "== Gate 1a PASSED =="
