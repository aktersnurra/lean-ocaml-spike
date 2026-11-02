#!/usr/bin/env bash
# Gate 1b: link the extracted object into a Dune executable and run the smoke test.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
# shellcheck disable=SC1091
. versions.env
scripts/extract.sh ocaml/leancore/extracted
opam exec --switch="$MALFUNCTION_SWITCH" -- dune build ./ocaml/bin/main.exe
EXE="$ROOT/_build/default/ocaml/bin/main.exe"
check() { got="$("$EXE" "$1")"; [ "$got" = "$2" ] || { echo "FAIL: $1 -> $got, want $2"; exit 1; }; echo "ok: $1 -> $got"; }
check 0 1
check 5 11
check 1267650600228229401496703205376 2535301200456458802993406410753   # 2^100 -> 2^101 + 1
if "$EXE" -1 >/dev/null 2>&1; then echo "FAIL: negative input accepted"; exit 1; else echo "ok: -1 rejected at the boundary"; fi
echo "== Gate 1b PASSED =="
