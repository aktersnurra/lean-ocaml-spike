#!/usr/bin/env bash
# Gate 2: opaque bytes -> bytes boundary (option (a): List Nat transport), via Dune.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
# shellcheck disable=SC1091
. versions.env
scripts/extract.sh ocaml/leancore/extracted
opam exec --switch="$MALFUNCTION_SWITCH" -- dune build ./ocaml/bin/main.exe ./ocaml/test/test_gate2.exe
opam exec --switch="$MALFUNCTION_SWITCH" -- dune exec --no-build ./ocaml/test/test_gate2.exe
