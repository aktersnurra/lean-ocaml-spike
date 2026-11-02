#!/usr/bin/env bash
# Gate 3 (OCaml 4.14 switch): round-trip/robustness tests with differential fuzz,
# proof/runtime axiom audit, and benchmark vs native. OCaml 5 domain + Eio tests are in
# scripts/gate3-ocaml5.sh.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"; cd "$ROOT"
# shellcheck disable=SC1091
. versions.env
scripts/extract.sh ocaml/leancore/extracted
D="opam exec --switch=$MALFUNCTION_SWITCH -- dune"
$D build ./ocaml/test/test_gate2.exe ./ocaml/test/test_gate3.exe ./ocaml/bench/bench.exe
$D exec --no-build ./ocaml/test/test_gate2.exe | tail -1
$D exec --no-build ./ocaml/test/test_gate3.exe | sed -n '/random valid/,$p'
scripts/audit.sh
$D exec --no-build ./ocaml/bench/bench.exe
