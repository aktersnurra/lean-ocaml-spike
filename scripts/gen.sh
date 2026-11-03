#!/usr/bin/env bash
# Interface generator: regenerate the OCaml client from the Lean types, check the checked-in
# copy is up to date, then run the generated-client tests (typed calls, echo round trips,
# v1/v2 agreement, decoder-agreement and mutation fuzz).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"; cd "$ROOT"
# shellcheck disable=SC1091
. versions.env
scripts/extract.sh ocaml/leancore/extracted     # the Lean build runs #gen_ocaml
if ! git diff --quiet -- ocaml/api/spike_api.ml; then
  echo "FAILED: ocaml/api/spike_api.ml is out of date with the Lean types (regenerated copy differs):"
  git --no-pager diff --stat -- ocaml/api/spike_api.ml
  exit 1
fi
echo "generated client is up to date"
D="opam exec --switch=$MALFUNCTION_SWITCH -- dune"
$D build ./ocaml/test/test_api.exe
$D exec --no-build ./ocaml/test/test_api.exe | sed -n '/echo:/,$p'
