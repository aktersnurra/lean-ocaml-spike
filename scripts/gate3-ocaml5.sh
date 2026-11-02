#!/usr/bin/env bash
# Gate 3 OCaml 5 tests: compile the same extracted core with the OCaml 5.3 switch and run
# the domain-concurrency stress test and (separately) the Eio fiber test.
# The switch: OCaml 5.3.0+flambda, malfunction at MALFUNCTION_REV installed with
# --ignore-constraints-on=ocaml (its opam file says ocaml < 5.0 although the source supports
# 5.2/5.3), zarith, dune, eio_main. See README.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"; cd "$ROOT"
SW=spike-ocaml5
SPIKE_MALFUNCTION_SWITCH=$SW scripts/extract.sh ocaml/leancore/extracted
opam exec --switch=$SW -- dune build --build-dir _build_ocaml5 ./ocaml/conc/domains_stress.exe ./ocaml/conc/eio_stress.exe ./ocaml/test/test_gate3.exe
B=_build_ocaml5/default/ocaml
opam exec --switch=$SW -- $B/test/test_gate3.exe | tail -1
opam exec --switch=$SW -- $B/conc/domains_stress.exe "${DOMAINS:-8}" "${PER:-50000}"
opam exec --switch=$SW -- $B/conc/eio_stress.exe
opam exec --switch=$SW -- dune build --build-dir _build_ocaml5 ./ocaml/bench/bench.exe
opam exec --switch=$SW -- $B/bench/bench.exe
# Leave the OCaml 4.14 artefacts in place for the other scripts.
scripts/extract.sh ocaml/leancore/extracted >/dev/null
