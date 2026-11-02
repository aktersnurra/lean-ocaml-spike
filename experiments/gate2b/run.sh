#!/usr/bin/env bash
# Reproduce the Gate 2 option (b) probe. Run scripts/extract.sh first (it builds the axioms).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"; cd "$ROOT"
# shellcheck disable=SC1091
. versions.env
export PATH="$HOME/.elan/bin:$PATH"
B="$ROOT/domain/build/probe_b"; mkdir -p "$B"
O="opam exec --switch=$MALFUNCTION_SWITCH -- ocamlfind ocamlopt -package zarith"
( cd domain && lake env lean "$ROOT/experiments/gate2b/ProbeB.lean" )
grep -q "unit -> unit" "$B/probeB.mli" && echo "note: generated mli is '$(cat "$B/probeB.mli")'; replacing with hand-written 'val main: bytes -> bytes'"
echo 'val main: bytes -> bytes' > "$B/probeB.mli"
cp domain/build/peregrine.config experiments/gate2b/bytearray.ml experiments/gate2b/bytearray.mli "$B/"
for m in decidable eq LeanArray nat int; do cp "domain/build/$m.ml" "domain/build/$m.mli" "$B/"; done
printf 'include Int\ninclude Nat\ninclude Eq\ninclude LeanArray\ninclude Bytearray\n' > "$B/axioms.ml"
printf 'include (module type of Nat)\ninclude (module type of Int)\ninclude (module type of Eq)\ninclude (module type of LeanArray)\ninclude (module type of Bytearray)\n' > "$B/axioms.mli"
cd "$B"
opam exec --switch="$PEREGRINE_SWITCH" -- peregrine compile probeB.ast peregrine.config --attributes=probeB.ast.inlinings | grep -q "Compiled successfully"
for m in decidable eq LeanArray nat int bytearray axioms; do $O -I . -c "$m.mli" "$m.ml"; done
$O -c probeB.mli && opam exec --switch="$MALFUNCTION_SWITCH" -- malfunction cmx probeB.mlf
echo 'let () = print_string (Bytes.to_string (ProbeB.main (Bytes.of_string Sys.argv.(1))))' > m.ml
$O -I . -linkpkg decidable.cmx eq.cmx LeanArray.cmx nat.cmx int.cmx bytearray.cmx axioms.cmx probeB.cmx m.ml -o probeB.exe
[ "$(./probeB.exe abc | od -An -tx1 | tr -d ' \n')" = "63626103" ] && [ "$(./probeB.exe '' | od -An -tx1 | tr -d ' \n')" = "00" ] && echo "== Gate 2 (b) probe PASSED =="
