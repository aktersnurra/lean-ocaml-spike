#!/usr/bin/env bash
# Gate 1: trivial pure Lean function -> lambda-box -> Malfunction -> native -> called from OCaml.
#
#   Lean steps    : verified in the authoring sandbox (proof checks, .ast and .mli produced).
#   Peregrine and
#   OCaml steps   : NOT yet run. They follow lean-to-lambdabox's benchmarks/via_malfunction
#                   Makefile at the pinned revision, with the default settings
#                   (INLINE_AXIOMS=1, PRUNE_CONSTRUCTORS=1, UNBOX=1, FLAMBDA=1, JCFArray).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
# shellcheck disable=SC1091
. versions.env

BUILD="$ROOT/domain/build"
TP="$ROOT/third_party/l2l"
PEREGRINE="opam exec --switch=$PEREGRINE_SWITCH -- peregrine"
MALFUNCTION="opam exec --switch=$MALFUNCTION_SWITCH -- malfunction"
OCAMLOPT="opam exec --switch=$MALFUNCTION_SWITCH -- ocamlfind ocamlopt -package zarith"

echo "== 1. Lean: check proofs, erase to lambda-box =="
mkdir -p "$BUILD"
( cd domain && lake build && lake lean Spike/Gate1.lean )
test -s "$BUILD/gate1.ast" && test -s "$BUILD/gate1.mli"

echo "== 2. Fetch runtime primitives at the pinned lean-to-lambdabox revision =="
if [ ! -d "$TP/.git" ]; then
  mkdir -p third_party
  git clone -q "$L2L_REPO" "$TP"
fi
git -C "$TP" checkout -q "$L2L_REV"
VM="$TP/benchmarks/via_malfunction"
# Same file selection as the upstream Makefile for the default settings.
cp "$VM/decidable.mli" "$BUILD/decidable.mli"; cp "$VM/decidable-pruned.ml" "$BUILD/decidable.ml"
cp "$VM/eq.mli"        "$BUILD/eq.mli";        cp "$VM/eq-inline.ml"        "$BUILD/eq.ml"
cp "$VM/nat.mli"       "$BUILD/nat.mli";       cp "$VM/nat-inline.ml"       "$BUILD/nat.ml"
cp "$VM/int.mli"       "$BUILD/int.mli";       cp "$VM/int-inline.ml"       "$BUILD/int.ml"
cp "$VM/LeanArray.mli" "$BUILD/LeanArray.mli"; cp "$VM/JCFArray.ml"         "$BUILD/LeanArray.ml"
cp "$VM/axioms.mli"    "$BUILD/axioms.mli";    cp "$VM/axioms.ml"           "$BUILD/axioms.ml"
cp "$VM/unbox.config"  "$BUILD/unbox.config"

echo "== 3. Peregrine: lambda-box -> Malfunction (.mlf) =="
$PEREGRINE compile "$BUILD/gate1.ast" "$BUILD/unbox.config" --attributes="$BUILD/gate1.ast.inlinings" > /dev/null
test -s "$BUILD/gate1.mlf"

echo "== 4. OCaml: compile axioms, compile extracted module, link =="
(
  cd "$BUILD"
  $OCAMLOPT -I . -c decidable.mli decidable.ml
  $OCAMLOPT -I . -c eq.mli eq.ml
  $OCAMLOPT -I . -c LeanArray.mli LeanArray.ml
  $OCAMLOPT -I . -c nat.mli nat.ml
  $OCAMLOPT -I . -c int.mli int.ml
  $OCAMLOPT -I . -c axioms.mli axioms.ml
  # Malfunction silently emits an empty .cmi without an .mli, so compile it first.
  $OCAMLOPT -c gate1.mli
  $MALFUNCTION cmx gate1.mlf
)
mkdir -p "$ROOT/bin"
cp "$ROOT/app/main.ml" "$BUILD/gate1_main.ml"
(
  cd "$BUILD"
  $OCAMLOPT -I . -linkpkg decidable.cmx eq.cmx nat.cmx int.cmx LeanArray.cmx axioms.cmx \
    gate1.cmx gate1_main.ml -o "$ROOT/bin/gate1"
)

echo "== 5. Smoke test (gate1 n = 2n + 1, including a bignum) =="
check() { got="$("$ROOT/bin/gate1" "$1")"; [ "$got" = "$2" ] || { echo "FAIL: gate1 $1 = $got, want $2"; exit 1; }; echo "ok: gate1 $1 = $got"; }
check 0 1
check 5 11
check 1267650600228229401496703205376 2535301200456458802993406410753   # 2^100 -> 2^101 + 1

echo "== Gate 1 PASSED =="
