#!/usr/bin/env bash
# Steps 1-4 of the pipeline: Lean check + #erase -> Peregrine -> Malfunction/ocamlopt.
# Leaves the extracted module and runtime axioms compiled in domain/build/, and, if an
# output directory is given, copies the linkable artefacts (.cmx .o .cmi) there.
#
#   scripts/extract.sh [OUTDIR]
#
# Module list (link order): decidable eq LeanArray nat int axioms gate1.
# Settings follow lean-to-lambdabox's benchmarks/via_malfunction Makefile defaults
# (INLINE_AXIOMS=1, PRUNE_CONSTRUCTORS=1, UNBOX=1, FLAMBDA=1) with ARRAYML=JCFArrayOCaml4.ml:
# the default JCFArray.ml uses Stdlib.Dynarray (OCaml >= 5.2); upstream's own
# "malfunction-ocaml4" backend selects JCFArrayOCaml4.ml for OCaml 4.14, which we pin.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
OUT="${1:-}"
[ -n "$OUT" ] && OUT="$(mkdir -p "$OUT" && cd "$OUT" && pwd)"
cd "$ROOT"
# shellcheck disable=SC1091
. versions.env
export PATH="$HOME/.elan/bin:$PATH"

BUILD="$ROOT/domain/build"
TP="$ROOT/third_party/l2l"
PEREGRINE="opam exec --switch=$PEREGRINE_SWITCH -- peregrine"
MALFUNCTION="opam exec --switch=$MALFUNCTION_SWITCH -- malfunction"
OCAMLOPT="opam exec --switch=$MALFUNCTION_SWITCH -- ocamlfind ocamlopt -package zarith"
MODULES="decidable eq LeanArray nat int axioms gate1"

echo "== 1. Lean: check proofs, erase to lambda-box =="
mkdir -p "$BUILD"
# lake build checks the proofs and, because Gate1.lean contains #erase, writes the .ast/.mli.
# `lake lean` (as in the upstream Makefile) re-elaborates unconditionally so the outputs exist even if lake had nothing to do.
# DEVIATION FROM THE STOP RULE (approved): patches/l2l-primint-numeric.patch makes the frontend
# print primInt literals as numeric atoms, the format Peregrine requires since 556fe09. It changes
# the serialization of integer literals only. `lake env true` materializes the dependency
# checkout without building it; the patch is applied once (idempotent) before anything compiles.
( cd domain && lake env true )
L2L_PKG="$ROOT/domain/.lake/packages/lean_to_lambdabox"
if git -C "$L2L_PKG" apply --check "$ROOT/patches/l2l-primint-numeric.patch" 2>/dev/null; then
  git -C "$L2L_PKG" apply "$ROOT/patches/l2l-primint-numeric.patch"; echo "applied l2l-primint-numeric.patch"
elif git -C "$L2L_PKG" apply --reverse --check "$ROOT/patches/l2l-primint-numeric.patch" 2>/dev/null; then
  echo "l2l-primint-numeric.patch already applied"
else
  echo "l2l-primint-numeric.patch does not apply to $L2L_PKG"; exit 1
fi
[ "$(git -C "$L2L_PKG" rev-parse HEAD)" = "$L2L_REV" ] || { echo "frontend checkout is not at L2L_REV"; exit 1; }
( cd domain && lake build && lake lean Spike/Gate1.lean )
test -s "$BUILD/gate1.ast" && test -s "$BUILD/gate1.mli"

echo "== 2. Fetch runtime axioms at the pinned lean-to-lambdabox revision =="
if [ ! -d "$TP/.git" ]; then
  mkdir -p third_party
  git clone -q "$L2L_REPO" "$TP"
fi
git -C "$TP" checkout -q "$L2L_REV"
VM="$TP/benchmarks/via_malfunction"
cp "$VM/decidable.mli" "$BUILD/decidable.mli"; cp "$VM/decidable-pruned.ml" "$BUILD/decidable.ml"
cp "$VM/eq.mli"        "$BUILD/eq.mli";        cp "$VM/eq-inline.ml"        "$BUILD/eq.ml"
cp "$VM/nat.mli"       "$BUILD/nat.mli";       cp "$VM/nat-inline.ml"       "$BUILD/nat.ml"
cp "$VM/int.mli"       "$BUILD/int.mli";       cp "$VM/int-inline.ml"       "$BUILD/int.ml"
cp "$VM/LeanArray.mli" "$BUILD/LeanArray.mli"; cp "$VM/JCFArrayOCaml4.ml"   "$BUILD/LeanArray.ml"
cp "$VM/axioms.mli"    "$BUILD/axioms.mli";    cp "$VM/axioms.ml"           "$BUILD/axioms.ml"
# Peregrine config: upstream's unbox.config (7-field erasure_phases) migrated to the 9-field
# form Peregrine requires at PEREGRINE_REV, as documented in its doc/format.md ("append None None").
cp "$ROOT/domain/peregrine.config" "$BUILD/peregrine.config"

echo "== 3. Peregrine: lambda-box -> Malfunction (.mlf) =="
# Peregrine reports failures on stdout and may still exit 0, so keep the log and check the output.
( cd "$BUILD" && $PEREGRINE compile gate1.ast peregrine.config --attributes=gate1.ast.inlinings > peregrine.log 2>&1 ) || true
if ! grep -q "Compiled successfully" "$BUILD/peregrine.log" || [ ! -s "$BUILD/gate1.mlf" ]; then
  echo "peregrine compile FAILED:"; cat "$BUILD/peregrine.log"; exit 1
fi

echo "== 4. OCaml: compile axioms and the extracted module =="
(
  cd "$BUILD"
  for m in decidable eq LeanArray nat int axioms; do
    $OCAMLOPT -I . -c "$m.mli" "$m.ml"
  done
  # Malfunction silently emits an empty .cmi without an .mli, so compile it first.
  $OCAMLOPT -c gate1.mli
  $MALFUNCTION cmx gate1.mlf
)

if [ -n "$OUT" ]; then
  for m in $MODULES; do cp "$BUILD/$m.cmx" "$BUILD/$m.o" "$BUILD/$m.cmi" "$OUT/"; done
  echo "artefacts copied to $OUT"
fi
