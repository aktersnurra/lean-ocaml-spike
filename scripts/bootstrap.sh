#!/usr/bin/env bash
# Create the two opam switches Gate 1 needs. UNVERIFIED: not run end to end yet
# (the authoring sandbox blocks opam.ocaml.org and rocq-prover.org). Expect to fix
# dependency constraints on the first run, and record what you changed in README.md.
set -euo pipefail
cd "$(dirname "$0")/.."
# shellcheck disable=SC1091
. versions.env

# Switch 1: peregrine (Rocq + MetaRocq + the middle-end). Needs the Rocq opam repo.
if ! opam switch list --short | grep -qx "$PEREGRINE_SWITCH"; then
  opam switch create "$PEREGRINE_SWITCH" --packages="$OCAML_VARIANT,$OCAML_OPTIONS" -y
fi
opam repo add rocq-released https://rocq-prover.org/opam/released --switch "$PEREGRINE_SWITCH" -y || true
opam update --switch "$PEREGRINE_SWITCH"
opam pin add rocq-peregrine "git+${PEREGRINE_REPO}#${PEREGRINE_REV}" --switch "$PEREGRINE_SWITCH" -y

# Switch 2: malfunction + zarith (the OCaml side that compiles and links extracted code).
if ! opam switch list --short | grep -qx "$MALFUNCTION_SWITCH"; then
  opam switch create "$MALFUNCTION_SWITCH" --packages="$OCAML_VARIANT,$OCAML_OPTIONS" -y
fi
opam pin add malfunction "git+${MALFUNCTION_REPO}#${MALFUNCTION_REV}" --switch "$MALFUNCTION_SWITCH" -y
opam install zarith --switch "$MALFUNCTION_SWITCH" -y

# Lean: the frontend pins v4.22.0. With elan, `cd domain && lake build` fetches it.
echo "bootstrap done. Versions:"
opam exec --switch "$PEREGRINE_SWITCH" -- peregrine --version || true
opam exec --switch "$MALFUNCTION_SWITCH" -- ocamlfind ocamlopt -version
