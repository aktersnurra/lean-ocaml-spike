#!/usr/bin/env bash
# Create the opam switches: peregrine (Rocq stack), malfunction (OCaml 4.14 + flambda) and,
# for Gate 3, OCaml 5.3 + flambda. Verified 2026-11-02 (see README). If GitHub archive
# downloads are blocked in your environment, see scripts/seed-opam-cache.sh.
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
opam install zarith ocamlfind dune --switch "$MALFUNCTION_SWITCH" -y

# Switch 3 (Gate 3): OCaml 5.3 + malfunction (constraint override, see versions.env) + Eio.
# Install everything in ONE command with the override: a later plain `opam install` would
# remove malfunction again to satisfy its stale ocaml < 5.0 constraint.
if ! opam switch list --short | grep -qx "$OCAML5_SWITCH"; then
  opam switch create "$OCAML5_SWITCH" --packages="$OCAML5_VARIANT,$OCAML_OPTIONS" -y
fi
opam pin add -n malfunction "git+${MALFUNCTION_REPO}#${MALFUNCTION_REV}" --switch "$OCAML5_SWITCH" -y
opam install --switch "$OCAML5_SWITCH" -y --ignore-constraints-on=ocaml \
  malfunction zarith ocamlfind dune "eio_main.$EIO_VERSION"

# Lean: the frontend pins v4.22.0. With elan, `cd domain && lake build` fetches it.
echo "bootstrap done. Versions:"
opam exec --switch "$PEREGRINE_SWITCH" -- peregrine --version || true
opam exec --switch "$MALFUNCTION_SWITCH" -- ocamlfind ocamlopt -version
