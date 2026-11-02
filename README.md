# Lean -> Peregrine -> OCaml extraction spike

Question: can we write a pure domain core in Lean 4, prove properties about it, extract it to
native OCaml with Peregrine, and call it from an ordinary OCaml application through a small,
trustworthy boundary, without maintaining a second implementation?

Scope here is **Gate 1 only**: one trivial pure function, extracted and called from OCaml.
Gates 2 and 3 are deliberately not scaffolded until Gate 1 passes.

## Status

| Step | State |
|------|-------|
| Lean project builds on the pinned toolchain, proof checks, no `sorry` | verified (authoring sandbox) |
| `#erase` emits `build/gate1.ast` and `build/gate1.mli` | verified (authoring sandbox) |
| opam switches (peregrine, malfunction), `scripts/bootstrap.sh` | **not run** |
| `peregrine compile` -> `.mlf` -> `malfunction cmx` -> link -> run | **not run** (`scripts/gate1.sh` steps 3-5) |
| Dune executable linking the extracted object | **not started** (Gate 1b, see below) |

The authoring sandbox could not reach `opam.ocaml.org` or `rocq-prover.org`, so nothing past the
Lean step has been executed. Treat steps 3-5 of `gate1.sh` as a transcription of the upstream
Makefile, not as a tested script.

## Run it

```bash
scripts/bootstrap.sh   # opam switches; first run will likely need constraint fixes
scripts/gate1.sh       # Lean check + extraction + link + smoke test
```

Needs `elan` (or Lean v4.22.0 on PATH), `opam`, `git`, `gcc`, `libgmp-dev`.
Pins live in `versions.env`.

**Stop rule:** if Gate 1 needs patches to Peregrine, the Lean frontend, or Malfunction beyond
version pins, stop and record exactly what broke. Do not start Gate 2.

## Gate 1b: Dune

`gate1.sh` links with `ocamlfind ocamlopt`, as the upstream benchmarks do. The Gate 1 criterion
also asks for a Dune executable. Suggested approach once 1a passes: a `rule` that runs steps 1-4
and produces `gate1.cmx`, `gate1.o`, `gate1.cmi` plus the axiom objects in one directory, then an
`executable` that adds that directory with `-I` and the `.cmx` files via `link_flags`. Whether
Dune accepts prebuilt `.cmx` files this way is untested; if it does not, an `(extra_objects)`
stanza or an opam-installed library built from the generated sources are the fallbacks.

## What reading the sources already told us (not yet tested)

1. **Two Lean versions.** The frontend (`lean-to-lambdabox`) pins Lean **v4.22.0**; the
   `peregrine-tool` repo pins v4.34.1 but that is for its *Lean backend*. The domain project must
   build on v4.22.0, so proofs are limited to what that version supports, and any upgrade is
   gated on the frontend following.
2. **The `.mli` is generated from the Lean type and is asserted, not checked.** `#erase` wrote
   `val main: Z.t -> Z.t` for `Nat -> Nat` (Nat maps to zarith's `Z.t`). The upstream Makefile
   warns that Malfunction silently produces an empty `.cmi` without an `.mli`, so the compiler
   does not verify the extracted code against this signature. This is the typed-boundary gap
   we discussed, now confirmed.
3. **The runtime axiom surface is small but real.** `#erase` reported `Nat.add` and `Nat.mul`
   as `@[extern]` and emitted them as axioms. The OCaml side supplies them in five modules
   (`decidable`, `eq`, `nat`, `int`, `LeanArray`, combined in `axioms`), taken from the upstream
   benchmarks directory at the pinned revision. These files are the audit surface.
4. **Entry point is always `main`**, one definition per `.ast`, in a module named after the file.
5. **Likely Gate 2 problem.** The frontend documents "Primitives" as unsupported, and the
   shipped runtime axioms cover only Nat, Int, equality, decidability and Array. There is no
   String or ByteArray support. A `bytes -> bytes` boundary therefore probably needs either a
   representation built from `Array Nat`/`List Nat`, or new OCaml axioms for an opaque byte type.
   Gate 2 should answer which, and it is the main risk to the serialized-boundary plan.

## Proof axioms (Gate 3 "audit" criterion, early read)

`#print axioms Spike.gate1_odd` reports `[propext, Quot.sound]` (via `omega`); `Spike.gate1`
itself depends on none. No `sorry`, no `Classical.choice`.

## Layout

```
versions.env            pinned revisions and switch names
domain/                 Lean 4 project (toolchain v4.22.0) with the frontend as a git dependency
  Spike/Gate1.lean      gate1 n = 2n + 1, proof it is odd, #erase to build/
scripts/bootstrap.sh    opam switches (unverified)
scripts/gate1.sh        full Gate 1 pipeline and smoke test (steps 3-5 unverified)
app/main.ml             OCaml harness calling Gate1.main
```
