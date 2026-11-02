# Lean -> Peregrine -> OCaml extraction spike

Question: can we write a pure domain core in Lean 4, prove properties about it, extract it to
native OCaml with Peregrine, and call it from an ordinary OCaml application through a small,
trustworthy boundary, without maintaining a second implementation?

Scope here is **Gate 1 only**: one trivial pure function, extracted and called from OCaml.
Gates 2 and 3 are deliberately not scaffolded until Gate 1 passes.

## Status: Gate 1 PASS with one approved deviation (frontend patch), 2026-11-02

| Step | State |
|------|-------|
| Lean project builds on v4.22.0, proof checks, no `sorry` | **pass** |
| `#erase` emits `build/gate1.ast`, `.ast.inlinings`, `gate1.mli` | **pass** |
| opam switches (`scripts/bootstrap.sh`) | **pass** (environment-only download workaround, see below) |
| `peregrine compile` (step 3) | **pass only with `patches/l2l-primint-numeric.patch`**; fails at the pins without it (below) |
| Gate 1a: `malfunction cmx`, `ocamlfind` link, smoke test incl. 2^100 -> 2^101+1 | **pass** |
| Gate 1b: Dune executable via `leancore` library, same smoke test, negative input rejected | **pass** |
| Clean rebuild (`rm -rf domain/.lake domain/build _build third_party bin`, then both gates) | **pass** |

**Deviation from the stop rule (approved after the failure below was reported):** a one-line
patch to the Lean frontend, `patches/l2l-primint-numeric.patch`, makes it print `primInt`
literals as numeric atoms (`(primInt 2)`) instead of quoted strings (`(primInt "2")`). It
changes the on-disk format of integer literals only, not erasure. `scripts/extract.sh` applies it
idempotently to the lake checkout of the frontend after checking that the checkout is at
`L2L_REV`. Upstream issue draft: `docs/upstream-issue-primint.md`. Peregrine and Malfunction are
unpatched.

Commands that pass (with the switches from `scripts/bootstrap.sh`):

```bash
scripts/gate1.sh    # Gate 1a
scripts/gate1b.sh   # Gate 1b
```

Boundary check: if `ocaml/bin/main.ml` calls `Gate1.main` directly, the build fails with
`Error: Unbound module Gate1`. Only `Leancore` is visible to clients.

## Original Gate 1 failure (without the patch)

### Exact failure

```
$ scripts/gate1.sh
== 3. Peregrine: lambda-box -> Malfunction (.mlf) ==
peregrine compile FAILED:
Compiling:
Could not compile:
Failed parsing input program\ncould not read integral type, got a non-Num atom "2" at location 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0
```

`#erase` writes the literal `2` in `n * 2 + 1` as `(tPrim (primInt "2"))`, a quoted string
(lean-to-lambdabox `LeanToLambdaBox/Printing.lean`, `instance Serialize (BitVec n)`).
Peregrine changed its `primInt` deserializer from a string atom (`Atom_ (Str i)` -> `prim_int_of_string`)
to a Ceres numeric atom in commit `556fe09` ("Use Ceres prim serializers", 2026-02-28). The
frontend's last functional change is 2026-02-17, and **every** lean-to-lambdabox branch
(18 checked, including `main` = our pin, `fixes-port`, `ml/*`, all on Lean 4.22-4.35) still
emits the quoted form. So no frontend pin works with Peregrine at or after `556fe09`.
Any real domain code has numeric literals, so this blocks the pipeline in general, not
just this example.

Options considered when Gate 1 stopped (the frontend patch was chosen):
- **One-line patch** to the frontend (`.atom i.repr` instead of a quoted string), or to
  Peregrine (accept both). This is a patch, so the stop rule forbids it.
- Rewriting the `.ast` with sed is a workaround, so also not done.
- **Pin-only option:** move `PEREGRINE_REV` back to `6a3a043`, the parent of `556fe09`. That
  revision needs a completely different stack: Rocq 9.0 (not 9.1), MetaRocq `1.4+9.0`,
  `cmdliner < 2`, `coq-compcert 3.16`, and **8 `pin-depends` to dev commits, several on a
  personal fork** (`4ever2/certicoq`, `4ever2/CompCert`, `4ever2/rocq-verified-extraction`, ...).
  It is a version pin in form only; it rolls back eight months of Peregrine fixes and means a
  multi-hour rebuild with unknown config-format drift. Not attempted; it needs a decision.

### Diagnostic (not a Gate 1 result): everything after the literal works

A literal-free probe `def diagDouble (n : Nat) : Nat := n + n` went through the identical
pipeline (same config, axioms, switches): `peregrine compile` -> "Compiled successfully",
`malfunction cmx`, link, `diagDouble (2^100) = 2^101` correct. So the integer-literal format
is the **only** remaining blocker found at these pins. The probe was used only to find how far
the incompatibility reaches; it is not committed as a way around it.

### Scaffold changes and why

1. `Spike/Gate1.lean`: `#erase ... config {remove_irrel_constr_args := true}`. The upstream
   Makefile selects `decidable-pruned.ml` *only together with* that erasure option; the scaffold
   used the pruned axiom without it.
2. `LeanArray.ml` comes from `JCFArrayOCaml4.ml`, not `JCFArray.ml`. The latter uses `Stdlib.Dynarray`
   (OCaml >= 5.2) and fails on 4.14.2 (`Unbound module Dynarray`). Upstream's own
   `malfunction-ocaml4` backend makes the same choice. Upstream's reference config runs Malfunction on OCaml 5.
3. Peregrine config: upstream `unbox.config` has a 7-field `erasure_phases`. Peregrine at the pin
   accepts only 9 fields (`not enough fields, expected 9, got only 7`). `domain/peregrine.config`
   is the same config migrated as Peregrine's `doc/format.md` prescribes (append `None None`).
   This is an input file, not a tool patch.
4. `scripts/gate1.sh` steps 1-4 moved to `scripts/extract.sh` (shared with Gate 1b). It no longer
   sends Peregrine's output to `/dev/null`, because Peregrine prints errors on stdout; failures are now shown.
5. Gate 1b (`dune-project`, `dune`, `ocaml/leancore`, `ocaml/bin`, `scripts/gate1b.sh`).
   Approach: the README's `link_flags` idea **does not work**, because Dune puts link flags
   *after* the executable's own modules (`No implementations provided for ... Fake`). What works:
   a `leancore` library whose `library_flags` put the prebuilt `.cmx` files into
   `leancore.cmxa` *ahead of* a hand-written boundary module. A rule copies the artefacts in,
   and a generated copy of the boundary source carries the dependency. Clients can only see the
   boundary module; the raw extracted module's `.cmi` is not exported.
6. `patches/l2l-primint-numeric.patch` (approved deviation, see Status).
7. `versions.env`: **unchanged.**

### Environment notes (not pipeline changes)

- The sandbox proxy returns 403 for GitHub HTTP archive downloads
  (`github.com/<o>/<r>/archive/*.tar.gz`) but allows git. 21 Rocq-side opam packages fetch such
  archives. `scripts/seed-opam-cache.sh` rebuilds each one from its git tag with
  `git archive | gzip -cn`, **checks it against the opam checksum**, and only then puts it in
  `~/.opam/download-cache`. All 21 matched byte for byte, so no versions or checksums changed.
  It is not needed where GitHub archives are reachable.
- Building the peregrine switch (82 packages: Rocq, MetaRocq, CertiRocq, CompCert, ...) takes a long
  time on 4 cores.
- opam 2.1.5 (Ubuntu 24.04 package), run as root with `OPAMROOTISOK=1`, `--disable-sandboxing`.

### Versions actually installed

| Component | Version |
|-----------|---------|
| Lean | 4.22.0 (`ba2cbbf`), elan 4.2.4 |
| lean-to-lambdabox | `58701f8` (= `main` HEAD) |
| peregrine-tool | `2984751` (= `master` HEAD, 2026-11-02) |
| rocq-core / rocq-stdlib | 9.1.1 / 9.0.0 |
| MetaRocq erasure, CertiRocq, verified-extraction | 1.5.1+9.1, 0.9.1+9.1, 1.0.0+9.1 |
| OCaml (both switches) | 4.14.2+options with flambda |
| malfunction | 0.7.1 (`1682ecd`) |
| zarith, ocamlfind, dune | 1.14, 1.9.8, 3.24.2 |

## Run it

```bash
scripts/bootstrap.sh                                   # opam switches
scripts/seed-opam-cache.sh spike-peregrine <pkgs...>   # only if GitHub archives are blocked
scripts/gate1.sh                                       # Gate 1a (applies the frontend patch)
scripts/gate1b.sh                                      # Gate 1b: Dune executable
```

Needs `elan`, `opam`, `git`, `gcc`, `libgmp-dev`. Pins live in `versions.env`.

**Stop rule:** if Gate 1 needs patches to Peregrine, the Lean frontend, or Malfunction beyond
version pins, stop and record exactly what broke. Do not start Gate 2. (Hit once; resolved by
the approved frontend patch above.)

## Early reads for later gates (not started, recorded so they are not lost)

- **Gate 2 (Lean side only, nothing linked):** `List Nat -> List Nat` erases with only Nat axioms,
  and the generated mli is `val main: Z.t list -> Z.t list`. The mli generator only knows `Nat`,
  `Unit`, `Bool` and `List`; anything else becomes `unit` with a warning. `UInt8`, `ByteArray` and
  `String` erase to new `@[extern]` axioms (`UInt8.ofNat/toNat`, `ByteArray.size/get!`,
  `String.data`, `Char.ofNatAux`, ...) that no shipped runtime file provides. String literals
  make the frontend panic (`"String literals not supported."`).
- **Gate 3, OCaml 5:** malfunction's opam file says `ocaml < 5.0.0`, but its history has
  "OCaml 5.2 support" and "OCaml 5.3 support", and upstream benchmarks run it on OCaml 5. The
  domain-concurrency test would need an OCaml 5 Malfunction switch, so this should be checked early.

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
versions.env               pinned revisions and switch names (unchanged)
domain/                    Lean 4 project (v4.22.0) with the frontend as a git dependency
  Spike/Gate1.lean         gate1 n = 2n + 1, proof it is odd, #erase to build/
  peregrine.config         Peregrine config (upstream unbox.config, 9-field form)
scripts/bootstrap.sh       opam switches
patches/                   l2l-primint-numeric.patch (approved deviation)
docs/                      upstream issue draft
scripts/seed-opam-cache.sh environment workaround for blocked GitHub archives (checksum-verified)
scripts/extract.sh         pipeline steps 1-4 (Lean -> .ast -> .mlf -> .cmx), optional copy-out dir
scripts/gate1.sh           Gate 1a: extract + ocamlfind link + smoke test
scripts/gate1b.sh          Gate 1b: extract + Dune build + smoke test
app/main.ml                Gate 1a harness calling Gate1.main
dune-project, dune         Dune project root (OCaml side only)
ocaml/leancore/            Dune library: imported extracted objects + boundary module Leancore
ocaml/bin/                 Gate 1b Dune executable using Leancore
```
