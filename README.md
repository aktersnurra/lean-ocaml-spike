# Lean -> Peregrine -> OCaml extraction spike

Question: can we write a pure domain core in Lean 4, prove properties about it, extract it to
native OCaml with Peregrine, and call it from an ordinary OCaml application through a small,
trustworthy boundary, without maintaining a second implementation?

Scope here is **Gate 1 only**: one trivial pure function, extracted and called from OCaml.
Gates 2 and 3 are deliberately not scaffolded until Gate 1 passes.

## Status (2026-11-02): Gates 1, 2, 3 PASS, with one approved deviation (frontend patch)

See "Gate 3" for results and "Verdict" for the recommendation. CI sequence (after `scripts/bootstrap.sh`):

```bash
scripts/gate1.sh && scripts/gate1b.sh            # Gate 1: extraction, ocamlfind link, Dune link
scripts/gate2.sh && experiments/gate2b/run.sh    # Gate 2: byte boundary (a), probe (b)
scripts/gate3.sh                                 # Gate 3: tests, differential fuzz, audit, benchmark
scripts/gate3-ocaml5.sh                          # Gate 3: OCaml 5 domains + Eio, benchmark
```

### Gate 1 details

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

## Gate 3: correctness and robustness, PASS

All commands pass from a clean tree (`rm -rf domain/.lake domain/build _build _build_ocaml5
third_party bin ocaml/leancore/extracted`, then the CI sequence below), 2026-11-02.

| Criterion | Result | Where |
|-----------|--------|-------|
| Representative pure domain function | `Spike.Order.priceOrder`: validation with 4 domain errors, nested data (order → lines), unbounded arithmetic | `domain/Spike/Order.lean` |
| `decode (encode x) = x` proved | Order (request) and Quote (response); generic varint and list lemmas | `exact_decodeOrder_encodeOrder`, `exact_decodeQuote_encodeQuote` |
| Extra proofs | `priceOrder_ok` (total + discount = subtotal, discount ≤ subtotal, ...), `allBytes_handle` (every response is bytes, so the OCaml byte check can only fire if the trusted base is broken), `handle_priceOrder` (handle on an encoded order = encoded `priceOrder` result) | `Order.lean`, `Gate2.lean` |
| Malformed input terminates with an encoded error | 200,000 fuzz inputs (mutated valid orders + random bytes): all well formed, 0 exceptions. Adversarial: count 2^60 on short input, 1 MB unterminated varint, 1,000,000-line orders all return encoded results in ≤ 1.7 s | `ocaml/test/test_gate3.ml` |
| Differential test vs native | byte-for-byte identical responses on all 200,000 fuzz inputs and 20,000 random valid orders | same |
| Round trip for every boundary constructor | both ops, ok response, every error code (1,3,4,5,16-19; 2 is kernel-checked in Lean since real bytes cannot trigger it), validation precedence, bignums | same + `example`s in `Gate2.lean` |
| OCaml 5 domain concurrency | 8 domains × 50,000 calls, each checked against native: 0 wrong, 0 exceptions | `ocaml/conc/domains_stress.ml`, `scripts/gate3-ocaml5.sh` |
| Eio fibers (separate test) | 1,000 fibers on one domain + 4 domains × 100 fibers via `Domain_manager`, 200,000 calls: 0 wrong | `ocaml/conc/eio_stress.ml` |
| Benchmark vs native (target ≤ 10x) | **1.0x–3.5x** on OCaml 4.14, **1.0x–3.8x** on OCaml 5.3 (table below) | `ocaml/bench/bench.ml` |
| Clean-build reproducibility in CI | **Passed on GitHub Actions** (ubuntu-24.04, 4 vCPU), cold: [run 41528451917](https://github.com/aktersnurra/lean-ocaml-spike/actions/runs/41528451917), 1h31m total, of which bootstrap 88 min and all gates under 2 min | `.github/workflows/ci.yml` |
| Runtime axioms minimal, documented, tested | 8 Nat axioms (below); `scripts/audit.sh` fails if the set changes; every test above exercises them | `scripts/runtime-axioms.txt` |
| Proof axioms audited | every theorem: `[propext, Quot.sound]`; `Spike.gate1`: none; `Spike.Wire.handle`: `[propext, Quot.sound]` (from `Lean.RBMap`'s well-formedness proof field, erased) | `domain/Spike/Audit.lean`, `scripts/audit.sh` |

### Benchmark (ns per call, best of 5, both sides flambda `-O3`, same machine)

| case | Lean (OCaml 4.14) | native | ratio | Lean (OCaml 5.3) | native | ratio |
|------|------:|------:|-----:|------:|------:|-----:|
| gate1 n=123456 | 110 | 34 | 3.2 | 119 | 46 | 2.6 |
| order, 1 line | 279 | 110 | 2.5 | 299 | 134 | 2.2 |
| order, 10 lines | 1,391 | 510 | 2.7 | 1,567 | 552 | 2.8 |
| order, 100 lines | 18,627 | 5,751 | 3.2 | 19,739 | 6,093 | 3.2 |
| order, 1,000 lines | 345,134 | 99,194 | 3.5 | 359,584 | 95,251 | 3.8 |
| order, 10,000 lines | 5,606,570 | 1,897,349 | 3.0 | 5,794,370 | 1,693,380 | 3.4 |
| malformed (truncated) | 65 | 63 | 1.0 | 71 | 71 | 1.0 |

The Lean column includes the boundary's `bytes <-> Z.t list` conversion. The native baseline
uses Zarith (needed for byte-identical semantics) and a `Hashtbl` duplicate check; a version
with native `int` would be faster still. **Build flags matter:** without flambda `-O3` the
extracted core was 7.6x–13x native (which fails the target). Peregrine's optional
`specialize_instances`/`cse` passes made no measurable difference on top of `-O3`.

### Problems Gate 3 found, and fixes (all in Lean or the build, no tool patches)

1. **Stack overflow on long input.** Non-tail-recursive Lean decoders became non-tail-recursive
   OCaml: a 1 MB varint raised `Stack_overflow` *out of* `Leancore.call` instead of returning an
   encoded error. Fix in Lean: a tail-recursive `terminated` scan rejects unterminated varints
   in linear time with no bignum, then tail-recursive accumulators decode varints and lists
   (`decodeNatAux`, `decodeElemsAux`); `subtotal` and the other traversals are tail recursive
   too. Proofs redone. **Lesson: the stack shape of the Lean definition is the stack shape of
   the extracted code; attacker-sized recursion must be written tail recursive.**
2. **Quadratic duplicate check.** 100,000 lines took 87 s with the list-based check. Rewritten
   with `Lean.RBMap` (core library red-black tree): 0.14 s. It extracts with **no new runtime
   axioms**, so library data structures written with structural recursion are usable.
   `Std.HashMap` was not tried (hashing goes through `UInt64` externs).
3. **Stale link in the Gate 1b Dune design.** `library_flags` registers no dependencies, so
   after re-extraction Dune's early cutoff kept the old `leancore.cmxa`, and the tests ran the
   *previous* core (op 2 answered `unknownOp`). The raw extracted module was correct. Fix: the
   generated boundary source embeds a digest of the imported objects. Any production
   integration must make re-extraction invalidate the link, and should test that it does.
4. **Toolchain:** OCaml 5 needs malfunction installed with `--ignore-constraints-on=ocaml` (stale
   `ocaml < 5.0` constraint, source supports 5.3), the `JCFArray.ml` array axiom (Dynarray), and
   all packages in one `opam install` (a later install silently removed malfunction).

### Runtime axiom surface (trusted, unverified)

The extracted core references exactly these OCaml functions (`scripts/runtime-axioms.txt`,
enforced by `scripts/audit.sh`), all from upstream `nat-inline.ml` at `L2L_REV`, with Lean
`Nat` = Zarith `Z.t`:

| Axiom | OCaml implementation | Exercised by |
|-------|----------------------|--------------|
| `Nat.add`, `Nat.sub`, `Nat.mul` | `Z.add`; `if n <= m then 0 else Z.sub n m` (saturating, as Lean); `Z.mul` | varint decode, subtotal, discount |
| `Nat.div`, `Nat.mod` | `if m = 0 then 0 else Z.ediv n m`; `if m = 0 then n else Z.erem n m` (Lean's division-by-zero semantics) | varint encode (`/128`, `%128`), discount `/100` |
| `Nat.beq`, `Nat.decEq`, `Nat.decLt` | `Z.equal`, `Z.lt` → `Decidable` via `dec_of_bool` | op dispatch, byte/terminator checks, RBMap compare |

Also linked but not referenced: `Int`, `Eq`, `LeanArray` (Filliâtre's persistent arrays, which
**mutate internally**; not safe to share across domains, unused by this core).

### Trust assumptions after Gate 3

- **Trusted, unproven:** the lean-to-lambdabox erasure (plus our one-line printer patch),
  Peregrine (its middle-end is verified in Rocq, but end-to-end verification of the pipeline
  is not claimed by its authors), Malfunction and the OCaml compiler with flambda `-O3`, the 8
  runtime axioms and Zarith, and the ~20-line `Leancore` boundary.
- **Asserted, unchecked:** the generated `.mli` (`Z.t list -> Z.t list`). The boundary checks
  the transport invariant on every response; `allBytes_handle` proves the check never fires
  unless the trusted base is wrong.
- **Proved in Lean:** codec round trips, domain invariants, response is bytes, and the
  end-to-end spec of `handle` for well-formed orders. Erased before extraction.
- **Resource limits are not in the proofs.** Big inputs terminate, but costs are polynomial in
  input size (bignum arithmetic on long varints is quadratic, also natively). Put a request size
  cap in the transport layer.

## Verdict

**Is Peregrine viable for a greenfield Lean-first domain core? Yes, with conditions.**
The core idea works: one Lean implementation, proved, extracted to native OCaml, called
through a small opaque `bytes -> bytes` boundary, 1–4x native speed, correct under fuzzing,
domain parallelism and Eio. No duplicate implementation is needed (the native one here is
only a test oracle and benchmark baseline). Conditions:
1. **Pin the frontend and Peregrine as a pair, and own a fork or patch queue.** They drifted
   on two serialization formats (integer literals, config fields) at their own HEADs, and no
   frontend branch matched current Peregrine. Upstream's answer to the issue matters
   (`docs/upstream-issue-primint.md`).
2. **Write the core in a disciplined fragment:** total, structural, tail recursive over
   input-sized data, `Nat`/`List`/inductives/`Lean.RBMap`; no `String` literals, no
   `ByteArray`/`UInt*`/`Float` (each needs new trusted axioms), no well-founded recursion
   (untested here). Keep the wire format in Lean.
3. **Build discipline:** flambda `-O3`, re-extraction must invalidate the link, and a large
   toolchain (the Rocq stack takes hours cold; cache it in CI).

**Should we proceed to a Lean-derived interface generator? Not yet; first two small steps.**
- The hand-written parts of the boundary are already tiny (`Leancore.call` plus a client-side
  decoder). The generator's value is the *client side*: OCaml types and decoders for responses
  (and encoders for requests) generated from the Lean types, so the wire format has one source.
  That is worth building once the toolchain pair is stable.
- Before that: (1) get the upstream answer on the frontend/Peregrine pairing and, if needed,
  set up the pinned fork; (2) run the CI workflow on GitHub once to confirm cold-build time and
  caching (done: cold run passes in 1h31m, see Gate 3 table). Then start the generator, with codec proofs (`decode (encode x) = x`) as part of its
  output, as done by hand here.

## Gate 2: opaque byte boundary, PASS (option (a)); option (b) also works but is not recommended

Both options survive extraction **without tool patches**. They rely only on the Gate 1 frontend patch (integer literals).

### (a) `List Nat` transport: chosen
- `domain/Spike/Gate2.lean`: `Spike.Wire.handle : List Nat → List Nat` holds the whole wire
  protocol (LEB128 varints, op dispatch, error tagging), all total and structurally recursive.
  Response `00 payload` | `01 code` (1 empty, 2 notBytes, 3 unknownOp, 4 truncated, 5 trailing).
- Generated mli `val main: Z.t list -> Z.t list`. **Axioms used: only the shipped Nat ones**
  (`add sub mul div mod beq decEq decLt`).
- OCaml `Leancore.call : bytes -> bytes` (`ocaml/leancore/leancore.ml.in`, about 20 lines):
  converts bytes to a `Z.t list`, calls the core, and checks each response element is 0..255
  (otherwise `Contract_violation`, meaning the trusted base is broken, not bad input). It never
  looks at domain values or decides on errors. Clients see only `Leancore`.
- Tests (`scripts/gate2.sh`, `ocaml/test/test_gate2.ml`): 11 fixed cases (every error tag,
  1/2-byte varint edges, 2^100, non-canonical varint) plus 100,000 random inputs through the
  boundary, all with well-formed responses and no exceptions. Seven more cases are kernel-checked
  `example`s in `Gate2.lean`, including `notBytes`, which real bytes cannot trigger.

### (b) Opaque `ByteArray` with hand-written OCaml axioms: works, not recommended
`experiments/gate2b/run.sh` erases `ByteArray -> ByteArray`, compiles, links and runs correctly.
Costs:
- **5 new hand-written trusted axioms** for even a tiny function (`UInt8.ofNat`,
  `ByteArray.emptyWithCapacity/size/get!/push`), and more for each extra operation used
  (`experiments/gate2b/bytearray.ml`).
- **The mli generator does not support it**: it emits `val main: unit -> unit` with a warning,
  so the mli must be hand-written, which adds one more unchecked assertion.
- The shipped `axioms.ml` aggregate has to be extended.
- Lean's in-place `push` becomes an O(n) copy (persistent semantics), unless the axioms add
  unchecked uniqueness assumptions.

String literals still make the frontend panic, and `String`/`Char` need further axioms, so text
fields would have to be bytes on the wire.

## Gate 1 (details)

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
7. `versions.env`: unchanged for Gates 1-2; Gate 3 added the OCaml 5 switch (`OCAML5_*`, `EIO_VERSION`).

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

- **Gate 2 (superseded by the Gate 2 section above):** `List Nat -> List Nat` erases with only Nat axioms,
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
scripts/gate2.sh           Gate 2: extract + Dune build + boundary tests and fuzz
scripts/gate3.sh           Gate 3: tests, differential fuzz, audit, benchmark (OCaml 4.14)
scripts/gate3-ocaml5.sh    Gate 3: OCaml 5 build, domain + Eio stress, benchmark
scripts/audit.sh           proof-axiom, forbidden-construct and runtime-axiom audit
scripts/runtime-axioms.txt the allowed runtime (OCaml) axiom set
domain/Spike/Wire.lean     varint/list codecs + round-trip lemmas
domain/Spike/Order.lean    domain: priceOrder, invariants, Order/Quote codecs + round trips
domain/Spike/Gate2.lean    handle (extracted as Gate2), end-to-end theorems
domain/Spike/Audit.lean    #print axioms list
ocaml/native/              native OCaml implementation (test oracle + benchmark baseline only)
ocaml/bench/               benchmark
ocaml/conc/                OCaml 5 domain and Eio stress tests
.github/workflows/ci.yml   clean-build CI (passes on GitHub Actions)
ocaml/test/                Gate 2 boundary tests
experiments/gate2b/        option (b) probe: ByteArray + hand-written axioms
app/main.ml                Gate 1a harness calling Gate1.main
dune-project, dune         Dune project root (OCaml side only)
ocaml/leancore/            Dune library: imported extracted objects + boundary module Leancore
ocaml/bin/                 Gate 1b Dune executable using Leancore
```
