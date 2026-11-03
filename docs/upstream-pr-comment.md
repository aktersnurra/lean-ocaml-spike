<!-- DRAFT comment for the lean-to-lambdabox PR (fix-primint-serialization). Review before posting. -->

Some more background, from checking that this doesn't break anything else:

**Why the quotes were there.** They were added in cf56c26 ("Add support for axioms and replacing
Nat with Zarith big integers", June 2025). At that time Peregrine itself serialized primitive ints
as string atoms (`string_of_prim_int` → `Atom (Str …)`) and parsed them with `Int64.of_string`, so
the quoting matched Peregrine's format. Peregrine moved to Ceres numeric atoms in peregrine-tool
556fe09 (2026-02-28), and the frontend didn't follow. So the quotes were only for format
compatibility; nothing else depends on them.

**Range.** Peregrine now parses with Ceres `SemiIntegral_sint` (signed 63-bit, accepts
`[min_int, max_int]`). The frontend only emits literals `n ≤ BitVec.intMax 63 = 2^62 - 1`, so every
literal it produces is in range. Checked end to end against peregrine-tool 2984751: literals `0` and
`2^62 - 1` serialize as bare atoms, compile, and compute correctly through malfunction
(including a bignum product `3 · (2^62-1)^2`).

**Other emitters.** The `BitVec` instance is only used for `PrimVal.primInt`; no float/string
primitives are emitted (string literals panic), so nothing else is affected.

**CI suggestion.** `build.yml` only builds the Lean code; nothing runs `#erase` output through
`peregrine compile`. A small job that erases one function with a `Nat` literal and runs
`peregrine compile` on it would have caught this drift (and the 7→9 field `erasure_phases`
change). Happy to help with that if useful.
