<!-- DRAFT, not filed. Target: peregrine-project/lean-to-lambdabox (cc peregrine-tool).
     Review before posting. -->

# `#erase` output is rejected by current Peregrine: `primInt` literals are quoted strings

## Summary

Every lambda-box program that contains a `Nat` literal fails to parse in current
`peregrine-tool`. lean-to-lambdabox prints primitive integers as string atoms,
`(primInt "2")`. Since peregrine-tool `556fe09` ("Use Ceres prim serializers", 2026-02-28),
Peregrine only accepts numeric atoms, `(primInt 2)`.

## Versions

- lean-to-lambdabox `58701f8` (`main`), Lean v4.22.0
- peregrine-tool `2984751` (`master`, 2026-11-02), Rocq 9.1.1, MetaRocq 1.5.1+9.1
- OCaml 4.14.2+flambda, malfunction 0.7.1

## Reproduce

```lean
import LeanToLambdaBox
def gate1 (n : Nat) : Nat := n * 2 + 1
#erase gate1 config {remove_irrel_constr_args := true} to "gate1.ast" mli "gate1.mli"
```

```
$ peregrine compile gate1.ast peregrine.config --attributes=gate1.ast.inlinings
Compiling:
Could not compile:
Failed parsing input program\ncould not read integral type, got a non-Num atom "2" at location 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0
```

(Peregrine prints this on stdout, so the benchmark Makefile's `> /dev/null` hides it.)

## Cause

- lean-to-lambdabox `LeanToLambdaBox/Printing.lean`:
  `instance: Serialize (BitVec n) where to_sexpr b := let i := b.toFin.toNat; .atom ("\"" ++ i.repr ++ "\"")`
- peregrine-tool before `556fe09`: `Deserialize_prim_int` matched `Atom_ (Str i)` and called `prim_int_of_string`.
  From `556fe09` on, it uses Ceres `Deserialize_SemiIntegral` and expects a `Num` atom.

All lean-to-lambdabox branches we checked (18, including `main`, `fixes-port`, `fix-scaffolding`,
`ml/*`, `l4l/*`) still use the quoted form.

## Fix we applied locally

```diff
 instance: Serialize (BitVec n) where
-  to_sexpr b := let i := b.toFin.toNat; .atom ("\"" ++ i.repr ++ "\"")
+  to_sexpr b := let i := b.toFin.toNat; .atom i.repr
```

With this, `n * 2 + 1` extracts, compiles through Malfunction, and returns `2^101 + 1` for `2^100`.

## Related format drift (same pins)

`benchmarks/via_malfunction/*.config` use the 7-field `erasure_phases`. Current Peregrine accepts
only the 9-field form (`not enough fields, expected 9, got only 7`). Per peregrine-tool
`doc/format.md`, appending `None None` fixes it.

## Question

Is there a supported pair of lean-to-lambdabox and peregrine-tool revisions (or a CI job that
runs `#erase` output through `peregrine compile`) that downstream users should pin together?
