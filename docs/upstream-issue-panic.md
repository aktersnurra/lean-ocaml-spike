<!-- DRAFT issue for peregrine-project/lean-to-lambdabox. Review before posting. -->

# Unsupported literals are silently erased to `tBox` (panic! continues, build succeeds)

## Summary

When `#erase` meets input it doesn't support, it reports it with `panic!` in
`Erasure.erase.visitLiteral`, but a Lean panic prints a message and *returns a default value*.
Elaboration continues, the unsupported literal becomes `tBox`, the `.ast` is written, `lake build`
exits 0 with "Build completed successfully", and `peregrine compile` compiles the result
("Compiled successfully"). Unless someone reads the log, the extracted program is silently wrong.

Affected cases (both in `visitLiteral`):
- a `Nat` literal larger than `BitVec.intMax 63` (`"Nat literal not representable as a 63-bit signed integer."`)
- any string literal (`"String literals not supported."`)

## Reproduce (Lean v4.22.0, lean-to-lambdabox 58701f8)

```lean
import LeanToLambdaBox
def eOver (n : Nat) : Nat := n + 4611686018427387904   -- 2^62
#erase eOver to "eOver.ast" mli "eOver.mli"
```

```
PANIC at Erasure.erase.visitLiteral LeanToLambdaBox.Erasure:387:8: Nat literal not representable as a 63-bit signed integer.
...
Build completed successfully.      # lake build exit code 0
```

`eOver.ast` contains `(tApp (tApp (tApp (tConst … "OfNat" "ofNat") tBox) tBox) (tApp (tConst … "instOfNatNat") tBox))`:
the literal is gone. `peregrine compile eOver.ast …` reports `Compiled successfully`.
Same for `def sLen (n : Nat) : Nat := n + "hello".length`.

## Suggestion

Report unsupported input as an elaboration error instead of a panic, e.g. `throwError` in
`visitLiteral` (EraseM runs in CoreM, so `throwError` is available), so `#erase` fails, no
`.ast` is written, and `lake build` fails. For large `Nat` literals there's also an alternative: emit
them as an application of the `Nat` axioms (e.g. multiply-add of in-range literals) instead of
rejecting them.

(Workaround on our side for now: fail the build if the Lean output contains `PANIC`.)
