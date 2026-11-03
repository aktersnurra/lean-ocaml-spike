import Lean
import Spike.Codec

/-!
# `deriving Codec`

For a non-recursive inductive type without parameters or indices (structures included),
generates

* `T.codecEnc : T → Bytes`: fields encoded in order; a constructor-tag byte first when the
  type has more than one constructor;
* `T.codecDec : Bytes → Except Err (T × Bytes)`: the matching decoder (`truncated` on short
  input, `badTag` on an unknown tag);
* `instance : Codec T`, whose `dec_enc` and `enc_bytes` proofs are discharged by a fixed
  `cases`/`simp` script from the field types' own `Codec` proofs.

So a derived codec either comes with its proofs or fails to elaborate; there is no unproved
derived codec. Every field type needs a `Codec` instance. Unsupported (clear error):
parameters, indices, recursive types, dependent fields, more than 255 constructors.
-/

namespace Spike.Wire.Derive
open Lean Elab Command Meta Term

/-- Field types of a constructor, as syntax, rejecting dependent fields. -/
def ctorFieldTypes (ctor : Name) : CommandElabM (Array Term) := do
  let .ctorInfo ci := (← getEnv).find? ctor |>.get! | throwError "{ctor} is not a constructor"
  liftTermElabM do
    forallTelescopeReducing ci.type fun xs _ => do
      let fields := xs.extract ci.numParams xs.size
      fields.mapM fun f => do
        let ty ← inferType f
        if ty.hasAnyFVar (fun fv => fields.any (·.fvarId! == fv)) then
          throwError "Codec deriving: dependent field in {ctor} is not supported"
        if (← synthInstance? (mkApp (mkConst ``Codec) ty)).isNone then
          throwError "Codec deriving: field of type {ty} in {ctor} has no Codec instance (derive one for it first, or use Nat/Bool/List/Except)"
        PrettyPrinter.delab ty

def mkCodec (declName : Name) : CommandElabM Unit := do
  let some (.inductInfo ind) := (← getEnv).find? declName
    | throwError "Codec deriving: {declName} is not an inductive type"
  if ind.numParams ≠ 0 || ind.numIndices ≠ 0 then
    throwError "Codec deriving: {declName} has parameters or indices (not supported yet)"
  if ind.isRec then throwError "Codec deriving: {declName} is recursive (not supported yet)"
  if ind.ctors.length > 255 then throwError "Codec deriving: more than 255 constructors"
  let tagged := ind.ctors.length != 1
  let tId := mkIdent declName
  let encId := mkIdent (declName ++ `codecEnc)
  let decId := mkIdent (declName ++ `codecDec)
  let mut encAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  let mut decBranches : Array (Nat × Term) := #[]
  for ctor in ind.ctors, i in [0:ind.ctors.length] do
    let tys ← ctorFieldTypes ctor
    let xs : Array Ident := (Array.range tys.size).map fun j => mkIdent (Name.mkSimple s!"x{j}")
    let rs : Array Ident := (Array.range (tys.size + 1)).map fun j => mkIdent (Name.mkSimple s!"r{j}")
    let cId := mkIdent ctor
    -- encoder: enc x0 ++ (enc x1 ++ ...), tag first if tagged
    let fieldsEnc : Term ← if xs.isEmpty then `(([] : Bytes)) else do
      let mut acc : Term ← `(Codec.enc $(xs.back!))
      for x in xs.pop.reverse do acc ← `(Codec.enc $x ++ $acc)
      pure acc
    let tagLit := Syntax.mkNumLit (toString i)
    let body : Term ← if tagged then `($tagLit :: $fieldsEnc) else pure fieldsEnc
    encAlts := encAlts.push (← `(Lean.Parser.Term.matchAltExpr| | $cId $xs* => $body))
    -- decoder chain, starting from input r0
    let mut chain : Term ← `(Except.ok ($cId $xs*, $(rs[xs.size]!)))
    for j in (List.range xs.size).reverse do
      chain ← `(match (Codec.dec $(rs[j]!) : Except Err ($(tys[j]!) × Bytes)) with
                | .error e => .error e
                | .ok ($(xs[j]!), $(rs[j+1]!)) => $chain)
    decBranches := decBranches.push (i, chain)
  let r0 := mkIdent `r0
  let decDef ← if tagged then do
      let mut ite : Term ← `(Except.error Err.badTag)
      for (i, chain) in decBranches.reverse do
        ite ← `(if t = $(Syntax.mkNumLit (toString i)) then $chain else $ite)
      `(def $decId : Bytes → Except Err ($tId × Bytes)
          | [] => .error .truncated
          | t :: $r0:ident => $ite)
    else
      `(def $decId ($r0 : Bytes) : Except Err ($tId × Bytes) := $(decBranches[0]!.2))
  let encDef ← `(def $encId : $tId → Bytes $encAlts:matchAlt*)
  let inst ← `(instance : Codec $tId where
      enc := $encId
      dec := $decId
      dec_enc := by
        intro x rest
        cases x <;> simp [$encId:ident, $decId:ident, List.append_assoc]
      enc_bytes := by
        intro x
        cases x <;> simp [$encId:ident, allBytes, allBytes_append])
  elabCommand encDef
  elabCommand decDef
  elabCommand inst

def deriveCodec (declNames : Array Name) : CommandElabM Bool := do
  for n in declNames do mkCodec n
  return true

initialize registerDerivingHandler ``Codec deriveCodec

end Spike.Wire.Derive
