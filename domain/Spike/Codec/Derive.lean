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
parameters, indices, nested or mutual recursion, dependent fields, more than 255 constructors.

**Recursive types** (a field of type `T` inside `T`) get a fuel-indexed decoder
`T.codecDecAux : Nat → Bytes → …` (structural on the fuel), called with fuel = input length:
every node consumes at least its tag byte, so a valid encoding never runs out of fuel. The
round trip is proved by induction on the value (`T.codecDecAux_enc`: fuel ≥ encoding length
suffices).
Their encoder is accumulator-passing (`T.codecEncAux x acc`, no subtree is copied, linear time),
proved equal to the plain append-form `T.codecEncSpec` (`T.codecEncAux_spec`), which the
round-trip proof uses.
-/

namespace Spike.Wire.Derive
open Lean Elab Command Meta Term

/-- Field types of a constructor, as syntax, with a flag for directly recursive fields
(type exactly `self`). Rejects dependent fields, nested recursion (`self` inside another
type, e.g. `List self`) and field types without a `Codec` instance. -/
def ctorFieldTypes (self : Name) (ctor : Name) : CommandElabM (Array (Term × Bool)) := do
  let .ctorInfo ci := (← getEnv).find? ctor |>.get! | throwError "{ctor} is not a constructor"
  liftTermElabM do
    forallTelescopeReducing ci.type fun xs _ => do
      let fields := xs.extract ci.numParams xs.size
      fields.mapM fun f => do
        let ty ← inferType f
        if ty.hasAnyFVar (fun fv => fields.any (·.fvarId! == fv)) then
          throwError "Codec deriving: dependent field in {ctor} is not supported"
        if ty.isConstOf self then
          return (← withOptions (·.setBool `pp.fullNames true) (PrettyPrinter.delab ty), true)
        if ty.getUsedConstants.contains self then
          throwError "Codec deriving: nested recursion in {ctor} (field type {ty}) is not supported yet"
        if (← synthInstance? (mkApp (mkConst ``Codec) ty)).isNone then
          throwError "Codec deriving: field of type {ty} in {ctor} has no Codec instance (derive one for it first, or use Nat/Bool/List/Except)"
        return (← withOptions (·.setBool `pp.fullNames true) (PrettyPrinter.delab ty), false)

def mkCodec (declName : Name) : CommandElabM Unit := do
  let some (.inductInfo ind) := (← getEnv).find? declName
    | throwError "Codec deriving: {declName} is not an inductive type"
  if ind.numParams ≠ 0 || ind.numIndices ≠ 0 then
    throwError "Codec deriving: {declName} has parameters or indices (not supported yet)"
  if ind.all.length != 1 then throwError "Codec deriving: mutual inductives are not supported yet"
  if ind.ctors.length > 255 then throwError "Codec deriving: more than 255 constructors"
  let recursive := ind.isRec
  let tagged := ind.ctors.length != 1
  if recursive && !tagged then
    throwError "Codec deriving: recursive type {declName} with a single constructor is not supported"
  let tId := mkIdent declName
  let encId := mkIdent (declName ++ `codecEnc)
  let decId := mkIdent (declName ++ `codecDec)
  let auxId := mkIdent (declName ++ `codecDecAux)
  let specId := mkIdent (declName ++ `codecEncSpec)
  let encAuxId := mkIdent (declName ++ `codecEncAux)
  let fuel := mkIdent `f
  let mut encAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  let mut encAuxAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  let mut decBranches : Array (Nat × Term) := #[]
  for ctor in ind.ctors, i in [0:ind.ctors.length] do
    let tys ← ctorFieldTypes declName ctor
    let xs : Array Ident := (Array.range tys.size).map fun j => mkIdent (Name.mkSimple s!"x{j}")
    let rs : Array Ident := (Array.range (tys.size + 1)).map fun j => mkIdent (Name.mkSimple s!"r{j}")
    let cId := mkIdent ctor
    -- encoder: enc x0 ++ (enc x1 ++ ...), tag first if tagged; recursive fields call encId
    -- spec encoder (append form; for recursive types used in proofs only)
    let encSelf := if recursive then specId else encId
    let encField (j : Nat) : CommandElabM Term :=
      if tys[j]!.2 then `($encSelf $(xs[j]!)) else `(Codec.enc $(xs[j]!))
    let fieldsEnc : Term ← if xs.isEmpty then `(([] : Bytes)) else do
      let mut acc : Term ← encField (xs.size - 1)
      for j in (List.range (xs.size - 1)).reverse do acc ← `($(← encField j) ++ $acc)
      pure acc
    let tagLit := Syntax.mkNumLit (toString i)
    let body : Term ← if tagged then `($tagLit :: $fieldsEnc) else pure fieldsEnc
    encAlts := encAlts.push (← `(Lean.Parser.Term.matchAltExpr| | $cId $xs* => $body))
    -- accumulator encoder (recursive types): no subtree is ever copied, so linear time
    let accId := mkIdent `acc
    let mut accBody : Term ← `($accId)
    for j in (List.range xs.size).reverse do
      accBody ← if tys[j]!.2 then `($encAuxId $(xs[j]!) $accBody) else `(Codec.enc $(xs[j]!) ++ $accBody)
    if tagged then accBody ← `($tagLit :: $accBody)
    encAuxAlts := encAuxAlts.push (← `(Lean.Parser.Term.matchAltExpr| | $cId $xs*, $accId => $accBody))
    -- decoder chain from r0; recursive fields use the fuel-indexed auxiliary decoder
    let mut chain : Term ← `(Except.ok ($cId $xs*, $(rs[xs.size]!)))
    for j in (List.range xs.size).reverse do
      let call : Term ← if tys[j]!.2 then `($auxId $fuel $(rs[j]!))
        else `((Codec.dec $(rs[j]!) : Except Err ($(tys[j]!.1) × Bytes)))
      chain ← `(match $call:term with
                | .error e => .error e
                | .ok ($(xs[j]!), $(rs[j+1]!)) => $chain)
    decBranches := decBranches.push (i, chain)
  let r0 := mkIdent `r0
  let mut ite : Term ← `(Except.error Err.badTag)
  for (i, chain) in decBranches.reverse do
    ite ← `(if t = $(Syntax.mkNumLit (toString i)) then $chain else $ite)
  if recursive then
    -- spec encoder (proofs), accumulator encoder (runs), and the link between them
    elabCommand (← `(def $specId : $tId → Bytes $encAlts:matchAlt*))
    elabCommand (← `(def $encAuxId : $tId → Bytes → Bytes $encAuxAlts:matchAlt*))
    let linkId := mkIdent (declName ++ `codecEncAux_spec)
    elabCommand (← `(theorem $linkId : ∀ (x : $tId) (acc : Bytes),
          $encAuxId x acc = $specId x ++ acc := by
        intro x
        induction x <;> intro acc <;> simp [$encAuxId:ident, $specId:ident, List.append_assoc, *]))
    elabCommand (← `(def $encId (x : $tId) : Bytes := $encAuxId x []))
    elabCommand (← `(theorem $(mkIdent (declName ++ `codecEnc_spec)) (x : $tId) : $encId x = $specId x := by
        simp [$encId:ident, $linkId:ident]))
  else
    elabCommand (← `(def $encId : $tId → Bytes $encAlts:matchAlt*))
  if recursive then
    /- Fuel = input length. Every node consumes at least its tag byte, so the nesting depth
       never exceeds the input length and fuel never runs out on a valid encoding. -/
    elabCommand (← `(def $auxId : Nat → Bytes → Except Err ($tId × Bytes)
        | 0, _ => .error .truncated
        | _ + 1, [] => .error .truncated
        | $fuel:ident + 1, t :: $r0:ident => $ite))
    elabCommand (← `(def $decId (bs : Bytes) : Except Err ($tId × Bytes) := $auxId bs.length bs))
    let keyId := mkIdent (declName ++ `codecDecAux_enc)
    elabCommand (← `(theorem $keyId : ∀ (x : $tId) (rest : Bytes) (fuel : Nat),
          ($specId x).length ≤ fuel → $auxId fuel ($specId x ++ rest) = .ok (x, rest) := by
        intro x
        induction x <;> intro rest fuel h <;> cases fuel with
        | zero =>
          -- every encoding starts with its tag byte, so length = _ + 1 > 0 (closed without
          -- simp/omega on the false hypothesis, which would pull in Classical.choice)
          simp only [$specId:ident, List.length_cons] at h
          exact absurd h (Nat.not_succ_le_zero _)
        | succ f =>
          simp [$specId:ident] at h
          simp (disch := omega) [$specId:ident, $auxId:ident, List.append_assoc, *]))
    let encSpecId := mkIdent (declName ++ `codecEnc_spec)
    elabCommand (← `(instance $(mkIdent (declName ++ `instCodec)):ident : Codec $tId where
        enc := $encId
        dec := $decId
        dec_enc := by
          intro x rest
          rw [$encSpecId:ident]
          exact $keyId x rest _ (by simp)
        enc_bytes := by
          intro x
          rw [$encSpecId:ident]
          induction x <;> simp_all [$specId:ident, allBytes, allBytes_append]))
  else
    let decDef ← if tagged then
        `(def $decId : Bytes → Except Err ($tId × Bytes)
            | [] => .error .truncated
            | t :: $r0:ident => $ite)
      else
        `(def $decId ($r0 : Bytes) : Except Err ($tId × Bytes) := $(decBranches[0]!.2))
    elabCommand decDef
    elabCommand (← `(instance $(mkIdent (declName ++ `instCodec)):ident : Codec $tId where
        enc := $encId
        dec := $decId
        dec_enc := by
          intro x rest
          cases x <;> simp [$encId:ident, $decId:ident, List.append_assoc]
        enc_bytes := by
          intro x
          cases x <;> simp [$encId:ident, allBytes, allBytes_append]))

/-- Generated declarations are elaborated at the root namespace (field types are printed with
full names), so `deriving instance Codec for T` inside another namespace still defines
`T.codecEnc`, `T.codecDec`, ... rather than `Current.Namespace.T.codecEnc`. -/
def deriveCodec (declNames : Array Name) : CommandElabM Bool := do
  for n in declNames do
    withScope (fun sc => { sc with currNamespace := Name.anonymous }) (mkCodec n)
  return true

initialize registerDerivingHandler ``Codec deriveCodec

end Spike.Wire.Derive
