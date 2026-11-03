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
parameters, indices, mutual inductives, nesting other than `List T`, dependent fields, more
than 255 constructors.

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

/-- Terms as `simp` arguments (for splicing into generated `simp [...]` calls). -/
def toSimpArgs (ts : Array Term) : CommandElabM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) :=
  ts.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)

/-- How a constructor field is encoded. -/
inductive FieldKind where
  | plain    -- any type with a `Codec` instance
  | self     -- the type being derived (direct recursion)
  | listSelf -- `List` of the type being derived (nested recursion)
deriving BEq, Inhabited

/-- Field types of a constructor, as syntax (full names), with their kind. Rejects dependent
fields, other nested recursion (`self` inside anything but a plain `List self`) and field
types without a `Codec` instance. -/
def ctorFieldTypes (self : Name) (ctor : Name) : CommandElabM (Array (Term × FieldKind)) := do
  let .ctorInfo ci := (← getEnv).find? ctor |>.get! | throwError "{ctor} is not a constructor"
  liftTermElabM do
    forallTelescopeReducing ci.type fun xs _ => do
      let fields := xs.extract ci.numParams xs.size
      fields.mapM fun f => do
        let ty ← inferType f
        if ty.hasAnyFVar (fun fv => fields.any (·.fvarId! == fv)) then
          throwError "Codec deriving: dependent field in {ctor} is not supported"
        let stx ← withOptions (·.setBool `pp.fullNames true) (PrettyPrinter.delab ty)
        if ty.isConstOf self then return (stx, .self)
        if ty.isAppOfArity ``List 1 && ty.appArg!.isConstOf self then return (stx, .listSelf)
        if ty.getUsedConstants.contains self then
          throwError "Codec deriving: nested recursion in {ctor} (field type {ty}) is not supported yet; only `List {self}` is"
        if (← synthInstance? (mkApp (mkConst ``Codec) ty)).isNone then
          throwError "Codec deriving: field of type {ty} in {ctor} has no Codec instance (derive one for it first, or use Nat/Bool/List/Except)"
        return (stx, .plain)

def mkCodec (declName : Name) : CommandElabM Unit := do
  let some (.inductInfo ind) := (← getEnv).find? declName
    | throwError "Codec deriving: {declName} is not an inductive type"
  if ind.numParams ≠ 0 || ind.numIndices ≠ 0 then
    throwError "Codec deriving: {declName} has parameters or indices (not supported yet)"
  if ind.all.length != 1 then throwError "Codec deriving: mutual inductives are not supported yet"
  if ind.ctors.length > 255 then throwError "Codec deriving: more than 255 constructors"
  let recursive := ind.isRec || ind.isNested
  -- recursive types always carry a tag byte (even with one constructor): every node then
  -- consumes at least one byte, which the fuel argument and its proof rely on
  let tagged := ind.ctors.length != 1 || recursive
  let ctorsInfo ← ind.ctors.toArray.mapM fun c => do pure (c, ← ctorFieldTypes declName c)
  let nested := ctorsInfo.any fun (_, tys) => tys.any (·.2 == .listSelf)
  let n (s : Name) := mkIdent (declName ++ s)
  let tId := mkIdent declName
  let encId := n `codecEnc; let decId := n `codecDec; let auxId := n `codecDecAux
  let specId := n `codecEncSpec; let specListId := n `codecEncSpecList
  let encAuxId := n `codecEncAux; let encAuxListId := n `codecEncAuxList
  let fuel := mkIdent `f
  let accId := mkIdent `acc
  let r0 := mkIdent `r0
  let mut encAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  let mut encAuxAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  let mut linkAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  let mut bytesAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  let mut decBranches : Array (Nat × Term) := #[]
  for (ctor, tys) in ctorsInfo, i in [0:ctorsInfo.size] do
    let xs : Array Ident := (Array.range tys.size).map fun j => mkIdent (Name.mkSimple s!"x{j}")
    let rs : Array Ident := (Array.range (tys.size + 1)).map fun j => mkIdent (Name.mkSimple s!"r{j}")
    let cId := mkIdent ctor
    let tagLit := Syntax.mkNumLit (toString i)
    -- spec encoder (append form): plain encoder for non-recursive types, proof-only otherwise
    let encSelf := if recursive then specId else encId
    let encField (j : Nat) : CommandElabM Term :=
      match tys[j]!.2 with
      | .plain => `(Codec.enc $(xs[j]!))
      | .self => `($encSelf $(xs[j]!))
      | .listSelf => `(encodeNat ($(xs[j]!)).length ++ $specListId $(xs[j]!))
    let fieldsEnc : Term ← if xs.isEmpty then `(([] : Bytes)) else do
      let mut acc : Term ← encField (xs.size - 1)
      for j in (List.range (xs.size - 1)).reverse do acc ← `($(← encField j) ++ $acc)
      pure acc
    let body : Term ← if tagged then `($tagLit :: $fieldsEnc) else pure fieldsEnc
    encAlts := encAlts.push (← `(Lean.Parser.Term.matchAltExpr| | $cId $xs* => $body))
    -- accumulator encoder (runs for recursive types): no subtree is copied, linear time
    let mut accBody : Term ← `($accId)
    for j in (List.range xs.size).reverse do
      accBody ← match tys[j]!.2 with
        | .plain => `(Codec.enc $(xs[j]!) ++ $accBody)
        | .self => `($encAuxId $(xs[j]!) $accBody)
        | .listSelf => `(encodeNat ($(xs[j]!)).length ++ $encAuxListId $(xs[j]!) $accBody)
    if tagged then accBody ← `($tagLit :: $accBody)
    encAuxAlts := encAuxAlts.push (← `(Lean.Parser.Term.matchAltExpr| | $cId $xs*, $accId => $accBody))
    -- per-constructor proofs name exactly the recursive lemmas this constructor needs
    let mut linkLemmas : Array Term := #[]
    let mut bytesLemmas : Array Term := #[]
    for j in [0:xs.size] do
      match tys[j]!.2 with
      | .plain => pure ()
      | .self =>
        linkLemmas := linkLemmas.push (← `($(n `codecEncAux_spec) $(xs[j]!)))
        bytesLemmas := bytesLemmas.push (← `($(n `codecEncSpec_bytes) $(xs[j]!)))
      | .listSelf =>
        linkLemmas := linkLemmas.push (← `($(n `codecEncAuxList_spec) $(xs[j]!)))
        bytesLemmas := bytesLemmas.push (← `($(n `codecEncSpecList_bytes) $(xs[j]!)))
    let linkArgs : Array (TSyntax `term) := #[← `($encAuxId), ← `($specId), ← `(List.append_assoc)] ++ linkLemmas
    let bytesArgs : Array (TSyntax `term) := #[← `($specId), ← `(allBytes), ← `(allBytes_append), ← `(allBytes_encodeNat)] ++ bytesLemmas
    let linkSA ← toSimpArgs linkArgs
    let bytesSA ← toSimpArgs bytesArgs
    linkAlts := linkAlts.push (← `(Lean.Parser.Term.matchAltExpr| | $cId $xs*, $accId => by simp [$linkSA,*]))
    bytesAlts := bytesAlts.push (← `(Lean.Parser.Term.matchAltExpr| | $cId $xs* => by simp [$bytesSA,*]))
    -- decoder chain from r0; recursive fields use the fuel-indexed auxiliary decoder
    let mut chain : Term ← `(Except.ok ($cId $xs*, $(rs[xs.size]!)))
    for j in (List.range xs.size).reverse do
      let call : Term ← match tys[j]!.2 with
        | .plain => `((Codec.dec $(rs[j]!) : Except Err ($(tys[j]!.1) × Bytes)))
        | .self => `($auxId $fuel $(rs[j]!))
        | .listSelf => `(decodeList ($auxId $fuel) $(rs[j]!))
      chain ← `(match $call:term with
                | .error e => .error e
                | .ok ($(xs[j]!), $(rs[j+1]!)) => $chain)
    decBranches := decBranches.push (i, chain)
  let mut ite : Term ← `(Except.error Err.badTag)
  for (i, chain) in decBranches.reverse do
    ite ← `(if t = $(Syntax.mkNumLit (toString i)) then $chain else $ite)
  if !recursive then
    elabCommand (← `(def $encId : $tId → Bytes $encAlts:matchAlt*))
    let decDef ← if tagged then
        `(def $decId : Bytes → Except Err ($tId × Bytes)
            | [] => .error .truncated
            | t :: $r0:ident => $ite)
      else
        `(def $decId ($r0 : Bytes) : Except Err ($tId × Bytes) := $(decBranches[0]!.2))
    elabCommand decDef
    elabCommand (← `(instance $(n `instCodec):ident : Codec $tId where
        enc := $encId
        dec := $decId
        dec_enc := by
          intro x rest
          cases x <;> simp [$encId:ident, $decId:ident, List.append_assoc]
        enc_bytes := by
          intro x
          cases x <;> simp [$encId:ident, allBytes, allBytes_append]))
    return
  /- Recursive types (direct `T` fields and/or nested `List T` fields). -/
  let tsId := mkIdent `ts; let tId' := mkIdent `t
  -- spec encoder(s) (append form; proofs only)
  if nested then
    elabCommand (← `(mutual
      def $specId : $tId → Bytes $encAlts:matchAlt*
      termination_by structural t => t
      def $specListId : List $tId → Bytes
        | [] => []
        | $tId' :: $tsId => $specId $tId' ++ $specListId $tsId
      termination_by structural ts => ts
      end))
  else
    elabCommand (← `(def $specId : $tId → Bytes $encAlts:matchAlt*))
  -- accumulator encoder(s) (run)
  if nested then
    elabCommand (← `(mutual
      def $encAuxId : $tId → Bytes → Bytes $encAuxAlts:matchAlt*
      termination_by structural t => t
      def $encAuxListId : List $tId → Bytes → Bytes
        | [], $accId => $accId
        | $tId' :: $tsId, $accId => $encAuxId $tId' ($encAuxListId $tsId $accId)
      termination_by structural ts => ts
      end))
  else
    elabCommand (← `(def $encAuxId : $tId → Bytes → Bytes $encAuxAlts:matchAlt*))
  -- link: accumulator encoder = spec ++ acc
  if nested then
    elabCommand (← `(set_option linter.unusedSimpArgs false in
      theorem $(n `codecEncSpecList_eq) : ∀ (ts : List $tId), $specListId ts = encodeElems $specId ts
        | [] => by simp [$specListId:ident, encodeElems]
        | $tId' :: $tsId => by simp [$specListId:ident, encodeElems, ($(n `codecEncSpecList_eq) $tsId)]))
    elabCommand (← `(set_option linter.unusedSimpArgs false in
      mutual
      theorem $(n `codecEncAux_spec) : ∀ (x : $tId) (acc : Bytes), $encAuxId x acc = $specId x ++ acc
        $linkAlts:matchAlt*
      termination_by structural x => x
      theorem $(n `codecEncAuxList_spec) : ∀ (ts : List $tId) (acc : Bytes),
          $encAuxListId ts acc = $specListId ts ++ acc
        | [], $accId => by simp [$encAuxListId:ident, $specListId:ident]
        | $tId' :: $tsId, $accId => by
          simp [$encAuxListId:ident, $specListId:ident, List.append_assoc,
            ($(n `codecEncAux_spec) $tId'), ($(n `codecEncAuxList_spec) $tsId)]
      termination_by structural ts => ts
      end))
  else
    elabCommand (← `(set_option linter.unusedSimpArgs false in
      theorem $(n `codecEncAux_spec) : ∀ (x : $tId) (acc : Bytes), $encAuxId x acc = $specId x ++ acc
        $linkAlts:matchAlt*))
  elabCommand (← `(def $encId (x : $tId) : Bytes := $encAuxId x []))
  elabCommand (← `(theorem $(n `codecEnc_spec) (x : $tId) : $encId x = $specId x := by
      simp [$encId:ident, $(n `codecEncAux_spec):ident]))
  /- Decoder: fuel = input length. Every node consumes at least its tag byte, so the nesting
     depth never exceeds the input length and fuel never runs out on a valid encoding. -/
  elabCommand (← `(def $auxId : Nat → Bytes → Except Err ($tId × Bytes)
      | 0, _ => .error .truncated
      | _ + 1, [] => .error .truncated
      | $fuel:ident + 1, t :: $r0:ident => $ite
      termination_by structural f => f))
  elabCommand (← `(def $decId (bs : Bytes) : Except Err ($tId × Bytes) := $auxId bs.length bs))
  -- round trip by induction on the fuel (no nested induction needed)
  let keyId := n `codecDecAux_enc
  let ih := mkIdent `ih
  let listEq ← `($(n `codecEncSpecList_eq):ident)
  let listFuel ← `(decodeList_fuel _ _ $fuel $ih)
  let extra : Array Term := if nested then #[listEq, listFuel] else #[]
  let succArgs ← toSimpArgs (#[← `($specId), ← `($auxId), ← `(List.append_assoc), ← `($ih)] ++ extra)
  let hArgs ← toSimpArgs (#[← `($specId)] ++ (if nested then #[listEq] else #[]))
  elabCommand (← `(set_option linter.unusedSimpArgs false in
    theorem $keyId : ∀ (fuel : Nat) (x : $tId) (rest : Bytes),
        ($specId x).length ≤ fuel → $auxId fuel ($specId x ++ rest) = .ok (x, rest) := by
      intro fuel
      induction fuel with
      | zero =>
        intro x rest h
        -- every encoding starts with its tag byte, so length = _ + 1 > 0 (closed without
        -- simp/omega on the false hypothesis, which would pull in Classical.choice)
        cases x <;> (simp only [$specId:ident, List.length_cons] at h; exact absurd h (Nat.not_succ_le_zero _))
      | succ $fuel:ident $ih:ident =>
        intro x rest h
        cases x <;> simp [$hArgs,*] at h <;> simp (disch := omega) [$succArgs,*]))
  -- encoders emit only bytes
  if nested then
    elabCommand (← `(set_option linter.unusedSimpArgs false in
      mutual
      theorem $(n `codecEncSpec_bytes) : ∀ (x : $tId), allBytes ($specId x) = true
        $bytesAlts:matchAlt*
      termination_by structural x => x
      theorem $(n `codecEncSpecList_bytes) : ∀ (ts : List $tId), allBytes ($specListId ts) = true
        | [] => by simp [$specListId:ident, allBytes]
        | $tId' :: $tsId => by
          simp [$specListId:ident, allBytes_append, ($(n `codecEncSpec_bytes) $tId'),
            ($(n `codecEncSpecList_bytes) $tsId)]
      termination_by structural ts => ts
      end))
  else
    elabCommand (← `(set_option linter.unusedSimpArgs false in
      theorem $(n `codecEncSpec_bytes) : ∀ (x : $tId), allBytes ($specId x) = true
        $bytesAlts:matchAlt*))
  elabCommand (← `(instance $(n `instCodec):ident : Codec $tId where
      enc := $encId
      dec := $decId
      dec_enc := by
        intro x rest
        rw [$(n `codecEnc_spec):ident]
        exact $keyId _ x rest (by simp)
      enc_bytes := by
        intro x
        rw [$(n `codecEnc_spec):ident]
        exact $(n `codecEncSpec_bytes) x))

/-- Generated declarations are elaborated at the root namespace (field types are printed with
full names), so `deriving instance Codec for T` inside another namespace still defines
`T.codecEnc`, `T.codecDec`, ... rather than `Current.Namespace.T.codecEnc`. -/
def deriveCodec (declNames : Array Name) : CommandElabM Bool := do
  for n in declNames do
    withScope (fun sc => { sc with currNamespace := Name.anonymous }) (mkCodec n)
  return true

initialize registerDerivingHandler ``Codec deriveCodec

end Spike.Wire.Derive
