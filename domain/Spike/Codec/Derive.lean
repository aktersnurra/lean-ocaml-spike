import Lean
import Spike.Codec

/-!
# `deriving Codec`

Generates `Codec` instances (encoder, decoder, and the round-trip / bytes-only proofs) for a
*block* of inductive types: a single type, or all types of a `mutual` block, possibly with
type parameters (`(α : Type)`, shared by the block).

* `T.codecEnc`, `T.codecDec`: fields encoded in order; a constructor-tag byte first when the
  type has more than one constructor or the block is recursive.
* `instance T.instCodec [Codec α] … : Codec (T α …)`, whose proofs are discharged by generated
  scripts from the field types' own `Codec` proofs. A derived codec either comes with its proofs
  or fails to elaborate; there is no unproved derived codec.

Field kinds: any type with a `Codec` instance (may mention the parameters; e.g. `List α`), a
block member applied to the block's parameters (direct or mutual recursion), or `List` of one
(nested recursion).

**Recursive blocks** get, per type `T`:
* encoders as mutual structural definitions over all block types and the `List` of those used
  nested: `T.codecEncSpec` (append form, proofs only) and `T.codecEncAux` (accumulator form,
  linear time, runs), proved equal (`T.codecEncAux_spec`);
* a fuel-indexed decoder `T.codecDecAux : Nat → Bytes → …` (mutual, structural on the fuel),
  called with fuel = input length: every node consumes its tag byte, so a valid encoding never
  runs out of fuel;
* the round trip proved by induction on the fuel for the whole block at once (a conjunction
  over the block's types), so no (nested or mutual) induction on values is needed.

Unsupported (clear error): indices, universe-polymorphic types, parameters that are not
`Type`, nesting other than `List T`, irregular recursion (a block member applied to other
arguments than the parameters), dependent fields, more than 255 constructors.
-/

namespace Spike.Wire.Derive
open Lean Elab Command Meta Term

/-- Terms as `simp` arguments (for splicing into generated `simp [...]` calls). -/
def toSimpArgs (ts : Array Term) : CommandElabM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) :=
  ts.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)

/-- How a constructor field is encoded. -/
inductive FieldKind where
  | plain           -- any type with a `Codec` instance
  | member (i : Nat)     -- block member `i` (direct or mutual recursion)
  | listMember (i : Nat) -- `List` of block member `i` (nested recursion)
deriving BEq, Inhabited

/-- Is `ty` block member `i` applied to exactly the parameters `ps`? -/
def blockMember? (block : Array Name) (ps : Array Expr) (ty : Expr) : Option Nat :=
  match ty.getAppFn with
  | .const c _ =>
    match block.findIdx? (· == c) with
    | some i => if ty.getAppArgs == ps then some i else none
    | none => none
  | _ => none

/-- Field types of a constructor (as syntax with full names) and their kinds. -/
def ctorFieldTypes (block : Array Name) (ctor : Name) : CommandElabM (Array (Term × FieldKind)) := do
  let .ctorInfo ci := (← getEnv).find? ctor |>.get! | throwError "{ctor} is not a constructor"
  liftTermElabM do
    forallTelescopeReducing ci.type fun xs _ => do
      let ps := xs.extract 0 ci.numParams
      let fields := xs.extract ci.numParams xs.size
      fields.mapM fun f => do
        let ty ← instantiateMVars (← inferType f)
        if ty.hasAnyFVar (fun fv => fields.any (·.fvarId! == fv)) then
          throwError "Codec deriving: dependent field in {ctor} is not supported"
        let stx ← withOptions (·.setBool `pp.fullNames true) (PrettyPrinter.delab ty)
        if let some i := blockMember? block ps ty then return (stx, .member i)
        if ty.isAppOfArity ``List 1 then
          if let some i := blockMember? block ps ty.appArg! then return (stx, .listMember i)
        if block.any (ty.getUsedConstants.contains ·) then
          throwError "Codec deriving: field type {ty} in {ctor} uses the type being derived in an unsupported way (only `T params` and `List (T params)` are supported)"
        -- instance check only for closed types (with parameters, `[Codec α]` is assumed)
        if !ty.hasFVar then
          if (← synthInstance? (mkApp (mkConst ``Codec) ty)).isNone then
            throwError "Codec deriving: field of type {ty} in {ctor} has no Codec instance (derive one for it first, or use Nat/Bool/List/Except)"
        return (stx, .plain)

/-- Parameter names of an inductive type, checking every parameter is a `Type`. -/
def paramNames (ind : InductiveVal) : CommandElabM (Array Name) := liftTermElabM do
  forallTelescopeReducing ind.type fun xs _ => do
    let ps := xs.extract 0 ind.numParams
    ps.mapM fun p => do
      let t ← inferType p
      unless t == mkSort levelOne do
        throwError "Codec deriving: parameter {p} of {ind.name} must have type `Type` (got {t})"
      return (← p.fvarId!.getDecl).userName

structure TyInfo where
  name : Name
  ctors : Array (Name × Array (Term × FieldKind))
deriving Inhabited

def mkCodecBlock (block : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  let inds ← block.mapM fun n => do
    let some (.inductInfo ind) := env.find? n | throwError "Codec deriving: {n} is not an inductive type"
    if ind.numIndices ≠ 0 then throwError "Codec deriving: {n} has indices (not supported)"
    if !ind.levelParams.isEmpty then
      throwError "Codec deriving: {n} is universe polymorphic (not supported; use `Type` parameters)"
    if ind.ctors.length > 255 then throwError "Codec deriving: {n} has more than 255 constructors"
    pure ind
  let pnames ← paramNames inds[0]!
  let recursive := inds.any fun ind => ind.isRec || ind.isNested
  let infos : Array TyInfo ← inds.mapM fun ind => do
    pure ⟨ind.name, ← ind.ctors.toArray.mapM fun c => do pure (c, ← ctorFieldTypes block c)⟩
  -- which block members are used under `List` (they need list helpers)
  let listUsed : Array Bool := (Array.range block.size).map fun j =>
    infos.any fun ti => ti.ctors.any fun (_, tys) => tys.any (·.2 == .listMember j)
  -- binders shared by all generated declarations
  let pIds : Array Ident := pnames.map mkIdent
  let mut binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  for p in pIds do binders := binders.push (← `(bracketedBinder| {$p : Type}))
  for p in pIds do binders := binders.push (← `(bracketedBinder| [Codec $p]))
  let tyOf (i : Nat) : CommandElabM Term := do
    let c := mkIdent block[i]!
    if pIds.isEmpty then pure c else `($c $pIds*)
  let nm (i : Nat) (s : Name) : Ident := mkIdent (block[i]! ++ s)
  let fuel := mkIdent `f; let accId := mkIdent `acc; let r0 := mkIdent `r0
  let tVar := mkIdent `t; let tsVar := mkIdent `ts
  if !recursive then
    -- non-recursive single type (a non-recursive "block" is always a single type)
    let ti := infos[0]!
    let tTy ← tyOf 0
    let tagged := ti.ctors.size != 1
    let encId := nm 0 `codecEnc; let decId := nm 0 `codecDec
    let mut encAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    let mut branches : Array (Nat × Term) := #[]
    for (ctor, tys) in ti.ctors, i in [0:ti.ctors.size] do
      let xs : Array Ident := (Array.range tys.size).map fun j => mkIdent (Name.mkSimple s!"x{j}")
      let rs : Array Ident := (Array.range (tys.size + 1)).map fun j => mkIdent (Name.mkSimple s!"r{j}")
      let cId := mkIdent ctor
      let fieldsEnc : Term ← if xs.isEmpty then `(([] : Bytes)) else do
        let mut acc : Term ← `(Codec.enc $(xs.back!))
        for x in xs.pop.reverse do acc ← `(Codec.enc $x ++ $acc)
        pure acc
      let body : Term ← if tagged then `($(Syntax.mkNumLit (toString i)) :: $fieldsEnc) else pure fieldsEnc
      encAlts := encAlts.push (← `(Lean.Parser.Term.matchAltExpr| | $cId $xs* => $body))
      let mut chain : Term ← `(Except.ok ($cId $xs*, $(rs[xs.size]!)))
      for j in (List.range xs.size).reverse do
        chain ← `(match (Codec.dec $(rs[j]!) : Except Err ($(tys[j]!.1) × Bytes)) with
                  | .error e => .error e
                  | .ok ($(xs[j]!), $(rs[j+1]!)) => $chain)
      branches := branches.push (i, chain)
    let mut ite : Term ← `(Except.error Err.badTag)
    for (i, chain) in branches.reverse do
      ite ← `(if t = $(Syntax.mkNumLit (toString i)) then $chain else $ite)
    elabCommand (← `(def $encId $binders* : $tTy → Bytes $encAlts:matchAlt*))
    if tagged then
      elabCommand (← `(def $decId $binders* : Bytes → Except Err ($tTy × Bytes)
          | [] => .error .truncated
          | t :: $r0:ident => $ite))
    else
      elabCommand (← `(def $decId $binders* ($r0 : Bytes) : Except Err ($tTy × Bytes) := $(branches[0]!.2)))
    elabCommand (← `(instance $(nm 0 `instCodec):ident $binders* : Codec $tTy where
        enc := $encId
        dec := $decId
        dec_enc := by
          intro x rest
          cases x <;> simp [$encId:ident, $decId:ident, List.append_assoc]
        enc_bytes := by
          intro x
          cases x <;> simp [$encId:ident, allBytes, allBytes_append]))
    return
  /- ===== Recursive blocks (direct, nested and/or mutual recursion) ===== -/
  -- recursive types always carry a tag byte: every node then consumes at least one byte
  let k := block.size
  let specId (i : Nat) := nm i `codecEncSpec
  let specListId (i : Nat) := nm i `codecEncSpecList
  let encAuxId (i : Nat) := nm i `codecEncAux
  let encAuxListId (i : Nat) := nm i `codecEncAuxList
  let auxId (i : Nat) := nm i `codecDecAux
  let mut specDefs : Array (TSyntax `command) := #[]
  let mut encAuxDefs : Array (TSyntax `command) := #[]
  let mut linkThms : Array (TSyntax `command) := #[]
  let mut bytesThms : Array (TSyntax `command) := #[]
  let mut auxDefs : Array (TSyntax `command) := #[]
  for ti in infos, ti_i in [0:k] do
    let tTy ← tyOf ti_i
    let mut encAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    let mut encAuxAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    let mut linkAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    let mut bytesAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    let mut branches : Array (Nat × Term) := #[]
    for (ctor, tys) in ti.ctors, i in [0:ti.ctors.size] do
      let xs : Array Ident := (Array.range tys.size).map fun j => mkIdent (Name.mkSimple s!"x{j}")
      let rs : Array Ident := (Array.range (tys.size + 1)).map fun j => mkIdent (Name.mkSimple s!"r{j}")
      let cId := mkIdent ctor
      let tagLit := Syntax.mkNumLit (toString i)
      -- spec encoder (append form)
      let encField (j : Nat) : CommandElabM Term :=
        match tys[j]!.2 with
        | .plain => `(Codec.enc $(xs[j]!))
        | .member m => `($(specId m) $(xs[j]!))
        | .listMember m => `(encodeNat ($(xs[j]!)).length ++ $(specListId m) $(xs[j]!))
      let fieldsEnc : Term ← if xs.isEmpty then `(([] : Bytes)) else do
        let mut acc : Term ← encField (xs.size - 1)
        for j in (List.range (xs.size - 1)).reverse do acc ← `($(← encField j) ++ $acc)
        pure acc
      encAlts := encAlts.push (← `(Lean.Parser.Term.matchAltExpr| | $cId $xs* => $tagLit :: $fieldsEnc))
      -- accumulator encoder
      let mut accBody : Term ← `($accId)
      for j in (List.range xs.size).reverse do
        accBody ← match tys[j]!.2 with
          | .plain => `(Codec.enc $(xs[j]!) ++ $accBody)
          | .member m => `($(encAuxId m) $(xs[j]!) $accBody)
          | .listMember m => `(encodeNat ($(xs[j]!)).length ++ $(encAuxListId m) $(xs[j]!) $accBody)
      encAuxAlts := encAuxAlts.push (← `(Lean.Parser.Term.matchAltExpr| | $cId $xs*, $accId => $tagLit :: $accBody))
      -- per-constructor proofs name exactly the recursive lemmas this constructor needs
      let mut linkLemmas : Array Term := #[]
      let mut bytesLemmas : Array Term := #[]
      for j in [0:xs.size] do
        match tys[j]!.2 with
        | .plain => pure ()
        | .member m =>
          linkLemmas := linkLemmas.push (← `($(nm m `codecEncAux_spec) $(xs[j]!)))
          bytesLemmas := bytesLemmas.push (← `($(nm m `codecEncSpec_bytes) $(xs[j]!)))
        | .listMember m =>
          linkLemmas := linkLemmas.push (← `($(nm m `codecEncAuxList_spec) $(xs[j]!)))
          bytesLemmas := bytesLemmas.push (← `($(nm m `codecEncSpecList_bytes) $(xs[j]!)))
      let allEnc : Array Term ← (Array.range k).mapM fun m => `($(encAuxId m))
      let allSpec : Array Term ← (Array.range k).mapM fun m => `($(specId m))
      let linkSA ← toSimpArgs (allEnc ++ allSpec ++ #[← `(List.append_assoc)] ++ linkLemmas)
      let bytesSA ← toSimpArgs (allSpec ++ #[← `(allBytes), ← `(allBytes_append), ← `(allBytes_encodeNat)] ++ bytesLemmas)
      linkAlts := linkAlts.push (← `(Lean.Parser.Term.matchAltExpr| | $cId $xs*, $accId => by simp [$linkSA,*]))
      bytesAlts := bytesAlts.push (← `(Lean.Parser.Term.matchAltExpr| | $cId $xs* => by simp [$bytesSA,*]))
      -- decoder chain
      let mut chain : Term ← `(Except.ok ($cId $xs*, $(rs[xs.size]!)))
      for j in (List.range xs.size).reverse do
        let call : Term ← match tys[j]!.2 with
          | .plain => `((Codec.dec $(rs[j]!) : Except Err ($(tys[j]!.1) × Bytes)))
          | .member m => `($(auxId m) $fuel $(rs[j]!))
          | .listMember m => `(decodeList ($(auxId m) $fuel) $(rs[j]!))
        chain ← `(match $call:term with
                  | .error e => .error e
                  | .ok ($(xs[j]!), $(rs[j+1]!)) => $chain)
      branches := branches.push (i, chain)
    let mut ite : Term ← `(Except.error Err.badTag)
    for (i, chain) in branches.reverse do
      ite ← `(if t = $(Syntax.mkNumLit (toString i)) then $chain else $ite)
    specDefs := specDefs.push (← `(def $(specId ti_i) $binders* : $tTy → Bytes $encAlts:matchAlt*
      termination_by structural x => x))
    encAuxDefs := encAuxDefs.push (← `(def $(encAuxId ti_i) $binders* : $tTy → Bytes → Bytes $encAuxAlts:matchAlt*
      termination_by structural x => x))
    linkThms := linkThms.push (← `(theorem $(nm ti_i `codecEncAux_spec) $binders* :
        ∀ (x : $tTy) (acc : Bytes), $(encAuxId ti_i) x acc = $(specId ti_i) x ++ acc
      $linkAlts:matchAlt*
      termination_by structural x => x))
    bytesThms := bytesThms.push (← `(theorem $(nm ti_i `codecEncSpec_bytes) $binders* :
        ∀ (x : $tTy), allBytes ($(specId ti_i) x) = true
      $bytesAlts:matchAlt*
      termination_by structural x => x))
    auxDefs := auxDefs.push (← `(def $(auxId ti_i) $binders* : Nat → Bytes → Except Err ($tTy × Bytes)
      | 0, _ => .error .truncated
      | _ + 1, [] => .error .truncated
      | $fuel:ident + 1, t :: $r0:ident => $ite
      termination_by structural f => f))
    -- list helpers for members used nested
    if listUsed[ti_i]! then
      specDefs := specDefs.push (← `(def $(specListId ti_i) $binders* : List $tTy → Bytes
        | [] => []
        | $tVar :: $tsVar => $(specId ti_i) $tVar ++ $(specListId ti_i) $tsVar
        termination_by structural ts => ts))
      encAuxDefs := encAuxDefs.push (← `(def $(encAuxListId ti_i) $binders* : List $tTy → Bytes → Bytes
        | [], $accId => $accId
        | $tVar :: $tsVar, $accId => $(encAuxId ti_i) $tVar ($(encAuxListId ti_i) $tsVar $accId)
        termination_by structural ts => ts))
      linkThms := linkThms.push (← `(theorem $(nm ti_i `codecEncAuxList_spec) $binders* :
          ∀ (ts : List $tTy) (acc : Bytes), $(encAuxListId ti_i) ts acc = $(specListId ti_i) ts ++ acc
        | [], $accId => by simp [$(encAuxListId ti_i):ident, $(specListId ti_i):ident]
        | $tVar :: $tsVar, $accId => by
          simp [$(encAuxListId ti_i):ident, $(specListId ti_i):ident, List.append_assoc,
            ($(nm ti_i `codecEncAux_spec) $tVar), ($(nm ti_i `codecEncAuxList_spec) $tsVar)]
        termination_by structural ts => ts))
      bytesThms := bytesThms.push (← `(theorem $(nm ti_i `codecEncSpecList_bytes) $binders* :
          ∀ (ts : List $tTy), allBytes ($(specListId ti_i) ts) = true
        | [] => by simp [$(specListId ti_i):ident, allBytes]
        | $tVar :: $tsVar => by
          simp [$(specListId ti_i):ident, allBytes_append, ($(nm ti_i `codecEncSpec_bytes) $tVar),
            ($(nm ti_i `codecEncSpecList_bytes) $tsVar)]
        termination_by structural ts => ts))
  let mutualOf (cmds : Array (TSyntax `command)) : CommandElabM (TSyntax `command) :=
    `(set_option linter.unusedSimpArgs false in mutual $cmds* end)
  elabCommand (← mutualOf specDefs)
  elabCommand (← mutualOf encAuxDefs)
  -- spec list = encodeElems spec (needed by the generic list lemma)
  for i in [0:k] do
    if listUsed[i]! then
      let tTy ← tyOf i
      elabCommand (← `(set_option linter.unusedSimpArgs false in
        theorem $(nm i `codecEncSpecList_eq) $binders* :
            ∀ (ts : List $tTy), $(specListId i) ts = encodeElems $(specId i) ts
          | [] => by simp [$(specListId i):ident, encodeElems]
          | $tVar :: $tsVar => by simp [$(specListId i):ident, encodeElems, ($(nm i `codecEncSpecList_eq) $tsVar)]))
  elabCommand (← mutualOf linkThms)
  for i in [0:k] do
    let tTy ← tyOf i
    elabCommand (← `(def $(nm i `codecEnc) $binders* (x : $tTy) : Bytes := $(encAuxId i) x []))
    elabCommand (← `(theorem $(nm i `codecEnc_spec) $binders* (x : $tTy) : $(nm i `codecEnc) x = $(specId i) x := by
        simp [$(nm i `codecEnc):ident, $(nm i `codecEncAux_spec):ident]))
  elabCommand (← mutualOf auxDefs)
  for i in [0:k] do
    let tTy ← tyOf i
    elabCommand (← `(def $(nm i `codecDec) $binders* (bs : Bytes) : Except Err ($tTy × Bytes) := $(auxId i) bs.length bs))
  -- round trip for the whole block, by induction on the fuel
  let stmtOf (i : Nat) (fuelT : Term) : CommandElabM Term := do
    let tTy ← tyOf i
    `(∀ (x : $tTy) (rest : Bytes), ($(specId i) x).length ≤ $fuelT → $(auxId i) $fuelT ($(specId i) x ++ rest) = .ok (x, rest))
  let fuelT ← `(fuel)
  let mut conj : Term ← stmtOf (k - 1) fuelT
  for i in (List.range (k - 1)).reverse do conj ← `($(← stmtOf i fuelT) ∧ $conj)
  -- the induction hypothesis is a conjunction; refer to its projections directly
  let ihProj (i : Nat) : CommandElabM Term := do
    let mut t : Term ← `(ih)
    if k > 1 then
      for _ in [0:i] do t ← `(($t).2)
      if i < k - 1 then t ← `(($t).1)
    pure t
  let ihTerms : Array Term ← (Array.range k).mapM ihProj
  let listEqs : Array Term ← (Array.range k).filter (listUsed[·]!) |>.mapM fun i => `($(nm i `codecEncSpecList_eq):ident)
  let listFuels : Array Term ← (Array.range k).filter (listUsed[·]!) |>.mapM fun i => do
    `(decodeList_fuel _ _ $fuel $(← ihProj i))
  let allSpec : Array Term ← (Array.range k).mapM fun m => `($(specId m))
  let allAux : Array Term ← (Array.range k).mapM fun m => `($(auxId m))
  let hSA ← toSimpArgs (allSpec ++ listEqs)
  let succSA ← toSimpArgs (allSpec ++ allAux ++ #[← `(List.append_assoc)] ++ ihTerms ++ listEqs ++ listFuels)
  let zeroSA ← toSimpArgs (allSpec ++ #[← `(List.length_cons)])
  let blockKey := nm 0 `codecDecAux_enc_block
  let holes : Array Term ← (Array.range k).mapM fun _ => `(?_)
  let introSplit : TSyntax `tactic ← if k == 1 then `(tactic| skip) else
      `(tactic| refine ⟨$holes,*⟩)
  elabCommand (← `(set_option linter.unusedSimpArgs false in
    theorem $blockKey $binders* : ∀ (fuel : Nat), $conj := by
      intro fuel
      induction fuel with
      | zero =>
        $introSplit:tactic <;> intro x rest h <;>
        -- every encoding starts with its tag byte, so length = _ + 1 > 0 (closed without
        -- simp/omega on the false hypothesis, which would pull in Classical.choice)
        cases x <;> (simp only [$zeroSA,*] at h; exact absurd h (Nat.not_succ_le_zero _))
      | succ $fuel:ident ih =>
        $introSplit:tactic <;> intro x rest h <;> cases x <;> simp [$hSA,*] at h <;>
          simp (disch := omega) [$succSA,*]))
  elabCommand (← mutualOf bytesThms)
  -- per-type projections and instances
  for i in [0:k] do
    let tTy ← tyOf i
    let mut proj : Term ← `($blockKey fuel)
    if k > 1 then
      for _ in [0:i] do proj ← `(($proj).2)
      if i < k - 1 then proj ← `(($proj).1)
    elabCommand (← `(theorem $(nm i `codecDecAux_enc) $binders* : ∀ (fuel : Nat), $(← stmtOf i fuelT) :=
        fun fuel => $proj))
    elabCommand (← `(instance $(nm i `instCodec):ident $binders* : Codec $tTy where
        enc := $(nm i `codecEnc)
        dec := $(nm i `codecDec)
        dec_enc := by
          intro x rest
          rw [$(nm i `codecEnc_spec):ident]
          exact $(nm i `codecDecAux_enc) _ x rest (by simp)
        enc_bytes := by
          intro x
          rw [$(nm i `codecEnc_spec):ident]
          exact $(nm i `codecEncSpec_bytes) x))

/-- Groups the requested names into mutual blocks; each block must be derived as a whole.
Generated declarations are elaborated at the root namespace (field types are printed with
full names), so `deriving instance Codec for T` inside another namespace still defines
`T.codecEnc`, ... rather than `Current.Namespace.T.codecEnc`. -/
def deriveCodec (declNames : Array Name) : CommandElabM Bool := do
  let env ← getEnv
  let mut done : Array Name := #[]
  for n in declNames do
    if done.contains n then continue
    let some (.inductInfo ind) := env.find? n | throwError "Codec deriving: {n} is not an inductive type"
    let block := ind.all.toArray
    for m in block do
      unless declNames.contains m do
        throwError "Codec deriving: {n} is in a mutual block with {m}; derive them together (`deriving instance Codec for {block.toList}`)"
    withScope (fun sc => { sc with currNamespace := Name.anonymous }) (mkCodecBlock block)
    done := done ++ block
  return true

initialize registerDerivingHandler ``Codec deriveCodec

end Spike.Wire.Derive
