import Lean
import Spike.Codec

/-!
# `#gen_ocaml`: OCaml client types and codecs from Lean types

```
#gen_ocaml "path/to/out.ml" [T1, T2, ...] call Req => (Except E Resp) via Leancore.call_api
```

Writes one OCaml module with
* a type per Lean type (structure → record, other inductive → variant), mutually recursive;
* `enc_t : Buffer.t -> t -> unit` and `dec_t : Wire_rt.cursor -> t` per type, following
  exactly the layout `deriving Codec` produces (fields in order, tag byte iff > 1 constructor);
* `encode_t : t -> bytes` and `decode_t : bytes -> (t, int) result`;
* optionally `call : req -> (resp, e) result`, sending the request through the given
  `bytes -> bytes` function and decoding the reply (a reply that does not decode raises
  `Leancore.Contract_violation`; the Lean side proves this cannot happen unless the trusted
  base is broken).

Field types: `Nat` (Z.t), `Bool`, `List α`, `Except ε α` (result), and the listed types.
The generated OCaml is not verified; it is checked differentially against the Lean codecs.
-/

namespace Spike.Wire.GenOCaml
open Lean Elab Command Meta

def ocamlKeywords : List String :=
  ["and","as","assert","begin","class","constraint","do","done","downto","else","end","exception",
   "external","false","for","fun","function","functor","if","in","include","inherit","initializer",
   "lazy","let","match","method","module","mutable","new","object","of","open","or","private","rec",
   "sig","struct","then","to","true","try","type","val","virtual","when","while","with"]

/-- camelCase → snake_case, lowercased, keyword-safe. -/
def snake (s : String) : String :=
  let out := s.foldl (fun (acc : String) c =>
    if c.isUpper then (if acc.isEmpty then acc else acc.push '_').push c.toLower else acc.push c) ""
  if ocamlKeywords.contains out then out ++ "_" else out

def typeName (n : Name) : String := snake n.getString!

/-- OCaml constructor name. `clashes` lists Lean constructor short names used by more than one
generated type; those get the type as prefix (`Request_gate1`) so OCaml never silently picks
the wrong type. -/
def ctorName (clashes : List String) (n : Name) : String :=
  let short := n.getString!
  if clashes.contains short then n.getPrefix.getString!.capitalize ++ "_" ++ short
  else short.capitalize

structure FieldRepr where
  ty : String    -- OCaml type
  enc : String   -- Buffer.t -> 'a -> unit
  dec : String   -- cursor -> 'a

partial def fieldRepr (known : List Name) (e : Expr) : MetaM FieldRepr := do
  let e ← instantiateMVars e
  match e with
  | .const ``Nat _ => pure ⟨"Z.t", "Wire_rt.enc_nat", "Wire_rt.dec_nat"⟩
  | .const ``Bool _ => pure ⟨"bool", "Wire_rt.enc_bool", "Wire_rt.dec_bool"⟩
  | .app (.const ``List _) a => do
    let r ← fieldRepr known a
    pure ⟨s!"({r.ty}) list", s!"(Wire_rt.enc_list {r.enc})", s!"(Wire_rt.dec_list {r.dec})"⟩
  | .app (.app (.const ``Except _) ε) a => do
    let re ← fieldRepr known ε; let ra ← fieldRepr known a
    pure ⟨s!"({ra.ty}, {re.ty}) result", s!"(Wire_rt.enc_except {ra.enc} {re.enc})",
          s!"(Wire_rt.dec_except {ra.dec} {re.dec})"⟩
  | .const n _ =>
    if known.contains n then pure ⟨typeName n, s!"enc_{typeName n}", s!"dec_{typeName n}"⟩
    else throwError "#gen_ocaml: type {n} is not in the generated set"
  | _ => throwError "#gen_ocaml: unsupported field type {e}"

/-- (type decl, encoder, decoder) for one Lean type. -/
def genType (known : List Name) (clashes : List String) (n : Name) : MetaM (String × String × String) := do
  let env ← getEnv
  let some (.inductInfo ind) := env.find? n | throwError "#gen_ocaml: {n} is not an inductive"
  let tn := typeName n
  let tagged := ind.ctors.length != 1
  let ctors ← ind.ctors.mapM fun c => do
    let .ctorInfo ci := env.find? c |>.get! | unreachable!
    forallTelescopeReducing ci.type fun xs _ => do
      let fs := xs.extract ci.numParams xs.size
      let reprs ← fs.mapM fun f => do fieldRepr known (← inferType f)
      pure (c, reprs)
  if isStructure env n then
    let fields := (getStructureFields env n).map (snake ·.getString!)
    let (_, reprs) := ctors[0]!
    let ty := s!"{tn} = \{ " ++ "; ".intercalate ((fields.zip reprs).toList.map fun (f, r) => s!"{f} : {r.ty}") ++ " }"
    let encBody := if fields.isEmpty then "()" else
      "; ".intercalate ((fields.zip reprs).toList.map fun (f, r) => s!"{r.enc} b x.{f}")
    let enc := s!"enc_{tn} (b : Buffer.t) (x : {tn}) : unit = {encBody}"
    -- locals are prefixed so a Lean field named `c`/`b`/`x` cannot capture the cursor/buffer
    let lets := String.join ((fields.zip reprs).toList.map fun (f, r) => s!"let f_{f} = {r.dec} c in ")
    let dec := s!"dec_{tn} (c : Wire_rt.cursor) : {tn} = {lets}(\{ " ++ "; ".intercalate (fields.toList.map fun f => s!"{f} = f_{f}") ++ s!" } : {tn})"
    return (ty, enc, dec)
  else
    let alts := ctors.map fun (c, reprs) =>
      if reprs.isEmpty then ctorName clashes c
      else s!"{ctorName clashes c} of " ++ " * ".intercalate (reprs.toList.map (·.ty))
    let ty := s!"{tn} =\n  | " ++ "\n  | ".intercalate alts
    let encAlts := (ctors.zipIdx).map fun ((c, reprs), i) =>
      let vars := (List.range reprs.size).map (s!"x{·}")
      let pat := if reprs.isEmpty then ctorName clashes c else s!"{ctorName clashes c} (" ++ ", ".intercalate vars ++ ")"
      let tagS := if tagged then [s!"Wire_rt.tag b {i}"] else []
      let encs := (reprs.toList.zip vars).map fun (r, v) => s!"{r.enc} b {v}"
      let body := "; ".intercalate (tagS ++ encs)
      s!"    | {pat} -> {if body.isEmpty then "()" else body}"
    let enc := s!"enc_{tn} (b : Buffer.t) (x : {tn}) : unit =\n  match x with\n" ++ "\n".intercalate encAlts
    let mkVal (c : Name) (reprs : Array FieldRepr) : String :=
      let vars := (List.range reprs.size).map (s!"x{·}")
      let lets := String.join ((reprs.toList.zip vars).map fun (r, v) => s!"let {v} = {r.dec} c in ")
      if reprs.isEmpty then ctorName clashes c else lets ++ s!"{ctorName clashes c} (" ++ ", ".intercalate vars ++ ")"
    let dec := if tagged then
        let alts := (ctors.zipIdx).map fun ((c, reprs), i) => s!"    | {i} -> {mkVal c reprs}"
        s!"dec_{tn} (c : Wire_rt.cursor) : {tn} =\n  match Wire_rt.byte c with\n" ++ "\n".intercalate alts
          ++ "\n    | _ -> raise (Wire_rt.Decode_error Wire_rt.bad_tag)"
      else s!"dec_{tn} (c : Wire_rt.cursor) : {tn} = {mkVal ctors[0]!.1 ctors[0]!.2}"
    return (ty, enc, dec)

syntax (name := genOCaml) "#gen_ocaml " str " [" ident,* "]"
  (" call " term " => " term " via " ident)? : command

@[command_elab genOCaml] def elabGenOCaml : CommandElab
  | `(#gen_ocaml $path:str [$ids,*] $[call $req => $resp via $fn]?) => do
    let names ← ids.getElems.mapM fun id => liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let known := names.toList
    let env ← getEnv
    let ctorShorts := names.toList.flatMap fun n =>
      match env.find? n with
      | some (.inductInfo ind) => if isStructure env n then [] else ind.ctors.map (·.getString!)
      | _ => []
    let clashes := ctorShorts.filter fun c => (ctorShorts.filter (· == c)).length > 1
    let parts : Array (String × String × String) ← liftTermElabM <| names.mapM fun n => (genType known clashes n : MetaM _)
    let tys := parts.toList.map (·.1)
    let encs := parts.toList.map (·.2.1)
    let decs := parts.toList.map (·.2.2)
    let helpers := names.toList.map fun n =>
      let t := typeName n
      s!"let encode_{t} (x : {t}) : bytes = Wire_rt.to_bytes enc_{t} x\nlet decode_{t} (bs : bytes) : ({t}, int) result = Wire_rt.decode dec_{t} bs"
    let callPart ← match req, resp, fn with
      | some req, some resp, some fn => liftTermElabM do
        let reqTy ← Term.elabType req
        let respTy ← Term.elabType resp
        let rq ← fieldRepr known reqTy
        let rs ← fieldRepr known respTy
        pure s!"\n(** Decode a raw reply from the core (Error = wire error code). *)\nlet decode_reply (bs : bytes) : ({rs.ty}, int) result = Wire_rt.decode {rs.dec} bs\n\n(** Typed call into the extracted Lean core. *)\nlet call (r : {rq.ty}) : {rs.ty} =\n  match decode_reply ({fn.getId} (Wire_rt.to_bytes {rq.enc} r)) with\n  | Ok v -> v\n  | Error code -> raise (Leancore.Contract_violation (Printf.sprintf \"undecodable reply (code %d)\" code))\n"
      | _, _, _ => pure ""
    let src := "(* GENERATED by #gen_ocaml (domain/Spike/Codec/OCaml.lean) from the Lean types. DO NOT EDIT.\n   Wire format v2: the layout of `deriving Codec`. *)\n\n"
      ++ "type " ++ "\n\nand ".intercalate tys ++ "\n\n"
      ++ "let rec " ++ "\n\nand ".intercalate encs ++ "\n\n"
      ++ "let rec " ++ "\n\nand ".intercalate decs ++ "\n\n"
      ++ "\n".intercalate helpers ++ "\n" ++ callPart
    IO.FS.writeFile path.getString src
    logInfo m!"#gen_ocaml: wrote {path.getString} ({names.size} types)"
  | _ => throwUnsupportedSyntax

end Spike.Wire.GenOCaml
