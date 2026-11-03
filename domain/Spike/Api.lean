import LeanToLambdaBox
import Spike.Gate1
import Spike.Order
import Spike.Formula
import Spike.Bundle
import Spike.Codec.Derive
import Spike.Codec.OCaml

/-!
# The API, defined once in Lean (wire format v2, generated)

The request, response and error types below are the single source of truth for the
boundary. From them:
* `deriving Codec` generates the Lean codecs together with their round-trip proofs;
* `handle` (extracted as OCaml module `Api`) decodes a request, runs the pure core, and
  encodes `Except ApiError Response`;
* `#gen_ocaml` writes the OCaml client (`ocaml/api/spike_api.ml`): the same types as OCaml
  records/variants, codecs with the same layout, and a typed `call`.
-/

namespace Spike.Api
open Spike.Wire Spike.Order Spike.Formula Spike.Bundle

deriving instance Codec for Err, OrderErr, Line, Order, Quote, Formula, Bundle, Category

inductive Request where
  | gate1 (n : Nat)
  | priceOrder (o : Order)
  | echo (o : Order)        -- returns its argument; used to test the generated codecs
  | evalFormula (f : Formula) (v : Nat)
  | echoFormula (f : Formula)
  | priceBundle (b : Bundle)
  | echoBundle (b : Bundle)
  | echoCategory (c : Category)
deriving Codec

inductive Response where
  | gate1 (n : Nat)
  | quote (q : Quote)
  | echoed (o : Order)
  | value (n : Nat)
  | formula (f : Formula)
  | bundle (b : Bundle)
  | category (c : Category)
deriving Codec

inductive ApiError where
  | transport (e : Err)     -- malformed request
  | order (e : OrderErr)    -- domain rejection
deriving Codec

/-- The pure service. -/
def serve : Request → Except ApiError Response
  | .gate1 n => .ok (.gate1 (Spike.gate1 n))
  | .priceOrder o =>
    match priceOrder o with
    | .ok q => .ok (.quote q)
    | .error e => .error (.order e)
  | .echo o => .ok (.echoed o)
  | .evalFormula f v => .ok (.value (f.eval v))
  | .echoFormula f => .ok (.formula f)
  | .priceBundle b => .ok (.value b.price)
  | .echoBundle b => .ok (.bundle b)
  | .echoCategory c => .ok (.category c)

/-- Request size limit. Recursive request types (`Formula`) are decoded and evaluated by
non-tail recursion whose depth can reach the request length (one tag byte per level). With
OCaml 4.14's 8 MB system stack the extracted core overflows somewhere between 200k and 300k
levels (and the generated OCaml client decoder around 200k); on OCaml 5 the stack grows,
but deep requests become slow (22 s at 3M levels). 64 KiB keeps the depth at least 3x below
the 4.14 limit. It is a policy constant: raise it only together with a depth budget. -/
def maxRequestBytes : Nat := 65536

/-- Decode, serve, encode. Total. -/
def respond (req : Bytes) : Except ApiError Response :=
  if req.length > maxRequestBytes then .error (.transport .tooLarge)
  else if allBytes req then
    match (Codec.decodeExact req : Except Err Request) with
    | .error e => .error (.transport e)
    | .ok r => serve r
  else .error (.transport .notBytes)

/-- The extracted entry point. -/
def handle (req : Bytes) : Bytes := Codec.enc (respond req)

/-! ## End-to-end theorems (from the derived codecs' proofs) -/

/-- Every reply is a byte string. -/
theorem allBytes_handle (req : Bytes) : allBytes (handle req) = true := Codec.enc_bytes _

/-- An encoded request within the size limit is answered with the encoded result of `serve`. -/
theorem handle_enc (r : Request) (h : (Codec.enc r).length ≤ maxRequestBytes) :
    handle (Codec.enc r) = Codec.enc (serve r) := by
  have h' : ¬ (Codec.enc r).length > maxRequestBytes := Nat.not_lt.mpr h
  simp [handle, respond, h', Codec.decodeExact_enc]

/-- The client can always decode the reply, and gets exactly `serve r`. -/
theorem decode_handle_enc (r : Request) (h : (Codec.enc r).length ≤ maxRequestBytes) :
    Codec.decodeExact (handle (Codec.enc r)) = .ok (serve r) := by
  rw [handle_enc r h, Codec.decodeExact_enc]

/-- Oversized requests get a typed error, never a crash. -/
theorem respond_tooLarge (req : Bytes) (h : req.length > maxRequestBytes) :
    respond req = .error (.transport .tooLarge) := by
  simp [respond, h]

end Spike.Api

#erase Spike.Api.handle config {remove_irrel_constr_args := true} to "build/api.ast" mli "build/api.mli"

open Spike.Wire Spike.Order Spike.Formula Spike.Bundle Spike.Api in
#gen_ocaml "../ocaml/api/spike_api.ml" [Err, OrderErr, Line, Order, Quote, Formula, Bundle, Category, Request, Response, ApiError]
  call Request => (Except ApiError Response) via Leancore.call_api
