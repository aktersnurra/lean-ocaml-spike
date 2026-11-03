import LeanToLambdaBox
import Spike.Gate1
import Spike.Order
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
open Spike.Wire Spike.Order

deriving instance Codec for Err, OrderErr, Line, Order, Quote

inductive Request where
  | gate1 (n : Nat)
  | priceOrder (o : Order)
  | echo (o : Order)        -- returns its argument; used to test the generated codecs
deriving Codec

inductive Response where
  | gate1 (n : Nat)
  | quote (q : Quote)
  | echoed (o : Order)
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

/-- Decode, serve, encode. Total. -/
def respond (req : Bytes) : Except ApiError Response :=
  if allBytes req then
    match (Codec.decodeExact req : Except Err Request) with
    | .error e => .error (.transport e)
    | .ok r => serve r
  else .error (.transport .notBytes)

/-- The extracted entry point. -/
def handle (req : Bytes) : Bytes := Codec.enc (respond req)

/-! ## End-to-end theorems (from the derived codecs' proofs) -/

/-- Every reply is a byte string. -/
theorem allBytes_handle (req : Bytes) : allBytes (handle req) = true := Codec.enc_bytes _

/-- An encoded request is answered with the encoded result of `serve`. -/
theorem handle_enc (r : Request) : handle (Codec.enc r) = Codec.enc (serve r) := by
  simp [handle, respond, Codec.decodeExact_enc]

/-- The client can always decode the reply, and gets exactly `serve r`. -/
theorem decode_handle_enc (r : Request) :
    Codec.decodeExact (handle (Codec.enc r)) = .ok (serve r) := by
  rw [handle_enc, Codec.decodeExact_enc]

end Spike.Api

#erase Spike.Api.handle config {remove_irrel_constr_args := true} to "build/api.ast" mli "build/api.mli"

open Spike.Wire Spike.Order Spike.Api in
#gen_ocaml "../ocaml/api/spike_api.ml" [Err, OrderErr, Line, Order, Quote, Request, Response, ApiError]
  call Request => (Except ApiError Response) via Leancore.call_api
