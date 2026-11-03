import Spike

/-! Proof-axiom audit. `scripts/audit.sh` checks that every line printed here names only
axioms from the allowed set {propext, Quot.sound} (or none). -/

#print axioms Spike.gate1_odd
#print axioms Spike.Wire.decodeNat_encodeNat
#print axioms Spike.Wire.decodeList_encodeList
#print axioms Spike.Order.priceOrder_ok
#print axioms Spike.Order.exact_decodeOrder_encodeOrder
#print axioms Spike.Order.exact_decodeQuote_encodeQuote
#print axioms Spike.Wire.allBytes_handle
#print axioms Spike.Wire.handle_priceOrder
-- The extracted definitions themselves:
#print axioms Spike.gate1
#print axioms Spike.Wire.handle
-- Wire format v2 (generated codecs):
#print axioms Spike.Wire.Codec.decodeExact_enc
#print axioms Spike.Api.Request.instCodec
#print axioms Spike.Order.Order.instCodec
#print axioms Spike.Formula.Formula.instCodec
#print axioms Spike.Formula.Formula.codecDecAux_enc
#print axioms Spike.Formula.Formula.eval_mono
#print axioms Spike.Api.allBytes_handle
#print axioms Spike.Api.handle_enc
#print axioms Spike.Api.decode_handle_enc
#print axioms Spike.Api.handle
#print axioms Spike.Bundle.Bundle.instCodec
#print axioms Spike.Bundle.Bundle.codecDecAux_enc
#print axioms Spike.Bundle.Bundle.price_le_gross
