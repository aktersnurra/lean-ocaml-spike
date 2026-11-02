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
