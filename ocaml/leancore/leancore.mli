(** Raised if the extracted code breaks the contract of its Lean type
    (for example, a non-byte element in a response). It signals a bug in the trusted base,
    not bad input: bad input is answered with an error response from [call]. *)
exception Contract_violation of string

(** [gate1 n = 2n + 1] for [n >= 0]; raises [Invalid_argument] for negative [n]. *)
val gate1 : Z.t -> Z.t

(** Opaque byte boundary to the Lean core ([Spike.Wire.handle]). Total: every input
    gets a response. Response byte 0 is [0x00] (ok, payload follows) or [0x01]
    (error, one code byte follows). The wire format is defined only in Lean. *)
val call : bytes -> bytes
