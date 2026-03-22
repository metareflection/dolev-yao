/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Symbolic Terms for the Dolev-Yao Model

The term algebra for symbolic cryptographic messages: atoms (names, nonces),
pairs, and symmetric encryption. This is the standard "free algebra" from
Dolev & Yao (1983), restricted to the symmetric-key fragment.

## Main definitions

* `DolevYao.Term` — the inductive type of symbolic messages
-/

namespace DolevYao

/-- Symbolic terms in the Dolev-Yao message algebra.

- `atom s` represents an atomic value: an agent name, nonce, or key.
- `pair t₁ t₂` represents concatenation of two messages.
- `enc m k` represents symmetric encryption of `m` under key `k`. -/
inductive Term where
  | atom : String → Term
  | pair : Term → Term → Term
  | enc : Term → Term → Term
  deriving DecidableEq, Repr

end DolevYao
