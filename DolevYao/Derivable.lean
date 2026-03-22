/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DolevYao.Terms
import Mathlib.Data.Finset.Basic

/-!
# Attacker Knowledge — The Derivable Relation

The Dolev-Yao attacker can intercept all messages on the network and
construct new messages using pairing, projection, encryption, and
decryption. This is formalized as an inductive relation `Derivable S t`,
read: "the attacker can derive term `t` from knowledge set `S`."

This combines Paulson's `analz` (decomposition) and `synth` (construction)
into a single relation for simplicity. His Isabelle formalization splits
them to get stronger inversion principles; we avoid the split by using a
semantic invariant (`guarded`) instead.

## Main results

* `DolevYao.Derivable` — the attacker capability relation
* `DolevYao.guarded` — a semantic invariant for secrecy proofs
* `DolevYao.guarded_of_derivable` — derivability preserves the `guarded`
  invariant

## Proof technique

The secrecy proof uses a "model" argument: define a predicate (`guarded`)
that holds on the initial knowledge, is preserved by every derivation rule,
and fails on the secret. This is analogous to showing a set is closed under
the attacker's operations — the approach Paulson uses with `analz` and
`synth`, but packaged as a single invariant over our combined relation.
-/

namespace DolevYao

open Term

/-! ### The derivation relation -/

/-- The Dolev-Yao attacker's derivation relation. `Derivable S t` holds when
the attacker can construct `t` from the set of known terms `S`.

The rules model a standard network attacker (Dolev & Yao, 1983):

- `ax`: the attacker knows everything in the initial set
- `fst`/`snd`: projection from pairs
- `pair`: pairing known terms
- `enc`: encryption with a known key
- `dec`: decryption with a known key -/
inductive Derivable : Finset Term → Term → Prop where
  | ax   {S t}     : t ∈ S → Derivable S t
  | fst  {S t₁ t₂} : Derivable S (.pair t₁ t₂) → Derivable S t₁
  | snd  {S t₁ t₂} : Derivable S (.pair t₁ t₂) → Derivable S t₂
  | pair {S t₁ t₂} : Derivable S t₁ → Derivable S t₂ → Derivable S (.pair t₁ t₂)
  | enc  {S m k}   : Derivable S m → Derivable S k → Derivable S (.enc m k)
  | dec  {S m k}   : Derivable S (.enc m k) → Derivable S k → Derivable S m

/-! ### The guarded invariant -/

/-- A term is `guarded secret key` when every occurrence of `secret` and `key`
in `t` sits inside an encryption layer whose key is `key`.

Concretely:
- An atom is guarded iff it is neither the secret nor the key.
- A pair is guarded iff both components are.
- An encryption `enc m k` is guarded if `k` is the protected key (the
  contents are then inaccessible), or if both `m` and `k` are guarded.

This is the heart of the secrecy proof: the attacker cannot break through
an encryption whose key it does not possess. -/
def guarded (secret key : Term) : Term → Prop
  | .atom s  => .atom s ≠ secret ∧ .atom s ≠ key
  | .pair t₁ t₂ => guarded secret key t₁ ∧ guarded secret key t₂
  | .enc m k => k = key ∨ (guarded secret key m ∧ guarded secret key k)

/-- **Invariant preservation.** If every term in `S` is guarded, then every
term derivable from `S` is also guarded.

The proof is by induction on the derivation. The critical case is `dec`:
decrypting `enc m k` requires the attacker to possess `k`. If `k` is the
protected key, then `k` itself must be guarded — but `guarded secret key key`
requires `key ≠ key`, which is absurd. So decryption under the protected key
is impossible, and the contents remain sealed. -/
theorem guarded_of_derivable {secret key : Term} {S : Finset Term} {t : Term}
    (hkey : ¬ guarded secret key key)
    (hd : Derivable S t) (hs : ∀ s ∈ S, guarded secret key s) :
    guarded secret key t := by
  induction hd with
  | ax hmem => exact hs _ hmem
  | fst _ ih => exact ih.1
  | snd _ ih => exact ih.2
  | pair _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | enc _ _ ih₁ ih₂ => exact Or.inr ⟨ih₁, ih₂⟩
  | dec _ _ ih₁ ih₂ =>
    rcases ih₁ with rfl | ⟨hm, _⟩
    · exact absurd ih₂ hkey
    · exact hm

end DolevYao
