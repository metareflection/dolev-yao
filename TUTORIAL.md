# Formalizing a Dolev-Yao Secrecy Proof in Lean 4

This tutorial walks through a machine-checked proof that a Dolev-Yao
attacker cannot extract a nonce from encrypted protocol messages without
the key. The formalization builds on Mathlib and compiles against Lean 4 /
Mathlib4.

## Background

The **Dolev-Yao model** (1983) treats cryptographic primitives as symbolic
term constructors — no probability, no computational hardness, just algebra.
An attacker controls the network: it can intercept every message, decompose
pairs, encrypt and decrypt with known keys, and assemble new messages from
the pieces. The one thing it *cannot* do is break encryption without the
key.

This "perfect cryptography" abstraction is the foundation of most
automated protocol verification tools (ProVerif, Tamarin, CPSA). Proving
a security property in the Dolev-Yao model means showing that the
protocol's structure alone — not the strength of any particular cipher —
prevents the attack.

### Why formalize this?

Dolev-Yao proofs are deceptively tricky. The attacker can combine
analysis (decomposition) and synthesis (construction) in arbitrary ways:
build a new term, decompose part of it, use the result to decrypt something
else. Getting the induction right — especially for secrecy — requires
careful invariant design. A machine-checked proof eliminates the risk of
a missed case.

Our formalization is deliberately minimal: three constructors, six
attacker rules, one protocol, one theorem. The goal is a clean reference
for the proof technique, not a general-purpose framework.

## Project structure

```
DolevYao/
  Terms.lean       -- Symbolic term algebra (atoms, pairs, encryption)
  Derivable.lean   -- Attacker derivation relation, guarded invariant
  Protocol.lean    -- Protocol instantiation, nonce secrecy theorem
DolevYao.lean      -- Root (imports all three)
```

The split follows the standard layering in protocol verification: separate
the *term algebra* (syntax) from the *attacker model* (what can be derived)
from the *protocol analysis* (what a specific protocol leaks). Each layer
depends only on the one below.

## Part 1: Symbolic terms

### The term type

The message algebra has three constructors:

```lean
inductive Term where
  | atom : String → Term
  | pair : Term → Term → Term
  | enc : Term → Term → Term
  deriving DecidableEq, Repr
```

Design choices:

1. **Atoms are strings.** Agent names (`"Alice"`), nonces (`"nA"`), and
   keys (`"kAB"`) are all atoms — the type system doesn't distinguish
   them. This mirrors the Dolev-Yao tradition: the attacker treats all
   atomic values uniformly. A richer formalization might use a sum type
   `Name | Nonce | Key`, but the extra structure buys nothing for our
   secrecy proof.

2. **No public-key encryption, no hashing, no signatures.** Just the
   symmetric-key fragment. This is the smallest algebra that demonstrates
   the proof technique. Extending to asymmetric primitives would add
   constructors (`aenc`, `sign`, `pk`, `sk`) and corresponding attacker
   rules, but the invariant method scales.

3. **`DecidableEq` is derived.** We need decidable equality for `Finset`
   membership (the attacker's knowledge set is a `Finset Term`). Lean 4's
   `deriving` clause generates this automatically from the inductive
   structure and `String`'s `DecidableEq`.

## Part 2: The attacker — derivation and the guarded invariant

### The derivation relation

```lean
inductive Derivable : Finset Term → Term → Prop where
  | ax   {S t}     : t ∈ S → Derivable S t
  | fst  {S t₁ t₂} : Derivable S (.pair t₁ t₂) → Derivable S t₁
  | snd  {S t₁ t₂} : Derivable S (.pair t₁ t₂) → Derivable S t₂
  | pair {S t₁ t₂} : Derivable S t₁ → Derivable S t₂ → Derivable S (.pair t₁ t₂)
  | enc  {S m k}   : Derivable S m → Derivable S k → Derivable S (.enc m k)
  | dec  {S m k}   : Derivable S (.enc m k) → Derivable S k → Derivable S m
```

Six rules in three pairs:

| Analysis (decomposition) | Synthesis (construction) |
|---|---|
| `fst`: extract left of pair | `pair`: build a pair |
| `snd`: extract right of pair | `enc`: encrypt with known key |
| `dec`: decrypt with known key | `ax`: use initial knowledge |

This combines what Paulson's Isabelle formalization splits into two
separate sets: `analz` (analysis closure — what the attacker can learn by
decomposing messages) and `synth` (synthesis closure — what it can build).
Paulson's split gives stronger inversion principles for free, since `analz`
only decomposes and `synth` only builds. We combine them into one relation
and compensate with a semantic invariant.

**Why combine?** Simplicity. With a single relation, the secrecy proof is
one induction, not a two-phase argument about `analz` and `synth`
separately. The cost is that direct inversion on `Derivable` is too weak
(the `fst`/`snd`/`dec` cases produce `Derivable` premises that may
themselves involve synthesis). The `guarded` invariant solves this.

### The guarded invariant

The key insight: we don't need to characterize *everything* the attacker
can derive. We just need to show a property that (a) holds on the initial
messages, (b) is preserved by all six rules, and (c) fails on the secret.

```lean
def guarded (secret key : Term) : Term → Prop
  | .atom s     => .atom s ≠ secret ∧ .atom s ≠ key
  | .pair t₁ t₂ => guarded secret key t₁ ∧ guarded secret key t₂
  | .enc m k    => k = key ∨ (guarded secret key m ∧ guarded secret key k)
```

Read `guarded secret key t` as: "the terms `secret` and `key` do not
appear *exposed* in `t` — every occurrence is sealed inside an `enc _ key`
layer."

Three cases:

- **Atom:** An atom is guarded iff it is neither the secret nor the key.
  This is the "base case" — exposed occurrences of `secret` or `key`
  violate the invariant.

- **Pair:** A pair is guarded iff both components are. Pairs don't hide
  anything — the attacker can always project.

- **Encryption:** `enc m k` is guarded if either (a) `k` is the protected
  key (the contents are sealed, so it doesn't matter what's inside), or
  (b) both the plaintext and the key are themselves guarded. Case (a) is
  what makes the invariant work: encrypted terms under the right key are
  *unconditionally* guarded, even if they contain the secret inside.

### Why include `key` in the invariant?

A first attempt might define `guarded` to track only the `secret`, not the
`key`. But that breaks the `dec` case: if the attacker could derive the key
itself, it could decrypt everything and extract the secret. By requiring
that the *key* is also unexposed, we get a self-reinforcing invariant: the
key can't be derived because it's not guarded against itself
(`key ≠ key` fails), and without the key, encrypted contents stay sealed.

### Invariant preservation

```lean
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
```

The proof is by induction on the derivation, one case per rule. The
hypothesis `hkey : ¬ guarded secret key key` says the key is not guarded —
this is used only in the `dec` case.

**Case `ax`:** The term is in the initial set `S`, so it's guarded by `hs`.

**Cases `fst`/`snd`:** The induction hypothesis gives `guarded` for a pair.
Since `guarded` on a pair is a conjunction, `.1` and `.2` extract the
components. This works because `guarded (.pair t₁ t₂)` *definitionally
reduces* to `guarded t₁ ∧ guarded t₂` in Lean 4 — no `unfold` or `simp`
needed.

**Case `pair`:** Both components are guarded by IH; pair them into a
conjunction.

**Case `enc`:** Both the plaintext and key are guarded by IH. We take the
right disjunct: `Or.inr ⟨ih₁, ih₂⟩`. (We *could* use `Or.inl` if the
encryption key happens to be `key`, but `Or.inr` works unconditionally.)

**Case `dec`:** This is the critical case. We have:

- `ih₁ : guarded secret key (.enc m k')` — the ciphertext is guarded
- `ih₂ : guarded secret key k'` — the decryption key is guarded
- Goal: `guarded secret key m` — the plaintext is guarded

The ciphertext being guarded means `k' = key ∨ (guarded m ∧ guarded k')`.
We case-split with `rcases`:

- If `k' = key`: then `ih₂` becomes `guarded secret key key`, contradicting
  `hkey`. The attacker would need the protected key to decrypt, but the key
  is *not* guarded (it would need `key ≠ key`), so it can't have been
  derived from any guarded set. `absurd ih₂ hkey` closes the goal.

- If `guarded m ∧ guarded k'`: then `hm` gives us `guarded m` directly.

This is the "the attacker can't have it both ways" argument: either the
ciphertext is protected (and you can't get the key), or the plaintext was
already safe (and decrypting reveals nothing new).

## Part 3: The protocol and secrecy theorem

### Protocol constants

```lean
abbrev nA : Term := .atom "nA"
abbrev kAB : Term := .atom "kAB"
abbrev alice : Term := .atom "Alice"

abbrev msg1 : Term := .enc (.pair nA alice) kAB
abbrev msg2 : Term := .enc nA kAB
```

The protocol has two messages:

    Message 1: Alice → Bob:   enc ⟨nA, Alice⟩ kAB
    Message 2: Bob → Alice:   enc nA kAB

Alice generates a fresh nonce `nA`, pairs it with her identity, encrypts
under the shared key `kAB`, and sends. Bob decrypts, extracts the nonce,
and echoes it back encrypted — a minimal challenge-response.

**`abbrev` vs `def`:** The protocol constants use `abbrev` (transparent
definitions) rather than `def` (opaque). This means Lean will unfold them
during elaboration, so `guarded nA kAB msg1` reduces definitionally to
`kAB = kAB ∨ (...)` without needing `simp` or `unfold`. This keeps the
proof terms short.

### The secrecy theorem

```lean
theorem nonce_secret : ¬ Derivable {msg1, msg2} nA := by
  intro hd
  -- Step 1: the key is not guarded (it cannot differ from itself)
  have hkey : ¬ guarded nA kAB kAB := fun h => h.2 rfl
  -- Step 2: both protocol messages are guarded (encrypted under kAB)
  have hs : ∀ s ∈ ({msg1, msg2} : Finset Term), guarded nA kAB s := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl <;> exact Or.inl rfl
  -- Step 3: nA would have to be guarded, but it isn't
  exact (guarded_of_derivable hkey hd hs).1 rfl
```

Three steps:

**Step 1 — the key is not guarded.** `guarded nA kAB kAB` reduces to
`kAB ≠ nA ∧ kAB ≠ kAB`. The second conjunct is `kAB ≠ kAB`, which is
false. So `fun h => h.2 rfl` constructs the negation: given a proof `h`
of `guarded nA kAB kAB`, extract `h.2 : kAB ≠ kAB` and apply it to `rfl`
to get `False`.

**Step 2 — the initial set is guarded.** For each message in `{msg1, msg2}`,
we must show `guarded nA kAB msg`. After `simp` reduces the `Finset`
membership to `s = msg1 ∨ s = msg2`, we handle both cases with
`<;> exact Or.inl rfl`. This works because both `msg1` and `msg2` are
`enc _ kAB` — encryption under `kAB` — and `guarded nA kAB (.enc _ kAB)`
reduces to `kAB = kAB ∨ (...)`, which is `Or.inl rfl`.

**Step 3 — contradiction.** By `guarded_of_derivable`, the hypothetical
derivation `hd : Derivable {msg1, msg2} nA` would imply `guarded nA kAB nA`.
This reduces to `nA ≠ nA ∧ nA ≠ kAB`. Applying `.1` gives `nA ≠ nA`, and
applying that to `rfl` produces `False`.

The entire secrecy proof is 7 lines of tactic code.

### The parameterized form

```lean
theorem nonce_secret' (initial : Finset Term)
    (h_init : initial = {enc (pair nA (atom "Alice")) kAB, enc nA kAB})
    (h_key : kAB ∉ initial) :
    ¬ Derivable initial nA := by
  subst h_init
  exact nonce_secret
```

This matches the problem statement's signature. After substituting
`h_init`, the goal is exactly `nonce_secret`. The hypothesis `h_key` is
unused — it follows from `h_init` and the fact that `kAB` is distinct from
both messages — but we include it to match the specification.

## Design notes

### Comparison with Paulson's Isabelle formalization

Paulson's *inductive approach* (1998) is the standard reference for
mechanized Dolev-Yao proofs. Key differences:

| | Paulson (Isabelle) | This formalization (Lean 4) |
|---|---|---|
| **Attacker model** | Split into `analz` and `synth` | Combined `Derivable` |
| **Secrecy proof** | Closure characterization of `analz` | Semantic invariant (`guarded`) |
| **Knowledge set** | `Set msg` (possibly infinite) | `Finset Term` (finite) |
| **Protocol model** | Inductive trace of protocol events | Direct: just the messages |

Paulson's split into `analz`/`synth` gives him powerful inversion lemmas
(`analz` is monotone, idempotent, distributes over union). We trade those
for a simpler definition and compensate with the `guarded` invariant, which
is tailored to the specific secrecy property we need.

Paulson also models the protocol as an inductive set of *traces* (sequences
of protocol events), which lets him reason about multi-session attacks. We
model only the messages on the wire, which suffices for one-session secrecy
but wouldn't extend to authentication or multi-session properties without
additional structure.

### Why `Finset` and not `Set`?

`Finset Term` requires `DecidableEq Term` but gives us decidable
membership, which keeps the proof constructive (no `Classical.choice`).
For a one-protocol formalization with a small initial knowledge set, there's
no practical difference. A larger formalization tracking attacker knowledge
across protocol steps might prefer `Set` to avoid finiteness obligations.

### What's not here

This formalization covers the simplest possible Dolev-Yao scenario.
Extensions that would be interesting to formalize:

- **Public-key encryption** — add `aenc m (pk a)` and `adec (aenc m (pk a)) (sk a)`,
  with the attacker able to compute `pk a` from `a` but not invert it.
  The `guarded` invariant would need an additional case for asymmetric
  encryption.

- **Authentication** — prove that Bob knows he's talking to Alice (not
  just that the nonce is secret). This requires modeling the protocol as
  a trace and reasoning about correspondence properties.

- **Multi-session attacks** — an attacker who interleaves messages from
  different protocol runs. This is where Paulson's trace-based model shines
  and our static "messages on the wire" model would need reworking.

- **Hashing and signatures** — add `hash t` (one-way) and `sign m (sk a)`
  (verifiable with `pk a`). The invariant method extends, but each new
  primitive needs its own preservation argument.

## Building

```bash
lake update          # resolve dependencies
lake exe cache get   # download pre-built Mathlib (optional but saves hours)
lake build           # compile
```

Requires [elan](https://github.com/leanprover/elan) (the Lean version
manager). The toolchain version is pinned in `lean-toolchain`.
