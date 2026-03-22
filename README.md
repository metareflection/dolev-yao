# DolevYao

A Lean 4 formalization of the Dolev-Yao attacker model for symbolic
cryptographic protocols, built on Mathlib.

## What's proved

**Theorem** (`DolevYao.nonce_secret`). A Dolev-Yao attacker who observes
both messages of a symmetric-key challenge-response protocol — but does not
possess the shared key — cannot derive the nonce. Encryption without the
key is opaque.

The formalization also includes:

- `DolevYao.Derivable` — the attacker capability relation, combining
  Paulson's `analz` (decomposition) and `synth` (construction) into a
  single inductive definition
- `DolevYao.guarded` — a semantic invariant: a term is *guarded* when every
  occurrence of the secret and key sits inside an encryption layer
- `DolevYao.guarded_of_derivable` — the invariant preservation theorem:
  derivability cannot break through encryption without the key

All proofs are constructive (no `Classical.choice` or `Decidable.em`) and
compile with zero `sorry`s.

## The protocol

A minimal two-message challenge-response between Alice and Bob sharing a
symmetric key `kAB`:

    Message 1: Alice → Bob:   enc ⟨nA, Alice⟩ kAB
    Message 2: Bob → Alice:   enc nA kAB

Alice generates a fresh nonce `nA`, pairs it with her identity, encrypts
with the shared key, and sends. Bob decrypts, extracts the nonce, and
echoes it back encrypted.

## Proof technique

The secrecy proof uses a *semantic invariant* rather than direct inversion
on the derivation. We define a predicate `guarded secret key t` meaning
"every occurrence of `secret` and `key` in `t` is sealed inside an
`enc _ key` layer." Then:

1. Both protocol messages are guarded (each is encrypted under `kAB`).
2. The key `kAB` is *not* guarded — it would need `kAB ≠ kAB`.
3. Every Dolev-Yao rule preserves guardedness. The critical case is
   decryption: to decrypt `enc m kAB`, the attacker needs `kAB`, but
   `kAB` is not guarded, so it cannot itself be derived from any guarded
   set.
4. The nonce `nA` is not guarded — it would need `nA ≠ nA`.
5. Therefore `nA` is not derivable.

This is analogous to Paulson's closure argument with `analz`/`synth`, but
packaged as a single preservation lemma over our combined `Derivable`
relation.

## Structure

| File | Contents |
|---|---|
| `DolevYao/Terms.lean` | `Term` inductive type (atoms, pairs, symmetric encryption) |
| `DolevYao/Derivable.lean` | `Derivable` relation, `guarded` invariant, `guarded_of_derivable` |
| `DolevYao/Protocol.lean` | Protocol constants, `nonce_secret` theorem |
| `DolevYao.lean` | Root import |
| `TUTORIAL.md` | Annotated walkthrough of every definition and proof |

## Building

Requires [elan](https://github.com/leanprover/elan).

```bash
lake update          # resolve dependencies
lake exe cache get   # download pre-built Mathlib (saves hours)
lake build           # compile — should finish in seconds
```

## References

- D. Dolev, A. C. Yao,
  [*On the Security of Public Key Protocols*](https://ieeexplore.ieee.org/document/1056650)
  (IEEE Trans. Information Theory, 1983). The original model. Section 2's
  formalization of attacker capabilities as closure rules is the direct
  ancestor of our `Derivable` relation.

- L. C. Paulson,
  [*The Inductive Approach to Verifying Cryptographic Protocols*](https://doi.org/10.3233/JCS-1998-61-205)
  (J. Computer Security, 1998). The closest existing mechanization
  (Isabelle/HOL). His `analz` and `synth` sets split the attacker into
  decomposition and construction phases; we combine them into one relation
  and use a semantic invariant (`guarded`) instead of a closure
  characterization.

- B. Blanchet,
  [*Modeling and Verifying Security Protocols with the Applied Pi Calculus and ProVerif*](https://bblanche.gitlabpages.inria.fr/publications/BlanchetFnTPS16.pdf)
  (Foundations and Trends in Privacy and Security, 2016). Section 2 gives
  a clean modern presentation of symbolic terms and attacker rules that
  maps well to an inductive Lean definition.

- [Mathlib4](https://github.com/leanprover-community/mathlib4). Provides
  the `Finset` infrastructure used for the attacker's knowledge set.
