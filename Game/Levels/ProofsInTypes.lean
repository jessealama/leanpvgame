import Game.Levels.ProofsInTypes.L08_Victory

World "ProofsInTypes"
Title "Proofs Packed in Types"

Introduction "
**Welcome to World 4: Proofs Packed in Types!**

In Worlds 1–3 we proved *theorems about programs*.
In this world, we go further: we pack those proofs *inside the types themselves*.

The result: values whose types **guarantee** correctness.
The compiler becomes the verifier — incorrect code simply won't compile.

**New ideas in this world**:
- **Subtypes** `{x : T // P x}` — values bundled with their proof
- **`Fin n`** — natural numbers that are provably `< n`
- **Proof-carrying functions** — types that enforce pre/postconditions
- **Invariant-preserving structures** — data structures that *cannot* violate their invariants
"
