# Program Verification Game

A lean4game that teaches **formal program verification** through an 8-world
progression — from basic functional proofs to imperative algorithms with loop
invariants.

Built with [lean4game](https://github.com/leanprover-community/lean4game).

## Curriculum

| World | Title | Theme | Status |
|-------|-------|-------|--------|
| 1 | **First Proofs** | Core tactics · GCD · Primality | ✅ Complete |
| 2 | **Functional Specifications** | Writing complete specs | 🚧 Stub |
| 3 | **Subtypes** | Type-level invariants | 🚧 Stub |
| 4 | **Termination** | Well-founded recursion | 🚧 Stub |
| 5 | **Data Invariants** | Sorted lists · Balanced trees | 🚧 Stub |
| 6 | **Pre/Post Conditions** | Hoare-style contracts | 🚧 Stub |
| 7 | **Imperative Intro** | Mutable state · Loops | 🚧 Stub |
| 8 | **Imperative Boss** | Full `mvcgen` verification | 🚧 Stub |

## World 1 Overview (First Proofs)

7 levels building the Euclidean GCD algorithm and a verified primality checker:

| Level | Title | Key Tactic |
|-------|-------|------------|
| 1 | Double or Nothing | `simp` |
| 2 | Even Numbers | `omega` |
| 3 | Length of Lists | `induction` |
| 4 | GCD Base Case | `simp [myGcd]` |
| 5 | GCD Step | `simp [myGcd, h]` |
| 6 | Coprime Numbers | `constructor` |
| 7 | Is This Prime? | `decide` |

## Local Dev Server Setup

### Prerequisites

- [elan](https://github.com/leanprover/elan) (installs Lean + Lake)
- [Node.js](https://nodejs.org) ≥ 18
- [npm](https://npmjs.com)

### Steps

**1. Clone lean4game (once)**

```bash
git clone --branch v4.23.0 \
  https://github.com/leanprover-community/lean4game \
  ../lean4game
cd ../lean4game && npm install
```

**2. Build the game**

```bash
# From pvgame/
lake build
```

**3. Start the dev server**

```bash
cd ../lean4game
VITE_LEAN4GAME_SINGLE=true VITE_LEAN4GAME_SINGLE_NAME=pvgame npm start
# Visit http://localhost:3000
```

### Troubleshooting

- If `lake build` fails, try `lake update -R` first to refresh dependencies.
- If the server can't find the game, check that `GAME_DIR` is an absolute path.

## Development

See [CLAUDE.md](CLAUDE.md) for project conventions, file naming, and how to
add new levels.

## License

Apache 2.0 — see [LICENSE](LICENSE).
