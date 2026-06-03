# Formal Mathematics with Lean and AI

## Members

- Samuel Chassot

## Repository

My fork of mathlib is available at [https://github.com/samuelchassot/mathlib4.git](https://github.com/samuelchassot/mathlib4.git). The whole work is in the branch `sam/eulerian`, with a clean version in the branch `sam/eulerianPathContrib`.

## Contributions

The main contribution is a constructive proof of the existence direction of
the classical Eulerian criterion for finite simple graphs:

> A connected finite simple graph has an Eulerian trail iff it has either
> zero or exactly two vertices of odd degree.

Mathlib already had the converse (`IsEulerian.card_odd_degree`); this work
adds the missing existence direction via the standard maximal-trail argument.

### Branch `sam/eulerianPathContrib` (PR-ready)

Clean, single-file contribution intended as a Mathlib PR:

- `Mathlib/Combinatorics/SimpleGraph/Eulerian.lean` (667 lines) — proves
  `exists_isEulerian_of_connected_card_oddDegree_eq_zero_or_two`, plus the
  zero-odd and two-odd specialisations. The three "longest trail of some kind"
  constructions are unified behind one helper `exists_maximal_walk`.

### Branch `sam/eulerian` (full development history)

Contains the iterative development and AI-assisted experiments under
`MathlibTest/`:

- `Eulerian_v1_chatGPT.lean` / `Eulerian_v1.5_chatGPT.lean` — first
  ChatGPT-assisted drafts of the proof.
- `Eulerian_v1_README.md` — informal write-up of the maximal-trail argument.
- `Eulerian_v2_claude.lean` (629 lines) + `Eulerian_v2_claude README.md` —
  Claude-assisted refactor that roughly halves the original proof size
  with no new mathematics.
- `Eulerian.lean` — final consolidated version that was upstreamed to
  `sam/eulerianPathContrib`.
