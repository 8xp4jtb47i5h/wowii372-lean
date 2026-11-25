# Written on the Wall II, Conjecture 372, in Lean 4

A Lean 4 proof of Graffiti.pc conjecture 372 from E. DeLaViña's *Written on the Wall II*, in the
form stated by the [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures)
repository (`FormalConjectures/WrittenOnTheWallII/GraphConjecture372.lean`).

For a finite tree `T`, let `τ(T)` be the vertex cover number, `γ_t(T)` the total domination
number and `p(T)` the path cover number. The following are proved:

| Lean declaration | Statement |
|---|---|
| `conjecture372` | `τ(T) / (p(T) − 1) ≤ γ_t(T)` when `T` has more than two vertices and `p(T) ≥ 2` |
| `conjecture372.variants.two_paths` | `τ(T) ≤ γ_t(T)` when `T` has at least two vertices and `p(T) ≤ 2` |
| `conjecture372.variants.regularized` | `τ(T) ≤ γ_t(T) · max(1, p(T) − 1)` when `T` has at least two vertices |

A written proof of the same statements is given in J. J. Gebendorfer's manuscript
([doi:10.13140/RG.2.2.25035.55849](https://doi.org/10.13140/RG.2.2.25035.55849), 28 October
2026). The case `p(T) ≥ 3` follows from the bound `γ_t(T) ≥ 2(τ(T) + 1)/3`, which the August 2009
note to the conjecture records. This repository supplies a machine-checked proof. Its argument
for `p(T) ≤ 2` is organized differently from the manuscript's.

## Repository map

- `Challenge.lean`: the statements and the definitions they use. This is the file to audit.
  The definitions are copied verbatim from Formal Conjectures (Apache License 2.0).
- `Solution.lean`: the same three declarations, proved.
- `WOWII372/Defs.lean`: the same definitions, for the proof development.
- `WOWII372/Proof.lean`: the proof.
- `comparator.json`: the declarations that `lake comparator` checks against `Challenge.lean`.
- `formalization.yaml`: provenance, authorship, automation and review information.

## The proof

1. **Every tree.** For a total dominating set `D`, count edges. Each vertex of `D` has a
   neighbour in `D`, each other vertex has a neighbour in `D`, and a tree has `n − 1` edges. So at
   most `(|D| − 2)/2` edges avoid `D`. Adding one endpoint of each to `D` gives a vertex cover, so
   `2τ(T) + 2 ≤ 3|D|`. This settles `p(T) ≥ 3`.
2. **At most two paths.** Number the vertices of each covering path. Two paths carry `n − 2`
   edges, so exactly one more edge exists, and it joins the paths. Every other vertex has only
   path neighbours. Counting neighbouring positions gives `|D ∩ P| ≥ ⌊|P|/2⌋` on each path, and
   every second vertex of a path covers its edges. In the one tight case, a parity count along
   the path gives a contradiction.

## Build and check

```bash
lake exe cache get
lake build
scripts/verify-comparator.sh
```

## Provenance

The Lean code was written by an AI agent (Claude Opus 5.5, in Claude Code) under the direction of
the maintainer. It has been checked by the Lean kernel and Comparator, not reviewed line by line
by a human. See `formalization.yaml`.

This project is prepared for the [Palomar registry](https://palomar-registry.org/); submissions go
through https://submit.palomar-registry.org/.

## Licence

Apache License 2.0. See `LICENSE`.
