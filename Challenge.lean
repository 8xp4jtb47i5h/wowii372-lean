module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.VertexCover
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Lattice.Nat

@[expose] public section

/-!
# Written on the Wall II, Conjecture 372

Let `T` be a finite tree. Write `τ(T)` for its vertex cover number, `γ_t(T)` for its total
domination number (the least size of a set `D` such that every vertex, including every vertex of
`D`, has a neighbour in `D`), and `p(T)` for its path cover number (the least number of pairwise
disjoint paths whose vertex sets cover all vertices; single-vertex paths are allowed).

Written on the Wall II, Conjecture 372 (E. DeLaViña, 18 February 2009) asserts
`γ_t(T) ≥ τ(T) / (p(T) - 1)` for trees on more than two vertices. The ratio is undefined on paths,
where `p(T) = 1`. J. J. Gebendorfer's manuscript (28 October 2026,
doi:10.13140/RG.2.2.25035.55849) proves it for `p(T) ≥ 2`, together with two related variants.

The three statements below are copied verbatim from the Formal Conjectures repository,
`FormalConjectures/WrittenOnTheWallII/GraphConjecture372.lean` at commit
`9097e2f90e66d2f6244209cb1c07f7120d17ec53`. The definitions of total domination and path covers
are copied verbatim from its `FormalConjecturesForMathlib` library at the same commit
(Copyright 2025–2026 The Formal Conjectures Authors, Apache License 2.0). The vertex cover number
`SimpleGraph.vertexCoverNum` and trees `SimpleGraph.IsTree` are Mathlib's.

* `conjecture372`: for a tree with more than two vertices and `p(T) ≥ 2`,
  `τ(T) / (p(T) - 1) ≤ γ_t(T)` (real division).
* `conjecture372.variants.two_paths`: for a tree with at least two vertices and `p(T) ≤ 2`,
  `τ(T) ≤ γ_t(T)`.
* `conjecture372.variants.regularized`: for a tree with at least two vertices,
  `τ(T) ≤ γ_t(T) · max 1 (p(T) - 1)`.
-/

namespace SimpleGraph

section PathCover

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A family of paths covering all vertices without overlaps. -/
def IsPathCover (G : SimpleGraph α) (P : Finset (Finset α)) : Prop :=
  (∀ s1 ∈ P, ∀ s2 ∈ P, s1 ≠ s2 → Disjoint s1 s2) ∧
  (Finset.univ ⊆ P.biUnion id) ∧
  (∀ s ∈ P, ∃ (u v : α) (p : G.Walk u v), p.IsPath ∧ s = p.support.toFinset)

/-- Minimum size of a path cover of `G`. -/
noncomputable def pathCoverNumber (G : SimpleGraph α) : ℕ :=
  sInf { k | ∃ P : Finset (Finset α), P.card = k ∧ IsPathCover G P }

end PathCover

section TotalDomination

variable {α : Type*} {G : SimpleGraph α} [Fintype α] [DecidableEq α]

/-- A set `D` is a total dominating set if every vertex is adjacent to a vertex
in `D`. -/
def IsTotalDominating (G : SimpleGraph α) (D : Set α) : Prop :=
  ∀ v, ∃ w ∈ D, G.Adj v w

/-- An `n`-total dominating set is a total dominating set with `n` vertices. -/
@[mk_iff]
structure IsTotalNDominatingSet (n : ℕ) (D : Finset α) : Prop where
  isTotalDominating : G.IsTotalDominating D
  card_eq : D.card = n

/-- The total domination number of `G`. -/
noncomputable def totalDominationNumber (G : SimpleGraph α) : ℕ :=
  sInf {n | ∃ D : Finset α, G.IsTotalNDominatingSet n D}

end TotalDomination

end SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture372

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] (T : SimpleGraph α)

/--
WOWII Conjecture 372 on its positive-denominator domain. If $T$ is a tree with
more than two vertices and path cover number $p(T) \ge 2$, then
$\gamma_t(T) \ge \tau(T)/(p(T)-1)$, where $\gamma_t$ is the total domination
number and $\tau$ is the vertex cover number.
-/
theorem conjecture372 (hT : T.IsTree) (hn : 2 < Fintype.card α)
    (hp : 2 ≤ T.pathCoverNumber) :
    (T.vertexCoverNum.toNat : ℝ) / ((T.pathCoverNumber : ℝ) - 1) ≤
      T.totalDominationNumber := by
  sorry

/--
The two-path variant: a tree $T$ of order at least two with $p(T) \le 2$
satisfies $\tau(T) \le \gamma_t(T)$.
-/
theorem conjecture372.variants.two_paths (hT : T.IsTree)
    (hn : 2 ≤ Fintype.card α) (hp : T.pathCoverNumber ≤ 2) :
    T.vertexCoverNum.toNat ≤ T.totalDominationNumber := by
  sorry

/--
A separate formulation with no division: every tree $T$ of order at least two
satisfies $\tau(T) \le \gamma_t(T)\max\{1,p(T)-1\}$. On paths the factor is one.
-/
theorem conjecture372.variants.regularized (hT : T.IsTree)
    (hn : 2 ≤ Fintype.card α) :
    T.vertexCoverNum.toNat ≤ T.totalDominationNumber * max 1 (T.pathCoverNumber - 1) := by
  sorry

end WrittenOnTheWallII.GraphConjecture372
