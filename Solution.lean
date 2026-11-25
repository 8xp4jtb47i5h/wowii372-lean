module

public import WOWII372

public section

/-!
# Proved solution

The three statements of `Challenge.lean`, with proofs from the `WOWII372` library. Comparator
checks that each declaration has exactly the type of its counterpart in `Challenge.lean` and uses
only the permitted axioms.
-/

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
  have h := WOWII372.regularized T hT (by omega)
  rw [max_eq_right (by omega)] at h
  have hpos : (0 : ℝ) < (T.pathCoverNumber : ℝ) - 1 := by
    have : (2 : ℝ) ≤ T.pathCoverNumber := by exact_mod_cast hp
    linarith
  rw [div_le_iff₀ hpos]
  have : ((T.pathCoverNumber - 1 : ℕ) : ℝ) = (T.pathCoverNumber : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [← this]
  exact_mod_cast h

/--
The two-path variant: a tree $T$ of order at least two with $p(T) \le 2$
satisfies $\tau(T) \le \gamma_t(T)$.
-/
theorem conjecture372.variants.two_paths (hT : T.IsTree)
    (hn : 2 ≤ Fintype.card α) (hp : T.pathCoverNumber ≤ 2) :
    T.vertexCoverNum.toNat ≤ T.totalDominationNumber :=
  WOWII372.vcn_le_totalDominationNumber hT hn hp

/--
A separate formulation with no division: every tree $T$ of order at least two
satisfies $\tau(T) \le \gamma_t(T)\max\{1,p(T)-1\}$. On paths the factor is one.
-/
theorem conjecture372.variants.regularized (hT : T.IsTree)
    (hn : 2 ≤ Fintype.card α) :
    T.vertexCoverNum.toNat ≤ T.totalDominationNumber * max 1 (T.pathCoverNumber - 1) :=
  WOWII372.regularized T hT hn

end WrittenOnTheWallII.GraphConjecture372
