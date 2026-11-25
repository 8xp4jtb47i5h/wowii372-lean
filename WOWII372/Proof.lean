module

public import WOWII372.Defs
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.VertexCover
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

public section


/-!
# WOWII 372, part 1: `2 τ(T) + 2 ≤ 3 |D|` for every total dominating set `D` of a tree `T`

Counting argument: write `a v` for the number of neighbours of `v` in `D` and `b v` for the
number outside `D`. Then `∑ (a v + b v) = 2 (n - 1)`, `∑_{v ∉ D} a v = ∑_{v ∈ D} b v`, and `a v ≥ 1`
for every `v` (total domination). The vertices outside `D` span at most `(|D| - 2) / 2` edges, and
`D` together with the larger endpoint (in a fixed numbering) of each such edge is a vertex cover.
-/

open SimpleGraph Finset

namespace WOWII372

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
/-- An explicit vertex cover bounds the vertex cover number. -/
lemma vertexCoverNum_toNat_le_card (T : SimpleGraph α) (C : Finset α)
    (hC : T.IsVertexCover (C : Set α)) : T.vertexCoverNum.toNat ≤ C.card := by
  have h := hC.vertexCoverNum_le
  rw [Set.encard_coe_eq_coe_finsetCard] at h
  simpa using ENat.toNat_le_toNat h (ENat.natCast_ne_top _)

/-- In a tree with at least two vertices a minimum total dominating set exists. -/
lemma exists_min_tds (T : SimpleGraph α) (hT : T.IsTree) (hn : 2 ≤ Fintype.card α) :
    ∃ D : Finset α, T.IsTotalDominating (D : Set α) ∧ D.card = T.totalDominationNumber := by
  classical
  have huniv : T.IsTotalDominating ((univ : Finset α) : Set α) := by
    intro v
    obtain ⟨w, hw⟩ : ∃ w, w ≠ v := by
      by_contra h
      push Not at h
      have : Fintype.card α ≤ 1 := Fintype.card_le_one_iff.mpr fun x y => (h x).trans (h y).symm
      omega
    obtain ⟨p⟩ := hT.connected.preconnected v w
    cases p with
    | nil => exact absurd rfl hw
    | cons h _ => exact ⟨_, by simp, h⟩
  have hne : {n | ∃ D : Finset α, T.IsTotalNDominatingSet n D}.Nonempty :=
    ⟨_, univ, ⟨huniv, rfl⟩⟩
  obtain ⟨D, hD⟩ := Nat.sInf_mem hne
  exact ⟨D, hD.isTotalDominating, hD.card_eq⟩

/-- Part 1: for a tree `T` and any total dominating set `D`, `2 τ(T) + 2 ≤ 3 |D|`. -/
theorem two_mul_vcn_add_two_le (T : SimpleGraph α) (hT : T.IsTree) (D : Finset α)
    (hD : T.IsTotalDominating (D : Set α)) :
    2 * T.vertexCoverNum.toNat + 2 ≤ 3 * D.card := by
  classical
  let r := Fintype.equivFin α
  set O : Finset α := Dᶜ with hO
  let ind : α → α → ℕ := fun v w => if T.Adj v w then 1 else 0
  let a : α → ℕ := fun v => ∑ w ∈ D, ind v w
  let b : α → ℕ := fun v => ∑ w ∈ O, ind v w
  let lo : α → α → ℕ := fun v w => if T.Adj v w ∧ r w < r v then 1 else 0
  let CO : Finset α := O.filter (fun v => ∃ w ∈ O, T.Adj v w ∧ r w < r v)
  -- the cover
  have hcover : T.IsVertexCover ((D ∪ CO : Finset α) : Set α) := by
    intro u v huv
    simp only [coe_union, Set.mem_union, mem_coe]
    by_cases hu : u ∈ D
    · exact Or.inl (Or.inl hu)
    by_cases hv : v ∈ D
    · exact Or.inr (Or.inl hv)
    have hu' : u ∈ O := by simpa [hO] using hu
    have hv' : v ∈ O := by simpa [hO] using hv
    have hne : r u ≠ r v := fun h => huv.ne (r.injective h)
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inr (Or.inr (mem_filter.mpr ⟨hv', u, hu', huv.symm, h⟩))
    · exact Or.inl (Or.inr (mem_filter.mpr ⟨hu', v, hv', huv, h⟩))
  have hτ : T.vertexCoverNum.toNat ≤ D.card + CO.card :=
    (vertexCoverNum_toNat_le_card T _ hcover).trans (card_union_le _ _)
  -- degrees split into neighbours inside and outside `D`
  have hdeg : ∀ v, T.degree v = a v + b v := by
    intro v
    rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, card_filter]
    exact (sum_add_sum_compl D (ind v)).symm
  -- degree sum of a tree
  have hsum : ∑ v, T.degree v + 2 = 2 * Fintype.card α := by
    rw [sum_degrees_eq_twice_card_edges, ← hT.card_edgeFinset]
    ring
  have hsplit : ∑ v, T.degree v = (∑ v ∈ D, a v + ∑ v ∈ O, a v) + (∑ v ∈ D, b v + ∑ v ∈ O, b v) := by
    simp_rw [hdeg, sum_add_distrib, hO, sum_add_sum_compl]
  -- double counting the edges between `D` and its complement
  have hab : ∑ v ∈ O, a v = ∑ v ∈ D, b v := by
    simp only [a, b]
    rw [sum_comm]
    refine sum_congr rfl fun w _ => sum_congr rfl fun v _ => ?_
    simp only [ind, T.adj_comm]
  -- total domination: every vertex has a neighbour in `D`
  have ha1 : ∀ v, 1 ≤ a v := by
    intro v
    obtain ⟨w, hw, hvw⟩ := hD v
    have : ind v w ≤ a v := single_le_sum (f := ind v) (fun _ _ => Nat.zero_le _) hw
    simpa [ind, hvw] using this
  have hDa : D.card ≤ ∑ v ∈ D, a v := by
    rw [card_eq_sum_ones]; exact sum_le_sum fun v _ => ha1 v
  have hOa : O.card ≤ ∑ v ∈ O, a v := by
    rw [card_eq_sum_ones]; exact sum_le_sum fun v _ => ha1 v
  -- edges inside the complement: each counted once from its larger endpoint
  have hlo : ∑ v ∈ O, b v = 2 * ∑ v ∈ O, ∑ w ∈ O, lo v w := by
    have hsplit_ind : ∀ v w, ind v w = lo v w + lo w v := by
      intro v w
      simp only [ind, lo]
      by_cases h : T.Adj v w
      · have hne : r v ≠ r w := fun e => h.ne (r.injective e)
        rcases lt_or_gt_of_ne hne with e | e
        · simp [h, h.symm, e, not_lt_of_gt e]
        · simp [h, h.symm, e, not_lt_of_gt e]
      · have h' : ¬ T.Adj w v := fun e => h e.symm
        simp [h, h']
    simp only [b, hsplit_ind, sum_add_distrib]
    rw [sum_comm (f := fun v w => lo w v)]
    ring
  have hCO : CO.card ≤ ∑ v ∈ O, ∑ w ∈ O, lo v w := by
    rw [card_filter]
    refine sum_le_sum fun v _ => ?_
    split_ifs with h
    · obtain ⟨w, hw, hvw, hlt⟩ := h
      have : lo v w ≤ ∑ w ∈ O, lo v w := single_le_sum (f := lo v) (fun _ _ => Nat.zero_le _) hw
      simpa [lo, hvw, hlt] using this
    · exact Nat.zero_le _
  have hOcard : O.card + D.card = Fintype.card α := by
    rw [hO, card_compl]; have := card_le_univ D; omega
  omega

end WOWII372

/-
# WOWII 372, part 2: the arithmetic of a single path

Positions `0, …, m-1` of a path; `k` is a neighbour of `i` when `|i - k| = 1`.
`Dm` is a set of positions (the dominating set restricted to the path); every position except
possibly `j0` has a neighbour in `Dm`.

* `two_mul_card_add_one_ge` : `m ≤ 2 |Dm| + 1`.
* `tight_no_nbr`            : if `m = 2 |Dm| + 1`, then `j0` has no neighbour in `Dm`.
* `tight_false`             : if `m = 2 |Dm| + 1`, `j0 ∈ Dm` and `j0` is even, contradiction.
* `exists_cover`            : every second position covers the path with `m / 2` positions, and the
                              cover can contain a chosen `j0` unless `m` is odd and `j0` even.
-/

open Finset

namespace WOWII372.Idx

/-- `k` is a neighbour of `i` on the path with positions `0, …, m-1`. -/
abbrev Nb (m i k : ℕ) : Prop := i < m ∧ k < m ∧ (k + 1 = i ∨ i + 1 = k)

lemma nb_symm {m i k : ℕ} : Nb m i k ↔ Nb m k i := by
  unfold Nb; omega

lemma card_nbrs_le_two (m i : ℕ) (s : Finset ℕ) : #(s.filter (Nb m i)) ≤ 2 := by
  calc #(s.filter (Nb m i)) ≤ #({i - 1, i + 1} : Finset ℕ) := by
        apply card_le_card
        intro k hk
        simp only [mem_filter] at hk
        simp only [mem_insert, mem_singleton]
        omega
    _ ≤ 2 := card_le_two

/-- Double counting of neighbouring pairs between two sets of positions. -/
lemma sum_nbrs_comm (m : ℕ) (s t : Finset ℕ) :
    ∑ v ∈ s, #(t.filter (Nb m v)) = ∑ d ∈ t, #(s.filter (Nb m d)) := by
  have := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := s) (t := t) (r := Nb m)
  simp only [bipartiteAbove, bipartiteBelow] at this
  rw [this]
  refine sum_congr rfl fun d _ => ?_
  congr 1
  ext v
  simp only [mem_filter]
  rw [nb_symm]

variable {m j0 : ℕ} {Dm : Finset ℕ}

/-- Lower bound: all positions but `j0` dominated by `Dm` forces `m ≤ 2 |Dm| + 1`. -/
lemma two_mul_card_add_one_ge
    (hU : ∀ v < m, v ≠ j0 → ∃ d ∈ Dm, Nb m v d) : m ≤ 2 * #Dm + 1 := by
  have h1 : m - 1 ≤ #((range m).erase j0) := by
    have := pred_card_le_card_erase (s := range m) (a := j0); simpa using this
  have h2 : #((range m).erase j0) ≤ ∑ v ∈ (range m).erase j0, #(Dm.filter (Nb m v)) := by
    rw [card_eq_sum_ones]
    refine sum_le_sum fun v hv => ?_
    simp only [mem_erase, mem_range] at hv
    obtain ⟨d, hd, hvd⟩ := hU v hv.2 hv.1
    exact card_pos.mpr ⟨d, mem_filter.mpr ⟨hd, hvd⟩⟩
  have h3 : ∑ v ∈ (range m).erase j0, #(Dm.filter (Nb m v)) ≤
      ∑ v ∈ range m, #(Dm.filter (Nb m v)) :=
    sum_le_sum_of_subset (erase_subset _ _)
  have h4 : ∑ v ∈ range m, #(Dm.filter (Nb m v)) = ∑ d ∈ Dm, #((range m).filter (Nb m d)) :=
    sum_nbrs_comm m _ _
  have h5 : ∑ d ∈ Dm, #((range m).filter (Nb m d)) ≤ ∑ d ∈ Dm, 2 :=
    sum_le_sum fun d _ => card_nbrs_le_two m d _
  simp only [sum_const, smul_eq_mul] at h5
  omega

/-- Facts in the tight case `m = 2 |Dm| + 1`: `j0` has no neighbour in `Dm`, every other position
has exactly one, and every position of `Dm` has two neighbours. -/
lemma tight_facts (hU : ∀ v < m, v ≠ j0 → ∃ d ∈ Dm, Nb m v d) (hj0 : j0 < m)
    (htight : m = 2 * #Dm + 1) :
    #(Dm.filter (Nb m j0)) = 0 ∧
      (∀ v < m, v ≠ j0 → #(Dm.filter (Nb m v)) = 1) ∧
      (∀ d ∈ Dm, #((range m).filter (Nb m d)) = 2) := by
  set c : ℕ → ℕ := fun v => #(Dm.filter (Nb m v)) with hc
  set nb : ℕ → ℕ := fun d => #((range m).filter (Nb m d)) with hnb
  have hS : ∑ v ∈ range m, c v = ∑ d ∈ Dm, nb d := sum_nbrs_comm m _ _
  have hnb2 : ∀ d, nb d ≤ 2 := fun d => card_nbrs_le_two m d _
  have hSle : ∑ d ∈ Dm, nb d ≤ 2 * #Dm := by
    have := sum_le_sum (s := Dm) fun d _ => hnb2 d
    simpa [mul_comm] using this
  have hpos : ∀ v ∈ (range m).erase j0, 1 ≤ c v := by
    intro v hv
    simp only [mem_erase, mem_range] at hv
    obtain ⟨d, hd, hvd⟩ := hU v hv.2 hv.1
    exact card_pos.mpr ⟨d, mem_filter.mpr ⟨hd, hvd⟩⟩
  have hsplit : ∑ v ∈ range m, c v = c j0 + ∑ v ∈ (range m).erase j0, c v :=
    (add_sum_erase _ _ (mem_range.mpr hj0)).symm
  have herase_card : #((range m).erase j0) = m - 1 := by
    rw [card_erase_of_mem (mem_range.mpr hj0), card_range]
  have hlow : m - 1 ≤ ∑ v ∈ (range m).erase j0, c v := by
    rw [← herase_card, card_eq_sum_ones]; exact sum_le_sum hpos
  refine ⟨?_, ?_, ?_⟩
  · show c j0 = 0
    omega
  · intro v hv hvj
    show c v = 1
    have hmem : v ∈ (range m).erase j0 := by simp [hv, hvj]
    by_contra hne
    have hge : 2 ≤ c v := by have := hpos v hmem; omega
    have := add_sum_erase _ c hmem
    have hlow' : m - 2 ≤ ∑ w ∈ ((range m).erase j0).erase v, c w := by
      have hcard : #(((range m).erase j0).erase v) = m - 2 := by
        rw [card_erase_of_mem hmem, herase_card]; omega
      rw [← hcard, card_eq_sum_ones]
      exact sum_le_sum fun w hw => hpos w (mem_of_mem_erase hw)
    omega
  · intro d hd
    show nb d = 2
    by_contra hne
    have hle : nb d ≤ 1 := by have := hnb2 d; omega
    have h1 := add_sum_erase _ nb hd
    have h2 : ∑ e ∈ Dm.erase d, nb e ≤ 2 * #(Dm.erase d) := by
      have := sum_le_sum (s := Dm.erase d) fun e _ => hnb2 e
      simpa [mul_comm] using this
    rw [card_erase_of_mem hd] at h2
    have : 1 ≤ #Dm := card_pos.mpr ⟨d, hd⟩
    have hlow2 : m - 1 ≤ ∑ v ∈ range m, c v := by omega
    omega

/-- In the tight case `j0` has no neighbour in `Dm`. -/
lemma tight_no_nbr (hU : ∀ v < m, v ≠ j0 → ∃ d ∈ Dm, Nb m v d) (hj0 : j0 < m)
    (htight : m = 2 * #Dm + 1) : ∀ d ∈ Dm, ¬ Nb m j0 d := by
  intro d hd hnb
  have := (tight_facts hU hj0 htight).1
  rw [card_eq_zero, filter_eq_empty_iff] at this
  exact this hd hnb

/-- The tight case is impossible when the exceptional position `j0` is even and lies in `Dm`. -/
lemma tight_false (hU : ∀ v < m, v ≠ j0 → ∃ d ∈ Dm, Nb m v d) (hj0m : j0 ∈ Dm)
    (hDm : Dm ⊆ range m) (htight : m = 2 * #Dm + 1) (heven : Even j0) : False := by
  have hj0 : j0 < m := mem_range.mp (hDm hj0m)
  obtain ⟨hc0, hc1, hnb2⟩ := tight_facts hU hj0 htight
  have hno := tight_no_nbr hU hj0 htight
  -- `j0` has two neighbours, so `1 ≤ j0` and `j0 + 1 < m`
  have hj0nb := hnb2 j0 hj0m
  have hj0pos : 1 ≤ j0 ∧ j0 + 1 < m := by
    by_contra h
    have : #((range m).filter (Nb m j0)) ≤ 1 := by
      calc #((range m).filter (Nb m j0)) ≤ #({if j0 = 0 then j0 + 1 else j0 - 1} : Finset ℕ) := by
            apply card_le_card
            intro k hk
            simp only [mem_filter, mem_range] at hk
            simp only [mem_singleton]
            split_ifs <;> omega
        _ = 1 := card_singleton _
    omega
  -- count neighbouring pairs into the positions left of `j0`
  have hL : ∑ v ∈ range j0, #(Dm.filter (Nb m v)) = j0 := by
    rw [sum_congr rfl (g := fun _ => 1) fun v hv => by
      simp only [mem_range] at hv
      exact hc1 v (by omega) (by omega)]
    simp
  rw [sum_nbrs_comm] at hL
  have hterm : ∀ d ∈ Dm, #((range j0).filter (Nb m d)) =
      if d = j0 then 1 else if d < j0 then 2 else 0 := by
    intro d hd
    have hdm : d < m := mem_range.mp (hDm hd)
    split_ifs with h1 h2
    · subst h1
      rw [card_eq_one]
      refine ⟨d - 1, ?_⟩
      ext k; simp only [mem_filter, mem_range, mem_singleton]; omega
    · -- `d` is not `j0 - 1`, since otherwise `j0` would have a neighbour in `Dm`
      have hd1 : d + 1 ≠ j0 := fun h => hno d hd (by unfold Nb; omega)
      have hdnb := hnb2 d hd
      have hdpos : 1 ≤ d := by
        by_contra h0
        have : #((range m).filter (Nb m d)) ≤ 1 := by
          calc #((range m).filter (Nb m d)) ≤ #({d + 1} : Finset ℕ) := by
                apply card_le_card
                intro k hk
                simp only [mem_filter, mem_range] at hk
                simp only [mem_singleton]
                omega
            _ = 1 := card_singleton _
        omega
      rw [card_eq_two]
      refine ⟨d - 1, d + 1, by omega, ?_⟩
      ext k; simp only [mem_filter, mem_range, mem_insert, mem_singleton]; omega
    · rw [card_eq_zero, filter_eq_empty_iff]
      intro k hk; simp only [mem_range] at hk; omega
  rw [sum_congr rfl hterm] at hL
  -- the sum is `1 + 2 · #{d ∈ Dm | d < j0}`
  have hsum : ∑ d ∈ Dm, (if d = j0 then 1 else if d < j0 then 2 else 0) =
      1 + 2 * #(Dm.filter (· < j0)) := by
    rw [← add_sum_erase _ _ hj0m, ite_eq_left rfl]
    congr 1
    rw [card_eq_sum_ones, mul_sum, sum_filter]
    rw [← sum_erase_add (s := Dm) (a := j0) (f := fun d => if d < j0 then 2 * 1 else 0) hj0m]
    simp only [lt_irrefl, ite_false, add_zero]
    refine sum_congr rfl fun d hd => ?_
    rw [ite_eq_right (ne_of_mem_erase hd)]
  rw [hsum] at hL
  obtain ⟨k, hk⟩ := heven
  omega

/-- Covers of a path: every second position, `m / 2` of them; the cover can be made to contain a
chosen position `j0 < m` unless `m` is odd and `j0` is even. -/
lemma exists_cover (m j0 : ℕ) :
    ∃ C : Finset ℕ, C ⊆ range m ∧ #C ≤ m / 2 ∧ (∀ i, i + 1 < m → i ∈ C ∨ i + 1 ∈ C) ∧
      (j0 < m → (Even m ∨ Odd j0) → j0 ∈ C) := by
  by_cases hev : Even m ∧ Even j0
  · obtain ⟨r, hr⟩ := hev.1
    refine ⟨(range (m / 2)).image (2 * ·), ?_, ?_, ?_, ?_⟩
    · intro x hx; simp only [mem_image, mem_range] at hx ⊢; omega
    · exact card_image_le.trans (by simp)
    · intro i hi
      rcases Nat.even_or_odd i with ⟨k, hk⟩ | ⟨k, hk⟩
      · left; simp only [mem_image, mem_range]; exact ⟨k, by omega, by omega⟩
      · right; simp only [mem_image, mem_range]; exact ⟨k + 1, by omega, by omega⟩
    · intro hj _; obtain ⟨k, hk⟩ := hev.2
      simp only [mem_image, mem_range]; exact ⟨k, by omega, by omega⟩
  · refine ⟨(range (m / 2)).image (2 * · + 1), ?_, ?_, ?_, ?_⟩
    · intro x hx; simp only [mem_image, mem_range] at hx ⊢; omega
    · exact card_image_le.trans (by simp)
    · intro i hi
      rcases Nat.even_or_odd i with ⟨k, hk⟩ | ⟨k, hk⟩
      · right; simp only [mem_image, mem_range]; exact ⟨k, by omega, by omega⟩
      · left; simp only [mem_image, mem_range]; exact ⟨k, by omega, by omega⟩
    · intro hj hor
      have hodd : Odd j0 := by
        rcases hor with hm | ho
        · rcases Nat.even_or_odd j0 with he | ho
          · exact absurd ⟨hm, he⟩ hev
          · exact ho
        · exact ho
      obtain ⟨k, hk⟩ := hodd
      simp only [mem_image, mem_range]; exact ⟨k, by omega, by omega⟩

end WOWII372.Idx

/-
# WOWII 372, part 2: trees covered by at most two paths

A path is numbered `0, …, m-1` (`NPath`). If two numbered paths cover a tree, they carry `n - 2`
edges, so exactly one more edge `xy` exists, and it joins the two paths. Every other vertex only
has path neighbours, so the position lemmas of `WOWII372.Idx` apply to each path.
-/

open SimpleGraph Finset

namespace WOWII372

variable {α : Type*} [DecidableEq α]

/-- A path in `T` with vertices numbered `0, …, m-1`. -/
structure NPath (T : SimpleGraph α) where
  /-- The number of vertices. -/
  m : ℕ
  /-- The numbering. -/
  f : ℕ → α
  inj : ∀ i j, i < m → j < m → f i = f j → i = j
  adj : ∀ i, i + 1 < m → T.Adj (f i) (f (i + 1))

namespace NPath

variable {T : SimpleGraph α} (P : NPath T)

/-- The vertex set of a numbered path. -/
def verts : Finset α := (range P.m).image P.f

/-- The edges of a numbered path. -/
def edges : Finset (Sym2 α) := (range (P.m - 1)).image fun i => s(P.f i, P.f (i + 1))

lemma card_verts : #P.verts = P.m := by
  rw [verts, card_image_of_injOn, card_range]
  intro i hi j hj h
  exact P.inj i j (by simpa using hi) (by simpa using hj) h

lemma mem_verts {v : α} : v ∈ P.verts ↔ ∃ i < P.m, P.f i = v := by
  simp [verts]

lemma f_mem_verts {i : ℕ} (hi : i < P.m) : P.f i ∈ P.verts := P.mem_verts.mpr ⟨i, hi, rfl⟩

lemma edges_subset [Fintype α] [DecidableRel T.Adj] : P.edges ⊆ T.edgeFinset := by
  intro e he
  simp only [edges, mem_image, mem_range] at he
  obtain ⟨i, hi, rfl⟩ := he
  simpa using P.adj i (by omega)

lemma card_edges : #P.edges = P.m - 1 := by
  rw [edges, card_image_of_injOn, card_range]
  intro i hi j hj h
  simp only [coe_range, Set.mem_Iio] at hi hj
  simp only [Sym2.eq_iff] at h
  rcases h with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact P.inj i j (by omega) (by omega) h1
  · have := P.inj i (j + 1) (by omega) (by omega) h1
    have := P.inj (i + 1) j (by omega) (by omega) h2
    omega

/-- A path edge joins two neighbouring positions. -/
lemma of_mem_edges {v w : α} (h : s(v, w) ∈ P.edges) :
    ∃ i k, Idx.Nb P.m i k ∧ P.f i = v ∧ P.f k = w := by
  simp only [edges, mem_image, mem_range] at h
  obtain ⟨j, hj, hjw⟩ := h
  rw [Sym2.eq_iff] at hjw
  rcases hjw with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨j, j + 1, by unfold Idx.Nb; omega, h1, h2⟩
  · exact ⟨j + 1, j, by unfold Idx.Nb; omega, h2, h1⟩

lemma mem_verts_of_mem_edges {v w : α} (h : s(v, w) ∈ P.edges) : v ∈ P.verts := by
  obtain ⟨i, k, hnb, rfl, -⟩ := P.of_mem_edges h
  exact P.f_mem_verts hnb.1

/-- A path edge at position `i` leads to a neighbouring position. -/
lemma nb_of_mem_edges {i : ℕ} (hi : i < P.m) {w : α} (h : s(P.f i, w) ∈ P.edges) :
    ∃ k, Idx.Nb P.m i k ∧ P.f k = w := by
  obtain ⟨i', k, hnb, h1, h2⟩ := P.of_mem_edges h
  obtain rfl := P.inj i' i hnb.1 hi h1
  exact ⟨k, hnb, h2⟩

/-- A set of positions covering consecutive pairs covers the path edges. -/
lemma covers {C : Finset ℕ} (hC : ∀ i, i + 1 < P.m → i ∈ C ∨ i + 1 ∈ C) {v w : α}
    (h : s(v, w) ∈ P.edges) : v ∈ C.image P.f ∨ w ∈ C.image P.f := by
  obtain ⟨i, k, hnb, rfl, rfl⟩ := P.of_mem_edges h
  obtain ⟨_, _, h | h⟩ := hnb
  · subst h
    rcases hC k (by omega) with h | h
    · exact Or.inr (mem_image_of_mem _ h)
    · exact Or.inl (mem_image_of_mem _ h)
  · subst h
    rcases hC i (by omega) with h | h
    · exact Or.inl (mem_image_of_mem _ h)
    · exact Or.inr (mem_image_of_mem _ h)

/-- The positions of a path that lie in `D`. -/
def pos (D : Finset α) : Finset ℕ := (range P.m).filter fun i => P.f i ∈ D

lemma pos_subset (D : Finset α) : P.pos D ⊆ range P.m := filter_subset _ _

lemma image_pos (D : Finset α) : (P.pos D).image P.f ⊆ D := by
  intro v hv
  simp only [pos, mem_image, mem_filter] at hv
  obtain ⟨i, ⟨-, h⟩, rfl⟩ := hv
  exact h

lemma card_image_pos (D : Finset α) : #((P.pos D).image P.f) = #(P.pos D) := by
  refine card_image_of_injOn fun i hi j hj h => ?_
  simp only [pos, coe_filter, mem_range, Set.mem_ofPred_eq] at hi hj
  exact P.inj i j hi.1 hj.1 h

lemma image_subset_verts (C : Finset ℕ) (hC : C ⊆ range P.m) : C.image P.f ⊆ P.verts :=
  image_subset_image hC

/-- Domination along a path: if every edge at a vertex other than position `j` is a path edge,
the positions in `D` dominate all positions other than `j`. -/
lemma dom (D : Finset α) (hD : T.IsTotalDominating (D : Set α)) (j : ℕ)
    (hloc : ∀ i < P.m, i ≠ j → ∀ w, T.Adj (P.f i) w → s(P.f i, w) ∈ P.edges) :
    ∀ v < P.m, v ≠ j → ∃ d ∈ P.pos D, Idx.Nb P.m v d := by
  intro v hv hvj
  obtain ⟨w, hw, hvw⟩ := hD (P.f v)
  obtain ⟨k, hnb, rfl⟩ := P.nb_of_mem_edges hv (hloc v hv hvj w hvw)
  exact ⟨k, mem_filter.mpr ⟨mem_range.mpr hnb.2.1, hw⟩, hnb⟩

/-- The numbered path of a path walk. -/
lemma exists_of_isPath {u v : α} (p : T.Walk u v) (hp : p.IsPath) :
    ∃ P : NPath T, P.verts = p.support.toFinset := by
  refine ⟨⟨p.length + 1, p.getVert, fun i j hi hj h => hp.getVert_injOn
    (show i ≤ p.length by omega) (show j ≤ p.length by omega) h,
    fun i hi => p.adj_getVert_succ (by omega)⟩, ?_⟩
  ext w
  simp only [mem_verts, List.mem_toFinset, Walk.mem_support_iff_exists_getVert]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, rfl, by omega⟩
  · rintro ⟨i, rfl, hi⟩; exact ⟨i, by omega, rfl⟩

end NPath

variable [Fintype α] {T : SimpleGraph α}

/-- A path cover with at most two paths gives one numbered path through all vertices, or two
disjoint numbered paths through all vertices. -/
lemma exists_npaths (hn : 2 ≤ Fintype.card α) (hp : T.pathCoverNumber ≤ 2) :
    (∃ P : NPath T, P.verts = univ) ∨
      ∃ P Q : NPath T, Disjoint P.verts Q.verts ∧ P.verts ∪ Q.verts = univ ∧ 1 ≤ P.m ∧ 1 ≤ Q.m := by
  classical
  have hne : {k | ∃ P : Finset (Finset α), P.card = k ∧ T.IsPathCover P}.Nonempty := by
    refine ⟨_, univ.image fun v => ({v} : Finset α), rfl, ?_, ?_, ?_⟩
    · intro s1 hs1 s2 hs2 hne
      simp only [mem_image, mem_univ, true_and] at hs1 hs2
      obtain ⟨a, rfl⟩ := hs1
      obtain ⟨b, rfl⟩ := hs2
      exact disjoint_singleton.mpr fun h => hne (h ▸ rfl)
    · intro v _
      simp
    · intro s hs
      simp only [mem_image, mem_univ, true_and] at hs
      obtain ⟨a, rfl⟩ := hs
      exact ⟨a, a, Walk.nil, Walk.IsPath.nil, by simp⟩
  obtain ⟨P0, hcard, hdisj, hcov, hpath⟩ := Nat.sInf_mem hne
  have hP0 : P0.card ≤ 2 := hcard ▸ hp
  have hmem : ∀ v, ∃ s ∈ P0, v ∈ s := by
    intro v
    have := hcov (mem_univ v)
    simpa using this
  have hpos : P0.card ≠ 0 := by
    intro h
    rw [card_eq_zero] at h
    obtain ⟨v⟩ : Nonempty α := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨s, hs, -⟩ := hmem v
    simp [h] at hs
  have hm : ∀ {u v : α} (p : T.Walk u v) (P : NPath T), P.verts = p.support.toFinset → 1 ≤ P.m := by
    intro u v p P hP
    rw [← P.card_verts, hP]
    exact card_pos.mpr ⟨u, by simp⟩
  rcases (by omega : P0.card = 1 ∨ P0.card = 2) with h1 | h2
  · obtain ⟨s, rfl⟩ := card_eq_one.mp h1
    obtain ⟨u, v, p, hpp, hs⟩ := hpath s (mem_singleton_self s)
    obtain ⟨P, hP⟩ := NPath.exists_of_isPath p hpp
    refine Or.inl ⟨P, ?_⟩
    rw [hP, ← hs]
    exact eq_univ_of_forall fun v => by
      obtain ⟨t, ht, hv⟩ := hmem v
      rwa [mem_singleton.mp ht] at hv
  · obtain ⟨s, t, hst, rfl⟩ := card_eq_two.mp h2
    obtain ⟨u, v, p, hpp, hs⟩ := hpath s (by simp)
    obtain ⟨u', v', q, hqp, ht⟩ := hpath t (by simp)
    obtain ⟨P, hP⟩ := NPath.exists_of_isPath p hpp
    obtain ⟨Q, hQ⟩ := NPath.exists_of_isPath q hqp
    refine Or.inr ⟨P, Q, ?_, ?_, hm p P hP, hm q Q hQ⟩
    · rw [hP, hQ, ← hs, ← ht]
      exact hdisj s (by simp) t (by simp) hst
    · rw [hP, hQ, ← hs, ← ht]
      exact eq_univ_of_forall fun w => by
        obtain ⟨r, hr, hw⟩ := hmem w
        simp only [mem_insert, mem_singleton] at hr
        rcases hr with rfl | rfl <;> simp [hw]

/-- One path through all vertices: `τ(T) ≤ |D|` for every total dominating set `D`. -/
theorem vcn_le_of_one_path (hT : T.IsTree) (P : NPath T) (hP : P.verts = univ) (D : Finset α)
    (hD : T.IsTotalDominating (D : Set α)) : T.vertexCoverNum.toNat ≤ #D := by
  classical
  have hcardP : P.m = Fintype.card α := by rw [← P.card_verts, hP, card_univ]
  have hall : ∀ e ∈ T.edgeFinset, e ∈ P.edges := by
    have hcard : #T.edgeFinset ≤ #P.edges := by
      have := hT.card_edgeFinset
      rw [P.card_edges]
      omega
    rw [eq_of_subset_of_card_le P.edges_subset hcard]
    exact fun e he => he
  have hloc : ∀ i < P.m, i ≠ P.m → ∀ w, T.Adj (P.f i) w → s(P.f i, w) ∈ P.edges :=
    fun i _ _ w h => hall s(P.f i, w) (mem_edgeFinset.mpr h)
  have hlow := Idx.two_mul_card_add_one_ge (P.dom D hD P.m hloc)
  obtain ⟨C, hCsub, hCcard, hCcov, -⟩ := Idx.exists_cover P.m 0
  have hcov : T.IsVertexCover ((C.image P.f : Finset α) : Set α) := by
    intro v w hvw
    exact P.covers hCcov (hall s(v, w) (mem_edgeFinset.mpr hvw))
  have h1 := vertexCoverNum_toNat_le_card T _ hcov
  have h2 : #(C.image P.f) ≤ #C := card_image_le
  have h3 : #(P.pos D) ≤ #D := by
    rw [← P.card_image_pos]; exact card_le_card (P.image_pos D)
  omega

/-- Two numbered paths through all vertices of a tree carry all edges but one, and the remaining
edge joins the two paths. -/
lemma two_paths_edges [DecidableRel T.Adj] (hT : T.IsTree) (P Q : NPath T)
    (hdisj : Disjoint P.verts Q.verts) (hcov : P.verts ∪ Q.verts = univ) (hP1 : 1 ≤ P.m)
    (hQ1 : 1 ≤ Q.m) :
    ∃ x ∈ P.verts, ∃ y ∈ Q.verts,
      ∀ e ∈ T.edgeFinset, e ∈ P.edges ∨ e ∈ Q.edges ∨ e = s(x, y) := by
  have hn : P.m + Q.m = Fintype.card α := by
    rw [← P.card_verts, ← Q.card_verts, ← card_union_of_disjoint hdisj, hcov, card_univ]
  have hE : Disjoint P.edges Q.edges := by
    rw [Finset.disjoint_left]
    intro e heP heQ
    induction e using Sym2.ind with
    | _ v w =>
      exact Finset.disjoint_left.mp hdisj (P.mem_verts_of_mem_edges heP) (Q.mem_verts_of_mem_edges heQ)
  have hsub : P.edges ∪ Q.edges ⊆ T.edgeFinset := union_subset P.edges_subset Q.edges_subset
  have hR : #(T.edgeFinset \ (P.edges ∪ Q.edges)) = 1 := by
    rw [card_sdiff_of_subset hsub, card_union_of_disjoint hE, P.card_edges, Q.card_edges]
    have := hT.card_edgeFinset
    omega
  -- an edge leaving `P.verts`
  have hu : P.f 0 ∈ (P.verts : Set α) := P.f_mem_verts (by omega)
  have hv : Q.f 0 ∉ (P.verts : Set α) := fun h =>
    Finset.disjoint_left.mp hdisj h (Q.f_mem_verts (by omega))
  obtain ⟨p⟩ := hT.connected.preconnected (P.f 0) (Q.f 0)
  obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart _ hu hv
  have hd2' : d.snd ∈ Q.verts := by
    have : d.snd ∈ P.verts ∪ Q.verts := hcov ▸ mem_univ _
    rcases mem_union.mp this with h | h
    · exact absurd h hd2
    · exact h
  have hdR : s(d.fst, d.snd) ∈ T.edgeFinset \ (P.edges ∪ Q.edges) := by
    refine mem_sdiff.mpr ⟨mem_edgeFinset.mpr d.adj, fun h => ?_⟩
    rcases mem_union.mp h with h | h
    · exact hd2 (P.mem_verts_of_mem_edges (Sym2.eq_swap ▸ h))
    · exact Finset.disjoint_left.mp hdisj hd1 (Q.mem_verts_of_mem_edges h)
  refine ⟨d.fst, hd1, d.snd, hd2', fun e he => ?_⟩
  by_contra hne
  push Not at hne
  have heR : e ∈ T.edgeFinset \ (P.edges ∪ Q.edges) :=
    mem_sdiff.mpr ⟨he, fun h => (mem_union.mp h).elim hne.1 hne.2.1⟩
  obtain ⟨r, hr⟩ := card_eq_one.mp hR
  rw [hr, mem_singleton] at heR hdR
  exact hne.2.2 (heR.trans hdR.symm)

/-- Two paths through all vertices: `τ(T) ≤ |D|` for every total dominating set `D`. -/
theorem vcn_le_of_two_paths (hT : T.IsTree) (P Q : NPath T) (hdisj : Disjoint P.verts Q.verts)
    (hcov : P.verts ∪ Q.verts = univ) (hP1 : 1 ≤ P.m) (hQ1 : 1 ≤ Q.m) (D : Finset α)
    (hD : T.IsTotalDominating (D : Set α)) : T.vertexCoverNum.toNat ≤ #D := by
  classical
  obtain ⟨x, hx, y, hy, hcl⟩ := two_paths_edges hT P Q hdisj hcov hP1 hQ1
  obtain ⟨j1, hj1, rfl⟩ := P.mem_verts.mp hx
  obtain ⟨j2, hj2, rfl⟩ := Q.mem_verts.mp hy
  have hxQ : P.f j1 ∉ Q.verts := Finset.disjoint_left.mp hdisj hx
  have hyP : Q.f j2 ∉ P.verts := fun h => Finset.disjoint_left.mp hdisj h hy
  -- edges at a vertex other than the end of the joining edge are path edges
  have hlocP : ∀ i < P.m, i ≠ j1 → ∀ w, T.Adj (P.f i) w → s(P.f i, w) ∈ P.edges := by
    intro i hi hij w hw
    rcases hcl s(P.f i, w) (mem_edgeFinset.mpr hw) with h | h | h
    · exact h
    · exact absurd (Q.mem_verts_of_mem_edges h) (Finset.disjoint_left.mp hdisj (P.f_mem_verts hi))
    · rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd (P.inj i j1 hi hj1 h1) hij
      · exact absurd (h1 ▸ P.f_mem_verts hi) hyP
  have hlocQ : ∀ i < Q.m, i ≠ j2 → ∀ w, T.Adj (Q.f i) w → s(Q.f i, w) ∈ Q.edges := by
    intro i hi hij w hw
    rcases hcl s(Q.f i, w) (mem_edgeFinset.mpr hw) with h | h | h
    · exact absurd (P.mem_verts_of_mem_edges h)
        (fun h' => Finset.disjoint_left.mp hdisj h' (Q.f_mem_verts hi))
    · exact h
    · rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd (h1 ▸ Q.f_mem_verts hi) hxQ
      · exact absurd (Q.inj i j2 hi hj2 h1) hij
  have hUP := P.dom D hD j1 hlocP
  have hUQ := Q.dom D hD j2 hlocQ
  have hlowP := Idx.two_mul_card_add_one_ge hUP
  have hlowQ := Idx.two_mul_card_add_one_ge hUQ
  -- the dominating set contains both position sets
  have hDcard : #(P.pos D) + #(Q.pos D) ≤ #D := by
    rw [← P.card_image_pos, ← Q.card_image_pos, ← card_union_of_disjoint]
    · exact card_le_card (union_subset (P.image_pos D) (Q.image_pos D))
    · exact disjoint_of_subset_left (P.image_subset_verts _ (P.pos_subset D))
        (disjoint_of_subset_right (Q.image_subset_verts _ (Q.pos_subset D)) hdisj)
  -- covers
  obtain ⟨C1, hC1sub, hC1card, hC1cov, hC1j⟩ := Idx.exists_cover P.m j1
  obtain ⟨C2, hC2sub, hC2card, hC2cov, hC2j⟩ := Idx.exists_cover Q.m j2
  by_cases hbad : Odd P.m ∧ Even j1 ∧ Odd Q.m ∧ Even j2
  · -- the joining edge needs an extra cover vertex; show the dominating set pays for it
    have hcover : T.IsVertexCover (((C1.image P.f ∪ C2.image Q.f) ∪ {P.f j1} : Finset α) : Set α) := by
      intro v w hvw
      simp only [coe_union, coe_singleton, Set.mem_union, mem_coe, Set.mem_singleton_iff]
      rcases hcl s(v, w) (mem_edgeFinset.mpr hvw) with h | h | h
      · rcases P.covers hC1cov h with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr (Or.inl (Or.inl h'))
      · rcases Q.covers hC2cov h with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr (Or.inl (Or.inr h'))
      · rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨-, h2⟩
        · exact Or.inl (Or.inr h1)
        · exact Or.inr (Or.inr h2)
    have hτ := vertexCoverNum_toNat_le_card T _ hcover
    have hc : #((C1.image P.f ∪ C2.image Q.f) ∪ {P.f j1}) ≤ #C1 + #C2 + 1 :=
      (card_union_le _ _).trans (by
        have := card_union_le (C1.image P.f) (C2.image Q.f)
        have := card_image_le (s := C1) (f := P.f)
        have := card_image_le (s := C2) (f := Q.f)
        simp only [card_singleton]
        omega)
    obtain ⟨hPodd, hj1even, hQodd, -⟩ := hbad
    -- if both paths are tight, the end `x` of the joining edge lies in `D`, contradicting parity
    by_cases htight : P.m = 2 * #(P.pos D) + 1 ∧ Q.m = 2 * #(Q.pos D) + 1
    · exfalso
      have hnoQ := Idx.tight_no_nbr hUQ hj2 htight.2
      -- the dominating neighbour of `y` is `x`
      obtain ⟨w, hw, hyw⟩ := hD (Q.f j2)
      have hxD : P.f j1 ∈ D := by
        rcases hcl s(Q.f j2, w) (mem_edgeFinset.mpr hyw) with h | h | h
        · exact absurd (P.mem_verts_of_mem_edges h) hyP
        · obtain ⟨k, hnb, rfl⟩ := Q.nb_of_mem_edges hj2 h
          exact absurd hnb (hnoQ k (mem_filter.mpr ⟨mem_range.mpr hnb.2.1, hw⟩))
        · rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨-, h2⟩
          · exact absurd (h1 ▸ Q.f_mem_verts hj2) hxQ
          · exact h2 ▸ hw
      exact Idx.tight_false hUP (mem_filter.mpr ⟨mem_range.mpr hj1, hxD⟩) (P.pos_subset D)
        htight.1 hj1even
    · obtain ⟨a, ha⟩ := hPodd
      obtain ⟨b, hb⟩ := hQodd
      omega
  · -- one end of the joining edge is in a cover already
    have hj : P.f j1 ∈ C1.image P.f ∨ Q.f j2 ∈ C2.image Q.f := by
      by_cases h1 : Even P.m ∨ Odd j1
      · exact Or.inl (mem_image_of_mem _ (hC1j hj1 h1))
      · right
        refine mem_image_of_mem _ (hC2j hj2 ?_)
        push Not at h1
        rw [Nat.not_even_iff_odd, Nat.not_odd_iff_even] at h1
        by_contra h2
        push Not at h2
        rw [Nat.not_even_iff_odd, Nat.not_odd_iff_even] at h2
        exact hbad ⟨h1.1, h1.2, h2.1, h2.2⟩
    have hcover : T.IsVertexCover ((C1.image P.f ∪ C2.image Q.f : Finset α) : Set α) := by
      intro v w hvw
      simp only [coe_union, Set.mem_union, mem_coe]
      rcases hcl s(v, w) (mem_edgeFinset.mpr hvw) with h | h | h
      · rcases P.covers hC1cov h with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr (Or.inl h')
      · rcases Q.covers hC2cov h with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr (Or.inr h')
      · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rcases hj with h' | h'
          · exact Or.inl (Or.inl h')
          · exact Or.inr (Or.inr h')
        · rcases hj with h' | h'
          · exact Or.inr (Or.inl h')
          · exact Or.inl (Or.inr h')
    have hτ := vertexCoverNum_toNat_le_card T _ hcover
    have := card_union_le (C1.image P.f) (C2.image Q.f)
    have := card_image_le (s := C1) (f := P.f)
    have := card_image_le (s := C2) (f := Q.f)
    omega

/-- Part 2: a tree of order at least two with path cover number at most two satisfies
`τ(T) ≤ γ_t(T)`. -/
theorem vcn_le_totalDominationNumber (hT : T.IsTree) (hn : 2 ≤ Fintype.card α)
    (hp : T.pathCoverNumber ≤ 2) : T.vertexCoverNum.toNat ≤ T.totalDominationNumber := by
  obtain ⟨D, hD, hDcard⟩ := exists_min_tds T hT hn
  rw [← hDcard]
  rcases exists_npaths hn hp with ⟨P, hP⟩ | ⟨P, Q, hdisj, hcov, hP1, hQ1⟩
  · exact vcn_le_of_one_path hT P hP D hD
  · exact vcn_le_of_two_paths hT P Q hdisj hcov hP1 hQ1 D hD

end WOWII372

-- The three statements of `GraphConjecture372`.

namespace WOWII372

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The universally defined form: `τ(T) ≤ γ_t(T) · max 1 (p(T) - 1)`. -/
theorem regularized (T : SimpleGraph α) (hT : T.IsTree) (hn : 2 ≤ Fintype.card α) :
    T.vertexCoverNum.toNat ≤ T.totalDominationNumber * max 1 (T.pathCoverNumber - 1) := by
  by_cases hp : T.pathCoverNumber ≤ 2
  · calc T.vertexCoverNum.toNat ≤ T.totalDominationNumber :=
          vcn_le_totalDominationNumber hT hn hp
      _ ≤ T.totalDominationNumber * max 1 (T.pathCoverNumber - 1) :=
          Nat.le_mul_of_pos_right _ (lt_of_lt_of_le Nat.one_pos (le_max_left _ _))
  · obtain ⟨D, hD, hDcard⟩ := exists_min_tds T hT hn
    have h1 := two_mul_vcn_add_two_le T hT D hD
    have h2 : 2 ≤ max 1 (T.pathCoverNumber - 1) := le_max_of_le_right (by omega)
    calc T.vertexCoverNum.toNat ≤ T.totalDominationNumber * 2 := by omega
      _ ≤ T.totalDominationNumber * max 1 (T.pathCoverNumber - 1) := Nat.mul_le_mul_left _ h2

end WOWII372
