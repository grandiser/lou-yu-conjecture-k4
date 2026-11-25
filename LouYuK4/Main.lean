import LouYuK4.Order16Count
import LouYuK4.Constructions

/-!
# Main Theorems: The Lou–Yu Conjecture (2004) for `k = 4`

D. Lou and Q. Yu (*Connectivity of k-extendable graphs with large k*, Discrete Applied Mathematics
136 (2004), 55–61) conjectured that every minimally `k`-extendable graph `G` on `ν ≤ 4k` vertices
satisfies `δ(G) ∈ {k + 1, 2k, 2k + 1}`.

This file assembles the complete Lean 4 verification for `k = 4`:
1. `lou_yu_k4_order_and_bounds` (**unconditional**): For every connected minimally 4-extendable
   graph `G` on `ν ≤ 16` vertices:
   - `ν ∈ {10, 12, 14, 16}`,
   - `∀ v, 5 ≤ G.degree v` (Plummer 1980),
   - `∃ v, G.degree v ≤ 9` (the open Lou–Yu upper bound for all four orders `10, 12, 14, 16`),
   - `IsBipartite G → ∃ v, G.degree v = 5`,
   - at `ν = 10`, `δ(G) ∈ {5, 9}`,
   - at `ν = 12`, `δ(G) ≠ 8`.
2. `lou_yu_k4_minDegree_spectrum`: Combined with Lou–Yu's published 2004 dichotomy for
   non-bipartite graphs (`¬ IsBipartite G → ∀ v, 8 ≤ G.degree v`), the minimum degree of `G`
   lies in `{5, 8, 9}`.
3. `lou_yu_k4_attainability` (**unconditional**): Every value `d ∈ {5, 8, 9}` is realized by a
   connected minimally 4-extendable graph of order `≤ 16` (`K_{5,5}`, `G_4`, `K_{10}`).
-/

open SimpleGraph Finset

namespace LouYuK4

section MainTheorems

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Main Unconditional Theorem (`Lou–Yu k = 4`)**: Every connected minimally 4-extendable
graph `G` on `ν ≤ 16` vertices has `ν ∈ {10, 12, 14, 16}`, `∀ v, 5 ≤ G.degree v`, and
`∃ v, G.degree v ≤ 9`, with `δ(G) = 5` if bipartite, `δ(G) ∈ {5, 9}` at `ν = 10`, and
`δ(G) ≠ 8` at `ν = 12`. -/
theorem lou_yu_k4_order_and_bounds {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcard : Fintype.card V ≤ 16) (hconn : G.Connected)
    (hmin : IsMinimallyKExtendable G 4) :
    (Fintype.card V = 10 ∨ Fintype.card V = 12 ∨ Fintype.card V = 14 ∨ Fintype.card V = 16) ∧
    (∀ v : V, 5 ≤ G.degree v) ∧
    (∃ v : V, G.degree v ≤ 9) ∧
    (IsBipartite G → ∃ v : V, G.degree v = 5) ∧
    (Fintype.card V = 10 → (∃ v : V, G.degree v = 5) ∨ (∀ v : V, G.degree v = 9)) ∧
    (Fintype.card V = 12 → ¬ ((∀ v : V, 8 ≤ G.degree v) ∧ ∃ v : V, G.degree v = 8)) := by
  obtain ⟨heven, hge8⟩ := isKExtendable_even_card_and_ge hmin.1
  have hne8 : Fintype.card V ≠ 8 := fun h => nu_ne_eight_of_connected_min_four h hconn hmin
  have hcases : Fintype.card V = 10 ∨ Fintype.card V = 12 ∨ Fintype.card V = 14 ∨ Fintype.card V = 16 := by
    obtain ⟨m, hm⟩ := heven; omega
  have hge5 : ∀ v : V, 5 ≤ G.degree v := plummer_min_degree hconn hmin.1 (by rcases hcases with h | h | h | h <;> omega)
  have hle9 : ∃ v : V, G.degree v ≤ 9 := by
    rcases hcases with h10 | h12 | h14 | h16
    · obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
      have hlt : G.degree v < Fintype.card V := G.degree_lt_card_verts v
      exact ⟨v, by omega⟩
    · exact nu_eq_12_upper h12 hmin
    · exact nu_eq_14_upper h14 hmin
    · exact nu_eq_16_upper h16 hmin
  have hbip5 : IsBipartite G → ∃ v : V, G.degree v = 5 :=
    bipartite_min_4ext_deg_five hcard hconn hmin
  have h10spec : Fintype.card V = 10 → (∃ v : V, G.degree v = 5) ∨ (∀ v : V, G.degree v = 9) := by
    intro h10
    by_cases h5 : ∃ v : V, G.degree v = 5
    · exact Or.inl h5
    · push Not at h5
      have hge6 : ∀ v : V, 6 ≤ G.degree v := fun v => by have := hge5 v; have := h5 v; omega
      exact Or.inr (nu_eq_10_ge_six_eq_nine h10 hmin.1 hge6)
  have h12not8 : Fintype.card V = 12 → ¬ ((∀ v : V, 8 ≤ G.degree v) ∧ ∃ v : V, G.degree v = 8) := by
    rintro h12 ⟨h8, v, hv8⟩
    exact nu_eq_12_not_eight h12 hmin.1 h8 ⟨v, hv8⟩
  exact ⟨hcases, hge5, hle9, hbip5, h10spec, h12not8⟩

/-- **Full Spectrum of `δ(G)` (`{5, 8, 9}`)**: Combining `lou_yu_k4_order_and_bounds` with
`hLouYu2004` (the `δ(G) ≥ κ(G) ≥ 2k = 8` degree consequence of Lou & Yu 2004 Theorem 2.1 for
non-bipartite `k`-extendable graphs on `ν ≤ 4k` vertices), the minimum degree of `G` belongs
to `{5, 8, 9}`. -/
theorem lou_yu_k4_minDegree_spectrum {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcard : Fintype.card V ≤ 16) (hconn : G.Connected)
    (hmin : IsMinimallyKExtendable G 4)
    (hLouYu2004 : ¬ IsBipartite G → ∀ v : V, 8 ≤ G.degree v) :
    ∃ v : V, (∀ w : V, G.degree v ≤ G.degree w) ∧
      (G.degree v = 5 ∨ G.degree v = 8 ∨ G.degree v = 9) := by
  obtain ⟨hcases, hge5, hle9, hbip5, _, _⟩ := lou_yu_k4_order_and_bounds hcard hconn hmin
  by_cases hbip : IsBipartite G
  · obtain ⟨v, hv5⟩ := hbip5 hbip
    exact ⟨v, fun w => by have := hge5 w; omega, Or.inl hv5⟩
  · have hge8 : ∀ w : V, 8 ≤ G.degree w := hLouYu2004 hbip
    by_cases h8 : ∃ v : V, G.degree v = 8
    · obtain ⟨v, hv8⟩ := h8
      exact ⟨v, fun w => by have := hge8 w; omega, Or.inr (Or.inl hv8)⟩
    · push Not at h8
      obtain ⟨v, hv9⟩ := hle9
      have hv_eq9 : G.degree v = 9 := by have := hge8 v; have := h8 v; omega
      exact ⟨v, fun w => by have := hge8 w; have := h8 w; omega, Or.inr (Or.inr hv_eq9)⟩

/-- **Sharpness / Attainability**: Every value `d ∈ {5, 8, 9}` is realized as the minimum degree
(in fact regular degree) of a connected minimally 4-extendable graph on `≤ 16` vertices. -/
theorem lou_yu_k4_attainability :
    (∃ (n : ℕ) (G : SimpleGraph (Fin n)), n ≤ 16 ∧ G.Connected ∧ IsMinimallyKExtendable G 4 ∧
      ∃ (_ : DecidableRel G.Adj), ∀ v : Fin n, G.degree v = 5) ∧
    (∃ (n : ℕ) (G : SimpleGraph (Fin n)), n ≤ 16 ∧ G.Connected ∧ IsMinimallyKExtendable G 4 ∧
      ∃ (_ : DecidableRel G.Adj), ∀ v : Fin n, G.degree v = 8) ∧
    (∃ (n : ℕ) (G : SimpleGraph (Fin n)), n ≤ 16 ∧ G.Connected ∧ IsMinimallyKExtendable G 4 ∧
      ∃ (_ : DecidableRel G.Adj), ∀ v : Fin n, G.degree v = 9) := by
  obtain ⟨hc5, hm5, hd5⟩ := witness_delta_5
  obtain ⟨hc8, hm8, hd8⟩ := witness_delta_8
  obtain ⟨hc9, hm9, hd9⟩ := witness_delta_9
  exact ⟨⟨10, graphK55, by omega, hc5, hm5, inferInstance, hd5⟩,
         ⟨16, graphG4, by omega, hc8, hm8, inferInstance, hd8⟩,
         ⟨10, ⊤, by omega, hc9, hm9, inferInstance, hd9⟩⟩

end MainTheorems

end LouYuK4
