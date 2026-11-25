import LouYuK4.SmallTutte

/-!
# Lou–Yu Conjecture for k = 4 at orders ν ∈ {10, 12, 14}

We prove (with zero sorry and zero custom axioms):
- `nu_eq_10_not_eight`: At `ν = 10`, any 4-extendable graph with `δ(G) ≥ 8` is complete (`δ = 9`).
- `nu_eq_12_not_eight`: At `ν = 12`, no 4-extendable graph has `δ(G) = 8`.
- `nu_eq_12_upper`: At `ν = 12`, any minimally 4-extendable graph has `δ(G) ≤ 9`.
- `nu_eq_14_upper`: At `ν = 14`, any minimally 4-extendable graph has `δ(G) ≤ 9`.
-/

open SimpleGraph Finset

namespace LouYuK4

section HelperLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
lemma induce_compl_eq_compl_induce (G : SimpleGraph V) (S : Set V) :
    (Gᶜ.induce S)ᶜ = G.induce S := by
  ext ⟨u, hu⟩ ⟨v, hv⟩
  simp only [SimpleGraph.compl_adj, SimpleGraph.induce_adj, ne_eq, Subtype.mk.injEq, not_and,
    Classical.not_not]
  exact ⟨fun h => h.2 h.1, fun h => ⟨h.ne, fun _ => h⟩⟩

omit [Fintype V] [DecidableEq V] in
lemma hasPM_induce_iff_compl (G : SimpleGraph V) (S : Finset V) :
    HasPM (G.induce (S : Set V)) ↔ HasPM ((Gᶜ.induce (S : Set V))ᶜ) := by
  rw [induce_compl_eq_compl_induce]

omit [Fintype V] [DecidableEq V] in
lemma card_coe_finset_set (S : Finset V) : Fintype.card (S : Set V) = S.card := by
  simp

omit [DecidableEq V] in
lemma degree_congr {H₁ H₂ : SimpleGraph V} [DecidableRel H₁.Adj] [DecidableRel H₂.Adj]
    (h : H₁ = H₂) (v : V) : H₁.degree v = H₂.degree v := by
  subst h
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext w
  simp [SimpleGraph.mem_neighborFinset]

lemma degree_add_compl_degree (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel Gᶜ.Adj]
    (v : V) : G.degree v + Gᶜ.degree v = Fintype.card V - 1 := by
  have hdisj : Disjoint (G.neighborFinset v) (Gᶜ.neighborFinset v) := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    rw [SimpleGraph.mem_neighborFinset] at hw1 hw2
    exact hw2.2 hw1
  have hun : G.neighborFinset v ∪ Gᶜ.neighborFinset v = Finset.univ.erase v := by
    ext w
    simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset, SimpleGraph.compl_adj,
      Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro (h | ⟨hne, _⟩)
      · exact h.ne.symm
      · exact hne.symm
    · intro hne
      by_cases h : G.Adj v w
      · exact Or.inl h
      · exact Or.inr ⟨hne.symm, h⟩
  have hc := congrArg Finset.card hun
  rw [Finset.card_union_of_disjoint hdisj, SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.card_neighborFinset_eq_degree, Finset.card_erase_of_mem (Finset.mem_univ v),
    Finset.card_univ] at hc
  exact hc

lemma compl_degree_le_of_degree_ge {G : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel Gᶜ.Adj]
    {d : ℕ} (h : ∀ v : V, d ≤ G.degree v) (v : V) :
    Gᶜ.degree v ≤ Fintype.card V - 1 - d := by
  have hsum := degree_add_compl_degree G v
  have hv := h v
  omega

lemma degree_induce_le (F : SimpleGraph V) [DecidableRel F.Adj] (S : Finset V)
    [DecidableRel (F.induce (S : Set V)).Adj] (v : (S : Set V)) :
    (F.induce (S : Set V)).degree v ≤ F.degree v.val := by
  classical
  have hsub : ((F.induce (S : Set V)).neighborFinset v).image Subtype.val ⊆ F.neighborFinset v.val := by
    intro w hw
    rw [Finset.mem_image] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    rw [SimpleGraph.mem_neighborFinset] at hu ⊢
    exact hu
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Subtype.val_injective,
    SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree] at hcard
  exact hcard

omit [DecidableEq V] in
lemma card_adj_pairs (H : SimpleGraph V) [DecidableRel H.Adj] :
    (Finset.univ.filter fun p : V × V => H.Adj p.1 p.2).card = ∑ u : V, H.degree u := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.card_filter]
  have hfeq : Finset.univ.filter (fun v : V => H.Adj u v) = H.neighborFinset u := by
    ext v; simp [SimpleGraph.mem_neighborFinset]
  rw [hfeq, SimpleGraph.card_neighborFinset_eq_degree]

omit [Fintype V] [DecidableEq V] in
lemma compl_deleteEdges_singleton {G : SimpleGraph V} {u v : V} (huv : G.Adj u v) :
    (G.deleteEdges {s(u, v)})ᶜ = Gᶜ ⊔ SimpleGraph.edge u v := by
  ext x y
  simp only [SimpleGraph.compl_adj, SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff,
    SimpleGraph.sup_adj, SimpleGraph.edge_adj]
  constructor
  · rintro ⟨hne, h⟩
    by_cases hadj : G.Adj x y
    · right
      have heq : s(x, y) = s(u, v) := by
        by_contra hne'
        exact h ⟨hadj, hne'⟩
      rw [Sym2.eq_iff] at heq
      refine ⟨?_, hne⟩
      rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨hne, hadj⟩
  · rintro (⟨hne, hna⟩ | ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, hne⟩)
    · exact ⟨hne, fun h => hna h.1⟩
    · exact ⟨huv.ne, fun h => h.2 rfl⟩
    · exact ⟨huv.ne.symm, fun h => h.2 Sym2.eq_swap⟩

omit [Fintype V] [DecidableEq V] in
lemma sup_edge_adj_iff {F : SimpleGraph V} {u v x y : V} :
    (F ⊔ SimpleGraph.edge u v).Adj x y ↔ F.Adj x y ∨ ((x = u ∧ y = v) ∨ (x = v ∧ y = u)) ∧ x ≠ y := by
  simp [SimpleGraph.sup_adj, SimpleGraph.edge_adj]

/-- If `Gᶜ` has max degree `≤ 3`, then every 8-set `W` has `HasPM (G.induce W)`. -/
lemma hasPM_induce_eight_of_compl_le_three {G : SimpleGraph V} [DecidableRel Gᶜ.Adj]
    (hdeg : ∀ v : V, Gᶜ.degree v ≤ 3) {W : Finset V} (hW : W.card = 8) :
    HasPM (G.induce (W : Set V)) := by
  classical
  rw [hasPM_induce_iff_compl]
  refine hasPM_eight_of_compl_le_three (X := Gᶜ.induce (W : Set V)) ?_ ?_
  · rw [card_coe_finset_set, hW]
  · intro w
    exact le_trans (degree_induce_le Gᶜ W w) (hdeg w.val)

omit [Fintype V] in
lemma not_hasPM_pair_of_not_adj {G : SimpleGraph V} {u v : V} (hna : ¬ G.Adj u v) :
    ¬ HasPM (G.induce (({u, v} : Finset V) : Set V)) := by
  rintro ⟨P, hPM, hPspan⟩
  obtain ⟨⟨w, hw⟩, hadj, _⟩ := hPM (hPspan ⟨u, by simp⟩)
  have hGadj : G.Adj u w := hadj.adj_sub
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl
  · exact hGadj.ne rfl
  · exact hna hGadj

omit [Fintype V] [DecidableEq V] in
lemma not_hasPM_of_isolated {G : SimpleGraph V} {S : Finset V} {v : V} (hv : v ∈ S)
    (hiso : ∀ w ∈ S, ¬ G.Adj v w) :
    ¬ HasPM (G.induce (S : Set V)) := by
  rintro ⟨P, hPM, hPspan⟩
  obtain ⟨⟨w, hw⟩, hadj, _⟩ := hPM (hPspan ⟨v, hv⟩)
  exact hiso w hw hadj.adj_sub

omit [Fintype V] in
/-- If `Gᶜ` has a clique `Q` inside `S` with `2 * Q.card > S.card`, then `G.induce S` has no PM. -/
lemma not_hasPM_of_compl_clique {G : SimpleGraph V} {S Q : Finset V}
    (hQS : Q ⊆ S) (hbig : S.card < 2 * Q.card) (hcl : Gᶜ.IsClique (Q : Set V)) :
    ¬ HasPM (G.induce (S : Set V)) := by
  classical
  rintro ⟨P, hPM, hPspan⟩
  choose f hf using fun q : Q => hPM (hPspan ⟨q.val, hQS q.property⟩)
  have hfmem : ∀ q : Q, (f q).val ∈ S \ Q := by
    intro q
    rw [Finset.mem_sdiff]
    refine ⟨(f q).property, fun hq' => ?_⟩
    have hGadj : G.Adj q.val (f q).val := (hf q).1.adj_sub
    have hne : q.val ≠ (f q).val := hGadj.ne
    have hcadj : Gᶜ.Adj q.val (f q).val := hcl q.property hq' hne
    exact hcadj.2 hGadj
  have hfinj : Function.Injective (fun q : Q => (f q).val) := by
    intro q₁ q₂ heq
    have hf_eq : f q₁ = f q₂ := Subtype.ext heq
    have h1 := (hf q₁).1
    have h2 := (hf q₂).1
    rw [hf_eq] at h1
    have hsub := hPM.eq_of_adj_right h1 h2
    exact Subtype.ext (congrArg (fun x : (S : Set V) => x.val) hsub)
  have hle : Q.card ≤ (S \ Q).card := by
    have hsub : Finset.univ.image (fun q : Q => (f q).val) ⊆ S \ Q := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨q, _, rfl⟩ := hx
      exact hfmem q
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_coe] at hc
    exact hc
  rw [Finset.card_sdiff_of_subset hQS] at hle
  omega

omit [Fintype V] in
/-- If `S = A ∪ B` with `A, B` disjoint, `Odd A.card`, and `A` completely joined to `B` in `Gᶜ`
(so no `G`-edge crosses between `A` and `B`), then `G.induce S` has no PM. -/
lemma not_hasPM_of_compl_bip {G : SimpleGraph V} {S A B : Finset V}
    (hS : S = A ∪ B) (hAodd : Odd A.card)
    (hadj : ∀ u ∈ A, ∀ v ∈ B, Gᶜ.Adj u v) :
    ¬ HasPM (G.induce (S : Set V)) := by
  classical
  rintro ⟨P, hPM, hPspan⟩
  let PA : (G.induce (A : Set V)).Subgraph := {
    verts := Set.univ
    Adj := fun u v => P.Adj ⟨u.val, by rw [Finset.mem_coe, hS]; exact Finset.mem_union_left B u.property⟩
      ⟨v.val, by rw [Finset.mem_coe, hS]; exact Finset.mem_union_left B v.property⟩
    adj_sub := fun h => h.adj_sub
    edge_vert := fun _ => Set.mem_univ _
    symm := ⟨fun _ _ h => h.symm⟩
  }
  have hPA : PA.IsPerfectMatching := by
    refine ⟨?_, fun _ => Set.mem_univ _⟩
    intro ⟨u, hu⟩ _
    obtain ⟨⟨w, hw⟩, hPuw, huniq⟩ := hPM (hPspan ⟨u, by rw [Finset.mem_coe, hS]; exact Finset.mem_union_left B hu⟩)
    have hwA : w ∈ A := by
      rw [Finset.mem_coe, hS, Finset.mem_union] at hw
      rcases hw with hwA | hwB
      · exact hwA
      · exact absurd hPuw.adj_sub (hadj u hu w hwB).2
    refine ⟨⟨w, hwA⟩, hPuw, ?_⟩
    intro ⟨z, hz⟩ hPuz
    have hsub := huniq ⟨z, by rw [Finset.mem_coe, hS]; exact Finset.mem_union_left B hz⟩ hPuz
    exact Subtype.ext (congrArg (fun x : (S : Set V) => x.val) hsub)
  have heven : Even (Fintype.card (A : Set V)) := hPA.even_card
  rw [card_coe_finset_set] at heven
  obtain ⟨k, hk⟩ := heven
  obtain ⟨j, hj⟩ := hAodd
  omega

/-- Degree of `x` in `F ⊔ edge u v` is `≤ F.degree x + 1`, and `≤ F.degree x` if `x ∉ {u, v}`. -/
lemma degree_sup_edge_le (F : SimpleGraph V) [DecidableRel F.Adj] (u v x : V)
    [DecidableRel (F ⊔ SimpleGraph.edge u v).Adj] :
    (F ⊔ SimpleGraph.edge u v).degree x ≤ F.degree x + (if x = u ∨ x = v then 1 else 0) := by
  classical
  by_cases hx : x = u ∨ x = v
  · simp only [hx, ↓reduceIte]
    rcases hx with rfl | rfl
    · have hsub : (F ⊔ SimpleGraph.edge x v).neighborFinset x ⊆ insert v (F.neighborFinset x) := by
        intro w hw
        rw [SimpleGraph.mem_neighborFinset, sup_edge_adj_iff] at hw
        rw [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
        rcases hw with h | ⟨⟨_, h2⟩ | ⟨h1, h2⟩, hne⟩
        · exact Or.inr h
        · exact Or.inl h2
        · exact absurd h2.symm hne
      have hc := Finset.card_le_card hsub
      rw [SimpleGraph.card_neighborFinset_eq_degree] at hc
      exact le_trans hc (by simpa [SimpleGraph.card_neighborFinset_eq_degree] using Finset.card_insert_le v (F.neighborFinset x))
    · have hsub : (F ⊔ SimpleGraph.edge u x).neighborFinset x ⊆ insert u (F.neighborFinset x) := by
        intro w hw
        rw [SimpleGraph.mem_neighborFinset, sup_edge_adj_iff] at hw
        rw [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
        rcases hw with h | ⟨⟨h1, h2⟩ | ⟨_, h2⟩, hne⟩
        · exact Or.inr h
        · exact absurd h2.symm hne
        · exact Or.inl h2
      have hc := Finset.card_le_card hsub
      rw [SimpleGraph.card_neighborFinset_eq_degree] at hc
      exact le_trans hc (by simpa [SimpleGraph.card_neighborFinset_eq_degree] using Finset.card_insert_le u (F.neighborFinset x))
  · simp only [hx, ↓reduceIte, add_zero]
    push Not at hx
    have hsub : (F ⊔ SimpleGraph.edge u v).neighborFinset x ⊆ F.neighborFinset x := by
      intro w hw
      rw [SimpleGraph.mem_neighborFinset, sup_edge_adj_iff] at hw
      rw [SimpleGraph.mem_neighborFinset]
      rcases hw with h | ⟨⟨h1, _⟩ | ⟨h1, _⟩, _⟩
      · exact h
      · exact absurd h1 hx.1
      · exact absurd h1 hx.2
    have hc := Finset.card_le_card hsub
    rw [SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree] at hc
    exact hc

end HelperLemmas

section Order10And12

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Order ν = 10**: Any 4-extendable graph on 10 vertices with `δ(G) ≥ 8` is complete (`δ = 9`). -/
theorem nu_eq_10_not_eight {G : SimpleGraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 10) (hext : IsKExtendable G 4)
    (hdeg : ∀ v : V, 8 ≤ G.degree v) : ∀ v : V, G.degree v = 9 := by
  classical
  have hcdeg : ∀ v : V, Gᶜ.degree v ≤ 1 := fun v => by
    have := compl_degree_le_of_degree_ge hdeg v; omega
  intro v
  by_contra hne9
  have hlt : G.degree v < 9 := by
    have := G.degree_lt_card_verts v; omega
  have hcd : 1 ≤ Gᶜ.degree v := by
    have := degree_add_compl_degree G v; omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (by rw [SimpleGraph.card_neighborFinset_eq_degree]; omega : 0 < (Gᶜ.neighborFinset v).card)
  rw [SimpleGraph.mem_neighborFinset, SimpleGraph.compl_adj] at hu
  let S : Finset V := {v, u}
  have hScard : S.card = 2 := Finset.card_pair hu.1
  let W : Finset V := Sᶜ
  have hWcard : W.card = 8 := by rw [Finset.card_compl, hV, hScard]
  have hWpm : HasPM (G.induce (W : Set V)) :=
    hasPM_induce_eight_of_compl_le_three (fun x => le_trans (hcdeg x) (by omega)) hWcard
  have hSpm : HasPM (G.induce (S : Set V)) := by
    have h1 := ((isKExtendable_iff_compl_pm.mp hext).2 W hWcard hWpm)
    have hWc : Wᶜ = S := compl_compl S
    rwa [hWc] at h1
  exact not_hasPM_pair_of_not_adj hu.2 hSpm

/-- **Order ν = 12 (no δ = 8)**: No 4-extendable graph on 12 vertices has `δ(G) = 8`. -/
theorem nu_eq_12_not_eight {G : SimpleGraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 12) (hext : IsKExtendable G 4)
    (hdeg : ∀ v : V, 8 ≤ G.degree v) (hex8 : ∃ v : V, G.degree v = 8) : False := by
  classical
  have hcdeg : ∀ v : V, Gᶜ.degree v ≤ 3 := fun v => by
    have := compl_degree_le_of_degree_ge hdeg v; omega
  obtain ⟨v, hv8⟩ := hex8
  have hv3 : Gᶜ.degree v = 3 := by
    have := degree_add_compl_degree G v; omega
  let S : Finset V := insert v (Gᶜ.neighborFinset v)
  have hvn : v ∉ Gᶜ.neighborFinset v := by simp
  have hScard : S.card = 4 := by
    rw [Finset.card_insert_of_notMem hvn, SimpleGraph.card_neighborFinset_eq_degree, hv3]
  let W : Finset V := Sᶜ
  have hWcard : W.card = 8 := by rw [Finset.card_compl, hV, hScard]
  have hWpm : HasPM (G.induce (W : Set V)) := hasPM_induce_eight_of_compl_le_three hcdeg hWcard
  have hSpm : HasPM (G.induce (S : Set V)) := by
    have h1 := ((isKExtendable_iff_compl_pm.mp hext).2 W hWcard hWpm)
    have hWc : Wᶜ = S := compl_compl S
    rwa [hWc] at h1
  refine not_hasPM_of_isolated (S := S) (v := v) (by simp [S]) ?_ hSpm
  intro w hw
  simp only [S, Finset.mem_insert, SimpleGraph.mem_neighborFinset, SimpleGraph.compl_adj] at hw
  rcases hw with rfl | ⟨_, hna⟩
  · exact fun h => h.ne rfl
  · exact hna

/-- **Order ν = 12 (upper bound)**: Any minimally 4-extendable graph on 12 vertices has `δ(G) ≤ 9`. -/
theorem nu_eq_12_upper {G : SimpleGraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 12) (hmin : IsMinimallyKExtendable G 4) :
    ∃ v : V, G.degree v ≤ 9 := by
  classical
  by_contra hge10
  push Not at hge10
  have hcdeg : ∀ v : V, Gᶜ.degree v ≤ 1 := fun v => by
    have h1 := compl_degree_le_of_degree_ge (G := G) (d := 10) (fun x => by have := hge10 x; omega) v
    omega
  obtain ⟨u⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; have := hge10 u; omega : 0 < (G.neighborFinset u).card)
  rw [SimpleGraph.mem_neighborFinset] at hv
  let e : Sym2 V := s(u, v)
  have he : e ∈ G.edgeSet := hv
  let G' := G.deleteEdges {e}
  have hG'c : G'ᶜ = Gᶜ ⊔ SimpleGraph.edge u v := compl_deleteEdges_singleton hv
  have hdegG'c : ∀ x : V, G'ᶜ.degree x ≤ 2 := fun x => by
    rw [degree_congr hG'c x]
    have h1 := degree_sup_edge_le Gᶜ u v x
    have h2 := hcdeg x
    split_ifs at h1 <;> omega
  -- G'ᶜ is triangle-free since Gᶜ has max degree ≤ 1!
  have hnoK3 : ∀ a b c : V, G'ᶜ.Adj a b → G'ᶜ.Adj b c → G'ᶜ.Adj a c → False := by
    intro a b c hab hbc hac
    have hne_ab : a ≠ b := hab.ne
    have hne_bc : b ≠ c := hbc.ne
    have hne_ac : a ≠ c := hac.ne
    rw [hG'c, sup_edge_adj_iff] at hab hbc hac
    have hcases : (Gᶜ.Adj a b ∧ Gᶜ.Adj a c) ∨ (Gᶜ.Adj a b ∧ Gᶜ.Adj b c) ∨ (Gᶜ.Adj a c ∧ Gᶜ.Adj b c) := by
      rcases hab with hab | ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩
      · rcases hbc with hbc | ⟨⟨h1, h2⟩ | ⟨h1, h2⟩, _⟩
        · exact Or.inr (Or.inl ⟨hab, hbc⟩)
        · rcases hac with hac | ⟨⟨h3, h4⟩ | ⟨h3, h4⟩, _⟩
          · exact Or.inl ⟨hab, hac⟩
          · exact absurd (h3.trans h1.symm) hne_ab
          · exact absurd (h4.trans h1.symm) hne_bc.symm
        · rcases hac with hac | ⟨⟨h3, h4⟩ | ⟨h3, h4⟩, _⟩
          · exact Or.inl ⟨hab, hac⟩
          · exact absurd (h4.trans h1.symm) hne_bc.symm
          · exact absurd (h3.trans h1.symm) hne_ab
      · rcases hbc with hbc | ⟨⟨h1, h2⟩ | ⟨h1, h2⟩, _⟩
        · rcases hac with hac | ⟨⟨h3, h4⟩ | ⟨h3, h4⟩, _⟩
          · exact Or.inr (Or.inr ⟨hac, hbc⟩)
          · exact absurd h4.symm hne_bc
          · exact absurd h3.symm hne_ab.symm
        · exact absurd h1 hne_ab.symm
        · exact absurd h2 hne_ac.symm
      · rcases hbc with hbc | ⟨⟨h1, h2⟩ | ⟨h1, h2⟩, _⟩
        · rcases hac with hac | ⟨⟨h3, h4⟩ | ⟨h3, h4⟩, _⟩
          · exact Or.inr (Or.inr ⟨hac, hbc⟩)
          · exact absurd h3.symm hne_ab.symm
          · exact absurd h4.symm hne_bc
        · exact absurd h2 hne_ac.symm
        · exact absurd h1 hne_ab.symm
    have hdeg2 : ∀ x y z : V, y ≠ z → Gᶜ.Adj x y → Gᶜ.Adj x z → False := by
      intro x y z hyz hxy hxz
      have hsub : ({y, z} : Finset V) ⊆ Gᶜ.neighborFinset x := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rw [SimpleGraph.mem_neighborFinset]
        rcases hw with rfl | rfl <;> assumption
      have hc := Finset.card_le_card hsub
      rw [Finset.card_pair hyz, SimpleGraph.card_neighborFinset_eq_degree] at hc
      have := hcdeg x; omega
    rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hdeg2 a b c hne_bc h1 h2
    · exact hdeg2 b a c hne_ac h1.symm h2
    · exact hdeg2 c a b hne_ab h1.symm h2.symm
  have hG'ext : IsKExtendable G' 4 := by
    refine isKExtendable_of_forall_card_pm ?_ ?_
    · obtain ⟨W, _, hW8⟩ := Finset.exists_subset_card_eq (s := Finset.univ) (by rw [Finset.card_univ, hV]; omega : 8 ≤ (Finset.univ : Finset V).card)
      exact ⟨W, hW8, hasPM_induce_eight_of_compl_le_three (fun x => le_trans (hdegG'c x) (by omega)) hW8⟩
    · intro T hT
      have hT4 : T.card = 4 := by omega
      rw [hasPM_induce_iff_compl]
      by_contra hno
      have hbad := not_hasPM_four (X := G'ᶜ.induce (T : Set V)) (by rw [card_coe_finset_set, hT4]) hno
      rcases hbad with ⟨Q, hQ3, hQcl⟩ | ⟨w, hw3⟩
      · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hQ3
        exact hnoK3 a.val b.val c.val
          (hQcl (by simp) (by simp) hab)
          (hQcl (by simp) (by simp) hbc)
          (hQcl (by simp) (by simp) hac)
      · have h1 := degree_induce_le G'ᶜ T w
        have h2 := hdegG'c w.val
        omega
  exact hmin.2 e he hG'ext

end Order10And12

section Order14

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Adapted from Gan–Huang Lemma 5.9 (`k = 4` analogue, via `exists_tutte_odd_partition`)**:
Suppose `F` has `Δ(F) ≤ 3`, no `K₄`, and no `K₃,₃`. If `u ≠ v`, `¬ F.Adj u v`, and `S` is a
6-set containing `u, v` such that `((F ⊔ edge u v).induce S)ᶜ` has no PM, then one of:
1. `K₄ - uv`,
2. degree-3 open twins `u, v`,
3. `K₃,₃ - uv`. -/
lemma obstructed_edge_six_cases {F : SimpleGraph V} [DecidableRel F.Adj]
    (hdeg : ∀ w : V, F.degree w ≤ 3)
    (hnoK4 : ¬ HasClique F 4) (hnoK33 : ¬ HasK F 3 3)
    {u v : V} (huv : u ≠ v)
    {S : Finset V} (hS : S.card = 6)
    (hnoPM : ¬ HasPM (((F ⊔ SimpleGraph.edge u v).induce (S : Set V))ᶜ)) :
    (∃ p q : V, F.Adj p q ∧ F.Adj p u ∧ F.Adj p v ∧ F.Adj q u ∧ F.Adj q v) ∨
    (F.degree u = 3 ∧ F.degree v = 3 ∧ F.neighborFinset u = F.neighborFinset v) ∨
    (∃ A B : Finset V, u ∈ A ∧ v ∈ B ∧ A.card = 3 ∧ B.card = 3 ∧ Disjoint A B ∧
      ∀ x ∈ A, ∀ y ∈ B, (x = u ∧ y = v) ∨ F.Adj x y) := by
  classical
  let X := (F ⊔ SimpleGraph.edge u v).induce (S : Set V)
  have hXdeg : ∀ x : (S : Set V), X.degree x ≤ 3 + (if x.val = u ∨ x.val = v then 1 else 0) := fun x =>
    le_trans (degree_induce_le (F ⊔ SimpleGraph.edge u v) S x)
      (le_trans (degree_sup_edge_le F u v x.val) (by have := hdeg x.val; split_ifs <;> omega))
  have hXdeg4 : ∀ x : (S : Set V), X.degree x ≤ 4 := fun x => by
    have := hXdeg x; split_ifs at this <;> omega
  have hcompl : (Xᶜ)ᶜ = X := compl_compl X
  have hScard : Fintype.card (S : Set V) = 6 := by rw [card_coe_finset_set, hS]
  obtain ⟨B, C, hB2, hCodd, hCdisj, hCpair, hsum, hadj⟩ :=
    exists_tutte_odd_partition (H := Xᶜ) (by rw [hScard]; exact ⟨3, rfl⟩) hnoPM
  rw [hcompl] at hadj
  have hCge : C.card ≤ ∑ c ∈ C, c.card := by
    calc C.card = ∑ _c ∈ C, 1 := by simp
      _ ≤ ∑ c ∈ C, c.card := Finset.sum_le_sum fun c hc => by
        obtain ⟨k, hk⟩ := hCodd c hc; omega
  have hCne : ∀ c ∈ C, c.Nonempty := fun c hc =>
    Finset.card_pos.mp (by obtain ⟨k, hk⟩ := hCodd c hc; omega)
  have hCadj : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → ∀ x ∈ c₁, ∀ y ∈ c₂, X.Adj x y :=
    fun c₁ hc₁ c₂ hc₂ hne x hx y hy =>
      hadj c₁ hc₁ x hx y (Finset.disjoint_left.mp (hCdisj c₂ hc₂) hy)
        (Finset.disjoint_right.mp (hCpair hc₁ hc₂ hne) hy)
  have hBbound : B.card ≤ 2 := by omega
  interval_cases hBc : B.card
  · -- |B| = 0 => K₃,₃ - uv
    have hge3 : ∀ c ∈ C, 3 ≤ c.card := by
      intro c hc
      obtain ⟨w, hw⟩ := hCne c hc
      have h1 := card_compl_sub_le_deg_of_tutte (X := X) hw (hCdisj c hc) (hadj c hc w hw)
      have h2 := hXdeg4 w
      obtain ⟨k, hk⟩ := hCodd c hc
      rw [hScard, hBc] at h1
      omega
    have hC2 : C.card = 2 := by
      have : 3 * C.card ≤ ∑ c ∈ C, c.card := by
        calc 3 * C.card = ∑ _c ∈ C, 3 := by simp [mul_comm]
          _ ≤ ∑ c ∈ C, c.card := Finset.sum_le_sum hge3
      omega
    obtain ⟨c₁, c₂, hcne, hCeq⟩ := Finset.card_eq_two.mp hC2
    have hc₁ : c₁ ∈ C := by rw [hCeq]; simp
    have hc₂ : c₂ ∈ C := by rw [hCeq]; simp
    have hsum2 : c₁.card + c₂.card ≤ 6 := by rw [hCeq, Finset.sum_pair hcne] at hsum; omega
    have hc₁3 : c₁.card = 3 := by have := hge3 c₁ hc₁; have := hge3 c₂ hc₂; omega
    have hc₂3 : c₂.card = 3 := by have := hge3 c₁ hc₁; have := hge3 c₂ hc₂; omega
    let A₁ : Finset V := c₁.image Subtype.val
    let A₂ : Finset V := c₂.image Subtype.val
    have hA₁3 : A₁.card = 3 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hc₁3]
    have hA₂3 : A₂.card = 3 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hc₂3]
    have hdisj12 : Disjoint A₁ A₂ := by
      rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      rw [Finset.mem_image] at hx₁ hx₂
      obtain ⟨a, ha, rfl⟩ := hx₁
      obtain ⟨b, hb, hval⟩ := hx₂
      have hab : b = a := Subtype.ext hval
      exact Finset.disjoint_left.mp (hCpair hc₁ hc₂ hcne) ha (hab ▸ hb)
    have hcross : ∀ x ∈ A₁, ∀ y ∈ A₂, (F ⊔ SimpleGraph.edge u v).Adj x y := by
      intro x hx y hy
      rw [Finset.mem_image] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact hCadj c₁ hc₁ c₂ hc₂ hcne a ha b hb
    by_cases h1 : u ∈ A₁ ∧ v ∈ A₂
    · refine Or.inr (Or.inr ⟨A₁, A₂, h1.1, h1.2, hA₁3, hA₂3, hdisj12, fun x hx y hy => ?_⟩)
      have hxy := hcross x hx y hy
      rw [sup_edge_adj_iff] at hxy
      rcases hxy with hF | ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩
      · exact Or.inr hF
      · exact Or.inl ⟨rfl, rfl⟩
      · exact absurd h1.1 (Finset.disjoint_right.mp hdisj12 hy)
    · by_cases h2 : u ∈ A₂ ∧ v ∈ A₁
      · refine Or.inr (Or.inr ⟨A₂, A₁, h2.1, h2.2, hA₂3, hA₁3, hdisj12.symm, fun x hx y hy => ?_⟩)
        have hxy := (hcross y hy x hx).symm
        rw [sup_edge_adj_iff] at hxy
        rcases hxy with hF | ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩
        · exact Or.inr hF
        · exact Or.inl ⟨rfl, rfl⟩
        · exact absurd h2.1 (Finset.disjoint_left.mp hdisj12 hy)
      · exfalso
        refine hnoK33 ⟨A₁, A₂, hA₁3, hA₂3, hdisj12, fun x hx y hy => ?_⟩
        have hxy := hcross x hx y hy
        rw [sup_edge_adj_iff] at hxy
        rcases hxy with hF | ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩
        · exact hF
        · exact absurd ⟨hx, hy⟩ h1
        · exact absurd ⟨hy, hx⟩ h2
  · -- |B| = 1 => deg-3 open twins u, v
    let C1 := C.filter (fun c => c.card = 1)
    let C3 := C.filter (fun c => 3 ≤ c.card)
    have hdisj13 : Disjoint C1 C3 := by
      rw [Finset.disjoint_left]; intro c h1 h3
      simp only [C1, C3, Finset.mem_filter] at h1 h3; omega
    have hun13 : C1 ∪ C3 = C := by
      ext c; simp only [C1, C3, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro hc; obtain ⟨k, hk⟩ := hCodd c hc; by_cases hk0 : k = 0
        · left; exact ⟨hc, by omega⟩
        · right; exact ⟨hc, by omega⟩
    have hpart : C1.card + C3.card = C.card := by
      rw [← Finset.card_union_of_disjoint hdisj13, hun13]
    have hsum_lb : C1.card + 3 * C3.card ≤ 5 := by
      have h1 : C1.card ≤ ∑ c ∈ C1, c.card := by
        calc C1.card = ∑ _c ∈ C1, 1 := by simp
          _ ≤ ∑ c ∈ C1, c.card := Finset.sum_le_sum fun c hc => by
            simp only [C1, Finset.mem_filter] at hc; omega
      have h3 : 3 * C3.card ≤ ∑ c ∈ C3, c.card := by
        calc 3 * C3.card = ∑ _c ∈ C3, 3 := by simp [mul_comm]
          _ ≤ ∑ c ∈ C3, c.card := Finset.sum_le_sum fun c hc => by
            simp only [C3, Finset.mem_filter] at hc; exact hc.2
      have htot : ∑ c ∈ C1, c.card + ∑ c ∈ C3, c.card = ∑ c ∈ C, c.card := by
        rw [← Finset.sum_union hdisj13, hun13]
      omega
    have hC1ge2 : 2 ≤ C1.card := by omega
    obtain ⟨D, hDsub, hD2⟩ := Finset.exists_subset_card_eq hC1ge2
    obtain ⟨c₁, c₂, hcne, hDeq⟩ := Finset.card_eq_two.mp hD2
    have hc₁ : c₁ ∈ C1 := hDsub (by rw [hDeq]; simp)
    have hc₂ : c₂ ∈ C1 := hDsub (by rw [hDeq]; simp)
    have hc₁C : c₁ ∈ C := (Finset.mem_filter.mp hc₁).1
    have hc₂C : c₂ ∈ C := (Finset.mem_filter.mp hc₂).1
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hc₁).2
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hc₂).2
    subst ha; subst hb
    have hab : a ≠ b := fun h => hcne (by simp [h])
    have ha4 : 4 ≤ X.degree a := by
      have h1 := card_compl_sub_le_deg_of_tutte (X := X) (v := a) (by simp) (hCdisj {a} hc₁C)
        (hadj {a} hc₁C a (by simp))
      simp only [hScard, hBc, Finset.card_singleton] at h1
      omega
    have hb4 : 4 ≤ X.degree b := by
      have h1 := card_compl_sub_le_deg_of_tutte (X := X) (v := b) (by simp) (hCdisj {b} hc₂C)
        (hadj {b} hc₂C b (by simp))
      simp only [hScard, hBc, Finset.card_singleton] at h1
      omega
    have hauv : a.val = u ∨ a.val = v := by
      by_contra h; have h1 := hXdeg a; simp only [h, ↓reduceIte] at h1; omega
    have hbuv : b.val = u ∨ b.val = v := by
      by_contra h; have h1 := hXdeg b; simp only [h, ↓reduceIte] at h1; omega
    have hab_val : a.val ≠ b.val := fun h => hab (Subtype.ext h)
    let R : Finset (S : Set V) := (B ∪ {a, b})ᶜ
    have haB : a ∉ B := Finset.disjoint_left.mp (hCdisj {a} hc₁C) (by simp)
    have hbB : b ∉ B := Finset.disjoint_left.mp (hCdisj {b} hc₂C) (by simp)
    have hdisjBab : Disjoint B {a, b} := by
      rw [Finset.disjoint_right]; intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hRcard : R.card = 3 := by
      simp only [R, Finset.card_compl, Finset.card_union_of_disjoint hdisjBab,
        hScard, hBc, Finset.card_pair hab]
    let RV : Finset V := R.image Subtype.val
    have hRVcard : RV.card = 3 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hRcard]
    have hRa : RV ⊆ F.neighborFinset a.val := by
      intro w hw
      rw [Finset.mem_image] at hw
      obtain ⟨z, hzR, rfl⟩ := hw
      simp only [R, Finset.mem_compl, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at hzR
      have hXaz : (F ⊔ SimpleGraph.edge u v).Adj a.val z.val :=
        hadj {a} hc₁C a (by simp) z hzR.1 (by simp [hzR.2.1])
      rw [sup_edge_adj_iff] at hXaz
      rw [SimpleGraph.mem_neighborFinset]
      have hz_ne_b : z.val ≠ b.val := fun h => hzR.2.2 (Subtype.ext h)
      rcases hXaz with hF | ⟨⟨h1, h2⟩ | ⟨h1, h2⟩, _⟩
      · exact hF
      · exfalso; rcases hbuv with hb' | hb'
        · exact hab_val (h1.trans hb'.symm)
        · exact hz_ne_b (h2.trans hb'.symm)
      · exfalso; rcases hbuv with hb' | hb'
        · exact hz_ne_b (h2.trans hb'.symm)
        · exact hab_val (h1.trans hb'.symm)
    have hRb : RV ⊆ F.neighborFinset b.val := by
      intro w hw
      rw [Finset.mem_image] at hw
      obtain ⟨z, hzR, rfl⟩ := hw
      simp only [R, Finset.mem_compl, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at hzR
      have hXbz : (F ⊔ SimpleGraph.edge u v).Adj b.val z.val :=
        hadj {b} hc₂C b (by simp) z hzR.1 (by simp [hzR.2.2])
      rw [sup_edge_adj_iff] at hXbz
      rw [SimpleGraph.mem_neighborFinset]
      have hz_ne_a : z.val ≠ a.val := fun h => hzR.2.1 (Subtype.ext h)
      rcases hXbz with hF | ⟨⟨h1, h2⟩ | ⟨h1, h2⟩, _⟩
      · exact hF
      · exfalso; rcases hauv with ha' | ha'
        · exact hab_val.symm (h1.trans ha'.symm)
        · exact hz_ne_a (h2.trans ha'.symm)
      · exfalso; rcases hauv with ha' | ha'
        · exact hz_ne_a (h2.trans ha'.symm)
        · exact hab_val.symm (h1.trans ha'.symm)
    have hda : F.degree a.val = 3 := by
      have h1 := Finset.card_le_card hRa
      rw [hRVcard, SimpleGraph.card_neighborFinset_eq_degree] at h1
      have := hdeg a.val; omega
    have hdb : F.degree b.val = 3 := by
      have h1 := Finset.card_le_card hRb
      rw [hRVcard, SimpleGraph.card_neighborFinset_eq_degree] at h1
      have := hdeg b.val; omega
    have hNa : F.neighborFinset a.val = RV :=
      (Finset.eq_of_subset_of_card_le hRa (by rw [SimpleGraph.card_neighborFinset_eq_degree, hda, hRVcard])).symm
    have hNb : F.neighborFinset b.val = RV :=
      (Finset.eq_of_subset_of_card_le hRb (by rw [SimpleGraph.card_neighborFinset_eq_degree, hdb, hRVcard])).symm
    refine Or.inr (Or.inl ?_)
    rcases hauv with ha' | ha' <;> rcases hbuv with hb' | hb'
    · exact absurd (ha'.trans hb'.symm) hab_val
    · rw [← ha', ← hb']; exact ⟨hda, hdb, hNa.trans hNb.symm⟩
    · rw [← hb', ← ha']; exact ⟨hdb, hda, hNb.trans hNa.symm⟩
    · exact absurd (ha'.trans hb'.symm) hab_val
  · -- |B| = 2 => K₄ - uv
    have hK4X : HasClique X 4 := hasClique_of_disjoint_sets (D := C) (k := 4) (by omega) hCne hCpair hCadj
    obtain ⟨Q, hQ4, hQcl⟩ := hK4X
    let QV : Finset V := Q.image Subtype.val
    have hQV4 : QV.card = 4 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hQ4]
    have hQVcl : (F ⊔ SimpleGraph.edge u v).IsClique (QV : Set V) := by
      intro x hx y hy hxy
      rw [Finset.mem_coe, Finset.mem_image] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact hQcl ha hb (fun h => hxy (congrArg Subtype.val h))
    have huvQV : u ∈ QV ∧ v ∈ QV := by
      by_contra hnot
      refine hnoK4 ⟨QV, hQV4, fun x hx y hy hxy => ?_⟩
      have hclxy := hQVcl hx hy hxy
      rw [sup_edge_adj_iff] at hclxy
      rcases hclxy with hF | ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩
      · exact hF
      · exact absurd ⟨hx, hy⟩ hnot
      · exact absurd ⟨hy, hx⟩ hnot
    let P2 : Finset V := (QV.erase u).erase v
    have hv_er : v ∈ QV.erase u := Finset.mem_erase.mpr ⟨huv.symm, huvQV.2⟩
    have hP2card : P2.card = 2 := by
      rw [Finset.card_erase_of_mem hv_er, Finset.card_erase_of_mem huvQV.1, hQV4]
    obtain ⟨p, q, hpq, hP2eq⟩ := Finset.card_eq_two.mp hP2card
    have hp : p ∈ P2 := by rw [hP2eq]; simp
    have hq : q ∈ P2 := by rw [hP2eq]; simp
    have hpQV : p ∈ QV := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp)
    have hqQV : q ∈ QV := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hq)
    have hpv : p ≠ v := (Finset.mem_erase.mp hp).1
    have hpu : p ≠ u := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hp)).1
    have hqv : q ≠ v := (Finset.mem_erase.mp hq).1
    have hqu : q ≠ u := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hq)).1
    have hF_of : ∀ x y : V, x ∈ QV → y ∈ QV → x ≠ y → ¬ (x = u ∧ y = v) → ¬ (x = v ∧ y = u) → F.Adj x y := by
      intro x y hx hy hxy h1 h2
      have hclxy := hQVcl hx hy hxy
      rw [sup_edge_adj_iff] at hclxy
      rcases hclxy with hF | ⟨h' | h', _⟩
      · exact hF
      · exact absurd h' h1
      · exact absurd h' h2
    exact Or.inl ⟨p, q,
      hF_of p q hpQV hqQV hpq (fun h => hpu h.1) (fun h => hpv h.1),
      hF_of p u hpQV huvQV.1 hpu (fun h => hpu h.1) (fun h => hpv h.1),
      hF_of p v hpQV huvQV.2 hpv (fun h => hpu h.1) (fun h => hpv h.1),
      hF_of q u hqQV huvQV.1 hqu (fun h => hqu h.1) (fun h => hqv h.1),
      hF_of q v hqQV huvQV.2 hqv (fun h => hqu h.1) (fun h => hqv h.1)⟩

/-- **Order ν = 14 (upper bound)**: Any minimally 4-extendable graph on 14 vertices has `δ(G) ≤ 9`.
Proof by global ordered-pair obstruction counting: `140 ≤ |Gpairs| ≤ 42 + 14 + 42 = 98`, contradiction. -/
theorem nu_eq_14_upper {G : SimpleGraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 14) (hmin : IsMinimallyKExtendable G 4) :
    ∃ v : V, G.degree v ≤ 9 := by
  classical
  by_contra hge10
  push Not at hge10
  let F := Gᶜ
  have hcdeg : ∀ v : V, F.degree v ≤ 3 := fun v => by
    have h1 := compl_degree_le_of_degree_ge (G := G) (d := 10) (fun x => by have := hge10 x; omega) v
    have h2 : F.degree v = Gᶜ.degree v := degree_congr rfl v
    omega
  have hall6 : ∀ S : Finset V, S.card = 6 → HasPM (G.induce (S : Set V)) := by
    intro S hS
    have hWcard : Sᶜ.card = 8 := by rw [Finset.card_compl, hV, hS]
    have hWpm := hasPM_induce_eight_of_compl_le_three hcdeg hWcard
    have h1 := (isKExtendable_iff_compl_pm.mp hmin.1).2 Sᶜ hWcard hWpm
    have hSc : (Sᶜ)ᶜ = S := compl_compl S
    rwa [hSc] at h1
  have hnoK4 : ¬ HasClique F 4 := by
    rintro ⟨Q, hQ4, hQcl⟩
    obtain ⟨R, hRsub, hR2⟩ := Finset.exists_subset_card_eq (s := Qᶜ)
      (by rw [Finset.card_compl, hV, hQ4]; omega : 2 ≤ Qᶜ.card)
    have hdisj : Disjoint Q R := Finset.disjoint_of_subset_right hRsub disjoint_compl_right
    have hS6 : (Q ∪ R).card = 6 := by rw [Finset.card_union_of_disjoint hdisj, hQ4, hR2]
    exact not_hasPM_of_compl_clique Finset.subset_union_left (by omega) hQcl (hall6 (Q ∪ R) hS6)
  have hnoK33 : ¬ HasK F 3 3 := by
    rintro ⟨A, B, hA3, hB3, hdisj, hadj⟩
    have hS6 : (A ∪ B).card = 6 := by rw [Finset.card_union_of_disjoint hdisj, hA3, hB3]
    exact not_hasPM_of_compl_bip rfl (by rw [hA3]; exact ⟨1, rfl⟩) hadj (hall6 (A ∪ B) hS6)
  let Gpairs : Finset (V × V) := Finset.univ.filter (fun p => G.Adj p.1 p.2)
  have hGpairs_card : 140 ≤ Gpairs.card := by
    rw [card_adj_pairs G]
    calc 140 = ∑ _u : V, 10 := by rw [Finset.sum_const, Finset.card_univ, hV]; rfl
      _ ≤ ∑ u : V, G.degree u := Finset.sum_le_sum fun u _ => by have := hge10 u; omega
  have hobs : ∀ p ∈ Gpairs,
      (∃ a b : V, F.Adj a b ∧ F.Adj a p.1 ∧ F.Adj a p.2 ∧ F.Adj b p.1 ∧ F.Adj b p.2) ∨
      (F.degree p.1 = 3 ∧ F.degree p.2 = 3 ∧ F.neighborFinset p.1 = F.neighborFinset p.2) ∨
      (∃ A B : Finset V, p.1 ∈ A ∧ p.2 ∈ B ∧ A.card = 3 ∧ B.card = 3 ∧ Disjoint A B ∧
        ∀ x ∈ A, ∀ y ∈ B, (x = p.1 ∧ y = p.2) ∨ F.Adj x y) := by
    rintro ⟨u, v⟩ hp
    simp only [Gpairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have he : s(u, v) ∈ G.edgeSet := hp
    have hnotext : ¬ IsKExtendable (G.deleteEdges {s(u, v)}) 4 := hmin.2 s(u, v) he
    have hG'c : (G.deleteEdges {s(u, v)})ᶜ = F ⊔ SimpleGraph.edge u v := compl_deleteEdges_singleton hp
    have hexW : ∃ W : Finset V, W.card = 8 ∧ HasPM ((G.deleteEdges {s(u, v)}).induce (W : Set V)) := by
      obtain ⟨W, hWsub, hW8⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset V).erase u)
        (by rw [Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, hV]; omega : 8 ≤ ((Finset.univ : Finset V).erase u).card)
      have huW : u ∉ W := fun h => (Finset.mem_erase.mp (hWsub h)).1 rfl
      have hsame : (G.deleteEdges {s(u, v)}).induce (W : Set V) = G.induce (W : Set V) := by
        ext ⟨x, hx⟩ ⟨y, hy⟩
        simp only [SimpleGraph.induce_adj, SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff,
          and_iff_left_iff_imp]
        intro _ heq
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨rfl, _⟩ | ⟨_, rfl⟩
        · exact huW hx
        · exact huW hy
      exact ⟨W, hW8, hsame ▸ hasPM_induce_eight_of_compl_le_three hcdeg hW8⟩
    have hbadS : ∃ S : Finset V, S.card = 6 ∧ ¬ HasPM ((G.deleteEdges {s(u, v)}).induce (S : Set V)) := by
      by_contra hall
      push Not at hall
      exact hnotext (isKExtendable_of_forall_card_pm hexW (fun T hT => hall T (by omega)))
    obtain ⟨S, hS6, hSnoPM⟩ := hbadS
    rw [hasPM_induce_iff_compl, hG'c] at hSnoPM
    exact obstructed_edge_six_cases hcdeg hnoK4 hnoK33 hp.ne hS6 hSnoPM
  have hFedges : F.edgeFinset.card ≤ 21 := by
    have hhs := F.sum_degrees_eq_twice_card_edges
    have hsum : ∑ v : V, F.degree v ≤ 42 :=
      calc ∑ v : V, F.degree v ≤ ∑ _v : V, 3 := Finset.sum_le_sum fun v _ => hcdeg v
        _ = 42 := by rw [Finset.sum_const, Finset.card_univ, hV]; rfl
    omega
  -- Bound 1: Type (i) ordered pairs ≤ 2 * F.edgeFinset.card ≤ 42
  let pairOf : Sym2 V → Finset (V × V) :=
    Sym2.lift ⟨fun a b => (F.neighborFinset a ∩ F.neighborFinset b).offDiag,
      fun a b => by dsimp only; rw [Finset.inter_comm]⟩
  let E1 : Finset (V × V) := F.edgeFinset.biUnion pairOf
  have hE1_card : E1.card ≤ 42 := by
    have h1 := Finset.card_biUnion_le (s := F.edgeFinset) (t := pairOf)
    have h2 : ∀ f ∈ F.edgeFinset, (pairOf f).card ≤ 2 := by
      intro f hf
      induction f using Sym2.ind with
      | _ a b =>
        simp only [pairOf, Sym2.lift_mk]
        have hab : F.Adj a b := SimpleGraph.mem_edgeFinset.mp hf
        have hsub : F.neighborFinset a ∩ F.neighborFinset b ⊆ (F.neighborFinset a).erase b := by
          intro x hx
          rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset] at hx
          rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset]
          exact ⟨hx.2.ne.symm, hx.1⟩
        have hbNa : b ∈ F.neighborFinset a := by rw [SimpleGraph.mem_neighborFinset]; exact hab
        have hle : (F.neighborFinset a ∩ F.neighborFinset b).card ≤ 2 := by
          have hc := Finset.card_le_card hsub
          rw [Finset.card_erase_of_mem hbNa, SimpleGraph.card_neighborFinset_eq_degree] at hc
          have := hcdeg a; omega
        rw [Finset.offDiag_card]
        set k := (F.neighborFinset a ∩ F.neighborFinset b).card
        interval_cases k <;> omega
    calc E1.card ≤ ∑ f ∈ F.edgeFinset, (pairOf f).card := h1
      _ ≤ ∑ _f ∈ F.edgeFinset, 2 := Finset.sum_le_sum h2
      _ = F.edgeFinset.card * 2 := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 42 := by omega
  have htwin_uniq : ∀ u v₁ v₂ : V, u ≠ v₁ → u ≠ v₂ →
      F.degree u = 3 → F.neighborFinset u = F.neighborFinset v₁ →
      F.neighborFinset u = F.neighborFinset v₂ → v₁ = v₂ := by
    intro u v₁ v₂ h1 h2 hdu hN1 hN2
    by_contra hne
    have hdisj : Disjoint ({u, v₁, v₂} : Finset V) (F.neighborFinset u) := by
      rw [Finset.disjoint_left]
      intro x hx hNu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx | hx
      · rw [hx] at hNu; exact ((SimpleGraph.mem_neighborFinset F u u).mp hNu).ne rfl
      · rw [hx, hN1] at hNu; exact ((SimpleGraph.mem_neighborFinset F v₁ v₁).mp hNu).ne rfl
      · rw [hx, hN2] at hNu; exact ((SimpleGraph.mem_neighborFinset F v₂ v₂).mp hNu).ne rfl
    refine hnoK33 ⟨{u, v₁, v₂}, F.neighborFinset u, ?_, ?_, hdisj, ?_⟩
    · rw [Finset.card_insert_of_notMem (by simp [h1, h2]), Finset.card_pair hne]
    · rw [SimpleGraph.card_neighborFinset_eq_degree, hdu]
    · intro x hx y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx | hx
      · rw [hx]; exact (SimpleGraph.mem_neighborFinset F u y).mp hy
      · rw [hx]; exact (SimpleGraph.mem_neighborFinset F v₁ y).mp (hN1 ▸ hy)
      · rw [hx]; exact (SimpleGraph.mem_neighborFinset F v₂ y).mp (hN2 ▸ hy)
  -- Bound 2: Type (ii) ordered pairs ≤ 14
  let E2 : Finset (V × V) := Gpairs.filter (fun p =>
    F.degree p.1 = 3 ∧ F.degree p.2 = 3 ∧ F.neighborFinset p.1 = F.neighborFinset p.2)
  have hE2_card : E2.card ≤ 14 := by
    have hinj : Set.InjOn Prod.fst (E2 : Set (V × V)) := by
      rintro ⟨u₁, v₁⟩ h₁ ⟨u₂, v₂⟩ h₂ heq
      simp only at heq
      subst heq
      simp only [Finset.mem_coe, E2, Gpairs, Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
      have hv : v₁ = v₂ := htwin_uniq u₁ v₁ v₂ h₁.1.ne h₂.1.ne h₁.2.1 h₁.2.2.2 h₂.2.2.2
      rw [hv]
    have hcard := Finset.card_image_of_injOn hinj
    rw [← hcard]
    exact le_trans (Finset.card_le_univ _) (by rw [hV])
  -- Bound 3: Type (iii) ordered pairs ≤ 42
  let E3 : Finset (V × V) := Gpairs.filter (fun p =>
    ∃ A B : Finset V, p.1 ∈ A ∧ p.2 ∈ B ∧ A.card = 3 ∧ B.card = 3 ∧ Disjoint A B ∧
      ∀ x ∈ A, ∀ y ∈ B, (x = p.1 ∧ y = p.2) ∨ F.Adj x y)
  let Fpairs : Finset (V × V) := Finset.univ.filter (fun p => F.Adj p.1 p.2)
  have hFpairs_card : Fpairs.card ≤ 42 := by
    rw [card_adj_pairs F]
    calc ∑ u : V, F.degree u ≤ ∑ _u : V, 3 := Finset.sum_le_sum fun u _ => hcdeg u
      _ = 42 := by rw [Finset.sum_const, Finset.card_univ, hV]; rfl
  have hE3_witness : ∀ p ∈ E3, ∃ a : V, (a, p.2) ∈ Fpairs ∧
      F.degree a = 3 ∧
      (∃ a' : V, a' ≠ a ∧ F.neighborFinset a' = F.neighborFinset a) ∧
      ∀ b ∈ (F.neighborFinset a).erase p.2, F.degree b = 3 ∧
        ∀ a' : V, a' ≠ a → F.neighborFinset a' = F.neighborFinset a →
          F.neighborFinset b = {p.1, a, a'} := by
    rintro ⟨u, v⟩ hp
    simp only [E3, Gpairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨_, A, B, huA, hvB, hA3, hB3, _, hcross⟩ := hp
    have hA2 : (A.erase u).card = 2 := by rw [Finset.card_erase_of_mem huA, hA3]
    obtain ⟨a, a', haa', hAeq⟩ := Finset.card_eq_two.mp hA2
    have haA : a ∈ A := Finset.mem_of_mem_erase (by rw [hAeq]; simp)
    have ha'A : a' ∈ A := Finset.mem_of_mem_erase (by rw [hAeq]; simp)
    have hau : a ≠ u := (Finset.mem_erase.mp (by rw [hAeq]; simp)).1
    have ha'u : a' ≠ u := (Finset.mem_erase.mp (by rw [hAeq]; simp)).1
    have hNa_sub : B ⊆ F.neighborFinset a := by
      intro y hy
      rw [SimpleGraph.mem_neighborFinset]
      rcases hcross a haA y hy with ⟨h1, _⟩ | hF
      · exact absurd h1 hau
      · exact hF
    have hNa'_sub : B ⊆ F.neighborFinset a' := by
      intro y hy
      rw [SimpleGraph.mem_neighborFinset]
      rcases hcross a' ha'A y hy with ⟨h1, _⟩ | hF
      · exact absurd h1 ha'u
      · exact hF
    have hda : F.degree a = 3 := by
      have hc := Finset.card_le_card hNa_sub
      rw [hB3, SimpleGraph.card_neighborFinset_eq_degree] at hc
      have := hcdeg a; omega
    have hda' : F.degree a' = 3 := by
      have hc := Finset.card_le_card hNa'_sub
      rw [hB3, SimpleGraph.card_neighborFinset_eq_degree] at hc
      have := hcdeg a'; omega
    have hNa : F.neighborFinset a = B :=
      (Finset.eq_of_subset_of_card_le hNa_sub (by rw [SimpleGraph.card_neighborFinset_eq_degree, hda, hB3])).symm
    have hNa' : F.neighborFinset a' = B :=
      (Finset.eq_of_subset_of_card_le hNa'_sub (by rw [SimpleGraph.card_neighborFinset_eq_degree, hda', hB3])).symm
    have hAfull : A = {u, a, a'} := by
      ext x
      constructor
      · intro hx
        by_cases hxu : x = u
        · simp [hxu]
        · have hx' : x ∈ A.erase u := Finset.mem_erase.mpr ⟨hxu, hx⟩
          rw [hAeq] at hx'
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx' ⊢
          tauto
      · intro hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
    refine ⟨a, ?_, hda, ⟨a', haa'.symm, hNa'.trans hNa.symm⟩, ?_⟩
    · simp only [Fpairs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (SimpleGraph.mem_neighborFinset F a v).mp (hNa.symm ▸ hvB)
    · intro b hb
      rw [hNa, Finset.mem_erase] at hb
      have hNb_sub : A ⊆ F.neighborFinset b := by
        intro x hx
        rw [SimpleGraph.mem_neighborFinset]
        rcases hcross x hx b hb.2 with ⟨_, h2⟩ | hF
        · exact absurd h2 hb.1
        · exact hF.symm
      have hdb : F.degree b = 3 := by
        have hc := Finset.card_le_card hNb_sub
        rw [hA3, SimpleGraph.card_neighborFinset_eq_degree] at hc
        have := hcdeg b; omega
      have hNb : F.neighborFinset b = A :=
        (Finset.eq_of_subset_of_card_le hNb_sub (by rw [SimpleGraph.card_neighborFinset_eq_degree, hdb, hA3])).symm
      refine ⟨hdb, ?_⟩
      intro a₂ ha₂a ha₂N
      have ha₂_eq : a₂ = a' :=
        htwin_uniq a a₂ a' ha₂a.symm haa' hda ha₂N.symm (hNa.trans hNa'.symm)
      rw [ha₂_eq, hNb, hAfull]
  choose wa hwa using hE3_witness
  let wmap : {p // p ∈ E3} → V × V := fun p => (wa p.1 p.2, p.1.2)
  have hwmap_mem : ∀ p : {p // p ∈ E3}, wmap p ∈ Fpairs := fun p => (hwa p.1 p.2).1
  have hwmap_inj : Function.Injective wmap := by
    rintro ⟨⟨u₁, v₁⟩, h₁⟩ ⟨⟨u₂, v₂⟩, h₂⟩ heq
    have ha_eq : wa (u₁, v₁) h₁ = wa (u₂, v₂) h₂ := (Prod.mk.inj heq).1
    have hv_eq : v₁ = v₂ := (Prod.mk.inj heq).2
    subst hv_eq
    set a := wa (u₁, v₁) h₁
    have hw₁ := hwa (u₁, v₁) h₁
    have hw₂ := hwa (u₂, v₁) h₂
    rw [← ha_eq] at hw₂
    have hvNa : v₁ ∈ F.neighborFinset a :=
      (SimpleGraph.mem_neighborFinset F a v₁).mpr (by simpa [Fpairs] using hw₁.1)
    have hpos : 0 < ((F.neighborFinset a).erase v₁).card := by
      rw [Finset.card_erase_of_mem hvNa, SimpleGraph.card_neighborFinset_eq_degree, hw₁.2.1]; omega
    obtain ⟨b, hb⟩ := Finset.card_pos.mp hpos
    obtain ⟨a', ha'a, ha'N⟩ := hw₁.2.2.1
    have hNb1 := (hw₁.2.2.2 b hb).2 a' ha'a ha'N
    have hNb2 := (hw₂.2.2.2 b hb).2 a' ha'a ha'N
    have hset : ({u₁, a, a'} : Finset V) = {u₂, a, a'} := hNb1.symm.trans hNb2
    have hcard1 : ({u₁, a, a'} : Finset V).card = 3 := by
      rw [← hNb1, SimpleGraph.card_neighborFinset_eq_degree, (hw₁.2.2.2 b hb).1]
    have hu₁_not : u₁ ∉ ({a, a'} : Finset V) := by
      intro hmem
      have : ({u₁, a, a'} : Finset V) = {a, a'} := Finset.insert_eq_of_mem hmem
      rw [this, Finset.card_pair ha'a.symm] at hcard1
      omega
    have hu₁_in : u₁ ∈ ({u₂, a, a'} : Finset V) := hset ▸ Finset.mem_insert_self u₁ {a, a'}
    rw [Finset.mem_insert] at hu₁_in
    have hu_eq : u₁ = u₂ := hu₁_in.resolve_right hu₁_not
    exact Subtype.ext (Prod.ext hu_eq rfl)
  have hE3_card : E3.card ≤ 42 := by
    have hsub : Finset.univ.image wmap ⊆ Fpairs := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨p, _, rfl⟩ := hx
      exact hwmap_mem p
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hwmap_inj, Finset.card_univ, Fintype.card_coe] at hc
    exact le_trans hc hFpairs_card
  have hcov : Gpairs ⊆ E1 ∪ E2 ∪ E3 := by
    intro p hp
    rcases hobs p hp with ⟨a, b, hab, hau, hav, hbu, hbv⟩ | h2 | h3
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      simp only [E1, Finset.mem_biUnion]
      refine ⟨s(a, b), SimpleGraph.mem_edgeFinset.mpr hab, ?_⟩
      simp only [pairOf, Sym2.lift_mk, Finset.mem_offDiag, Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      have hGp : G.Adj p.1 p.2 := (Finset.mem_filter.mp hp).2
      exact ⟨⟨hau, hbu⟩, ⟨hav, hbv⟩, hGp.ne⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨hp, h2⟩
    · apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨hp, h3⟩
  have htot := Finset.card_le_card hcov
  have hun1 := Finset.card_union_le (E1 ∪ E2) E3
  have hun2 := Finset.card_union_le E1 E2
  omega

end Order14

end LouYuK4
