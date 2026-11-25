import LouYuK4.LowerAndBipartite

/-!
# Explicit Attainability Witnesses for `{5, 8, 9}`

We prove that all three values in `{k + 1, 2k, 2k + 1} = {5, 8, 9}` are realized by connected
minimally 4-extendable graphs of order `ν ≤ 16`:
1. `witness_delta_5`: `K_{5,5}` on `Fin 10` (`δ = 5`),
2. `witness_delta_8`: `G_4 = (K_8 ⊔ K_8) + M_8` on `Fin 16` (`δ = 8`),
3. `witness_delta_9`: `K_{10}` on `Fin 10` (`δ = 9`).
-/

open SimpleGraph Finset

namespace LouYuK4

section Attainability

/-- Helper: Any even-size subset of a complete graph induces a graph with a PM. -/
lemma hasPM_complete_of_even_card {V : Type*} [Fintype V] [DecidableEq V] {S : Finset V}
    (heven : Even S.card) : HasPM ((⊤ : SimpleGraph V).induce (S : Set V)) := by
  classical
  obtain ⟨m, hm⟩ := heven
  revert S
  induction m with
  | zero =>
    intro S hS
    have hSe : S = ∅ := Finset.card_eq_zero.mp (by omega)
    refine ⟨⊥, ?_, fun x => False.elim (by simpa [hSe] using x.property)⟩
    intro x _; exact False.elim (by simpa [hSe] using x.property)
  | succ m ih =>
    intro S hS
    obtain ⟨a, haS⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    obtain ⟨b, hbS'⟩ := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem haS]; omega : 0 < (S.erase a).card)
    have hba : b ≠ a := (Finset.mem_erase.mp hbS').1
    have hbS : b ∈ S := Finset.mem_of_mem_erase hbS'
    let S' := (S.erase a).erase b
    have hS'card : S'.card = m + m := by
      rw [Finset.card_erase_of_mem hbS', Finset.card_erase_of_mem haS]; omega
    obtain ⟨P', hP'M, hP'span⟩ := ih hS'card
    refine ⟨{
      verts := Set.univ
      Adj := fun x y => (x.val = a ∧ y.val = b) ∨ (x.val = b ∧ y.val = a) ∨
        ∃ (hx : x.val ∈ S') (hy : y.val ∈ S'), P'.Adj ⟨x.val, hx⟩ ⟨y.val, hy⟩
      adj_sub := by
        rintro ⟨x, hx⟩ ⟨y, hy⟩ (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hx', hy', h⟩)
        · exact hba.symm
        · exact hba
        · exact h.adj_sub
      edge_vert := fun _ => Set.mem_univ _
      symm := ⟨by
        rintro x y (h | h | ⟨hx', hy', h⟩)
        · exact Or.inr (Or.inl h.symm)
        · exact Or.inl h.symm
        · exact Or.inr (Or.inr ⟨hy', hx', h.symm⟩)⟩
    }, ?_, fun _ => Set.mem_univ _⟩
    intro ⟨x, hx⟩ _
    by_cases hxa : x = a
    · subst hxa
      refine ⟨⟨b, hbS⟩, Or.inl ⟨rfl, rfl⟩, ?_⟩
      rintro ⟨y, hy⟩ (⟨_, rfl⟩ | ⟨h, _⟩ | ⟨hx', _, _⟩)
      · rfl
      · exact absurd h hba.symm
      · exact absurd rfl (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx')).1
    · by_cases hxb : x = b
      · subst hxb
        refine ⟨⟨a, haS⟩, Or.inr (Or.inl ⟨rfl, rfl⟩), ?_⟩
        rintro ⟨y, hy⟩ (⟨h, _⟩ | ⟨_, rfl⟩ | ⟨hx', _, _⟩)
        · exact absurd h hba
        · rfl
        · exact absurd rfl (Finset.mem_erase.mp hx').1
      · have hx' : x ∈ S' := Finset.mem_erase.mpr ⟨hxb, Finset.mem_erase.mpr ⟨hxa, hx⟩⟩
        obtain ⟨⟨y, hy'⟩, hxy, huniq⟩ := hP'M (hP'span ⟨x, hx'⟩)
        refine ⟨⟨y, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy')⟩,
          Or.inr (Or.inr ⟨hx', hy', hxy⟩), ?_⟩
        rintro ⟨z, hz⟩ (⟨h, _⟩ | ⟨h, _⟩ | ⟨_, hz', hxz⟩)
        · exact absurd h hxa
        · exact absurd h hxb
        · exact Subtype.ext (congrArg (fun t : (S' : Set V) => t.val) (huniq ⟨z, hz'⟩ hxz))

/-- Helper: Combine PMs on two disjoint sets `A, B` into a PM on `A ∪ B`. -/
lemma hasPM_induce_union {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {A B : Finset V} (hdisj : Disjoint A B)
    (hA : HasPM (G.induce (A : Set V))) (hB : HasPM (G.induce (B : Set V))) :
    HasPM (G.induce ((A ∪ B : Finset V) : Set V)) := by
  obtain ⟨MA, hMA, hMAv⟩ := exists_isMatching_of_hasPM_induce hA
  obtain ⟨MB, hMB, hMBv⟩ := exists_isMatching_of_hasPM_induce hB
  have hdisjS : Disjoint MA.support MB.support := by
    rw [hMA.support_eq_verts, hMB.support_eq_verts, hMAv, hMBv]
    exact Finset.disjoint_coe.mpr hdisj
  refine hasPM_induce_of_isMatching (hMA.sup hMB hdisjS) ?_
  rw [Subgraph.verts_sup, hMAv, hMBv, Finset.coe_union]

/-- Helper: Any adjacent pair `{u, v}` induces a PM. -/
lemma hasPM_induce_pair {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {u v : V} (huv : G.Adj u v) : HasPM (G.induce (({u, v} : Finset V) : Set V)) := by
  refine ⟨{
    verts := Set.univ
    Adj := fun x y => (x.val = u ∧ y.val = v) ∨ (x.val = v ∧ y.val = u)
    adj_sub := by
      rintro x y (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · rw [SimpleGraph.induce_adj, h1, h2]; exact huv
      · rw [SimpleGraph.induce_adj, h1, h2]; exact huv.symm
    edge_vert := fun _ => Set.mem_univ _
    symm := ⟨by rintro x y (h | h); exact Or.inr h.symm; exact Or.inl h.symm⟩
  }, ?_, fun _ => Set.mem_univ _⟩
  intro ⟨x, hx⟩ _
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hxu | hxv
  · refine ⟨⟨v, by simp⟩, Or.inl ⟨hxu, rfl⟩, ?_⟩
    rintro ⟨y, _⟩ (⟨_, hy⟩ | ⟨h, _⟩); exact Subtype.ext hy; exact absurd (hxu.symm.trans h) huv.ne
  · refine ⟨⟨u, by simp⟩, Or.inr ⟨hxv, rfl⟩, ?_⟩
    rintro ⟨y, _⟩ (⟨h, _⟩ | ⟨_, hy⟩); exact absurd (hxv.symm.trans h) huv.ne.symm; exact Subtype.ext hy

/-- Helper: Deleting an edge `{u, v}` outside `S` does not change `G.induce S`. -/
lemma induce_deleteEdges_eq_of_notMem {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {u v : V} {S : Finset V} (hnot : u ∉ S ∨ v ∉ S) :
    (G.deleteEdges {s(u, v)}).induce (S : Set V) = G.induce (S : Set V) := by
  ext ⟨x, hx⟩ ⟨y, hy⟩
  simp only [SimpleGraph.induce_adj, SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff,
    Sym2.eq_iff, and_iff_left_iff_imp]
  intro _ h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hnot with hu | hv
  · exact hu (h1 ▸ hx)
  · exact hv (h2 ▸ hy)
  · exact hu (h2 ▸ hy)
  · exact hv (h1 ▸ hx)

/-- **Attainability of `δ = 9`**: `K₁₀` on `Fin 10` is connected, minimally 4-extendable,
and 9-regular. -/
theorem witness_delta_9 :
    let G : SimpleGraph (Fin 10) := ⊤
    G.Connected ∧ IsMinimallyKExtendable G 4 ∧ ∀ v : Fin 10, G.degree v = 9 := by
  dsimp only
  have hconn : (⊤ : SimpleGraph (Fin 10)).Connected := by
    refine ⟨fun u v => ?_⟩
    by_cases h : u = v
    · subst h; exact ⟨SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons h SimpleGraph.Walk.nil⟩
  have hext : IsKExtendable (⊤ : SimpleGraph (Fin 10)) 4 := by
    rw [isKExtendable_iff_compl_pm]
    refine ⟨⟨Finset.univ.filter (fun i : Fin 10 => i.val < 8), by decide,
        hasPM_complete_of_even_card (by rw [show (Finset.univ.filter (fun i : Fin 10 => i.val < 8)).card = 8 by decide]; exact ⟨4, rfl⟩)⟩,
      fun S hS8 _ => hasPM_complete_of_even_card (by rw [Finset.card_compl, hS8, Fintype.card_fin]; exact ⟨1, rfl⟩)⟩
  have hmin : IsMinimallyKExtendable (⊤ : SimpleGraph (Fin 10)) 4 := by
    refine ⟨hext, fun e he => ?_⟩
    induction e using Sym2.ind with
    | _ u v =>
      have huv : u ≠ v := he
      intro hext'
      let S : Finset (Fin 10) := ({u, v} : Finset (Fin 10))ᶜ
      have hS8 : S.card = 8 := by rw [Finset.card_compl, Finset.card_pair huv, Fintype.card_fin]
      have hSPM : HasPM (((⊤ : SimpleGraph (Fin 10)).deleteEdges {s(u, v)}).induce (S : Set (Fin 10))) := by
        rw [induce_deleteEdges_eq_of_notMem _ (Or.inl (by simp [S]))]
        exact hasPM_complete_of_even_card (by rw [hS8]; exact ⟨4, rfl⟩)
      have hScPM := (isKExtendable_iff_compl_pm.mp hext').2 S hS8 hSPM
      rw [show Sᶜ = ({u, v} : Finset (Fin 10)) from compl_compl _] at hScPM
      exact not_hasPM_pair_of_not_adj (by simp [SimpleGraph.deleteEdges_adj]) hScPM
  refine ⟨hconn, hmin, fun v => ?_⟩
  have hN : (⊤ : SimpleGraph (Fin 10)).neighborFinset v = Finset.univ.erase v := by
    ext w; simp [ne_comm]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hN, Finset.card_erase_of_mem (Finset.mem_univ v),
    Finset.card_univ, Fintype.card_fin]

/-- Complete bipartite graph `K_{5,5}` on `Fin 10` (parts `{0..4}` and `{5..9}`). -/
def graphK55 : SimpleGraph (Fin 10) where
  Adj u v := (u.val < 5 ∧ 5 ≤ v.val) ∨ (5 ≤ u.val ∧ v.val < 5)
  symm := ⟨fun _ _ h => by rcases h with ⟨a, b⟩ | ⟨a, b⟩; exact Or.inr ⟨b, a⟩; exact Or.inl ⟨b, a⟩⟩
  loopless := ⟨fun _ h => by omega⟩

instance : DecidableRel graphK55.Adj := fun u v => by
  unfold graphK55; infer_instance

/-- **Attainability of `δ = 5`**: `K_{5,5}` on `Fin 10` is connected, minimally 4-extendable,
and 5-regular. -/
theorem witness_delta_5 :
    graphK55.Connected ∧ IsMinimallyKExtendable graphK55 4 ∧ ∀ v : Fin 10, graphK55.degree v = 5 := by
  have hconn : graphK55.Connected := by
    refine ⟨fun u v => ?_⟩
    by_cases hu : u.val < 5 <;> by_cases hv : v.val < 5
    · exact ⟨SimpleGraph.Walk.cons (Or.inl ⟨hu, by decide⟩ : graphK55.Adj u ⟨5, by decide⟩)
        (SimpleGraph.Walk.cons (Or.inr ⟨by decide, hv⟩) SimpleGraph.Walk.nil)⟩
    · exact ⟨SimpleGraph.Walk.cons (Or.inl ⟨hu, by omega⟩) SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons (Or.inr ⟨by omega, hv⟩) SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons (Or.inr ⟨by omega, by decide⟩ : graphK55.Adj u ⟨0, by decide⟩)
        (SimpleGraph.Walk.cons (Or.inl ⟨by decide, by omega⟩) SimpleGraph.Walk.nil)⟩
  let L : Finset (Fin 10) := Finset.univ.filter (fun i : Fin 10 => i.val < 5)
  let R : Finset (Fin 10) := Finset.univ.filter (fun i : Fin 10 => 5 ≤ i.val)
  have hLR_disj : Disjoint L R := by
    rw [Finset.disjoint_left]; intro x hx hy; simp only [L, R, Finset.mem_filter] at hx hy; omega
  have hLR_un : L ∪ R = Finset.univ := by
    ext x; simp only [L, R, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact lt_or_ge x.val 5
  have hL5 : L.card = 5 := by decide
  have hR5 : R.card = 5 := by decide
  have hbal_pm : ∀ S : Finset (Fin 10), (S ∩ L).card = (S ∩ R).card →
      HasPM (graphK55.induce (S : Set (Fin 10))) := by
    intro S hbal
    let SL := S ∩ L
    let SR := S ∩ R
    have heq_fintype : Fintype.card SL = Fintype.card SR := by
      rw [Fintype.card_coe, Fintype.card_coe]; exact hbal
    let e : SL ≃ SR := Fintype.equivOfCardEq heq_fintype
    have hdisj : Disjoint SL SR := Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right hLR_disj
    obtain ⟨M, hM, _, hMverts⟩ := exists_matching_of_inj_disjoint (G := graphK55) hdisj
      (fun x : SL => (e x).val) (fun a b h => e.injective (Subtype.ext h))
      (fun x => (e x).property)
      (fun x => Or.inl ⟨(Finset.mem_filter.mp (Finset.mem_inter.mp x.property).2).2,
        (Finset.mem_filter.mp (Finset.mem_inter.mp (e x).property).2).2⟩)
    have hIm : Finset.univ.image (fun x : SL => (e x).val) = SR := by
      ext y; simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨x, rfl⟩; exact (e x).property
      · intro hy; exact ⟨e.symm ⟨y, hy⟩, by simp⟩
    have hMvS : M.verts = (S : Set (Fin 10)) := by
      rw [hMverts, hIm]; ext v
      simp only [SL, SR, Finset.mem_coe, Finset.mem_union, Finset.mem_inter]
      have hvLR : v ∈ L ∨ v ∈ R := by rw [← Finset.mem_union, hLR_un]; exact Finset.mem_univ v
      tauto
    exact hasPM_induce_of_isMatching hM hMvS
  have hext : IsKExtendable graphK55 4 := by
    rw [isKExtendable_iff_compl_pm]
    refine ⟨⟨Finset.univ.filter (fun i : Fin 10 => i.val ≠ 0 ∧ i.val ≠ 5), by decide,
        hbal_pm _ (by decide)⟩, fun S hS8 hSPM => ?_⟩
    obtain ⟨P, hPM, hPspan⟩ := hSPM
    choose f hf_adj _ using fun x : (S : Set (Fin 10)) => hPM (hPspan x)
    have hfinj : Function.Injective f := fun a b h => by
      have h1 := hf_adj a; rw [h] at h1; exact hPM.eq_of_adj_right h1 (hf_adj b)
    have h1 : (S ∩ L).card ≤ (S ∩ R).card := by
      let g : {x : Fin 10 // x ∈ S ∩ L} → Fin 10 := fun x => (f ⟨x.val, (Finset.mem_inter.mp x.property).1⟩).val
      have hginj : Function.Injective g := fun a b h =>
        Subtype.ext (congrArg (fun t : (S : Set (Fin 10)) => t.val) (hfinj (Subtype.ext h)))
      have hsub : Finset.univ.image g ⊆ S ∩ R := by
        intro w hw; rw [Finset.mem_image] at hw; obtain ⟨x, _, rfl⟩ := hw
        have hadj : graphK55.Adj x.val (f ⟨x.val, (Finset.mem_inter.mp x.property).1⟩).val :=
          (hf_adj ⟨x.val, (Finset.mem_inter.mp x.property).1⟩).adj_sub
        have hxL : x.val.val < 5 := (Finset.mem_filter.mp (Finset.mem_inter.mp x.property).2).2
        refine Finset.mem_inter.mpr ⟨(f ⟨x.val, (Finset.mem_inter.mp x.property).1⟩).property,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        rcases hadj with ⟨_, h⟩ | ⟨h, _⟩ <;> omega
      simpa [Finset.card_image_of_injective _ hginj] using Finset.card_le_card hsub
    have h2 : (S ∩ R).card ≤ (S ∩ L).card := by
      let g : {x : Fin 10 // x ∈ S ∩ R} → Fin 10 := fun x => (f ⟨x.val, (Finset.mem_inter.mp x.property).1⟩).val
      have hginj : Function.Injective g := fun a b h =>
        Subtype.ext (congrArg (fun t : (S : Set (Fin 10)) => t.val) (hfinj (Subtype.ext h)))
      have hsub : Finset.univ.image g ⊆ S ∩ L := by
        intro w hw; rw [Finset.mem_image] at hw; obtain ⟨x, _, rfl⟩ := hw
        have hadj : graphK55.Adj x.val (f ⟨x.val, (Finset.mem_inter.mp x.property).1⟩).val :=
          (hf_adj ⟨x.val, (Finset.mem_inter.mp x.property).1⟩).adj_sub
        have hxR : 5 ≤ x.val.val := (Finset.mem_filter.mp (Finset.mem_inter.mp x.property).2).2
        refine Finset.mem_inter.mpr ⟨(f ⟨x.val, (Finset.mem_inter.mp x.property).1⟩).property,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        rcases hadj with ⟨h, _⟩ | ⟨_, h⟩ <;> omega
      simpa [Finset.card_image_of_injective _ hginj] using Finset.card_le_card hsub
    have hSpart : (S ∩ L).card + (S ∩ R).card = 8 := by
      rw [← Finset.card_union_of_disjoint (Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right hLR_disj)]
      have : S ∩ L ∪ S ∩ R = S := by
        ext v; simp only [Finset.mem_union, Finset.mem_inter]
        have : v ∈ L ∨ v ∈ R := by rw [← Finset.mem_union, hLR_un]; simp
        tauto
      rw [this, hS8]
    have hScL : (Sᶜ ∩ L).card = 1 := by
      have : (S ∩ L).card + (Sᶜ ∩ L).card = L.card := by
        rw [← Finset.card_union_of_disjoint (Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left disjoint_compl_right)]
        have : S ∩ L ∪ Sᶜ ∩ L = L := by ext v; simp; tauto
        rw [this]
      omega
    have hScR : (Sᶜ ∩ R).card = 1 := by
      have : (S ∩ R).card + (Sᶜ ∩ R).card = R.card := by
        rw [← Finset.card_union_of_disjoint (Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left disjoint_compl_right)]
        have : S ∩ R ∪ Sᶜ ∩ R = R := by ext v; simp; tauto
        rw [this]
      omega
    exact hbal_pm Sᶜ (by omega)
  have hmin : IsMinimallyKExtendable graphK55 4 := by
    refine ⟨hext, fun e he => ?_⟩
    induction e using Sym2.ind with
    | _ u v =>
      have huv : graphK55.Adj u v := he
      intro hext'
      let S : Finset (Fin 10) := ({u, v} : Finset (Fin 10))ᶜ
      have hS8 : S.card = 8 := by rw [Finset.card_compl, Finset.card_pair huv.ne, Fintype.card_fin]
      have hbalS : (S ∩ L).card = (S ∩ R).card := by
        have hpair_bal : ∀ a b : Fin 10, a.val < 5 → 5 ≤ b.val →
            ((({a, b} : Finset (Fin 10))ᶜ ∩ L).card = 4 ∧ (({a, b} : Finset (Fin 10))ᶜ ∩ R).card = 4) := by
          intro a b haL hbR
          have ha_inL : a ∈ L := Finset.mem_filter.mpr ⟨Finset.mem_univ a, haL⟩
          have hb_inR : b ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ b, hbR⟩
          have h1 : ({a, b} : Finset (Fin 10))ᶜ ∩ L = L.erase a := by
            ext x; simp only [L, Finset.mem_inter, Finset.mem_compl, Finset.mem_insert,
              Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, not_or]
            constructor
            · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
            · rintro ⟨h1, h2⟩; exact ⟨⟨h1, fun h => by subst h; omega⟩, h2⟩
          have h2 : ({a, b} : Finset (Fin 10))ᶜ ∩ R = R.erase b := by
            ext x; simp only [R, Finset.mem_inter, Finset.mem_compl, Finset.mem_insert,
              Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, not_or]
            constructor
            · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨h1, h2⟩
            · rintro ⟨h1, h2⟩; exact ⟨⟨fun h => by subst h; omega, h1⟩, h2⟩
          rw [h1, h2, Finset.card_erase_of_mem ha_inL, Finset.card_erase_of_mem hb_inR, hL5, hR5]
          exact ⟨rfl, rfl⟩
        rcases huv with ⟨huL, hvR⟩ | ⟨huR, hvL⟩
        · have h := hpair_bal u v huL hvR; exact h.1.trans h.2.symm
        · have h := hpair_bal v u hvL huR
          have hcomm : ({u, v} : Finset (Fin 10)) = {v, u} := Finset.pair_comm u v
          dsimp only [S]; rw [hcomm]; exact h.1.trans h.2.symm
      have hSPM : HasPM ((graphK55.deleteEdges {s(u, v)}).induce (S : Set (Fin 10))) := by
        rw [induce_deleteEdges_eq_of_notMem _ (Or.inl (by simp [S]))]
        exact hbal_pm S hbalS
      have hScPM := (isKExtendable_iff_compl_pm.mp hext').2 S hS8 hSPM
      rw [show Sᶜ = ({u, v} : Finset (Fin 10)) from compl_compl _] at hScPM
      exact not_hasPM_pair_of_not_adj (by simp [SimpleGraph.deleteEdges_adj]) hScPM
  exact ⟨hconn, hmin, by decide⟩

/-- The 8-regular graph `G_4 = (K_8 ⊔ K_8) + M_8` on `Fin 16`. -/
def graphG4 : SimpleGraph (Fin 16) where
  Adj u v := u ≠ v ∧ ((u.val < 8 ∧ v.val < 8) ∨ (8 ≤ u.val ∧ 8 ≤ v.val) ∨
    u.val + 8 = v.val ∨ v.val + 8 = u.val)
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rcases h.2 with ⟨a, b⟩ | ⟨a, b⟩ | h1 | h2 <;> tauto⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel graphG4.Adj := fun u v => by
  unfold graphG4; infer_instance

private def g4L : Finset (Fin 16) := Finset.univ.filter (fun i : Fin 16 => i.val < 8)
private def g4R : Finset (Fin 16) := Finset.univ.filter (fun i : Fin 16 => 8 ≤ i.val)

private lemma g4L_card : g4L.card = 8 := by decide
private lemma g4R_card : g4R.card = 8 := by decide

private lemma g4LR_disj : Disjoint g4L g4R := by
  rw [Finset.disjoint_left]; intro x hx hy
  simp only [g4L, g4R, Finset.mem_filter] at hx hy; omega

private lemma g4LR_un : g4L ∪ g4R = Finset.univ := by
  ext x; simp only [g4L, g4R, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact lt_or_ge x.val 8

private lemma graphG4_clique_pm {S : Finset (Fin 16)} (hside : S ⊆ g4L ∨ S ⊆ g4R)
    (hev : Even S.card) : HasPM (graphG4.induce (S : Set (Fin 16))) := by
  have heq : graphG4.induce (S : Set (Fin 16)) = (⊤ : SimpleGraph (Fin 16)).induce (S : Set (Fin 16)) := by
    ext ⟨x, hx⟩ ⟨y, hy⟩
    simp only [SimpleGraph.induce_adj, SimpleGraph.top_adj, graphG4]
    constructor
    · exact fun h => h.1
    · intro hxy; refine ⟨hxy, ?_⟩
      rcases hside with hL | hR
      · exact Or.inl ⟨(Finset.mem_filter.mp (hL hx)).2, (Finset.mem_filter.mp (hL hy)).2⟩
      · exact Or.inr (Or.inl ⟨(Finset.mem_filter.mp (hR hx)).2, (Finset.mem_filter.mp (hR hy)).2⟩)
  rw [heq]; exact hasPM_complete_of_even_card hev

private lemma graphG4_connected : graphG4.Connected := by
  refine ⟨fun u v => ?_⟩
  by_cases huv : u = v
  · subst huv; exact ⟨SimpleGraph.Walk.nil⟩
  by_cases hu : u.val < 8 <;> by_cases hv : v.val < 8
  · exact ⟨SimpleGraph.Walk.cons ⟨huv, Or.inl ⟨hu, hv⟩⟩ SimpleGraph.Walk.nil⟩
  · let u' : Fin 16 := ⟨u.val + 8, by omega⟩
    have huu' : graphG4.Adj u u' := ⟨by intro h; have := congrArg Fin.val h; dsimp [u'] at this; omega, Or.inr (Or.inr (Or.inl rfl))⟩
    by_cases h' : u' = v
    · rw [← h']; exact ⟨SimpleGraph.Walk.cons huu' SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons huu' (SimpleGraph.Walk.cons ⟨h', Or.inr (Or.inl ⟨by dsimp [u']; omega, by omega⟩)⟩ SimpleGraph.Walk.nil)⟩
  · let v' : Fin 16 := ⟨v.val + 8, by omega⟩
    have hv'v : graphG4.Adj v' v := ⟨by intro h; have := congrArg Fin.val h; dsimp [v'] at this; omega, Or.inr (Or.inr (Or.inr rfl))⟩
    by_cases h' : u = v'
    · rw [h']; exact ⟨SimpleGraph.Walk.cons hv'v SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons ⟨h', Or.inr (Or.inl ⟨by omega, by dsimp [v']; omega⟩)⟩ (SimpleGraph.Walk.cons hv'v SimpleGraph.Walk.nil)⟩
  · exact ⟨SimpleGraph.Walk.cons ⟨huv, Or.inr (Or.inl ⟨by omega, by omega⟩)⟩ SimpleGraph.Walk.nil⟩

private lemma graphG4_isKExtendable : IsKExtendable graphG4 4 := by
  classical
  rw [isKExtendable_iff_compl_pm]
  refine ⟨⟨g4L, g4L_card, graphG4_clique_pm (Or.inl Subset.rfl) ⟨4, by rw [g4L_card]⟩⟩,
    fun S hS8 hSPM => ?_⟩
  let T := Sᶜ
  have hT8 : T.card = 8 := by rw [Finset.card_compl, hS8, Fintype.card_fin]
  have hTpart : T = (T ∩ g4L) ∪ (T ∩ g4R) := by
    ext v; simp only [Finset.mem_union, Finset.mem_inter]
    have : v ∈ g4L ∨ v ∈ g4R := by rw [← Finset.mem_union, g4LR_un]; simp
    tauto
  have hTcard_sum : (T ∩ g4L).card + (T ∩ g4R).card = 8 := by
    rw [← Finset.card_union_of_disjoint (Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right g4LR_disj),
      ← hTpart, hT8]
  rcases Nat.even_or_odd (T ∩ g4L).card with hTev | hTodd
  · rw [show Sᶜ = (T ∩ g4L) ∪ (T ∩ g4R) from hTpart]
    refine hasPM_induce_union (Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right g4LR_disj)
      (graphG4_clique_pm (Or.inl Finset.inter_subset_right) hTev)
      (graphG4_clique_pm (Or.inr Finset.inter_subset_right) ?_)
    obtain ⟨m, hm⟩ := hTev; exact ⟨4 - m, by omega⟩
  · have hex_pair : ∃ i : Fin 8, (⟨i.val, by omega⟩ : Fin 16) ∈ T ∧ (⟨i.val + 8, by omega⟩ : Fin 16) ∈ T := by
      obtain ⟨P, hPM, hPspan⟩ := hSPM
      choose f hf_adj hf_uniq using fun x : (S : Set (Fin 16)) => hPM (hPspan x)
      have hSL_odd : Odd (S ∩ g4L).card := by
        have : (S ∩ g4L).card + (T ∩ g4L).card = 8 := by
          rw [← Finset.card_union_of_disjoint (Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left disjoint_compl_right)]
          have : S ∩ g4L ∪ T ∩ g4L = g4L := by ext v; simp [T]; tauto
          rw [this, g4L_card]
        obtain ⟨m, hm⟩ := hTodd; exact ⟨3 - m, by omega⟩
      have hex_cross : ∃ x : (S : Set (Fin 16)), x.val ∈ g4L ∧ (f x).val ∈ g4R := by
        by_contra hno; push Not at hno
        let M_SL : (graphG4.induce (S : Set (Fin 16))).Subgraph := {
          verts := {x : (S : Set (Fin 16)) | x.val ∈ g4L}
          Adj := fun x y => x.val ∈ g4L ∧ y.val ∈ g4L ∧ P.Adj x y
          adj_sub := fun h => h.2.2.adj_sub
          edge_vert := fun h => h.1
          symm := ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩
        }
        have hM_SL : M_SL.IsMatching := by
          intro x hx
          have hfxL : (f x).val ∈ g4L := by
            have : (f x).val ∈ g4L ∨ (f x).val ∈ g4R := by rw [← Finset.mem_union, g4LR_un]; simp
            exact this.resolve_right (hno x hx)
          exact ⟨f x, ⟨hx, hfxL, hf_adj x⟩, fun y hy => hf_uniq x y hy.2.2⟩
        have h1 := isMatching_verts_ncard hM_SL
        have h2 : M_SL.verts.toFinset.image Subtype.val = S ∩ g4L := by
          ext v
          simp only [M_SL, Finset.mem_image, Set.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_inter]
          constructor
          · rintro ⟨⟨w, hwS⟩, hwL, rfl⟩; exact ⟨hwS, hwL⟩
          · rintro ⟨hvS, hvL⟩; exact ⟨⟨v, hvS⟩, hvL, rfl⟩
        rw [Set.ncard_eq_toFinset_card', ← Finset.card_image_of_injective _ Subtype.val_injective, h2] at h1
        obtain ⟨m, hm⟩ := hSL_odd; omega
      obtain ⟨x₀, hx₀L, hfx₀R⟩ := hex_cross
      have hadj0 : graphG4.Adj x₀.val (f x₀).val := (hf_adj x₀).adj_sub
      have hx₀_val : x₀.val.val < 8 := (Finset.mem_filter.mp hx₀L).2
      have hfx₀_val : 8 ≤ (f x₀).val.val := (Finset.mem_filter.mp hfx₀R).2
      have hpair0 : x₀.val.val + 8 = (f x₀).val.val := by
        rcases hadj0.2 with ⟨_, h⟩ | ⟨h, _⟩ | h | h <;> omega
      let proj : Fin 16 → Fin 8 := fun v => ⟨v.val % 8, Nat.mod_lt _ (by decide)⟩
      have hsame : proj x₀.val = proj (f x₀).val := by apply Fin.ext; dsimp [proj]; omega
      have hsub_er : S.image proj ⊆ (S.erase (f x₀).val).image proj := by
        intro i hi; rw [Finset.mem_image] at hi ⊢
        obtain ⟨v, hvS, rfl⟩ := hi
        by_cases hvf : v = (f x₀).val
        · subst hvf; exact ⟨x₀.val, Finset.mem_erase.mpr ⟨hadj0.1, x₀.property⟩, hsame⟩
        · exact ⟨v, Finset.mem_erase.mpr ⟨hvf, hvS⟩, rfl⟩
      have him_le : (S.image proj).card ≤ 7 := by
        have h1 := Finset.card_le_card hsub_er
        have h2 := Finset.card_image_le (f := proj) (s := S.erase (f x₀).val)
        rw [Finset.card_erase_of_mem (f x₀).property, hS8] at h2; omega
      have hmiss : (Finset.univ \ S.image proj).Nonempty := Finset.card_pos.mp (by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]; omega)
      obtain ⟨i, hi⟩ := hmiss
      have hi_not : i ∉ S.image proj := (Finset.mem_sdiff.mp hi).2
      refine ⟨i, Finset.mem_compl.mpr fun h => hi_not (Finset.mem_image.mpr ⟨_, h, ?_⟩),
        Finset.mem_compl.mpr fun h => hi_not (Finset.mem_image.mpr ⟨_, h, ?_⟩)⟩
      · apply Fin.ext; dsimp [proj]; exact Nat.mod_eq_of_lt i.isLt
      · apply Fin.ext; dsimp [proj]; omega
    obtain ⟨i, hiL, hiR⟩ := hex_pair
    let u : Fin 16 := ⟨i.val, by omega⟩
    let v : Fin 16 := ⟨i.val + 8, by omega⟩
    have huv_adj : graphG4.Adj u v := ⟨by intro h; have := congrArg Fin.val h; dsimp [u, v] at this; omega,
      Or.inr (Or.inr (Or.inl rfl))⟩
    let TL' := (T ∩ g4L).erase u
    let TR' := (T ∩ g4R).erase v
    have huTL : u ∈ T ∩ g4L := Finset.mem_inter.mpr ⟨hiL, Finset.mem_filter.mpr ⟨Finset.mem_univ u, i.isLt⟩⟩
    have hvTR : v ∈ T ∩ g4R := Finset.mem_inter.mpr ⟨hiR, Finset.mem_filter.mpr ⟨Finset.mem_univ v, by dsimp [v]; omega⟩⟩
    have hTdecomp : Sᶜ = ({u, v} : Finset (Fin 16)) ∪ (TL' ∪ TR') := by
      ext w; simp only [TL', TR', Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Finset.mem_erase, Finset.mem_inter]
      have hwLR : w ∈ g4L ∨ w ∈ g4R := by rw [← Finset.mem_union, g4LR_un]; simp
      constructor
      · intro hwT; by_cases hwu : w = u; · exact Or.inl (Or.inl hwu)
        by_cases hwv : w = v; · exact Or.inl (Or.inr hwv)
        rcases hwLR with hwL | hwR
        · exact Or.inr (Or.inl ⟨hwu, hwT, hwL⟩)
        · exact Or.inr (Or.inr ⟨hwv, hwT, hwR⟩)
      · rintro ((rfl | rfl) | (⟨_, hwT, _⟩ | ⟨_, hwT, _⟩)) <;> assumption
    have hdisj_uv_rest : Disjoint ({u, v} : Finset (Fin 16)) (TL' ∪ TR') := by
      rw [Finset.disjoint_left]; intro w hw hrest
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      simp only [TL', TR', Finset.mem_union, Finset.mem_erase, Finset.mem_inter] at hrest
      rcases hw with rfl | rfl <;> rcases hrest with ⟨h1, _, h2⟩ | ⟨h1, _, h2⟩
      · exact h1 rfl
      · exact Finset.disjoint_left.mp g4LR_disj (Finset.mem_filter.mpr ⟨Finset.mem_univ u, i.isLt⟩) h2
      · exact Finset.disjoint_right.mp g4LR_disj (Finset.mem_filter.mpr ⟨Finset.mem_univ v, by dsimp [v]; omega⟩) h2
      · exact h1 rfl
    have hdisj_TL'R' : Disjoint TL' TR' := Disjoint.mono (Finset.erase_subset _ _ |>.trans Finset.inter_subset_right)
      (Finset.erase_subset _ _ |>.trans Finset.inter_subset_right) g4LR_disj
    have hTL'ev : Even TL'.card := by
      rw [Finset.card_erase_of_mem huTL]; obtain ⟨m, hm⟩ := hTodd; exact ⟨m, by omega⟩
    have hTR'ev : Even TR'.card := by
      rw [Finset.card_erase_of_mem hvTR]; obtain ⟨m, hm⟩ := hTodd; exact ⟨3 - m, by omega⟩
    rw [hTdecomp]
    exact hasPM_induce_union hdisj_uv_rest (hasPM_induce_pair huv_adj)
      (hasPM_induce_union hdisj_TL'R'
        (graphG4_clique_pm (Or.inl (Finset.erase_subset _ _ |>.trans Finset.inter_subset_right)) hTL'ev)
        (graphG4_clique_pm (Or.inr (Finset.erase_subset _ _ |>.trans Finset.inter_subset_right)) hTR'ev))

private lemma graphG4_delete_clique_left {u v : Fin 16} (huv : u ≠ v) (huL : u.val < 8) (hvL : v.val < 8) :
    ¬ IsKExtendable (graphG4.deleteEdges {s(u, v)}) 4 := by
  intro hext'
  let G' := graphG4.deleteEdges {s(u, v)}
  let u' : Fin 16 := ⟨u.val + 8, by omega⟩
  let v' : Fin 16 := ⟨v.val + 8, by omega⟩
  have hu_inL : u ∈ g4L := Finset.mem_filter.mpr ⟨Finset.mem_univ u, huL⟩
  have hv_inL : v ∈ g4L := Finset.mem_filter.mpr ⟨Finset.mem_univ v, hvL⟩
  have hv_er : v ∈ g4L.erase u := Finset.mem_erase.mpr ⟨huv.symm, hv_inL⟩
  let S : Finset (Fin 16) := ((g4L.erase u).erase v) ∪ {u', v'}
  have hu'v' : u' ≠ v' := by intro h; exact huv (Fin.ext (by have := congrArg Fin.val h; dsimp [u', v'] at this; omega))
  have hdisjS : Disjoint ((g4L.erase u).erase v) {u', v'} := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    have hxL : x.val < 8 := (Finset.mem_filter.mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx1))).2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx2
    rcases hx2 with rfl | rfl <;> dsimp [u', v'] at hxL <;> omega
  have hS8 : S.card = 8 := by
    rw [Finset.card_union_of_disjoint hdisjS, Finset.card_erase_of_mem hv_er,
      Finset.card_erase_of_mem hu_inL, Finset.card_pair hu'v', g4L_card]
  have hu_notS : u ∉ S := by
    intro h; simp only [S, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with ⟨_, h, _⟩ | (h | h)
    · exact h rfl
    · have := congrArg Fin.val h; dsimp [u'] at this; omega
    · have := congrArg Fin.val h; dsimp [v'] at this; omega
  have hSPM : HasPM (G'.induce (S : Set (Fin 16))) := by
    rw [induce_deleteEdges_eq_of_notMem _ (Or.inl hu_notS)]
    exact hasPM_induce_union hdisjS
      (graphG4_clique_pm (Or.inl (Finset.erase_subset _ _ |>.trans (Finset.erase_subset _ _)))
        ⟨3, by rw [Finset.card_erase_of_mem hv_er, Finset.card_erase_of_mem hu_inL, g4L_card]⟩)
      (graphG4_clique_pm (Or.inr fun x hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp [u', v']; omega⟩)
        ⟨1, by rw [Finset.card_pair hu'v']⟩)
  have hScPM := (isKExtendable_iff_compl_pm.mp hext').2 S hS8 hSPM
  refine not_hasPM_of_isolated (G := G') (S := Sᶜ) (v := u) (Finset.mem_compl.mpr hu_notS) ?_ hScPM
  intro w hwSc hadj
  rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff] at hadj
  have hadjG : graphG4.Adj u w := hadj.1
  have hne_uv : s(u, w) ≠ s(u, v) := hadj.2
  rcases hadjG.2 with ⟨_, hwL⟩ | ⟨huR, _⟩ | h1 | h2
  · have hwv : w ≠ v := fun h => hne_uv (by rw [h])
    have hw_inL : w ∈ g4L := Finset.mem_filter.mpr ⟨Finset.mem_univ w, hwL⟩
    exact (Finset.mem_compl.mp hwSc) (Finset.mem_union_left _
      (Finset.mem_erase.mpr ⟨hwv, Finset.mem_erase.mpr ⟨hadjG.1.symm, hw_inL⟩⟩))
  · omega
  · have hwu' : w = u' := Fin.ext h1.symm
    exact (Finset.mem_compl.mp hwSc) (Finset.mem_union_right _ (by simp [hwu']))
  · omega

private lemma graphG4_delete_clique_right {u v : Fin 16} (huv : u ≠ v) (huR : 8 ≤ u.val) (hvR : 8 ≤ v.val) :
    ¬ IsKExtendable (graphG4.deleteEdges {s(u, v)}) 4 := by
  intro hext'
  let G' := graphG4.deleteEdges {s(u, v)}
  let u' : Fin 16 := ⟨u.val - 8, by omega⟩
  let v' : Fin 16 := ⟨v.val - 8, by omega⟩
  have hu_inR : u ∈ g4R := Finset.mem_filter.mpr ⟨Finset.mem_univ u, huR⟩
  have hv_inR : v ∈ g4R := Finset.mem_filter.mpr ⟨Finset.mem_univ v, hvR⟩
  have hv_er : v ∈ g4R.erase u := Finset.mem_erase.mpr ⟨huv.symm, hv_inR⟩
  let S : Finset (Fin 16) := ((g4R.erase u).erase v) ∪ {u', v'}
  have hu'v' : u' ≠ v' := by intro h; exact huv (Fin.ext (by have := congrArg Fin.val h; dsimp [u', v'] at this; omega))
  have hdisjS : Disjoint ((g4R.erase u).erase v) {u', v'} := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    have hxR : 8 ≤ x.val := (Finset.mem_filter.mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx1))).2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx2
    rcases hx2 with rfl | rfl <;> dsimp [u', v'] at hxR <;> omega
  have hS8 : S.card = 8 := by
    rw [Finset.card_union_of_disjoint hdisjS, Finset.card_erase_of_mem hv_er,
      Finset.card_erase_of_mem hu_inR, Finset.card_pair hu'v', g4R_card]
  have hu_notS : u ∉ S := by
    intro h; simp only [S, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with ⟨_, h, _⟩ | (h | h)
    · exact h rfl
    · have := congrArg Fin.val h; dsimp [u'] at this; omega
    · have := congrArg Fin.val h; dsimp [v'] at this; omega
  have hSPM : HasPM (G'.induce (S : Set (Fin 16))) := by
    rw [induce_deleteEdges_eq_of_notMem _ (Or.inl hu_notS)]
    exact hasPM_induce_union hdisjS
      (graphG4_clique_pm (Or.inr (Finset.erase_subset _ _ |>.trans (Finset.erase_subset _ _)))
        ⟨3, by rw [Finset.card_erase_of_mem hv_er, Finset.card_erase_of_mem hu_inR, g4R_card]⟩)
      (graphG4_clique_pm (Or.inl fun x hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp [u', v']; omega⟩)
        ⟨1, by rw [Finset.card_pair hu'v']⟩)
  have hScPM := (isKExtendable_iff_compl_pm.mp hext').2 S hS8 hSPM
  refine not_hasPM_of_isolated (G := G') (S := Sᶜ) (v := u) (Finset.mem_compl.mpr hu_notS) ?_ hScPM
  intro w hwSc hadj
  rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff] at hadj
  have hadjG : graphG4.Adj u w := hadj.1
  have hne_uv : s(u, w) ≠ s(u, v) := hadj.2
  rcases hadjG.2 with ⟨huL, _⟩ | ⟨_, hwR⟩ | h1 | h2
  · omega
  · have hwv : w ≠ v := fun h => hne_uv (by rw [h])
    have hw_inR : w ∈ g4R := Finset.mem_filter.mpr ⟨Finset.mem_univ w, hwR⟩
    exact (Finset.mem_compl.mp hwSc) (Finset.mem_union_left _
      (Finset.mem_erase.mpr ⟨hwv, Finset.mem_erase.mpr ⟨hadjG.1.symm, hw_inR⟩⟩))
  · omega
  · have hwu' : w = u' := Fin.ext (by dsimp [u']; omega)
    exact (Finset.mem_compl.mp hwSc) (Finset.mem_union_right _ (by simp [hwu']))

private lemma graphG4_delete_cross {u v : Fin 16} (hcross : u.val + 8 = v.val) :
    ¬ IsKExtendable (graphG4.deleteEdges {s(u, v)}) 4 := by
  intro hext'
  have huL : u.val < 8 := by omega
  have hu_inL : u ∈ g4L := Finset.mem_filter.mpr ⟨Finset.mem_univ u, huL⟩
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hu_inL, g4L_card]; omega : 0 < (g4L.erase u).card)
  have hwu : w ≠ u := (Finset.mem_erase.mp hw).1
  have hw_inL : w ∈ g4L := Finset.mem_of_mem_erase hw
  have hwL : w.val < 8 := (Finset.mem_filter.mp hw_inL).2
  let w' : Fin 16 := ⟨w.val + 8, by omega⟩
  let S : Finset (Fin 16) := insert w' (g4L.erase u)
  have hw'_notL : w' ∉ g4L.erase u := fun h => by
    have := (Finset.mem_filter.mp (Finset.mem_of_mem_erase h)).2; dsimp [w'] at this; omega
  have hS8 : S.card = 8 := by
    rw [Finset.card_insert_of_notMem hw'_notL, Finset.card_erase_of_mem hu_inL, g4L_card]
  have hu_notS : u ∉ S := by
    intro h; simp only [S, Finset.mem_insert, Finset.mem_erase] at h
    rcases h with h | ⟨h, _⟩
    · have := congrArg Fin.val h; dsimp [w'] at this; omega
    · exact h rfl
  have hSsplit : S = ({w, w'} : Finset (Fin 16)) ∪ ((g4L.erase u).erase w) := by
    ext x; simp only [S, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]
    constructor
    · rintro (rfl | ⟨h1, h2⟩)
      · exact Or.inl (Or.inr rfl)
      · by_cases hxw : x = w; · exact Or.inl (Or.inl hxw)
        exact Or.inr ⟨hxw, h1, h2⟩
    · rintro ((rfl | rfl) | ⟨_, h1, h2⟩)
      · exact Or.inr ⟨hwu, hw_inL⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨h1, h2⟩
  have hdisj : Disjoint ({w, w'} : Finset (Fin 16)) ((g4L.erase u).erase w) := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx1
    rcases hx1 with rfl | rfl
    · exact (Finset.mem_erase.mp hx2).1 rfl
    · exact hw'_notL (Finset.mem_of_mem_erase hx2)
  have hww' : graphG4.Adj w w' := ⟨by intro h; have := congrArg Fin.val h; dsimp [w'] at this; omega,
    Or.inr (Or.inr (Or.inl rfl))⟩
  have hSPM : HasPM ((graphG4.deleteEdges {s(u, v)}).induce (S : Set (Fin 16))) := by
    rw [induce_deleteEdges_eq_of_notMem _ (Or.inl hu_notS), hSsplit]
    exact hasPM_induce_union hdisj (hasPM_induce_pair hww')
      (graphG4_clique_pm (Or.inl (Finset.erase_subset _ _ |>.trans (Finset.erase_subset _ _)))
        ⟨3, by rw [Finset.card_erase_of_mem hw, Finset.card_erase_of_mem hu_inL, g4L_card]⟩)
  have hScPM := (isKExtendable_iff_compl_pm.mp hext').2 S hS8 hSPM
  refine not_hasPM_of_isolated (G := graphG4.deleteEdges {s(u, v)}) (S := Sᶜ) (v := u)
    (Finset.mem_compl.mpr hu_notS) ?_ hScPM
  intro z hzSc hadj
  rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff] at hadj
  have hadjG : graphG4.Adj u z := hadj.1
  have hne_uv : s(u, z) ≠ s(u, v) := hadj.2
  rcases hadjG.2 with ⟨_, hzL⟩ | ⟨huR, _⟩ | h1 | h2
  · have hz_inL : z ∈ g4L := Finset.mem_filter.mpr ⟨Finset.mem_univ z, hzL⟩
    exact (Finset.mem_compl.mp hzSc) (Finset.mem_insert_of_mem
      (Finset.mem_erase.mpr ⟨hadjG.1.symm, hz_inL⟩))
  · omega
  · exact hne_uv (by rw [show z = v from Fin.ext (by omega)])
  · omega

/-- **Attainability of `δ = 8`**: `G_4 = (K_8 ⊔ K_8) + M_8` on `Fin 16` is connected, minimally
4-extendable, and 8-regular. -/
theorem witness_delta_8 :
    graphG4.Connected ∧ IsMinimallyKExtendable graphG4 4 ∧ ∀ v : Fin 16, graphG4.degree v = 8 := by
  have hmin : IsMinimallyKExtendable graphG4 4 := by
    refine ⟨graphG4_isKExtendable, fun e he => ?_⟩
    induction e using Sym2.ind with
    | _ u v =>
      have huv : graphG4.Adj u v := he
      rcases huv.2 with ⟨huL, hvL⟩ | ⟨huR, hvR⟩ | hcross | hcross
      · exact graphG4_delete_clique_left huv.1 huL hvL
      · exact graphG4_delete_clique_right huv.1 huR hvR
      · exact graphG4_delete_cross hcross
      · rw [Sym2.eq_swap]; exact graphG4_delete_cross hcross
  exact ⟨graphG4_connected, hmin, by decide⟩

end Attainability

end LouYuK4
