import LouYuK4.Order16Closure

/-!
# Order ν = 16, Part B: Obstruction Counting (`128 < 160`)

We prove `nu_eq_16_upper`: Every minimally 4-extendable graph on 16 vertices has `δ(G) ≤ 9`.

Assuming `∀ v, 10 ≤ G.degree v`, `Order16Closure.nu_eq_16_no_bad_eight` gives that `F = Gᶜ`
has `Δ(F) ≤ 5` and NO `K₅`, NO `K₃ ∨ 3K₁`, and NO `K₃,₅`.
Then `|{(u, v) : G.Adj u v}| ≥ 160`, while every ordered edge `(u, v)` of `G` must satisfy one
of the five Tutte obstruction patterns from `SmallTutte.not_hasPM_eight_of_compl_le_six`.
Global charging yields:
- Patterns 1 ∪ 2a: `≤ 32` ordered pairs,
- Pattern 5 (`K₁ ∨ K₃,₃`): `≤ 32` ordered pairs,
- Patterns 4, 3, 2b: `≤ |O| + 3|O| + 2|C| ≤ 4(|O| + |C|) ≤ 64` ordered pairs,
where `O` and `C` are the disjoint sets of degree-5 open twins and degree-5 closed twins in `F`.
Thus `160 ≤ 32 + 32 + 64 = 128`, contradiction.
-/

open SimpleGraph Finset

namespace LouYuK4

section Order16Count

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Directed Pattern 5 (`K₁ ∨ K₃,₃`): `x` has degree 5 in `F`, `¬ F.Adj x y`, and `N_F(x)`
partitions into `X` (size 2) and `Y` (size 3) with `X` complete to `Y` and `y` complete to `Y`. -/
def HasP5Dir (F : SimpleGraph V) [DecidableRel F.Adj] (x y : V) : Prop :=
  x ≠ y ∧ F.degree x = 5 ∧ ¬ F.Adj x y ∧
  ∃ X Y : Finset V, X.card = 2 ∧ Y.card = 3 ∧ Disjoint X Y ∧ X ∪ Y = F.neighborFinset x ∧
    (∀ a ∈ X, ∀ b ∈ Y, F.Adj a b) ∧ (∀ b ∈ Y, F.Adj y b)

/-- Every obstructed edge `u v` (when `Δ(F) ≤ 5` and `¬ HasBad8 F`) satisfies one of the
six concrete patterns P1, P2a, P2b, P3, P4, P5. -/
lemma obstructed_edge_eight_cases {F : SimpleGraph V} [DecidableRel F.Adj]
    (hdeg : ∀ w : V, F.degree w ≤ 5) (hgood : ¬ HasBad8 F)
    {u v : V} (huv : u ≠ v) (hnF : ¬ F.Adj u v)
    {S : Finset V} (hS : S.card = 8)
    (hnoPM : ¬ HasPM (((F ⊔ SimpleGraph.edge u v).induce (S : Set V))ᶜ)) :
    -- P1: K₅ - uv
    (∃ a b c : V, F.Adj a b ∧ F.Adj b c ∧ F.Adj a c ∧
      F.Adj u a ∧ F.Adj u b ∧ F.Adj u c ∧ F.Adj v a ∧ F.Adj v b ∧ F.Adj v c) ∨
    -- P2a: K₃ ∨ 3K₁ with uv inside A
    (∃ a : V, F.degree a = 5 ∧ F.Adj a u ∧ F.Adj a v ∧
      ∀ w ∈ ((F.neighborFinset a).erase u).erase v, F.Adj u w ∧ F.Adj v w) ∨
    -- P2b: K₃ ∨ 3K₁ with uv between A and B (closed twin pair {a₁, a₂})
    (∃ a₁ a₂ : V, F.Adj a₁ a₂ ∧ F.degree a₁ = 5 ∧ F.degree a₂ = 5 ∧
      insert a₁ (F.neighborFinset a₁) = insert a₂ (F.neighborFinset a₂) ∧
      u ∈ (F.neighborFinset a₁).erase a₂ ∧ v ∈ (F.neighborFinset a₁).erase a₂ ∧
      ((∀ w ∈ (((F.neighborFinset a₁).erase a₂).erase u).erase v, F.Adj u w) ∨
       (∀ w ∈ (((F.neighborFinset a₁).erase a₂).erase u).erase v, F.Adj v w))) ∨
    -- P3: K₃,₅ - uv (open twin pair {a₁, a₂})
    (∃ a₁ a₂ : V, a₁ ≠ a₂ ∧ F.degree a₁ = 5 ∧ F.degree a₂ = 5 ∧
      F.neighborFinset a₁ = F.neighborFinset a₂ ∧
      ((v ∈ F.neighborFinset a₁ ∧ ∀ w ∈ (F.neighborFinset a₁).erase v, F.Adj u w) ∨
       (u ∈ F.neighborFinset a₁ ∧ ∀ w ∈ (F.neighborFinset a₁).erase u, F.Adj v w))) ∨
    -- P4: K₂ ∨ 5K₁ (u, v are deg-5 open twins)
    (F.degree u = 5 ∧ F.degree v = 5 ∧ F.neighborFinset u = F.neighborFinset v) ∨
    -- P5: K₁ ∨ K₃,₃
    (HasP5Dir F u v ∨ HasP5Dir F v u) := by
  classical
  have hnoK5 : ¬ HasClique F 5 := fun h => hgood (Or.inl h)
  have hnoK331 : ¬ HasCliqueJoin F 3 3 := fun h => hgood (Or.inr (Or.inl h))
  have hnoK35 : ¬ HasK F 3 5 := fun h => hgood (Or.inr (Or.inr h))
  have hdeg6 : ∀ x : (S : Set V), ((F ⊔ SimpleGraph.edge u v).induce (S : Set V)).degree x ≤ 6 := fun x =>
    le_trans (degree_induce_le (F ⊔ SimpleGraph.edge u v) S x)
      (le_trans (degree_sup_edge_le F u v x.val) (by have := hdeg x.val; split_ifs <;> omega))
  have hno_edge : ∀ x y : V, (F ⊔ SimpleGraph.edge u v).Adj x y →
      ¬ (x = u ∧ y = v) → ¬ (x = v ∧ y = u) → F.Adj x y := by
    intro x y h h1 h2
    rw [sup_edge_adj_iff] at h
    rcases h with hF | ⟨h' | h', _⟩
    · exact hF
    · exact absurd h' h1
    · exact absurd h' h2
  have hclass := not_hasPM_eight_of_compl_le_six (by rw [card_coe_finset_set, hS]) hdeg6 hnoPM
  rcases hclass with ⟨K, hK5, hKcl⟩ | ⟨A, B, hA3, hB3, hdisj, hcl, hadj⟩ |
      ⟨A, B, hA3, hB5, hdisj, hadj⟩ | ⟨A, B, hA2, hB5, hdisj, hcl, hadj⟩ |
      ⟨z, A, B, hzA, hzB, hA3, hB3, hdisj, h1, h2, h3⟩
  · -- Pattern 1: K₅ in F ⊔ edge u v => u, v ∈ KV and remaining 3 vertices form triangle in N(u) ∩ N(v)!
    let KV := K.image Subtype.val
    have hKV5 : KV.card = 5 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hK5]
    have hKVcl : (F ⊔ SimpleGraph.edge u v).IsClique (KV : Set V) := fun x hx y hy hxy => by
      rw [Finset.mem_coe, Finset.mem_image] at hx hy
      obtain ⟨p, hp, rfl⟩ := hx; obtain ⟨q, hq, rfl⟩ := hy
      exact hKcl hp hq (fun h => hxy (congrArg Subtype.val h))
    have huvKV : u ∈ KV ∧ v ∈ KV := by
      by_contra hnot
      refine hnoK5 ⟨KV, hKV5, fun x hx y hy hxy => ?_⟩
      exact hno_edge x y (hKVcl hx hy hxy) (fun ⟨h1, h2⟩ => hnot ⟨h1 ▸ hx, h2 ▸ hy⟩)
        (fun ⟨h1, h2⟩ => hnot ⟨h2 ▸ hy, h1 ▸ hx⟩)
    let T3 := (KV.erase u).erase v
    have hv_er : v ∈ KV.erase u := Finset.mem_erase.mpr ⟨huv.symm, huvKV.2⟩
    have hT3 : T3.card = 3 := by
      rw [Finset.card_erase_of_mem hv_er, Finset.card_erase_of_mem huvKV.1, hKV5]
    obtain ⟨a, b, c, hab, hac, hbc, hT3eq⟩ := Finset.card_eq_three.mp hT3
    have haT : a ∈ T3 := by rw [hT3eq]; simp
    have hbT : b ∈ T3 := by rw [hT3eq]; simp
    have hcT : c ∈ T3 := by rw [hT3eq]; simp
    have hmem : ∀ x ∈ T3, x ∈ KV ∧ x ≠ u ∧ x ≠ v := fun x hx =>
      ⟨Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx),
       (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx)).1,
       (Finset.mem_erase.mp hx).1⟩
    obtain ⟨haKV, hau, hav⟩ := hmem a haT
    obtain ⟨hbKV, hbu, hbv⟩ := hmem b hbT
    obtain ⟨hcKV, hcu, hcv⟩ := hmem c hcT
    refine Or.inl ⟨a, b, c, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hno_edge a b (hKVcl haKV hbKV hab) (fun h => hau h.1) (fun h => hav h.1)
    · exact hno_edge b c (hKVcl hbKV hcKV hbc) (fun h => hbu h.1) (fun h => hbv h.1)
    · exact hno_edge a c (hKVcl haKV hcKV hac) (fun h => hau h.1) (fun h => hav h.1)
    · exact hno_edge u a (hKVcl huvKV.1 haKV hau.symm) (fun h => hav h.2) (fun h => huv h.1)
    · exact hno_edge u b (hKVcl huvKV.1 hbKV hbu.symm) (fun h => hbv h.2) (fun h => huv h.1)
    · exact hno_edge u c (hKVcl huvKV.1 hcKV hcu.symm) (fun h => hcv h.2) (fun h => huv h.1)
    · exact hno_edge v a (hKVcl huvKV.2 haKV hav.symm) (fun h => huv.symm h.1) (fun h => hau h.2)
    · exact hno_edge v b (hKVcl huvKV.2 hbKV hbv.symm) (fun h => huv.symm h.1) (fun h => hbu h.2)
    · exact hno_edge v c (hKVcl huvKV.2 hcKV hcv.symm) (fun h => huv.symm h.1) (fun h => hcu h.2)
  · -- Pattern 2: K₃ ∨ 3K₁ in F ⊔ edge u v => either {u,v} ⊆ AV (P2a) or one in AV, one in BV (P2b)!
    let AV := A.image Subtype.val; let BV := B.image Subtype.val
    have hAV3 : AV.card = 3 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hA3]
    have hBV3 : BV.card = 3 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hB3]
    have hdisjV : Disjoint AV BV := by
      rw [Finset.disjoint_left]; intro x hx hy
      rw [Finset.mem_image] at hx hy
      obtain ⟨p, hp, rfl⟩ := hx; obtain ⟨q, hq, he⟩ := hy
      exact Finset.disjoint_left.mp hdisj hp ((Subtype.ext he) ▸ hq)
    have hAcl' : ∀ x ∈ AV, ∀ y ∈ AV, x ≠ y → (F ⊔ SimpleGraph.edge u v).Adj x y := fun x hx y hy hxy => by
      rw [Finset.mem_image] at hx hy; obtain ⟨p, hp, rfl⟩ := hx; obtain ⟨q, hq, rfl⟩ := hy
      exact hcl hp hq (fun h => hxy (congrArg Subtype.val h))
    have hAB' : ∀ x ∈ AV, ∀ y ∈ BV, (F ⊔ SimpleGraph.edge u v).Adj x y := fun x hx y hy => by
      rw [Finset.mem_image] at hx hy; obtain ⟨p, hp, rfl⟩ := hx; obtain ⟨q, hq, rfl⟩ := hy
      exact hadj p hp q hq
    by_cases h2a : u ∈ AV ∧ v ∈ AV
    · -- P2a: A = {u, v, a}
      have hv_er : v ∈ AV.erase u := Finset.mem_erase.mpr ⟨huv.symm, h2a.2⟩
      have h1card : ((AV.erase u).erase v).card = 1 := by
        rw [Finset.card_erase_of_mem hv_er, Finset.card_erase_of_mem h2a.1, hAV3]
      obtain ⟨a, haeq⟩ := Finset.card_eq_one.mp h1card
      have ha_mem : a ∈ (AV.erase u).erase v := by rw [haeq]; simp
      have hav : a ≠ v := (Finset.mem_erase.mp ha_mem).1
      have hau : a ≠ u := (Finset.mem_erase.mp (Finset.mem_of_mem_erase ha_mem)).1
      have haAV : a ∈ AV := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ha_mem)
      have hau_adj : F.Adj a u := hno_edge a u (hAcl' a haAV u h2a.1 hau) (fun h => hau h.1) (fun h => hav h.1)
      have hav_adj : F.Adj a v := hno_edge a v (hAcl' a haAV v h2a.2 hav) (fun h => hau h.1) (fun h => hav h.1)
      have hdisj_uvB : Disjoint ({u, v} : Finset V) BV :=
        Disjoint.mono (fun x hx => by simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl; exact h2a.1; exact h2a.2) le_rfl hdisjV
      have hNa : F.neighborFinset a = {u, v} ∪ BV := by
        refine neighborFinset_eq_of_subset_card_five (hdeg a) ?_ ?_
        · rw [Finset.card_union_of_disjoint hdisj_uvB, Finset.card_pair huv, hBV3]
        · intro w hw; rw [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with (rfl | rfl) | hwB
          · exact hau_adj
          · exact hav_adj
          · exact hno_edge a w (hAB' a haAV w hwB) (fun h => hau h.1) (fun h => hav h.1)
      have hda5 : F.degree a = 5 := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree, hNa, Finset.card_union_of_disjoint hdisj_uvB,
          Finset.card_pair huv, hBV3]
      refine Or.inr (Or.inl ⟨a, hda5, hau_adj, hav_adj, fun w hw => ?_⟩)
      rw [hNa, Finset.mem_erase, Finset.mem_erase, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hw
      have hwB : w ∈ BV := by tauto
      have hwu : w ≠ u := hw.2.1
      have hwv : w ≠ v := hw.1
      exact ⟨hno_edge u w (hAB' u h2a.1 w hwB) (fun h => hwv h.2) (fun h => huv h.1),
             hno_edge v w (hAB' v h2a.2 w hwB) (fun h => huv.symm h.1) (fun h => hwu h.2)⟩
    · by_cases h2b : (u ∈ AV ∧ v ∈ BV) ∨ (v ∈ AV ∧ u ∈ BV)
      · -- P2b: pick {a₁, a₂} = AV \ {x} where x ∈ {u, v} ∩ AV!
        have hP2b_sym : ∀ (x y : V), x ∈ AV → y ∈ BV → ((x = u ∧ y = v) ∨ (x = v ∧ y = u)) →
            ∃ a₁ a₂ : V, F.Adj a₁ a₂ ∧ F.degree a₁ = 5 ∧ F.degree a₂ = 5 ∧
              insert a₁ (F.neighborFinset a₁) = insert a₂ (F.neighborFinset a₂) ∧
              u ∈ (F.neighborFinset a₁).erase a₂ ∧ v ∈ (F.neighborFinset a₁).erase a₂ ∧
              ((∀ w ∈ (((F.neighborFinset a₁).erase a₂).erase u).erase v, F.Adj u w) ∨
               (∀ w ∈ (((F.neighborFinset a₁).erase a₂).erase u).erase v, F.Adj v w)) := by
          intro x y hxAV hyBV hxy_uv
          have hxy : x ≠ y := fun h => Finset.disjoint_left.mp hdisjV hxAV (h ▸ hyBV)
          have hA2 : (AV.erase x).card = 2 := by rw [Finset.card_erase_of_mem hxAV, hAV3]
          obtain ⟨a₁, a₂, ha12, hAeq⟩ := Finset.card_eq_two.mp hA2
          have ha₁_er : a₁ ∈ AV.erase x := by rw [hAeq]; simp
          have ha₂_er : a₂ ∈ AV.erase x := by rw [hAeq]; simp
          have ha₁x : a₁ ≠ x := (Finset.mem_erase.mp ha₁_er).1
          have ha₂x : a₂ ≠ x := (Finset.mem_erase.mp ha₂_er).1
          have ha₁AV : a₁ ∈ AV := Finset.mem_of_mem_erase ha₁_er
          have ha₂AV : a₂ ∈ AV := Finset.mem_of_mem_erase ha₂_er
          have ha₁y : a₁ ≠ y := fun h => Finset.disjoint_left.mp hdisjV ha₁AV (h ▸ hyBV)
          have ha₂y : a₂ ≠ y := fun h => Finset.disjoint_left.mp hdisjV ha₂AV (h ▸ hyBV)
          have hne_uv : ∀ a : V, a ≠ x → a ≠ y → ∀ w : V, ¬ (a = u ∧ w = v) ∧ ¬ (a = v ∧ w = u) := by
            intro a hax hay w
            rcases hxy_uv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact ⟨fun h => hax h.1, fun h => hay h.1⟩
            · exact ⟨fun h => hay h.1, fun h => hax h.1⟩
          have ha12_adj : F.Adj a₁ a₂ :=
            hno_edge a₁ a₂ (hAcl' a₁ ha₁AV a₂ ha₂AV ha12) (hne_uv a₁ ha₁x ha₁y a₂).1 (hne_uv a₁ ha₁x ha₁y a₂).2
          have hRset : AV = {x, a₁, a₂} := by
            ext t; constructor
            · intro ht; by_cases htx : t = x
              · simp [htx]
              · have := Finset.mem_erase.mpr ⟨htx, ht⟩; rw [hAeq] at this
                simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢; tauto
            · intro ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
              rcases ht with rfl | rfl | rfl <;> assumption
          have hNa₁ : F.neighborFinset a₁ = insert a₂ (insert x BV) := by
            refine neighborFinset_eq_of_subset_card_five (hdeg a₁) ?_ ?_
            · have hxB : x ∉ BV := Finset.disjoint_left.mp hdisjV hxAV
              have ha2xB : a₂ ∉ insert x BV := by
                rw [Finset.mem_insert, not_or]; exact ⟨ha₂x, Finset.disjoint_left.mp hdisjV ha₂AV⟩
              rw [Finset.card_insert_of_notMem ha2xB, Finset.card_insert_of_notMem hxB, hBV3]
            · intro w hw; simp only [Finset.mem_insert] at hw
              rcases hw with hw1 | hw2 | hwB
              · rw [hw1]; exact ha12_adj
              · rw [hw2]; exact hno_edge a₁ x (hAcl' a₁ ha₁AV x hxAV ha₁x) (hne_uv a₁ ha₁x ha₁y x).1 (hne_uv a₁ ha₁x ha₁y x).2
              · exact hno_edge a₁ w (hAB' a₁ ha₁AV w hwB) (hne_uv a₁ ha₁x ha₁y w).1 (hne_uv a₁ ha₁x ha₁y w).2
          have hNa₂ : F.neighborFinset a₂ = insert a₁ (insert x BV) := by
            refine neighborFinset_eq_of_subset_card_five (hdeg a₂) ?_ ?_
            · have hxB : x ∉ BV := Finset.disjoint_left.mp hdisjV hxAV
              have ha1xB : a₁ ∉ insert x BV := by
                rw [Finset.mem_insert, not_or]; exact ⟨ha₁x, Finset.disjoint_left.mp hdisjV ha₁AV⟩
              rw [Finset.card_insert_of_notMem ha1xB, Finset.card_insert_of_notMem hxB, hBV3]
            · intro w hw; simp only [Finset.mem_insert] at hw
              rcases hw with hw1 | hw2 | hwB
              · rw [hw1]; exact ha12_adj.symm
              · rw [hw2]; exact hno_edge a₂ x (hAcl' a₂ ha₂AV x hxAV ha₂x) (hne_uv a₂ ha₂x ha₂y x).1 (hne_uv a₂ ha₂x ha₂y x).2
              · exact hno_edge a₂ w (hAB' a₂ ha₂AV w hwB) (hne_uv a₂ ha₂x ha₂y w).1 (hne_uv a₂ ha₂x ha₂y w).2
          have hda₁ : F.degree a₁ = 5 := by
            rw [← SimpleGraph.card_neighborFinset_eq_degree, hNa₁]
            have hxB : x ∉ BV := Finset.disjoint_left.mp hdisjV hxAV
            have ha2xB : a₂ ∉ insert x BV := by rw [Finset.mem_insert, not_or]; exact ⟨ha₂x, Finset.disjoint_left.mp hdisjV ha₂AV⟩
            rw [Finset.card_insert_of_notMem ha2xB, Finset.card_insert_of_notMem hxB, hBV3]
          have hda₂ : F.degree a₂ = 5 := by
            rw [← SimpleGraph.card_neighborFinset_eq_degree, hNa₂]
            have hxB : x ∉ BV := Finset.disjoint_left.mp hdisjV hxAV
            have ha1xB : a₁ ∉ insert x BV := by rw [Finset.mem_insert, not_or]; exact ⟨ha₁x, Finset.disjoint_left.mp hdisjV ha₁AV⟩
            rw [Finset.card_insert_of_notMem ha1xB, Finset.card_insert_of_notMem hxB, hBV3]
          have hclosed : insert a₁ (F.neighborFinset a₁) = insert a₂ (F.neighborFinset a₂) := by
            rw [hNa₁, hNa₂, Finset.insert_comm]
          have herase : (F.neighborFinset a₁).erase a₂ = insert x BV := by
            rw [hNa₁, Finset.erase_insert]
            rw [Finset.mem_insert, not_or]; exact ⟨ha₂x, Finset.disjoint_left.mp hdisjV ha₂AV⟩
          have hx_in : x ∈ (F.neighborFinset a₁).erase a₂ := by rw [herase]; exact Finset.mem_insert_self x BV
          have hy_in : y ∈ (F.neighborFinset a₁).erase a₂ := by rw [herase]; exact Finset.mem_insert_of_mem hyBV
          have hrem : ∀ w ∈ (((F.neighborFinset a₁).erase a₂).erase x).erase y, F.Adj x w := by
            intro w hw
            rw [herase, Finset.mem_erase, Finset.mem_erase, Finset.mem_insert] at hw
            have hwB : w ∈ BV := hw.2.2.resolve_left hw.2.1
            have hwy : w ≠ y := hw.1
            rcases hxy_uv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hno_edge x w (hAB' x hxAV w hwB) (fun h => hwy h.2) (fun h => hxy h.1)
            · exact hno_edge x w (hAB' x hxAV w hwB) (fun h => hxy h.1) (fun h => hwy h.2)
          refine ⟨a₁, a₂, ha12_adj, hda₁, hda₂, hclosed, ?_, ?_, ?_⟩
          · rcases hxy_uv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
          · rcases hxy_uv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
          · rcases hxy_uv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inl hrem
            · right; intro w hw; apply hrem w; rwa [Finset.erase_right_comm]
        rcases h2b with ⟨huA, hvB⟩ | ⟨hvA, huB⟩
        · exact Or.inr (Or.inr (Or.inl (hP2b_sym u v huA hvB (Or.inl ⟨rfl, rfl⟩))))
        · exact Or.inr (Or.inr (Or.inl (hP2b_sym v u hvA huB (Or.inr ⟨rfl, rfl⟩))))
      · exfalso
        refine hnoK331 ⟨AV, BV, hAV3, hBV3, hdisjV, ?_, ?_⟩
        · intro x hx y hy hxy
          exact hno_edge x y (hAcl' x hx y hy hxy) (fun ⟨h1, h2⟩ => h2a ⟨h1 ▸ hx, h2 ▸ hy⟩)
            (fun ⟨h1, h2⟩ => h2a ⟨h2 ▸ hy, h1 ▸ hx⟩)
        · intro x hx y hy
          exact hno_edge x y (hAB' x hx y hy) (fun ⟨h1, h2⟩ => h2b (Or.inl ⟨h1 ▸ hx, h2 ▸ hy⟩))
            (fun ⟨h1, h2⟩ => h2b (Or.inr ⟨h1 ▸ hx, h2 ▸ hy⟩))
  · -- Pattern 3: K₃,₅ in F ⊔ edge u v => one of u, v in AV and the other in BV!
    let AV := A.image Subtype.val; let BV := B.image Subtype.val
    have hAV3 : AV.card = 3 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hA3]
    have hBV5 : BV.card = 5 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hB5]
    have hdisjV : Disjoint AV BV := by
      rw [Finset.disjoint_left]; intro x hx hy
      rw [Finset.mem_image] at hx hy
      obtain ⟨p, hp, rfl⟩ := hx; obtain ⟨q, hq, he⟩ := hy
      exact Finset.disjoint_left.mp hdisj hp ((Subtype.ext he) ▸ hq)
    have hAB' : ∀ x ∈ AV, ∀ y ∈ BV, (F ⊔ SimpleGraph.edge u v).Adj x y := fun x hx y hy => by
      rw [Finset.mem_image] at hx hy; obtain ⟨p, hp, rfl⟩ := hx; obtain ⟨q, hq, rfl⟩ := hy
      exact hadj p hp q hq
    have hP3_sym : ∀ (x y : V), x ∈ AV → y ∈ BV → ((x = u ∧ y = v) ∨ (x = v ∧ y = u)) →
        ∃ a₁ a₂ : V, a₁ ≠ a₂ ∧ F.degree a₁ = 5 ∧ F.degree a₂ = 5 ∧
          F.neighborFinset a₁ = F.neighborFinset a₂ ∧
          y ∈ F.neighborFinset a₁ ∧ ∀ w ∈ (F.neighborFinset a₁).erase y, F.Adj x w := by
      intro x y hxAV hyBV hxy_uv
      have hxy : x ≠ y := fun h => Finset.disjoint_left.mp hdisjV hxAV (h ▸ hyBV)
      have hA2 : (AV.erase x).card = 2 := by rw [Finset.card_erase_of_mem hxAV, hAV3]
      obtain ⟨a₁, a₂, ha12, hAeq⟩ := Finset.card_eq_two.mp hA2
      have ha₁_er : a₁ ∈ AV.erase x := by rw [hAeq]; simp
      have ha₂_er : a₂ ∈ AV.erase x := by rw [hAeq]; simp
      have ha₁x : a₁ ≠ x := (Finset.mem_erase.mp ha₁_er).1
      have ha₂x : a₂ ≠ x := (Finset.mem_erase.mp ha₂_er).1
      have ha₁AV : a₁ ∈ AV := Finset.mem_of_mem_erase ha₁_er
      have ha₂AV : a₂ ∈ AV := Finset.mem_of_mem_erase ha₂_er
      have ha₁y : a₁ ≠ y := fun h => Finset.disjoint_left.mp hdisjV ha₁AV (h ▸ hyBV)
      have ha₂y : a₂ ≠ y := fun h => Finset.disjoint_left.mp hdisjV ha₂AV (h ▸ hyBV)
      have hne_uv : ∀ a : V, a ≠ x → a ≠ y → ∀ w : V, ¬ (a = u ∧ w = v) ∧ ¬ (a = v ∧ w = u) := by
        intro a hax hay w
        rcases hxy_uv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨fun h => hax h.1, fun h => hay h.1⟩
        · exact ⟨fun h => hay h.1, fun h => hax h.1⟩
      have hNa₁ : F.neighborFinset a₁ = BV :=
        neighborFinset_eq_of_subset_card_five (hdeg a₁) hBV5 fun w hw =>
          hno_edge a₁ w (hAB' a₁ ha₁AV w hw) (hne_uv a₁ ha₁x ha₁y w).1 (hne_uv a₁ ha₁x ha₁y w).2
      have hNa₂ : F.neighborFinset a₂ = BV :=
        neighborFinset_eq_of_subset_card_five (hdeg a₂) hBV5 fun w hw =>
          hno_edge a₂ w (hAB' a₂ ha₂AV w hw) (hne_uv a₂ ha₂x ha₂y w).1 (hne_uv a₂ ha₂x ha₂y w).2
      have hda₁ : F.degree a₁ = 5 := by rw [← SimpleGraph.card_neighborFinset_eq_degree, hNa₁, hBV5]
      have hda₂ : F.degree a₂ = 5 := by rw [← SimpleGraph.card_neighborFinset_eq_degree, hNa₂, hBV5]
      refine ⟨a₁, a₂, ha12, hda₁, hda₂, hNa₁.trans hNa₂.symm, hNa₁.symm ▸ hyBV, fun w hw => ?_⟩
      rw [hNa₁, Finset.mem_erase] at hw
      rcases hxy_uv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hno_edge x w (hAB' x hxAV w hw.2) (fun h => hw.1 h.2) (fun h => hxy h.1)
      · exact hno_edge x w (hAB' x hxAV w hw.2) (fun h => hxy h.1) (fun h => hw.1 h.2)
    by_cases h1 : u ∈ AV ∧ v ∈ BV
    · obtain ⟨a₁, a₂, h1', h2', h3', h4', h5', h6'⟩ := hP3_sym u v h1.1 h1.2 (Or.inl ⟨rfl, rfl⟩)
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a₁, a₂, h1', h2', h3', h4', Or.inl ⟨h5', h6'⟩⟩)))
    · by_cases h2 : v ∈ AV ∧ u ∈ BV
      · obtain ⟨a₁, a₂, h1', h2', h3', h4', h5', h6'⟩ := hP3_sym v u h2.1 h2.2 (Or.inr ⟨rfl, rfl⟩)
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a₁, a₂, h1', h2', h3', h4', Or.inr ⟨h5', h6'⟩⟩)))
      · exfalso
        refine hnoK35 ⟨AV, BV, hAV3, hBV5, hdisjV, fun x hx y hy => ?_⟩
        exact hno_edge x y (hAB' x hx y hy) (fun ⟨ha, hb⟩ => h1 ⟨ha ▸ hx, hb ▸ hy⟩)
          (fun ⟨ha, hb⟩ => h2 ⟨ha ▸ hx, hb ▸ hy⟩)
  · -- Pattern 4: K₂ ∨ 5K₁ => both vertices of A have degree 6 in F ⊔ edge u v => A = {u, v}, deg-5 open twins!
    obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hA2
    let BV := B.image Subtype.val
    have hBV5 : BV.card = 5 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hB5]
    have hp6 : 6 ≤ (F ⊔ SimpleGraph.edge u v).degree p.val := by
      have hsub : insert q.val BV ⊆ (F ⊔ SimpleGraph.edge u v).neighborFinset p.val := fun w hw => by
        rw [Finset.mem_insert] at hw; rw [SimpleGraph.mem_neighborFinset]
        rcases hw with rfl | hwB
        · exact hcl (by simp) (by simp) hpq
        · rw [Finset.mem_image] at hwB; obtain ⟨b, hb, rfl⟩ := hwB; exact hadj p (by simp) b hb
      have hqB : q.val ∉ BV := fun h => by
        rw [Finset.mem_image] at h; obtain ⟨b, hb, he⟩ := h
        exact Finset.disjoint_left.mp hdisj (by simp : q ∈ ({p, q} : Finset _)) ((Subtype.ext he) ▸ hb)
      have hc := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hqB, hBV5, SimpleGraph.card_neighborFinset_eq_degree] at hc; exact hc
    have hq6 : 6 ≤ (F ⊔ SimpleGraph.edge u v).degree q.val := by
      have hsub : insert p.val BV ⊆ (F ⊔ SimpleGraph.edge u v).neighborFinset q.val := fun w hw => by
        rw [Finset.mem_insert] at hw; rw [SimpleGraph.mem_neighborFinset]
        rcases hw with rfl | hwB
        · exact hcl (by simp) (by simp) hpq.symm
        · rw [Finset.mem_image] at hwB; obtain ⟨b, hb, rfl⟩ := hwB; exact hadj q (by simp) b hb
      have hpB : p.val ∉ BV := fun h => by
        rw [Finset.mem_image] at h; obtain ⟨b, hb, he⟩ := h
        exact Finset.disjoint_left.mp hdisj (by simp : p ∈ ({p, q} : Finset _)) ((Subtype.ext he) ▸ hb)
      have hc := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hpB, hBV5, SimpleGraph.card_neighborFinset_eq_degree] at hc; exact hc
    have hpuv : p.val = u ∨ p.val = v := by
      by_contra h; have h1 := degree_sup_edge_le F u v p.val; simp [h] at h1; have := hdeg p.val; omega
    have hquv : q.val = u ∨ q.val = v := by
      by_contra h; have h1 := degree_sup_edge_le F u v q.val; simp [h] at h1; have := hdeg q.val; omega
    have hpq_val : p.val ≠ q.val := fun h => hpq (Subtype.ext h)
    have hNp : F.neighborFinset p.val = BV := by
      refine neighborFinset_eq_of_subset_card_five (hdeg p.val) hBV5 fun w hw => ?_
      rw [Finset.mem_image] at hw; obtain ⟨b, hb, rfl⟩ := hw
      have hbp : b.val ≠ p.val := fun h => Finset.disjoint_left.mp hdisj (by simp : p ∈ ({p, q} : Finset _)) ((Subtype.ext h) ▸ hb)
      have hbq : b.val ≠ q.val := fun h => Finset.disjoint_left.mp hdisj (by simp : q ∈ ({p, q} : Finset _)) ((Subtype.ext h) ▸ hb)
      have h' : (F ⊔ SimpleGraph.edge u v).Adj p.val b.val := hadj p (by simp) b hb
      rcases hpuv with hp' | hp' <;> rcases hquv with hq' | hq'
      · exact absurd (hp'.trans hq'.symm) hpq_val
      · exact hno_edge p.val b.val h' (fun h => hbq (h.2.trans hq'.symm)) (fun h => huv (hp'.symm.trans h.1))
      · exact hno_edge p.val b.val h' (fun h => huv.symm (hp'.symm.trans h.1)) (fun h => hbq (h.2.trans hq'.symm))
      · exact absurd (hp'.trans hq'.symm) hpq_val
    have hNq : F.neighborFinset q.val = BV := by
      refine neighborFinset_eq_of_subset_card_five (hdeg q.val) hBV5 fun w hw => ?_
      rw [Finset.mem_image] at hw; obtain ⟨b, hb, rfl⟩ := hw
      have hbp : b.val ≠ p.val := fun h => Finset.disjoint_left.mp hdisj (by simp : p ∈ ({p, q} : Finset _)) ((Subtype.ext h) ▸ hb)
      have hbq : b.val ≠ q.val := fun h => Finset.disjoint_left.mp hdisj (by simp : q ∈ ({p, q} : Finset _)) ((Subtype.ext h) ▸ hb)
      have h' : (F ⊔ SimpleGraph.edge u v).Adj q.val b.val := hadj q (by simp) b hb
      rcases hpuv with hp' | hp' <;> rcases hquv with hq' | hq'
      · exact absurd (hp'.trans hq'.symm) hpq_val
      · exact hno_edge q.val b.val h' (fun h => huv.symm (hq'.symm.trans h.1)) (fun h => hbp (h.2.trans hp'.symm))
      · exact hno_edge q.val b.val h' (fun h => hbp (h.2.trans hp'.symm)) (fun h => huv (hq'.symm.trans h.1))
      · exact absurd (hp'.trans hq'.symm) hpq_val
    have hdp5 : F.degree p.val = 5 := by rw [← SimpleGraph.card_neighborFinset_eq_degree, hNp, hBV5]
    have hdq5 : F.degree q.val = 5 := by rw [← SimpleGraph.card_neighborFinset_eq_degree, hNq, hBV5]
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    rcases hpuv with hp' | hp' <;> rcases hquv with hq' | hq'
    · exact absurd (hp'.trans hq'.symm) hpq_val
    · rw [← hp', ← hq']; exact ⟨hdp5, hdq5, hNp.trans hNq.symm⟩
    · rw [← hq', ← hp']; exact ⟨hdq5, hdp5, hNq.trans hNp.symm⟩
    · exact absurd (hp'.trans hq'.symm) hpq_val
  · -- Pattern 5: K₁ ∨ K₃,₃ => z has degree 6 in F ⊔ edge u v => z ∈ {u, v}, other vertex in A ∪ B!
    let AV := A.image Subtype.val; let BV := B.image Subtype.val
    have hAV3 : AV.card = 3 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hA3]
    have hBV3 : BV.card = 3 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hB3]
    have hdisjV : Disjoint AV BV := by
      rw [Finset.disjoint_left]; intro x hx hy
      rw [Finset.mem_image] at hx hy
      obtain ⟨p, hp, rfl⟩ := hx; obtain ⟨q, hq, he⟩ := hy
      exact Finset.disjoint_left.mp hdisj hp ((Subtype.ext he) ▸ hq)
    have hz6 : 6 ≤ (F ⊔ SimpleGraph.edge u v).degree z.val := by
      have hsub : AV ∪ BV ⊆ (F ⊔ SimpleGraph.edge u v).neighborFinset z.val := fun w hw => by
        rw [Finset.mem_union] at hw; rw [SimpleGraph.mem_neighborFinset]
        rcases hw with hwA | hwB
        · rw [Finset.mem_image] at hwA; obtain ⟨a, ha, rfl⟩ := hwA; exact h1 a ha
        · rw [Finset.mem_image] at hwB; obtain ⟨b, hb, rfl⟩ := hwB; exact h2 b hb
      have hc := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisjV, hAV3, hBV3, SimpleGraph.card_neighborFinset_eq_degree] at hc
      exact hc
    have hzuv : z.val = u ∨ z.val = v := by
      by_contra h; have h1' := degree_sup_edge_le F u v z.val; simp [h] at h1'; have := hdeg z.val; omega
    have hP5_sym : ∀ (x y : V), z.val = x → ((x = u ∧ y = v) ∨ (x = v ∧ y = u)) → HasP5Dir F x y := by
      intro x y hzx hxy_uv
      have hxy : x ≠ y := by rcases hxy_uv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exact huv; exact huv.symm
      have hnFxy : ¬ F.Adj x y := by rcases hxy_uv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exact hnF; exact fun h => hnF h.symm
      have hy_in : y ∈ AV ∪ BV := by
        by_contra hy_out
        have hsub6 : AV ∪ BV ⊆ F.neighborFinset x := fun w hw => by
          have hwy : w ≠ y := fun h => hy_out (h ▸ hw)
          rw [SimpleGraph.mem_neighborFinset]
          have h' : (F ⊔ SimpleGraph.edge u v).Adj x w := by
            rw [← hzx]; rw [Finset.mem_union] at hw
            rcases hw with hwA | hwB
            · rw [Finset.mem_image] at hwA; obtain ⟨a, ha, rfl⟩ := hwA; exact h1 a ha
            · rw [Finset.mem_image] at hwB; obtain ⟨b, hb, rfl⟩ := hwB; exact h2 b hb
          rcases hxy_uv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hno_edge x w h' (fun h => hwy h.2) (fun h => hxy h.1)
          · exact hno_edge x w h' (fun h => hxy h.1) (fun h => hwy h.2)
        have hc := Finset.card_le_card hsub6
        rw [Finset.card_union_of_disjoint hdisjV, hAV3, hBV3, SimpleGraph.card_neighborFinset_eq_degree] at hc
        have := hdeg x; omega
      have hbuild : ∀ (P Q : Finset V), P.card = 3 → Q.card = 3 → Disjoint P Q →
          y ∈ P → (∀ a ∈ P, (F ⊔ SimpleGraph.edge u v).Adj x a) →
          (∀ b ∈ Q, (F ⊔ SimpleGraph.edge u v).Adj x b) →
          (∀ a ∈ P, ∀ b ∈ Q, (F ⊔ SimpleGraph.edge u v).Adj a b) →
          (∀ a ∈ P, a ≠ x) → (∀ b ∈ Q, b ≠ x) → HasP5Dir F x y := by
        intro P Q hP3 hQ3 hdisjPQ hyP hxP hxQ hPQ hPx hQx
        let X := P.erase y
        have hX2 : X.card = 2 := by rw [Finset.card_erase_of_mem hyP, hP3]
        have hdisjXQ : Disjoint X Q := Disjoint.mono_left (Finset.erase_subset y P) hdisjPQ
        have hNx : F.neighborFinset x = X ∪ Q := by
          refine neighborFinset_eq_of_subset_card_five (hdeg x) (by rw [Finset.card_union_of_disjoint hdisjXQ, hX2, hQ3]) ?_
          intro w hw; rw [Finset.mem_union] at hw
          rcases hw with hwX | hwQ
          · have hwy : w ≠ y := (Finset.mem_erase.mp hwX).1
            have hwP : w ∈ P := Finset.mem_of_mem_erase hwX
            rcases hxy_uv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hno_edge x w (hxP w hwP) (fun h => hwy h.2) (fun h => hxy h.1)
            · exact hno_edge x w (hxP w hwP) (fun h => hxy h.1) (fun h => hwy h.2)
          · have hwy : w ≠ y := fun h => Finset.disjoint_right.mp hdisjPQ hwQ (h ▸ hyP)
            rcases hxy_uv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hno_edge x w (hxQ w hwQ) (fun h => hwy h.2) (fun h => hxy h.1)
            · exact hno_edge x w (hxQ w hwQ) (fun h => hxy h.1) (fun h => hwy h.2)
        have hdx5 : F.degree x = 5 := by
          rw [← SimpleGraph.card_neighborFinset_eq_degree, hNx, Finset.card_union_of_disjoint hdisjXQ, hX2, hQ3]
        refine ⟨hxy, hdx5, hnFxy, X, Q, hX2, hQ3, hdisjXQ, hNx.symm, ?_, ?_⟩
        · intro a ha b hb
          have haP : a ∈ P := Finset.mem_of_mem_erase ha
          have hay : a ≠ y := (Finset.mem_erase.mp ha).1
          have hax : a ≠ x := hPx a haP
          rcases hxy_uv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hno_edge a b (hPQ a haP b hb) (fun h => hax h.1) (fun h => hay h.1)
          · exact hno_edge a b (hPQ a haP b hb) (fun h => hay h.1) (fun h => hax h.1)
        · intro b hb
          have hbx : b ≠ x := hQx b hb
          rcases hxy_uv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hno_edge y b (hPQ y hyP b hb) (fun h => hxy.symm h.1) (fun h => hbx h.2)
          · exact hno_edge y b (hPQ y hyP b hb) (fun h => hbx h.2) (fun h => hxy.symm h.1)
      have hxAV_all : ∀ a ∈ AV, (F ⊔ SimpleGraph.edge u v).Adj x a := fun a ha => by
        rw [Finset.mem_image] at ha; obtain ⟨a', ha', rfl⟩ := ha; rw [← hzx]; exact h1 a' ha'
      have hxBV_all : ∀ b ∈ BV, (F ⊔ SimpleGraph.edge u v).Adj x b := fun b hb => by
        rw [Finset.mem_image] at hb; obtain ⟨b', hb', rfl⟩ := hb; rw [← hzx]; exact h2 b' hb'
      have hAB_all : ∀ a ∈ AV, ∀ b ∈ BV, (F ⊔ SimpleGraph.edge u v).Adj a b := fun a ha b hb => by
        rw [Finset.mem_image] at ha hb; obtain ⟨a', ha', rfl⟩ := ha; obtain ⟨b', hb', rfl⟩ := hb; exact h3 a' ha' b' hb'
      have hAx : ∀ a ∈ AV, a ≠ x := fun a ha h => by
        rw [Finset.mem_image] at ha; obtain ⟨a', ha', rfl⟩ := ha
        exact hzA (Subtype.ext (hzx.trans h.symm) ▸ ha')
      have hBx : ∀ b ∈ BV, b ≠ x := fun b hb h => by
        rw [Finset.mem_image] at hb; obtain ⟨b', hb', rfl⟩ := hb
        exact hzB (Subtype.ext (hzx.trans h.symm) ▸ hb')
      rw [Finset.mem_union] at hy_in
      rcases hy_in with hyA | hyB
      · exact hbuild AV BV hAV3 hBV3 hdisjV hyA hxAV_all hxBV_all hAB_all hAx hBx
      · exact hbuild BV AV hBV3 hAV3 hdisjV.symm hyB hxBV_all hxAV_all (fun b hb a ha => (hAB_all a ha b hb).symm) hBx hAx
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
    rcases hzuv with hzu | hzv
    · exact Or.inl (hP5_sym u v hzu (Or.inl ⟨rfl, rfl⟩))
    · exact Or.inr (hP5_sym v u hzv (Or.inr ⟨rfl, rfl⟩))

/-- **Local Pattern 5 uniqueness**: For a fixed `x : V`, when `Δ(F) ≤ 5` and `¬ HasBad8 F`,
at most ONE vertex `y : V` satisfies `HasP5Dir F x y`. -/
lemma p5_unique_target {F : SimpleGraph V} [DecidableRel F.Adj]
    (hdeg : ∀ w : V, F.degree w ≤ 5) (hgood : ¬ HasBad8 F)
    {x y₁ y₂ : V} (h₁ : HasP5Dir F x y₁) (h₂ : HasP5Dir F x y₂) : y₁ = y₂ := by
  classical
  have hnoK331 : ¬ HasCliqueJoin F 3 3 := fun h => hgood (Or.inr (Or.inl h))
  have hnoK35 : ¬ HasK F 3 5 := fun h => hgood (Or.inr (Or.inr h))
  obtain ⟨hxy₁, hdx, hnx1, X₁, Y₁, hX₁2, hY₁3, hdisj₁, hun₁, hXY₁, hyY₁⟩ := h₁
  obtain ⟨hxy₂, _, hnx2, X₂, Y₂, hX₂2, hY₂3, hdisj₂, hun₂, hXY₂, hyY₂⟩ := h₂
  have hX₁_ind : ∀ a ∈ X₁, ∀ b ∈ X₁, ¬ F.Adj a b := by
    intro a ha b hb hab
    have hX₁pair : X₁ = {a, b} := by
      have hsub : ({a, b} : Finset V) ⊆ X₁ := by intro t ht; simp at ht; rcases ht with rfl | rfl <;> assumption
      exact (Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hab.ne, hX₁2])).symm
    have hx_not_N : x ∉ F.neighborFinset x := by simp
    have hxX₁ : x ∉ X₁ := fun h => hx_not_N (hun₁ ▸ Finset.mem_union_left Y₁ h)
    have hdisj_xXY : Disjoint (insert x X₁) Y₁ := by
      rw [Finset.disjoint_insert_left]
      exact ⟨fun h => hx_not_N (hun₁ ▸ Finset.mem_union_right X₁ h), hdisj₁⟩
    refine hnoK331 ⟨insert x X₁, Y₁, by rw [Finset.card_insert_of_notMem hxX₁, hX₁2], hY₁3, hdisj_xXY, ?_, ?_⟩
    · intro p hp q hq hpq
      rw [Finset.mem_coe, Finset.mem_insert] at hp hq
      rcases hp with hpx | hpX <;> rcases hq with hqx | hqX
      · exact absurd (hpx.trans hqx.symm) hpq
      · rw [hpx]; exact (SimpleGraph.mem_neighborFinset F x q).mp (hun₁ ▸ Finset.mem_union_left Y₁ hqX)
      · rw [hqx]; exact ((SimpleGraph.mem_neighborFinset F x p).mp (hun₁ ▸ Finset.mem_union_left Y₁ hpX)).symm
      · rw [hX₁pair, Finset.mem_insert, Finset.mem_singleton] at hpX hqX
        rcases hpX with rfl | rfl <;> rcases hqX with rfl | rfl
        · exact absurd rfl hpq
        · exact hab
        · exact hab.symm
        · exact absurd rfl hpq
    · intro p hp q hq
      rw [Finset.mem_insert] at hp
      rcases hp with hpx | hpX
      · rw [hpx]; exact (SimpleGraph.mem_neighborFinset F x q).mp (hun₁ ▸ Finset.mem_union_right X₁ hq)
      · exact hXY₁ p hpX q hq
  have hY₁_degN : ∀ w ∈ Y₁, (F.neighborFinset w ∩ F.neighborFinset x).card ≤ 3 := by
    intro w hw
    have hxNw : x ∈ F.neighborFinset w :=
      (SimpleGraph.mem_neighborFinset F w x).mpr ((SimpleGraph.mem_neighborFinset F x w).mp (hun₁ ▸ Finset.mem_union_right X₁ hw)).symm
    have hyNw : y₁ ∈ F.neighborFinset w := (SimpleGraph.mem_neighborFinset F w y₁).mpr (hyY₁ w hw).symm
    have hdisj_xy : Disjoint ({x, y₁} : Finset V) (F.neighborFinset w ∩ F.neighborFinset x) := by
      rw [Finset.disjoint_left]; intro t ht hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      have htNx : t ∈ F.neighborFinset x := (Finset.mem_inter.mp hmem).2
      rw [SimpleGraph.mem_neighborFinset] at htNx
      rcases ht with rfl | rfl
      · exact htNx.ne rfl
      · exact hnx1 htNx
    have hsub : {x, y₁} ∪ (F.neighborFinset w ∩ F.neighborFinset x) ⊆ F.neighborFinset w := by
      intro t ht; rw [Finset.mem_union] at ht
      rcases ht with h | h
      · simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with rfl | rfl <;> assumption
      · exact (Finset.mem_inter.mp h).1
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj_xy, Finset.card_pair hxy₁, SimpleGraph.card_neighborFinset_eq_degree] at hc
    have := hdeg w; omega
  have hXeq : X₁ = X₂ := by
    by_contra hne
    by_cases hdisjX : Disjoint X₁ X₂
    · have hinter : (Y₁ ∩ Y₂).Nonempty := by
        have hunsub : Y₁ ∪ Y₂ ⊆ F.neighborFinset x := Finset.union_subset
          (hun₁ ▸ Finset.subset_union_right) (hun₂ ▸ Finset.subset_union_right)
        have huc := Finset.card_le_card hunsub
        rw [SimpleGraph.card_neighborFinset_eq_degree, hdx] at huc
        have hi := Finset.card_union_add_card_inter Y₁ Y₂
        rw [hY₁3, hY₂3] at hi
        exact Finset.card_pos.mp (by omega : 0 < (Y₁ ∩ Y₂).card)
      obtain ⟨w, hw⟩ := hinter
      have hw1 : w ∈ Y₁ := (Finset.mem_inter.mp hw).1
      have hw2 : w ∈ Y₂ := (Finset.mem_inter.mp hw).2
      have hsub : X₁ ∪ X₂ ⊆ F.neighborFinset w ∩ F.neighborFinset x := by
        intro t ht; rw [Finset.mem_union] at ht; rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
        rcases ht with ht1 | ht2
        · exact ⟨(hXY₁ t ht1 w hw1).symm, hun₁ ▸ Finset.mem_union_left Y₁ ht1⟩
        · exact ⟨(hXY₂ t ht2 w hw2).symm, hun₂ ▸ Finset.mem_union_left Y₂ ht2⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisjX, hX₁2, hX₂2] at hc
      have := hY₁_degN w hw1; omega
    · rw [Finset.not_disjoint_iff] at hdisjX
      obtain ⟨a, ha1, ha2⟩ := hdisjX
      have hnsub : ¬ X₁ ⊆ X₂ := fun hs => hne (Finset.eq_of_subset_of_card_le hs (by omega))
      obtain ⟨b, hb1, hb2⟩ := Finset.not_subset.mp hnsub
      have hbN : b ∈ F.neighborFinset x := hun₁ ▸ Finset.mem_union_left Y₁ hb1
      rw [← hun₂, Finset.mem_union] at hbN
      have hbY₂ : b ∈ Y₂ := hbN.resolve_left hb2
      exact hX₁_ind a ha1 b hb1 (hXY₂ a ha2 b hbY₂)
  have hYeq : Y₁ = Y₂ := by
    ext t; constructor <;> intro ht
    · have htN : t ∈ F.neighborFinset x := hun₁ ▸ Finset.mem_union_right X₁ ht
      have htX : t ∉ X₂ := hXeq ▸ Finset.disjoint_right.mp hdisj₁ ht
      rw [← hun₂, Finset.mem_union] at htN; exact htN.resolve_left htX
    · have htN : t ∈ F.neighborFinset x := hun₂ ▸ Finset.mem_union_right X₂ ht
      have htX : t ∉ X₁ := hXeq.symm ▸ Finset.disjoint_right.mp hdisj₂ ht
      rw [← hun₁, Finset.mem_union] at htN; exact htN.resolve_left htX
  by_contra hy12
  let T : Finset V := {x, y₁, y₂}
  have hT3 : T.card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hy12]
    simp [hxy₁, hxy₂]
  have hdisj_TN : Disjoint T (F.neighborFinset x) := by
    rw [Finset.disjoint_left]; intro t ht htN
    rw [SimpleGraph.mem_neighborFinset] at htN
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact htN.ne rfl
    · exact hnx1 htN
    · exact hnx2 htN
  have hdisj_TX : Disjoint T X₁ := Disjoint.mono_right (hun₁ ▸ Finset.subset_union_left) hdisj_TN
  have hdisj_TY : Disjoint T Y₁ := Disjoint.mono_right (hun₁ ▸ Finset.subset_union_right) hdisj_TN
  have hdisj_Y_TX : Disjoint Y₁ (T ∪ X₁) := Finset.disjoint_union_right.mpr ⟨hdisj_TY.symm, hdisj₁.symm⟩
  refine hnoK35 ⟨Y₁, T ∪ X₁, hY₁3, by rw [Finset.card_union_of_disjoint hdisj_TX, hT3, hX₁2], hdisj_Y_TX, ?_⟩
  intro w hw t ht
  rw [Finset.mem_union] at ht
  rcases ht with htT | htX
  · simp only [T, Finset.mem_insert, Finset.mem_singleton] at htT
    rcases htT with htx | hty1 | hty2
    · rw [htx]; exact ((SimpleGraph.mem_neighborFinset F x w).mp (hun₁ ▸ Finset.mem_union_right X₁ hw)).symm
    · rw [hty1]; exact (hyY₁ w hw).symm
    · rw [hty2]; exact (hyY₂ w (hYeq ▸ hw)).symm
  · exact (hXY₁ t htX w hw).symm

/-- Local charging bound for Patterns 1 and 2a around a fixed vertex `a`:
`|(S1 a)| + 3 * |(S2a a)| ≤ 6` whenever `F.degree a ≤ 5`. -/
lemma local_12a_bound {G : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel Gᶜ.Adj]
    (a : V) (hdeg : Gᶜ.degree a ≤ 5) :
    let F := Gᶜ
    let Na := F.neighborFinset a
    let Gpairs := Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2)
    let S1 := Gpairs.filter (fun p => p.1 ∈ Na ∧ p.2 ∈ Na ∧
      ∃ b ∈ Na, ∃ c ∈ Na, F.Adj b c ∧ F.Adj p.1 b ∧ F.Adj p.1 c ∧ F.Adj p.2 b ∧ F.Adj p.2 c)
    let S2a := Gpairs.filter (fun p => p ∉ S1 ∧ F.degree a = 5 ∧ p.1 ∈ Na ∧ p.2 ∈ Na ∧
      ∀ w ∈ (Na.erase p.1).erase p.2, F.Adj p.1 w ∧ F.Adj p.2 w)
    S1.card + 3 * S2a.card ≤ 6 := by
  classical
  intro F Na Gpairs S1 S2a
  have hNa_le : Na.card ≤ 5 := by simpa [Na, SimpleGraph.card_neighborFinset_eq_degree] using hdeg
  by_cases h2a : S2a.Nonempty
  · obtain ⟨⟨u, v⟩, huv⟩ := h2a
    simp only [S2a, Gpairs, Finset.mem_filter, Finset.mem_univ, true_and] at huv
    obtain ⟨hGuv, hnotS1, hda5, huNa, hvNa, hB_all⟩ := huv
    have huv_ne : u ≠ v := hGuv.ne
    have hnFuv : ¬ F.Adj u v := fun h => h.2 hGuv
    let B := (Na.erase u).erase v
    have hNa5 : Na.card = 5 := by simpa [Na, SimpleGraph.card_neighborFinset_eq_degree] using hda5
    have hB_ind : ∀ b ∈ B, ∀ c ∈ B, ¬ F.Adj b c := by
      intro b hb c hc hbc
      have hbNa : b ∈ Na := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hb)
      have hcNa : c ∈ Na := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc)
      refine hnotS1 ?_
      simp only [S1, Gpairs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hGuv, huNa, hvNa, b, hbNa, c, hcNa, hbc, (hB_all b hb).1, (hB_all c hc).1,
        (hB_all b hb).2, (hB_all c hc).2⟩
    have hNa_part : ∀ w ∈ Na, w = u ∨ w = v ∨ w ∈ B := fun w hw => by
      by_cases hwu : w = u
      · exact Or.inl hwu
      · by_cases hwv : w = v
        · exact Or.inr (Or.inl hwv)
        · exact Or.inr (Or.inr (Finset.mem_erase.mpr ⟨hwv, Finset.mem_erase.mpr ⟨hwu, hw⟩⟩))
    have hS1_empty : S1 = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      rintro ⟨x, y⟩ hxy
      simp only [S1, Gpairs, Finset.mem_filter, Finset.mem_univ, true_and] at hxy
      obtain ⟨_, hxNa, _, b, hbNa, c, hcNa, hbc, hxb, hxc, _, _⟩ := hxy
      have hnot_uv : ∀ s ∈ ({u, v} : Finset V), ∀ t ∈ ({u, v} : Finset V), ¬ F.Adj s t := by
        intro s hs t ht hst
        simp only [Finset.mem_insert, Finset.mem_singleton] at hs ht
        rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
        · exact hst.ne rfl
        · exact hnFuv hst
        · exact hnFuv hst.symm
        · exact hst.ne rfl
      have hpart2 : ∀ w ∈ Na, w ∈ ({u, v} : Finset V) ∨ w ∈ B := fun w hw => by
        rcases hNa_part w hw with rfl | rfl | hwB
        · exact Or.inl (by simp)
        · exact Or.inl (by simp)
        · exact Or.inr hwB
      rcases hpart2 x hxNa with hx1 | hx2 <;> rcases hpart2 b hbNa with hb1 | hb2 <;>
        rcases hpart2 c hcNa with hc1 | hc2
      · exact hnot_uv x hx1 b hb1 hxb
      · exact hnot_uv x hx1 b hb1 hxb
      · exact hnot_uv x hx1 c hc1 hxc
      · exact hB_ind b hb2 c hc2 hbc
      · exact hnot_uv b hb1 c hc1 hbc
      · exact hB_ind x hx2 c hc2 hxc
      · exact hB_ind x hx2 b hb2 hxb
      · exact hB_ind x hx2 b hb2 hxb
    have hS2a_sub : S2a ⊆ {(u, v), (v, u)} := by
      rintro ⟨x, y⟩ hxy
      simp only [S2a, Gpairs, Finset.mem_filter, Finset.mem_univ, true_and] at hxy
      obtain ⟨hGxy, _, _, hxNa, hyNa, hxy_all⟩ := hxy
      have hxy_ne : x ≠ y := hGxy.ne
      have hx_uv : x = u ∨ x = v := by
        rcases hNa_part x hxNa with rfl | rfl | hxB
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exfalso
          have hsub : (Na.erase x).erase y ⊆ ({u, v} : Finset V) := by
            intro w hw
            have hwNa : w ∈ Na := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hw)
            rcases hNa_part w hwNa with rfl | rfl | hwB
            · simp
            · simp
            · exact absurd (hxy_all w hw).1 (hB_ind x hxB w hwB)
          have hcard := Finset.card_le_card hsub
          have hy_er : y ∈ Na.erase x := Finset.mem_erase.mpr ⟨hxy_ne.symm, hyNa⟩
          rw [Finset.card_erase_of_mem hy_er, Finset.card_erase_of_mem hxNa, hNa5,
            Finset.card_pair huv_ne] at hcard
          omega
      have hy_uv : y = u ∨ y = v := by
        rcases hNa_part y hyNa with rfl | rfl | hyB
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exfalso
          have hsub : (Na.erase x).erase y ⊆ ({u, v} : Finset V) := by
            intro w hw
            have hwNa : w ∈ Na := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hw)
            rcases hNa_part w hwNa with rfl | rfl | hwB
            · simp
            · simp
            · exact absurd (hxy_all w hw).2 (hB_ind y hyB w hwB)
          have hcard := Finset.card_le_card hsub
          have hy_er : y ∈ Na.erase x := Finset.mem_erase.mpr ⟨hxy_ne.symm, hyNa⟩
          rw [Finset.card_erase_of_mem hy_er, Finset.card_erase_of_mem hxNa, hNa5,
            Finset.card_pair huv_ne] at hcard
          omega
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
      rcases hx_uv with rfl | rfl <;> rcases hy_uv with rfl | rfl
      · exact absurd rfl hxy_ne
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact absurd rfl hxy_ne
    have hc2 := Finset.card_le_card hS2a_sub
    have h2le : ({(u, v), (v, u)} : Finset (V × V)).card ≤ 2 := Finset.card_le_two
    rw [hS1_empty, Finset.card_empty]
    omega
  · rw [Finset.not_nonempty_iff_eq_empty] at h2a
    rw [h2a, Finset.card_empty]
    by_contra hbig
    have h7 : 7 ≤ S1.card := by omega
    obtain ⟨⟨u, v⟩, huv⟩ := Finset.card_pos.mp (by omega : 0 < S1.card)
    simp only [S1, Gpairs, Finset.mem_filter, Finset.mem_univ, true_and] at huv
    obtain ⟨hGuv, huNa, hvNa, b, hbNa, c, hcNa, hbc, hub, huc, hvb, hvc⟩ := huv
    have huv_ne : u ≠ v := hGuv.ne
    let Q : Finset V := {u, v, b, c}
    have hQsub : Q ⊆ Na := by
      intro t ht; simp only [Q, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl <;> assumption
    have hQ4 : Q.card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hbc.ne]
      · simp [hvb.ne, hvc.ne]
      · simp [huv_ne, hub.ne, huc.ne]
    have hQ_nonadj : ∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → ¬ F.Adj x y → (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
      intro x hx y hy hxy hnF
      simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl
      · exact absurd rfl hxy
      · exact Or.inl ⟨rfl, rfl⟩
      · exact absurd hub hnF
      · exact absurd huc hnF
      · exact Or.inr ⟨rfl, rfl⟩
      · exact absurd rfl hxy
      · exact absurd hvb hnF
      · exact absurd hvc hnF
      · exact absurd hub.symm hnF
      · exact absurd hvb.symm hnF
      · exact absurd rfl hxy
      · exact absurd hbc hnF
      · exact absurd huc.symm hnF
      · exact absurd hvc.symm hnF
      · exact absurd hbc.symm hnF
      · exact absurd rfl hxy
    have hcardQ_ge : 4 ≤ Na.card := hQ4 ▸ Finset.card_le_card hQsub
    by_cases hNa4 : Na.card = 4
    · have hNa_eq : Na = Q := (Finset.eq_of_subset_of_card_le hQsub (by omega)).symm
      have hS1_sub : S1 ⊆ {(u, v), (v, u)} := by
        rintro ⟨x, y⟩ hxy
        simp only [S1, Gpairs, Finset.mem_filter, Finset.mem_univ, true_and] at hxy
        have h1 := hQ_nonadj x (hNa_eq ▸ hxy.2.1) y (hNa_eq ▸ hxy.2.2.1) hxy.1.ne (fun h => h.2 hxy.1)
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]; exact h1
      have hc := Finset.card_le_card hS1_sub
      have h2le : ({(u, v), (v, u)} : Finset (V × V)).card ≤ 2 := Finset.card_le_two
      omega
    · have hNa5 : Na.card = 5 := by omega
      have hdiff1 : (Na \ Q).card = 1 := by rw [Finset.card_sdiff_of_subset hQsub, hNa5, hQ4]
      obtain ⟨w, hweq⟩ := Finset.card_eq_one.mp hdiff1
      have hw_mem : w ∈ Na \ Q := by rw [hweq]; simp
      have hwNa : w ∈ Na := (Finset.mem_sdiff.mp hw_mem).1
      have hwQ : w ∉ Q := (Finset.mem_sdiff.mp hw_mem).2
      have hNa_eq : Na = insert w Q := by
        ext t; constructor
        · intro ht; by_cases htQ : t ∈ Q
          · exact Finset.mem_insert_of_mem htQ
          · have : t ∈ Na \ Q := Finset.mem_sdiff.mpr ⟨ht, htQ⟩
            rw [hweq, Finset.mem_singleton] at this; exact Finset.mem_insert.mpr (Or.inl this)
        · intro ht; rw [Finset.mem_insert] at ht; rcases ht with rfl | htQ; exact hwNa; exact hQsub htQ
      -- Count ordered adjacent pairs in Na.offDiag: at least 10 inside Q plus 2 * |N_F(w) ∩ Q|!
      let adjNa := Na.offDiag.filter (fun p => F.Adj p.1 p.2)
      let adjQ := Q.offDiag.filter (fun p => F.Adj p.1 p.2)
      let adjW1 := (F.neighborFinset w ∩ Q).image (fun z => (w, z))
      let adjW2 := (F.neighborFinset w ∩ Q).image (fun z => (z, w))
      have hQadj_card : adjQ.card = 10 := by
        have hcomp : Q.offDiag \ adjQ = {(u, v), (v, u)} := by
          ext ⟨x, y⟩; simp only [adjQ, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_offDiag,
            Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
          constructor
          · rintro ⟨⟨hx, hy, hxy⟩, hnot⟩
            exact hQ_nonadj x hx y hy hxy (fun h => hnot ⟨⟨hx, hy, hxy⟩, h⟩)
          · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
            · exact ⟨⟨by simp [Q], by simp [Q], huv_ne⟩, fun h => h.2.2 hGuv⟩
            · exact ⟨⟨by simp [Q], by simp [Q], huv_ne.symm⟩, fun h => h.2.2 hGuv.symm⟩
        have hsub : adjQ ⊆ Q.offDiag := Finset.filter_subset _ _
        have h1 := Finset.card_sdiff_of_subset hsub
        rw [hcomp, Finset.card_pair (by intro h; exact huv_ne (Prod.mk.inj h).1),
          Finset.offDiag_card, hQ4] at h1
        omega
      have hdisj_QW1 : Disjoint adjQ adjW1 := by
        rw [Finset.disjoint_left]; rintro ⟨x, y⟩ h1 h2
        rw [Finset.mem_image] at h2; obtain ⟨z, _, he⟩ := h2
        have hxw : x = w := (Prod.mk.inj he).1.symm
        simp only [adjQ, Finset.mem_filter, Finset.mem_offDiag] at h1
        exact hwQ (hxw ▸ h1.1.1)
      have hdisj_QW2 : Disjoint adjQ adjW2 := by
        rw [Finset.disjoint_left]; rintro ⟨x, y⟩ h1 h2
        rw [Finset.mem_image] at h2; obtain ⟨z, _, he⟩ := h2
        have hyw : y = w := (Prod.mk.inj he).2.symm
        simp only [adjQ, Finset.mem_filter, Finset.mem_offDiag] at h1
        exact hwQ (hyw ▸ h1.1.2.1)
      have hdisj_W12 : Disjoint adjW1 adjW2 := by
        rw [Finset.disjoint_left]; rintro ⟨x, y⟩ h1 h2
        rw [Finset.mem_image] at h1 h2
        obtain ⟨z1, hz1, he1⟩ := h1; obtain ⟨z2, hz2, he2⟩ := h2
        have : z1 = w := ((Prod.mk.inj he1).2.trans (Prod.mk.inj he2).2.symm)
        exact hwQ (this ▸ (Finset.mem_inter.mp hz1).2)
      have hadj_sub : adjQ ∪ adjW1 ∪ adjW2 ⊆ adjNa := by
        rintro ⟨x, y⟩ hxy
        simp only [Finset.mem_union] at hxy
        simp only [adjNa, Finset.mem_filter, Finset.mem_offDiag]
        rcases hxy with (h | h) | h
        · simp only [adjQ, Finset.mem_filter, Finset.mem_offDiag] at h
          exact ⟨⟨hQsub h.1.1, hQsub h.1.2.1, h.1.2.2⟩, h.2⟩
        · rw [Finset.mem_image] at h; obtain ⟨z, hz, he⟩ := h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
          have hadj : F.Adj w z := (SimpleGraph.mem_neighborFinset F w z).mp (Finset.mem_inter.mp hz).1
          exact ⟨⟨hwNa, hQsub (Finset.mem_inter.mp hz).2, hadj.ne⟩, hadj⟩
        · rw [Finset.mem_image] at h; obtain ⟨z, hz, he⟩ := h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
          have hadj : F.Adj z w := ((SimpleGraph.mem_neighborFinset F w z).mp (Finset.mem_inter.mp hz).1).symm
          exact ⟨⟨hQsub (Finset.mem_inter.mp hz).2, hwNa, hadj.ne⟩, hadj⟩
      have hadjNa_ge : 10 + 2 * (F.neighborFinset w ∩ Q).card ≤ adjNa.card := by
        have hc := Finset.card_le_card hadj_sub
        rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hdisj_QW2, hdisj_W12⟩),
          Finset.card_union_of_disjoint hdisj_QW1, hQadj_card,
          Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2),
          Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)] at hc
        omega
      have hdisj_S1_adj : Disjoint S1 adjNa := by
        rw [Finset.disjoint_left]; rintro ⟨x, y⟩ h1 h2
        simp only [S1, Gpairs, Finset.mem_filter, Finset.mem_univ, true_and] at h1
        simp only [adjNa, Finset.mem_filter] at h2
        exact h2.2.2 h1.1
      have hS1_sub_off : S1 ⊆ Na.offDiag := by
        rintro ⟨x, y⟩ hxy
        simp only [S1, Gpairs, Finset.mem_filter, Finset.mem_univ, true_and] at hxy
        exact Finset.mem_offDiag.mpr ⟨hxy.2.1, hxy.2.2.1, hxy.1.ne⟩
      have hun_le : S1.card + adjNa.card ≤ 20 := by
        have hsub : S1 ∪ adjNa ⊆ Na.offDiag := Finset.union_subset hS1_sub_off (Finset.filter_subset _ _)
        have hc := Finset.card_le_card hsub
        rw [Finset.card_union_of_disjoint hdisj_S1_adj, Finset.offDiag_card, hNa5] at hc
        omega
      have hw_degQ : (F.neighborFinset w ∩ Q).card ≤ 1 := by omega
      -- Since |N_F(w) ∩ Q| ≤ 1, w has ≤ 1 neighbor in Na, so w never appears in S1!
      have hS1_sub_uv : S1 ⊆ {(u, v), (v, u)} := by
        rintro ⟨x, y⟩ hxy
        simp only [S1, Gpairs, Finset.mem_filter, Finset.mem_univ, true_and] at hxy
        obtain ⟨hGxy, hxNa, hyNa, b', hb'Na, c', hc'Na, hb'c', hxb', hxc', hyb', hyc'⟩ := hxy
        have hxw : x ≠ w := by
          intro h; subst h
          have hb'Q : b' ∈ Q := by
            rw [hNa_eq, Finset.mem_insert] at hb'Na; exact hb'Na.resolve_left hxb'.ne.symm
          have hc'Q : c' ∈ Q := by
            rw [hNa_eq, Finset.mem_insert] at hc'Na; exact hc'Na.resolve_left hxc'.ne.symm
          have hpair_sub : ({b', c'} : Finset V) ⊆ F.neighborFinset x ∩ Q := by
            intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
            rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
            rcases ht with rfl | rfl; exact ⟨hxb', hb'Q⟩; exact ⟨hxc', hc'Q⟩
          have hc := Finset.card_le_card hpair_sub
          rw [Finset.card_pair hb'c'.ne] at hc; omega
        have hyw : y ≠ w := by
          intro h; subst h
          have hb'Q : b' ∈ Q := by
            rw [hNa_eq, Finset.mem_insert] at hb'Na; exact hb'Na.resolve_left hyb'.ne.symm
          have hc'Q : c' ∈ Q := by
            rw [hNa_eq, Finset.mem_insert] at hc'Na; exact hc'Na.resolve_left hyc'.ne.symm
          have hpair_sub : ({b', c'} : Finset V) ⊆ F.neighborFinset y ∩ Q := by
            intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
            rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
            rcases ht with rfl | rfl; exact ⟨hyb', hb'Q⟩; exact ⟨hyc', hc'Q⟩
          have hc := Finset.card_le_card hpair_sub
          rw [Finset.card_pair hb'c'.ne] at hc; omega
        rw [hNa_eq, Finset.mem_insert] at hxNa hyNa
        have hxQ : x ∈ Q := hxNa.resolve_left hxw
        have hyQ : y ∈ Q := hyNa.resolve_left hyw
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
        exact hQ_nonadj x hxQ y hyQ hGxy.ne (fun h => h.2 hGxy)
      have hc := Finset.card_le_card hS1_sub_uv
      have h2le : ({(u, v), (v, u)} : Finset (V × V)).card ≤ 2 := Finset.card_le_two
      omega

/-- **Main Theorem for ν = 16**: Every minimally 4-extendable graph on 16 vertices has `δ(G) ≤ 9`. -/
theorem nu_eq_16_upper {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcard : Fintype.card V = 16) (hmin : IsMinimallyKExtendable G 4) :
    ∃ v : V, G.degree v ≤ 9 := by
  classical
  by_contra hall
  push Not at hall
  have h10 : ∀ v : V, 10 ≤ G.degree v := fun v => hall v
  let F := Gᶜ
  have hdegF : ∀ v : V, F.degree v ≤ 5 := fun v => by
    have h1 := degree_add_compl_degree G v
    rw [hcard] at h1
    have h2 := h10 v
    dsimp [F]
    omega
  have hgood : ¬ HasBad8 F := nu_eq_16_no_bad_eight hcard hmin h10
  have hnoK5 : ¬ HasClique F 5 := fun h => hgood (Or.inl h)
  have hnoK331 : ¬ HasCliqueJoin F 3 3 := fun h => hgood (Or.inr (Or.inl h))
  have hnoK35 : ¬ HasK F 3 5 := fun h => hgood (Or.inr (Or.inr h))
  let Gpairs : Finset (V × V) := Finset.univ.filter (fun p => G.Adj p.1 p.2)
  have hGpairs_ge : 160 ≤ Gpairs.card := by
    rw [card_adj_pairs]
    have hsum : ∑ _v : V, 10 ≤ ∑ v : V, G.degree v := Finset.sum_le_sum (fun v _ => h10 v)
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, hcard] at hsum
    omega
  -- Define the 6 obstruction classes of ordered edges of G
  let E1 := Gpairs.filter (fun p => ∃ a b c : V, F.Adj a b ∧ F.Adj b c ∧ F.Adj a c ∧
    F.Adj p.1 a ∧ F.Adj p.1 b ∧ F.Adj p.1 c ∧ F.Adj p.2 a ∧ F.Adj p.2 b ∧ F.Adj p.2 c)
  let E2a := Gpairs.filter (fun p => p ∉ E1 ∧ ∃ a : V, F.degree a = 5 ∧ F.Adj a p.1 ∧ F.Adj a p.2 ∧
    ∀ w ∈ ((F.neighborFinset a).erase p.1).erase p.2, F.Adj p.1 w ∧ F.Adj p.2 w)
  let E5 := Gpairs.filter (fun p => HasP5Dir F p.1 p.2 ∨ HasP5Dir F p.2 p.1)
  let E4 := Gpairs.filter (fun p => F.degree p.1 = 5 ∧ F.degree p.2 = 5 ∧
    F.neighborFinset p.1 = F.neighborFinset p.2)
  let E3 := Gpairs.filter (fun p => ∃ a₁ a₂ : V, a₁ ≠ a₂ ∧ F.degree a₁ = 5 ∧ F.degree a₂ = 5 ∧
    F.neighborFinset a₁ = F.neighborFinset a₂ ∧
    ((p.2 ∈ F.neighborFinset a₁ ∧ ∀ w ∈ (F.neighborFinset a₁).erase p.2, F.Adj p.1 w) ∨
     (p.1 ∈ F.neighborFinset a₁ ∧ ∀ w ∈ (F.neighborFinset a₁).erase p.1, F.Adj p.2 w)))
  let E2b := Gpairs.filter (fun p => ∃ a₁ a₂ : V, F.Adj a₁ a₂ ∧ F.degree a₁ = 5 ∧ F.degree a₂ = 5 ∧
    insert a₁ (F.neighborFinset a₁) = insert a₂ (F.neighborFinset a₂) ∧
    p.1 ∈ (F.neighborFinset a₁).erase a₂ ∧ p.2 ∈ (F.neighborFinset a₁).erase a₂ ∧
    ((∀ w ∈ (((F.neighborFinset a₁).erase a₂).erase p.1).erase p.2, F.Adj p.1 w) ∨
     (∀ w ∈ (((F.neighborFinset a₁).erase a₂).erase p.1).erase p.2, F.Adj p.2 w)))
  -- Every ordered edge of G falls into one of the 6 classes
  have hcover : Gpairs ⊆ E1 ∪ E2a ∪ E5 ∪ E4 ∪ E3 ∪ E2b := by
    rintro ⟨u, v⟩ huv
    have hGuv : G.Adj u v := (Finset.mem_filter.mp huv).2
    have hnotext : ¬ IsKExtendable (G.deleteEdges {s(u, v)}) 4 := hmin.2 s(u, v) hGuv
    have hexS : ∃ S : Finset V, S.card = 8 ∧ ¬ HasPM ((G.deleteEdges {s(u, v)}).induce (S : Set V)) := by
      by_contra hallPM
      push Not at hallPM
      exact hnotext (isKExtendable_of_forall_two_k_pm (by omega) hallPM)
    obtain ⟨S, hS8, hnoPM⟩ := hexS
    have hnoPM' : ¬ HasPM (((F ⊔ SimpleGraph.edge u v).induce (S : Set V))ᶜ) := by
      have heq : ((F ⊔ SimpleGraph.edge u v).induce (S : Set V))ᶜ =
          (G.deleteEdges {s(u, v)}).induce (S : Set V) := by
        dsimp only [F]
        rw [← compl_deleteEdges_singleton hGuv]
        ext ⟨a, _⟩ ⟨b, _⟩
        simp only [SimpleGraph.compl_adj, SimpleGraph.induce_adj]
        by_cases hne : a = b
        · subst hne; simp
        · simp [hne]
      rwa [heq]
    have hcases := obstructed_edge_eight_cases hdegF hgood hGuv.ne (fun h => h.2 hGuv) hS8 hnoPM'
    simp only [Finset.mem_union]
    rcases hcases with h1 | h2a | h2b | h3 | h4 | h5
    · left; left; left; left; left; exact Finset.mem_filter.mpr ⟨huv, h1⟩
    · by_cases hp1 : (u, v) ∈ E1
      · left; left; left; left; left; exact hp1
      · left; left; left; left; right; exact Finset.mem_filter.mpr ⟨huv, hp1, h2a⟩
    · right; exact Finset.mem_filter.mpr ⟨huv, h2b⟩
    · left; right; exact Finset.mem_filter.mpr ⟨huv, h3⟩
    · left; left; right; exact Finset.mem_filter.mpr ⟨huv, h4⟩
    · left; left; left; right; exact Finset.mem_filter.mpr ⟨huv, h5⟩
  -- Bound 1: E1.card + E2a.card ≤ 32
  have hB1 : E1.card + E2a.card ≤ 32 := by
    let S1 : V → Finset (V × V) := fun a =>
      Gpairs.filter (fun p => p.1 ∈ F.neighborFinset a ∧ p.2 ∈ F.neighborFinset a ∧
        ∃ b ∈ F.neighborFinset a, ∃ c ∈ F.neighborFinset a,
          F.Adj b c ∧ F.Adj p.1 b ∧ F.Adj p.1 c ∧ F.Adj p.2 b ∧ F.Adj p.2 c)
    let S2a : V → Finset (V × V) := fun a =>
      Gpairs.filter (fun p => p ∉ S1 a ∧ F.degree a = 5 ∧ p.1 ∈ F.neighborFinset a ∧ p.2 ∈ F.neighborFinset a ∧
        ∀ w ∈ ((F.neighborFinset a).erase p.1).erase p.2, F.Adj p.1 w ∧ F.Adj p.2 w)
    have hE1_cnt : 3 * E1.card ≤ ∑ a : V, (S1 a).card := by
      have hswap : ∑ a : V, (S1 a).card = ∑ p ∈ Gpairs, (Finset.univ.filter (fun a : V => p ∈ S1 a)).card := by
        simp_rw [Finset.card_eq_sum_ones]
        have h1 : ∀ a : V, ∑ _p ∈ S1 a, 1 = ∑ p ∈ Gpairs, if p ∈ S1 a then 1 else 0 := fun a => by
          rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (Finset.filter_subset _ _)]
        simp_rw [h1]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← Finset.sum_filter]
      rw [hswap]
      have hge : ∑ p ∈ E1, 3 ≤ ∑ p ∈ Gpairs, (Finset.univ.filter (fun a : V => p ∈ S1 a)).card := by
        calc ∑ p ∈ E1, 3
            ≤ ∑ p ∈ E1, (Finset.univ.filter (fun a : V => p ∈ S1 a)).card := by
              refine Finset.sum_le_sum fun p hp => ?_
              have hpG : p ∈ Gpairs := (Finset.mem_filter.mp hp).1
              obtain ⟨a, b, c, hab, hbc, hac, hpa, hpb, hpc, hqa, hqb, hqc⟩ := (Finset.mem_filter.mp hp).2
              have hsub : ({a, b, c} : Finset V) ⊆ Finset.univ.filter (fun x : V => p ∈ S1 x) := by
                intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, S1]
                rcases hx with hxa | hxb | hxc
                · rw [hxa]; exact ⟨hpG, (SimpleGraph.mem_neighborFinset F a p.1).mpr hpa.symm,
                    (SimpleGraph.mem_neighborFinset F a p.2).mpr hqa.symm,
                    b, (SimpleGraph.mem_neighborFinset F a b).mpr hab,
                    c, (SimpleGraph.mem_neighborFinset F a c).mpr hac, hbc, hpb, hpc, hqb, hqc⟩
                · rw [hxb]; exact ⟨hpG, (SimpleGraph.mem_neighborFinset F b p.1).mpr hpb.symm,
                    (SimpleGraph.mem_neighborFinset F b p.2).mpr hqb.symm,
                    a, (SimpleGraph.mem_neighborFinset F b a).mpr hab.symm,
                    c, (SimpleGraph.mem_neighborFinset F b c).mpr hbc, hac, hpa, hpc, hqa, hqc⟩
                · rw [hxc]; exact ⟨hpG, (SimpleGraph.mem_neighborFinset F c p.1).mpr hpc.symm,
                    (SimpleGraph.mem_neighborFinset F c p.2).mpr hqc.symm,
                    a, (SimpleGraph.mem_neighborFinset F c a).mpr hac.symm,
                    b, (SimpleGraph.mem_neighborFinset F c b).mpr hbc.symm, hab, hpa, hpb, hqa, hqb⟩
              have hc := Finset.card_le_card hsub
              rw [Finset.card_insert_of_notMem (by simp [hab.ne, hac.ne]), Finset.card_pair hbc.ne] at hc
              exact hc
          _ ≤ ∑ p ∈ Gpairs, (Finset.univ.filter (fun a : V => p ∈ S1 a)).card :=
              Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      simp only [Finset.sum_const, smul_eq_mul] at hge
      omega
    have hE2a_cnt : E2a.card ≤ ∑ a : V, (S2a a).card := by
      have hswap : ∑ a : V, (S2a a).card = ∑ p ∈ Gpairs, (Finset.univ.filter (fun a : V => p ∈ S2a a)).card := by
        simp_rw [Finset.card_eq_sum_ones]
        have h1 : ∀ a : V, ∑ _p ∈ S2a a, 1 = ∑ p ∈ Gpairs, if p ∈ S2a a then 1 else 0 := fun a => by
          rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (Finset.filter_subset _ _)]
        simp_rw [h1]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← Finset.sum_filter]
      rw [hswap]
      have hge : ∑ p ∈ E2a, 1 ≤ ∑ p ∈ Gpairs, (Finset.univ.filter (fun a : V => p ∈ S2a a)).card := by
        calc ∑ p ∈ E2a, 1
            ≤ ∑ p ∈ E2a, (Finset.univ.filter (fun a : V => p ∈ S2a a)).card := by
              refine Finset.sum_le_sum fun p hp => ?_
              have hpG : p ∈ Gpairs := (Finset.mem_filter.mp hp).1
              obtain ⟨hnotE1, a, hda5, hap1, hap2, hallw⟩ := (Finset.mem_filter.mp hp).2
              have hpS2a : p ∈ S2a a := by
                refine Finset.mem_filter.mpr ⟨hpG, ?_, hda5,
                  (SimpleGraph.mem_neighborFinset F a p.1).mpr hap1,
                  (SimpleGraph.mem_neighborFinset F a p.2).mpr hap2, hallw⟩
                intro hpS1
                obtain ⟨_, _, b, hbNa, c, hcNa, hbc, hpb, hpc, hqb, hqc⟩ := (Finset.mem_filter.mp hpS1).2
                exact hnotE1 (Finset.mem_filter.mpr ⟨hpG, a, b, c,
                  (SimpleGraph.mem_neighborFinset F a b).mp hbNa, hbc,
                  (SimpleGraph.mem_neighborFinset F a c).mp hcNa,
                  hap1.symm, hpb, hpc, hap2.symm, hqb, hqc⟩)
              exact Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, hpS2a⟩⟩
          _ ≤ ∑ p ∈ Gpairs, (Finset.univ.filter (fun a : V => p ∈ S2a a)).card :=
              Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      simp only [Finset.sum_const, smul_eq_mul, mul_one] at hge
      exact hge
    have hsum6 : ∑ a : V, ((S1 a).card + 3 * (S2a a).card) ≤ 96 := by
      calc ∑ a : V, ((S1 a).card + 3 * (S2a a).card)
          ≤ ∑ _a : V, 6 := Finset.sum_le_sum fun a _ => local_12a_bound a (hdegF a)
        _ = 96 := by simp [hcard]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum6
    omega
  -- Bound 2: E5.card ≤ 32
  have hB2 : E5.card ≤ 32 := by
    let E5dir := Finset.univ.filter (fun p : V × V => HasP5Dir F p.1 p.2)
    have hdir_le : E5dir.card ≤ 16 := by
      have hinj : Set.InjOn Prod.fst (E5dir : Set (V × V)) := by
        rintro ⟨x₁, y₁⟩ h1 ⟨x₂, y₂⟩ h2 hfst
        simp only [E5dir, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        dsimp only at hfst; subst hfst
        exact Prod.ext rfl (p5_unique_target hdegF hgood h1 h2)
      have hc := Finset.card_image_of_injOn hinj
      have hle : (E5dir.image Prod.fst).card ≤ Fintype.card V := Finset.card_le_univ _
      rw [hc, hcard] at hle; exact hle
    have hsub : E5 ⊆ E5dir ∪ E5dir.image Prod.swap := by
      rintro ⟨u, v⟩ huv
      simp only [E5, Finset.mem_filter] at huv
      rw [Finset.mem_union]
      rcases huv.2 with h1 | h2
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
      · exact Or.inr (Finset.mem_image.mpr ⟨(v, u), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩, rfl⟩)
    have hc := Finset.card_le_card hsub
    have hun := Finset.card_union_le E5dir (E5dir.image Prod.swap)
    have him := Finset.card_image_le (f := Prod.swap) (s := E5dir)
    omega
  -- Bound 3: E4.card + E3.card + E2b.card ≤ 64
  let O := Finset.univ.filter (fun a : V => F.degree a = 5 ∧
    ∃ a' : V, a' ≠ a ∧ F.degree a' = 5 ∧ F.neighborFinset a = F.neighborFinset a')
  let C := Finset.univ.filter (fun a : V => F.degree a = 5 ∧
    ∃ a' : V, F.Adj a a' ∧ F.degree a' = 5 ∧ insert a (F.neighborFinset a) = insert a' (F.neighborFinset a'))
  have hdisjOC : Disjoint O C := by
    rw [Finset.disjoint_left]; intro a haO haC
    obtain ⟨_, a₁, ha1a, _, hNa1⟩ := (Finset.mem_filter.mp haO).2
    obtain ⟨_, a₂, haa2, _, hNa2⟩ := (Finset.mem_filter.mp haC).2
    have ha2Na1 : a₂ ∈ F.neighborFinset a₁ := hNa1 ▸ (SimpleGraph.mem_neighborFinset F a a₂).mpr haa2
    have ha1Na2 : a₁ ∈ F.neighborFinset a₂ :=
      (SimpleGraph.mem_neighborFinset F a₂ a₁).mpr ((SimpleGraph.mem_neighborFinset F a₁ a₂).mp ha2Na1).symm
    have ha1_ins : a₁ ∈ insert a (F.neighborFinset a) := hNa2 ▸ Finset.mem_insert_of_mem ha1Na2
    have ha1_Na : a₁ ∈ F.neighborFinset a := (Finset.mem_insert.mp ha1_ins).resolve_left ha1a
    rw [hNa1] at ha1_Na
    exact ((SimpleGraph.mem_neighborFinset F a₁ a₁).mp ha1_Na).ne rfl
  have hOC_le : O.card + C.card ≤ 16 := by
    rw [← Finset.card_union_of_disjoint hdisjOC, ← hcard]
    exact Finset.card_le_univ _
  have hO_uniq : ∀ a a₁ a₂ : V, F.degree a = 5 → F.neighborFinset a = F.neighborFinset a₁ →
      F.neighborFinset a = F.neighborFinset a₂ → a₁ ≠ a → a₂ ≠ a → a₁ = a₂ := by
    intro a a₁ a₂ hda h1 h2 ha1a ha2a
    by_contra h12
    let A : Finset V := {a, a₁, a₂}
    have hA3 : A.card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [ha1a.symm, ha2a.symm]), Finset.card_pair h12]
    have hdisj : Disjoint A (F.neighborFinset a) := by
      rw [Finset.disjoint_left]; intro x hx hxN
      simp only [A, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ((SimpleGraph.mem_neighborFinset F x x).mp hxN).ne rfl
      · rw [h1] at hxN; exact ((SimpleGraph.mem_neighborFinset F x x).mp hxN).ne rfl
      · rw [h2] at hxN; exact ((SimpleGraph.mem_neighborFinset F x x).mp hxN).ne rfl
    refine hnoK35 ⟨A, F.neighborFinset a, hA3, by rwa [SimpleGraph.card_neighborFinset_eq_degree], hdisj, ?_⟩
    intro x hx y hy
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact (SimpleGraph.mem_neighborFinset F x y).mp hy
    · exact (SimpleGraph.mem_neighborFinset F x y).mp (h1 ▸ hy)
    · exact (SimpleGraph.mem_neighborFinset F x y).mp (h2 ▸ hy)
  have hC_uniq : ∀ a a₁ a₂ : V, F.degree a = 5 → F.Adj a a₁ → F.Adj a a₂ →
      insert a (F.neighborFinset a) = insert a₁ (F.neighborFinset a₁) →
      insert a (F.neighborFinset a) = insert a₂ (F.neighborFinset a₂) → a₁ = a₂ := by
    intro a a₁ a₂ hda ha1 ha2 h1 h2
    by_contra h12
    have ha12 : F.Adj a₁ a₂ := by
      have hm : a₂ ∈ insert a₁ (F.neighborFinset a₁) :=
        h1 ▸ Finset.mem_insert_of_mem ((SimpleGraph.mem_neighborFinset F a a₂).mpr ha2)
      exact (SimpleGraph.mem_neighborFinset F a₁ a₂).mp ((Finset.mem_insert.mp hm).resolve_left (Ne.symm h12))
    let A : Finset V := {a, a₁, a₂}
    let B : Finset V := ((F.neighborFinset a).erase a₁).erase a₂
    have hA3 : A.card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [ha1.ne, ha2.ne]), Finset.card_pair h12]
    have ha1Na : a₁ ∈ F.neighborFinset a := (SimpleGraph.mem_neighborFinset F a a₁).mpr ha1
    have ha2_er : a₂ ∈ (F.neighborFinset a).erase a₁ :=
      Finset.mem_erase.mpr ⟨Ne.symm h12, (SimpleGraph.mem_neighborFinset F a a₂).mpr ha2⟩
    have hB3 : B.card = 3 := by
      rw [Finset.card_erase_of_mem ha2_er, Finset.card_erase_of_mem ha1Na,
        SimpleGraph.card_neighborFinset_eq_degree, hda]
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]; intro x hx hxB
      simp only [B, Finset.mem_erase] at hxB
      simp only [A, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ((SimpleGraph.mem_neighborFinset F x x).mp hxB.2.2).ne rfl
      · exact hxB.2.1 rfl
      · exact hxB.1 rfl
    refine hnoK331 ⟨A, B, hA3, hB3, hdisj, ?_, ?_⟩
    · intro x hx y hy hxy
      simp only [A, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      · exact absurd rfl hxy
      · exact ha1
      · exact ha2
      · exact ha1.symm
      · exact absurd rfl hxy
      · exact ha12
      · exact ha2.symm
      · exact ha12.symm
      · exact absurd rfl hxy
    · intro x hx y hy
      simp only [B, Finset.mem_erase] at hy
      simp only [A, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact (SimpleGraph.mem_neighborFinset F x y).mp hy.2.2
      · have : y ∈ insert x (F.neighborFinset x) := h1 ▸ Finset.mem_insert_of_mem hy.2.2
        exact (SimpleGraph.mem_neighborFinset F x y).mp ((Finset.mem_insert.mp this).resolve_left hy.2.1)
      · have : y ∈ insert x (F.neighborFinset x) := h2 ▸ Finset.mem_insert_of_mem hy.2.2
        exact (SimpleGraph.mem_neighborFinset F x y).mp ((Finset.mem_insert.mp this).resolve_left hy.1)
  have hE4_le : E4.card ≤ O.card := by
    have him : E4.image Prod.fst ⊆ O := by
      intro x hx; rw [Finset.mem_image] at hx; obtain ⟨⟨u, v⟩, huv, rfl⟩ := hx
      simp only [E4, Gpairs, Finset.mem_filter, Finset.mem_univ, true_and] at huv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, huv.2.1, v, huv.1.ne.symm, huv.2.2.1, huv.2.2.2⟩
    have hinj : Set.InjOn Prod.fst (E4 : Set (V × V)) := by
      rintro ⟨u₁, v₁⟩ h1 ⟨u₂, v₂⟩ h2 hfst
      simp only [E4, Gpairs, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      dsimp only at hfst; subst hfst
      exact Prod.ext rfl (hO_uniq u₁ v₁ v₂ h1.2.1 h1.2.2.2 h2.2.2.2 h1.1.ne.symm h2.1.ne.symm)
    rw [← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card him
  have hE3_le : E3.card ≤ 3 * O.card := by
    let E3dir := Gpairs.filter (fun p => ∃ a₁ a₂ : V, a₁ ≠ a₂ ∧ F.degree a₁ = 5 ∧ F.degree a₂ = 5 ∧
      F.neighborFinset a₁ = F.neighborFinset a₂ ∧
      p.2 ∈ F.neighborFinset a₁ ∧ ∀ w ∈ (F.neighborFinset a₁).erase p.2, F.Adj p.1 w)
    have hE3_sub : E3 ⊆ E3dir ∪ E3dir.image Prod.swap := by
      rintro ⟨u, v⟩ huv
      simp only [E3, Finset.mem_filter] at huv
      obtain ⟨huvG, a₁, a₂, h12, hd1, hd2, hN12, hdir | hdir⟩ := huv
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨huvG, a₁, a₂, h12, hd1, hd2, hN12, hdir⟩)
      · have hvuG : (v, u) ∈ Gpairs := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp huvG).2.symm⟩
        exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨(v, u), Finset.mem_filter.mpr ⟨hvuG, a₁, a₂, h12, hd1, hd2, hN12, hdir⟩, rfl⟩)
    let T3 : V → Finset (V × V) := fun a =>
      E3dir.filter (fun p => p.2 ∈ F.neighborFinset a ∧ ∀ w ∈ (F.neighborFinset a).erase p.2, F.Adj p.1 w)
    have hT3_le : ∀ a ∈ O, (T3 a).card ≤ 3 := by
      intro a haO
      obtain ⟨hda, a', ha'a, _, hNa'⟩ := (Finset.mem_filter.mp haO).2
      let B := F.neighborFinset a
      let U := (T3 a).image Prod.fst
      have hinj : Set.InjOn Prod.fst (T3 a : Set (V × V)) := by
        rintro ⟨u₁, v₁⟩ h1 ⟨u₂, v₂⟩ h2 hfst
        simp only [T3, E3dir, Gpairs, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        dsimp only at hfst; subst hfst
        refine Prod.ext rfl ?_
        by_contra hv12
        have hv2_er : v₂ ∈ (F.neighborFinset a).erase v₁ := Finset.mem_erase.mpr ⟨Ne.symm hv12, h2.2.1⟩
        exact (h1.2.2 v₂ hv2_er).2 h2.1.1
      have hcardU : (T3 a).card = U.card := (Finset.card_image_of_injOn hinj).symm
      have haU : a ∉ U := by
        intro h; rw [Finset.mem_image] at h; obtain ⟨⟨u, v⟩, huv, hu⟩ := h; dsimp only at hu; subst hu
        simp only [T3, E3dir, Gpairs, Finset.mem_filter, Finset.mem_univ, true_and] at huv
        exact ((SimpleGraph.mem_neighborFinset F u v).mp huv.2.1).2 huv.1.1
      have ha'U : a' ∉ U := by
        intro h; rw [Finset.mem_image] at h; obtain ⟨⟨u, v⟩, huv, hu⟩ := h; dsimp only at hu; subst hu
        simp only [T3, E3dir, Gpairs, Finset.mem_filter, Finset.mem_univ, true_and] at huv
        exact ((SimpleGraph.mem_neighborFinset F u v).mp (hNa' ▸ huv.2.1)).2 huv.1.1
      have h4U : 4 * U.card ≤ ∑ u ∈ U, (F.neighborFinset u ∩ B).card := by
        have h1 : ∑ _u ∈ U, 4 ≤ ∑ u ∈ U, (F.neighborFinset u ∩ B).card := by
          refine Finset.sum_le_sum fun u hu => ?_
          rw [Finset.mem_image] at hu; obtain ⟨⟨u', v⟩, huv, hu'⟩ := hu; dsimp only at hu'; rw [hu'] at huv
          simp only [T3, Finset.mem_filter] at huv
          have hsub : B.erase v ⊆ F.neighborFinset u ∩ B := fun w hw =>
            Finset.mem_inter.mpr ⟨(SimpleGraph.mem_neighborFinset F u w).mpr (huv.2.2 w hw),
              Finset.mem_of_mem_erase hw⟩
          have hc := Finset.card_le_card hsub
          rw [Finset.card_erase_of_mem huv.2.1, SimpleGraph.card_neighborFinset_eq_degree, hda] at hc
          exact hc
        simp only [Finset.sum_const, smul_eq_mul] at h1; omega
      have hswap : ∑ u ∈ U, (F.neighborFinset u ∩ B).card = ∑ b ∈ B, (F.neighborFinset b ∩ U).card := by
        simp_rw [Finset.card_eq_sum_ones]
        have h1 : ∀ u ∈ U, ∑ _b ∈ F.neighborFinset u ∩ B, 1 = ∑ b ∈ B, if F.Adj u b then 1 else 0 := fun u _ => by
          rw [← Finset.sum_filter]
          congr 1; ext b; simp [SimpleGraph.mem_neighborFinset, and_comm]
        have h2 : ∀ b ∈ B, ∑ _u ∈ F.neighborFinset b ∩ U, 1 = ∑ u ∈ U, if F.Adj u b then 1 else 0 := fun b _ => by
          rw [← Finset.sum_filter]
          congr 1; ext u; simp [SimpleGraph.mem_neighborFinset, adj_comm, and_comm]
        rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.sum_congr rfl fun b hb => (h2 b hb).symm]
      have hB_le : ∑ b ∈ B, (F.neighborFinset b ∩ U).card ≤ 15 := by
        calc ∑ b ∈ B, (F.neighborFinset b ∩ U).card
            ≤ ∑ _b ∈ B, 3 := by
              refine Finset.sum_le_sum fun b hb => ?_
              have hdisj : Disjoint ({a, a'} : Finset V) (F.neighborFinset b ∩ U) := by
                rw [Finset.disjoint_left]; intro t ht hmem
                simp only [Finset.mem_insert, Finset.mem_singleton] at ht
                rcases ht with rfl | rfl
                · exact haU (Finset.mem_inter.mp hmem).2
                · exact ha'U (Finset.mem_inter.mp hmem).2
              have hsub : {a, a'} ∪ (F.neighborFinset b ∩ U) ⊆ F.neighborFinset b := by
                intro t ht; rw [Finset.mem_union] at ht
                rcases ht with h | h
                · simp only [Finset.mem_insert, Finset.mem_singleton] at h
                  rcases h with hta | hta'
                  · rw [hta]; exact (SimpleGraph.mem_neighborFinset F b a).mpr ((SimpleGraph.mem_neighborFinset F a b).mp hb).symm
                  · rw [hta']; exact (SimpleGraph.mem_neighborFinset F b a').mpr ((SimpleGraph.mem_neighborFinset F a' b).mp (hNa' ▸ hb)).symm
                · exact (Finset.mem_inter.mp h).1
              have hc := Finset.card_le_card hsub
              rw [Finset.card_union_of_disjoint hdisj, Finset.card_pair ha'a.symm,
                SimpleGraph.card_neighborFinset_eq_degree] at hc
              have := hdegF b; omega
          _ = 15 := by simp [B, SimpleGraph.card_neighborFinset_eq_degree, hda]
      omega
    have h2E3dir : 2 * E3dir.card ≤ ∑ a ∈ O, (T3 a).card := by
      have hswap : ∑ a ∈ O, (T3 a).card = ∑ p ∈ E3dir, (O.filter (fun a => p ∈ T3 a)).card := by
        simp_rw [Finset.card_eq_sum_ones]
        have h1 : ∀ a ∈ O, ∑ _p ∈ T3 a, 1 = ∑ p ∈ E3dir, if p ∈ T3 a then 1 else 0 := fun a _ => by
          rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (Finset.filter_subset _ _)]
        rw [Finset.sum_congr rfl h1, Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← Finset.sum_filter]
      rw [hswap]
      have hge : ∑ _p ∈ E3dir, 2 ≤ ∑ p ∈ E3dir, (O.filter (fun a => p ∈ T3 a)).card := by
        refine Finset.sum_le_sum fun p hp => ?_
        obtain ⟨a₁, a₂, h12, hd1, hd2, hN12, hp2, hallw⟩ := (Finset.mem_filter.mp hp).2
        have ha1O : a₁ ∈ O := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd1, a₂, h12.symm, hd2, hN12⟩
        have ha2O : a₂ ∈ O := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd2, a₁, h12, hd1, hN12.symm⟩
        have hsub : ({a₁, a₂} : Finset V) ⊆ O.filter (fun a => p ∈ T3 a) := by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rw [Finset.mem_filter]
          rcases hx with rfl | rfl
          · exact ⟨ha1O, Finset.mem_filter.mpr ⟨hp, hp2, hallw⟩⟩
          · exact ⟨ha2O, Finset.mem_filter.mpr ⟨hp, hN12 ▸ hp2, hN12 ▸ hallw⟩⟩
        have hc := Finset.card_le_card hsub
        rw [Finset.card_pair h12] at hc; exact hc
      simp only [Finset.sum_const, smul_eq_mul] at hge; omega
    have hsumO : ∑ a ∈ O, (T3 a).card ≤ 3 * O.card := by
      calc ∑ a ∈ O, (T3 a).card
          ≤ ∑ _a ∈ O, 3 := Finset.sum_le_sum hT3_le
        _ = 3 * O.card := by simp [mul_comm]
    have hE3_card := Finset.card_le_card hE3_sub
    have hun := Finset.card_union_le E3dir (E3dir.image Prod.swap)
    have him := Finset.card_image_le (f := Prod.swap) (s := E3dir)
    omega
  have hE2b_le : E2b.card ≤ 2 * C.card := by
    let T2b : V → Finset (V × V) := fun a =>
      E2b.filter (fun p => ∃ a' : V, F.Adj a a' ∧ F.degree a' = 5 ∧
        insert a (F.neighborFinset a) = insert a' (F.neighborFinset a') ∧
        p.1 ∈ (F.neighborFinset a).erase a' ∧ p.2 ∈ (F.neighborFinset a).erase a' ∧
        ((∀ w ∈ (((F.neighborFinset a).erase a').erase p.1).erase p.2, F.Adj p.1 w) ∨
         (∀ w ∈ (((F.neighborFinset a).erase a').erase p.1).erase p.2, F.Adj p.2 w)))
    have hT2b_le : ∀ a ∈ C, (T2b a).card ≤ 4 := by
      intro a haC
      obtain ⟨hda, a', haa', hda', hclosed⟩ := (Finset.mem_filter.mp haC).2
      let R := (F.neighborFinset a).erase a'
      have hR4 : R.card = 4 := by
        rw [Finset.card_erase_of_mem ((SimpleGraph.mem_neighborFinset F a a').mpr haa'),
          SimpleGraph.card_neighborFinset_eq_degree, hda]
      have hR_adj_a : ∀ z ∈ R, F.Adj a z := fun z hz =>
        (SimpleGraph.mem_neighborFinset F a z).mp (Finset.mem_of_mem_erase hz)
      have hR_adj_a' : ∀ z ∈ R, F.Adj a' z := fun z hz => by
        have hm : z ∈ insert a' (F.neighborFinset a') := hclosed ▸ Finset.mem_insert_of_mem (Finset.mem_of_mem_erase hz)
        exact (SimpleGraph.mem_neighborFinset F a' z).mp ((Finset.mem_insert.mp hm).resolve_left (Finset.mem_erase.mp hz).1)
      have hR_tri_free : ∀ x ∈ R, ∀ y ∈ R, ∀ z ∈ R, F.Adj x y → F.Adj y z → ¬ F.Adj x z := by
        intro x hx y hy z hz hxy hyz hxz
        let K : Finset V := {a, a', x, y, z}
        have ha_not : a ∉ ({a', x, y, z} : Finset V) := by
          simp [haa'.ne, (hR_adj_a x hx).ne, (hR_adj_a y hy).ne, (hR_adj_a z hz).ne]
        have ha'_not : a' ∉ ({x, y, z} : Finset V) := by
          simp [(hR_adj_a' x hx).ne, (hR_adj_a' y hy).ne, (hR_adj_a' z hz).ne]
        have hK5 : K.card = 5 := by
          rw [Finset.card_insert_of_notMem ha_not, Finset.card_insert_of_notMem ha'_not,
            Finset.card_insert_of_notMem (by simp [hxy.ne, hxz.ne]), Finset.card_pair hyz.ne]
        refine hnoK5 ⟨K, hK5, fun p hp q hq hpq => ?_⟩
        simp only [K, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hp hq
        rcases hp with rfl | rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl | rfl
        · exact absurd rfl hpq
        · exact haa'
        · exact hR_adj_a _ hx
        · exact hR_adj_a _ hy
        · exact hR_adj_a _ hz
        · exact haa'.symm
        · exact absurd rfl hpq
        · exact hR_adj_a' _ hx
        · exact hR_adj_a' _ hy
        · exact hR_adj_a' _ hz
        · exact (hR_adj_a _ hx).symm
        · exact (hR_adj_a' _ hx).symm
        · exact absurd rfl hpq
        · exact hxy
        · exact hxz
        · exact (hR_adj_a _ hy).symm
        · exact (hR_adj_a' _ hy).symm
        · exact hxy.symm
        · exact absurd rfl hpq
        · exact hyz
        · exact (hR_adj_a _ hz).symm
        · exact (hR_adj_a' _ hz).symm
        · exact hxz.symm
        · exact hyz.symm
        · exact absurd rfl hpq
      by_cases hne : (T2b a).Nonempty
      · obtain ⟨⟨u₀, v₀⟩, huv0⟩ := hne
        have hmem_R : ∀ p ∈ T2b a, p.1 ∈ R ∧ p.2 ∈ R ∧ p.1 ≠ p.2 ∧ ¬ F.Adj p.1 p.2 ∧
            ((∀ w ∈ (R.erase p.1).erase p.2, F.Adj p.1 w) ∨
             (∀ w ∈ (R.erase p.1).erase p.2, F.Adj p.2 w)) := by
          intro p hp
          obtain ⟨hpE, a'', haa'', _, hcl'', hp1, hp2, hall⟩ := Finset.mem_filter.mp hp
          have ha_eq : a'' = a' := hC_uniq a a'' a' hda haa'' haa' hcl'' hclosed
          subst ha_eq
          have hGp : G.Adj p.1 p.2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hpE).1).2
          exact ⟨hp1, hp2, hGp.ne, fun h => h.2 hGp, hall⟩
        obtain ⟨hu0R, hv0R, huv0_ne, hnFuv0, hdir0⟩ := hmem_R (u₀, v₀) huv0
        -- Pick u, v with u adjacent to both vertices x, y of (R.erase u).erase v
        have hex_uv : ∃ u v : V, u ∈ R ∧ v ∈ R ∧ u ≠ v ∧ ¬ F.Adj u v ∧
            ∀ w ∈ (R.erase u).erase v, F.Adj u w := by
          rcases hdir0 with h1 | h2
          · exact ⟨u₀, v₀, hu0R, hv0R, huv0_ne, hnFuv0, h1⟩
          · refine ⟨v₀, u₀, hv0R, hu0R, huv0_ne.symm, fun h => hnFuv0 h.symm, fun w hw => h2 w ?_⟩
            rwa [Finset.erase_right_comm]
        obtain ⟨u, v, huR, hvR, huv_ne, hnFuv, hu_all⟩ := hex_uv
        have h2card : ((R.erase u).erase v).card = 2 := by
          rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨huv_ne.symm, hvR⟩),
            Finset.card_erase_of_mem huR, hR4]
        obtain ⟨x, y, hxy_ne, hxy_eq⟩ := Finset.card_eq_two.mp h2card
        have hx_er : x ∈ (R.erase u).erase v := by rw [hxy_eq]; simp
        have hy_er : y ∈ (R.erase u).erase v := by rw [hxy_eq]; simp
        have hxR : x ∈ R := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx_er)
        have hyR : y ∈ R := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy_er)
        have hux : F.Adj u x := hu_all x hx_er
        have huy : F.Adj u y := hu_all y hy_er
        have hnFxy : ¬ F.Adj x y := fun hxy => hR_tri_free u huR x hxR y hyR hux hxy huy
        have hR_eq : R = {u, v, x, y} := by
          ext t; constructor
          · intro ht; simp only [Finset.mem_insert, Finset.mem_singleton]
            by_cases htu : t = u; · exact Or.inl htu
            by_cases htv : t = v; · exact Or.inr (Or.inl htv)
            have : t ∈ (R.erase u).erase v := Finset.mem_erase.mpr ⟨htv, Finset.mem_erase.mpr ⟨htu, ht⟩⟩
            rw [hxy_eq, Finset.mem_insert, Finset.mem_singleton] at this
            tauto
          · intro ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
            rcases ht with rfl | rfl | rfl | rfl <;> assumption
        have hsub4 : T2b a ⊆ {(u, v), (v, u), (x, y), (y, x)} := by
          rintro ⟨p, q⟩ hpq
          obtain ⟨hpR, hqR, hpq_ne, hnFpq, hdir⟩ := hmem_R (p, q) hpq
          dsimp only at hpR hqR hpq_ne hnFpq hdir
          have hxv : x ≠ v := (Finset.mem_erase.mp hx_er).1
          have hyv : y ≠ v := (Finset.mem_erase.mp hy_er).1
          have hxu : x ≠ u := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx_er)).1
          have hyu : y ≠ u := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hy_er)).1
          rw [hR_eq, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hpR hqR
          simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
          rcases hpR with rfl | rfl | rfl | rfl <;> rcases hqR with rfl | rfl | rfl | rfl
          · exact absurd rfl hpq_ne
          · exact Or.inl ⟨rfl, rfl⟩
          · exact absurd hux hnFpq
          · exact absurd huy hnFpq
          · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
          · exact absurd rfl hpq_ne
          · -- (v, x): neither v nor x can be adjacent to both u and y!
            exfalso
            rcases hdir with hv_all | hx_all
            · exact hnFuv (hv_all u (Finset.mem_erase.mpr ⟨hxu.symm, Finset.mem_erase.mpr ⟨huv_ne, huR⟩⟩)).symm
            · exact hnFxy (hx_all y (Finset.mem_erase.mpr ⟨hxy_ne.symm, Finset.mem_erase.mpr ⟨hyv, hyR⟩⟩))
          · -- (v, y): neither v nor y can be adjacent to both u and x!
            exfalso
            rcases hdir with hv_all | hy_all
            · exact hnFuv (hv_all u (Finset.mem_erase.mpr ⟨hyu.symm, Finset.mem_erase.mpr ⟨huv_ne, huR⟩⟩)).symm
            · exact hnFxy (hy_all x (Finset.mem_erase.mpr ⟨hxy_ne, Finset.mem_erase.mpr ⟨hxv, hxR⟩⟩)).symm
          · exact absurd hux.symm hnFpq
          · -- (x, v)
            exfalso
            rcases hdir with hx_all | hv_all
            · exact hnFxy (hx_all y (Finset.mem_erase.mpr ⟨hyv, Finset.mem_erase.mpr ⟨hxy_ne.symm, hyR⟩⟩))
            · exact hnFuv (hv_all u (Finset.mem_erase.mpr ⟨huv_ne, Finset.mem_erase.mpr ⟨hxu.symm, huR⟩⟩)).symm
          · exact absurd rfl hpq_ne
          · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
          · exact absurd huy.symm hnFpq
          · -- (y, v)
            exfalso
            rcases hdir with hy_all | hv_all
            · exact hnFxy (hy_all x (Finset.mem_erase.mpr ⟨hxv, Finset.mem_erase.mpr ⟨hxy_ne, hxR⟩⟩)).symm
            · exact hnFuv (hv_all u (Finset.mem_erase.mpr ⟨huv_ne, Finset.mem_erase.mpr ⟨hyu.symm, huR⟩⟩)).symm
          · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
          · exact absurd rfl hpq_ne
        have hc := Finset.card_le_card hsub4
        have h4 : ({(u, v), (v, u), (x, y), (y, x)} : Finset (V × V)).card ≤ 4 :=
          le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _)
            (Nat.succ_le_succ Finset.card_le_two)))
        omega
      · rw [Finset.not_nonempty_iff_eq_empty] at hne; rw [hne, Finset.card_empty]; omega
    have h2E2b : 2 * E2b.card ≤ ∑ a ∈ C, (T2b a).card := by
      have hswap : ∑ a ∈ C, (T2b a).card = ∑ p ∈ E2b, (C.filter (fun a => p ∈ T2b a)).card := by
        simp_rw [Finset.card_eq_sum_ones]
        have h1 : ∀ a ∈ C, ∑ _p ∈ T2b a, 1 = ∑ p ∈ E2b, if p ∈ T2b a then 1 else 0 := fun a _ => by
          rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (Finset.filter_subset _ _)]
        rw [Finset.sum_congr rfl h1, Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← Finset.sum_filter]
      rw [hswap]
      have hge : ∑ _p ∈ E2b, 2 ≤ ∑ p ∈ E2b, (C.filter (fun a => p ∈ T2b a)).card := by
        refine Finset.sum_le_sum fun p hp => ?_
        obtain ⟨a₁, a₂, ha12, hd1, hd2, hcl, hp1, hp2, hall⟩ := (Finset.mem_filter.mp hp).2
        have ha1C : a₁ ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd1, a₂, ha12, hd2, hcl⟩
        have ha2C : a₂ ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd2, a₁, ha12.symm, hd1, hcl.symm⟩
        have herase_eq : (F.neighborFinset a₁).erase a₂ = (F.neighborFinset a₂).erase a₁ := by
          ext t; simp only [Finset.mem_erase]
          constructor
          · rintro ⟨ht2, ht1⟩
            have ht_ne1 : t ≠ a₁ := ((SimpleGraph.mem_neighborFinset F a₁ t).mp ht1).ne.symm
            have : t ∈ insert a₂ (F.neighborFinset a₂) := hcl ▸ Finset.mem_insert_of_mem ht1
            exact ⟨ht_ne1, (Finset.mem_insert.mp this).resolve_left ht2⟩
          · rintro ⟨ht1, ht2⟩
            have ht_ne2 : t ≠ a₂ := ((SimpleGraph.mem_neighborFinset F a₂ t).mp ht2).ne.symm
            have : t ∈ insert a₁ (F.neighborFinset a₁) := hcl.symm ▸ Finset.mem_insert_of_mem ht2
            exact ⟨ht_ne2, (Finset.mem_insert.mp this).resolve_left ht1⟩
        have hsub : ({a₁, a₂} : Finset V) ⊆ C.filter (fun a => p ∈ T2b a) := by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rw [Finset.mem_filter]
          rcases hx with rfl | rfl
          · exact ⟨ha1C, Finset.mem_filter.mpr ⟨hp, a₂, ha12, hd2, hcl, hp1, hp2, hall⟩⟩
          · exact ⟨ha2C, Finset.mem_filter.mpr ⟨hp, a₁, ha12.symm, hd1, hcl.symm,
              herase_eq ▸ hp1, herase_eq ▸ hp2, herase_eq ▸ hall⟩⟩
        have hc := Finset.card_le_card hsub
        rw [Finset.card_pair ha12.ne] at hc; exact hc
      simp only [Finset.sum_const, smul_eq_mul] at hge; omega
    have hsumC : ∑ a ∈ C, (T2b a).card ≤ 4 * C.card := by
      calc ∑ a ∈ C, (T2b a).card
          ≤ ∑ _a ∈ C, 4 := Finset.sum_le_sum hT2b_le
        _ = 4 * C.card := by simp [mul_comm]
    omega
  -- Final contradiction: 160 ≤ 32 + 32 + 64 = 128!
  have hcov_card := Finset.card_le_card hcover
  have hu1 := Finset.card_union_le (E1 ∪ E2a ∪ E5 ∪ E4 ∪ E3) E2b
  have hu2 := Finset.card_union_le (E1 ∪ E2a ∪ E5 ∪ E4) E3
  have hu3 := Finset.card_union_le (E1 ∪ E2a ∪ E5) E4
  have hu4 := Finset.card_union_le (E1 ∪ E2a) E5
  have hu5 := Finset.card_union_le E1 E2a
  omega

end Order16Count

end LouYuK4
