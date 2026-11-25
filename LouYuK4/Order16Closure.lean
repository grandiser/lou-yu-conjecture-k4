import LouYuK4.SmallOrders

/-!
# Order ν = 16, Part A: 10-Vertex Hitting Lemma and Closure Elimination

We prove:
- `exists_good_eight_of_ten`: Every 10-vertex graph `H` with `Δ(H) ≤ 5` contains an 8-vertex
  induced subgraph with no `K₅`, no `K₃ ∨ 3K₁`, and no `K₃,₅`.
- `exists_good_eight_of_eleven`: Corollary for 11-vertex graphs with `Δ(H) ≤ 5`.
- `nu_eq_16_no_bad_eight`: If `G` is minimally 4-extendable on 16 vertices with `δ(G) ≥ 10`
  (so `Δ(Gᶜ) ≤ 5`), then `Gᶜ` has NO `K₅`, NO `K₃ ∨ 3K₁`, and NO `K₃,₅` (hence every 8-set
  of `G` has a perfect matching).
-/

open SimpleGraph Finset

namespace LouYuK4

section Bad8Helpers

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The three minimal 8-vertex obstructions with `Δ ≤ 5`: `K₅`, `K₃ ∨ 3K₁`, or `K₃,₅`. -/
def HasBad8 (F : SimpleGraph V) : Prop :=
  HasClique F 5 ∨ HasCliqueJoin F 3 3 ∨ HasK F 3 5

omit [Fintype V] in
/-- On an 8-set `S`, if `Gᶜ` contains `K₃ ∨ 3K₁` inside `S`, then `G.induce S` has no PM. -/
lemma not_hasPM_eight_of_hasCliqueJoin33 {G : SimpleGraph V} {S A B : Finset V}
    (hS : S.card = 8) (hAS : A ⊆ S) (hBS : B ⊆ S)
    (hA3 : A.card = 3) (hB3 : B.card = 3) (hdisj : Disjoint A B)
    (hcl : Gᶜ.IsClique (A : Set V)) (hadj : ∀ u ∈ A, ∀ v ∈ B, Gᶜ.Adj u v) :
    ¬ HasPM (G.induce (S : Set V)) := by
  classical
  rintro ⟨P, hPM, hPspan⟩
  choose f hf using fun a : A => hPM (hPspan ⟨a.val, hAS a.property⟩)
  -- Every vertex of A must be matched into S \ (A ∪ B), which has size 8 - 6 = 2 < 3!
  have hfmem : ∀ a : A, (f a).val ∈ S \ (A ∪ B) := by
    intro a
    rw [Finset.mem_sdiff, Finset.mem_union]
    refine ⟨(f a).property, ?_⟩
    rintro (ha' | hb')
    · have hGadj : G.Adj a.val (f a).val := (hf a).1.adj_sub
      exact (hcl a.property ha' hGadj.ne).2 hGadj
    · have hGadj : G.Adj a.val (f a).val := (hf a).1.adj_sub
      exact (hadj a.val a.property (f a).val hb').2 hGadj
  have hfinj : Function.Injective (fun a : A => (f a).val) := by
    intro a₁ a₂ heq
    have hf_eq : f a₁ = f a₂ := Subtype.ext heq
    have h1 := (hf a₁).1
    have h2 := (hf a₂).1
    rw [hf_eq] at h1
    have hsub := hPM.eq_of_adj_right h1 h2
    exact Subtype.ext (congrArg (fun x : (S : Set V) => x.val) hsub)
  have hle : A.card ≤ (S \ (A ∪ B)).card := by
    have hsub : Finset.univ.image (fun a : A => (f a).val) ⊆ S \ (A ∪ B) := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨a, _, rfl⟩ := hx
      exact hfmem a
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_coe] at hc
    exact hc
  have hABsub : A ∪ B ⊆ S := Finset.union_subset hAS hBS
  rw [Finset.card_sdiff_of_subset hABsub, Finset.card_union_of_disjoint hdisj, hS, hA3, hB3] at hle
  omega

omit [Fintype V] [DecidableEq V] in
/-- Lifting `HasClique`, `HasCliqueJoin`, `HasK`, and `HasBad8` from `F.induce S` to `F`. -/
lemma hasClique_of_induce {F : SimpleGraph V} {S : Finset V} {r : ℕ}
    (h : HasClique (F.induce (S : Set V)) r) : HasClique F r := by
  classical
  obtain ⟨Q, hQr, hcl⟩ := h
  refine ⟨Q.image Subtype.val, by rw [Finset.card_image_of_injective _ Subtype.val_injective, hQr], ?_⟩
  intro x hx y hy hxy
  rw [Finset.mem_coe, Finset.mem_image] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx; obtain ⟨b, hb, rfl⟩ := hy
  exact hcl ha hb (fun he => hxy (congrArg Subtype.val he))

omit [Fintype V] [DecidableEq V] in
lemma hasCliqueJoin_of_induce {F : SimpleGraph V} {S : Finset V} {a b : ℕ}
    (h : HasCliqueJoin (F.induce (S : Set V)) a b) : HasCliqueJoin F a b := by
  classical
  obtain ⟨A, B, hA, hB, hdisj, hcl, hadj⟩ := h
  refine ⟨A.image Subtype.val, B.image Subtype.val,
    by rw [Finset.card_image_of_injective _ Subtype.val_injective, hA],
    by rw [Finset.card_image_of_injective _ Subtype.val_injective, hB], ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]; intro x hx hy
    rw [Finset.mem_image] at hx hy
    obtain ⟨p, hp, rfl⟩ := hx; obtain ⟨q, hq, hv⟩ := hy
    exact Finset.disjoint_left.mp hdisj hp ((Subtype.ext hv) ▸ hq)
  · intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_image] at hx hy
    obtain ⟨p, hp, rfl⟩ := hx; obtain ⟨q, hq, rfl⟩ := hy
    exact hcl hp hq (fun he => hxy (congrArg Subtype.val he))
  · intro x hx y hy
    rw [Finset.mem_image] at hx hy
    obtain ⟨p, hp, rfl⟩ := hx; obtain ⟨q, hq, rfl⟩ := hy
    exact hadj p hp q hq

omit [Fintype V] [DecidableEq V] in
lemma hasK_of_induce {F : SimpleGraph V} {S : Finset V} {a b : ℕ}
    (h : HasK (F.induce (S : Set V)) a b) : HasK F a b := by
  classical
  obtain ⟨A, B, hA, hB, hdisj, hadj⟩ := h
  refine ⟨A.image Subtype.val, B.image Subtype.val,
    by rw [Finset.card_image_of_injective _ Subtype.val_injective, hA],
    by rw [Finset.card_image_of_injective _ Subtype.val_injective, hB], ?_, ?_⟩
  · rw [Finset.disjoint_left]; intro x hx hy
    rw [Finset.mem_image] at hx hy
    obtain ⟨p, hp, rfl⟩ := hx; obtain ⟨q, hq, hv⟩ := hy
    exact Finset.disjoint_left.mp hdisj hp ((Subtype.ext hv) ▸ hq)
  · intro x hx y hy
    rw [Finset.mem_image] at hx hy
    obtain ⟨p, hp, rfl⟩ := hx; obtain ⟨q, hq, rfl⟩ := hy
    exact hadj p hp q hq

omit [Fintype V] [DecidableEq V] in
lemma hasBad8_of_induce {F : SimpleGraph V} {S : Finset V}
    (h : HasBad8 (F.induce (S : Set V))) : HasBad8 F := by
  rcases h with h1 | h2 | h3
  · exact Or.inl (hasClique_of_induce h1)
  · exact Or.inr (Or.inl (hasCliqueJoin_of_induce h2))
  · exact Or.inr (Or.inr (hasK_of_induce h3))

lemma hasBad8_map_equiv {W₁ W₂ : Type*} [DecidableEq W₁] [DecidableEq W₂]
    {G₁ : SimpleGraph W₁} {G₂ : SimpleGraph W₂} (e : W₁ ≃ W₂)
    (hadj_iff : ∀ u v, G₁.Adj u v → G₂.Adj (e u) (e v))
    (h : HasBad8 G₁) : HasBad8 G₂ := by
  have hdisj_map : ∀ {s t : Finset W₁}, Disjoint s t →
      Disjoint (s.map e.toEmbedding) (t.map e.toEmbedding) := by
    intro s t hd
    rw [Finset.disjoint_left]; intro x hx hy
    rw [Finset.mem_map] at hx hy
    obtain ⟨u, hu, rfl⟩ := hx; obtain ⟨v, hv, he⟩ := hy
    exact Finset.disjoint_left.mp hd hu (e.injective he ▸ hv)
  rcases h with ⟨K, hK5, hcl⟩ | ⟨A, B, hA3, hB3, hdisj, hcl, hadj⟩ | ⟨A, B, hA3, hB5, hdisj, hadj⟩
  · refine Or.inl ⟨K.map e.toEmbedding, by rw [Finset.card_map, hK5], fun x hx y hy hxy => ?_⟩
    rw [Finset.mem_coe, Finset.mem_map] at hx hy
    obtain ⟨u, hu, rfl⟩ := hx; obtain ⟨v, hv, rfl⟩ := hy
    exact hadj_iff u v (hcl hu hv (fun he => hxy (congrArg e he)))
  · refine Or.inr (Or.inl ⟨A.map e.toEmbedding, B.map e.toEmbedding,
      by rw [Finset.card_map, hA3], by rw [Finset.card_map, hB3], hdisj_map hdisj,
      fun x hx y hy hxy => ?_, fun x hx y hy => ?_⟩)
    · rw [Finset.mem_coe, Finset.mem_map] at hx hy
      obtain ⟨u, hu, rfl⟩ := hx; obtain ⟨v, hv, rfl⟩ := hy
      exact hadj_iff u v (hcl hu hv (fun he => hxy (congrArg e he)))
    · rw [Finset.mem_map] at hx hy
      obtain ⟨u, hu, rfl⟩ := hx; obtain ⟨v, hv, rfl⟩ := hy
      exact hadj_iff u v (hadj u hu v hv)
  · refine Or.inr (Or.inr ⟨A.map e.toEmbedding, B.map e.toEmbedding,
      by rw [Finset.card_map, hA3], by rw [Finset.card_map, hB5], hdisj_map hdisj,
      fun x hx y hy => ?_⟩)
    rw [Finset.mem_map] at hx hy
    obtain ⟨u, hu, rfl⟩ := hx; obtain ⟨v, hv, rfl⟩ := hy
    exact hadj_iff u v (hadj u hu v hv)

/-- On an 8-set `S`, if `F = Gᶜ` satisfies `HasBad8 (F.induce S)`, then `G.induce S` has no PM. -/
lemma not_hasPM_eight_of_hasBad8 {G : SimpleGraph V} {S : Finset V} (hS : S.card = 8)
    (hbad : HasBad8 (Gᶜ.induce (S : Set V))) : ¬ HasPM (G.induce (S : Set V)) := by
  classical
  rcases hbad with ⟨Q, hQ5, hcl⟩ | ⟨A, B, hA3, hB3, hdisj, hcl, hadj⟩ | ⟨A, B, hA3, hB5, hdisj, hadj⟩
  · let QV := Q.image Subtype.val
    have hQVsub : QV ⊆ S := fun x hx => by
      rw [Finset.mem_image] at hx; obtain ⟨a, _, rfl⟩ := hx; exact a.property
    have hQV5 : QV.card = 5 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hQ5]
    refine not_hasPM_of_compl_clique hQVsub (by omega) ?_
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_image] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx; obtain ⟨b, hb, rfl⟩ := hy
    exact hcl ha hb (fun he => hxy (congrArg Subtype.val he))
  · let AV := A.image Subtype.val
    let BV := B.image Subtype.val
    have hAVsub : AV ⊆ S := fun x hx => by
      rw [Finset.mem_image] at hx; obtain ⟨a, _, rfl⟩ := hx; exact a.property
    have hBVsub : BV ⊆ S := fun x hx => by
      rw [Finset.mem_image] at hx; obtain ⟨b, _, rfl⟩ := hx; exact b.property
    have hAV3 : AV.card = 3 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hA3]
    have hBV3 : BV.card = 3 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hB3]
    have hdisjV : Disjoint AV BV := by
      rw [Finset.disjoint_left]; intro x hx hy
      rw [Finset.mem_image] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx; obtain ⟨b, hb, hv⟩ := hy
      exact Finset.disjoint_left.mp hdisj ha ((Subtype.ext hv) ▸ hb)
    refine not_hasPM_eight_of_hasCliqueJoin33 hS hAVsub hBVsub hAV3 hBV3 hdisjV ?_ ?_
    · intro x hx y hy hxy
      rw [Finset.mem_coe, Finset.mem_image] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx; obtain ⟨b, hb, rfl⟩ := hy
      exact hcl ha hb (fun he => hxy (congrArg Subtype.val he))
    · intro x hx y hy
      rw [Finset.mem_image] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx; obtain ⟨b, hb, rfl⟩ := hy
      exact hadj a ha b hb
  · let AV := A.image Subtype.val
    let BV := B.image Subtype.val
    have hAVsub : AV ⊆ S := fun x hx => by
      rw [Finset.mem_image] at hx; obtain ⟨a, _, rfl⟩ := hx; exact a.property
    have hBVsub : BV ⊆ S := fun x hx => by
      rw [Finset.mem_image] at hx; obtain ⟨b, _, rfl⟩ := hx; exact b.property
    have hAV3 : AV.card = 3 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hA3]
    have hBV5 : BV.card = 5 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hB5]
    have hdisjV : Disjoint AV BV := by
      rw [Finset.disjoint_left]; intro x hx hy
      rw [Finset.mem_image] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx; obtain ⟨b, hb, hv⟩ := hy
      exact Finset.disjoint_left.mp hdisj ha ((Subtype.ext hv) ▸ hb)
    have hSeq : S = AV ∪ BV := by
      refine (Finset.eq_of_subset_of_card_le (Finset.union_subset hAVsub hBVsub) ?_).symm
      rw [Finset.card_union_of_disjoint hdisjV, hAV3, hBV5, hS]
    refine not_hasPM_of_compl_bip hSeq (by rw [hAV3]; exact ⟨1, rfl⟩) ?_
    intro x hx y hy
    rw [Finset.mem_image] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx; obtain ⟨b, hb, rfl⟩ := hy
    exact hadj a ha b hb

/-- On an 8-set `S` with `Δ(Gᶜ) ≤ 5`, `¬ HasPM (G.induce S) ↔ HasBad8 (Gᶜ.induce S)`. -/
lemma not_hasPM_eight_iff_hasBad8 {G : SimpleGraph V} [DecidableRel Gᶜ.Adj]
    (hdeg : ∀ v : V, Gᶜ.degree v ≤ 5) {S : Finset V} (hS : S.card = 8) :
    ¬ HasPM (G.induce (S : Set V)) ↔ HasBad8 (Gᶜ.induce (S : Set V)) := by
  classical
  constructor
  · intro hno
    rw [hasPM_induce_iff_compl] at hno
    exact not_hasPM_eight_of_compl_le_five (X := Gᶜ.induce (S : Set V))
      (by rw [card_coe_finset_set, hS])
      (fun w => le_trans (degree_induce_le Gᶜ S w) (hdeg w.val)) hno
  · exact not_hasPM_eight_of_hasBad8 hS

omit [DecidableEq V] in
/-- Useful helper: if `u` has degree `≤ 5` in `H` and is adjacent to every vertex of a 5-set `T`,
then `H.neighborFinset u = T` (so `u` has no neighbors outside `T`). -/
lemma neighborFinset_eq_of_subset_card_five {H : SimpleGraph V} [DecidableRel H.Adj]
    {u : V} {T : Finset V} (hdeg : H.degree u ≤ 5) (hT5 : T.card = 5)
    (hadj : ∀ w ∈ T, H.Adj u w) : H.neighborFinset u = T := by
  have hsub : T ⊆ H.neighborFinset u := fun w hw => by
    rw [SimpleGraph.mem_neighborFinset]; exact hadj w hw
  have hle : (H.neighborFinset u).card ≤ T.card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hT5]; exact hdeg
  exact (Finset.eq_of_subset_of_card_le hsub hle).symm

/-- If `H` has `HasCliqueJoin H 3 3` or `HasK H 3 5` on `S`, then `S` contains 3 vertices of
degree `≥ 5` in `H.induce S`. -/
lemma exists_three_deg_five_of_k3join_or_k35 {H : SimpleGraph V} [DecidableRel H.Adj]
    (h : HasCliqueJoin H 3 3 ∨ HasK H 3 5) :
    ∃ A : Finset V, A.card = 3 ∧ ∀ a ∈ A, 5 ≤ H.degree a := by
  rcases h with ⟨A, B, hA3, hB3, hdisj, hcl, hadj⟩ | ⟨A, B, hA3, hB5, hdisj, hadj⟩
  · refine ⟨A, hA3, fun a ha => ?_⟩
    have hsub : A.erase a ∪ B ⊆ H.neighborFinset a := by
      intro w hw
      rw [Finset.mem_union, Finset.mem_erase] at hw
      rw [SimpleGraph.mem_neighborFinset]
      rcases hw with ⟨hne, hwA⟩ | hwB
      · exact hcl ha hwA hne.symm
      · exact hadj a ha w hwB
    have hdisj' : Disjoint (A.erase a) B := Finset.disjoint_of_subset_left (Finset.erase_subset a A) hdisj
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj', Finset.card_erase_of_mem ha, hA3, hB3,
      SimpleGraph.card_neighborFinset_eq_degree] at hc
    exact hc
  · refine ⟨A, hA3, fun a ha => ?_⟩
    have hsub : B ⊆ H.neighborFinset a := fun w hw => by
      rw [SimpleGraph.mem_neighborFinset]; exact hadj a ha w hw
    have hc := Finset.card_le_card hsub
    rw [hB5, SimpleGraph.card_neighborFinset_eq_degree] at hc
    exact hc

end Bad8Helpers

section HittingTenAndEleven

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Lemma A (10-vertex hitting lemma)**: Every 10-vertex graph `H` with `Δ(H) ≤ 5` has
an 8-vertex induced subgraph with no `K₅`, no `K₃ ∨ 3K₁`, and no `K₃,₅`. -/
theorem exists_good_eight_of_ten {H : SimpleGraph V} [DecidableRel H.Adj]
    (hV : Fintype.card V = 10) (hdeg : ∀ v : V, H.degree v ≤ 5) :
    ∃ S : Finset V, S.card = 8 ∧ ¬ HasBad8 (H.induce (S : Set V)) := by
  classical
  -- Case 1: H contains a K₅ on Q (|Q| = 5).
  by_cases hK5 : HasClique H 5
  · obtain ⟨Q, hQ5, hQcl⟩ := hK5
    let R : Finset V := Qᶜ
    have hR5 : R.card = 5 := by rw [Finset.card_compl, hV, hQ5]
    -- Subcase 1a: Some vertex z ∈ R is adjacent to all 5 vertices of Q (so Q ∪ {z} is a K₆ component!).
    by_cases hK6 : ∃ z ∈ R, ∀ q ∈ Q, H.Adj z q
    · obtain ⟨z, hzR, hzQ⟩ := hK6
      -- Delete z and one vertex x ∈ Q; remaining 8 vertices are Q' (size 4) ⊔ R' (size 4) with NO edges between Q' and R'!
      obtain ⟨x, hxQ⟩ := Finset.card_pos.mp (by omega : 0 < Q.card)
      let S : Finset V := (Finset.univ.erase z).erase x
      have hxz : x ≠ z := fun h => by subst h; exact (Finset.mem_compl.mp hzR) hxQ
      have hx_er : x ∈ (Finset.univ : Finset V).erase z := Finset.mem_erase.mpr ⟨hxz, Finset.mem_univ x⟩
      have hS8 : S.card = 8 := by
        rw [Finset.card_erase_of_mem hx_er, Finset.card_erase_of_mem (Finset.mem_univ z),
          Finset.card_univ, hV]
      refine ⟨S, hS8, fun hbad => ?_⟩
      -- Every vertex q ∈ Q \ {x} has ALL 5 neighbors in insert z (Q \ {q}), hence NO neighbors in R \ {z}!
      -- Thus in H.induce S, Q' = Q.erase x (size 4) has NO edges to R' = R.erase z (size 4)!
      -- Hence every vertex of H.induce S has degree ≤ 3, contradicting HasBad8 (which needs degree ≥ 4)!
      have hdegS : ∀ w : (S : Set V), (H.induce (S : Set V)).degree w ≤ 3 := by
        intro ⟨w, hwS⟩
        have hwz : w ≠ z := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hwS)).1
        have hwx : w ≠ x := (Finset.mem_erase.mp hwS).1
        by_cases hwQ : w ∈ Q
        · -- N_H(w) = insert z (Q.erase w), so N_{H[S]}(w) ⊆ Q \ {w, x} (size 3)!
          have hNw : H.neighborFinset w = insert z (Q.erase w) := by
            refine neighborFinset_eq_of_subset_card_five (hdeg w) ?_ ?_
            · have hzQ' : z ∉ Q.erase w := fun h => (Finset.mem_compl.mp hzR) (Finset.mem_of_mem_erase h)
              rw [Finset.card_insert_of_notMem hzQ', Finset.card_erase_of_mem hwQ, hQ5]
            · intro u hu
              rw [Finset.mem_insert, Finset.mem_erase] at hu
              rcases hu with rfl | ⟨huw, huQ⟩
              · exact (hzQ w hwQ).symm
              · exact hQcl hwQ huQ huw.symm
          have hsub : ((H.induce (S : Set V)).neighborFinset ⟨w, hwS⟩).image Subtype.val ⊆ (Q.erase w).erase x := by
            intro u hu
            rw [Finset.mem_image] at hu
            obtain ⟨⟨u, huS⟩, huN, rfl⟩ := hu
            rw [SimpleGraph.mem_neighborFinset] at huN
            have huNw : u ∈ H.neighborFinset w := (SimpleGraph.mem_neighborFinset H w u).mpr huN
            rw [hNw, Finset.mem_insert] at huNw
            have huz : u ≠ z := (Finset.mem_erase.mp (Finset.mem_of_mem_erase huS)).1
            have hux : u ≠ x := (Finset.mem_erase.mp huS).1
            exact Finset.mem_erase.mpr ⟨hux, huNw.resolve_left huz⟩
          have hc := Finset.card_le_card hsub
          rw [Finset.card_image_of_injective _ Subtype.val_injective,
            SimpleGraph.card_neighborFinset_eq_degree] at hc
          have hxQw : x ∈ Q.erase w := Finset.mem_erase.mpr ⟨hwx.symm, hxQ⟩
          rw [Finset.card_erase_of_mem hxQw, Finset.card_erase_of_mem hwQ, hQ5] at hc
          exact hc
        · -- w ∈ R \ {z}; w has NO neighbors in Q (since every q ∈ Q has N_H(q) = insert z (Q.erase q)!)
          have hwR : w ∈ R := Finset.mem_compl.mpr hwQ
          have hsub : ((H.induce (S : Set V)).neighborFinset ⟨w, hwS⟩).image Subtype.val ⊆ (R.erase z).erase w := by
            intro u hu
            rw [Finset.mem_image] at hu
            obtain ⟨⟨u, huS⟩, huN, rfl⟩ := hu
            rw [SimpleGraph.mem_neighborFinset] at huN
            have huw : u ≠ w := (SimpleGraph.ne_of_adj H huN).symm
            have huz : u ≠ z := (Finset.mem_erase.mp (Finset.mem_of_mem_erase huS)).1
            have huR : u ∈ R := by
              rw [Finset.mem_compl]
              intro huQ
              have hNu : H.neighborFinset u = insert z (Q.erase u) := by
                refine neighborFinset_eq_of_subset_card_five (hdeg u) ?_ ?_
                · have hzQ' : z ∉ Q.erase u := fun h => (Finset.mem_compl.mp hzR) (Finset.mem_of_mem_erase h)
                  rw [Finset.card_insert_of_notMem hzQ', Finset.card_erase_of_mem huQ, hQ5]
                · intro t ht
                  rw [Finset.mem_insert, Finset.mem_erase] at ht
                  rcases ht with rfl | ⟨htu, htQ⟩
                  · exact (hzQ u huQ).symm
                  · exact hQcl huQ htQ htu.symm
              have hwNu : w ∈ H.neighborFinset u := (SimpleGraph.mem_neighborFinset H u w).mpr huN.symm
              rw [hNu, Finset.mem_insert, Finset.mem_erase] at hwNu
              rcases hwNu with rfl | ⟨_, hwQ'⟩
              · exact hwz rfl
              · exact hwQ hwQ'
            exact Finset.mem_erase.mpr ⟨huw, Finset.mem_erase.mpr ⟨huz, huR⟩⟩
          have hc := Finset.card_le_card hsub
          rw [Finset.card_image_of_injective _ Subtype.val_injective,
            SimpleGraph.card_neighborFinset_eq_degree] at hc
          have hwRz : w ∈ R.erase z := Finset.mem_erase.mpr ⟨hwz, hwR⟩
          rw [Finset.card_erase_of_mem hwRz, Finset.card_erase_of_mem hzR, hR5] at hc
          exact hc
      -- Contradiction: any HasBad8 has a vertex of degree ≥ 4!
      rcases hbad with ⟨K, hK5', hKcl⟩ | h23
      · obtain ⟨w, hwK⟩ := Finset.card_pos.mp (by omega : 0 < K.card)
        have hsub : K.erase w ⊆ (H.induce (S : Set V)).neighborFinset w := fun u hu => by
          rw [Finset.mem_erase] at hu
          rw [SimpleGraph.mem_neighborFinset]
          exact hKcl hwK hu.2 hu.1.symm
        have hc := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hwK, hK5', SimpleGraph.card_neighborFinset_eq_degree] at hc
        have := hdegS w; omega
      · obtain ⟨A, hA3, hA5⟩ := exists_three_deg_five_of_k3join_or_k35 h23
        obtain ⟨w, hwA⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
        have := hA5 w hwA; have := hdegS w; omega
    · -- Subcase 1b: No vertex z ∈ R is adjacent to all 5 vertices of Q.
      -- Each q ∈ Q has 4 neighbors in Q, hence at most 1 neighbor in R!
      -- Thus ∑_{r ∈ R} |N_H(r) ∩ Q| = ∑_{q ∈ Q} |N_H(q) ∩ R| ≤ 5.
      -- Pick x ∈ Q arbitrarily, and pick y ∈ R maximizing |N_H(y) ∩ Q|!
      push Not at hK6
      have hqR : ∀ q ∈ Q, (H.neighborFinset q ∩ R).card ≤ 1 := by
        intro q hq
        have hdisj : Disjoint (Q.erase q) (H.neighborFinset q ∩ R) := by
          rw [Finset.disjoint_left]; intro u hu1 hu2
          exact (Finset.mem_compl.mp (Finset.mem_inter.mp hu2).2) (Finset.mem_of_mem_erase hu1)
        have hsub : Q.erase q ∪ (H.neighborFinset q ∩ R) ⊆ H.neighborFinset q := by
          intro u hu; rw [Finset.mem_union] at hu
          rcases hu with hu1 | hu2
          · rw [Finset.mem_erase] at hu1
            rw [SimpleGraph.mem_neighborFinset]
            exact hQcl hq hu1.2 hu1.1.symm
          · exact (Finset.mem_inter.mp hu2).1
        have hc := Finset.card_le_card hsub
        rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem hq, hQ5,
          SimpleGraph.card_neighborFinset_eq_degree] at hc
        have := hdeg q; omega
      -- Double count edges between Q and R: ∑ r ∈ R, (N(r) ∩ Q).card ≤ 5!
      have hQRsum : ∑ r ∈ R, (H.neighborFinset r ∩ Q).card ≤ 5 := by
        have hswap : ∑ r ∈ R, (H.neighborFinset r ∩ Q).card = ∑ q ∈ Q, (H.neighborFinset q ∩ R).card := by
          simp_rw [Finset.card_eq_sum_ones]
          have h1 : ∀ r ∈ R, ∑ _x ∈ H.neighborFinset r ∩ Q, 1 = ∑ q ∈ Q, if H.Adj r q then 1 else 0 := by
            intro r _
            rw [← Finset.sum_filter]
            refine Finset.sum_congr ?_ fun _ _ => rfl
            ext q; simp [Finset.mem_inter, SimpleGraph.mem_neighborFinset, and_comm]
          have h2 : ∀ q ∈ Q, ∑ _x ∈ H.neighborFinset q ∩ R, 1 = ∑ r ∈ R, if H.Adj r q then 1 else 0 := by
            intro q _
            rw [← Finset.sum_filter]
            refine Finset.sum_congr ?_ fun _ _ => rfl
            ext r; simp [Finset.mem_inter, SimpleGraph.mem_neighborFinset, SimpleGraph.adj_comm, and_comm]
          rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_comm]
        rw [hswap]
        calc ∑ q ∈ Q, (H.neighborFinset q ∩ R).card ≤ ∑ _q ∈ Q, 1 := Finset.sum_le_sum hqR
          _ = 5 := by rw [Finset.sum_const, hQ5]; rfl
      obtain ⟨x, hxQ⟩ := Finset.card_pos.mp (by omega : 0 < Q.card)
      obtain ⟨y, hyR, hyMax⟩ := Finset.exists_max_image R (fun r => (H.neighborFinset r ∩ Q).card)
        (Finset.card_pos.mp (by omega : 0 < R.card))
      let Q' : Finset V := Q.erase x
      let R' : Finset V := R.erase y
      have hQ'4 : Q'.card = 4 := by rw [Finset.card_erase_of_mem hxQ, hQ5]
      have hR'4 : R'.card = 4 := by rw [Finset.card_erase_of_mem hyR, hR5]
      have hdisjQ'R' : Disjoint Q' R' :=
        Disjoint.mono (Finset.erase_subset x Q) (Finset.erase_subset y R) disjoint_compl_right
      let S : Finset V := Q' ∪ R'
      have hS8 : S.card = 8 := by rw [Finset.card_union_of_disjoint hdisjQ'R', hQ'4, hR'4]
      refine ⟨S, hS8, fun hbad => ?_⟩
      -- Bound edges from Q' to R': each q ∈ Q' has ≤ 1 neighbor in R', so total ≤ 4!
      have hQ'deg : ∀ q ∈ Q', (H.neighborFinset q ∩ S).card ≤ 4 := by
        intro q hq
        have hqQ : q ∈ Q := Finset.mem_of_mem_erase hq
        have hsub : H.neighborFinset q ∩ S ⊆ Q'.erase q ∪ (H.neighborFinset q ∩ R) := by
          intro u hu
          rw [Finset.mem_inter, Finset.mem_union] at hu
          rw [Finset.mem_union]
          rcases hu.2 with huQ' | huR'
          · left; exact Finset.mem_erase.mpr ⟨((SimpleGraph.mem_neighborFinset H q u).mp hu.1).ne.symm, huQ'⟩
          · right; exact Finset.mem_inter.mpr ⟨hu.1, Finset.mem_of_mem_erase huR'⟩
        have hc := Finset.card_le_card hsub
        have hun := Finset.card_union_le (Q'.erase q) (H.neighborFinset q ∩ R)
        rw [Finset.card_erase_of_mem hq, hQ'4] at hun
        have := hqR q hqQ
        omega
      -- Every r ∈ R' has (N_H(r) ∩ Q).card ≤ 2 (since sum over R is ≤ 5 and y maximizes it!)
      have hR'Q2 : ∀ r ∈ R', (H.neighborFinset r ∩ Q).card ≤ 2 := by
        intro r hr
        have hrR : r ∈ R := Finset.mem_of_mem_erase hr
        have hry : r ≠ y := (Finset.mem_erase.mp hr).1
        have hle := hyMax r hrR
        have hsub2 : ({r, y} : Finset V) ⊆ R := by
          intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl <;> assumption
        have hsum2 := Finset.sum_le_sum_of_subset (f := fun t => (H.neighborFinset t ∩ Q).card) hsub2
        rw [Finset.sum_pair hry] at hsum2
        omega
      -- Analyze HasBad8 (H.induce S):
      rcases hbad with ⟨K, hK5', hKcl⟩ | h23
      · -- K₅ in S = Q' ∪ R' (4 + 4): let KV = K.image val!
        let KV : Finset V := K.image Subtype.val
        have hKV5 : KV.card = 5 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hK5']
        have hKVsub : KV ⊆ Q' ∪ R' := fun u hu => by
          rw [Finset.mem_image] at hu; obtain ⟨a, _, rfl⟩ := hu; exact a.property
        have hKVcl : H.IsClique (KV : Set V) := fun a ha b hb hab => by
          rw [Finset.mem_coe, Finset.mem_image] at ha hb
          obtain ⟨u, hu, rfl⟩ := ha; obtain ⟨v, hv, rfl⟩ := hb
          exact hKcl hu hv (fun he => hab (congrArg Subtype.val he))
        have hsplit : (KV ∩ Q').card + (KV ∩ R').card = 5 := by
          rw [← Finset.card_union_of_disjoint (Disjoint.mono Finset.inter_subset_right
            Finset.inter_subset_right hdisjQ'R'), ← Finset.inter_union_distrib_left,
            Finset.inter_eq_left.mpr hKVsub, hKV5]
        have hKQle4 : (KV ∩ Q').card ≤ 4 := le_trans (Finset.card_le_card Finset.inter_subset_right) (by rw [hQ'4])
        have hKRle4 : (KV ∩ R').card ≤ 4 := le_trans (Finset.card_le_card Finset.inter_subset_right) (by rw [hR'4])
        by_cases h1 : (KV ∩ R').card = 1
        · obtain ⟨r, hr⟩ := Finset.card_eq_one.mp h1
          have hrKV : r ∈ KV := (Finset.mem_inter.mp (by rw [hr]; simp)).1
          have hrR' : r ∈ R' := (Finset.mem_inter.mp (by rw [hr]; simp)).2
          have hsub : KV ∩ Q' ⊆ H.neighborFinset r ∩ Q := by
            intro q hq
            rw [Finset.mem_inter] at hq ⊢
            refine ⟨(SimpleGraph.mem_neighborFinset H r q).mpr ?_, Finset.mem_of_mem_erase hq.2⟩
            exact hKVcl hrKV hq.1 (fun h => Finset.disjoint_right.mp hdisjQ'R' hrR' (h ▸ hq.2))
          have hc := Finset.card_le_card hsub
          have := hR'Q2 r hrR'
          omega
        · have hQpos : 0 < (KV ∩ Q').card := by omega
          have hRge2 : 2 ≤ (KV ∩ R').card := by omega
          obtain ⟨q, hq⟩ := Finset.card_pos.mp hQpos
          have hqKV : q ∈ KV := (Finset.mem_inter.mp hq).1
          have hqQ' : q ∈ Q' := (Finset.mem_inter.mp hq).2
          have hsub : KV ∩ R' ⊆ H.neighborFinset q ∩ R := by
            intro r hr
            rw [Finset.mem_inter] at hr ⊢
            refine ⟨(SimpleGraph.mem_neighborFinset H q r).mpr ?_, Finset.mem_of_mem_erase hr.2⟩
            exact hKVcl hqKV hr.1 (fun h => Finset.disjoint_left.mp hdisjQ'R' hqQ' (h ▸ hr.2))
          have hc := Finset.card_le_card hsub
          have := hqR q (Finset.mem_of_mem_erase hqQ')
          omega
      · -- K₃ ∨ 3K₁ or K₃,₅ in H.induce S => 3 vertices of degree 5 in H.induce S!
        -- None can be in Q' (by hQ'deg ≤ 4!), so all 3 are in R'!
        -- Each r ∈ R' has ≤ 3 neighbors in R' and hence ≥ 2 neighbors in Q' -> sum of edges from R' to Q' ≥ 6 > 5!
        obtain ⟨A, hA3, hA5⟩ := exists_three_deg_five_of_k3join_or_k35 h23
        let AV : Finset V := A.image Subtype.val
        have hAV3 : AV.card = 3 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hA3]
        have hAVdeg : ∀ a ∈ AV, 5 ≤ (H.neighborFinset a ∩ S).card := by
          intro a ha
          rw [Finset.mem_image] at ha
          obtain ⟨u, huA, rfl⟩ := ha
          have hsub : ((H.induce (S : Set V)).neighborFinset u).image Subtype.val ⊆ H.neighborFinset u.val ∩ S := by
            intro w hw
            rw [Finset.mem_image] at hw
            obtain ⟨z, hz, rfl⟩ := hw
            rw [SimpleGraph.mem_neighborFinset] at hz
            exact Finset.mem_inter.mpr ⟨(SimpleGraph.mem_neighborFinset H u.val z.val).mpr hz, z.property⟩
          have hc := Finset.card_le_card hsub
          rw [Finset.card_image_of_injective _ Subtype.val_injective,
            SimpleGraph.card_neighborFinset_eq_degree] at hc
          exact le_trans (hA5 u huA) hc
        have hAVR' : AV ⊆ R' := by
          intro a ha
          have haS : a ∈ S := by
            rw [Finset.mem_image] at ha; obtain ⟨u, _, rfl⟩ := ha; exact u.property
          rw [Finset.mem_union] at haS
          rcases haS with haQ' | haR'
          · exfalso; have := hQ'deg a haQ'; have := hAVdeg a ha; omega
          · exact haR'
        have hAVQ2 : ∀ a ∈ AV, 2 ≤ (H.neighborFinset a ∩ Q).card := by
          intro a ha
          have haR' : a ∈ R' := hAVR' ha
          have hsub : H.neighborFinset a ∩ S ⊆ R'.erase a ∪ (H.neighborFinset a ∩ Q) := by
            intro w hw
            rw [Finset.mem_inter, Finset.mem_union] at hw
            rw [Finset.mem_union]
            rcases hw.2 with hwQ' | hwR'
            · right; exact Finset.mem_inter.mpr ⟨hw.1, Finset.mem_of_mem_erase hwQ'⟩
            · left; exact Finset.mem_erase.mpr ⟨((SimpleGraph.mem_neighborFinset H a w).mp hw.1).ne.symm, hwR'⟩
          have hc := Finset.card_le_card hsub
          have hun := Finset.card_union_le (R'.erase a) (H.neighborFinset a ∩ Q)
          rw [Finset.card_erase_of_mem haR', hR'4] at hun
          have := hAVdeg a ha
          omega
        have hAVsubR : AV ⊆ R := Finset.Subset.trans hAVR' (Finset.erase_subset y R)
        have hsum3 : 6 ≤ ∑ r ∈ R, (H.neighborFinset r ∩ Q).card := by
          calc 6 = ∑ _a ∈ AV, 2 := by rw [Finset.sum_const, hAV3]; rfl
            _ ≤ ∑ a ∈ AV, (H.neighborFinset a ∩ Q).card := Finset.sum_le_sum hAVQ2
            _ ≤ ∑ r ∈ R, (H.neighborFinset r ∩ Q).card := Finset.sum_le_sum_of_subset hAVsubR
        omega
  -- Case 2: No K₅, and H contains K₃ ∨ 3K₁ on A ∪ B (|A|=3, |B|=3)!
  · by_cases hK331 : HasCliqueJoin H 3 3
    · obtain ⟨A, B, hA3, hB3, hdisjAB, hAcl, hABadj⟩ := hK331
      obtain ⟨x, hxA⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
      obtain ⟨y, hyB⟩ := Finset.card_pos.mp (by omega : 0 < B.card)
      let A' := A.erase x
      let B' := B.erase y
      let R := (A ∪ B)ᶜ
      have hA'2 : A'.card = 2 := by rw [Finset.card_erase_of_mem hxA, hA3]
      have hB'2 : B'.card = 2 := by rw [Finset.card_erase_of_mem hyB, hB3]
      have hR4 : R.card = 4 := by
        rw [Finset.card_compl, Finset.card_union_of_disjoint hdisjAB, hV, hA3, hB3]
      have hxy : x ≠ y := fun h => Finset.disjoint_left.mp hdisjAB hxA (h ▸ hyB)
      let S : Finset V := (Finset.univ.erase x).erase y
      have hS8 : S.card = 8 := by
        rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hxy.symm, Finset.mem_univ y⟩),
          Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, hV]
      refine ⟨S, hS8, fun hbad => ?_⟩
      -- First: every a ∈ A has N_H(a) = A.erase a ∪ B (zero edges to R)!
      have hNa : ∀ a ∈ A, H.neighborFinset a = A.erase a ∪ B := by
        intro a ha
        refine neighborFinset_eq_of_subset_card_five (hdeg a) ?_ ?_
        · rw [Finset.card_union_of_disjoint (Finset.disjoint_of_subset_left (Finset.erase_subset a A) hdisjAB),
            Finset.card_erase_of_mem ha, hA3, hB3]
        · intro w hw; rw [Finset.mem_union, Finset.mem_erase] at hw
          rcases hw with ⟨hne, hwA⟩ | hwB
          · exact hAcl ha hwA hne.symm
          · exact hABadj a ha w hwB
      -- H.induce S has no K₅ (since H has no K₅!)
      rcases hbad with hK5' | h23
      · exact hK5 (hasClique_of_induce hK5')
      · -- So H.induce S has 3 vertices of degree 5 in H.induce S!
        -- Show: no vertex of A' or B' has degree 5 in H.induce S (every a ∈ A' has x removed => deg ≤ 4,
        -- every b ∈ B' has x ∈ A removed => deg ≤ 4)!
        -- Hence all 3 degree-5 vertices lie in R!
        have hdeg_le4_AB : ∀ u : (S : Set V), u.val ∈ A ∪ B → (H.induce (S : Set V)).degree u ≤ 4 := by
          intro ⟨u, huS⟩ huAB
          have hux : u ≠ x := (Finset.mem_erase.mp (Finset.mem_of_mem_erase huS)).1
          have hxNu : x ∈ H.neighborFinset u := by
            rw [SimpleGraph.mem_neighborFinset]
            rw [Finset.mem_union] at huAB
            rcases huAB with huA | huB
            · exact hAcl huA hxA hux
            · exact (hABadj x hxA u huB).symm
          have hsub : ((H.induce (S : Set V)).neighborFinset ⟨u, huS⟩).image Subtype.val ⊆ (H.neighborFinset u).erase x := by
            intro w hw
            rw [Finset.mem_image] at hw; obtain ⟨⟨w, hwS⟩, hwN, rfl⟩ := hw
            rw [SimpleGraph.mem_neighborFinset] at hwN
            exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp (Finset.mem_of_mem_erase hwS)).1,
              (SimpleGraph.mem_neighborFinset H u w).mpr hwN⟩
          have hc := Finset.card_le_card hsub
          rw [Finset.card_image_of_injective _ Subtype.val_injective,
            SimpleGraph.card_neighborFinset_eq_degree, Finset.card_erase_of_mem hxNu,
            SimpleGraph.card_neighborFinset_eq_degree] at hc
          have := hdeg u; omega
        -- Every r ∈ R has ZERO neighbors in A (so N_{H[S]}(r) ⊆ R ∪ B' has size ≤ 6 - 1 = 5)!
        have hnoRA : ∀ r ∈ R, ∀ a ∈ A, ¬ H.Adj r a := by
          intro r hr a ha hadj
          have hrNa : r ∈ H.neighborFinset a := (SimpleGraph.mem_neighborFinset H a r).mpr hadj.symm
          rw [hNa a ha, Finset.mem_union] at hrNa
          have hrAB : r ∉ A ∪ B := Finset.mem_compl.mp hr
          rcases hrNa with h1 | h2
          · exact hrAB (Finset.mem_union_left B (Finset.mem_of_mem_erase h1))
          · exact hrAB (Finset.mem_union_right A h2)
        -- Now split h23 into K₃ ∨ 3K₁ vs K₃,₅!
        rcases h23 with ⟨A2, B2, hA2_3, hB2_3, hdisj2, hcl2, hadj2⟩ | ⟨A2, B2, hA2_3, hB2_5, hdisj2, hadj2⟩
        · -- Every vertex of A2 has degree 5 in H.induce S, so A2V ⊆ R!
          let A2V := A2.image Subtype.val
          let B2V := B2.image Subtype.val
          have hA2V3 : A2V.card = 3 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hA2_3]
          have hB2V3 : B2V.card = 3 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hB2_3]
          have hA2R : A2V ⊆ R := by
            intro r hr
            rw [Finset.mem_image] at hr; obtain ⟨u, hu, rfl⟩ := hr
            have hdu5 : 5 ≤ (H.induce (S : Set V)).degree u := by
              have hsub : A2.erase u ∪ B2 ⊆ (H.induce (S : Set V)).neighborFinset u := fun w hw => by
                rw [Finset.mem_union, Finset.mem_erase] at hw
                rw [SimpleGraph.mem_neighborFinset]
                rcases hw with ⟨hne, hwA⟩ | hwB
                · exact hcl2 hu hwA hne.symm
                · exact hadj2 u hu w hwB
              have hc := Finset.card_le_card hsub
              rw [Finset.card_union_of_disjoint (Finset.disjoint_of_subset_left (Finset.erase_subset u A2) hdisj2),
                Finset.card_erase_of_mem hu, hA2_3, hB2_3, SimpleGraph.card_neighborFinset_eq_degree] at hc
              exact hc
            rw [Finset.mem_compl]
            intro huAB
            have := hdeg_le4_AB u huAB; omega
          -- Every vertex of B2V is adjacent to A2V (⊆ R), so B2V ∩ A = ∅, hence B2V ⊆ (R \ A2V) ∪ B' (size 1 + 2 = 3)!
          -- Since |B2V| = 3 and |R \ A2V| = 1, B2V MUST contain a vertex b ∈ B'!
          -- That b ∈ B' is adjacent to all 3 vertices of A2V (⊆ R) AND all 3 vertices of A => deg_H(b) ≥ 6 > 5!
          have hB2noA : Disjoint B2V A := by
            rw [Finset.disjoint_left]; intro w hwB2 hwA
            obtain ⟨r, hr⟩ := Finset.card_pos.mp (by omega : 0 < A2V.card)
            rw [Finset.mem_image] at hwB2 hr
            obtain ⟨u, huB2, rfl⟩ := hwB2; obtain ⟨v, hvA2, rfl⟩ := hr
            exact hnoRA v.val (hA2R (Finset.mem_image_of_mem Subtype.val hvA2)) u.val hwA (hadj2 v hvA2 u huB2)
          have hdisj2V : Disjoint A2V B2V := by
            rw [Finset.disjoint_left]; intro w hw1 hw2
            rw [Finset.mem_image] at hw1 hw2
            obtain ⟨u, hu, rfl⟩ := hw1; obtain ⟨v, hv, he⟩ := hw2
            exact Finset.disjoint_left.mp hdisj2 hu ((Subtype.ext he) ▸ hv)
          have hB2_sub_RB : B2V ⊆ (R \ A2V) ∪ B' := by
            intro w hw
            rw [Finset.mem_image] at hw; obtain ⟨⟨w, hwS⟩, hwB2, rfl⟩ := hw
            have hwy : w ≠ y := (Finset.mem_erase.mp hwS).1
            have hwA : w ∉ A := Finset.disjoint_left.mp hB2noA (Finset.mem_image_of_mem Subtype.val hwB2)
            by_cases hwB : w ∈ B
            · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hwy, hwB⟩)
            · have hwR : w ∈ R := Finset.mem_compl.mpr (by rw [Finset.mem_union]; tauto)
              have hwA2 : w ∉ A2V := Finset.disjoint_right.mp hdisj2V (Finset.mem_image_of_mem Subtype.val hwB2)
              exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hwR, hwA2⟩)
          have hexB' : (B2V ∩ B').Nonempty := by
            by_contra hemp
            rw [Finset.not_nonempty_iff_eq_empty] at hemp
            have hsubR : B2V ⊆ R \ A2V := fun w hw => by
              have h1 := hB2_sub_RB hw
              rw [Finset.mem_union] at h1
              exact h1.resolve_right fun hwB' => by
                have : w ∈ B2V ∩ B' := Finset.mem_inter.mpr ⟨hw, hwB'⟩
                rw [hemp] at this; exact Finset.notMem_empty w this
            have hc := Finset.card_le_card hsubR
            rw [Finset.card_sdiff_of_subset hA2R, hR4, hA2V3, hB2V3] at hc
            omega
          obtain ⟨b, hb⟩ := hexB'
          have hbB2 : b ∈ B2V := (Finset.mem_inter.mp hb).1
          have hbB : b ∈ B := Finset.mem_of_mem_erase (Finset.mem_inter.mp hb).2
          -- b is adjacent to all 3 vertices of A and all 3 vertices of A2V (disjoint from A since A2V ⊆ R!)
          have hsub6 : A ∪ A2V ⊆ H.neighborFinset b := by
            intro w hw; rw [Finset.mem_union] at hw; rw [SimpleGraph.mem_neighborFinset]
            rcases hw with hwA | hwA2
            · exact (hABadj w hwA b hbB).symm
            · rw [Finset.mem_image] at hbB2 hwA2
              obtain ⟨u, huB2, rfl⟩ := hbB2; obtain ⟨v, hvA2, rfl⟩ := hwA2
              exact (hadj2 v hvA2 u huB2).symm
          have hdisjAA2 : Disjoint A A2V :=
            Finset.disjoint_of_subset_right hA2R (Finset.disjoint_of_subset_left (Finset.subset_union_left) disjoint_compl_right)
          have hc := Finset.card_le_card hsub6
          rw [Finset.card_union_of_disjoint hdisjAA2, hA3, hA2V3, SimpleGraph.card_neighborFinset_eq_degree] at hc
          have := hdeg b; omega
        · -- K₃,₅ in H.induce S: A2V ⊆ R (size 3), B2V = S \ A2V (size 5) MUST contain A' (size 2)!
          -- So every r ∈ A2V is adjacent to A' ⊆ A, contradicting hnoRA!
          let A2V := A2.image Subtype.val
          let B2V := B2.image Subtype.val
          have hA2V3 : A2V.card = 3 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hA2_3]
          have hB2V5 : B2V.card = 5 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hB2_5]
          have hA2R : A2V ⊆ R := by
            intro r hr
            rw [Finset.mem_image] at hr; obtain ⟨u, hu, rfl⟩ := hr
            have hdu5 : 5 ≤ (H.induce (S : Set V)).degree u := by
              have hsub : B2 ⊆ (H.induce (S : Set V)).neighborFinset u := fun w hw => by
                rw [SimpleGraph.mem_neighborFinset]; exact hadj2 u hu w hw
              have hc := Finset.card_le_card hsub
              rw [hB2_5, SimpleGraph.card_neighborFinset_eq_degree] at hc
              exact hc
            rw [Finset.mem_compl]; intro huAB
            have := hdeg_le4_AB u huAB; omega
          have hdisj2V : Disjoint A2V B2V := by
            rw [Finset.disjoint_left]; intro w hw1 hw2
            rw [Finset.mem_image] at hw1 hw2
            obtain ⟨u, hu, rfl⟩ := hw1; obtain ⟨v, hv, he⟩ := hw2
            exact Finset.disjoint_left.mp hdisj2 hu ((Subtype.ext he) ▸ hv)
          have hA2subS : A2V ⊆ S := fun w hw => by
            rw [Finset.mem_image] at hw; obtain ⟨u, _, rfl⟩ := hw; exact u.property
          have hB2subS : B2V ⊆ S := fun w hw => by
            rw [Finset.mem_image] at hw; obtain ⟨u, _, rfl⟩ := hw; exact u.property
          have hSeq : A2V ∪ B2V = S := Finset.eq_of_subset_of_card_le (Finset.union_subset hA2subS hB2subS)
            (by rw [Finset.card_union_of_disjoint hdisj2V, hA2V3, hB2V5, hS8])
          obtain ⟨a, haA'⟩ := Finset.card_pos.mp (by omega : 0 < A'.card)
          have haA : a ∈ A := Finset.mem_of_mem_erase haA'
          have hax : a ≠ x := (Finset.mem_erase.mp haA').1
          have hay : a ≠ y := fun h => Finset.disjoint_left.mp hdisjAB haA (h ▸ hyB)
          have haS : a ∈ S := Finset.mem_erase.mpr ⟨hay, Finset.mem_erase.mpr ⟨hax, Finset.mem_univ a⟩⟩
          have haB2 : a ∈ B2V := by
            rw [← hSeq, Finset.mem_union] at haS
            exact haS.resolve_left fun haA2 => (Finset.mem_compl.mp (hA2R haA2)) (Finset.mem_union_left B haA)
          obtain ⟨r, hr⟩ := Finset.card_pos.mp (by omega : 0 < A2V.card)
          rw [Finset.mem_image] at haB2 hr
          obtain ⟨u, huB2, rfl⟩ := haB2; obtain ⟨v, hvA2, rfl⟩ := hr
          exact hnoRA v.val (hA2R (Finset.mem_image_of_mem Subtype.val hvA2)) u.val haA (hadj2 v hvA2 u huB2)
    -- Case 3: No K₅, no K₃ ∨ 3K₁, and H contains K₃,₅ on A ∪ B (|A|=3, |B|=5)!
    · by_cases hK35 : HasK H 3 5
      · obtain ⟨A, B, hA3, hB5, hdisjAB, hABadj⟩ := hK35
        obtain ⟨x, hxA⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
        obtain ⟨y, hyB⟩ := Finset.card_pos.mp (by omega : 0 < B.card)
        have hxy : x ≠ y := fun h => Finset.disjoint_left.mp hdisjAB hxA (h ▸ hyB)
        let S : Finset V := (Finset.univ.erase x).erase y
        have hS8 : S.card = 8 := by
          rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hxy.symm, Finset.mem_univ y⟩),
            Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, hV]
        refine ⟨S, hS8, fun hbad => ?_⟩
        -- Since H has no K₅ and no K₃ ∨ 3K₁, H.induce S can only have K₃,₅!
        rcases hbad with h1 | h2 | ⟨A2, B2, hA2_3, hB2_5, hdisj2, hadj2⟩
        · exact hK5 (hasClique_of_induce h1)
        · exact hK331 (hasCliqueJoin_of_induce h2)
        · -- Every a ∈ A has N_H(a) = B (zero edges outside B!), so every a ∈ A.erase x has degree 4 in H.induce S!
          -- Hence A2V ∩ A = ∅, so A.erase x ⊆ B2V!
          -- Therefore every u ∈ A2V is adjacent to A.erase x => u ∈ B!
          -- Hence every u ∈ A2V is adjacent in H to all 5 vertices of B2V PLUS x ∈ A (since x ∉ S) => deg_H(u) ≥ 6 > 5!
          have hNa : ∀ a ∈ A, H.neighborFinset a = B :=
            fun a ha => neighborFinset_eq_of_subset_card_five (hdeg a) hB5 (hABadj a ha)
          let A2V := A2.image Subtype.val
          let B2V := B2.image Subtype.val
          have hA2V3 : A2V.card = 3 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hA2_3]
          have hB2V5 : B2V.card = 5 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hB2_5]
          have hdisj2V : Disjoint A2V B2V := by
            rw [Finset.disjoint_left]; intro w hw1 hw2
            rw [Finset.mem_image] at hw1 hw2
            obtain ⟨u, hu, rfl⟩ := hw1; obtain ⟨v, hv, he⟩ := hw2
            exact Finset.disjoint_left.mp hdisj2 hu ((Subtype.ext he) ▸ hv)
          have hA2subS : A2V ⊆ S := fun w hw => by
            rw [Finset.mem_image] at hw; obtain ⟨u, _, rfl⟩ := hw; exact u.property
          have hB2subS : B2V ⊆ S := fun w hw => by
            rw [Finset.mem_image] at hw; obtain ⟨u, _, rfl⟩ := hw; exact u.property
          have hSeq : A2V ∪ B2V = S := Finset.eq_of_subset_of_card_le (Finset.union_subset hA2subS hB2subS)
            (by rw [Finset.card_union_of_disjoint hdisj2V, hA2V3, hB2V5, hS8])
          -- A.erase x (card 2) is disjoint from A2V (since a ∈ A.erase x has y ∈ B = N_H(a) deleted => deg_S(a) ≤ 4!)
          have hA'subB2 : A.erase x ⊆ B2V := by
            intro a ha
            have haA : a ∈ A := Finset.mem_of_mem_erase ha
            have hax : a ≠ x := (Finset.mem_erase.mp ha).1
            have hay : a ≠ y := fun h => Finset.disjoint_left.mp hdisjAB haA (h ▸ hyB)
            have haS : a ∈ S := Finset.mem_erase.mpr ⟨hay, Finset.mem_erase.mpr ⟨hax, Finset.mem_univ a⟩⟩
            rw [← hSeq, Finset.mem_union] at haS
            refine haS.resolve_left fun haA2 => ?_
            rw [Finset.mem_image] at haA2
            obtain ⟨u, huA2, hua⟩ := haA2
            have hsub : B2V ⊆ B.erase y := by
              intro w hw
              rw [Finset.mem_image] at hw; obtain ⟨v, hvB2, rfl⟩ := hw
              have hwy : v.val ≠ y := (Finset.mem_erase.mp v.property).1
              have haw : H.Adj a v.val := hua ▸ hadj2 u huA2 v hvB2
              have hwNa : v.val ∈ H.neighborFinset a := (SimpleGraph.mem_neighborFinset H a v.val).mpr haw
              rw [hNa a haA] at hwNa
              exact Finset.mem_erase.mpr ⟨hwy, hwNa⟩
            have hc := Finset.card_le_card hsub
            rw [hB2V5, Finset.card_erase_of_mem hyB, hB5] at hc
            omega
          -- Pick a ∈ A.erase x and u ∈ A2V: u is adjacent to a, so u ∈ N_H(a) = B!
          obtain ⟨a, haA'⟩ := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hxA, hA3]; omega : 0 < (A.erase x).card)
          obtain ⟨u, huA2⟩ := Finset.card_pos.mp (by omega : 0 < A2V.card)
          have haB2 : a ∈ B2V := hA'subB2 haA'
          rw [Finset.mem_image] at huA2 haB2
          obtain ⟨u', hu'A2, rfl⟩ := huA2
          obtain ⟨a', ha'B2, ha'eq⟩ := haB2
          have hua : H.Adj u'.val a := ha'eq ▸ hadj2 u' hu'A2 a' ha'B2
          have huB : u'.val ∈ B := by
            have := (SimpleGraph.mem_neighborFinset H a u'.val).mpr hua.symm
            rwa [hNa a (Finset.mem_of_mem_erase haA')] at this
          -- Thus u'.val is adjacent in H to x (since x ∈ A, u'.val ∈ B) AND all 5 vertices of B2V (and x ∉ B2V since x ∉ S)!
          have hx_not_B2V : x ∉ B2V := fun hxB2 => (Finset.mem_erase.mp (Finset.mem_of_mem_erase (hB2subS hxB2))).1 rfl
          have hsub6 : insert x B2V ⊆ H.neighborFinset u'.val := by
            intro w hw; rw [Finset.mem_insert] at hw; rw [SimpleGraph.mem_neighborFinset]
            rcases hw with hw | hwB2
            · rw [hw]; exact (hABadj x hxA u'.val huB).symm
            · rw [Finset.mem_image] at hwB2; obtain ⟨v, hvB2, rfl⟩ := hwB2
              exact hadj2 u' hu'A2 v hvB2
          have hc := Finset.card_le_card hsub6
          rw [Finset.card_insert_of_notMem hx_not_B2V, hB2V5, SimpleGraph.card_neighborFinset_eq_degree] at hc
          have := hdeg u'.val; omega
      -- Case 4: H has no K₅, no K₃ ∨ 3K₁, and no K₃,₅ at all! Pick any 8-set!
      · obtain ⟨S, _, hS8⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset V))
          (by rw [Finset.card_univ, hV]; omega : 8 ≤ (Finset.univ : Finset V).card)
        refine ⟨S, hS8, fun hbad => ?_⟩
        rcases hasBad8_of_induce hbad with h1 | h2 | h3
        · exact hK5 h1
        · exact hK331 h2
        · exact hK35 h3

/-- **Corollary (11-vertex hitting lemma)**: Every 11-vertex graph `H` with `Δ(H) ≤ 5` has
an 8-vertex induced subgraph with no `K₅`, no `K₃ ∨ 3K₁`, and no `K₃,₅`. -/
theorem exists_good_eight_of_eleven {H : SimpleGraph V} [DecidableRel H.Adj]
    (hV : Fintype.card V = 11) (hdeg : ∀ v : V, H.degree v ≤ 5) :
    ∃ S : Finset V, S.card = 8 ∧ ¬ HasBad8 (H.induce (S : Set V)) := by
  classical
  obtain ⟨z⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
  let T : Finset V := Finset.univ.erase z
  have hT10 : T.card = 10 := by rw [Finset.card_erase_of_mem (Finset.mem_univ z), Finset.card_univ, hV]
  have hTcard : Fintype.card (T : Set V) = 10 := by rw [card_coe_finset_set, hT10]
  obtain ⟨S', hS'8, hgood⟩ := exists_good_eight_of_ten (H := H.induce (T : Set V)) hTcard
    (fun w => le_trans (degree_induce_le H T w) (hdeg w.val))
  let S : Finset V := S'.image Subtype.val
  have hS8 : S.card = 8 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hS'8]
  refine ⟨S, hS8, fun hbad => hgood ?_⟩
  -- Pull back HasBad8 from H.induce S to (H.induce T).induce S'!
  have hSsubT : S ⊆ T := fun x hx => by
    rw [Finset.mem_image] at hx; obtain ⟨u, _, rfl⟩ := hx; exact u.property
  let e : (S : Set V) ≃ (S' : Set (T : Set V)) := {
    toFun := fun ⟨x, hx⟩ => ⟨⟨x, hSsubT hx⟩, by
      rw [Finset.mem_coe] at hx ⊢
      rw [Finset.mem_image] at hx
      obtain ⟨u, hu, rfl⟩ := hx
      exact hu⟩
    invFun := fun ⟨⟨x, _⟩, hx⟩ => ⟨x, Finset.mem_image_of_mem Subtype.val hx⟩
    left_inv := fun ⟨_, _⟩ => rfl
    right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
  }
  exact hasBad8_map_equiv e (fun _ _ h => h) hbad

end HittingTenAndEleven

section Closure16

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Order ν = 16, Part A (`nu_eq_16_no_bad_eight`)**:
If `G` is minimally 4-extendable on 16 vertices and `∀ v, 10 ≤ G.degree v` (so `Δ(Gᶜ) ≤ 5`),
then `Gᶜ` contains NO `K₅`, NO `K₃ ∨ 3K₁`, and NO `K₃,₅`. -/
theorem nu_eq_16_no_bad_eight {G : SimpleGraph V} [DecidableRel G.Adj]
    (hV : Fintype.card V = 16) (hmin : IsMinimallyKExtendable G 4)
    (hdeg : ∀ v : V, 10 ≤ G.degree v) : ¬ HasBad8 Gᶜ := by
  classical
  let F := Gᶜ
  have hcdeg : ∀ v : V, F.degree v ≤ 5 := fun v => by
    have h1 := compl_degree_le_of_degree_ge (G := G) (d := 10) hdeg v
    have h2 : F.degree v = Gᶜ.degree v := degree_congr rfl v
    omega
  -- Closure from 4-extendability: if S is an 8-set and ¬ HasPM (G.induce S), then ¬ HasPM (G.induce Sᶜ)!
  have hclosure : ∀ S : Finset V, S.card = 8 → ¬ HasPM (G.induce (S : Set V)) →
      ¬ HasPM (G.induce ((Sᶜ : Finset V) : Set V)) := by
    intro S hS hSno hScPM
    have hSc8 : Sᶜ.card = 8 := by rw [Finset.card_compl, hV, hS]
    have h1 := (isKExtendable_iff_compl_pm.mp hmin.1).2 Sᶜ hSc8 hScPM
    have hScc : (Sᶜ)ᶜ = S := compl_compl S
    rw [hScc] at h1
    exact hSno h1
  -- Step 1: F has NO K₅ (by 11-vertex hitting lemma + closure!)
  have hnoK5 : ¬ HasClique F 5 := by
    rintro ⟨Q, hQ5, hQcl⟩
    let R : Finset V := Qᶜ
    have hR11 : R.card = 11 := by rw [Finset.card_compl, hV, hQ5]
    obtain ⟨W', hW'8, hW'good⟩ := exists_good_eight_of_eleven (H := F.induce (R : Set V))
      (by rw [card_coe_finset_set, hR11]) (fun w => le_trans (degree_induce_le F R w) (hcdeg w.val))
    let W : Finset V := W'.image Subtype.val
    have hW8 : W.card = 8 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hW'8]
    have hWsubR : W ⊆ R := fun x hx => by
      rw [Finset.mem_image] at hx; obtain ⟨u, _, rfl⟩ := hx; exact u.property
    have hQsubWc : Q ⊆ Wᶜ := fun q hq => by
      rw [Finset.mem_compl]; intro hqW
      exact (Finset.mem_compl.mp (hWsubR hqW)) hq
    have hWc8 : Wᶜ.card = 8 := by rw [Finset.card_compl, hV, hW8]
    have hWcNoPM : ¬ HasPM (G.induce ((Wᶜ : Finset V) : Set V)) :=
      not_hasPM_of_compl_clique hQsubWc (by omega) hQcl
    have hWNoPM : ¬ HasPM (G.induce (W : Set V)) := by
      have := hclosure Wᶜ hWc8 hWcNoPM
      rwa [compl_compl] at this
    have hWbad : HasBad8 (F.induce (W : Set V)) :=
      (not_hasPM_eight_iff_hasBad8 hcdeg hW8).mp hWNoPM
    -- Transport HasBad8 back to (F.induce R).induce W'
    let e : (W : Set V) ≃ (W' : Set (R : Set V)) := {
      toFun := fun ⟨x, hx⟩ => ⟨⟨x, hWsubR hx⟩, by
        rw [Finset.mem_coe] at hx ⊢; rw [Finset.mem_image] at hx
        obtain ⟨u, hu, rfl⟩ := hx; exact hu⟩
      invFun := fun ⟨⟨x, _⟩, hx⟩ => ⟨x, Finset.mem_image_of_mem Subtype.val hx⟩
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
    }
    exact hW'good (hasBad8_map_equiv e (fun _ _ h => h) hWbad)
  -- Step 2: F has NO K₃ ∨ 3K₁ (by 10-vertex hitting lemma + closure!)
  have hnoK331 : ¬ HasCliqueJoin F 3 3 := by
    rintro ⟨A, B, hA3, hB3, hdisjAB, hAcl, hABadj⟩
    let R : Finset V := (A ∪ B)ᶜ
    have hR10 : R.card = 10 := by
      rw [Finset.card_compl, Finset.card_union_of_disjoint hdisjAB, hV, hA3, hB3]
    obtain ⟨W', hW'8, hW'good⟩ := exists_good_eight_of_ten (H := F.induce (R : Set V))
      (by rw [card_coe_finset_set, hR10]) (fun w => le_trans (degree_induce_le F R w) (hcdeg w.val))
    let W : Finset V := W'.image Subtype.val
    have hW8 : W.card = 8 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hW'8]
    have hWsubR : W ⊆ R := fun x hx => by
      rw [Finset.mem_image] at hx; obtain ⟨u, _, rfl⟩ := hx; exact u.property
    have hAsubWc : A ⊆ Wᶜ := fun a ha => by
      rw [Finset.mem_compl]; intro haW
      exact (Finset.mem_compl.mp (hWsubR haW)) (Finset.mem_union_left B ha)
    have hBsubWc : B ⊆ Wᶜ := fun b hb => by
      rw [Finset.mem_compl]; intro hbW
      exact (Finset.mem_compl.mp (hWsubR hbW)) (Finset.mem_union_right A hb)
    have hWc8 : Wᶜ.card = 8 := by rw [Finset.card_compl, hV, hW8]
    have hWcNoPM : ¬ HasPM (G.induce ((Wᶜ : Finset V) : Set V)) :=
      not_hasPM_eight_of_hasCliqueJoin33 hWc8 hAsubWc hBsubWc hA3 hB3 hdisjAB hAcl hABadj
    have hWNoPM : ¬ HasPM (G.induce (W : Set V)) := by
      have := hclosure Wᶜ hWc8 hWcNoPM
      rwa [compl_compl] at this
    have hWbad : HasBad8 (F.induce (W : Set V)) :=
      (not_hasPM_eight_iff_hasBad8 hcdeg hW8).mp hWNoPM
    let e : (W : Set V) ≃ (W' : Set (R : Set V)) := {
      toFun := fun ⟨x, hx⟩ => ⟨⟨x, hWsubR hx⟩, by
        rw [Finset.mem_coe] at hx ⊢; rw [Finset.mem_image] at hx
        obtain ⟨u, hu, rfl⟩ := hx; exact hu⟩
      invFun := fun ⟨⟨x, _⟩, hx⟩ => ⟨x, Finset.mem_image_of_mem Subtype.val hx⟩
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
    }
    exact hW'good (hasBad8_map_equiv e (fun _ _ h => h) hWbad)
  -- Step 3: F has NO K₃,₅! If it did, then by closure F contains K₃,₅ ⊔ K₃,₅, and deleting
  -- a₁ a₂ (between the two 3-parts) preserves exact bad 8-sets, contradicting minimality!
  intro hbad
  rcases hbad with h1 | h2 | ⟨A₁, B₁, hA₁3, hB₁5, hdisj1, h1adj⟩
  · exact hnoK5 h1
  · exact hnoK331 h2
  · let X₁ : Finset V := A₁ ∪ B₁
    have hX₁8 : X₁.card = 8 := by rw [Finset.card_union_of_disjoint hdisj1, hA₁3, hB₁5]
    have hX₁NoPM : ¬ HasPM (G.induce (X₁ : Set V)) :=
      not_hasPM_of_compl_bip rfl (by rw [hA₁3]; exact ⟨1, rfl⟩) h1adj
    have hX₂8 : X₁ᶜ.card = 8 := by rw [Finset.card_compl, hV, hX₁8]
    have hX₂NoPM : ¬ HasPM (G.induce ((X₁ᶜ : Finset V) : Set V)) := hclosure X₁ hX₁8 hX₁NoPM
    have hX₂bad := (not_hasPM_eight_iff_hasBad8 hcdeg hX₂8).mp hX₂NoPM
    -- Since F has no K₅ and no K₃ ∨ 3K₁, X₁ᶜ MUST contain a K₃,₅!
    have hX₂K35 : HasK (F.induce ((X₁ᶜ : Finset V) : Set V)) 3 5 := by
      rcases hX₂bad with hK5' | hK331' | hK35'
      · exact absurd (hasClique_of_induce hK5') hnoK5
      · exact absurd (hasCliqueJoin_of_induce hK331') hnoK331
      · exact hK35'
    obtain ⟨A₂', B₂', hA₂'3, hB₂'5, hdisj2', h2'adj⟩ := hX₂K35
    let A₂ : Finset V := A₂'.image Subtype.val
    let B₂ : Finset V := B₂'.image Subtype.val
    have hA₂3 : A₂.card = 3 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hA₂'3]
    have hB₂5 : B₂.card = 5 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hB₂'5]
    have hA₂sub : A₂ ⊆ X₁ᶜ := fun x hx => by
      rw [Finset.mem_image] at hx; obtain ⟨u, _, rfl⟩ := hx; exact u.property
    have hB₂sub : B₂ ⊆ X₁ᶜ := fun x hx => by
      rw [Finset.mem_image] at hx; obtain ⟨u, _, rfl⟩ := hx; exact u.property
    have h2adj : ∀ u ∈ A₂, ∀ v ∈ B₂, F.Adj u v := by
      intro u hu v hv
      rw [Finset.mem_image] at hu hv
      obtain ⟨a, ha, rfl⟩ := hu; obtain ⟨b, hb, rfl⟩ := hv
      exact h2'adj a ha b hb
    -- Pick a₁ ∈ A₁ and a₂ ∈ A₂!
    obtain ⟨a₁, ha₁⟩ := Finset.card_pos.mp (by omega : 0 < A₁.card)
    obtain ⟨a₂, ha₂⟩ := Finset.card_pos.mp (by omega : 0 < A₂.card)
    have hNa₁ : F.neighborFinset a₁ = B₁ :=
      neighborFinset_eq_of_subset_card_five (hcdeg a₁) hB₁5 (h1adj a₁ ha₁)
    have hNa₂ : F.neighborFinset a₂ = B₂ :=
      neighborFinset_eq_of_subset_card_five (hcdeg a₂) hB₂5 (h2adj a₂ ha₂)
    have hdisjB12 : Disjoint B₁ B₂ :=
      Disjoint.mono (Finset.subset_union_right (s₁ := A₁)) hB₂sub disjoint_compl_right
    have ha₁a₂_ne : a₁ ≠ a₂ := fun h => by
      subst h; exact (Finset.mem_compl.mp (hA₂sub ha₂)) (Finset.mem_union_left B₁ ha₁)
    have hnaF : ¬ F.Adj a₁ a₂ := fun hadj => by
      have ha₂B₁ : a₂ ∈ B₁ := hNa₁ ▸ (SimpleGraph.mem_neighborFinset F a₁ a₂).mpr hadj
      exact (Finset.mem_compl.mp (hA₂sub ha₂)) (Finset.mem_union_right A₁ ha₂B₁)
    have hGadj : G.Adj a₁ a₂ := by
      by_contra hna; exact hnaF ⟨ha₁a₂_ne, hna⟩
    -- Now show G' = G.deleteEdges {s(a₁, a₂)} has the EXACT same good/bad 8-sets as G!
    let G' := G.deleteEdges {s(a₁, a₂)}
    have hG'c : G'ᶜ = F ⊔ SimpleGraph.edge a₁ a₂ := compl_deleteEdges_singleton hGadj
    have hsame : ∀ S : Finset V, S.card = 8 →
        (HasPM (G.induce (S : Set V)) ↔ HasPM (G'.induce (S : Set V))) := by
      intro S hS8
      constructor
      · intro hGpm
        by_contra hG'no
        -- Since G' ≤ G, we know G.induce S has PM (so F[S] has no bad8!), while G'.induce S has no PM.
        have hFgoodS : ¬ HasBad8 (F.induce (S : Set V)) := by
          intro hb; exact not_hasPM_eight_of_hasBad8 hS8 hb hGpm
        rw [hasPM_induce_iff_compl, hG'c] at hG'no
        have hdeg6 : ∀ x : (S : Set V), ((F ⊔ SimpleGraph.edge a₁ a₂).induce (S : Set V)).degree x ≤ 6 := fun x =>
          le_trans (degree_induce_le (F ⊔ SimpleGraph.edge a₁ a₂) S x)
            (le_trans (degree_sup_edge_le F a₁ a₂ x.val) (by have := hcdeg x.val; split_ifs <;> omega))
        have hclass := not_hasPM_eight_of_compl_le_six (by rw [card_coe_finset_set, hS8]) hdeg6 hG'no
        -- Show none of the 5 patterns in F ⊔ edge a₁ a₂ can occur!
        -- Helper: common neighbors of a₁ and a₂ in F is empty (B₁ ∩ B₂ = ∅)!
        have hno_cn : ∀ w : V, F.Adj a₁ w → F.Adj a₂ w → False := fun w h1 h2 =>
          Finset.disjoint_left.mp hdisjB12
            (hNa₁ ▸ (SimpleGraph.mem_neighborFinset F a₁ w).mpr h1)
            (hNa₂ ▸ (SimpleGraph.mem_neighborFinset F a₂ w).mpr h2)
        have hno_edge_of_disj : ∀ x y : V, (F ⊔ SimpleGraph.edge a₁ a₂).Adj x y →
            ¬ (x = a₁ ∧ y = a₂) → ¬ (x = a₂ ∧ y = a₁) → F.Adj x y := by
          intro x y h h1 h2
          rw [sup_edge_adj_iff] at h
          rcases h with hF | ⟨h' | h', _⟩
          · exact hF
          · exact absurd h' h1
          · exact absurd h' h2
        -- Check each of the 5 patterns:
        rcases hclass with ⟨K, hK5, hKcl⟩ | ⟨A, B, hA3, hB3, hdisj, hcl, hadj⟩ |
            ⟨A, B, hA3, hB5, hdisj, hadj⟩ | ⟨A, B, hA2, hB5, hdisj, hcl, hadj⟩ |
            ⟨u, A, B, huA, huB, hA3, hB3, hdisj, h1, h2, h3⟩
        · -- Pattern 1: K₅ in F ⊔ edge a₁ a₂ => a₁, a₂ ∈ K and 3 common neighbors in F, impossible!
          let KV := K.image Subtype.val
          have hKV5 : KV.card = 5 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hK5]
          have h12 : a₁ ∈ KV ∧ a₂ ∈ KV := by
            by_contra hnot
            apply hnoK5
            refine ⟨KV, hKV5, fun x hx y hy hxy => ?_⟩
            rw [Finset.mem_coe, Finset.mem_image] at hx hy
            obtain ⟨p, hp, rfl⟩ := hx; obtain ⟨q, hq, rfl⟩ := hy
            exact hno_edge_of_disj p.val q.val (hKcl hp hq (fun h => hxy (congrArg Subtype.val h)))
              (fun ⟨h1, h2⟩ => hnot ⟨h1 ▸ Finset.mem_image_of_mem Subtype.val hp, h2 ▸ Finset.mem_image_of_mem Subtype.val hq⟩)
              (fun ⟨h1, h2⟩ => hnot ⟨h2 ▸ Finset.mem_image_of_mem Subtype.val hq, h1 ▸ Finset.mem_image_of_mem Subtype.val hp⟩)
          have hpos : 0 < ((KV.erase a₁).erase a₂).card := by
            rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨ha₁a₂_ne.symm, h12.2⟩),
              Finset.card_erase_of_mem h12.1, hKV5]; omega
          obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
          have hw2 : w ≠ a₂ := (Finset.mem_erase.mp hw).1
          have hw1 : w ≠ a₁ := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hw)).1
          have hwKV : w ∈ KV := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hw)
          have h1w : F.Adj a₁ w := by
            rw [Finset.mem_image] at hwKV
            have ha1 := h12.1; rw [Finset.mem_image] at ha1
            obtain ⟨pw, hpw, rfl⟩ := hwKV; obtain ⟨p1, hp1, hp1e⟩ := ha1
            have hne_p : p1 ≠ pw := fun h => hw1 (hp1e ▸ congrArg Subtype.val h).symm
            have hadj_p : (F ⊔ SimpleGraph.edge a₁ a₂).Adj p1.val pw.val := hKcl hp1 hpw hne_p
            rw [hp1e] at hadj_p
            exact hno_edge_of_disj a₁ pw.val hadj_p (fun h => hw2 h.2) (fun h => ha₁a₂_ne h.1)
          have h2w : F.Adj a₂ w := by
            rw [Finset.mem_image] at hwKV
            have ha2 := h12.2; rw [Finset.mem_image] at ha2
            obtain ⟨pw, hpw, rfl⟩ := hwKV; obtain ⟨p2, hp2, hp2e⟩ := ha2
            have hne_p : p2 ≠ pw := fun h => hw2 (hp2e ▸ congrArg Subtype.val h).symm
            have hadj_p : (F ⊔ SimpleGraph.edge a₁ a₂).Adj p2.val pw.val := hKcl hp2 hpw hne_p
            rw [hp2e] at hadj_p
            exact hno_edge_of_disj a₂ pw.val hadj_p (fun h => ha₁a₂_ne.symm h.1) (fun h => hw1 h.2)
          exact hno_cn w h1w h2w
        · -- Pattern 2: K₃ ∨ 3K₁ in F ⊔ edge a₁ a₂ => a₁ and a₂ have a common neighbor in F!
          let AV := A.image Subtype.val; let BV := B.image Subtype.val
          have hAV3 : AV.card = 3 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hA3]
          have hBV3 : BV.card = 3 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hB3]
          have hdisjV : Disjoint AV BV := by
            rw [Finset.disjoint_left]; intro x hx hy
            rw [Finset.mem_image] at hx hy
            obtain ⟨p, hp, rfl⟩ := hx; obtain ⟨q, hq, he⟩ := hy
            exact Finset.disjoint_left.mp hdisj hp ((Subtype.ext he) ▸ hq)
          have hAcl' : ∀ x ∈ AV, ∀ y ∈ AV, x ≠ y → (F ⊔ SimpleGraph.edge a₁ a₂).Adj x y := fun x hx y hy hxy => by
            rw [Finset.mem_image] at hx hy; obtain ⟨p, hp, rfl⟩ := hx; obtain ⟨q, hq, rfl⟩ := hy
            exact hcl hp hq (fun h => hxy (congrArg Subtype.val h))
          have hAB' : ∀ x ∈ AV, ∀ y ∈ BV, (F ⊔ SimpleGraph.edge a₁ a₂).Adj x y := fun x hx y hy => by
            rw [Finset.mem_image] at hx hy; obtain ⟨p, hp, rfl⟩ := hx; obtain ⟨q, hq, rfl⟩ := hy
            exact hadj p hp q hq
          by_cases h11 : a₁ ∈ AV ∧ a₂ ∈ AV
          · obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < BV.card)
            have hb1 : b ≠ a₁ := fun h => Finset.disjoint_right.mp hdisjV hb (h ▸ h11.1)
            have hb2 : b ≠ a₂ := fun h => Finset.disjoint_right.mp hdisjV hb (h ▸ h11.2)
            exact hno_cn b
              (hno_edge_of_disj a₁ b (hAB' a₁ h11.1 b hb) (fun h => hb2 h.2) (fun h => ha₁a₂_ne h.1))
              (hno_edge_of_disj a₂ b (hAB' a₂ h11.2 b hb) (fun h => ha₁a₂_ne.symm h.1) (fun h => hb1 h.2))
          · by_cases h12 : (a₁ ∈ AV ∧ a₂ ∈ BV) ∨ (a₂ ∈ AV ∧ a₁ ∈ BV)
            · rcases h12 with ⟨h1A, h2B⟩ | ⟨h2A, h1B⟩
              · obtain ⟨w, hw⟩ := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem h1A, hAV3]; omega : 0 < (AV.erase a₁).card)
                have hw1 : w ≠ a₁ := (Finset.mem_erase.mp hw).1
                have hwA : w ∈ AV := Finset.mem_of_mem_erase hw
                have hw2 : w ≠ a₂ := fun h => Finset.disjoint_left.mp hdisjV hwA (h ▸ h2B)
                exact hno_cn w
                  (hno_edge_of_disj a₁ w (hAcl' a₁ h1A w hwA hw1.symm) (fun h => hw2 h.2) (fun h => ha₁a₂_ne h.1))
                  (hno_edge_of_disj w a₂ (hAB' w hwA a₂ h2B) (fun h => hw1 h.1) (fun h => hw2 h.1)).symm
              · obtain ⟨w, hw⟩ := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem h2A, hAV3]; omega : 0 < (AV.erase a₂).card)
                have hw2 : w ≠ a₂ := (Finset.mem_erase.mp hw).1
                have hwA : w ∈ AV := Finset.mem_of_mem_erase hw
                have hw1 : w ≠ a₁ := fun h => Finset.disjoint_left.mp hdisjV hwA (h ▸ h1B)
                exact hno_cn w
                  (hno_edge_of_disj w a₁ (hAB' w hwA a₁ h1B) (fun h => hw1 h.1) (fun h => hw2 h.1)).symm
                  (hno_edge_of_disj a₂ w (hAcl' a₂ h2A w hwA hw2.symm) (fun h => ha₁a₂_ne.symm h.1) (fun h => hw1 h.2))
            · apply hnoK331
              refine ⟨AV, BV, hAV3, hBV3, hdisjV, ?_, ?_⟩
              · intro x hx y hy hxy
                exact hno_edge_of_disj x y (hAcl' x hx y hy hxy)
                  (fun ⟨h1, h2⟩ => h11 ⟨h1 ▸ hx, h2 ▸ hy⟩)
                  (fun ⟨h1, h2⟩ => h11 ⟨h2 ▸ hy, h1 ▸ hx⟩)
              · intro x hx y hy
                exact hno_edge_of_disj x y (hAB' x hx y hy)
                  (fun ⟨h1, h2⟩ => h12 (Or.inl ⟨h1 ▸ hx, h2 ▸ hy⟩))
                  (fun ⟨h1, h2⟩ => h12 (Or.inr ⟨h1 ▸ hx, h2 ▸ hy⟩))
        · -- Pattern 3: K₃,₅ in F ⊔ edge a₁ a₂!
          let AV := A.image Subtype.val; let BV := B.image Subtype.val
          have hAV3 : AV.card = 3 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hA3]
          have hBV5 : BV.card = 5 := by rw [Finset.card_image_of_injective _ Subtype.val_injective, hB5]
          have hdisjV : Disjoint AV BV := by
            rw [Finset.disjoint_left]; intro x hx hy
            rw [Finset.mem_image] at hx hy
            obtain ⟨p, hp, rfl⟩ := hx; obtain ⟨q, hq, he⟩ := hy
            exact Finset.disjoint_left.mp hdisj hp ((Subtype.ext he) ▸ hq)
          have hAB' : ∀ x ∈ AV, ∀ y ∈ BV, (F ⊔ SimpleGraph.edge a₁ a₂).Adj x y := fun x hx y hy => by
            rw [Finset.mem_image] at hx hy; obtain ⟨p, hp, rfl⟩ := hx; obtain ⟨q, hq, rfl⟩ := hy
            exact hadj p hp q hq
          by_cases h12 : a₁ ∈ AV ∧ a₂ ∈ BV
          · obtain ⟨w, hw⟩ := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem h12.1, hAV3]; omega : 0 < (AV.erase a₁).card)
            have hwa1 : w ≠ a₁ := (Finset.mem_erase.mp hw).1
            have hwAV : w ∈ AV := Finset.mem_of_mem_erase hw
            have hwa2 : w ≠ a₂ := fun h => Finset.disjoint_left.mp hdisjV hwAV (h ▸ h12.2)
            have hwa2_adj : F.Adj w a₂ :=
              hno_edge_of_disj w a₂ (hAB' w hwAV a₂ h12.2) (fun h => hwa1 h.1) (fun h => hwa2 h.1)
            have hwB₂ : w ∈ B₂ := hNa₂ ▸ (SimpleGraph.mem_neighborFinset F a₂ w).mpr hwa2_adj.symm
            have hBVsubB1 : BV.erase a₂ ⊆ B₁ := fun z hz => by
              have hza2 : z ≠ a₂ := (Finset.mem_erase.mp hz).1
              have hzBV : z ∈ BV := Finset.mem_of_mem_erase hz
              have h1z : F.Adj a₁ z :=
                hno_edge_of_disj a₁ z (hAB' a₁ h12.1 z hzBV) (fun h => hza2 h.2) (fun h => ha₁a₂_ne h.1)
              exact hNa₁ ▸ (SimpleGraph.mem_neighborFinset F a₁ z).mpr h1z
            have hdisjA2B1 : Disjoint A₂ (BV.erase a₂) :=
              Disjoint.mono hA₂sub (Finset.Subset.trans hBVsubB1 Finset.subset_union_right) disjoint_compl_left
            have hsub7 : A₂ ∪ BV.erase a₂ ⊆ F.neighborFinset w := by
              intro z hz; rw [Finset.mem_union] at hz; rw [SimpleGraph.mem_neighborFinset]
              rcases hz with hzA₂ | hzBV'
              · exact (h2adj z hzA₂ w hwB₂).symm
              · exact hno_edge_of_disj w z (hAB' w hwAV z (Finset.mem_of_mem_erase hzBV'))
                  (fun h => hwa1 h.1) (fun h => hwa2 h.1)
            have hc := Finset.card_le_card hsub7
            rw [Finset.card_union_of_disjoint hdisjA2B1, hA₂3, Finset.card_erase_of_mem h12.2, hBV5,
              SimpleGraph.card_neighborFinset_eq_degree] at hc
            have := hcdeg w; omega
          · by_cases h21 : a₂ ∈ AV ∧ a₁ ∈ BV
            · obtain ⟨w, hw⟩ := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem h21.1, hAV3]; omega : 0 < (AV.erase a₂).card)
              have hwa2 : w ≠ a₂ := (Finset.mem_erase.mp hw).1
              have hwAV : w ∈ AV := Finset.mem_of_mem_erase hw
              have hwa1 : w ≠ a₁ := fun h => Finset.disjoint_left.mp hdisjV hwAV (h ▸ h21.2)
              have hwa1_adj : F.Adj w a₁ :=
                hno_edge_of_disj w a₁ (hAB' w hwAV a₁ h21.2) (fun h => hwa1 h.1) (fun h => hwa2 h.1)
              have hwB₁ : w ∈ B₁ := hNa₁ ▸ (SimpleGraph.mem_neighborFinset F a₁ w).mpr hwa1_adj.symm
              have hBVsubB2 : BV.erase a₁ ⊆ B₂ := fun z hz => by
                have hza1 : z ≠ a₁ := (Finset.mem_erase.mp hz).1
                have hzBV : z ∈ BV := Finset.mem_of_mem_erase hz
                have h2z : F.Adj a₂ z :=
                  hno_edge_of_disj a₂ z (hAB' a₂ h21.1 z hzBV) (fun h => ha₁a₂_ne.symm h.1) (fun h => hza1 h.2)
                exact hNa₂ ▸ (SimpleGraph.mem_neighborFinset F a₂ z).mpr h2z
              have hdisjA1B2 : Disjoint A₁ (BV.erase a₁) :=
                Disjoint.mono Finset.subset_union_left (Finset.Subset.trans hBVsubB2 hB₂sub) disjoint_compl_right
              have hsub7 : A₁ ∪ BV.erase a₁ ⊆ F.neighborFinset w := by
                intro z hz; rw [Finset.mem_union] at hz; rw [SimpleGraph.mem_neighborFinset]
                rcases hz with hzA₁ | hzBV'
                · exact (h1adj z hzA₁ w hwB₁).symm
                · exact hno_edge_of_disj w z (hAB' w hwAV z (Finset.mem_of_mem_erase hzBV'))
                    (fun h => hwa1 h.1) (fun h => hwa2 h.1)
              have hc := Finset.card_le_card hsub7
              rw [Finset.card_union_of_disjoint hdisjA1B2, hA₁3, Finset.card_erase_of_mem h21.2, hBV5,
                SimpleGraph.card_neighborFinset_eq_degree] at hc
              have := hcdeg w; omega
            · -- Neither (a₁∈AV, a₂∈BV) nor (a₂∈AV, a₁∈BV), so A, B form K₃,₅ in F.induce S, contradicting hFgoodS!
              apply hFgoodS
              refine Or.inr (Or.inr ⟨A, B, hA3, hB5, hdisj, fun p hp q hq => ?_⟩)
              exact hno_edge_of_disj p.val q.val (hadj p hp q hq)
                (fun ⟨h1, h2⟩ => h12 ⟨h1 ▸ Finset.mem_image_of_mem Subtype.val hp, h2 ▸ Finset.mem_image_of_mem Subtype.val hq⟩)
                (fun ⟨h1, h2⟩ => h21 ⟨h1 ▸ Finset.mem_image_of_mem Subtype.val hp, h2 ▸ Finset.mem_image_of_mem Subtype.val hq⟩)
        · -- Pattern 4: K₂ ∨ 5K₁ => both vertices of A have degree 6 in F ⊔ edge a₁ a₂, so A = {a₁, a₂},
          -- hence a₁ and a₂ share 5 common neighbors in F, contradicting hno_cn!
          obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hA2
          have hdeg6p : 6 ≤ (F ⊔ SimpleGraph.edge a₁ a₂).degree p.val := by
            have hsub : insert q.val (B.image Subtype.val) ⊆ (F ⊔ SimpleGraph.edge a₁ a₂).neighborFinset p.val := by
              intro w hw; rw [Finset.mem_insert] at hw; rw [SimpleGraph.mem_neighborFinset]
              rcases hw with rfl | hwB
              · exact hcl (by simp) (by simp) hpq
              · rw [Finset.mem_image] at hwB; obtain ⟨b, hb, rfl⟩ := hwB
                exact hadj p (by simp) b hb
            have hqnotB : q.val ∉ B.image Subtype.val := fun h => by
              rw [Finset.mem_image] at h; obtain ⟨b, hb, he⟩ := h
              exact Finset.disjoint_left.mp hdisj (by simp : q ∈ ({p, q} : Finset _)) ((Subtype.ext he) ▸ hb)
            have hc := Finset.card_le_card hsub
            rw [Finset.card_insert_of_notMem hqnotB, Finset.card_image_of_injective _ Subtype.val_injective,
              hB5, SimpleGraph.card_neighborFinset_eq_degree] at hc
            exact hc
          have hdeg6q : 6 ≤ (F ⊔ SimpleGraph.edge a₁ a₂).degree q.val := by
            have hsub : insert p.val (B.image Subtype.val) ⊆ (F ⊔ SimpleGraph.edge a₁ a₂).neighborFinset q.val := by
              intro w hw; rw [Finset.mem_insert] at hw; rw [SimpleGraph.mem_neighborFinset]
              rcases hw with rfl | hwB
              · exact hcl (by simp) (by simp) hpq.symm
              · rw [Finset.mem_image] at hwB; obtain ⟨b, hb, rfl⟩ := hwB
                exact hadj q (by simp) b hb
            have hpnotB : p.val ∉ B.image Subtype.val := fun h => by
              rw [Finset.mem_image] at h; obtain ⟨b, hb, he⟩ := h
              exact Finset.disjoint_left.mp hdisj (by simp : p ∈ ({p, q} : Finset _)) ((Subtype.ext he) ▸ hb)
            have hc := Finset.card_le_card hsub
            rw [Finset.card_insert_of_notMem hpnotB, Finset.card_image_of_injective _ Subtype.val_injective,
              hB5, SimpleGraph.card_neighborFinset_eq_degree] at hc
            exact hc
          have hp12 : p.val = a₁ ∨ p.val = a₂ := by
            by_contra h; have h1 := degree_sup_edge_le F a₁ a₂ p.val; simp only [h, ↓reduceIte] at h1
            have := hcdeg p.val; omega
          have hq12 : q.val = a₁ ∨ q.val = a₂ := by
            by_contra h; have h1 := degree_sup_edge_le F a₁ a₂ q.val; simp only [h, ↓reduceIte] at h1
            have := hcdeg q.val; omega
          have hpq_val : p.val ≠ q.val := fun h => hpq (Subtype.ext h)
          obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < B.card)
          have hbp : b.val ≠ p.val := fun h => Finset.disjoint_left.mp hdisj (by simp : p ∈ ({p, q} : Finset _)) ((Subtype.ext h) ▸ hb)
          have hbq : b.val ≠ q.val := fun h => Finset.disjoint_left.mp hdisj (by simp : q ∈ ({p, q} : Finset _)) ((Subtype.ext h) ▸ hb)
          rcases hp12 with hp' | hp' <;> rcases hq12 with hq' | hq'
          · exact hpq_val (hp'.trans hq'.symm)
          · exact hno_cn b.val
              (hno_edge_of_disj a₁ b.val (hp' ▸ hadj p (by simp) b hb) (fun h => hbq (h.2.trans hq'.symm)) (fun h => ha₁a₂_ne h.1))
              (hno_edge_of_disj a₂ b.val (hq' ▸ hadj q (by simp) b hb) (fun h => ha₁a₂_ne.symm h.1) (fun h => hbp (h.2.trans hp'.symm)))
          · exact hno_cn b.val
              (hno_edge_of_disj a₁ b.val (hq' ▸ hadj q (by simp) b hb) (fun h => hbp (h.2.trans hp'.symm)) (fun h => ha₁a₂_ne h.1))
              (hno_edge_of_disj a₂ b.val (hp' ▸ hadj p (by simp) b hb) (fun h => ha₁a₂_ne.symm h.1) (fun h => hbq (h.2.trans hq'.symm)))
          · exact hpq_val (hp'.trans hq'.symm)
        · -- Pattern 5: K₁ ∨ K₃,₃ => u has degree 6 in F ⊔ edge a₁ a₂, so u ∈ {a₁, a₂}, and the OTHER of {a₁, a₂}
          -- lies in A ∪ B and is adjacent to 3 vertices in the opposite part (all neighbors of u in F), contradicting hno_cn!
          have hdeg6u : 6 ≤ (F ⊔ SimpleGraph.edge a₁ a₂).degree u.val := by
            have hsub : (A ∪ B).image Subtype.val ⊆ (F ⊔ SimpleGraph.edge a₁ a₂).neighborFinset u.val := by
              intro w hw; rw [Finset.mem_image] at hw; obtain ⟨z, hz, rfl⟩ := hw
              rw [Finset.mem_union] at hz; rw [SimpleGraph.mem_neighborFinset]
              rcases hz with hzA | hzB
              · exact h1 z hzA
              · exact h2 z hzB
            have hc := Finset.card_le_card hsub
            rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_union_of_disjoint hdisj,
              hA3, hB3, SimpleGraph.card_neighborFinset_eq_degree] at hc
            exact hc
          have hu12 : u.val = a₁ ∨ u.val = a₂ := by
            by_contra h; have h1 := degree_sup_edge_le F a₁ a₂ u.val; simp only [h, ↓reduceIte] at h1
            have := hcdeg u.val; omega
          -- The other vertex (say v) MUST lie in A ∪ B (else u has 6 neighbors in F, impossible!)
          have hv_in : ∀ (u₀ v₀ : V), u.val = u₀ → ((u₀ = a₁ ∧ v₀ = a₂) ∨ (u₀ = a₂ ∧ v₀ = a₁)) →
              ∃ z ∈ A ∪ B, z.val = v₀ := by
            intro u₀ v₀ hu0 huv0
            by_contra hno
            push Not at hno
            have hsub6 : (A ∪ B).image Subtype.val ⊆ F.neighborFinset u₀ := by
              intro w hw; rw [Finset.mem_image] at hw; obtain ⟨z, hz, rfl⟩ := hw
              rw [SimpleGraph.mem_neighborFinset]
              have hadj_uz : (F ⊔ SimpleGraph.edge a₁ a₂).Adj u₀ z.val := by
                rw [Finset.mem_union] at hz; rw [← hu0]
                rcases hz with hzA | hzB
                · exact h1 z hzA
                · exact h2 z hzB
              have hne_zv : z.val ≠ v₀ := hno z hz
              rcases huv0 with ⟨hu', hv'⟩ | ⟨hu', hv'⟩
              · exact hno_edge_of_disj u₀ z.val hadj_uz
                  (fun h => hne_zv (h.2.trans hv'.symm)) (fun h => ha₁a₂_ne (hu'.symm.trans h.1))
              · exact hno_edge_of_disj u₀ z.val hadj_uz
                  (fun h => ha₁a₂_ne.symm (hu'.symm.trans h.1)) (fun h => hne_zv (h.2.trans hv'.symm))
            have hc := Finset.card_le_card hsub6
            rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_union_of_disjoint hdisj,
              hA3, hB3, SimpleGraph.card_neighborFinset_eq_degree] at hc
            have := hcdeg u₀; omega
          have hkill5 : ∀ (u₀ v₀ : V), u.val = u₀ → ((u₀ = a₁ ∧ v₀ = a₂) ∨ (u₀ = a₂ ∧ v₀ = a₁)) → False := by
            intro u₀ v₀ hu0 huv0
            obtain ⟨z, hzAB, hzv0⟩ := hv_in u₀ v₀ hu0 huv0
            have hcn_uv : ∀ w : V, F.Adj u₀ w → F.Adj v₀ w → False := fun w h1' h2' => by
              rcases huv0 with ⟨hu', hv'⟩ | ⟨hu', hv'⟩
              · rw [hu'] at h1'; rw [hv'] at h2'; exact hno_cn w h1' h2'
              · rw [hu'] at h1'; rw [hv'] at h2'; exact hno_cn w h2' h1'
            rw [Finset.mem_union] at hzAB
            rcases hzAB with hzA | hzB
            · obtain ⟨b, hbB⟩ := Finset.card_pos.mp (by omega : 0 < B.card)
              have hbu : b.val ≠ u₀ := fun h => huB (Subtype.ext (hu0.trans h.symm) ▸ hbB)
              have hbv : b.val ≠ v₀ := fun h => Finset.disjoint_left.mp hdisj hzA (Subtype.ext (hzv0.trans h.symm) ▸ hbB)
              have hub_sup : (F ⊔ SimpleGraph.edge a₁ a₂).Adj u₀ b.val := by rw [← hu0]; exact h2 b hbB
              have hvb_sup : (F ⊔ SimpleGraph.edge a₁ a₂).Adj v₀ b.val := by rw [← hzv0]; exact h3 z hzA b hbB
              have hub : F.Adj u₀ b.val := by
                rcases huv0 with ⟨hu', hv'⟩ | ⟨hu', hv'⟩
                · exact hno_edge_of_disj u₀ b.val hub_sup (fun h => hbv (h.2.trans hv'.symm)) (fun h => ha₁a₂_ne (hu'.symm.trans h.1))
                · exact hno_edge_of_disj u₀ b.val hub_sup (fun h => ha₁a₂_ne.symm (hu'.symm.trans h.1)) (fun h => hbv (h.2.trans hv'.symm))
              have hvb : F.Adj v₀ b.val := by
                rcases huv0 with ⟨hu', hv'⟩ | ⟨hu', hv'⟩
                · exact hno_edge_of_disj v₀ b.val hvb_sup (fun h => ha₁a₂_ne.symm (hv'.symm.trans h.1)) (fun h => hbu (h.2.trans hu'.symm))
                · exact hno_edge_of_disj v₀ b.val hvb_sup (fun h => hbu (h.2.trans hu'.symm)) (fun h => ha₁a₂_ne (hv'.symm.trans h.1))
              exact hcn_uv b.val hub hvb
            · obtain ⟨a, haA⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
              have hau : a.val ≠ u₀ := fun h => huA (Subtype.ext (hu0.trans h.symm) ▸ haA)
              have hav : a.val ≠ v₀ := fun h => Finset.disjoint_right.mp hdisj hzB (Subtype.ext (hzv0.trans h.symm) ▸ haA)
              have hua_sup : (F ⊔ SimpleGraph.edge a₁ a₂).Adj u₀ a.val := by rw [← hu0]; exact h1 a haA
              have hva_sup : (F ⊔ SimpleGraph.edge a₁ a₂).Adj v₀ a.val := by rw [← hzv0]; exact (h3 a haA z hzB).symm
              have hua : F.Adj u₀ a.val := by
                rcases huv0 with ⟨hu', hv'⟩ | ⟨hu', hv'⟩
                · exact hno_edge_of_disj u₀ a.val hua_sup (fun h => hav (h.2.trans hv'.symm)) (fun h => ha₁a₂_ne (hu'.symm.trans h.1))
                · exact hno_edge_of_disj u₀ a.val hua_sup (fun h => ha₁a₂_ne.symm (hu'.symm.trans h.1)) (fun h => hav (h.2.trans hv'.symm))
              have hva : F.Adj v₀ a.val := by
                rcases huv0 with ⟨hu', hv'⟩ | ⟨hu', hv'⟩
                · exact hno_edge_of_disj v₀ a.val hva_sup (fun h => ha₁a₂_ne.symm (hv'.symm.trans h.1)) (fun h => hau (h.2.trans hu'.symm))
                · exact hno_edge_of_disj v₀ a.val hva_sup (fun h => hau (h.2.trans hu'.symm)) (fun h => ha₁a₂_ne (hv'.symm.trans h.1))
              exact hcn_uv a.val hua hva
          rcases hu12 with hu1 | hu2
          · exact hkill5 a₁ a₂ hu1 (Or.inl ⟨rfl, rfl⟩)
          · exact hkill5 a₂ a₁ hu2 (Or.inr ⟨rfl, rfl⟩)
      · -- Reverse direction: G' ≤ G, so HasPM (G'.induce S) → HasPM (G.induce S)!
        rintro ⟨P, hPM, hPspan⟩
        have hle : G'.induce (S : Set V) ≤ G.induce (S : Set V) :=
          fun _ _ h => h.1
        refine ⟨P.map (SimpleGraph.Hom.ofLE hle), hPM.map_ofLE hle, ?_⟩
        intro v
        exact ⟨v, hPspan v, rfl⟩
    exact hmin.2 s(a₁, a₂) hGadj (isKExtendable_of_same_pm hmin.1 hsame (by omega))

end Closure16

end LouYuK4
