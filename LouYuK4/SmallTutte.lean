import LouYuK4.Defs
import Mathlib.Tactic.IntervalCases

/-!
# Small-order Tutte classifications (orders 4, 6, and 8)

We package Mathlib's `SimpleGraph.tutte` into an explicit odd-component partition lemma
(`exists_tutte_odd_partition`), then deduce:
- `not_hasPM_four` (Gan–Huang Lemma 3.4),
- `hasPM_six_of_deg_le_two_except_two` (Gan–Huang Lemma 5.2),
- `not_hasPM_six_of_compl_le_three` (Gan–Huang Lemma 5.4),
- `hasPM_eight_of_compl_le_three` (Dirac / Tutte on 8 vertices with `Δ(X) ≤ 3`),
- `not_hasPM_eight_of_compl_le_six` (new 8-vertex classification for `Δ(X) ≤ 6`),
- `not_hasPM_eight_of_compl_le_five` (corollary for `Δ(X) ≤ 5`).
-/

open SimpleGraph Finset

namespace LouYuK4

section StructuralPredicates

variable {V : Type*}

/-- `X` contains a clique of size `r`. -/
def HasClique (X : SimpleGraph V) (r : ℕ) : Prop :=
  ∃ Q : Finset V, Q.card = r ∧ X.IsClique (Q : Set V)

/-- `X` contains a complete bipartite subgraph `K_{a, b}` (not necessarily induced). -/
def HasK (X : SimpleGraph V) (a b : ℕ) : Prop :=
  ∃ A B : Finset V, A.card = a ∧ B.card = b ∧ Disjoint A B ∧
    ∀ u ∈ A, ∀ v ∈ B, X.Adj u v

/-- `X` contains `K_a ∨ bK_1`: a clique `A` of size `a` completely joined to a disjoint
set `B` of size `b`. -/
def HasCliqueJoin (X : SimpleGraph V) (a b : ℕ) : Prop :=
  ∃ A B : Finset V, A.card = a ∧ B.card = b ∧ Disjoint A B ∧
    X.IsClique (A : Set V) ∧ ∀ u ∈ A, ∀ v ∈ B, X.Adj u v

/-- `X` contains `K_1 ∨ K_{3,3}`: a vertex `u` adjacent to all vertices of a `K_{3,3}`
disjoint from `{u}`. -/
def HasK1JoinK33 (X : SimpleGraph V) : Prop :=
  ∃ (u : V) (A B : Finset V), u ∉ A ∧ u ∉ B ∧ A.card = 3 ∧ B.card = 3 ∧ Disjoint A B ∧
    (∀ x ∈ A, X.Adj u x) ∧ (∀ y ∈ B, X.Adj u y) ∧ (∀ x ∈ A, ∀ y ∈ B, X.Adj x y)

lemma HasClique.mono {X Y : SimpleGraph V} (h : X ≤ Y) {r : ℕ} (hx : HasClique X r) :
    HasClique Y r := by
  obtain ⟨Q, hQ, hcl⟩ := hx
  exact ⟨Q, hQ, hcl.mono h⟩

lemma HasK.mono {X Y : SimpleGraph V} (h : X ≤ Y) {a b : ℕ} (hx : HasK X a b) :
    HasK Y a b := by
  obtain ⟨A, B, hA, hB, hdisj, hadj⟩ := hx
  exact ⟨A, B, hA, hB, hdisj, fun u hu v hv => h (hadj u hu v hv)⟩

lemma HasCliqueJoin.mono {X Y : SimpleGraph V} (h : X ≤ Y) {a b : ℕ}
    (hx : HasCliqueJoin X a b) : HasCliqueJoin Y a b := by
  obtain ⟨A, B, hA, hB, hdisj, hcl, hadj⟩ := hx
  exact ⟨A, B, hA, hB, hdisj, hcl.mono h, fun u hu v hv => h (hadj u hu v hv)⟩

lemma HasK1JoinK33.mono {X Y : SimpleGraph V} (h : X ≤ Y) (hx : HasK1JoinK33 X) :
    HasK1JoinK33 Y := by
  obtain ⟨u, A, B, huA, huB, hA, hB, hdisj, h1, h2, h3⟩ := hx
  exact ⟨u, A, B, huA, huB, hA, hB, hdisj,
    fun x hx => h (h1 x hx), fun y hy => h (h2 y hy), fun x hx y hy => h (h3 x hx y hy)⟩

end StructuralPredicates

section TutteBridge

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Clean Finset form of Tutte's theorem for a graph `H` on an even number of vertices with
no perfect matching: there exist a barrier `S : Finset V` and a family `C : Finset (Finset V)`
of pairwise-disjoint odd subsets of `Sᶜ` with `S.card + 2 ≤ C.card` such that in `Hᶜ`,
every vertex of `c ∈ C` is adjacent to every vertex of `Sᶜ \ c`. -/
theorem exists_tutte_odd_partition {H : SimpleGraph V}
    (heven : Even (Fintype.card V)) (hno : ¬ HasPM H) :
    ∃ (S : Finset V) (C : Finset (Finset V)),
      S.card + 2 ≤ C.card ∧
      (∀ c ∈ C, Odd c.card) ∧
      (∀ c ∈ C, Disjoint c S) ∧
      (C : Set (Finset V)).PairwiseDisjoint id ∧
      (∑ c ∈ C, c.card) + S.card ≤ Fintype.card V ∧
      ∀ c ∈ C, ∀ v ∈ c, ∀ w : V, w ∉ S → w ∉ c → Hᶜ.Adj v w := by
  classical
  have hviol : ∃ u : Set V, H.IsTutteViolator u := by
    by_contra h
    push Not at h
    exact hno ((SimpleGraph.tutte (G := H)).mpr h)
  obtain ⟨u, hu⟩ := hviol
  let Gdel := ((⊤ : H.Subgraph).deleteVerts u).coe
  let S : Finset V := u.toFinset
  -- Project each odd component of `Gdel` to a Finset of `V`
  let proj : Gdel.ConnectedComponent → Finset V :=
    fun K => (Finset.univ.filter (fun x : ((⊤ : H.Subgraph).deleteVerts u).verts =>
      Gdel.connectedComponentMk x = K)).image Subtype.val
  let Ofin : Finset Gdel.ConnectedComponent := Gdel.oddComponents.toFinset
  have hproj_inj : Set.InjOn proj (Ofin : Set Gdel.ConnectedComponent) := by
    intro K₁ hK₁ K₂ hK₂ heq
    have hK₁odd : Odd K₁.supp.ncard := by simpa [Ofin, SimpleGraph.oddComponents] using hK₁
    have hne : K₁.supp.Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      rw [hempty, Set.ncard_empty] at hK₁odd
      exact Nat.not_odd_zero hK₁odd
    obtain ⟨x, hx⟩ := hne
    have hx1 : x.val ∈ proj K₁ := by
      simp only [proj, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨x, hx, rfl⟩
    rw [heq] at hx1
    simp only [proj, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx1
    obtain ⟨y, hy, hval⟩ := hx1
    have hxy : y = x := Subtype.ext hval
    rw [hxy] at hy
    have hx' : Gdel.connectedComponentMk x = K₁ := hx
    exact hx'.symm.trans hy
  let C : Finset (Finset V) := Ofin.image proj
  have hCcard : C.card = Gdel.oddComponents.ncard := by
    rw [Finset.card_image_of_injOn hproj_inj, Set.ncard_eq_toFinset_card']
  have hSlt : S.card < C.card := by
    rw [hCcard]
    simpa [S, SimpleGraph.IsTutteViolator, Set.ncard_eq_toFinset_card'] using hu
  -- Parity: `C.card` and `S.card` have the same parity since `card V` is even
  have hpar : Odd C.card ↔ Odd S.card := by
    rw [hCcard, SimpleGraph.odd_ncard_oddComponents]
    have hcard_del : Nat.card ((⊤ : H.Subgraph).deleteVerts u).verts + S.card = Fintype.card V := by
      have hset : ((⊤ : H.Subgraph).deleteVerts u).verts = ((Sᶜ : Finset V) : Set V) := by
        ext x
        simp [S]
      rw [Nat.card_coe_set_eq, hset, Set.ncard_coe_finset, Finset.card_compl]
      exact Nat.sub_add_cancel (Finset.card_le_univ S)
    obtain ⟨m, hm⟩ := heven
    constructor <;> intro ho <;> obtain ⟨r, hr⟩ := ho
    · have : Odd (Fintype.card V - Nat.card ((⊤ : H.Subgraph).deleteVerts u).verts) := by
        refine ⟨m - r - 1, ?_⟩; omega
      have hsub : S.card = Fintype.card V - Nat.card ((⊤ : H.Subgraph).deleteVerts u).verts := by omega
      rwa [hsub]
    · have hsub : Nat.card ((⊤ : H.Subgraph).deleteVerts u).verts = Fintype.card V - S.card := by omega
      rw [hsub]
      refine ⟨m - r - 1, ?_⟩; omega
  have hS2 : S.card + 2 ≤ C.card := by
    by_contra hlt
    have heq : C.card = S.card + 1 := by omega
    rw [heq] at hpar
    rcases Nat.even_or_odd S.card with ⟨k, hk⟩ | ⟨k, hk⟩
    · have h1 : Odd (S.card + 1) := ⟨k, by omega⟩
      have h2 : Odd S.card := hpar.mp h1
      obtain ⟨j, hj⟩ := h2; omega
    · have h1 : Odd S.card := ⟨k, hk⟩
      have h2 : Odd (S.card + 1) := hpar.mpr h1
      obtain ⟨j, hj⟩ := h2; omega
  have hproj_card : ∀ K : Gdel.ConnectedComponent, (proj K).card = K.supp.ncard := by
    intro K
    rw [Finset.card_image_of_injective _ Subtype.val_injective]
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext x
    simp [SimpleGraph.ConnectedComponent.mem_supp_iff]
  have hCodd : ∀ c ∈ C, Odd c.card := by
    intro c hc
    obtain ⟨K, hK, rfl⟩ := Finset.mem_image.mp hc
    rw [hproj_card]
    simpa [Ofin, SimpleGraph.oddComponents] using hK
  have hCdisjS : ∀ c ∈ C, Disjoint c S := by
    intro c hc
    obtain ⟨K, _, rfl⟩ := Finset.mem_image.mp hc
    rw [Finset.disjoint_left]
    intro v hv hvS
    simp only [proj, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨x, _, rfl⟩ := hv
    have hx : x.val ∉ u := by simpa [Subgraph.deleteVerts_verts] using x.property
    exact hx (by simpa [S] using hvS)
  have hCpair : (C : Set (Finset V)).PairwiseDisjoint id := by
    intro c₁ hc₁ c₂ hc₂ hne
    obtain ⟨K₁, hK₁, rfl⟩ := Finset.mem_image.mp hc₁
    obtain ⟨K₂, hK₂, rfl⟩ := Finset.mem_image.mp hc₂
    have hKne : K₁ ≠ K₂ := fun h => hne (congrArg proj h)
    rw [Function.onFun, id, id, Finset.disjoint_left]
    intro v hv₁ hv₂
    simp only [proj, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hv₁ hv₂
    obtain ⟨x₁, hx₁, rfl⟩ := hv₁
    obtain ⟨x₂, hx₂, hval⟩ := hv₂
    have hx : x₂ = x₁ := Subtype.ext hval
    rw [hx] at hx₂
    exact hKne (hx₁.symm.trans hx₂)
  have hsum : (∑ c ∈ C, c.card) + S.card ≤ Fintype.card V := by
    have hbi : (C.biUnion id).card = ∑ c ∈ C, c.card := Finset.card_biUnion hCpair
    have hdisj : Disjoint (C.biUnion id) S := by
      rw [Finset.disjoint_biUnion_left]
      exact hCdisjS
    have hunion : (C.biUnion id ∪ S).card ≤ Fintype.card V := Finset.card_le_univ _
    rw [Finset.card_union_of_disjoint hdisj, hbi] at hunion
    exact hunion
  have hcompl_adj : ∀ c ∈ C, ∀ v ∈ c, ∀ w : V, w ∉ S → w ∉ c → Hᶜ.Adj v w := by
    intro c hc v hv w hwS hwc
    obtain ⟨K, _, rfl⟩ := Finset.mem_image.mp hc
    have hne : v ≠ w := fun h => hwc (h ▸ hv)
    rw [SimpleGraph.compl_adj]
    refine ⟨hne, fun hvw => ?_⟩
    simp only [proj, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    have hw_del : w ∈ ((⊤ : H.Subgraph).deleteVerts u).verts := by
      simp only [Subgraph.deleteVerts_verts, Subgraph.verts_top, Set.mem_sdiff, Set.mem_univ,
        true_and]
      intro hwu
      exact hwS (by simpa [S] using hwu)
    let y : ((⊤ : H.Subgraph).deleteVerts u).verts := ⟨w, hw_del⟩
    have hadj : Gdel.Adj x y := by
      change ((⊤ : H.Subgraph).deleteVerts u).Adj x.val y.val
      simp only [Subgraph.deleteVerts_adj, Subgraph.top_adj, Subgraph.verts_top, Set.mem_univ,
        true_and]
      exact ⟨by simpa using x.property, by simpa using hw_del, hvw⟩
    have hyK : Gdel.connectedComponentMk y = K := by
      rw [← hx]
      exact SimpleGraph.ConnectedComponent.sound hadj.symm.reachable
    apply hwc
    simp only [proj, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨y, hyK, rfl⟩
  exact ⟨S, C, hS2, hCodd, hCdisjS, hCpair, hsum, hcompl_adj⟩

/-- In a Tutte odd partition, if `X = Hᶜ` has `deg_X(v) ≤ d` for all `v ∈ c`, then
`Fintype.card V - S.card - c.card ≤ d`. -/
lemma card_compl_sub_le_deg_of_tutte {X : SimpleGraph V} [DecidableRel X.Adj]
    {S c : Finset V} {v : V} (_hv : v ∈ c) (hdisj : Disjoint c S)
    (hadj : ∀ w : V, w ∉ S → w ∉ c → X.Adj v w) :
    Fintype.card V - S.card - c.card ≤ X.degree v := by
  have hsub : (S ∪ c)ᶜ ⊆ X.neighborFinset v := by
    intro w hw
    rw [Finset.mem_compl, Finset.mem_union, not_or] at hw
    rw [SimpleGraph.mem_neighborFinset]
    exact hadj w hw.1 hw.2
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_compl, Finset.card_union_of_disjoint hdisj.symm, SimpleGraph.card_neighborFinset_eq_degree] at hcard
  omega

omit [Fintype V] in
/-- Pick one element from each of `k` distinct pairwise-disjoint nonempty Finsets to form a
`k`-clique in `X`. -/
lemma hasClique_of_disjoint_sets {X : SimpleGraph V} {D : Finset (Finset V)} {k : ℕ}
    (hk : k ≤ D.card)
    (hne : ∀ c ∈ D, c.Nonempty)
    (hpair : (D : Set (Finset V)).PairwiseDisjoint id)
    (hadj : ∀ c₁ ∈ D, ∀ c₂ ∈ D, c₁ ≠ c₂ → ∀ u ∈ c₁, ∀ v ∈ c₂, X.Adj u v) :
    HasClique X k := by
  classical
  obtain ⟨D', hD'sub, hD'card⟩ := Finset.exists_subset_card_eq hk
  choose f hf using fun c : D' => hne c.val (hD'sub c.property)
  let Q : Finset V := D'.attach.image f
  have hfinj : Function.Injective f := by
    intro c₁ c₂ heq
    by_contra hne'
    have hval : c₁.val ≠ c₂.val := fun h => hne' (Subtype.ext h)
    have hd := hpair (hD'sub c₁.property) (hD'sub c₂.property) hval
    rw [Function.onFun, id, id, Finset.disjoint_left] at hd
    exact hd (hf c₁) (heq ▸ hf c₂)
  refine ⟨Q, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hfinj, Finset.card_attach, hD'card]
  · intro u hu v hv huv
    simp only [Q, Finset.mem_coe, Finset.mem_image, Finset.mem_attach, true_and] at hu hv
    obtain ⟨c₁, rfl⟩ := hu
    obtain ⟨c₂, rfl⟩ := hv
    have hcne : c₁.val ≠ c₂.val := fun h => huv (congrArg f (Subtype.ext h))
    exact hadj c₁.val (hD'sub c₁.property) c₂.val (hD'sub c₂.property) hcne _ (hf c₁) _ (hf c₂)

end TutteBridge

section SmallOrders

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Gan–Huang Lemma 3.4 (necessity direction)**: On 4 vertices, if `Xᶜ` has no PM then `X`
contains a `K₃` or a vertex of degree `3` (a `K_{1,3}`). -/
theorem not_hasPM_four {X : SimpleGraph V} [DecidableRel X.Adj]
    (hV : Fintype.card V = 4) (hno : ¬ HasPM Xᶜ) :
    HasClique X 3 ∨ ∃ v : V, X.degree v = 3 := by
  classical
  have hcompl : (Xᶜ)ᶜ = X := compl_compl X
  obtain ⟨S, C, hS2, hCodd, hCdisj, hCpair, hsum, hadj⟩ :=
    exists_tutte_odd_partition (H := Xᶜ) (by rw [hV]; exact ⟨2, rfl⟩) hno
  rw [hcompl] at hadj
  have hCge : C.card ≤ ∑ c ∈ C, c.card := by
    calc C.card = ∑ _c ∈ C, 1 := by simp
      _ ≤ ∑ c ∈ C, c.card := Finset.sum_le_sum fun c hc => by
        obtain ⟨k, hk⟩ := hCodd c hc; omega
  have hSbound : S.card ≤ 1 := by omega
  interval_cases hSc : S.card
  · -- |S| = 0, C.card ≥ 2, sum ≤ 4. Some c ∈ C must have card 1!
    have hex1 : ∃ c ∈ C, c.card = 1 := by
      by_contra hall
      push Not at hall
      have hge3 : ∀ c ∈ C, 3 ≤ c.card := by
        intro c hc
        obtain ⟨k, hk⟩ := hCodd c hc
        have hne1 := hall c hc
        omega
      have : 3 * C.card ≤ ∑ c ∈ C, c.card := by
        calc 3 * C.card = ∑ _c ∈ C, 3 := by simp [mul_comm]
          _ ≤ ∑ c ∈ C, c.card := Finset.sum_le_sum hge3
      omega
    obtain ⟨c, hcC, hc1⟩ := hex1
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hc1
    right
    refine ⟨v, ?_⟩
    have hge := card_compl_sub_le_deg_of_tutte (X := X) (v := v) (by simp) (hCdisj {v} hcC)
      (fun w hwS hwc => hadj {v} hcC v (by simp) w hwS hwc)
    have hle : X.degree v ≤ 3 := by
      have := X.degree_lt_card_verts v; omega
    simp only [hV, hSc, Finset.card_singleton] at hge
    omega
  · -- |S| = 1, C.card ≥ 3, sum ≤ 3 -> K₃!
    left
    refine hasClique_of_disjoint_sets (D := C) (k := 3) (by omega) ?_ hCpair ?_
    · intro c hc; obtain ⟨k, hk⟩ := hCodd c hc; exact Finset.card_pos.mp (by omega)
    · intro c₁ hc₁ c₂ hc₂ hne u hu v hv
      have hvS : v ∉ S := Finset.disjoint_left.mp (hCdisj c₂ hc₂) hv
      have hvc₁ : v ∉ c₁ := Finset.disjoint_right.mp (hCpair hc₁ hc₂ hne) hv
      exact hadj c₁ hc₁ u hu v hvS hvc₁

/-- **Gan–Huang Lemma 5.2**: On 6 vertices, if `Δ(X \ {uv}) ≤ 2` (equivalently every vertex
outside `{u, v}` has degree `≤ 2` in `X`, and `u, v` have degree `≤ 3` in `X`), then `Xᶜ`
has a perfect matching. -/
theorem hasPM_six_of_deg_le_two_except_two {X : SimpleGraph V} [DecidableRel X.Adj]
    (hV : Fintype.card V = 6) (u v : V)
    (hdeg : ∀ w : V, w ≠ u → w ≠ v → X.degree w ≤ 2)
    (hdu : X.degree u ≤ 3) (hdv : X.degree v ≤ 3) :
    HasPM Xᶜ := by
  classical
  by_contra hno
  have hcompl : (Xᶜ)ᶜ = X := compl_compl X
  obtain ⟨S, C, hS2, hCodd, hCdisj, hCpair, hsum, hadj⟩ :=
    exists_tutte_odd_partition (H := Xᶜ) (by rw [hV]; exact ⟨3, rfl⟩) hno
  rw [hcompl] at hadj
  have hCge : C.card ≤ ∑ c ∈ C, c.card := by
    calc C.card = ∑ _c ∈ C, 1 := by simp
      _ ≤ ∑ c ∈ C, c.card := Finset.sum_le_sum fun c hc => by
        obtain ⟨k, hk⟩ := hCodd c hc; omega
  have hdeg3 : ∀ w : V, X.degree w ≤ 3 := fun w => by
    by_cases hwu : w = u
    · exact hwu ▸ hdu
    · by_cases hwv : w = v
      · exact hwv ▸ hdv
      · exact le_trans (hdeg w hwu hwv) (by omega)
  have hSbound : S.card ≤ 2 := by omega
  interval_cases hSc : S.card
  · -- |S| = 0, C.card ≥ 2, sum ≤ 6. Every c has |c| ≥ 6 - 3 = 3!
    have hge3 : ∀ c ∈ C, 3 ≤ c.card := by
      intro c hc
      have hpos : 0 < c.card := by obtain ⟨k, hk⟩ := hCodd c hc; omega
      obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
      have h1 := card_compl_sub_le_deg_of_tutte (X := X) hw (hCdisj c hc) (hadj c hc w hw)
      have h2 := hdeg3 w
      rw [hV, hSc] at h1
      omega
    -- If C.card ≥ 3 then sum ≥ 9 > 6; if C.card = 2 then both have card 3, so some vertex
    -- of each component is neither u nor v (since 3 > 2), giving degree ≥ 6 - 3 = 3 > 2!
    have hC2 : C.card = 2 := by
      have : 3 * C.card ≤ ∑ c ∈ C, c.card := by
        calc 3 * C.card = ∑ _c ∈ C, 3 := by simp [mul_comm]
          _ ≤ ∑ c ∈ C, c.card := Finset.sum_le_sum hge3
      omega
    obtain ⟨c, hcC⟩ := Finset.card_pos.mp (by omega : 0 < C.card)
    have hc3 : c.card = 3 := by
      have hrest : 3 * (C.erase c).card ≤ ∑ d ∈ C.erase c, d.card := by
        calc 3 * (C.erase c).card = ∑ _d ∈ C.erase c, 3 := by simp [mul_comm]
          _ ≤ ∑ d ∈ C.erase c, d.card := Finset.sum_le_sum fun d hd =>
            hge3 d (Finset.mem_of_mem_erase hd)
      have hsplit := Finset.add_sum_erase C (fun d => d.card) hcC
      have hce : (C.erase c).card = 1 := by rw [Finset.card_erase_of_mem hcC, hC2]
      have := hge3 c hcC
      omega
    have hexw : ∃ w ∈ c, w ≠ u ∧ w ≠ v := by
      have hsub : ¬ c ⊆ ({u, v} : Finset V) := by
        intro hs
        have h1 := Finset.card_le_card hs
        have h2 : ({u, v} : Finset V).card ≤ 2 := Finset.card_le_two
        omega
      rw [Finset.not_subset] at hsub
      obtain ⟨w, hwc, hwuv⟩ := hsub
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hwuv
      exact ⟨w, hwc, hwuv.1, hwuv.2⟩
    obtain ⟨w, hwc, hwu, hwv⟩ := hexw
    have h1 := card_compl_sub_le_deg_of_tutte (X := X) hwc (hCdisj c hcC) (hadj c hcC w hwc)
    have h2 := hdeg w hwu hwv
    rw [hV, hSc, hc3] at h1
    omega
  · -- |S| = 1, C.card ≥ 3, sum ≤ 5. Every c has |c| ≥ 5 - 3 = 2, odd => ≥ 3, so sum ≥ 9 > 5!
    have hge3 : ∀ c ∈ C, 3 ≤ c.card := by
      intro c hc
      have hpos : 0 < c.card := by obtain ⟨k, hk⟩ := hCodd c hc; omega
      obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
      have h1 := card_compl_sub_le_deg_of_tutte (X := X) hw (hCdisj c hc) (hadj c hc w hw)
      have h2 := hdeg3 w
      obtain ⟨k, hk⟩ := hCodd c hc
      rw [hV, hSc] at h1
      omega
    have : 3 * C.card ≤ ∑ c ∈ C, c.card := by
      calc 3 * C.card = ∑ _c ∈ C, 3 := by simp [mul_comm]
        _ ≤ ∑ c ∈ C, c.card := Finset.sum_le_sum hge3
    omega
  · -- |S| = 2, C.card ≥ 4, sum ≤ 4 -> all 4 components are singletons!
    -- At least 2 of the 4 singletons are neither u nor v, each has degree ≥ 6 - 2 - 1 = 3 > 2!
    have hC4 : C.card = 4 := by omega
    have hall1 : ∀ c ∈ C, c.card = 1 := by
      intro c hc
      by_contra hne1
      obtain ⟨k, hk⟩ := hCodd c hc
      have hge3 : 3 ≤ c.card := by omega
      have hrest : (C.erase c).card ≤ ∑ d ∈ C.erase c, d.card := by
        calc (C.erase c).card = ∑ _d ∈ C.erase c, 1 := by simp
          _ ≤ ∑ d ∈ C.erase c, d.card := Finset.sum_le_sum fun d hd => by
            obtain ⟨j, hj⟩ := hCodd d (Finset.mem_of_mem_erase hd); omega
      have hsplit := Finset.add_sum_erase C (fun d => d.card) hc
      have hce : (C.erase c).card = 3 := by rw [Finset.card_erase_of_mem hc, hC4]
      omega
    have hbiCard : (C.biUnion id).card = 4 := by
      rw [Finset.card_biUnion hCpair]
      simp only [id]
      rw [Finset.sum_congr rfl (fun c hc => hall1 c hc), Finset.sum_const, smul_eq_mul, hC4]
    have hexw : ∃ w ∈ C.biUnion id, w ≠ u ∧ w ≠ v := by
      have hsub : ¬ C.biUnion id ⊆ ({u, v} : Finset V) := by
        intro hs
        have h1 := Finset.card_le_card hs
        have h2 : ({u, v} : Finset V).card ≤ 2 := Finset.card_le_two
        omega
      rw [Finset.not_subset] at hsub
      obtain ⟨w, hw, hwuv⟩ := hsub
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hwuv
      exact ⟨w, hw, hwuv.1, hwuv.2⟩
    obtain ⟨w, hw, hwu, hwv⟩ := hexw
    rw [Finset.mem_biUnion] at hw
    obtain ⟨c, hcC, hwc⟩ := hw
    have hc1 := hall1 c hcC
    have h1 := card_compl_sub_le_deg_of_tutte (X := X) hwc (hCdisj c hcC) (hadj c hcC w hwc)
    have h2 := hdeg w hwu hwv
    simp only [id, hV, hSc, hc1] at h1
    omega

/-- **Gan–Huang Corollary 5.3**: On 6 vertices, if `Δ(X) ≤ 2`, then `Xᶜ` has a PM. -/
theorem hasPM_six_of_compl_le_two {X : SimpleGraph V} [DecidableRel X.Adj]
    (hV : Fintype.card V = 6) (hdeg : ∀ w : V, X.degree w ≤ 2) :
    HasPM Xᶜ := by
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨u⟩ := hne
  exact hasPM_six_of_deg_le_two_except_two hV u u (fun w _ _ => hdeg w)
    (le_trans (hdeg u) (by omega)) (le_trans (hdeg u) (by omega))

/-- **Gan–Huang Lemma 5.4 (necessity direction)**: On 6 vertices, if `Δ(X) ≤ 3` and `Xᶜ` has no
PM, then `X` contains `K₄` or `K₃,₃`. -/
theorem not_hasPM_six_of_compl_le_three {X : SimpleGraph V} [DecidableRel X.Adj]
    (hV : Fintype.card V = 6) (hdeg : ∀ w : V, X.degree w ≤ 3) (hno : ¬ HasPM Xᶜ) :
    HasClique X 4 ∨ HasK X 3 3 := by
  classical
  have hcompl : (Xᶜ)ᶜ = X := compl_compl X
  obtain ⟨S, C, hS2, hCodd, hCdisj, hCpair, hsum, hadj⟩ :=
    exists_tutte_odd_partition (H := Xᶜ) (by rw [hV]; exact ⟨3, rfl⟩) hno
  rw [hcompl] at hadj
  have hCge : C.card ≤ ∑ c ∈ C, c.card := by
    calc C.card = ∑ _c ∈ C, 1 := by simp
      _ ≤ ∑ c ∈ C, c.card := Finset.sum_le_sum fun c hc => by
        obtain ⟨k, hk⟩ := hCodd c hc; omega
  have hSbound : S.card ≤ 2 := by omega
  interval_cases hSc : S.card
  · -- |S| = 0, C.card ≥ 2, sum ≤ 6, each |c| ≥ 6 - 3 = 3 => two components of size 3 => K_{3,3}!
    have hge3 : ∀ c ∈ C, 3 ≤ c.card := by
      intro c hc
      have hpos : 0 < c.card := by obtain ⟨k, hk⟩ := hCodd c hc; omega
      obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
      have h1 := card_compl_sub_le_deg_of_tutte (X := X) hw (hCdisj c hc) (hadj c hc w hw)
      have h2 := hdeg w
      rw [hV, hSc] at h1
      omega
    have hC2 : C.card = 2 := by
      have : 3 * C.card ≤ ∑ c ∈ C, c.card := by
        calc 3 * C.card = ∑ _c ∈ C, 3 := by simp [mul_comm]
          _ ≤ ∑ c ∈ C, c.card := Finset.sum_le_sum hge3
      omega
    obtain ⟨A, B, hAB, hCeq⟩ := Finset.card_eq_two.mp hC2
    have hA : A ∈ C := by rw [hCeq]; simp
    have hB : B ∈ C := by rw [hCeq]; simp
    have hsumAB : A.card + B.card ≤ 6 := by
      rw [hCeq, Finset.sum_pair hAB] at hsum; omega
    have hA3 : A.card = 3 := by have := hge3 A hA; have := hge3 B hB; omega
    have hB3 : B.card = 3 := by have := hge3 A hA; have := hge3 B hB; omega
    right
    refine ⟨A, B, hA3, hB3, hCpair hA hB hAB, fun u hu v hv => ?_⟩
    exact hadj A hA u hu v (Finset.disjoint_left.mp (hCdisj B hB) hv)
      (Finset.disjoint_right.mp (hCpair hA hB hAB) hv)
  · -- |S| = 1, C.card ≥ 3, sum ≤ 5, each |c| ≥ 2, odd => ≥ 3, sum ≥ 9 > 5!
    have hge3 : ∀ c ∈ C, 3 ≤ c.card := by
      intro c hc
      have hpos : 0 < c.card := by obtain ⟨k, hk⟩ := hCodd c hc; omega
      obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
      have h1 := card_compl_sub_le_deg_of_tutte (X := X) hw (hCdisj c hc) (hadj c hc w hw)
      have h2 := hdeg w
      obtain ⟨k, hk⟩ := hCodd c hc
      rw [hV, hSc] at h1
      omega
    have : 3 * C.card ≤ ∑ c ∈ C, c.card := by
      calc 3 * C.card = ∑ _c ∈ C, 3 := by simp [mul_comm]
        _ ≤ ∑ c ∈ C, c.card := Finset.sum_le_sum hge3
    omega
  · -- |S| = 2, C.card ≥ 4 => K₄!
    left
    refine hasClique_of_disjoint_sets (D := C) (k := 4) (by omega) ?_ hCpair ?_
    · intro c hc; obtain ⟨k, hk⟩ := hCodd c hc; exact Finset.card_pos.mp (by omega)
    · intro c₁ hc₁ c₂ hc₂ hne u hu v hv
      exact hadj c₁ hc₁ u hu v (Finset.disjoint_left.mp (hCdisj c₂ hc₂) hv)
        (Finset.disjoint_right.mp (hCpair hc₁ hc₂ hne) hv)

/-- **Dirac / Tutte on 8 vertices**: If `card V = 8` and `Δ(X) ≤ 3` (i.e. `δ(Xᶜ) ≥ 4`), then
`Xᶜ` has a perfect matching. -/
theorem hasPM_eight_of_compl_le_three {X : SimpleGraph V} [DecidableRel X.Adj]
    (hV : Fintype.card V = 8) (hdeg : ∀ w : V, X.degree w ≤ 3) :
    HasPM Xᶜ := by
  classical
  by_contra hno
  have hcompl : (Xᶜ)ᶜ = X := compl_compl X
  obtain ⟨S, C, hS2, hCodd, hCdisj, hCpair, hsum, hadj⟩ :=
    exists_tutte_odd_partition (H := Xᶜ) (by rw [hV]; exact ⟨4, rfl⟩) hno
  rw [hcompl] at hadj
  have hCge : C.card ≤ ∑ c ∈ C, c.card := by
    calc C.card = ∑ _c ∈ C, 1 := by simp
      _ ≤ ∑ c ∈ C, c.card := Finset.sum_le_sum fun c hc => by
        obtain ⟨k, hk⟩ := hCodd c hc; omega
  have hSbound : S.card ≤ 3 := by omega
  have hmin : ∀ c ∈ C, 8 - S.card - 3 ≤ c.card := by
    intro c hc
    have hpos : 0 < c.card := by obtain ⟨k, hk⟩ := hCodd c hc; omega
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
    have h1 := card_compl_sub_le_deg_of_tutte (X := X) hw (hCdisj c hc) (hadj c hc w hw)
    have h2 := hdeg w
    rw [hV] at h1
    omega
  interval_cases hSc : S.card
  · have hge5 : ∀ c ∈ C, 5 ≤ c.card := fun c hc => by have := hmin c hc; omega
    have : 5 * C.card ≤ ∑ c ∈ C, c.card := by
      calc 5 * C.card = ∑ _c ∈ C, 5 := by simp [mul_comm]
        _ ≤ ∑ c ∈ C, c.card := Finset.sum_le_sum hge5
    omega
  · have hge5 : ∀ c ∈ C, 5 ≤ c.card := fun c hc => by
      have := hmin c hc; obtain ⟨k, hk⟩ := hCodd c hc; omega
    have : 5 * C.card ≤ ∑ c ∈ C, c.card := by
      calc 5 * C.card = ∑ _c ∈ C, 5 := by simp [mul_comm]
        _ ≤ ∑ c ∈ C, c.card := Finset.sum_le_sum hge5
    omega
  · have hge3 : ∀ c ∈ C, 3 ≤ c.card := fun c hc => by have := hmin c hc; omega
    have : 3 * C.card ≤ ∑ c ∈ C, c.card := by
      calc 3 * C.card = ∑ _c ∈ C, 3 := by simp [mul_comm]
        _ ≤ ∑ c ∈ C, c.card := Finset.sum_le_sum hge3
    omega
  · have hge3 : ∀ c ∈ C, 3 ≤ c.card := fun c hc => by
      have := hmin c hc; obtain ⟨k, hk⟩ := hCodd c hc; omega
    have : 3 * C.card ≤ ∑ c ∈ C, c.card := by
      calc 3 * C.card = ∑ _c ∈ C, 3 := by simp [mul_comm]
        _ ≤ ∑ c ∈ C, c.card := Finset.sum_le_sum hge3
    omega

/-- **8-vertex Tutte classification for `Δ(X) ≤ 6`**:
If `card V = 8`, `Δ(X) ≤ 6`, and `Xᶜ` has no perfect matching, then `X` contains one of:
1. `K₅`,
2. `K₃ ∨ 3K₁`,
3. `K₃,₅`,
4. `K₂ ∨ 5K₁` (two adjacent vertices of degree 6 in `X`, complete to 5 others), or
5. `K₁ ∨ K₃,₃` (one vertex of degree 6 in `X`, joined to a `K₃,₃`). -/
theorem not_hasPM_eight_of_compl_le_six {X : SimpleGraph V} [DecidableRel X.Adj]
    (hV : Fintype.card V = 8) (hdeg : ∀ w : V, X.degree w ≤ 6) (hno : ¬ HasPM Xᶜ) :
    HasClique X 5 ∨ HasCliqueJoin X 3 3 ∨ HasK X 3 5 ∨
      HasCliqueJoin X 2 5 ∨ HasK1JoinK33 X := by
  classical
  have hcompl : (Xᶜ)ᶜ = X := compl_compl X
  obtain ⟨S, C, hS2, hCodd, hCdisj, hCpair, hsum, hadj⟩ :=
    exists_tutte_odd_partition (H := Xᶜ) (by rw [hV]; exact ⟨4, rfl⟩) hno
  rw [hcompl] at hadj
  have hCge : C.card ≤ ∑ c ∈ C, c.card := by
    calc C.card = ∑ _c ∈ C, 1 := by simp
      _ ≤ ∑ c ∈ C, c.card := Finset.sum_le_sum fun c hc => by
        obtain ⟨k, hk⟩ := hCodd c hc; omega
  have hCne : ∀ c ∈ C, c.Nonempty := fun c hc =>
    Finset.card_pos.mp (by obtain ⟨k, hk⟩ := hCodd c hc; omega)
  have hCadj : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → ∀ u ∈ c₁, ∀ v ∈ c₂, X.Adj u v :=
    fun c₁ hc₁ c₂ hc₂ hne u hu v hv =>
      hadj c₁ hc₁ u hu v (Finset.disjoint_left.mp (hCdisj c₂ hc₂) hv)
        (Finset.disjoint_right.mp (hCpair hc₁ hc₂ hne) hv)
  -- If C.card ≥ 5, we immediately get K₅!
  by_cases hC5 : 5 ≤ C.card
  · exact Or.inl (hasClique_of_disjoint_sets hC5 hCne hCpair hCadj)
  push Not at hC5
  have hSbound : S.card ≤ 2 := by omega
  interval_cases hSc : S.card
  · -- |S| = 0, C.card ∈ {2, 3, 4}, sum ≤ 8.
    -- Since Δ(X) ≤ 6, no component can have size 1 (else deg_X ≥ 8 - 0 - 1 = 7)!
    have hge3 : ∀ c ∈ C, 3 ≤ c.card := by
      intro c hc
      obtain ⟨w, hw⟩ := hCne c hc
      have h1 := card_compl_sub_le_deg_of_tutte (X := X) hw (hCdisj c hc) (hadj c hc w hw)
      have h2 := hdeg w
      obtain ⟨k, hk⟩ := hCodd c hc
      omega
    have hC2 : C.card = 2 := by
      have : 3 * C.card ≤ ∑ c ∈ C, c.card := by
        calc 3 * C.card = ∑ _c ∈ C, 3 := by simp [mul_comm]
          _ ≤ ∑ c ∈ C, c.card := Finset.sum_le_sum hge3
      omega
    obtain ⟨A, B, hAB, hCeq⟩ := Finset.card_eq_two.mp hC2
    have hA : A ∈ C := by rw [hCeq]; simp
    have hB : B ∈ C := by rw [hCeq]; simp
    have hsumAB : A.card + B.card ≤ 8 := by rw [hCeq, Finset.sum_pair hAB] at hsum; omega
    have hA3 : 3 ≤ A.card := hge3 A hA
    have hB3 : 3 ≤ B.card := hge3 B hB
    -- Either A.card = 3 (and B.card ∈ {3, 5}) or B.card = 3!
    -- Wait: if A.card = 3 and B.card = 3, then there are 2 leftover vertices in (A ∪ B)ᶜ,
    -- which are ALSO adjacent in X to all of A! So A (size 3) is complete to Aᶜ (size 5) => K_{3,5}!
    have hex3 : ∃ c ∈ C, c.card = 3 := by
      by_contra hno3
      push Not at hno3
      have hA5 : 5 ≤ A.card := by obtain ⟨k, hk⟩ := hCodd A hA; have := hno3 A hA; omega
      have hB5 : 5 ≤ B.card := by obtain ⟨k, hk⟩ := hCodd B hB; have := hno3 B hB; omega
      omega
    obtain ⟨c, hcC, hc3⟩ := hex3
    refine Or.inr (Or.inr (Or.inl ⟨c, cᶜ, hc3, ?_, disjoint_compl_right, ?_⟩))
    · rw [Finset.card_compl, hV, hc3]
    · intro u hu v hv
      rw [Finset.mem_compl] at hv
      have hvS : v ∉ S := by
        have hSe : S = ∅ := Finset.card_eq_zero.mp hSc
        simp [hSe]
      exact hadj c hcC u hu v hvS hv
  · -- |S| = 1, C.card ∈ {3, 4}, sum ≤ 7.
    -- Let C1 = components of size 1, C3 = components of size ≥ 3.
    let C1 := C.filter (fun c => c.card = 1)
    let C3 := C.filter (fun c => 3 ≤ c.card)
    have hpart : C1.card + C3.card = C.card := by
      have hdisj : Disjoint C1 C3 := by
        rw [Finset.disjoint_left]; intro c h1 h3
        simp only [C1, C3, Finset.mem_filter] at h1 h3; omega
      have hun : C1 ∪ C3 = C := by
        ext c; simp only [C1, C3, Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        · intro hc; obtain ⟨k, hk⟩ := hCodd c hc; by_cases hk0 : k = 0
          · left; exact ⟨hc, by omega⟩
          · right; exact ⟨hc, by omega⟩
      rw [← Finset.card_union_of_disjoint hdisj, hun]
    have hsum_lb : C1.card + 3 * C3.card ≤ ∑ c ∈ C, c.card := by
      have hdisj : Disjoint C1 C3 := by
        rw [Finset.disjoint_left]; intro c h1 h3
        simp only [C1, C3, Finset.mem_filter] at h1 h3; omega
      have hun : C1 ∪ C3 = C := by
        ext c; simp only [C1, C3, Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        · intro hc; obtain ⟨k, hk⟩ := hCodd c hc; by_cases hk0 : k = 0
          · left; exact ⟨hc, by omega⟩
          · right; exact ⟨hc, by omega⟩
      rw [← hun, Finset.sum_union hdisj]
      have h1 : C1.card ≤ ∑ c ∈ C1, c.card := by
        calc C1.card = ∑ _c ∈ C1, 1 := by simp
          _ ≤ ∑ c ∈ C1, c.card := Finset.sum_le_sum fun c hc => by
            simp only [C1, Finset.mem_filter] at hc; omega
      have h3 : 3 * C3.card ≤ ∑ c ∈ C3, c.card := by
        calc 3 * C3.card = ∑ _c ∈ C3, 3 := by simp [mul_comm]
          _ ≤ ∑ c ∈ C3, c.card := Finset.sum_le_sum fun c hc => by
            simp only [C3, Finset.mem_filter] at hc; exact hc.2
      omega
    -- Either C1.card ≥ 2 (gives K₂ ∨ 5K₁!) or C1.card = 1 and C3.card = 2 (gives K₁ ∨ K₃,₃!)
    by_cases hC1ge2 : 2 ≤ C1.card
    · -- Pick 2 singleton components {a}, {b} ∈ C1; {a, b} is K₂ complete to (S ∪ {a, b})ᶜ (size 5)!
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
      have haS : a ∉ S := Finset.disjoint_left.mp (hCdisj {a} hc₁C) (by simp)
      have hbS : b ∉ S := Finset.disjoint_left.mp (hCdisj {b} hc₂C) (by simp)
      let A : Finset V := {a, b}
      let B : Finset V := (S ∪ A)ᶜ
      have hdisjSA : Disjoint S A := by
        rw [Finset.disjoint_right]
        intro x hx; simp only [A, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      have hAcard : A.card = 2 := Finset.card_pair hab
      have hBcard : B.card = 5 := by
        simp only [B, Finset.card_compl, Finset.card_union_of_disjoint hdisjSA, hV, hSc, hAcard]
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨A, B, hAcard, hBcard, ?_, ?_, ?_⟩)))
      · rw [Finset.disjoint_right]
        intro x hxB hxA
        simp only [B, Finset.mem_compl, Finset.mem_union] at hxB
        exact hxB (Or.inr hxA)
      · intro x hx y hy hxy
        simp only [A, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · exact absurd (hx.trans hy.symm) hxy
        · rw [hx, hy]; exact hCadj {a} hc₁C {b} hc₂C hcne a (by simp) b (by simp)
        · rw [hx, hy]; exact hCadj {b} hc₂C {a} hc₁C hcne.symm b (by simp) a (by simp)
        · exact absurd (hx.trans hy.symm) hxy
      · intro x hx y hy
        simp only [A, Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [B, Finset.mem_compl, Finset.mem_union, not_or] at hy
        rcases hx with hx | hx
        · rw [hx]; exact hadj {a} hc₁C a (by simp) y hy.1 (fun h => hy.2 (by simp_all [A]))
        · rw [hx]; exact hadj {b} hc₂C b (by simp) y hy.1 (fun h => hy.2 (by simp_all [A]))
    · -- C1.card ≤ 1, C1.card + C3.card ≥ 3, C1.card + 3 * C3.card ≤ 7 => C1.card = 1, C3.card = 2!
      have hC1eq : C1.card = 1 := by omega
      have hC3eq : C3.card = 2 := by omega
      obtain ⟨c₀, hc₀eq⟩ := Finset.card_eq_one.mp hC1eq
      have hc₀1 : c₀ ∈ C1 := by rw [hc₀eq]; simp
      have hc₀C : c₀ ∈ C := (Finset.mem_filter.mp hc₀1).1
      obtain ⟨u, rfl⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hc₀1).2
      obtain ⟨A, B, hAB, hC3def⟩ := Finset.card_eq_two.mp hC3eq
      have hA3m : A ∈ C3 := by rw [hC3def]; simp
      have hB3m : B ∈ C3 := by rw [hC3def]; simp
      have hAC : A ∈ C := (Finset.mem_filter.mp hA3m).1
      have hBC : B ∈ C := (Finset.mem_filter.mp hB3m).1
      have hA_ge3 : 3 ≤ A.card := (Finset.mem_filter.mp hA3m).2
      have hB_ge3 : 3 ≤ B.card := (Finset.mem_filter.mp hB3m).2
      have hA_ne_u : {u} ≠ A := fun h => by rw [← h] at hA_ge3; simp at hA_ge3
      have hB_ne_u : {u} ≠ B := fun h => by rw [← h] at hB_ge3; simp at hB_ge3
      -- Both A and B have card 3 (since 1 + A.card + B.card ≤ 7)
      have hsub3 : ({ {u}, A, B } : Finset (Finset V)) ⊆ C := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      have hsum3 : ({u} : Finset V).card + A.card + B.card ≤ ∑ c ∈ C, c.card := by
        have h1 := Finset.sum_le_sum_of_subset (f := fun c : Finset V => c.card) hsub3
        rw [Finset.sum_insert (by simp [hA_ne_u, hB_ne_u]), Finset.sum_pair hAB] at h1
        omega
      have hA3 : A.card = 3 := by simp at hsum3; omega
      have hB3 : B.card = 3 := by simp at hsum3; omega
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨u, A, B, ?_, ?_, hA3, hB3, hCpair hAC hBC hAB, ?_, ?_, ?_⟩)))
      · exact Finset.disjoint_left.mp (hCpair hc₀C hAC hA_ne_u) (by simp)
      · exact Finset.disjoint_left.mp (hCpair hc₀C hBC hB_ne_u) (by simp)
      · intro x hx; exact hCadj {u} hc₀C A hAC hA_ne_u u (by simp) x hx
      · intro y hy; exact hCadj {u} hc₀C B hBC hB_ne_u u (by simp) y hy
      · intro x hx y hy; exact hCadj A hAC B hBC hAB x hx y hy
  · -- |S| = 2, C.card = 4, sum ≤ 6 => at least 3 singletons!
    -- Those 3 singletons form K₃ complete to (S ∪ A)ᶜ (size 3) => K₃ ∨ 3K₁!
    have hC4 : C.card = 4 := by omega
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
    have hpart : C1.card + C3.card = 4 := by
      rw [← Finset.card_union_of_disjoint hdisj13, hun13, hC4]
    have hsum_lb : C1.card + 3 * C3.card ≤ 6 := by
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
    have hC1ge3 : 3 ≤ C1.card := by omega
    obtain ⟨D, hDsub, hD3⟩ := Finset.exists_subset_card_eq hC1ge3
    let A : Finset V := D.biUnion id
    have hDpair : (D : Set (Finset V)).PairwiseDisjoint id :=
      hCpair.subset (fun c hc => (Finset.mem_filter.mp (hDsub hc)).1)
    have hAcard : A.card = 3 := by
      rw [Finset.card_biUnion hDpair]
      simp only [id]
      have h1 : ∀ c ∈ D, c.card = 1 := fun c hc => (Finset.mem_filter.mp (hDsub hc)).2
      rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, hD3]
    have hdisjSA : Disjoint S A := by
      rw [Finset.disjoint_right]
      intro v hv hvS
      rw [Finset.mem_biUnion] at hv
      obtain ⟨c, hcD, hvc⟩ := hv
      exact Finset.disjoint_left.mp (hCdisj c (Finset.mem_filter.mp (hDsub hcD)).1) hvc hvS
    let B : Finset V := (S ∪ A)ᶜ
    have hBcard : B.card = 3 := by
      simp only [B, Finset.card_compl, Finset.card_union_of_disjoint hdisjSA, hV, hSc, hAcard]
    refine Or.inr (Or.inl ⟨A, B, hAcard, hBcard, ?_, ?_, ?_⟩)
    · rw [Finset.disjoint_right]; intro x hxB hxA
      simp only [B, Finset.mem_compl, Finset.mem_union] at hxB
      exact hxB (Or.inr hxA)
    · intro x hx y hy hxy
      rw [Finset.mem_coe, Finset.mem_biUnion] at hx hy
      obtain ⟨c₁, hc₁D, hxc₁⟩ := hx
      obtain ⟨c₂, hc₂D, hyc₂⟩ := hy
      have hc₁C : c₁ ∈ C := (Finset.mem_filter.mp (hDsub hc₁D)).1
      have hc₂C : c₂ ∈ C := (Finset.mem_filter.mp (hDsub hc₂D)).1
      have hne : c₁ ≠ c₂ := by
        intro heq; subst heq
        obtain ⟨z, rfl⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp (hDsub hc₁D)).2
        simp only [id, Finset.mem_singleton] at hxc₁ hyc₂
        exact hxy (hxc₁.trans hyc₂.symm)
      exact hCadj c₁ hc₁C c₂ hc₂C hne x hxc₁ y hyc₂
    · intro x hx y hy
      rw [Finset.mem_biUnion] at hx
      obtain ⟨c, hcD, hxc⟩ := hx
      have hcC : c ∈ C := (Finset.mem_filter.mp (hDsub hcD)).1
      simp only [B, Finset.mem_compl, Finset.mem_union, not_or] at hy
      have hyc : y ∉ c := fun h => hy.2 (Finset.mem_biUnion.mpr ⟨c, hcD, h⟩)
      exact hadj c hcC x hxc y hy.1 hyc

/-- **Corollary 8.2 (8-vertex classification for `Δ(X) ≤ 5`)**:
If `card V = 8`, `Δ(X) ≤ 5`, and `Xᶜ` has no perfect matching, then `X` contains `K₅`,
`K₃ ∨ 3K₁`, or `K₃,₅`. -/
theorem not_hasPM_eight_of_compl_le_five {X : SimpleGraph V} [DecidableRel X.Adj]
    (hV : Fintype.card V = 8) (hdeg : ∀ w : V, X.degree w ≤ 5) (hno : ¬ HasPM Xᶜ) :
    HasClique X 5 ∨ HasCliqueJoin X 3 3 ∨ HasK X 3 5 := by
  have h6 := not_hasPM_eight_of_compl_le_six hV (fun w => le_trans (hdeg w) (by omega)) hno
  rcases h6 with h1 | h2 | h3 | h4 | h5
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)
  · -- HasCliqueJoin X 2 5 implies some vertex has degree ≥ 6!
    exfalso
    obtain ⟨A, B, hA, hB, hdisj, hcl, hadj⟩ := h4
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hA
    have hsub : insert b B ⊆ X.neighborFinset a := by
      intro x hx
      rw [SimpleGraph.mem_neighborFinset]
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hxB
      · exact hcl (by simp) (by simp) hab
      · exact hadj a (by simp) x hxB
    have hbB : b ∉ B := Finset.disjoint_left.mp hdisj (by simp)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hbB, hB, SimpleGraph.card_neighborFinset_eq_degree] at hcard
    have := hdeg a
    omega
  · -- HasK1JoinK33 X implies u has degree ≥ 6!
    exfalso
    obtain ⟨u, A, B, huA, huB, hA, hB, hdisj, h1, h2, _⟩ := h5
    have hsub : A ∪ B ⊆ X.neighborFinset u := by
      intro x hx
      rw [SimpleGraph.mem_neighborFinset]
      rw [Finset.mem_union] at hx
      rcases hx with hxA | hxB
      · exact h1 x hxA
      · exact h2 x hxB
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, hA, hB, SimpleGraph.card_neighborFinset_eq_degree] at hcard
    have := hdeg u
    omega

end SmallOrders

end LouYuK4
