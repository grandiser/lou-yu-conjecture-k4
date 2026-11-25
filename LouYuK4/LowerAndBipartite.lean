import Mathlib.Combinatorics.Hall.Finite
import LouYuK4.SmallOrders

/-!
# Lower Bound (Plummer 1980) and Bipartite Minimality

We prove:
1. `isKExtendable_even_card_and_ge`: Every `k`-extendable graph has even order `≥ 2k`.
2. `nu_ne_eight_of_connected_min_four`: No connected minimally 4-extendable graph has 8 vertices.
3. `nu_eq_10_ge_six_eq_nine`: At `ν = 10`, any 4-extendable graph with `δ ≥ 6` is `K₁₀` (`δ = 9`).
4. `isKExtendable_pred` and `plummer_min_degree` (Plummer 1980): Every connected `k`-extendable
   graph on `ν ≥ 2k + 2` vertices is `(k + 1)`-connected, hence `∀ v, k + 1 ≤ G.degree v`.
5. `bipartite_min_4ext_deg_five`: Every connected bipartite minimally 4-extendable graph on
   `ν ≤ 16` vertices has `∃ v, G.degree v = 5`.
-/

open SimpleGraph Finset

namespace LouYuK4

section LowerAndBipartite

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A graph is bipartite if its vertices partition into two independent sets. -/
def IsBipartite (G : SimpleGraph V) : Prop :=
  ∃ X : Finset V, (∀ u ∈ X, ∀ v ∈ X, ¬ G.Adj u v) ∧ (∀ u ∉ X, ∀ v ∉ X, ¬ G.Adj u v)

/-- A graph is `k`-connected (in the vertex-cut sense) if no set of `< k` vertices separates
two nonempty parts of the remaining vertices. -/
def IsKConnected (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ S A B : Finset V, S.card < k → A.Nonempty → B.Nonempty →
    Disjoint A B → Disjoint S A → Disjoint S B → S ∪ A ∪ B = Finset.univ →
    ∃ a ∈ A, ∃ b ∈ B, G.Adj a b

/-- Every connected graph has an edge crossing any nontrivial bipartition of `univ`. -/
lemma exists_adj_crossing_of_connected {G : SimpleGraph V} (hconn : G.Connected)
    {A B : Finset V} (hA : A.Nonempty) (hB : B.Nonempty)
    (hdisj : Disjoint A B) (hun : A ∪ B = Finset.univ) :
    ∃ a ∈ A, ∃ b ∈ B, G.Adj a b := by
  obtain ⟨a₀, ha₀⟩ := hA
  obtain ⟨b₀, hb₀⟩ := hB
  obtain ⟨p⟩ := hconn a₀ b₀
  have hwalk : ∀ {x y : V} (w : G.Walk x y), x ∈ A → y ∈ B → ∃ a ∈ A, ∃ b ∈ B, G.Adj a b := by
    intro x y w
    induction w with
    | nil => intro hx hy; exact absurd hy (Finset.disjoint_left.mp hdisj hx)
    | @cons u v z huv w' ih =>
      intro hu hz
      by_cases hvA : v ∈ A
      · exact ih hvA hz
      · have hvB : v ∈ B := by
          have : v ∈ A ∪ B := hun ▸ Finset.mem_univ v
          exact (Finset.mem_union.mp this).resolve_left hvA
        exact ⟨u, hu, v, hvB, huv⟩
  exact hwalk p ha₀ hb₀

lemma isKConnected_one_of_connected {G : SimpleGraph V} (hconn : G.Connected) :
    IsKConnected G 1 := by
  intro S A B hS hA hB hAB _ _ hun
  have hSe : S = ∅ := Finset.card_eq_zero.mp (by omega)
  rw [hSe, Finset.empty_union] at hun
  exact exists_adj_crossing_of_connected hconn hA hB hAB hun

/-- Any `k`-extendable graph has even order `≥ 2k`. -/
lemma isKExtendable_even_card_and_ge {G : SimpleGraph V} {k : ℕ} (hext : IsKExtendable G k) :
    Even (Fintype.card V) ∧ 2 * k ≤ Fintype.card V := by
  classical
  obtain ⟨⟨M₀, hM₀, hM₀card⟩, hE⟩ := hext
  obtain ⟨P, _, hP⟩ := hE M₀ hM₀ hM₀card
  have hPverts := isMatching_verts_ncard hP.1
  have hPuniv : P.verts = Set.univ := Set.eq_univ_of_forall hP.2
  rw [hPuniv, Set.ncard_univ, Nat.card_eq_fintype_card] at hPverts
  have hMverts := isMatching_verts_ncard hM₀
  rw [hM₀card, Set.ncard_eq_toFinset_card'] at hMverts
  have hle : M₀.verts.toFinset.card ≤ Fintype.card V := Finset.card_le_univ _
  exact ⟨⟨P.edgeSet.ncard, by omega⟩, by omega⟩

/-- No connected minimally 4-extendable graph has 8 vertices. -/
lemma nu_ne_eight_of_connected_min_four {G : SimpleGraph V}
    (hcard : Fintype.card V = 8) (hconn : G.Connected) :
    ¬ IsMinimallyKExtendable G 4 := by
  classical
  intro hmin
  obtain ⟨⟨M₀, hM₀, hM₀card⟩, _⟩ := hmin.1
  have hM₀verts := isMatching_verts_ncard hM₀
  rw [hM₀card, Set.ncard_eq_toFinset_card'] at hM₀verts
  have hM₀univ : M₀.verts.toFinset = Finset.univ :=
    Finset.eq_univ_of_card _ (by omega)
  have hM₀span : ∀ v : V, v ∈ M₀.verts := fun v => by
    have : v ∈ M₀.verts.toFinset := hM₀univ ▸ Finset.mem_univ v
    exact Set.mem_toFinset.mp this
  obtain ⟨v₀⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨v₁, hv01, hv01_uniq⟩ := hM₀ (hM₀span v₀)
  let A : Finset V := {v₀, v₁}
  let B : Finset V := Aᶜ
  have hAcard : A.card = 2 := Finset.card_pair hv01.ne
  have hBne : B.Nonempty := Finset.card_pos.mp (by rw [Finset.card_compl, hAcard, hcard]; omega)
  obtain ⟨a, haA, b, hbB, habG⟩ := exists_adj_crossing_of_connected hconn
    ⟨v₀, by simp [A]⟩ hBne disjoint_compl_right (Finset.union_compl A)
  have hab_notM₀ : ¬ M₀.Adj a b := by
    intro hMab
    have hbA : b ∈ A := by
      simp only [A, Finset.mem_insert, Finset.mem_singleton] at haA ⊢
      rcases haA with rfl | rfl
      · exact Or.inr (hv01_uniq b hMab)
      · exact Or.inl (hM₀.eq_of_adj_left hMab hv01.symm)
    exact (Finset.mem_compl.mp hbB) hbA
  have hnotext := hmin.2 s(a, b) habG
  apply hnotext
  let G' := G.deleteEdges {s(a, b)}
  have hM₀_in : ∀ u w : V, M₀.Adj u w → G'.Adj u w := by
    intro u w hMuw
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨hMuw.adj_sub, ?_⟩
    intro heq
    rw [Set.mem_singleton_iff, Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hab_notM₀ hMuw
    · exact hab_notM₀ hMuw.symm
  let M₀' : G'.Subgraph := {
    verts := M₀.verts
    Adj := M₀.Adj
    adj_sub := hM₀_in _ _
    edge_vert := M₀.edge_vert
    symm := M₀.symm
  }
  refine ⟨⟨M₀', hM₀, hM₀card⟩, fun M hM hMcard => ?_⟩
  have hMv := isMatching_verts_ncard hM
  rw [hMcard, Set.ncard_eq_toFinset_card'] at hMv
  have hMuniv : M.verts.toFinset = Finset.univ := Finset.eq_univ_of_card _ (by omega)
  refine ⟨M, le_rfl, hM, fun v => Set.mem_toFinset.mp (hMuniv ▸ Finset.mem_univ v)⟩

/-- At `ν = 10`, any 4-extendable graph with `δ(G) ≥ 6` is `K₁₀` (`∀ v, G.degree v = 9`). -/
theorem nu_eq_10_ge_six_eq_nine {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcard : Fintype.card V = 10) (hext : IsKExtendable G 4)
    (hmin6 : ∀ v : V, 6 ≤ G.degree v) :
    ∀ v : V, G.degree v = 9 := by
  classical
  have hdegC : ∀ v : V, Gᶜ.degree v ≤ 3 := fun v => by
    have h1 := degree_add_compl_degree G v
    have h2 := hmin6 v
    omega
  have hall_adj : ∀ u v : V, u ≠ v → G.Adj u v := by
    intro u v huv
    by_contra hna
    let S : Finset V := ({u, v} : Finset V)ᶜ
    have hS8 : S.card = 8 := by rw [Finset.card_compl, Finset.card_pair huv, hcard]
    have hSPM : HasPM (G.induce (S : Set V)) := hasPM_induce_eight_of_compl_le_three hdegC hS8
    have hScPM : HasPM (G.induce ((Sᶜ : Finset V) : Set V)) :=
      (isKExtendable_iff_compl_pm.mp hext).2 S hS8 hSPM
    have hSceq : Sᶜ = ({u, v} : Finset V) := compl_compl _
    rw [hSceq] at hScPM
    exact not_hasPM_pair_of_not_adj hna hScPM
  intro v
  have hN : G.neighborFinset v = Finset.univ.erase v := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨fun h => h.ne.symm, fun h => hall_adj v w h.symm⟩
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hN, Finset.card_erase_of_mem (Finset.mem_univ v),
    Finset.card_univ, hcard]

/-- **Plummer (1980), Theorem 2.2**: Every `(k + 1)`-extendable graph on `ν ≥ 2(k + 1) + 2`
vertices is `k`-extendable. -/
theorem isKExtendable_pred {G : SimpleGraph V} {k : ℕ}
    (hext : IsKExtendable G (k + 1)) (hcard : 2 * (k + 1) + 2 ≤ Fintype.card V) :
    IsKExtendable G k := by
  classical
  obtain ⟨⟨M₀, hM₀, hM₀card⟩, hE⟩ := hext
  obtain ⟨P₀, _, hP₀⟩ := hE M₀ hM₀ hM₀card
  -- First: G has a k-matching (drop one edge from M₀)
  have hex_k : ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = k := by
    have hne : M₀.edgeSet.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
    obtain ⟨e, he⟩ := hne
    induction e using Sym2.ind with
    | _ u v =>
      have huv : M₀.Adj u v := he
      let S : Finset V := (M₀.verts.toFinset.erase u).erase v
      have huM : u ∈ M₀.verts.toFinset := Set.mem_toFinset.mpr huv.fst_mem
      have hvM : v ∈ M₀.verts.toFinset := Set.mem_toFinset.mpr huv.snd_mem
      have hM0v := isMatching_verts_ncard hM₀
      rw [hM₀card, Set.ncard_eq_toFinset_card'] at hM0v
      have hScard : S.card = 2 * k := by
        rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨huv.ne.symm, hvM⟩),
          Finset.card_erase_of_mem huM, hM0v]; omega
      let M' : G.Subgraph := {
        verts := (S : Set V)
        Adj := fun x y => x ∈ S ∧ y ∈ S ∧ M₀.Adj x y
        adj_sub := fun h => h.2.2.adj_sub
        edge_vert := fun h => h.1
        symm := ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩
      }
      have hM' : M'.IsMatching := by
        intro x hx
        have hxM : x ∈ M₀.verts := Set.mem_toFinset.mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
        obtain ⟨y, hxy, huniq⟩ := hM₀ hxM
        have hyS : y ∈ S := by
          refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, Set.mem_toFinset.mpr hxy.snd_mem⟩⟩
          · intro hyv; subst hyv
            have hxu : x = u := hM₀.eq_of_adj_right hxy huv
            exact (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx)).1 hxu
          · intro hyu; subst hyu
            have hxv : x = v := hM₀.eq_of_adj_right hxy huv.symm
            exact (Finset.mem_erase.mp hx).1 hxv
        exact ⟨y, ⟨hx, hyS, hxy⟩, fun z hz => huniq z hz.2.2⟩
      have hM'v := isMatching_verts_ncard hM'
      have hM'verts : M'.verts.ncard = 2 * k := by
        change (S : Set V).ncard = 2 * k; rw [Set.ncard_coe_finset, hScard]
      exact ⟨M', hM', by omega⟩
  refine ⟨hex_k, fun M hM hMcard => ?_⟩
  let VM : Finset V := M.verts.toFinset
  let I : Finset V := VMᶜ
  have hVMcard : VM.card = 2 * k := by
    have h1 := isMatching_verts_ncard hM
    rw [hMcard, Set.ncard_eq_toFinset_card'] at h1; exact h1
  have hIcard : I.card = Fintype.card V - 2 * k := by rw [Finset.card_compl, hVMcard]
  -- If I contains an edge of G, extend M by that edge to a (k+1)-matching and apply hE!
  by_cases hedge : ∃ a ∈ I, ∃ b ∈ I, G.Adj a b
  · obtain ⟨a, haI, b, hbI, habG⟩ := hedge
    let M' : G.Subgraph := {
      verts := insert a (insert b M.verts)
      Adj := fun x y => M.Adj x y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a)
      adj_sub := by rintro x y (h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩); exact h.adj_sub; exact habG; exact habG.symm
      edge_vert := by
        rintro x y (h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ h.fst_mem)
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      symm := ⟨by rintro x y (h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩); exact Or.inl h.symm; exact Or.inr (Or.inr ⟨rfl, rfl⟩); exact Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    }
    have haM : a ∉ M.verts := fun h => (Finset.mem_compl.mp haI) (Set.mem_toFinset.mpr h)
    have hbM : b ∉ M.verts := fun h => (Finset.mem_compl.mp hbI) (Set.mem_toFinset.mpr h)
    have hM' : M'.IsMatching := by
      intro x hx
      rcases hx with rfl | rfl | hxM
      · refine ⟨b, Or.inr (Or.inl ⟨rfl, rfl⟩), ?_⟩
        rintro y (h | ⟨_, rfl⟩ | ⟨h, _⟩)
        · exact absurd h.fst_mem haM
        · rfl
        · exact absurd h habG.ne
      · refine ⟨a, Or.inr (Or.inr ⟨rfl, rfl⟩), ?_⟩
        rintro y (h | ⟨h, _⟩ | ⟨_, rfl⟩)
        · exact absurd h.fst_mem hbM
        · exact absurd h habG.ne.symm
        · rfl
      · obtain ⟨y, hxy, huniq⟩ := hM hxM
        refine ⟨y, Or.inl hxy, ?_⟩
        rintro z (h | ⟨rfl, _⟩ | ⟨rfl, _⟩)
        · exact huniq z h
        · exact absurd hxM haM
        · exact absurd hxM hbM
    have hM'v := isMatching_verts_ncard hM'
    have hM'fin : M'.verts.toFinset = insert a (insert b VM) := by
      ext t; simp [M', VM]
    have hM'card_v : M'.verts.ncard = 2 * k + 2 := by
      rw [Set.ncard_eq_toFinset_card', hM'fin,
        Finset.card_insert_of_notMem (by simp [habG.ne, Finset.mem_compl.mp haI]),
        Finset.card_insert_of_notMem (Finset.mem_compl.mp hbI), hVMcard]
    obtain ⟨P, hM'P, hP⟩ := hE M' hM' (by omega)
    exact ⟨P, le_trans ⟨fun x hx => Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hx), fun _ _ h => Or.inl h⟩ hM'P, hP⟩
  · -- Otherwise I is independent; follow an alternating path in M Δ P₀ from u₀ ∈ I to get a (k+1)-matching M₁!
    exfalso
    have hI_ind : ∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b := fun a ha b hb hab => hedge ⟨a, ha, b, hb, hab⟩
    choose p hp_adj hp_uniq using fun v : V => hP₀.1 (hP₀.2 v)
    have hp_inv : ∀ v : V, p (p v) = v := fun v => (hp_uniq (p v) v (hp_adj v).symm).symm
    have hm_ex : ∀ v : V, ∃ w : V, (v ∈ M.verts → M.Adj v w) ∧ (v ∉ M.verts → w = v) := by
      intro v; by_cases hv : v ∈ M.verts
      · obtain ⟨w, hvw, _⟩ := hM hv; exact ⟨w, fun _ => hvw, fun h => absurd hv h⟩
      · exact ⟨v, fun h => absurd h hv, fun _ => rfl⟩
    choose m hm_adj hm_out using hm_ex
    have hm_inv : ∀ v ∈ M.verts, m (m v) = v := fun v hv => by
      have h1 : M.Adj v (m v) := hm_adj v hv
      have h2 : M.Adj (m v) (m (m v)) := hm_adj (m v) h1.snd_mem
      exact hM.eq_of_adj_left h2 h1.symm
    obtain ⟨u₀, hu₀I⟩ : I.Nonempty := Finset.card_pos.mp (by omega)
    let x : ℕ → V := fun n => Nat.rec u₀ (fun _ prev => m (p prev)) n
    have hx0 : x 0 = u₀ := rfl
    have hxsucc : ∀ n, x (n + 1) = m (p (x n)) := fun _ => rfl
    have hex_hit : ∃ n : ℕ, p (x n) ∈ I := by
      by_contra hno
      push Not at hno
      have hpxM : ∀ n, p (x n) ∈ M.verts := fun n => by
        have := hno n; simp only [I, VM, Finset.mem_compl, Set.mem_toFinset, not_not] at this; exact this
      have hxM_pos : ∀ n, x (n + 1) ∈ M.verts := fun n => (hm_adj (p (x n)) (hpxM n)).snd_mem
      obtain ⟨i, j, hij, hxeq⟩ := Finite.exists_ne_map_eq_of_infinite x
      have hlt_ex : ∃ i j : ℕ, i < j ∧ x i = x j := by
        rcases lt_or_gt_of_ne hij with h | h; exact ⟨i, j, h, hxeq⟩; exact ⟨j, i, h, hxeq.symm⟩
      have hdesc : ∀ i : ℕ, ∀ j : ℕ, i < j → x i = x j → False := by
        intro i; induction i with
        | zero =>
          intro j hj h0j
          obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
          have h1 : u₀ ∈ M.verts := by rw [← hx0, h0j]; exact hxM_pos j'
          exact (Finset.mem_compl.mp hu₀I) (Set.mem_toFinset.mpr h1)
        | succ i' ih =>
          intro j hj hij_eq
          obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
          rw [hxsucc, hxsucc] at hij_eq
          have hp_eq : p (x i') = p (x j') := by
            have := congrArg m hij_eq
            rwa [hm_inv _ (hpxM i'), hm_inv _ (hpxM j')] at this
          have hx_eq : x i' = x j' := by
            have := congrArg p hp_eq
            rwa [hp_inv, hp_inv] at this
          exact ih j' (by omega) hx_eq
      obtain ⟨i, j, hlt, heq⟩ := hlt_ex
      exact hdesc i j hlt heq
    let r := Nat.find hex_hit
    have hpr_I : p (x r) ∈ I := Nat.find_spec hex_hit
    have hpx_M : ∀ i < r, p (x i) ∈ M.verts := fun i hi => by
      have hnotI : p (x i) ∉ I := Nat.find_min hex_hit hi
      simp only [I, VM, Finset.mem_compl, Set.mem_toFinset, not_not] at hnotI; exact hnotI
    have hx_M : ∀ i, 0 < i → i ≤ r → x i ∈ M.verts := fun i hi hir => by
      obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      exact (hm_adj (p (x i')) (hpx_M i' (by omega))).snd_mem
    have hx_inj : ∀ i ≤ r, ∀ j ≤ r, x i = x j → i = j := by
      intro i hi j hj heq
      by_contra hne
      have hdesc : ∀ a b : ℕ, a < b → b ≤ r → x a = x b → False := by
        intro a; induction a with
        | zero =>
          intro b hb hbr h0b
          have h1 : u₀ ∈ M.verts := by rw [← hx0, h0b]; exact hx_M b hb hbr
          exact (Finset.mem_compl.mp hu₀I) (Set.mem_toFinset.mpr h1)
        | succ a' ih =>
          intro b hb hbr hab
          obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
          rw [hxsucc, hxsucc] at hab
          have hp_eq : p (x a') = p (x b') := by
            have := congrArg m hab
            rwa [hm_inv _ (hpx_M a' (by omega)), hm_inv _ (hpx_M b' (by omega))] at this
          have hx_eq : x a' = x b' := by
            have := congrArg p hp_eq
            rwa [hp_inv, hp_inv] at this
          exact ih b' (by omega) (by omega) hx_eq
      rcases lt_or_gt_of_ne hne with h | h
      · exact hdesc i j h hj heq
      · exact hdesc j i h hi heq.symm
    have hx_ne_px : ∀ d : ℕ, ∀ i ≤ r, ∀ j ≤ r, j - i = d → i ≤ j → x i ≠ p (x j) := by
      intro d
      induction d using Nat.strong_induction_on with
      | ind d ih =>
        intro i hi j hj hdiff hij heq
        by_cases hd0 : d = 0
        · have hij_eq : i = j := by omega
          subst hij_eq; exact (hp_adj (x i)).ne heq
        · by_cases hd1 : d = 1
          · have hj_eq : j = i + 1 := by omega
            subst hj_eq
            have h1 : p (x i) = x (i + 1) := by
              have := congrArg p heq; rwa [hp_inv] at this
            rw [hxsucc] at h1
            exact (hm_adj (p (x i)) (hpx_M i (by omega))).ne h1
          · have hj1 : 0 < j := by omega
            obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
            have h1 : p (x i) = m (p (x j')) := by
              have := congrArg p heq; rwa [hp_inv, hxsucc] at this
            have h2 : x (i + 1) = p (x j') := by
              rw [hxsucc, h1, hm_inv _ (hpx_M j' (by omega))]
            exact ih (d - 2) (by omega) (i + 1) (by omega) j' (by omega) (by omega) (by omega) h2
    have hx_ne_px_all : ∀ i ≤ r, ∀ j ≤ r, x i ≠ p (x j) := by
      intro i hi j hj heq
      rcases le_total i j with hij | hji
      · exact hx_ne_px (j - i) i hi j hj rfl hij heq
      · have h' : x j = p (x i) := by have := congrArg p heq; rw [hp_inv] at this; exact this.symm
        exact hx_ne_px (i - j) j hj i hi rfl hji h'
    let Sx : Finset V := (Finset.range (r + 1)).image x
    let Sp : Finset V := (Finset.range (r + 1)).image (fun i => p (x i))
    let Spath : Finset V := Sx ∪ Sp
    have hp_Spath : ∀ v ∈ Spath, p v ∈ Spath := by
      intro v hv; rw [Finset.mem_union] at hv ⊢
      rcases hv with hvx | hvp
      · rw [Finset.mem_image] at hvx; obtain ⟨i, hi, rfl⟩ := hvx
        exact Or.inr (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      · rw [Finset.mem_image] at hvp; obtain ⟨i, hi, rfl⟩ := hvp
        rw [hp_inv]; exact Or.inl (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    have hm_Spath : ∀ v ∈ M.verts, (v ∈ Spath ↔ m v ∈ Spath) := by
      have hdir : ∀ v ∈ M.verts, v ∈ Spath → m v ∈ Spath := by
        intro v hvM hvS; rw [Finset.mem_union] at hvS
        rcases hvS with hvx | hvp
        · rw [Finset.mem_image] at hvx; obtain ⟨i, hi, rfl⟩ := hvx
          have hi_pos : 0 < i := by
            by_contra h0; have : i = 0 := by omega
            subst this; exact (Finset.mem_compl.mp hu₀I) (Set.mem_toFinset.mpr hvM)
          obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
          rw [hxsucc, hm_inv _ (hpx_M i' (by rw [Finset.mem_range] at hi; omega))]
          exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i', Finset.mem_range.mpr (by rw [Finset.mem_range] at hi; omega), rfl⟩)
        · rw [Finset.mem_image] at hvp; obtain ⟨i, hi, rfl⟩ := hvp
          have hi_lt : i < r := by
            rw [Finset.mem_range] at hi
            by_contra hge; have hir : i = r := by omega
            subst hir; exact (Finset.mem_compl.mp hpr_I) (Set.mem_toFinset.mpr hvM)
          exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i + 1, Finset.mem_range.mpr (by omega), rfl⟩)
      intro v hvM
      exact ⟨hdir v hvM, fun hmv => by
        have h1 := hdir (m v) (hm_adj v hvM).snd_mem hmv
        rwa [hm_inv v hvM] at h1⟩
    -- Build the (k+1)-matching M₁ on M.verts ∪ {u₀, p (x r)}!
    let V1 : Set V := insert u₀ (insert (p (x r)) M.verts)
    have hSpath_sub : ∀ v ∈ Spath, v ∈ V1 := by
      intro v hv; rw [Finset.mem_union] at hv
      rcases hv with hvx | hvp
      · rw [Finset.mem_image] at hvx; obtain ⟨i, hi, rfl⟩ := hvx
        rw [Finset.mem_range] at hi
        by_cases hi0 : i = 0
        · subst hi0; exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (hx_M i (by omega) (by omega)))
      · rw [Finset.mem_image] at hvp; obtain ⟨i, hi, rfl⟩ := hvp
        rw [Finset.mem_range] at hi
        by_cases hir : i = r
        · subst hir; exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
        · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (hpx_M i (by omega)))
    let M₁ : G.Subgraph := {
      verts := V1
      Adj := fun u v => (u ∈ Spath ∧ v ∈ Spath ∧ P₀.Adj u v) ∨ (u ∉ Spath ∧ v ∉ Spath ∧ M.Adj u v)
      adj_sub := by rintro u v (⟨_, _, h⟩ | ⟨_, _, h⟩); exact h.adj_sub; exact h.adj_sub
      edge_vert := by
        rintro u v (⟨hu, _, _⟩ | ⟨_, _, h⟩)
        · exact hSpath_sub u hu
        · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ h.fst_mem)
      symm := ⟨by rintro u v (⟨hu, hv, h⟩ | ⟨hu, hv, h⟩); exact Or.inl ⟨hv, hu, h.symm⟩; exact Or.inr ⟨hv, hu, h.symm⟩⟩
    }
    have hM₁ : M₁.IsMatching := by
      intro v hv
      by_cases hvS : v ∈ Spath
      · refine ⟨p v, Or.inl ⟨hvS, hp_Spath v hvS, hp_adj v⟩, ?_⟩
        rintro w (⟨_, _, hPw⟩ | ⟨hnot, _, _⟩)
        · exact hp_uniq v w hPw
        · exact absurd hvS hnot
      · have hvM : v ∈ M.verts := by
          rcases hv with rfl | rfl | hvM
          · exact absurd (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨0, by simp, rfl⟩)) hvS
          · exact absurd (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r, by simp, rfl⟩)) hvS
          · exact hvM
        obtain ⟨w, hvw, huniq⟩ := hM hvM
        have hw_eq : w = m v := hM.eq_of_adj_left hvw (hm_adj v hvM)
        have hwS : w ∉ Spath := fun h => hvS ((hm_Spath v hvM).mpr (hw_eq ▸ h))
        refine ⟨w, Or.inr ⟨hvS, hwS, hvw⟩, ?_⟩
        rintro z (⟨hzS, _, _⟩ | ⟨_, _, hMz⟩)
        · exact absurd hzS hvS
        · exact huniq z hMz
    have hu0_ne_pr : u₀ ≠ p (x r) := hx_ne_px_all 0 (Nat.zero_le r) r le_rfl
    have hM₁fin : M₁.verts.toFinset = insert u₀ (insert (p (x r)) VM) := by
      ext t; simp [M₁, V1, VM]
    have hM₁v := isMatching_verts_ncard hM₁
    have hM₁card_v : M₁.verts.ncard = 2 * (k + 1) := by
      rw [Set.ncard_eq_toFinset_card', hM₁fin,
        Finset.card_insert_of_notMem (by simp [hu0_ne_pr, Finset.mem_compl.mp hu₀I]),
        Finset.card_insert_of_notMem (Finset.mem_compl.mp hpr_I), hVMcard]
      omega
    obtain ⟨P₁, hM₁P₁, hP₁⟩ := hE M₁ hM₁ (by omega)
    have hrem_ne : (M₁.verts.toFinsetᶜ : Finset V).Nonempty := by
      refine Finset.card_pos.mp ?_
      rw [Finset.card_compl]
      have : M₁.verts.toFinset.card = 2 * (k + 1) := by rwa [Set.ncard_eq_toFinset_card'] at hM₁card_v
      omega
    obtain ⟨w, hw⟩ := hrem_ne
    have hw_notM₁ : w ∉ M₁.verts := fun h => (Finset.mem_compl.mp hw) (Set.mem_toFinset.mpr h)
    obtain ⟨w', hww', _⟩ := hP₁.1 (hP₁.2 w)
    have hw'_notM₁ : w' ∉ M₁.verts := by
      intro hw'M₁
      obtain ⟨z, hzw', _⟩ := hM₁ hw'M₁
      have hzw : z = w := hP₁.1.eq_of_adj_left (hM₁P₁.2 hzw') hww'.symm
      subst hzw; exact hw_notM₁ hzw'.snd_mem
    have hwI : w ∈ I := Finset.mem_compl.mpr fun h => hw_notM₁ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_toFinset.mp h)))
    have hw'I : w' ∈ I := Finset.mem_compl.mpr fun h => hw'_notM₁ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_toFinset.mp h)))
    exact hI_ind w hwI w' hw'I hww'.adj_sub

/-- A graph with an isolated odd component (no edges to its complement) has no PM. -/
lemma not_hasPM_of_odd_isolated {G : SimpleGraph V} {A : Finset V}
    (hodd : Odd A.card) (hiso : ∀ a ∈ A, ∀ b ∉ A, ¬ G.Adj a b) :
    ¬ HasPM G := by
  rintro ⟨P, hPM, hPspan⟩
  let M : G.Subgraph := {
    verts := (A : Set V)
    Adj := fun u v => u ∈ A ∧ v ∈ A ∧ P.Adj u v
    adj_sub := fun h => h.2.2.adj_sub
    edge_vert := fun h => h.1
    symm := ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩
  }
  have hM : M.IsMatching := by
    intro a ha
    obtain ⟨b, hab, huniq⟩ := hPM (hPspan a)
    have hbA : b ∈ A := by
      by_contra hnot; exact hiso a ha b hnot hab.adj_sub
    exact ⟨b, ⟨ha, hbA, hab⟩, fun z hz => huniq z hz.2.2⟩
  have h1 := isMatching_verts_ncard hM
  change (A : Set V).ncard = 2 * M.edgeSet.ncard at h1
  rw [Set.ncard_coe_finset] at h1
  obtain ⟨m, hm⟩ := hodd
  omega

/-- Helper: build a matching subgraph of `G` from an injective map `f : S' → V` sending each
`s ∈ S'` to an adjacent vertex outside `S'`. -/
lemma exists_matching_of_inj_disjoint {G : SimpleGraph V} {S' T : Finset V}
    (hdisj : Disjoint S' T) (f : S' → V) (hinj : Function.Injective f)
    (hfT : ∀ s : S', f s ∈ T) (hfAdj : ∀ s : S', G.Adj s.val (f s)) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = S'.card ∧
      M.verts = ((S' ∪ Finset.univ.image f : Finset V) : Set V) := by
  classical
  let Im : Finset V := Finset.univ.image f
  have hdisj' : Disjoint S' Im := Disjoint.mono_right (fun x hx => by
    rw [Finset.mem_image] at hx; obtain ⟨s, _, rfl⟩ := hx; exact hfT s) hdisj
  let M : G.Subgraph := {
    verts := ((S' ∪ Im : Finset V) : Set V)
    Adj := fun u v => (∃ (hu : u ∈ S'), v = f ⟨u, hu⟩) ∨ (∃ (hv : v ∈ S'), u = f ⟨v, hv⟩)
    adj_sub := by
      rintro u v (⟨hu, rfl⟩ | ⟨hv, rfl⟩)
      · exact hfAdj ⟨u, hu⟩
      · exact (hfAdj ⟨v, hv⟩).symm
    edge_vert := by
      rintro u v (⟨hu, _⟩ | ⟨hv, rfl⟩)
      · exact Finset.mem_union_left Im hu
      · exact Finset.mem_union_right S' (Finset.mem_image.mpr ⟨⟨v, hv⟩, Finset.mem_univ _, rfl⟩)
    symm := ⟨by rintro u v (h | h); exact Or.inr h; exact Or.inl h⟩
  }
  have hM : M.IsMatching := by
    intro v hv
    rw [Finset.mem_coe, Finset.mem_union] at hv
    rcases hv with hvS | hvIm
    · refine ⟨f ⟨v, hvS⟩, Or.inl ⟨hvS, rfl⟩, ?_⟩
      rintro w (⟨_, rfl⟩ | ⟨hwS, hveq⟩)
      · rfl
      · exfalso; exact Finset.disjoint_left.mp hdisj' hvS (hveq ▸ Finset.mem_image.mpr ⟨⟨w, hwS⟩, Finset.mem_univ _, rfl⟩)
    · rw [Finset.mem_image] at hvIm; obtain ⟨⟨s, hsS⟩, _, rfl⟩ := hvIm
      refine ⟨s, Or.inr ⟨hsS, rfl⟩, ?_⟩
      rintro w (⟨hfS, _⟩ | ⟨hwS, hfeq⟩)
      · exfalso; exact Finset.disjoint_left.mp hdisj' hfS (Finset.mem_image.mpr ⟨⟨s, hsS⟩, Finset.mem_univ _, rfl⟩)
      · exact congrArg Subtype.val (hinj hfeq.symm)
  have hMv := isMatching_verts_ncard hM
  have hVcard : M.verts.ncard = 2 * S'.card := by
    change ((S' ∪ Im : Finset V) : Set V).ncard = 2 * S'.card
    rw [Set.ncard_coe_finset, Finset.card_union_of_disjoint hdisj',
      Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe]
    omega
  exact ⟨M, hM, by omega, rfl⟩

/-- Inductive step of **Plummer (1980), Theorem 4.2**: for `k ≥ 1`, a `k`-connected `k`-extendable
graph on `ν ≥ 2k + 2` vertices is `(k + 1)`-connected. -/
lemma isKConnected_succ_of_isKExtendable {G : SimpleGraph V} {k : ℕ}
    (hk : 1 ≤ k) (hconn : IsKConnected G k) (hext : IsKExtendable G k)
    (hcard : 2 * k + 2 ≤ Fintype.card V) :
    IsKConnected G (k + 1) := by
  classical
  intro S A B hSlt hAne hBne hAB hSA hSB hun
  by_contra hnoAB
  push Not at hnoAB
  have hSk : S.card = k := by
    by_contra hne
    obtain ⟨a, ha, b, hb, hab⟩ := hconn S A B (by omega) hAne hBne hAB hSA hSB hun
    exact hnoAB a ha b hb hab
  have htot : S.card + A.card + B.card = Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hSA,
      ← Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hSB, hAB⟩),
      hun, Finset.card_univ]
  -- Hall helper: any subset S' ⊆ S with |S'| ≤ |X| matches into X (for X ∈ {A, B})!
  have hall_into : ∀ (X Y : Finset V), X.Nonempty → Y.Nonempty →
      Disjoint X Y → Disjoint S X → Disjoint S Y → S ∪ X ∪ Y = Finset.univ →
      (∀ x ∈ X, ∀ y ∈ Y, ¬ G.Adj x y) →
      ∀ S' ⊆ S, S'.card ≤ X.card →
      ∃ f : S' → V, Function.Injective f ∧ ∀ s : S', f s ∈ X ∧ G.Adj s.val (f s) := by
    intro X Y _ hYne hXY hSX hSY hSXY hnoXY S' hS'S hleX
    let t : S' → Finset V := fun s => G.neighborFinset s.val ∩ X
    have hHall : ∀ T : Finset S', T.card ≤ (T.biUnion t).card := by
      intro T
      by_cases hTe : T = ∅
      · simp [hTe]
      let N := T.biUnion t
      have hNX : N ⊆ X := by
        intro x hx; rw [Finset.mem_biUnion] at hx; obtain ⟨s, _, hsx⟩ := hx
        exact (Finset.mem_inter.mp hsx).2
      by_cases hNeq : N = X
      · rw [show T.biUnion t = N from rfl, hNeq]
        have hTle : T.card ≤ S'.card := by
          have := Finset.card_le_univ T; rwa [Fintype.card_coe] at this
        omega
      by_contra hlt
      push Not at hlt
      let T' : Finset V := T.image Subtype.val
      have hT'card : T'.card = T.card := Finset.card_image_of_injective T Subtype.val_injective
      have hT'S : T' ⊆ S := fun v hv => by
        rw [Finset.mem_image] at hv; obtain ⟨s, _, rfl⟩ := hv; exact hS'S s.property
      let C : Finset V := (S \ T') ∪ N
      let A' : Finset V := X \ N
      let B' : Finset V := Y ∪ T'
      have hdisj_SN : Disjoint (S \ T') N := Disjoint.mono Finset.sdiff_subset hNX hSX
      have hCcard : C.card < k := by
        have hTleS : T'.card ≤ S.card := Finset.card_le_card hT'S
        have hNlt : N.card < T.card := hlt
        rw [Finset.card_union_of_disjoint hdisj_SN, Finset.card_sdiff_of_subset hT'S]; omega
      have hA'ne : A'.Nonempty := by
        refine Finset.ne_empty_iff_nonempty.mp fun h => hNeq ?_
        exact Finset.Subset.antisymm hNX (Finset.sdiff_eq_empty_iff_subset.mp h)
      have hB'ne : B'.Nonempty := hYne.mono Finset.subset_union_left
      have hA'B' : Disjoint A' B' := Finset.disjoint_union_right.mpr
        ⟨Disjoint.mono_left Finset.sdiff_subset hXY, Disjoint.mono Finset.sdiff_subset hT'S hSX.symm⟩
      have hCA' : Disjoint C A' := Finset.disjoint_union_left.mpr
        ⟨Disjoint.mono Finset.sdiff_subset Finset.sdiff_subset hSX, disjoint_sdiff_self_right⟩
      have hCB' : Disjoint C B' := Finset.disjoint_union_left.mpr
        ⟨Finset.disjoint_union_right.mpr ⟨Disjoint.mono_left Finset.sdiff_subset hSY, disjoint_sdiff_self_left⟩,
         Finset.disjoint_union_right.mpr ⟨Disjoint.mono_left hNX hXY, Disjoint.mono hNX hT'S hSX.symm⟩⟩
      have hCun : C ∪ A' ∪ B' = Finset.univ := by
        ext v; simp only [C, A', B', Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, iff_true]
        have hv : v ∈ S ∪ X ∪ Y := hSXY ▸ Finset.mem_univ v
        simp only [Finset.mem_union] at hv
        by_cases hvT' : v ∈ T'
        · exact Or.inr (Or.inr hvT')
        · by_cases hvN : v ∈ N
          · exact Or.inl (Or.inl (Or.inr hvN))
          · rcases hv with (hvS | hvX) | hvY
            · exact Or.inl (Or.inl (Or.inl ⟨hvS, hvT'⟩))
            · exact Or.inl (Or.inr ⟨hvX, hvN⟩)
            · exact Or.inr (Or.inl hvY)
      obtain ⟨x, hxA', y, hyB', hxyG⟩ := hconn C A' B' hCcard hA'ne hB'ne hA'B' hCA' hCB' hCun
      have hxX : x ∈ X := (Finset.mem_sdiff.mp hxA').1
      have hxN : x ∉ N := (Finset.mem_sdiff.mp hxA').2
      rw [Finset.mem_union] at hyB'
      rcases hyB' with hyY | hyT'
      · exact hnoXY x hxX y hyY hxyG
      · rw [Finset.mem_image] at hyT'; obtain ⟨s, hsT, rfl⟩ := hyT'
        exact hxN (Finset.mem_biUnion.mpr ⟨s, hsT, Finset.mem_inter.mpr
          ⟨(SimpleGraph.mem_neighborFinset G s.val x).mpr hxyG.symm, hxX⟩⟩)
    obtain ⟨f, hinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hHall
    exact ⟨f, hinj, fun s => ⟨(Finset.mem_inter.mp (hf s)).2,
      (SimpleGraph.mem_neighborFinset G s.val (f s)).mp (Finset.mem_inter.mp (hf s)).1⟩⟩
  -- Contradiction helper: any k-matching M covering S and leaving an odd subset of X isolated
  have hkill : ∀ (X Y : Finset V), Disjoint X Y → Disjoint S X → S ∪ X ∪ Y = Finset.univ →
      (∀ x ∈ X, ∀ y ∈ Y, ¬ G.Adj x y) →
      ∀ (M : G.Subgraph), M.IsMatching → M.edgeSet.ncard = k →
      (∀ s ∈ S, s ∈ M.verts) → Odd (X \ M.verts.toFinset).card → False := by
    intro X Y hXY hSX hSXY hnoXY M hM hMcard hScov hoddX
    obtain ⟨P, hMP, hP⟩ := hext.2 M hM hMcard
    let MV := M.verts.toFinset
    have hPM_rem : HasPM (G.induce ((MVᶜ : Finset V) : Set V)) :=
      hasPM_induce_compl_of_le_pm hM hMP hP (by simp [MV])
    let AX : Finset ((MVᶜ : Finset V) : Set V) := Finset.univ.filter (fun v => v.val ∈ X)
    have hAXcard : AX.card = (X \ MV).card := by
      have him : AX.image Subtype.val = X \ MV := by
        ext v; simp only [AX, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_sdiff]
        constructor
        · rintro ⟨⟨w, hw⟩, hwX, rfl⟩; exact ⟨hwX, Finset.mem_compl.mp hw⟩
        · rintro ⟨hvX, hvMV⟩; exact ⟨⟨v, Finset.mem_compl.mpr hvMV⟩, hvX, rfl⟩
      rw [← him, Finset.card_image_of_injective _ Subtype.val_injective]
    refine not_hasPM_of_odd_isolated (A := AX) (by rw [hAXcard]; exact hoddX) ?_ hPM_rem
    intro a ha b hb hadj
    have haX : a.val ∈ X := (Finset.mem_filter.mp ha).2
    have hbX : b.val ∉ X := fun h => hb (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    have hbS : b.val ∉ S := fun h => (Finset.mem_compl.mp b.property) (Set.mem_toFinset.mpr (hScov b.val h))
    have hbY : b.val ∈ Y := by
      have := hSXY ▸ Finset.mem_univ b.val
      simp only [Finset.mem_union] at this
      tauto
    exact hnoXY a.val haX b.val hbY hadj
  -- Case 1 & 2: k < X.card (for X ∈ {A, B})
  have hcase_big : ∀ (X Y : Finset V), X.Nonempty → Y.Nonempty →
      Disjoint X Y → Disjoint S X → Disjoint S Y → S ∪ X ∪ Y = Finset.univ →
      (∀ x ∈ X, ∀ y ∈ Y, ¬ G.Adj x y) → k < X.card → False := by
    intro X Y hXne hYne hXY hSX hSY hSXY hnoXY hXbig
    obtain ⟨f, hinj, hf⟩ := hall_into X Y hXne hYne hXY hSX hSY hSXY hnoXY S Subset.rfl (by omega)
    have hSYX : S ∪ Y ∪ X = Finset.univ := by rw [← hSXY]; ext v; simp; tauto
    rcases Nat.even_or_odd Y.card with hYeven | hYodd
    · -- Y.card is even (≥ 2); pick one edge s₀ - y₀ from S to Y, match S \ {s₀} into X via f!
      have hSY_adj : ∃ s₀ ∈ S, ∃ y₀ ∈ Y, G.Adj s₀ y₀ := by
        have hun' : (∅ : Finset V) ∪ (S ∪ X) ∪ Y = Finset.univ := by rw [Finset.empty_union]; exact hSXY
        obtain ⟨u, huSX, y₀, hy₀, huy⟩ := hconn ∅ (S ∪ X) Y (by simp; omega)
          (hXne.mono Finset.subset_union_right) hYne
          (Finset.disjoint_union_left.mpr ⟨hSY, hXY⟩) (Finset.disjoint_empty_left _) (Finset.disjoint_empty_left _) hun'
        rw [Finset.mem_union] at huSX
        rcases huSX with huS | huX
        · exact ⟨u, huS, y₀, hy₀, huy⟩
        · exact absurd huy (hnoXY u huX y₀ hy₀)
      obtain ⟨s₀, hs₀S, y₀, hy₀Y, hs₀y₀⟩ := hSY_adj
      let g : S → V := fun s => if s.val = s₀ then y₀ else f s
      have hginj : Function.Injective g := by
        intro s₁ s₂ hge
        dsimp only [g] at hge
        split_ifs at hge with h1 h2 h2
        · exact Subtype.ext (h1.trans h2.symm)
        · exfalso; exact Finset.disjoint_left.mp hXY (hf s₂).1 (hge ▸ hy₀Y)
        · exfalso; exact Finset.disjoint_left.mp hXY (hf s₁).1 (hge.symm ▸ hy₀Y)
        · exact hinj hge
      have hgT : ∀ s : S, g s ∈ X ∪ Y := fun s => by
        dsimp only [g]; split_ifs
        · exact Finset.mem_union_right _ hy₀Y
        · exact Finset.mem_union_left _ (hf s).1
      have hgAdj : ∀ s : S, G.Adj s.val (g s) := fun s => by
        dsimp only [g]; split_ifs with h
        · rw [h]; exact hs₀y₀
        · exact (hf s).2
      obtain ⟨M, hM, hMcard, hMverts⟩ := exists_matching_of_inj_disjoint
        (Finset.disjoint_union_right.mpr ⟨hSX, hSY⟩) g hginj hgT hgAdj
      have hScov : ∀ s ∈ S, s ∈ M.verts := fun s hs => hMverts ▸ Finset.mem_union_left _ hs
      have hYrem : Y \ M.verts.toFinset = Y.erase y₀ := by
        ext y; simp only [Finset.mem_sdiff, Set.mem_toFinset, hMverts, Finset.mem_coe,
          Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase, not_or]
        constructor
        · rintro ⟨hyY, _, hnotim⟩
          refine ⟨fun hy0 => hnotim ⟨⟨s₀, hs₀S⟩, ?_⟩, hyY⟩
          simp [g, hy0]
        · rintro ⟨hy0, hyY⟩
          refine ⟨hyY, Finset.disjoint_right.mp hSY hyY, ?_⟩
          rintro ⟨s, hgs⟩
          dsimp only [g] at hgs
          split_ifs at hgs with hs
          · exact hy0 hgs.symm
          · exact Finset.disjoint_right.mp hXY hyY (hgs ▸ (hf s).1)
      have hYodd' : Odd (Y \ M.verts.toFinset).card := by
        rw [hYrem, Finset.card_erase_of_mem hy₀Y]
        obtain ⟨m, hm⟩ := hYeven
        have hYpos : 0 < Y.card := Finset.Nonempty.card_pos hYne
        exact ⟨m - 1, by omega⟩
      exact hkill Y X hXY.symm hSY hSYX (fun y hy x hx h => hnoXY x hx y hy h.symm)
        M hM (hSk ▸ hMcard) hScov hYodd'
    · -- Y.card is odd: match all of S into X via f!
      obtain ⟨M, hM, hMcard, hMverts⟩ := exists_matching_of_inj_disjoint hSX f hinj
        (fun s => (hf s).1) (fun s => (hf s).2)
      have hScov : ∀ s ∈ S, s ∈ M.verts := fun s hs => hMverts ▸ Finset.mem_union_left _ hs
      have hYM : Disjoint Y M.verts.toFinset := by
        rw [Finset.disjoint_left]; intro y hy hyM
        rw [Set.mem_toFinset, hMverts, Finset.mem_coe, Finset.mem_union] at hyM
        rcases hyM with hyS | hyIm
        · exact Finset.disjoint_right.mp hSY hy hyS
        · rw [Finset.mem_image] at hyIm; obtain ⟨s, _, rfl⟩ := hyIm
          exact Finset.disjoint_right.mp hXY hy (hf s).1
      have hYsdiff : Y \ M.verts.toFinset = Y := Finset.sdiff_eq_self_of_disjoint hYM
      exact hkill Y X hXY.symm hSY hSYX (fun y hy x hx h => hnoXY x hx y hy h.symm)
        M hM (hSk ▸ hMcard) hScov (hYsdiff.symm ▸ hYodd)
  by_cases hAbig : k < A.card
  · exact hcase_big A B hAne hBne hAB hSA hSB hun hnoAB hAbig
  by_cases hBbig : k < B.card
  · have hun' : S ∪ B ∪ A = Finset.univ := by rw [← hun]; ext v; simp; tauto
    exact hcase_big B A hBne hAne hAB.symm hSB hSA hun' (fun b hb a ha h => hnoAB a ha b hb h.symm) hBbig
  -- Case 3: A.card ≤ k and B.card ≤ k; match A into S via Hall, drop one vertex a₀ ∈ A, match rest of S into B!
  have hAle : A.card ≤ k := by omega
  have hall_A_into_S : ∃ f : A → V, Function.Injective f ∧ ∀ a : A, f a ∈ S ∧ G.Adj a.val (f a) := by
    let t : A → Finset V := fun a => G.neighborFinset a.val ∩ S
    have hHall : ∀ T : Finset A, T.card ≤ (T.biUnion t).card := by
      intro T
      by_cases hTe : T = ∅
      · simp [hTe]
      let N := T.biUnion t
      have hNS : N ⊆ S := by
        intro s hs; rw [Finset.mem_biUnion] at hs; obtain ⟨a, _, hsa⟩ := hs
        exact (Finset.mem_inter.mp hsa).2
      by_cases hNeq : N = S
      · rw [show T.biUnion t = N from rfl, hNeq, hSk]
        have hTle : T.card ≤ A.card := by have := Finset.card_le_univ T; rwa [Fintype.card_coe] at this
        omega
      by_contra hlt
      push Not at hlt
      let T' : Finset V := T.image Subtype.val
      have hT'card : T'.card = T.card := Finset.card_image_of_injective T Subtype.val_injective
      have hT'A : T' ⊆ A := fun v hv => by
        rw [Finset.mem_image] at hv; obtain ⟨a, _, rfl⟩ := hv; exact a.property
      let C : Finset V := (A \ T') ∪ N
      let A' : Finset V := T'
      let B' : Finset V := B ∪ (S \ N)
      have hdisj_AN : Disjoint (A \ T') N := Disjoint.mono Finset.sdiff_subset hNS hSA.symm
      have hCcard : C.card < k := by
        have hTleA : T'.card ≤ A.card := Finset.card_le_card hT'A
        have hNlt : N.card < T.card := hlt
        rw [Finset.card_union_of_disjoint hdisj_AN, Finset.card_sdiff_of_subset hT'A]; omega
      have hA'ne : A'.Nonempty := (Finset.ne_empty_iff_nonempty.mp hTe).image Subtype.val
      have hB'ne : B'.Nonempty := hBne.mono Finset.subset_union_left
      have hA'B' : Disjoint A' B' := Finset.disjoint_union_right.mpr
        ⟨Disjoint.mono_left hT'A hAB, Disjoint.mono hT'A Finset.sdiff_subset hSA.symm⟩
      have hCA' : Disjoint C A' := Finset.disjoint_union_left.mpr
        ⟨disjoint_sdiff_self_left, Disjoint.mono hNS hT'A hSA⟩
      have hCB' : Disjoint C B' := Finset.disjoint_union_left.mpr
        ⟨Finset.disjoint_union_right.mpr ⟨Disjoint.mono_left Finset.sdiff_subset hAB,
          Disjoint.mono Finset.sdiff_subset Finset.sdiff_subset hSA.symm⟩,
         Finset.disjoint_union_right.mpr ⟨Disjoint.mono_left hNS hSB, disjoint_sdiff_self_right⟩⟩
      have hCun : C ∪ A' ∪ B' = Finset.univ := by
        ext v; simp only [C, A', B', Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, iff_true]
        have hv : v ∈ S ∪ A ∪ B := hun ▸ Finset.mem_univ v
        simp only [Finset.mem_union] at hv
        by_cases hvT' : v ∈ T'
        · exact Or.inl (Or.inr hvT')
        · by_cases hvN : v ∈ N
          · exact Or.inl (Or.inl (Or.inr hvN))
          · rcases hv with (hvS | hvA) | hvB
            · exact Or.inr (Or.inr ⟨hvS, hvN⟩)
            · exact Or.inl (Or.inl (Or.inl ⟨hvA, hvT'⟩))
            · exact Or.inr (Or.inl hvB)
      obtain ⟨a, haA', b, hbB', habG⟩ := hconn C A' B' hCcard hA'ne hB'ne hA'B' hCA' hCB' hCun
      rw [Finset.mem_image] at haA'; obtain ⟨a', ha'T, rfl⟩ := haA'
      rw [Finset.mem_union] at hbB'
      rcases hbB' with hbB | hbSN
      · exact hnoAB a'.val a'.property b hbB habG
      · exact (Finset.mem_sdiff.mp hbSN).2 (Finset.mem_biUnion.mpr ⟨a', ha'T, Finset.mem_inter.mpr
          ⟨(SimpleGraph.mem_neighborFinset G a'.val b).mpr habG, (Finset.mem_sdiff.mp hbSN).1⟩⟩)
    obtain ⟨f, hinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hHall
    exact ⟨f, hinj, fun a => ⟨(Finset.mem_inter.mp (hf a)).2,
      (SimpleGraph.mem_neighborFinset G a.val (f a)).mp (Finset.mem_inter.mp (hf a)).1⟩⟩
  obtain ⟨fA, hfA_inj, hfA⟩ := hall_A_into_S
  obtain ⟨a₀, ha₀A⟩ := hAne
  let A_er : Finset V := A.erase a₀
  let SA_im : Finset V := (Finset.univ.filter (fun a : A => a.val ≠ a₀)).image fA
  have hSA_im_sub : SA_im ⊆ S := by
    intro s hs; rw [Finset.mem_image] at hs; obtain ⟨a, _, rfl⟩ := hs; exact (hfA a).1
  have hSA_im_card : SA_im.card = A.card - 1 := by
    rw [Finset.card_image_of_injective _ hfA_inj]
    have hfeq : (Finset.univ.filter (fun a : A => a.val ≠ a₀)).image Subtype.val = A_er := by
      ext v; simp [A_er, Finset.mem_erase, Finset.mem_image]
    rw [← Finset.card_image_of_injective _ Subtype.val_injective, hfeq, Finset.card_erase_of_mem ha₀A]
  let S' : Finset V := S \ SA_im
  have hS'card : S'.card = k - (A.card - 1) := by
    rw [Finset.card_sdiff_of_subset hSA_im_sub, hSk, hSA_im_card]
  have hS'leB : S'.card ≤ B.card := by omega
  have hun' : S ∪ B ∪ A = Finset.univ := by rw [← hun]; ext v; simp; tauto
  obtain ⟨fB, hfB_inj, hfB⟩ := hall_into B A hBne ⟨a₀, ha₀A⟩ hAB.symm hSB hSA hun'
    (fun b hb a ha h => hnoAB a ha b hb h.symm) S' Finset.sdiff_subset hS'leB
  -- Combine inverse of fA on SA_im (into A.erase a₀) and fB on S' (into B) to get a k-matching covering S!
  have hex_inv : ∀ s : S, s.val ∈ SA_im → ∃ a : A, a.val ≠ a₀ ∧ fA a = s.val := by
    intro s hs; rw [Finset.mem_image] at hs; obtain ⟨a, ha, he⟩ := hs
    exact ⟨a, (Finset.mem_filter.mp ha).2, he⟩
  let g : S → V := fun s =>
    if hs : s.val ∈ SA_im then (Classical.choose (hex_inv s hs)).val
    else fB ⟨s.val, Finset.mem_sdiff.mpr ⟨s.property, hs⟩⟩
  have hginj : Function.Injective g := by
    intro s₁ s₂ hge
    dsimp only [g] at hge
    split_ifs at hge with h1 h2 h2
    · have ha1 := Classical.choose_spec (hex_inv s₁ h1)
      have ha2 := Classical.choose_spec (hex_inv s₂ h2)
      have heqA : Classical.choose (hex_inv s₁ h1) = Classical.choose (hex_inv s₂ h2) := Subtype.ext hge
      exact Subtype.ext (ha1.2.symm.trans (congrArg fA heqA |>.trans ha2.2))
    · exfalso
      have ha1 := (Classical.choose (hex_inv s₁ h1)).property
      exact Finset.disjoint_left.mp hAB ha1 (hge ▸ (hfB _).1)
    · exfalso
      have ha2 := (Classical.choose (hex_inv s₂ h2)).property
      exact Finset.disjoint_left.mp hAB ha2 (hge.symm ▸ (hfB _).1)
    · have h' : (⟨s₁.val, Finset.mem_sdiff.mpr ⟨s₁.property, h1⟩⟩ : S') =
          ⟨s₂.val, Finset.mem_sdiff.mpr ⟨s₂.property, h2⟩⟩ := hfB_inj hge
      exact Subtype.ext (congrArg (fun x : S' => x.val) h')
  have hgT : ∀ s : S, g s ∈ A ∪ B := fun s => by
    dsimp only [g]; split_ifs with hs
    · exact Finset.mem_union_left _ (Classical.choose (hex_inv s hs)).property
    · exact Finset.mem_union_right _ (hfB _).1
  have hgAdj : ∀ s : S, G.Adj s.val (g s) := fun s => by
    dsimp only [g]; split_ifs with hs
    · have ha := Classical.choose_spec (hex_inv s hs)
      have h1 := (hfA (Classical.choose (hex_inv s hs))).2.symm
      rwa [ha.2] at h1
    · exact (hfB ⟨s.val, Finset.mem_sdiff.mpr ⟨s.property, hs⟩⟩).2
  obtain ⟨M, hM, hMcard, hMverts⟩ := exists_matching_of_inj_disjoint
    (Finset.disjoint_union_right.mpr ⟨hSA, hSB⟩) g hginj hgT hgAdj
  have hScov : ∀ s ∈ S, s ∈ M.verts := fun s hs => hMverts ▸ Finset.mem_union_left _ hs
  have hArem : A \ M.verts.toFinset = {a₀} := by
    ext v; simp only [Finset.mem_sdiff, Set.mem_toFinset, hMverts, Finset.mem_coe,
      Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton, not_or]
    constructor
    · rintro ⟨hvA, _, hnotim⟩
      by_contra hva0
      have hfv_in : fA ⟨v, hvA⟩ ∈ SA_im := Finset.mem_image.mpr
        ⟨⟨v, hvA⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hva0⟩, rfl⟩
      refine hnotim ⟨⟨fA ⟨v, hvA⟩, (hfA ⟨v, hvA⟩).1⟩, ?_⟩
      dsimp only [g]; simp only [hfv_in, ↓reduceDIte]
      have ha := Classical.choose_spec (hex_inv ⟨fA ⟨v, hvA⟩, (hfA ⟨v, hvA⟩).1⟩ hfv_in)
      exact congrArg Subtype.val (hfA_inj ha.2)
    · rintro rfl
      refine ⟨ha₀A, Finset.disjoint_right.mp hSA ha₀A, ?_⟩
      rintro ⟨s, hgs⟩
      dsimp only [g] at hgs
      split_ifs at hgs with hs
      · exact (Classical.choose_spec (hex_inv s hs)).1 hgs
      · exact Finset.disjoint_left.mp hAB ha₀A (hgs ▸ (hfB _).1)
  have hAodd : Odd (A \ M.verts.toFinset).card := by rw [hArem, Finset.card_singleton]; exact ⟨0, rfl⟩
  exact hkill A B hAB hSA hun hnoAB M hM (hSk ▸ hMcard) hScov hAodd

/-- **Plummer (1980), Theorem 4.2**: Every connected `k`-extendable graph on `ν ≥ 2k + 2`
vertices is `(k + 1)`-connected. -/
theorem plummer_kConnected {G : SimpleGraph V} {k : ℕ}
    (hconn : G.Connected) (hext : IsKExtendable G k)
    (hcard : 2 * k + 2 ≤ Fintype.card V) :
    IsKConnected G (k + 1) := by
  induction k with
  | zero => exact isKConnected_one_of_connected hconn
  | succ k ih =>
    have hpred : IsKExtendable G k := isKExtendable_pred hext hcard
    have hck : IsKConnected G (k + 1) := ih hpred (by omega)
    exact isKConnected_succ_of_isKExtendable (by omega) hck hext hcard

/-- **Plummer (1980) degree lower bound**: Every connected `k`-extendable graph on `ν ≥ 2k + 2`
vertices has `∀ v, k + 1 ≤ G.degree v`. -/
theorem plummer_min_degree {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hconn : G.Connected) (hext : IsKExtendable G k)
    (hcard : 2 * k + 2 ≤ Fintype.card V) :
    ∀ v : V, k + 1 ≤ G.degree v := by
  have hkconn := plummer_kConnected hconn hext hcard
  intro v
  by_contra hlt
  push Not at hlt
  let S := G.neighborFinset v
  let A : Finset V := {v}
  let B : Finset V := (insert v S)ᶜ
  have hSlt : S.card < k + 1 := by rwa [SimpleGraph.card_neighborFinset_eq_degree]
  have hvS : v ∉ S := by simp [S]
  have hBne : B.Nonempty := by
    refine Finset.card_pos.mp ?_
    rw [Finset.card_compl, Finset.card_insert_of_notMem hvS]
    omega
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]; intro x hx hxB
    rw [Finset.mem_singleton] at hx; subst hx
    exact (Finset.mem_compl.mp hxB) (Finset.mem_insert_self _ _)
  have hSA : Disjoint S A := by simp [A, hvS]
  have hSB : Disjoint S B := by
    rw [Finset.disjoint_left]; intro x hx hxB
    exact (Finset.mem_compl.mp hxB) (Finset.mem_insert_of_mem hx)
  have hun : S ∪ A ∪ B = Finset.univ := by
    ext x; simp only [A, B, Finset.mem_union, Finset.mem_singleton, Finset.mem_compl,
      Finset.mem_insert, Finset.mem_univ, iff_true]
    tauto
  obtain ⟨a, haA, b, hbB, hab⟩ := hkconn S A B hSlt ⟨v, by simp [A]⟩ hBne hAB hSA hSB hun
  rw [Finset.mem_singleton] at haA; subst haA
  exact (Finset.mem_compl.mp hbB) (Finset.mem_insert_of_mem ((SimpleGraph.mem_neighborFinset G a b).mpr hab))

/-- Every connected bipartite minimally 4-extendable graph on `ν ≤ 16` vertices has `δ(G) = 5`
(i.e. `∃ v, G.degree v = 5`). -/
theorem bipartite_min_4ext_deg_five {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcard : Fintype.card V ≤ 16) (hconn : G.Connected)
    (hmin : IsMinimallyKExtendable G 4) (hbip : IsBipartite G) :
    ∃ v : V, G.degree v = 5 := by
  classical
  obtain ⟨heven, hge8⟩ := isKExtendable_even_card_and_ge hmin.1
  have hne8 : Fintype.card V ≠ 8 := fun h => nu_ne_eight_of_connected_min_four h hconn hmin
  have hge10 : 10 ≤ Fintype.card V := by obtain ⟨m, hm⟩ := heven; omega
  have hge5 : ∀ v : V, 5 ≤ G.degree v := plummer_min_degree hconn hmin.1 (by omega)
  by_contra hno5
  push Not at hno5
  have hge6 : ∀ v : V, 6 ≤ G.degree v := fun v => by have := hge5 v; have := hno5 v; omega
  obtain ⟨X, hXind, hXcind⟩ := hbip
  -- From a PM of G, X.card = Xᶜ.card = ν / 2
  obtain ⟨⟨M₀, hM₀, hM₀card⟩, hE⟩ := hmin.1
  obtain ⟨P₀, _, hP₀⟩ := hE M₀ hM₀ hM₀card
  choose p hp_adj hp_uniq using fun v : V => hP₀.1 (hP₀.2 v)
  have hp_inv : ∀ v : V, p (p v) = v := fun v => (hp_uniq (p v) v (hp_adj v).symm).symm
  have hp_inj : Function.Injective p := Function.LeftInverse.injective hp_inv
  have hp_X : ∀ v ∈ X, p v ∈ Xᶜ := fun v hv =>
    Finset.mem_compl.mpr fun h => hXind v hv (p v) h (hp_adj v).adj_sub
  have hp_Xc : ∀ v ∈ Xᶜ, p v ∈ X := fun v hv => by
    by_contra h; exact hXcind v (Finset.mem_compl.mp hv) (p v) h (hp_adj v).adj_sub
  have hXeq : X.card = Xᶜ.card := by
    have h1 : X.card ≤ Xᶜ.card := by
      have hsub : X.image p ⊆ Xᶜ := fun w hw => by
        rw [Finset.mem_image] at hw; obtain ⟨v, hv, rfl⟩ := hw; exact hp_X v hv
      simpa [Finset.card_image_of_injective _ hp_inj] using Finset.card_le_card hsub
    have h2 : Xᶜ.card ≤ X.card := by
      have hsub : Xᶜ.image p ⊆ X := fun w hw => by
        rw [Finset.mem_image] at hw; obtain ⟨v, hv, rfl⟩ := hw; exact hp_Xc v hv
      simpa [Finset.card_image_of_injective _ hp_inj] using Finset.card_le_card hsub
    omega
  have htot : X.card + Xᶜ.card = Fintype.card V := by
    rw [← Finset.card_union_of_disjoint disjoint_compl_right, Finset.union_compl, Finset.card_univ]
  set n := X.card with hn_def
  have hn_bounds : 5 ≤ n ∧ n ≤ 8 := by omega
  -- Pick any edge u v of G with u ∈ X, v ∈ Xᶜ
  obtain ⟨u₀, hu₀X⟩ : X.Nonempty := Finset.card_pos.mp (by omega)
  let v₀ := p u₀
  have hv₀Xc : v₀ ∈ Xᶜ := hp_X u₀ hu₀X
  have huv₀ : G.Adj u₀ v₀ := (hp_adj u₀).adj_sub
  let G' := G.deleteEdges {s(u₀, v₀)}
  -- Show G' is STILL 4-extendable, contradicting hmin.2!
  apply hmin.2 s(u₀, v₀) huv₀
  -- First, G' has a 4-matching (take 4 edges from P₀ \ {u₀ v₀}; since n ≥ 5, X.erase u₀ has ≥ 4 vertices!)
  have hex4 : ∃ M : G'.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = 4 := by
    have h4le : 4 ≤ (X.erase u₀).card := by rw [Finset.card_erase_of_mem hu₀X]; omega
    obtain ⟨S₄, hS₄sub, hS₄card⟩ := Finset.exists_subset_card_eq h4le
    have hdisj : Disjoint S₄ Xᶜ := Disjoint.mono_left (hS₄sub.trans (Finset.erase_subset _ _)) disjoint_compl_right
    obtain ⟨M, hM, hMcard, _⟩ := exists_matching_of_inj_disjoint (G := G') hdisj
      (fun x : S₄ => p x.val) (fun a b h => Subtype.ext (hp_inj h))
      (fun x => hp_X x.val (Finset.mem_of_mem_erase (hS₄sub x.property)))
      (fun x => by
        rw [SimpleGraph.deleteEdges_adj]
        refine ⟨(hp_adj x.val).adj_sub, ?_⟩
        intro heq
        rw [Set.mem_singleton_iff, Sym2.eq_iff] at heq
        have hxu0 : x.val ≠ u₀ := (Finset.mem_erase.mp (hS₄sub x.property)).1
        rcases heq with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact hxu0 h1
        · exact (Finset.mem_compl.mp hv₀Xc) (h1 ▸ Finset.mem_of_mem_erase (hS₄sub x.property)))
    exact ⟨M, hM, hS₄card ▸ hMcard⟩
  refine ⟨hex4, fun M hM hMcard => ?_⟩
  -- For any 4-matching M of G', let A = X \ M.verts and B = Xᶜ \ M.verts; both have card s = n - 4 ∈ {1,2,3,4}!
  let MV := M.verts.toFinset
  let A : Finset V := X \ MV
  let B : Finset V := Xᶜ \ MV
  have hMXeq : (X ∩ MV).card = (Xᶜ ∩ MV).card := by
    choose m hm_adj hm_uniq using fun v : M.verts => hM v.property
    have hsub1 : (X ∩ MV).card ≤ (Xᶜ ∩ MV).card := by
      let f : {v : V // v ∈ X ∩ MV} → V := fun v => m ⟨v.val, Set.mem_toFinset.mp (Finset.mem_inter.mp v.property).2⟩
      have hfinj : Function.Injective f := by
        intro a b hab
        have h1 := hm_adj ⟨a.val, Set.mem_toFinset.mp (Finset.mem_inter.mp a.property).2⟩
        have h2 := hm_adj ⟨b.val, Set.mem_toFinset.mp (Finset.mem_inter.mp b.property).2⟩
        dsimp only [f] at hab
        rw [hab] at h1
        exact Subtype.ext (hM.eq_of_adj_right h1 h2)
      have hfsub : Finset.univ.image f ⊆ Xᶜ ∩ MV := by
        intro w hw; rw [Finset.mem_image] at hw; obtain ⟨v, _, rfl⟩ := hw
        have hadj := hm_adj ⟨v.val, Set.mem_toFinset.mp (Finset.mem_inter.mp v.property).2⟩
        refine Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr fun hwX =>
          hXind v.val (Finset.mem_inter.mp v.property).1 _ hwX hadj.adj_sub.1, Set.mem_toFinset.mpr hadj.snd_mem⟩
      simpa [Finset.card_image_of_injective _ hfinj] using Finset.card_le_card hfsub
    have hsub2 : (Xᶜ ∩ MV).card ≤ (X ∩ MV).card := by
      let f : {v : V // v ∈ Xᶜ ∩ MV} → V := fun v => m ⟨v.val, Set.mem_toFinset.mp (Finset.mem_inter.mp v.property).2⟩
      have hfinj : Function.Injective f := by
        intro a b hab
        have h1 := hm_adj ⟨a.val, Set.mem_toFinset.mp (Finset.mem_inter.mp a.property).2⟩
        have h2 := hm_adj ⟨b.val, Set.mem_toFinset.mp (Finset.mem_inter.mp b.property).2⟩
        dsimp only [f] at hab
        rw [hab] at h1
        exact Subtype.ext (hM.eq_of_adj_right h1 h2)
      have hfsub : Finset.univ.image f ⊆ X ∩ MV := by
        intro w hw; rw [Finset.mem_image] at hw; obtain ⟨v, _, rfl⟩ := hw
        have hadj := hm_adj ⟨v.val, Set.mem_toFinset.mp (Finset.mem_inter.mp v.property).2⟩
        refine Finset.mem_inter.mpr ⟨?_, Set.mem_toFinset.mpr hadj.snd_mem⟩
        by_contra hwX
        exact hXcind v.val (Finset.mem_compl.mp (Finset.mem_inter.mp v.property).1) _ hwX hadj.adj_sub.1
      simpa [Finset.card_image_of_injective _ hfinj] using Finset.card_le_card hfsub
    omega
  have hMV8 : MV.card = 8 := by
    have h1 := isMatching_verts_ncard hM; rw [hMcard, Set.ncard_eq_toFinset_card'] at h1; exact h1
  have hMVpart : (X ∩ MV).card + (Xᶜ ∩ MV).card = 8 := by
    rw [← Finset.card_union_of_disjoint (Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left disjoint_compl_right)]
    have heq : X ∩ MV ∪ Xᶜ ∩ MV = MV := by ext v; simp; tauto
    rw [heq, hMV8]
  have hAcard : A.card = n - 4 := by
    have := Finset.card_sdiff_add_card_inter X MV; dsimp only [A]; omega
  have hBcard : B.card = n - 4 := by
    have := Finset.card_sdiff_add_card_inter Xᶜ MV; dsimp only [B]; omega
  have hn6 : 6 ≤ n := by
    have hsub : G.neighborFinset u₀ ⊆ Xᶜ := fun w hw =>
      Finset.mem_compl.mpr fun hwX => hXind u₀ hu₀X w hwX ((SimpleGraph.mem_neighborFinset G u₀ w).mp hw)
    have hc := Finset.card_le_card hsub
    rw [SimpleGraph.card_neighborFinset_eq_degree] at hc
    have := hge6 u₀; omega
  -- Non-degree bounds in G'
  have hG'_degX : ∀ a ∈ X, (Xᶜ.filter (fun b => ¬ G'.Adj a b)).card ≤ (if a = u₀ then n - 5 else n - 6) := by
    intro a ha
    have hNGsub : G.neighborFinset a ⊆ Xᶜ := fun w hw =>
      Finset.mem_compl.mpr fun hwX => hXind a ha w hwX ((SimpleGraph.mem_neighborFinset G a w).mp hw)
    have hmissG : (Xᶜ \ G.neighborFinset a).card ≤ n - 6 := by
      rw [Finset.card_sdiff_of_subset hNGsub, SimpleGraph.card_neighborFinset_eq_degree]
      have := hge6 a; omega
    split_ifs with hau
    · subst hau
      have hsub : Xᶜ.filter (fun b => ¬ G'.Adj a b) ⊆ insert v₀ (Xᶜ \ G.neighborFinset a) := by
        intro b hb; rw [Finset.mem_filter] at hb
        by_cases hbv : b = v₀
        · exact Finset.mem_insert.mpr (Or.inl hbv)
        · refine Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hb.1, fun hN => hb.2 ?_⟩)
          rw [SimpleGraph.deleteEdges_adj]
          refine ⟨(SimpleGraph.mem_neighborFinset G a b).mp hN, ?_⟩
          intro heq; rw [Set.mem_singleton_iff, Sym2.eq_iff] at heq
          rcases heq with ⟨_, rfl⟩ | ⟨_, h2⟩
          · exact hbv rfl
          · exact (Finset.mem_compl.mp hb.1) (h2 ▸ ha)
      have hc := Finset.card_le_card hsub
      have hi := Finset.card_insert_le v₀ (Xᶜ \ G.neighborFinset a)
      omega
    · have hsub : Xᶜ.filter (fun b => ¬ G'.Adj a b) ⊆ Xᶜ \ G.neighborFinset a := by
        intro b hb; rw [Finset.mem_filter] at hb
        refine Finset.mem_sdiff.mpr ⟨hb.1, fun hN => hb.2 ?_⟩
        rw [SimpleGraph.deleteEdges_adj]
        refine ⟨(SimpleGraph.mem_neighborFinset G a b).mp hN, ?_⟩
        intro heq; rw [Set.mem_singleton_iff, Sym2.eq_iff] at heq
        rcases heq with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact hau h1
        · exact (Finset.mem_compl.mp hv₀Xc) (h1 ▸ ha)
      exact le_trans (Finset.card_le_card hsub) hmissG
  have hG'_degXc : ∀ b ∈ Xᶜ, (X.filter (fun a => ¬ G'.Adj a b)).card ≤ (if b = v₀ then n - 5 else n - 6) := by
    intro b hb
    have hNGsub : G.neighborFinset b ⊆ X := fun w hw => by
      by_contra hwX; exact hXcind b (Finset.mem_compl.mp hb) w hwX ((SimpleGraph.mem_neighborFinset G b w).mp hw)
    have hmissG : (X \ G.neighborFinset b).card ≤ n - 6 := by
      rw [Finset.card_sdiff_of_subset hNGsub, SimpleGraph.card_neighborFinset_eq_degree]
      have := hge6 b; omega
    split_ifs with hbv
    · have hsub : X.filter (fun a => ¬ G'.Adj a b) ⊆ insert u₀ (X \ G.neighborFinset b) := by
        intro a ha; rw [Finset.mem_filter] at ha
        by_cases hau : a = u₀
        · exact Finset.mem_insert.mpr (Or.inl hau)
        · refine Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨ha.1, fun hN => ha.2 ?_⟩)
          rw [SimpleGraph.deleteEdges_adj]
          refine ⟨((SimpleGraph.mem_neighborFinset G b a).mp hN).symm, ?_⟩
          intro heq; rw [Set.mem_singleton_iff, Sym2.eq_iff] at heq
          rcases heq with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact hau h1
          · exact (Finset.mem_compl.mp hv₀Xc) (h1 ▸ ha.1)
      have hc := Finset.card_le_card hsub
      have hi := Finset.card_insert_le u₀ (X \ G.neighborFinset b)
      omega
    · have hsub : X.filter (fun a => ¬ G'.Adj a b) ⊆ X \ G.neighborFinset b := by
        intro a ha; rw [Finset.mem_filter] at ha
        refine Finset.mem_sdiff.mpr ⟨ha.1, fun hN => ha.2 ?_⟩
        rw [SimpleGraph.deleteEdges_adj]
        refine ⟨((SimpleGraph.mem_neighborFinset G b a).mp hN).symm, ?_⟩
        intro heq; rw [Set.mem_singleton_iff, Sym2.eq_iff] at heq
        rcases heq with ⟨_, h2⟩ | ⟨_, h2⟩
        · exact hbv h2
        · exact (Finset.mem_compl.mp hb) (h2 ▸ hu₀X)
      exact le_trans (Finset.card_le_card hsub) hmissG
  -- Hall's condition for matching A into B in G'!
  let t : A → Finset V := fun a => B.filter (fun b => G'.Adj a.val b)
  have hHall : ∀ T : Finset A, T.card ≤ (T.biUnion t).card := by
    intro T
    by_cases hT0 : T.card = 0
    · omega
    have hTsubA : T.card ≤ n - 4 := by
      have := Finset.card_le_univ T; rwa [Fintype.card_coe, hAcard] at this
    by_cases hT1 : T.card = 1
    · obtain ⟨a, haT⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
      have hmiss : (B \ t a).card ≤ n - 5 := by
        have hsub : B \ t a ⊆ Xᶜ.filter (fun b => ¬ G'.Adj a.val b) := by
          intro b hb; simp only [t, Finset.mem_sdiff, Finset.mem_filter] at hb ⊢
          exact ⟨(Finset.mem_sdiff.mp hb.1).1, fun h => hb.2 ⟨hb.1, h⟩⟩
        have h1 := hG'_degX a.val (Finset.mem_sdiff.mp a.property).1
        have h2 := Finset.card_le_card hsub
        split_ifs at h1 <;> omega
      have hta_sub : t a ⊆ B := Finset.filter_subset _ _
      have hta_le : t a ⊆ T.biUnion t := fun b hb => Finset.mem_biUnion.mpr ⟨a, haT, hb⟩
      have h1 := Finset.card_sdiff_of_subset hta_sub
      have h2 := Finset.card_le_card hta_le
      omega
    by_cases hT2 : T.card = 2
    · -- T contains some a with a.val ≠ u₀!
      have hex_ne : ∃ a ∈ T, a.val ≠ u₀ := by
        by_contra hall; push Not at hall
        have hle1 : T.card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb => Subtype.ext ((hall a ha).trans (hall b hb).symm)
        omega
      obtain ⟨a, haT, hau⟩ := hex_ne
      have hmiss : (B \ t a).card ≤ n - 6 := by
        have hsub : B \ t a ⊆ Xᶜ.filter (fun b => ¬ G'.Adj a.val b) := by
          intro b hb; simp only [t, Finset.mem_sdiff, Finset.mem_filter] at hb ⊢
          exact ⟨(Finset.mem_sdiff.mp hb.1).1, fun h => hb.2 ⟨hb.1, h⟩⟩
        have h1 := hG'_degX a.val (Finset.mem_sdiff.mp a.property).1
        simp only [hau, ↓reduceIte] at h1
        exact le_trans (Finset.card_le_card hsub) h1
      have hta_sub : t a ⊆ B := Finset.filter_subset _ _
      have hta_le : t a ⊆ T.biUnion t := fun b hb => Finset.mem_biUnion.mpr ⟨a, haT, hb⟩
      have h1 := Finset.card_sdiff_of_subset hta_sub
      have h2 := Finset.card_le_card hta_le
      omega
    · -- T.card ≥ 3 (so n ∈ {7, 8}): every b ∈ B \ (T.biUnion t) has ≥ T.card non-neighbors in X!
      have hT3 : 3 ≤ T.card := by omega
      have hNsub : T.biUnion t ⊆ B := by
        intro b hb; rw [Finset.mem_biUnion] at hb; obtain ⟨a, _, hab⟩ := hb
        exact (Finset.mem_filter.mp hab).1
      have hmiss_all : ∀ b ∈ B \ T.biUnion t, T.card ≤ (if b = v₀ then n - 5 else n - 6) := by
        intro b hb
        have hbB : b ∈ B := (Finset.mem_sdiff.mp hb).1
        have hbN : b ∉ T.biUnion t := (Finset.mem_sdiff.mp hb).2
        have hsub : T.image Subtype.val ⊆ X.filter (fun a => ¬ G'.Adj a b) := by
          intro a ha; rw [Finset.mem_image] at ha; obtain ⟨a', ha'T, rfl⟩ := ha
          refine Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp a'.property).1, fun hadj => hbN ?_⟩
          exact Finset.mem_biUnion.mpr ⟨a', ha'T, Finset.mem_filter.mpr ⟨hbB, hadj⟩⟩
        have h1 := Finset.card_le_card hsub
        rw [Finset.card_image_of_injective _ Subtype.val_injective] at h1
        exact le_trans h1 (hG'_degXc b (Finset.mem_sdiff.mp hbB).1)
      have hmiss_le : (B \ T.biUnion t).card ≤ if T.card = 3 ∧ n = 8 then 1 else 0 := by
        split_ifs with h38
        · refine Finset.card_le_one.mpr fun b₁ hb1 b₂ hb2 => ?_
          have h1 := hmiss_all b₁ hb1
          have h2 := hmiss_all b₂ hb2
          have hb1v : b₁ = v₀ := by by_contra hne; simp only [hne, ↓reduceIte] at h1; omega
          have hb2v : b₂ = v₀ := by by_contra hne; simp only [hne, ↓reduceIte] at h2; omega
          exact hb1v.trans hb2v.symm
        · refine Nat.le_zero.mpr (Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr fun b hb => ?_))
          have h1 := hmiss_all b hb
          split_ifs at h1 <;> omega
      have h1 := Finset.card_sdiff_of_subset hNsub
      split_ifs at hmiss_le <;> omega
  obtain ⟨f, hfinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hHall
  have hdisjAB : Disjoint A B := Disjoint.mono Finset.sdiff_subset Finset.sdiff_subset disjoint_compl_right
  obtain ⟨M', hM', _, hM'verts⟩ := exists_matching_of_inj_disjoint (G := G') hdisjAB f hfinj
    (fun a => (Finset.mem_filter.mp (hf a)).1) (fun a => (Finset.mem_filter.mp (hf a)).2)
  have hIm_eq : Finset.univ.image f = B := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro b hb; rw [Finset.mem_image] at hb; obtain ⟨a, _, rfl⟩ := hb; exact (Finset.mem_filter.mp (hf a)).1
    · rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_coe, hAcard, hBcard]
  have hM'v_eq : M'.verts = ((MVᶜ : Finset V) : Set V) := by
    rw [hM'verts, hIm_eq]
    ext v; simp only [A, B, Finset.mem_coe, Finset.mem_union, Finset.mem_sdiff, Finset.mem_compl]
    tauto
  have hdisjMM' : Disjoint M.support M'.support := by
    rw [hM.support_eq_verts, hM'.support_eq_verts, hM'v_eq, Finset.coe_compl]
    rw [show M.verts = (MV : Set V) by simp [MV]]
    exact disjoint_compl_right
  refine ⟨M ⊔ M', le_sup_left, hM.sup hM' hdisjMM', fun v => ?_⟩
  rw [Subgraph.verts_sup, hM'v_eq, show M.verts = (MV : Set V) by simp [MV]]
  simp [Finset.coe_compl]

end LowerAndBipartite

end LouYuK4
