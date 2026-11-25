import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Tutte
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Definitions for minimally k-extendable graphs and Lemma 3.3

We define `HasPM`, `IsKExtendable`, and `IsMinimallyKExtendable` directly on top of
Mathlib's `SimpleGraph.Subgraph.IsMatching` and `SimpleGraph.Subgraph.IsPerfectMatching`,
and establish the complementary-induced-subgraph characterization (Gan-Huang Lemma 3.3).
-/

open SimpleGraph Finset

namespace LouYuK4

variable {V : Type*}

/-- A graph `G` has a perfect matching. -/
def HasPM (G : SimpleGraph V) : Prop :=
  ∃ M : G.Subgraph, M.IsPerfectMatching

/-- A graph `G` is `k`-extendable if it has a matching of `k` edges and every matching
of `k` edges extends to a perfect matching of `G`. -/
def IsKExtendable (G : SimpleGraph V) (k : ℕ) : Prop :=
  (∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = k) ∧
  ∀ M : G.Subgraph, M.IsMatching → M.edgeSet.ncard = k →
    ∃ P : G.Subgraph, M ≤ P ∧ P.IsPerfectMatching

/-- A graph `G` is minimally `k`-extendable if it is `k`-extendable and deleting any single
edge destroys `k`-extendability. -/
def IsMinimallyKExtendable (G : SimpleGraph V) (k : ℕ) : Prop :=
  IsKExtendable G k ∧ ∀ e ∈ G.edgeSet, ¬ IsKExtendable (G.deleteEdges {e}) k

section BasicLemmas

variable [Fintype V] [DecidableEq V]

/-- A matching `M` has `|M.verts| = 2 * |M.edgeSet|`. -/
lemma isMatching_verts_ncard {G : SimpleGraph V} {M : G.Subgraph} (hM : M.IsMatching) :
    M.verts.ncard = 2 * M.edgeSet.ncard := by
  classical
  have h1 : Fintype.card M.verts = 2 * Fintype.card M.edgeSet := by
    have hsum := Finset.card_eq_sum_card_fiberwise
      (f := hM.toEdge) (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
    have hfib : ∀ e : M.edgeSet, (Finset.univ.filter (fun v : M.verts => hM.toEdge v = e)).card = 2 := by
      rintro ⟨e, he⟩
      induction e using Sym2.ind with
      | _ u v =>
        have huv : M.Adj u v := he
        have hpre := hM.toEdge_preimage_singleton huv
        have hset : (Finset.univ.filter (fun x : M.verts => hM.toEdge x = ⟨s(u, v), huv⟩) : Set M.verts) =
            {⟨u, huv.fst_mem⟩, ⟨v, huv.snd_mem⟩} := by
          ext x
          simpa using Set.ext_iff.mp hpre x
        have hne : (⟨u, huv.fst_mem⟩ : M.verts) ≠ ⟨v, huv.snd_mem⟩ := by
          intro h
          exact huv.ne (congrArg Subtype.val h)
        have hfeq : Finset.univ.filter (fun x : M.verts => hM.toEdge x = ⟨s(u, v), huv⟩) =
            {⟨u, huv.fst_mem⟩, ⟨v, huv.snd_mem⟩} := by
          ext x
          have := Set.ext_iff.mp hset x
          simpa using this
        rw [hfeq, Finset.card_pair hne]
    simp only [Finset.card_univ] at hsum
    rw [hsum, Finset.sum_congr rfl (fun e _ => hfib e), Finset.sum_const, Finset.card_univ,
      smul_eq_mul, mul_comm]
  rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
  simpa [Set.toFinset_card] using h1

omit [Fintype V] [DecidableEq V] in
/-- Induced-subgraph perfect matching from a subgraph matching supported on `S`. -/
lemma hasPM_induce_of_isMatching {G : SimpleGraph V} {M : G.Subgraph}
    (hM : M.IsMatching) {S : Finset V} (hS : M.verts = (S : Set V)) :
    HasPM (G.induce (S : Set V)) := by
  classical
  refine ⟨{
    verts := Set.univ
    Adj := fun u v => M.Adj u.val v.val
    adj_sub := fun h => h.adj_sub
    edge_vert := fun _ => Set.mem_univ _
    symm := ⟨fun _ _ h => h.symm⟩
  }, ?_, fun _ => Set.mem_univ _⟩
  intro ⟨v, hv⟩ _
  have hvM : v ∈ M.verts := hS ▸ hv
  obtain ⟨w, hvw, huniq⟩ := hM hvM
  have hwS : w ∈ (S : Set V) := hS ▸ M.edge_vert hvw.symm
  refine ⟨⟨w, hwS⟩, hvw, ?_⟩
  intro ⟨u, _⟩ hvu
  exact Subtype.ext (huniq u hvu)

omit [Fintype V] [DecidableEq V] in
/-- Convert a perfect matching on `G.induce S` to a matching subgraph of `G` with `verts = S`. -/
lemma exists_isMatching_of_hasPM_induce {G : SimpleGraph V} {S : Finset V}
    (h : HasPM (G.induce (S : Set V))) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.verts = (S : Set V) := by
  classical
  obtain ⟨P, hPM, hPspan⟩ := h
  refine ⟨{
    verts := (S : Set V)
    Adj := fun u v => ∃ (hu : u ∈ (S : Set V)) (hv : v ∈ (S : Set V)), P.Adj ⟨u, hu⟩ ⟨v, hv⟩
    adj_sub := fun ⟨_, _, h⟩ => h.adj_sub
    edge_vert := fun ⟨hu, _, _⟩ => hu
    symm := ⟨fun _ _ ⟨hu, hv, h⟩ => ⟨hv, hu, h.symm⟩⟩
  }, ?_, rfl⟩
  intro v hv
  obtain ⟨⟨w, hw⟩, hvw, huniq⟩ := hPM (hPspan ⟨v, hv⟩)
  refine ⟨w, ⟨hv, hw, hvw⟩, ?_⟩
  rintro u ⟨_, hu, hvu⟩
  have := huniq ⟨u, hu⟩ hvu
  exact congrArg Subtype.val this

/-- Restricting a perfect matching `P` of `G` that extends `M` to the complement `M.vertsᶜ`
yields a perfect matching of `G.induce M.vertsᶜ`. -/
lemma hasPM_induce_compl_of_le_pm {G : SimpleGraph V} {M P : G.Subgraph}
    (hM : M.IsMatching) (hMP : M ≤ P) (hP : P.IsPerfectMatching)
    {S : Finset V} (hS : M.verts = (S : Set V)) :
    HasPM (G.induce ((Sᶜ : Finset V) : Set V)) := by
  classical
  refine ⟨{
    verts := Set.univ
    Adj := fun u v => P.Adj u.val v.val
    adj_sub := fun h => h.adj_sub
    edge_vert := fun _ => Set.mem_univ _
    symm := ⟨fun _ _ h => h.symm⟩
  }, ?_, fun _ => Set.mem_univ _⟩
  intro ⟨v, hv⟩ _
  obtain ⟨w, hvw, huniq⟩ := hP.1 (hP.2 v)
  have hw : w ∈ ((Sᶜ : Finset V) : Set V) := by
    simp only [Finset.coe_compl, Set.mem_compl_iff] at hv ⊢
    intro hwS
    have hwM : w ∈ M.verts := hS ▸ hwS
    obtain ⟨u, hwu, _⟩ := hM hwM
    have hwuP : P.Adj w u := hMP.2 hwu
    have huv : u = v := hP.1.eq_of_adj_left hwuP hvw.symm
    subst huv
    exact hv (hS ▸ M.edge_vert hwu.symm)
  refine ⟨⟨w, hw⟩, hvw, ?_⟩
  intro ⟨u, _⟩ hvu
  exact Subtype.ext (huniq u hvu)

/-- Combining a matching on `S` and a matching on `Sᶜ` yields a perfect matching of `G`
extending the first matching. -/
lemma exists_pm_extending_of_compl {G : SimpleGraph V} {M : G.Subgraph}
    (hM : M.IsMatching) {S : Finset V} (hS : M.verts = (S : Set V))
    (hcompl : HasPM (G.induce ((Sᶜ : Finset V) : Set V))) :
    ∃ P : G.Subgraph, M ≤ P ∧ P.IsPerfectMatching := by
  classical
  obtain ⟨M', hM', hM'verts⟩ := exists_isMatching_of_hasPM_induce hcompl
  have hdisj : Disjoint M.support M'.support := by
    rw [hM.support_eq_verts, hM'.support_eq_verts, hS, hM'verts, Finset.coe_compl]
    exact disjoint_compl_right
  refine ⟨M ⊔ M', le_sup_left, hM.sup hM' hdisj, ?_⟩
  intro v
  rw [Subgraph.verts_sup, hS, hM'verts]
  simp [Finset.coe_compl]

/-- **Lemma 3.3(i)** (Gan–Huang): `G` is `k`-extendable iff `G` has a `2k`-set with a PM,
and for every `2k`-set `S`, `HasPM (G.induce S) → HasPM (G.induce Sᶜ)`. -/
theorem isKExtendable_iff_compl_pm {G : SimpleGraph V} {k : ℕ} :
    IsKExtendable G k ↔
      (∃ S : Finset V, S.card = 2 * k ∧ HasPM (G.induce (S : Set V))) ∧
      ∀ S : Finset V, S.card = 2 * k →
        HasPM (G.induce (S : Set V)) → HasPM (G.induce ((Sᶜ : Finset V) : Set V)) := by
  classical
  constructor
  · rintro ⟨⟨M₀, hM₀, hM₀card⟩, hext⟩
    refine ⟨?_, ?_⟩
    · refine ⟨M₀.verts.toFinset, ?_, ?_⟩
      · have := isMatching_verts_ncard hM₀
        rw [hM₀card, Set.ncard_eq_toFinset_card'] at this
        exact this
      · exact hasPM_induce_of_isMatching hM₀ (by simp)
    · intro S hScard hSPM
      obtain ⟨M, hM, hMverts⟩ := exists_isMatching_of_hasPM_induce hSPM
      have hMcard : M.edgeSet.ncard = k := by
        have h1 := isMatching_verts_ncard hM
        rw [hMverts, Set.ncard_coe_finset, hScard] at h1
        omega
      obtain ⟨P, hMP, hP⟩ := hext M hM hMcard
      exact hasPM_induce_compl_of_le_pm hM hMP hP hMverts
  · rintro ⟨⟨S₀, hS₀card, hS₀PM⟩, hcompl⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨M₀, hM₀, hM₀verts⟩ := exists_isMatching_of_hasPM_induce hS₀PM
      refine ⟨M₀, hM₀, ?_⟩
      have h1 := isMatching_verts_ncard hM₀
      rw [hM₀verts, Set.ncard_coe_finset, hS₀card] at h1
      omega
    · intro M hM hMcard
      let S : Finset V := M.verts.toFinset
      have hSverts : M.verts = (S : Set V) := by simp [S]
      have hScard : S.card = 2 * k := by
        have h1 := isMatching_verts_ncard hM
        rw [hMcard, Set.ncard_eq_toFinset_card'] at h1
        exact h1
      have hSPM : HasPM (G.induce (S : Set V)) := hasPM_induce_of_isMatching hM hSverts
      exact exists_pm_extending_of_compl hM hSverts (hcompl S hScard hSPM)

/-- **Lemma 3.3(ii)** (Gan–Huang): If `G` has a `2k`-set with a PM and every `(ν - 2k)`-set
induces a graph with a PM, then `G` is `k`-extendable. -/
theorem isKExtendable_of_forall_card_pm {G : SimpleGraph V} {k : ℕ}
    (hex : ∃ S : Finset V, S.card = 2 * k ∧ HasPM (G.induce (S : Set V)))
    (hpm : ∀ T : Finset V, T.card = Fintype.card V - 2 * k → HasPM (G.induce (T : Set V))) :
    IsKExtendable G k := by
  rw [isKExtendable_iff_compl_pm]
  refine ⟨hex, fun S hScard _ => hpm Sᶜ ?_⟩
  rw [Finset.card_compl, hScard]

/-- Equivalent form of `isKExtendable_of_forall_card_pm` when `Fintype.card V = 4 * k`
(so `ν - 2k = 2k`): if every `2k`-set has a PM and `2k ≤ ν`, then `G` is `k`-extendable. -/
theorem isKExtendable_of_forall_two_k_pm {G : SimpleGraph V} {k : ℕ}
    (hcard : Fintype.card V = 4 * k)
    (hpm : ∀ T : Finset V, T.card = 2 * k → HasPM (G.induce (T : Set V))) :
    IsKExtendable G k := by
  have hle : 2 * k ≤ Fintype.card V := by omega
  obtain ⟨S₀, hS₀⟩ := Finset.exists_subset_card_eq (s := Finset.univ) (by simpa using hle)
  exact isKExtendable_of_forall_card_pm ⟨S₀, hS₀.2, hpm S₀ hS₀.2⟩
    (fun T hT => hpm T (by omega))

/-- For `G` on `4k` vertices, if `G` and `G'` have the same set of bad `2k`-sets and `G` is
`k`-extendable, then `G'` is `k`-extendable. -/
theorem isKExtendable_of_same_pm {G G' : SimpleGraph V} {k : ℕ}
    (hG : IsKExtendable G k)
    (hsame : ∀ S : Finset V, S.card = 2 * k →
      (HasPM (G.induce (S : Set V)) ↔ HasPM (G'.induce (S : Set V))))
    (hcard : Fintype.card V = 4 * k) :
    IsKExtendable G' k := by
  rw [isKExtendable_iff_compl_pm] at hG ⊢
  obtain ⟨⟨S₀, hS₀card, hS₀PM⟩, hcompl⟩ := hG
  refine ⟨⟨S₀, hS₀card, (hsame S₀ hS₀card).mp hS₀PM⟩, fun S hScard hSPM => ?_⟩
  have hScCard : Sᶜ.card = 2 * k := by rw [Finset.card_compl, hScard, hcard]; omega
  rw [← hsame Sᶜ hScCard]
  exact hcompl S hScard ((hsame S hScard).mpr hSPM)

end BasicLemmas

end LouYuK4
