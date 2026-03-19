import Graphs.Basic
import Graphs.Minor
import Graphs.TreeDecomposition

open Classical Set SimpleGraph

universe u

variable {α β : Type u} {G : SimpleGraph α} {H : SimpleGraph β} {n : ℕ}

noncomputable def treeWidth (G : SimpleGraph α) : ℕ∞ :=
  sInf {w | ∃ D : TreeDecomposition G, D.width = w}

theorem treeWidth_ge_one (h : G ≠ ⊥) : 1 ≤ treeWidth G := by
  refine le_csInf ⟨_, .trivial, rfl⟩ ?_
  rintro w ⟨D, rfl⟩
  obtain ⟨u, v, huv⟩ : ∃ u v : α, G.Adj u v := by contrapose! h; aesop
  obtain ⟨t, ht⟩ := D.edge_mem_bag huv
  refine' le_trans _ ( le_iSup _ t )
  have h1 : {u, v} ⊆ D.V t := by grind
  have h2 := encard_mono h1
  have h3 : ({u, v} : Set _).encard = 2 := by
    rw [encard_insert_of_notMem]
    · simp +decide
    · simpa using huv.ne
  convert tsub_le_tsub_right h2 1
  simp +decide [h3]

theorem bot_treeWidth : treeWidth (⊥ : SimpleGraph α) = 0 := by
  refine le_antisymm ?_ bot_le
  suffices : ∃ D : TreeDecomposition (⊥ : SimpleGraph α), D.width = 0
  · obtain ⟨D, hD⟩ := this ; exact sInf_le ⟨D, hD⟩
  by_cases hne : Nonempty α
  · obtain ⟨a⟩ := hne ; use .botAt a
    simp [TreeDecomposition.botAt, TreeDecomposition.width]
  · letI : IsEmpty α := not_nonempty_iff.mp hne ; use .trivial
    have := ENat.card_eq_zero_iff_empty α |>.2 this
    simp [TreeDecomposition.width, TreeDecomposition.trivial, this]

theorem treeWidth_tree_le_one (hG : G.IsTree) : treeWidth G ≤ 1 := by
  by_cases hG' : G = ⊥
  · simp [hG', bot_treeWidth]
  · obtain ⟨r, -⟩ : ∃ x : α, True := by contrapose! hG' ; aesop
    exact csInf_le_of_le (OrderBot.bddBelow _) (by simp) (treeDecompositionOfTree_width hG r)

theorem tree_treeWidth (hG : G.IsTree) (hG' : G ≠ ⊥) : treeWidth G = 1 :=
  le_antisymm (treeWidth_tree_le_one hG) (treeWidth_ge_one hG')

theorem treeWidth_le {H : SimpleGraph α} (h : H ≤ G) : treeWidth H ≤ treeWidth G := by
  apply sInf_le_sInf
  rintro w ⟨D, rfl⟩
  exact ⟨D.restrict' h, rfl⟩

theorem treeWidth_mono {H : G.Subgraph} : treeWidth H.coe ≤ treeWidth G := by
  unfold treeWidth
  refine le_csInf ⟨_, TreeDecomposition.trivial, rfl⟩ ?_
  rintro w ⟨D, rfl⟩
  exact le_trans (sInf_le ⟨D.restrict H, rfl⟩) (D.width_restrict_le H)

theorem treeWidth_contract (h : G ≼c H) : treeWidth G ≤ treeWidth H := by
  rcases h with ⟨φ, hφs, hφa, rfl⟩
  unfold treeWidth
  refine le_csInf ⟨_, TreeDecomposition.trivial, rfl⟩ ?_
  rintro w ⟨D, rfl⟩
  exact le_trans (sInf_le ⟨D.map φ hφs hφa, rfl⟩) (D.width_map_le φ hφs hφa)

theorem treeWidth_minor (h : G ≼ H) : treeWidth G ≤ treeWidth H := by
  rcases h with ⟨K, hK⟩
  exact le_trans (treeWidth_contract hK) (treeWidth_mono (H := K))

theorem treeWidth_le_one [Nonempty α] : treeWidth G ≤ 1 ↔ G.IsAcyclic := by
  constructor
  · sorry
  · intro h
    obtain ⟨H, h1, h2⟩ := exists_maximal_isAcyclic_of_le_isAcyclic le_top h
    simp at h2
    trans (treeWidth H)
    · apply treeWidth_le h1
    · apply treeWidth_tree_le_one h2

theorem treeWidth_loop_le_two (h : 2 < n) : treeWidth (cycleGraph n) ≤ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  exact csInf_le_of_le (OrderBot.bddBelow _) ⟨td_cycle m, td_cycle_width⟩ le_rfl

#print axioms treeWidth_minor
