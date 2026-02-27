import Mathlib
import Graphs.Minor
import Graphs.TreeDecomposition

open Classical Set SimpleGraph

universe u

variable {α β : Type u} {G : SimpleGraph α} {H : SimpleGraph β}

noncomputable def treeWidth [Fintype α] (G : SimpleGraph α) : ℕ∞ :=
  sInf {w | ∃ D : TreeDecomposition G, D.width = w}

theorem treeWidth_ge_one [Fintype α] (h : G ≠ ⊥) : 1 ≤ treeWidth G := by
  refine le_csInf ⟨_, .trivial, rfl⟩ ?_
  rintro w ⟨D, rfl⟩
  obtain ⟨u, v, huv⟩ : ∃ u v : α, G.Adj u v := by contrapose! h; aesop
  obtain ⟨t, ht⟩ := D.edge_mem_bag huv
  refine' le_trans _ ( le_ciSup _ t )
  · refine' Nat.cast_le.mpr ( Nat.le_sub_one_of_lt _ )
    exact Fintype.one_lt_card_iff_nontrivial.mpr ⟨ ⟨ u, ht.1 ⟩, ⟨ v, ht.2 ⟩, by aesop ⟩
  · simp

theorem tree_treeWidth [Fintype α] (hG : G.IsTree) (hG' : G ≠ ⊥) : treeWidth G = 1 := by
  refine' le_antisymm _ _
  · refine' le_trans ( csInf_le _ _ ) _
    exact ( treeDecompositionOfTree hG ( Classical.choose ( show ∃ x : α, True from by
                                                              contrapose! hG'; aesop ) ) ).width
    all_goals generalize_proofs at *
    · exact ⟨ 0, fun w hw => hw.choose_spec.symm ▸ zero_le _ ⟩
    · exact ⟨ _, rfl ⟩
    · (expose_names; exact treeDecompositionOfTree_width hG (choose pf))
  · exact treeWidth_ge_one hG'

theorem bot_treeWidth [Fintype α] : treeWidth (⊥ : SimpleGraph α) = 0 := by
  classical
  by_cases hne : Nonempty α
  · letI : Nonempty α := hne
    obtain ⟨T, _, hTtree⟩ : ∃ T : SimpleGraph α, T ≤ (⊤ : SimpleGraph α) ∧ T.IsTree :=
      (SimpleGraph.connected_top (V := α)).exists_isTree_le
    let D : TreeDecomposition (⊥ : SimpleGraph α) := {
      ι := α
      V := fun t ↦ {t}
      T := T
      tree := hTtree
      union_bags := by ext x; simp
      edge_mem_bag := by intro u v huv; cases huv
      bag_inter := by
        intro t₁ t₂ t₃ h x hx
        rcases hx with ⟨hx1, hx3⟩
        have hx1' : x = t₁ := by simpa using hx1
        have hx3' : x = t₃ := by simpa using hx3
        have ht13 : t₁ = t₃ := hx1'.symm.trans hx3'
        have h' : hTtree.ordered t₁ t₂ t₁ := by simpa [ht13] using h
        have ht2 : t₂ = t₁ := by
          have : t₂ ∈ (hTtree.path t₁ t₁).1.support := by
            simpa [SimpleGraph.IsTree.ordered] using h'
          have hnil : (hTtree.path t₁ t₁).1 = (SimpleGraph.Walk.nil : T.Walk t₁ t₁) := by
            simpa using (hTtree.path_spec' (u := t₁) (v := t₁) ⟨SimpleGraph.Walk.nil, by simp⟩).symm
          simpa [hnil] using this
        simp [hx1', ht2] }
    have hD : D.width = 0 := by
      simp [TreeDecomposition.width, D]
    refine le_antisymm ?_ bot_le
    unfold treeWidth
    exact sInf_le ⟨D, hD⟩
  · letI : IsEmpty α := not_nonempty_iff.mp hne
    let D : TreeDecomposition (⊥ : SimpleGraph α) := TreeDecomposition.trivial
    have hD : D.width = 0 := by
      simp [TreeDecomposition.width, D]
    refine le_antisymm ?_ bot_le
    unfold treeWidth
    exact sInf_le ⟨D, hD⟩

theorem treeWidth_mono [Fintype α] {H : G.Subgraph} : treeWidth H.coe ≤ treeWidth G := by
  unfold treeWidth
  refine le_csInf ⟨_, TreeDecomposition.trivial, rfl⟩ ?_
  rintro w ⟨D, rfl⟩
  exact le_trans (sInf_le ⟨D.restrict H, rfl⟩) (D.width_restrict_le H)

theorem treeWidth_contract [Fintype α] [Fintype β] (h : G ≼c H) : treeWidth G ≤ treeWidth H := by
  rcases h with ⟨φ, hφs, hφa, rfl⟩
  unfold treeWidth
  refine le_csInf ⟨_, TreeDecomposition.trivial, rfl⟩ ?_
  rintro w ⟨D, rfl⟩
  exact le_trans (sInf_le ⟨D.map φ hφs hφa, rfl⟩) (D.width_map_le φ hφs hφa)

theorem treeWidth_minor [Fintype α] [Fintype β] (h : G ≼ H) : treeWidth G ≤ treeWidth H := by
  rcases h with ⟨K, hK⟩
  exact le_trans (treeWidth_contract hK) (treeWidth_mono (H := K))

#print axioms treeWidth_minor
