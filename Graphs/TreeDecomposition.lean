import Mathlib
import Graphs.Separation
import Graphs.Tree

open Classical Set SimpleGraph

variable {α : Type*} [Fintype α] {G : SimpleGraph α}

structure TreeDecomposition (G : SimpleGraph α) where
  bags : Set (Set α)
  T : SimpleGraph bags
  --
  T_tree : T.IsTree
  union_bags : ⋃₀ bags = univ
  edge_mem_bag {u v : α} : G.Adj u v → ∃ b : bags, u ∈ b.1 ∧ v ∈ b.1
  bag_inter {b₁ b₂ b₃ : bags} : T_tree.ordered b₁ b₂ b₃ → b₁.1 ∩ b₃.1 ⊆ b₂.1

namespace TreeDecomposition

variable {D : TreeDecomposition G}

noncomputable def width (D : TreeDecomposition G) : ℕ∞ := ⨆ b ∈ D.bags, Fintype.card b

lemma diestel_12_3_1 {b₁ b₂ : D.bags} (h : D.T.Adj b₁ b₂) :
    G.Separates (⋃₀ D.T_tree.left b₁ b₂) (⋃₀ D.T_tree.right b₁ b₂) (b₁ ∩ b₂) := by
  set T₁ := D.T_tree.left b₁ b₂
  set T₂ := D.T_tree.right b₁ b₂
  set U₁ : Set α := ⋃₀ T₁
  set U₂ : Set α := ⋃₀ T₂
  have h1 : U₁ ∪ U₂ = univ := by
    simp only [U₁, U₂, T₁, T₂, sUnion_eq_biUnion, ← biUnion_union, ← image_union]
    simp only [D.T_tree.left_union_right h, ← sUnion_eq_biUnion]
    simp only [image_univ, Subtype.range_coe_subtype, setOf_mem_eq, D.union_bags]
  refine separates_cover h1 |>.2 ⟨?_, ?_⟩
  · sorry
  · sorry

end TreeDecomposition

noncomputable def treeWidth (G : SimpleGraph α) : ℕ∞ :=
  sInf {w | ∃ D : TreeDecomposition G, D.width = w}
