import Mathlib
import Graphs.Menger

open Classical Set

variable {α : Type*} [Fintype α] {G : SimpleGraph α}

noncomputable def SimpleGraph.IsTree.thePath (h : G.IsTree) (u v : α) : G.Path u v := by
  choose p hp₁ hp₂ using h.existsUnique_path u v
  refine ⟨p, hp₁⟩

def SimpleGraph.IsTree.leftPart (h : G.IsTree) (u v : α) : Set α := {w : α | u ∈ (h.thePath w v).1.support}

def SimpleGraph.IsTree.rightPart (h : G.IsTree) (u v : α) : Set α := {w : α | v ∈ (h.thePath w u).1.support}

structure TreeDecomposition (G : SimpleGraph α) where
  bags : Set (Set α)
  --
  T : SimpleGraph bags
  T_tree : T.IsTree
  --
  union_bags : ⋃₀ bags = univ
  edge_mem_bag {u v} : G.Adj u v → ∃ b ∈ bags, u ∈ b ∧ v ∈ b
  bag_inter {b₁ b₂ b₃} : b₂ ∈ (T_tree.thePath b₁ b₃).1.support → b₁.1 ∩ b₃.1 ⊆ b₂.1

namespace TreeDecomposition

noncomputable def width (D : TreeDecomposition G) : ℕ∞ := ⨆ b ∈ D.bags, Fintype.card b

lemma diestel_12_3_1 (D : TreeDecomposition G) (t₁ t₂ : D.bags) (h : D.T.Adj t₁ t₂) :
    G.Separates (⋃₀ D.T_tree.leftPart t₁ t₂) (⋃₀ D.T_tree.rightPart t₁ t₂) (t₁ ∩ t₂) := by
  sorry

end TreeDecomposition

noncomputable def treeWidth (G : SimpleGraph α) : ℕ∞ :=
  sInf {w | ∃ D : TreeDecomposition G, D.width = w}
