import Mathlib
import Graphs.Menger

open Classical

variable {α support : Type*} {G : SimpleGraph α}

noncomputable def SimpleGraph.IsTree.thePath (h : G.IsTree) (u v : α) : G.Path u v := by
  choose p hp₁ hp₂ using h.existsUnique_path u v
  refine ⟨p, hp₁⟩

def SimpleGraph.IsTree.leftPart (h : G.IsTree) (u v : α) : Set α := {w : α | u ∈ (h.thePath w v).1.support}

def SimpleGraph.IsTree.rightPart (h : G.IsTree) (u v : α) : Set α := {w : α | v ∈ (h.thePath w u).1.support}

structure TreeDecomposition (G : SimpleGraph α) where
  support : Type
  --
  T : SimpleGraph support
  T_tree : T.IsTree
  --
  bag : support → Finset α
  union_bags a : ∃ b, a ∈ bag b
  edge_mem_bag {u v} : G.Adj u v → ∃ w, u ∈ bag w ∧ v ∈ bag w
  bag_inter {b₁ b₂ b₃} : b₂ ∈ (T_tree.thePath b₁ b₃).1.support → bag b₁ ∩ bag b₃ ⊆ bag b₂

namespace TreeDecomposition

noncomputable def width (D : TreeDecomposition G) : ℕ∞ :=
  iSup (fun w => ((D.bag w).card : ℕ∞))

lemma diestel_12_3_1 (D : TreeDecomposition G) (t₁ t₂ : D.support) (h : D.T.Adj t₁ t₂) :
  G.Separates (⋃ b ∈ D.T_tree.leftPart t₁ t₂, D.bag b) (⋃ b ∈ D.T_tree.rightPart t₁ t₂, D.bag b)
    (D.bag t₁ ∩ D.bag t₂) :=
  sorry

end TreeDecomposition

noncomputable def treeWidth (G : SimpleGraph α) : ℕ∞ :=
  sInf {w | ∃ D : TreeDecomposition G, D.width = w}
