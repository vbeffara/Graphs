import Mathlib
import Graphs.Separation
import Graphs.Tree

open Classical Set SimpleGraph

variable {α : Type*} {G : SimpleGraph α}

structure TreeDecomposition (G : SimpleGraph α) where
  bags : Set (Set α)
  T : SimpleGraph bags
  --
  tree : T.IsTree
  union_bags : ⋃₀ bags = univ
  edge_mem_bag {u v : α} : G.Adj u v → ∃ b : bags, u ∈ b.1 ∧ v ∈ b.1
  bag_inter {b₁ b₂ b₃ : bags} : tree.ordered b₁ b₂ b₃ → b₁.1 ∩ b₃.1 ⊆ b₂.1

namespace TreeDecomposition

variable {D : TreeDecomposition G} {b₁ b₂ : D.bags}

def U₁ (D : TreeDecomposition G) (b₁ b₂ : D.bags) : Set α := ⋃₀ D.tree.left b₁ b₂

def U₂ (D : TreeDecomposition G) (b₁ b₂ : D.bags) : Set α := ⋃₀ D.tree.right b₁ b₂

theorem U_cover (h : D.T.Adj b₁ b₂) : D.U₁ b₁ b₂ ∪ D.U₂ b₁ b₂ = univ := by
  simp only [U₁, U₂, sUnion_eq_biUnion, ← biUnion_union, ← image_union]
  simp only [D.tree.left_union_right h, ← sUnion_eq_biUnion]
  simp only [image_univ, Subtype.range_coe_subtype, setOf_mem_eq, D.union_bags]

lemma diestel_12_3_1 (h : D.T.Adj b₁ b₂) : G.Separates (D.U₁ b₁ b₂) (D.U₂ b₁ b₂) (b₁ ∩ b₂) := by
  refine separates_cover (U_cover h) |>.2 ⟨?_, ?_⟩
  · intro v hv
    obtain ⟨a', ⟨a, ha, rfl⟩, hv₁⟩ := hv.1
    obtain ⟨b', ⟨b, hb, rfl⟩, hv₂⟩ := hv.2
    have h1 := D.tree.left_right_ordered h ha hb
    have h2 := D.bag_inter h1.2
    have h3 := D.bag_inter ha;
    grind
  · intros u hu v hv huv
    obtain ⟨b₃, hb₃⟩ := D.edge_mem_bag huv;
    have h1 := D.tree.left_union_right h;
    obtain h2 | h2 := eq_univ_iff_forall.mp h1 b₃
    · obtain ⟨b₄, hb₄, hb₄'⟩ := hv;
      obtain ⟨b₅, hb₅, rfl⟩ := hb₄;
      have h3 := D.tree.left_right_ordered h h2 hb₅
      have h4 := D.bag_inter h3.1
      have h5 := D.bag_inter h3.2
      grind
    · obtain ⟨b₄, hb₄, hb₄'⟩ := hu;
      obtain ⟨b₅, hb₅, rfl⟩ := hb₄;
      have h3 := D.tree.left_right_ordered h hb₅ h2
      have h4 := D.bag_inter h2
      have h5 := D.bag_inter h3.1
      grind

theorem adhesion (h : D.T.Adj b₁ b₂) : D.U₁ b₁ b₂ ∩ D.U₂ b₁ b₂ = b₁.1 ∩ b₂.1 := by
  sorry

noncomputable def width [Fintype α] (D : TreeDecomposition G) : ℕ∞ := ⨆ b ∈ D.bags, Fintype.card b

end TreeDecomposition

noncomputable def treeWidth [Fintype α] (G : SimpleGraph α) : ℕ∞ :=
  sInf {w | ∃ D : TreeDecomposition G, D.width = w}
