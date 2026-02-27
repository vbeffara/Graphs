import Mathlib
import Graphs.Separation
import Graphs.Tree

open Classical Set SimpleGraph

universe u

variable {α : Type u} {G : SimpleGraph α}

structure TreeDecomposition (G : SimpleGraph α) where
  ι : Type u
  V : ι → Set α
  T : SimpleGraph ι
  --
  tree : T.IsTree
  union_bags : ⋃ i, V i = univ
  edge_mem_bag {u v : α} : G.Adj u v → ∃ t : ι, u ∈ V t ∧ v ∈ V t
  bag_inter {t₁ t₂ t₃ : ι} : tree.ordered t₁ t₂ t₃ → V t₁ ∩ V t₃ ⊆ V t₂

namespace TreeDecomposition

variable {D : TreeDecomposition G} {t₁ t₂ : D.ι}

def U₁ (D : TreeDecomposition G) (t₁ t₂ : D.ι) : Set α := ⋃ t ∈ D.tree.left t₁ t₂, D.V t

def U₂ (D : TreeDecomposition G) (t₁ t₂ : D.ι) : Set α := ⋃ t ∈ D.tree.right t₁ t₂, D.V t

theorem U_cover (h : D.T.Adj t₁ t₂) : D.U₁ t₁ t₂ ∪ D.U₂ t₁ t₂ = univ := by
  ext x
  constructor
  · intro hx
    simp
  · intro hx
    have hx' : x ∈ ⋃ i, D.V i := by simp [D.union_bags]
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx'
    have hi_lr : i ∈ D.tree.left t₁ t₂ ∪ D.tree.right t₁ t₂ := by
      simp [D.tree.left_union_right h]
    rcases hi_lr with hleft | hright
    · exact Or.inl (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hleft, hi⟩⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hright, hi⟩⟩)

lemma diestel_12_3_1 (h : D.T.Adj t₁ t₂) :
    G.Separates (D.U₁ t₁ t₂) (D.U₂ t₁ t₂) (D.V t₁ ∩ D.V t₂) := by
  refine separates_cover (U_cover h) |>.2 ⟨?_, ?_⟩
  · intro v hv
    obtain ⟨a, ha⟩ := mem_iUnion.mp hv.1
    obtain ⟨ha, hv₁⟩ := mem_iUnion.mp ha
    obtain ⟨b, hb⟩ := mem_iUnion.mp hv.2
    obtain ⟨hb, hv₂⟩ := mem_iUnion.mp hb
    have h1 := D.tree.left_right_ordered h ha hb
    have h2 := D.bag_inter h1.2
    have h3 := D.bag_inter ha;
    grind
  · intros u hu v hv huv
    obtain ⟨t₃, ht₃⟩ := D.edge_mem_bag huv;
    have h1 := D.tree.left_union_right h;
    obtain h2 | h2 := eq_univ_iff_forall.mp h1 t₃
    · obtain ⟨t₄, ht₄⟩ := mem_iUnion.mp hv;
      obtain ⟨ht₅, ht₄'⟩ := mem_iUnion.mp ht₄
      have h3 := D.tree.left_right_ordered h h2 ht₅
      have h4 := D.bag_inter h3.1
      have h5 := D.bag_inter h3.2
      grind
    · obtain ⟨t₄, ht₄⟩ := mem_iUnion.mp hu;
      obtain ⟨ht₅, ht₄'⟩ := mem_iUnion.mp ht₄
      have h3 := D.tree.left_right_ordered h ht₅ h2
      have h4 := D.bag_inter h2
      have h5 := D.bag_inter h3.1
      grind

theorem adhesion (h : D.T.Adj t₁ t₂) :
    D.U₁ t₁ t₂ ∩ D.U₂ t₁ t₂ = D.V t₁ ∩ D.V t₂ := by
  ext x; constructor <;> intro hx
  · obtain ⟨y, h1, h2⟩ := diestel_12_3_1 h x hx.1 x hx.2 SimpleGraph.Walk.nil ; simp_all
  · refine ⟨?_, ?_⟩
    · exact mem_iUnion.mpr ⟨t₁, mem_iUnion.mpr ⟨by
        simp [SimpleGraph.IsTree.left, SimpleGraph.IsTree.ordered], hx.1⟩⟩
    · exact mem_iUnion.mpr ⟨t₂, mem_iUnion.mpr ⟨by
        simp [SimpleGraph.IsTree.right, SimpleGraph.IsTree.ordered], hx.2⟩⟩

def restrict (D : TreeDecomposition G) (H : G.Subgraph) : TreeDecomposition H.coe where
  ι := D.ι
  V t := {v | (v : α) ∈ D.V t}
  T := D.T
  tree := D.tree
  union_bags := by
    ext v
    constructor
    · intro hv
      simp
    · intro hv
      have hv' : (v : α) ∈ ⋃ i, D.V i := by simp [D.union_bags]
      obtain ⟨i, hi⟩ := mem_iUnion.mp hv'
      exact mem_iUnion.mpr ⟨i, hi⟩
  edge_mem_bag := by
    intro u v huv
    have huv' : G.Adj (u : α) (v : α) := H.coe_adj_sub u v huv
    obtain ⟨b, hub, hvb⟩ := D.edge_mem_bag huv'
    exact ⟨b, hub, hvb⟩
  bag_inter := by
    intro b₁ b₂ b₃ hordered x hx
    exact D.bag_inter hordered ⟨hx.1, hx.2⟩

noncomputable def width [Fintype α] (D : TreeDecomposition G) : ℕ∞ := ⨆ b, Fintype.card (D.V b)

end TreeDecomposition

noncomputable def treeWidth [Fintype α] (G : SimpleGraph α) : ℕ∞ :=
  sInf {w | ∃ D : TreeDecomposition G, D.width = w}
