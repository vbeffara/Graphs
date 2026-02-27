/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: eca2a5cf-caa4-40c5-944f-27f6e5cf70cc

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- lemma diestel_12_3_1 {b₁ b₂ : D.bags} (h : D.T.Adj b₁ b₂) :
    G.Separates (⋃₀ D.T_tree.left b₁ b₂) (⋃₀ D.T_tree.right b₁ b₂) (b₁ ∩ b₂)
-/

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
  ·
    intro v hv
    obtain ⟨a, ha, hv₁⟩ : ∃ a ∈ T₁, v ∈ a.val := by
      grind
    obtain ⟨b, hb, hv₂⟩ : ∃ b ∈ T₂, v ∈ b.val := by
      grind
    have h_path : a.val ∩ b.val ⊆ b₂.val := by
      apply D.bag_inter;
      -- Since $a \in T₁$ and $b \in T₂$, we have $a \in \text{left}(b₁, b₂)$ and $b \in \text{right}(b₁, b₂)$.
      have h_a_left : a ∈ T₁ := by
        exact ha
      have h_b_right : b ∈ T₂ := by
        exact hb;
      have := D.T_tree.left_right_ordered h h_a_left h_b_right; aesop;
    have h_path' : b₂.val ∩ a.val ⊆ b₁.val := by
      -- Since $a$ is in the left set of $b₁$ and $b₂$, and $b₂$ is in the right set, the path from $b₁$ to $b₂$ goes through $a$. Therefore, any element in $b₂$'s bag that's also in $a$'s bag must be in $b₁$'s bag.
      have h_path' : a.val ∩ b₂.val ⊆ b₁.val := by
        have h_ordered : D.T_tree.ordered a b₁ b₂ := by
          exact?
        exact D.bag_inter h_ordered;
      simpa only [ Set.inter_comm ] using h_path'
    aesop
  ·
    -- Since T₁ and T₂ are disjoint and their union is the entire set of bags, any edge between u and v must cross the edge between b₁ and b₂. Therefore, either u is in b₁ or v is in b₂.
    intros u hu v hv huv
    obtain ⟨b₃, hb₃⟩ : ∃ b₃ : D.bags, u ∈ b₃.1 ∧ v ∈ b₃.1 := by
      exact D.edge_mem_bag huv;
    -- Since $b₃$ is in the path from $b₁$ to $b₂$, it must be in either $T₁$ or $T₂$.
    have hb₃_T₁_or_T₂ : b₃ ∈ T₁ ∨ b₃ ∈ T₂ := by
      have := D.T_tree.left_union_right h;
      exact Set.eq_univ_iff_forall.mp this b₃;
    cases' hb₃_T₁_or_T₂ with hb₃_T₁ hb₃_T₂;
    · obtain ⟨ b₄, hb₄, hb₄' ⟩ := hv;
      obtain ⟨ b₅, hb₅, rfl ⟩ := hb₄;
      have := D.T_tree.left_right_ordered h hb₃_T₁ hb₅;
      exact Or.inr ⟨ by
        have := D.bag_inter this.1; aesop;, by
        have := D.bag_inter this.2; aesop; ⟩;
    · obtain ⟨ b₄, hb₄, hb₄' ⟩ := hu;
      obtain ⟨ b₅, hb₅, rfl ⟩ := hb₄;
      have := D.bag_inter ( show D.T_tree.ordered b₅ b₁ b₃ from ?_ );
      · have := D.bag_inter ( show D.T_tree.ordered b₁ b₂ b₃ from ?_ );
        · grind +ring;
        · exact?;
      · -- Since $b₅$ is in the left set of $b₁$ and $b₂$, and $b₃$ is in the right set of $b₁$ and $b₂$, by the definition of ordered, this should hold.
        apply (D.T_tree.left_right_ordered h hb₅ hb₃_T₂).left

end TreeDecomposition

noncomputable def treeWidth (G : SimpleGraph α) : ℕ∞ :=
  sInf {w | ∃ D : TreeDecomposition G, D.width = w}