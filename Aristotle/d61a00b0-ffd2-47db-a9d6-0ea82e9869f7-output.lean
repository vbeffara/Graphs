/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d61a00b0-ffd2-47db-a9d6-0ea82e9869f7

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem adhesion (h : D.T.Adj b₁ b₂) : D.U₁ b₁ b₂ ∩ D.U₂ b₁ b₂ = b₁.1 ∩ b₂.1
-/

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
  ext x;
  constructor;
  · intro hx
    obtain ⟨b₁', hb₁', hx₁⟩ := hx.left
    obtain ⟨b₂', hb₂', hx₂⟩ := hx.right
    have h_sep : G.Separates (D.U₁ b₁ b₂) (D.U₂ b₁ b₂) (b₁.1 ∩ b₂.1) := by
      apply diestel_12_3_1;
      exact h
    exact (by
    specialize h_sep x hx.1 x hx.2 ( SimpleGraph.Walk.nil ) ; aesop);
  · -- If x is in the intersection of b₁ and b₂, then x is in both b₁ and b₂. Since b₁ and b₂ are bags in the tree decomposition, their intersection is part of the separator.
    intro hx
    simp [hx, TreeDecomposition.U₁, TreeDecomposition.U₂];
    constructor;
    · use b₁.val;
      -- Since $x$ is in both $b₁$ and $b₂$, and the path from $b₁$ to $b₂$ is just the edge between them, $x$ is in the support of that path.
      simp [SimpleGraph.IsTree.left, hx];
      simp [SimpleGraph.IsTree.ordered];
      exact hx.1;
    · use b₂.val;
      simp_all +decide [ SimpleGraph.IsTree.right ];
      unfold SimpleGraph.IsTree.ordered; aesop;

noncomputable def width [Fintype α] (D : TreeDecomposition G) : ℕ∞ := ⨆ b ∈ D.bags, Fintype.card b

end TreeDecomposition

noncomputable def treeWidth [Fintype α] (G : SimpleGraph α) : ℕ∞ :=
  sInf {w | ∃ D : TreeDecomposition G, D.width = w}