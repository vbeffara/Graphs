/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 7c56e6ed-33bc-4c07-b040-2ac5d9a2fcca

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was negated by Aristotle:

- theorem tree_treeWidth [Fintype α] (hG : G.IsTree) : treeWidth G = 1

Here is the code for the `negate_state` tactic, used within these negations:

```lean
import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)
```
-/

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
  simp [U₁, U₂, ← biUnion_union, D.tree.left_union_right h, D.union_bags]

lemma diestel_12_3_1 (h : D.T.Adj t₁ t₂) : G.Separates (D.U₁ t₁ t₂) (D.U₂ t₁ t₂) (D.V t₁ ∩ D.V t₂) := by
  refine separates_cover (U_cover h) |>.2 ⟨?_, ?_⟩
  · intro v hv
    obtain ⟨w1, ⟨a, rfl⟩, w3, ⟨ha, rfl⟩, hv₁⟩ := hv.1
    obtain ⟨w1, ⟨b, rfl⟩, w3, ⟨hb, rfl⟩, hv₂⟩ := hv.2
    have h1 := D.tree.left_right_ordered h ha hb
    have h2 := D.bag_inter h1.2
    have h3 := D.bag_inter ha
    grind
  · intros u hu v hv huv
    obtain ⟨t₃, ht₃⟩ := D.edge_mem_bag huv
    have h1 := D.tree.left_union_right h
    obtain h2 | h2 := eq_univ_iff_forall.mp h1 t₃
    · obtain ⟨t₄, ht₅, ht₄'⟩ : ∃ t, t ∈ D.tree.right t₁ t₂ ∧ v ∈ D.V t := by
        simpa [U₂] using hv
      have h3 := D.tree.left_right_ordered h h2 ht₅
      have h4 := D.bag_inter h3.1
      have h5 := D.bag_inter h3.2
      grind
    · obtain ⟨t₄, ht₅, ht₄'⟩ : ∃ t, t ∈ D.tree.left t₁ t₂ ∧ u ∈ D.V t := by
        simpa [U₁] using hu
      have h3 := D.tree.left_right_ordered h ht₅ h2
      have h4 := D.bag_inter h2
      have h5 := D.bag_inter h3.1
      grind

theorem adhesion (h : D.T.Adj t₁ t₂) : D.U₁ t₁ t₂ ∩ D.U₂ t₁ t₂ = D.V t₁ ∩ D.V t₂ := by
  ext x; constructor <;> intro hx
  · obtain ⟨y, h1, h2⟩ := diestel_12_3_1 h x hx.1 x hx.2 SimpleGraph.Walk.nil ; simp_all
  · refine ⟨⟨_, ⟨t₁, ?_⟩, hx.1⟩, ⟨_, ⟨t₂, ?_⟩, hx.2⟩⟩ <;>
    simp [SimpleGraph.IsTree.left, SimpleGraph.IsTree.right, SimpleGraph.IsTree.ordered]

def restrict (D : TreeDecomposition G) (H : G.Subgraph) : TreeDecomposition H.coe where
  ι := D.ι
  V t := {v | v.1 ∈ D.V t}
  T := D.T
  tree := D.tree
  union_bags := by simp [iUnion_setOf, ← mem_iUnion, D.union_bags]
  edge_mem_bag {u v} huv := D.edge_mem_bag (H.coe_adj_sub u v huv)
  bag_inter {b₁ b₂ b₃} hordered x hx := D.bag_inter hordered ⟨hx.1, hx.2⟩

noncomputable def width [Fintype α] (D : TreeDecomposition G) : ℕ∞ := ⨆ b, Fintype.card (D.V b) - 1

end TreeDecomposition

noncomputable def treeWidth [Fintype α] (G : SimpleGraph α) : ℕ∞ :=
  sInf {w | ∃ D : TreeDecomposition G, D.width = w}

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem tree_treeWidth [Fintype α] (hG : G.IsTree) : treeWidth G = 1 :=
  by
    -- Wait, there's a mistake. We can actually prove the opposite.
    negate_state;
    -- Proof starts here:
    use PUnit;
    refine' ⟨ ⊥, inferInstance, _, _ ⟩;
    · constructor <;> norm_num [ SimpleGraph.IsTree ];
      native_decide +revert;
    · refine' ne_of_lt ( lt_of_le_of_lt ( csInf_le _ _ ) _ );
      exact 0;
      · exact ⟨ 0, fun w hw => hw.choose_spec ▸ zero_le _ ⟩;
      · refine' ⟨ _, _ ⟩;
        refine' { .. };
        exact PUnit;
        refine' fun _ => Set.univ;
        exact ⊥;
        all_goals norm_num [ Set.ext_iff ];
        constructor;
        decide +revert;
        simp +decide [ SimpleGraph.isAcyclic_iff_forall_adj_isBridge ];
        simp +decide [ TreeDecomposition.width ];
        simp +decide [ Finset.filter_singleton ];
      · norm_num

-/
theorem tree_treeWidth [Fintype α] (hG : G.IsTree) : treeWidth G = 1 :=
  sorry