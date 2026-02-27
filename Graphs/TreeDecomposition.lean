import Mathlib
import Graphs.Contraction
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

def trivial : TreeDecomposition G where
  ι := PUnit
  V _ := univ
  T := ⊥
  tree := .of_subsingleton
  union_bags := iUnion_const _
  edge_mem_bag := by tauto
  bag_inter := by tauto

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

lemma width_restrict_le [Fintype α] (D : TreeDecomposition G) (H : G.Subgraph) :
    (D.restrict H).width ≤ D.width := by
  classical
  unfold width
  refine iSup_le ?_
  intro t
  have hcard : Fintype.card ((D.restrict H).V t) ≤ Fintype.card (D.V t) := by
    let f : ((D.restrict H).V t) → (D.V t) := fun x => ⟨x.1.1, x.2⟩
    have hf : Function.Injective f := by
      intro x y hxy
      have hval : (x.1.1 : α) = y.1.1 := by
        exact congrArg (fun z : D.V t => (z : α)) hxy
      apply Subtype.ext
      apply Subtype.ext
      exact hval
    exact Fintype.card_le_of_injective f hf
  have hcard' : (Fintype.card ((D.restrict H).V t) : ℕ∞) ≤ (Fintype.card (D.V t) : ℕ∞) := by
    exact Nat.cast_le.mpr hcard
  exact le_iSup_of_le t (tsub_le_tsub_right hcard' 1)

section Map

variable {β : Type u} {H : SimpleGraph β}

private lemma map_build_walk (D : TreeDecomposition H) (φ : β → α) :
    ∀ {u v : β} (p : H.Walk u v) {a : α}, (∀ z ∈ p.support, φ z = a) →
      ∀ {s t : D.ι}, u ∈ D.V s → v ∈ D.V t →
      ∃ q : D.T.Walk s t, ∀ r ∈ q.support, ∃ x ∈ D.V r, φ x = a := by
  intro u v p a hp s t hs ht
  induction p generalizing s with
  | @nil u =>
      refine ⟨(D.tree.path s t).1, ?_⟩
      intro r hr
      refine ⟨u, ?_, ?_⟩
      · exact D.bag_inter (by simpa [SimpleGraph.IsTree.ordered] using hr) ⟨hs, ht⟩
      · exact hp u (by simp)
  | @cons u v w huv p ih =>
      have hua : φ u = a := hp u (by simp)
      have htail : ∀ z ∈ p.support, φ z = a := by
        intro z hz
        exact hp z (by simp [hz])
      obtain ⟨b, hub, hvb⟩ := D.edge_mem_bag huv
      obtain ⟨q₂, hq₂⟩ := ih htail hvb ht
      let q₁ : D.T.Walk s b := (D.tree.path s b).1
      have hq₁ : ∀ r ∈ q₁.support, ∃ x ∈ D.V r, φ x = a := by
        intro r hr
        refine ⟨u, ?_, hua⟩
        exact D.bag_inter (by simpa [q₁, SimpleGraph.IsTree.ordered] using hr) ⟨hs, hub⟩
      refine ⟨q₁.append q₂, ?_⟩
      intro r hr
      have hmem : r ∈ q₁.support ∨ r ∈ q₂.support.tail := by
        simpa [SimpleGraph.Walk.support_append] using hr
      rcases hmem with hr | hr
      · exact hq₁ r hr
      · exact hq₂ r (List.mem_of_mem_tail hr)

noncomputable def map (D : TreeDecomposition H) (φ : β → α) (hφs : Function.Surjective φ)
    (hφa : H.Adapted φ) : TreeDecomposition (H.map' φ) := {
  ι := D.ι
  V := fun t => φ '' D.V t
  T := D.T
  tree := D.tree
  union_bags := by
    ext a
    constructor
    · intro ha
      simp
    · intro ha
      rcases hφs a with ⟨b, rfl⟩
      have hb : b ∈ ⋃ i, D.V i := by simp [D.union_bags]
      rcases mem_iUnion.mp hb with ⟨t, ht⟩
      exact mem_iUnion.mpr ⟨t, ⟨b, ht, rfl⟩⟩
  edge_mem_bag := by
    intro u v huv
    rcases huv with ⟨_, x, y, hxy, rfl, rfl⟩
    rcases D.edge_mem_bag hxy with ⟨t, hxt, hyt⟩
    exact ⟨t, ⟨x, hxt, rfl⟩, ⟨y, hyt, rfl⟩⟩
  bag_inter := by
    intro t₁ t₂ t₃ hordered a ha
    rcases ha.1 with ⟨x₁, hx₁, rfl⟩
    rcases ha.2 with ⟨x₃, hx₃, hx₃₁⟩
    obtain ⟨p, hp⟩ := hφa hx₃₁.symm
    obtain ⟨q, hq⟩ := map_build_walk D φ p hp hx₁ hx₃
    have ht₂_toPath : t₂ ∈ (q.toPath : D.T.Walk t₁ t₃).support := by
      have hqpath : (q.toPath : D.T.Walk t₁ t₃) = (D.tree.path t₁ t₃).1 := by
        simpa using (D.tree.path_spec' (u := t₁) (v := t₃) q.toPath)
      simpa [SimpleGraph.IsTree.ordered, hqpath] using hordered
    have ht₂ : t₂ ∈ q.support := (SimpleGraph.Walk.support_toPath_subset q) ht₂_toPath
    rcases hq t₂ ht₂ with ⟨x₂, hx₂, hx₂φ⟩
    exact ⟨x₂, hx₂, hx₂φ.trans hx₃₁⟩ }

lemma width_map_le [Fintype α] [Fintype β] (D : TreeDecomposition H) (φ : β → α)
    (hφs : Function.Surjective φ) (hφa : H.Adapted φ) :
    (D.map φ hφs hφa).width ≤ D.width := by
  unfold TreeDecomposition.width
  refine iSup_le ?_
  intro t
  letI : Fintype ((D.map φ hφs hφa).V t) := Subtype.fintype (Membership.mem ((D.map φ hφs hφa).V t))
  have hcard :
      @Fintype.card ((D.map φ hφs hφa).V t)
          (Subtype.fintype (Membership.mem ((D.map φ hφs hφa).V t))) ≤ Fintype.card (D.V t) := by
    let f : D.V t → (D.map φ hφs hφa).V t := fun x => ⟨φ x, ⟨x, x.2, rfl⟩⟩
    have hf : Function.Surjective f := by
      rintro ⟨y, ⟨x, hx, rfl⟩⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    exact Fintype.card_le_of_surjective f hf
  have hcast :
      ((@Fintype.card ((D.map φ hφs hφa).V t)
          (Subtype.fintype (Membership.mem ((D.map φ hφs hφa).V t))) : ℕ∞)) ≤
        (Fintype.card (D.V t) : ℕ∞) := Nat.cast_le.mpr hcard
  exact le_iSup_of_le t (tsub_le_tsub_right hcast 1)

end Map

end TreeDecomposition

def tree_bag [Fintype α] (hG : G.IsTree) (root : α) (t : α) : Set α :=
  insert t {p | G.Adj t p ∧ hG.ordered root p t}

lemma tree_bag_inter [Fintype α] (hG : G.IsTree) (root : α) {t₁ t₂ t₃ : α}
    (h_ordered : hG.ordered t₁ t₂ t₃) :
    tree_bag hG root t₁ ∩ tree_bag hG root t₃ ⊆ tree_bag hG root t₂ := by
      intro x hx
      obtain ⟨hx₁, hx₃⟩ := hx;
      -- Since x is in the tree bag of t₁ and t₃, it is adjacent to t₁ and t₃ or equal to them.
      have h_adj : G.Adj x t₁ ∨ x = t₁ := by
        cases hx₁ ; aesop;
        exact Or.inl ( by rename_i h; exact h.1.symm )
      have h_adj' : G.Adj x t₃ ∨ x = t₃ := by
        cases hx₃ <;> simp_all +decide [ SimpleGraph.IsTree.ordered ];
        exact Or.inl ( by tauto );
      have h_path : ∃ p : G.Walk t₁ t₃, p.support ⊆ [t₁, x, t₃] := by
        rcases h_adj with ( h_adj | rfl ) <;> rcases h_adj' with ( h_adj' | rfl );
        · exact ⟨ SimpleGraph.Walk.cons h_adj.symm ( SimpleGraph.Walk.cons h_adj' SimpleGraph.Walk.nil ), by simp +decide ⟩;
        · exact ⟨ SimpleGraph.Walk.cons h_adj.symm SimpleGraph.Walk.nil, by simp +decide ⟩;
        · exact ⟨ SimpleGraph.Walk.cons h_adj' SimpleGraph.Walk.nil, by simp +decide ⟩;
        · exact ⟨ SimpleGraph.Walk.nil, by simp +decide ⟩;
      obtain ⟨ p, hp ⟩ := h_path;
      have h_path : t₂ ∈ p.support := by
        have h_unique_path : ∀ (p q : G.Walk t₁ t₃), p.IsPath → q.IsPath → p = q := by
          have := hG.existsUnique_path t₁ t₃;
          exact fun p q hp hq => this.unique hp hq;
        contrapose! h_unique_path;
        refine' ⟨ p.toPath, hG.path t₁ t₃, _, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.Walk.isPath_def ];
        intro h; have := hG.ordered t₁ t₂ t₃; simp_all +decide [ SimpleGraph.IsTree.ordered ] ;
        replace h := congr_arg ( fun q => t₂ ∈ q.support ) h ; simp_all +decide [ SimpleGraph.Walk.toPath ] ;
        exact h_unique_path ( by simpa using SimpleGraph.Walk.support_bypass_subset p h );
      have h_path : t₂ ∈ [t₁, x, t₃] := by
        exact hp h_path;
      unfold tree_bag at *; aesop;

/-
Constructs a tree decomposition of a tree `G` where the decomposition tree is `G` itself and bags are `{node, parent}`.
-/
noncomputable def treeDecompositionOfTree [Fintype α] (hG : G.IsTree) (root : α) : TreeDecomposition G where
  ι := α
  V := tree_bag hG root
  T := G
  tree := hG
  union_bags := by
    exact Set.eq_univ_iff_forall.mpr fun x => Set.mem_iUnion.mpr ⟨ x, Set.mem_insert _ _ ⟩
  edge_mem_bag {u v} huv := by
    by_cases h_ordered : hG.ordered root u v
    · refine ⟨v, ?_, by simp [tree_bag]⟩
      exact Or.inr ⟨huv.symm, h_ordered⟩
    · have h_ordered_rev : hG.ordered root v u := by
        exact Or.resolve_left (SimpleGraph.IsTree.adj_ordered_cases hG root huv) h_ordered
      refine ⟨u, by simp [tree_bag], ?_⟩
      exact Or.inr ⟨huv, h_ordered_rev⟩
  bag_inter h := tree_bag_inter hG root h

/-
The width of the canonical tree decomposition of a tree is at most 1.
-/
lemma treeDecompositionOfTree_width [Fintype α] (hG : G.IsTree) (root : α) :
    (treeDecompositionOfTree hG root).width ≤ 1 := by
      -- Each bag in the tree decomposition contains at most 2 vertices, so the width is at most 1.
      have h_card : ∀ t : α, (Fintype.card (tree_bag hG root t)) ≤ 2 := by
        intros t
        set parents := {p | G.Adj t p ∧ hG.ordered root p t}
        have h_parents_card : parents.ncard ≤ 1 := by
          have h_parents_card : ∀ p₁ p₂ : α, p₁ ∈ parents → p₂ ∈ parents → p₁ = p₂ := by
            intro p₁ p₂ hp₁ hp₂; have := SimpleGraph.IsTree.parent_unique hG root t p₁ p₂; aesop;
          exact ncard_le_one_iff_subsingleton.mpr fun ⦃x⦄ x_1 ⦃y⦄ ↦ h_parents_card x y x_1;
        have h_card : (tree_bag hG root t).ncard ≤ 1 + parents.ncard := by
          convert Set.ncard_union_le { t } parents using 1 ; aesop;
        simp only [Set.ncard_eq_toFinset_card', toFinset_card] at h_card h_parents_card
        linarith
      convert ciSup_le fun t => Nat.cast_le.mpr ( Nat.sub_le_sub_right ( h_card t ) 1 ) using 1;
      · exact ⟨ root ⟩;
      · infer_instance;
      · exact fun _ => inferInstance;
      · infer_instance
