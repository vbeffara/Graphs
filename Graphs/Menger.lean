-- With help from Aristotle

import Graphs.Util
import Graphs.Separation
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Int.Star
import Mathlib.Data.Set.Card

set_option maxHeartbeats 0

open Classical

variable {V W : Type*} {G : SimpleGraph V} {x y u v : V} {A B : Set V} {n : ℕ}

namespace SimpleGraph

/-
The set of all vertex sets that separate A from B.
-/
def Separator (G : SimpleGraph V) (A B : Set V) := { S : Set V // G.Separates A B S }

/-
The set of separators is nonempty (e.g., A itself is a separator).
-/
instance Separator.nonempty (G : SimpleGraph V) (A B : Set V) : Nonempty (G.Separator A B) :=
  ⟨A, fun u hu _ _ p => ⟨u, p.start_mem_support, hu⟩⟩

/-
An A-B path is a path in G starting in A and ending in B.
-/
structure ABPath (G : SimpleGraph V) (A B : Set V) where
  u : A
  v : B
  p : G.Path u v

abbrev ABPath.support (P : G.ABPath A B) : Set V := {v | v ∈ P.p.1.support}

/-
A set of A-B paths is disjoint if any two distinct paths in the set are vertex-disjoint.
-/
def disjointPaths (P : Set (G.ABPath A B)) : Prop := P.Pairwise (Disjoint ·.support ·.support)

def Joiner (G : SimpleGraph V) (A B : Set V) :=
  { P : Set (G.ABPath A B) // disjointPaths P }

namespace Joiner

variable {P : G.Joiner A B}

instance : Nonempty (G.Joiner A B) := ⟨⟨∅, Set.pairwise_empty _⟩⟩

theorem le_sep (P : G.Joiner A B) (S : G.Separator A B) : P.1.encard ≤ S.1.encard := by
  have key : ∀ p : G.ABPath A B, ∃ x ∈ S.1, x ∈ p.support := by
    intro p
    obtain ⟨x, h1, h2⟩ := S.2 p.u p.u.2 p.v p.v.2 p.p
    exact ⟨x, h2, h1⟩
  choose f hf_sep hf_supp using key
  have hf_inj : Set.InjOn f P.1 := by
    intro p hp q hq hpq
    by_contra h
    exact Set.disjoint_left.mp (P.2 hp hq h) (hf_supp p) (hpq ▸ hf_supp q)
  exact Set.encard_le_encard_of_injOn (fun _ hp => hf_sep _) hf_inj

theorem encard_le (P : G.Joiner A B) : P.1.encard ≤ A.encard :=
  P.le_sep ⟨A, fun u hu _ _ p => ⟨u, p.start_mem_support, hu⟩⟩

end Joiner

/- =========================== REVIEW BAR ===================== -/

/-
The minimum size of a separator and the maximum number of disjoint paths.
-/
noncomputable def mincut (G : SimpleGraph V) (A B : Set V) : ℕ∞ :=
  ⨅ S : G.Separator A B, S.1.encard

noncomputable def maxflow (G : SimpleGraph V) (A B : Set V) : ℕ∞ :=
  ⨆ P : G.Joiner A B, P.1.encard

/-
The maximum number of disjoint A-B paths is at most the minimum size of an A-B separator.
-/
theorem Menger_weak : G.maxflow A B ≤ G.mincut A B := by
  apply iSup_le; intro P; apply le_iInf; intro S; exact Joiner.le_sep P S

/-
Base case of Menger's theorem: if G has no edges, the theorem holds.
-/
lemma Menger_strong_base (G : SimpleGraph V) (A B : Set V) (h : G.edgeSet = ∅) :
    G.mincut A B ≤ G.maxflow A B := by
  simp at h ; subst G
  have h_empty : ∀ u v, (⊥ : SimpleGraph V).Walk u v → u = v := by
    intro u v p; induction p <;> aesop;
  -- The separator A ∩ B has size ≤ mincut
  have h_mincut_le : mincut ⊥ A B ≤ (A ∩ B).encard := by
    exact iInf_le_of_le ⟨A ∩ B, fun a ha b hb p => ⟨a, p.start_mem_support, by
      simp [← h_empty a b p] at hb; simp [ha, hb]⟩⟩ le_rfl
  -- Build a joiner from A ∩ B
  let γ : ↥(A ∩ B) → (⊥ : SimpleGraph V).ABPath A B := fun a =>
    ⟨⟨a, a.2.1⟩, ⟨a, a.2.2⟩, Walk.nil, Walk.IsPath.nil⟩
  have hγ_inj : Function.Injective γ := by
    intro a b hab; simp [γ] at hab; exact Subtype.ext hab.1
  have h_joiner : disjointPaths (Set.range γ) := by
    intro p hp q hq hpq
    obtain ⟨a, rfl⟩ := hp; obtain ⟨b, rfl⟩ := hq
    simp only [ABPath.support, γ, Set.disjoint_left, Set.mem_setOf_eq, Walk.support_nil,
      List.mem_cons, List.mem_nil_iff, or_false]
    intro z hz1 hz2; rw [hz1] at hz2
    exact hpq (by congr 1; all_goals exact Subtype.ext hz2)
  have h_maxflow_ge : (A ∩ B).encard ≤ maxflow ⊥ A B := by
    apply le_iSup_of_le ⟨Set.range γ, h_joiner⟩
    show (A ∩ B).encard ≤ (Set.range γ).encard
    rw [← Set.image_univ, hγ_inj.encard_image]; simp
  exact h_mincut_le.trans h_maxflow_ge

noncomputable def merge_to {x y : V} (h : y ≠ x) (z : V) : {z : V // z ≠ x} :=
  if h' : z = x then ⟨y, h⟩ else ⟨z, h'⟩

noncomputable def contract (G : SimpleGraph V) {x y : V} (h : y ≠ x) := G.map (merge_to h)

/-
Definitions for edge contraction: the setoid identifying the endpoints, the
contracted graph, and the projection map.
-/
def contractEdgeSetoid (x y : V) : Setoid V :=
  Setoid.mk (fun a b => a = b ∨ (a = x ∧ b = y) ∨ (a = y ∧ b = x)) (by constructor <;> aesop)

abbrev contractType (x y : V) := Quotient (contractEdgeSetoid x y)

/-
The contraction of edge (x, y) in G.
-/
def contractEdge (G : SimpleGraph V) (x y : V) : SimpleGraph (Quotient (contractEdgeSetoid x y)) :=
  fromRel (fun a b => ∃ a' b', ⟦a'⟧ = a ∧ ⟦b'⟧ = b ∧ G.Adj a' b')

lemma contract_eq_map : contractEdge G x y = G.map (⟦·⟧) := by
  ext a b
  simp [SimpleGraph.map, Relation.Map, contractEdge, Quotient.mk_eq_iff_out]
  intro h ; constructor ; rintro (⟨a', h1, b', h2, h3⟩ | ⟨a', h1, b', h2, h3⟩)
  all_goals { grind [Adj.symm] }

def contractEdge_liftSet (x y : V) (S : Set V) : Set (contractType x y) :=
  (⟦·⟧) '' S

noncomputable def Walk.map' (f : V → W) : ∀ ⦃u v⦄ (p : G.Walk u v),
    {q : (G.map f).Walk (f u) (f v) // q.support.toFinset ⊆ p.support.toFinset.image f}
  | _, _, .nil => ⟨Walk.nil, by simp⟩
  | u, _, .cons h p => by
    rename_i v'
    by_cases h : f v' = f u
    · use .copy (p.map' f) h rfl, by simpa using (p.map' f).2.trans $ Finset.subset_insert _ _
    · use .cons (by simp [SimpleGraph.map, Relation.Map] ; grind) (p.map' f).1, by simp [(p.map' f).2]

/-
Given a walk in G, there exists a walk in the contracted graph G/e between the
projected endpoints, whose support is contained in the image of the original
walk's support.
-/
lemma exists_walk_of_path_contraction (G : SimpleGraph V) (x y : V) (p : G.Walk u v) :
    ∃ (w : (G.contractEdge x y).Walk ⟦u⟧ ⟦v⟧),
    w.support.toFinset ⊆ p.support.toFinset.image (⟦·⟧) := by
  induction' p with u v p ih;
  · exact ⟨Walk.nil, by simp⟩;
  · simp +zetaDelta at *;
    cases' ‹∃ w, _› with w hw;
    by_cases h : (⟦v⟧ : contractType x y) = ⟦p⟧;
    · grind;
    · have h_adj : (G.contractEdge x y).Adj ⟦v⟧ ⟦p⟧ := by
        unfold contractEdge
        aesop;
      refine' ⟨ Walk.cons h_adj w, _ ⟩;
      simp_all [ Finset.subset_iff ]

/-
The preimage of a set of vertices in the contracted graph.
-/
noncomputable def contractEdge_preimage (x y : V)
    (Y : Set (Quotient (contractEdgeSetoid x y))) : Set V :=
  {v | ⟦v⟧ ∈ Y}

lemma mem_contractEdge_preimage {x y : V}
    {Y : Set (Quotient (contractEdgeSetoid x y))} {v : V} :
  v ∈ contractEdge_preimage x y Y ↔ ⟦v⟧ ∈ Y := by
  simp [contractEdge_preimage]

/-
If a set of vertices separates A and B in the contracted graph G/e, then its preimage separates A and B in G.
-/
lemma contractEdge_preimage_separates
    (Y : (G.contractEdge x y).Separator (contractEdge_liftSet x y A) (contractEdge_liftSet x y B)) :
  G.Separates A B (contractEdge_preimage x y Y.1) := by
    intro u hu v hv p
    obtain ⟨ w, hw ⟩ := exists_walk_of_path_contraction G x y p;
    obtain ⟨ z, hzY, hzw ⟩ : ∃ z ∈ Y.1, z ∈ w.support := by
      have := Y.2 ⟦u⟧
        (by exact Set.mem_image_of_mem _ hu)
        ⟦v⟧
        (by exact Set.mem_image_of_mem _ hv)
        w.toPath;
      exact this |> fun ⟨z, hz₁, hz₂ ⟩ => ⟨ z, hz₂, by simpa using Walk.support_bypass_subset _ hz₁ ⟩;
    have := hw ( by simpa using hzw );
    simp +zetaDelta at *;
    refine ⟨this.choose, this.choose_spec.1, ?_⟩
    exact (mem_contractEdge_preimage (x := x) (y := y) (Y := Y.1) (v := this.choose)).2
      (by simpa [this.choose_spec.2] using hzY)

/-
The contracted vertex in the quotient graph.
-/
def contractEdge_vertex (x y : V) : Quotient (contractEdgeSetoid x y) :=
  Quotient.mk (contractEdgeSetoid x y) x

lemma contractEdge_vertex_eq (x y : V) :
  contractEdge_vertex x y = Quotient.mk (contractEdgeSetoid x y) y := by
  apply Quotient.sound
  right ; grind

/-
A vertex projects to the contracted vertex if and only if it is one of the endpoints of the contracted edge.
-/
lemma contractEdgeProj_eq_vertex_iff (x y u : V) :
    (⟦u⟧ : contractType x y) = ⟦x⟧ ↔ u = x ∨ u = y := by
  simp [contractEdgeSetoid, Quotient.eq]
  grind

/-
If the projections of two vertices are adjacent in the contracted graph and neither projects to the contracted vertex, then the original vertices are adjacent in the original graph.
-/
lemma contractEdge_adj_lift (G : SimpleGraph V) (x y : V) (u v : V)
  (hu : ⟦u⟧ ≠ contractEdge_vertex x y)
  (hv : ⟦v⟧ ≠ contractEdge_vertex x y) :
  (G.contractEdge x y).Adj ⟦u⟧ ⟦v⟧ → G.Adj u v := by
    rintro ⟨ a, b, ha, hb, hab ⟩;
    · unfold contractEdge_vertex at *; simp_all [ Quotient.eq ] ;
      unfold contractEdgeSetoid at *; aesop;
    · -- Apply the lemma that states if the projections of two vertices are adjacent and neither is the contracted vertex, then the original vertices are adjacent.
      have h_adj : ⟦v⟧ ≠ contractEdge_vertex x y → ⟦u⟧ ≠ contractEdge_vertex x y → (G.contractEdge x y).Adj ⟦v⟧ ⟦u⟧ → G.Adj v u := by
        unfold contractEdge_vertex at *; simp_all [ Quotient.eq ] ;
        unfold contractEdgeSetoid at *; aesop;
      simp_all [ adj_comm ];
      unfold contractEdge at *; aesop;

/-
The size of the preimage of a set of vertices in the contracted graph.
-/
private lemma quot_injOn_away (h : x ≠ y) (Y : Set (Quotient (contractEdgeSetoid x y)))
    (hv : contractEdge_vertex x y ∉ Y) :
    Set.InjOn (fun v : V => (⟦v⟧ : Quotient (contractEdgeSetoid x y)))
      (contractEdge_preimage x y Y) := by
  intro a ha b hb hab
  simp only [contractEdge_preimage, Set.mem_setOf_eq] at ha hb
  simp only [Quotient.eq, contractEdgeSetoid] at hab
  rcases hab with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact absurd ha hv
  · exact absurd hb hv

private lemma quot_image_preimage (Y : Set (Quotient (contractEdgeSetoid x y))) :
    (fun v : V => (⟦v⟧ : Quotient (contractEdgeSetoid x y))) '' (contractEdge_preimage x y Y) = Y := by
  ext z
  simp only [Set.mem_image, contractEdge_preimage, Set.mem_setOf_eq]
  constructor
  · rintro ⟨v, hv, rfl⟩; exact hv
  · intro hz; obtain ⟨v, rfl⟩ := Quotient.exists_rep z; exact ⟨v, hz, rfl⟩

lemma encard_preimage_contractEdge (h : x ≠ y) (Y : Set (Quotient (contractEdgeSetoid x y))) :
    (contractEdge_preimage x y Y).encard =
    if contractEdge_vertex x y ∈ Y then Y.encard + 1 else Y.encard := by
  split_ifs with hv
  · -- Case: contractEdge_vertex ∈ Y
    set Y' := Y \ {contractEdge_vertex x y} with hY'_def
    have hv' : contractEdge_vertex x y ∉ Y' := by simp [Y']
    -- Preimage decomposes
    have h_pre_eq : contractEdge_preimage x y Y =
        contractEdge_preimage x y Y' ∪ {x, y} := by
      ext v; simp only [contractEdge_preimage, Set.mem_setOf_eq, Set.mem_union,
        Set.mem_singleton_iff, Set.mem_insert_iff]
      constructor
      · intro hv_mem
        by_cases hx : v = x
        · right; left; exact hx
        · by_cases hy : v = y
          · right; right; exact hy
          · left; refine ⟨hv_mem, ?_⟩
            intro heq
            have := contractEdgeProj_eq_vertex_iff x y v |>.mp heq
            rcases this with rfl | rfl <;> contradiction
      · rintro (⟨hv_mem, _⟩ | hv_x | hv_y)
        · exact hv_mem
        · rw [hv_x]; exact hv
        · rw [hv_y]; rw [← contractEdge_vertex_eq]; exact hv
    have h_disj : Disjoint (contractEdge_preimage x y Y') ({x, y} : Set V) := by
      rw [Set.disjoint_left]
      intro v hv_mem hv_xy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv_xy
      simp only [contractEdge_preimage, Set.mem_setOf_eq] at hv_mem
      rcases hv_xy with hv_x | hv_y
      · rw [hv_x] at hv_mem; exact hv' hv_mem
      · rw [hv_y, ← contractEdge_vertex_eq] at hv_mem; exact hv' hv_mem
    rw [h_pre_eq, Set.encard_union_eq h_disj, Set.encard_pair h]
    -- preimage of Y' has encard = Y'.encard (by injectivity + image = Y')
    have h_inj := quot_injOn_away h Y' hv'
    have h_img := quot_image_preimage (x := x) (y := y) Y'
    have h_encard := h_inj.encard_image
    rw [h_img] at h_encard
    -- h_encard : Y'.encard = (contractEdge_preimage x y Y').encard
    -- Y.encard = Y'.encard + 1
    have hY_eq : Y = insert (contractEdge_vertex x y) Y' := by
      ext z; constructor
      · intro hz; by_cases hze : z = contractEdge_vertex x y
        · exact hze ▸ Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ ⟨hz, hze⟩
      · rintro (rfl | ⟨hz, _⟩)
        · exact hv
        · exact hz
    rw [hY_eq, Set.encard_insert_of_notMem hv', ← h_encard]
    ring
  · -- Case: contractEdge_vertex ∉ Y
    have h_inj := quot_injOn_away h Y hv
    have h_img := quot_image_preimage (x := x) (y := y) Y
    have h_encard := h_inj.encard_image
    rw [h_img] at h_encard
    exact h_encard.symm

/-
A walk in the contracted graph that avoids the contracted vertex can be lifted to a walk in the original graph.
-/
lemma lift_walk_avoiding_contraction {u v : Quotient (contractEdgeSetoid x y)}
    (p : (G.contractEdge x y).Walk u v) (hp : contractEdge_vertex x y ∉ p.support) :
  ∃ (u' v' : V) (q : G.Walk u' v'), ⟦u'⟧ = u ∧ ⟦v'⟧ = v ∧
    (q.support.toFinset.image (⟦·⟧)) = p.support.toFinset ∧
    x ∉ q.support ∧ y ∉ q.support := by
  induction' p with u v p ih;
  · obtain ⟨ u', rfl ⟩ := Quotient.exists_rep u;
    by_cases hu : u' = x ∨ u' = y;
    · cases hu <;> simp_all [ Quotient.eq, contractEdge_vertex, contractEdgeSetoid ];
      · grind
      · apply hp
        erw [List.mem_cons]
        simp [Quotient.eq]
    · refine' ⟨ u', u', Walk.nil, _, _, _, _ ⟩ <;> simp_all
      tauto;
  · rename_i h₁ h₂;
    -- Since v is not the contracted vertex, there exists a unique u' in V such that contractEdgeProj x y u' = v.
    obtain ⟨u', hu'⟩ : ∃ u' : V, ⟦u'⟧ = v ∧ u' ≠ x ∧ u' ≠ y := by
      rcases Quotient.exists_rep v with ⟨ u', rfl ⟩;
      refine' ⟨ u', rfl, _, _ ⟩ <;> contrapose! hp <;> simp_all [ contractEdge_vertex ];
      exact Or.inl ( by simp [Quotient.eq, contractEdgeSetoid] );
    obtain ⟨ v', hv' ⟩ := h₂ ( by intro h; simp_all [ Walk.support_cons ] );
    obtain ⟨ v'', q, hv'', hv''', hq, hx, hy ⟩ := hv';
    refine' ⟨ u', v'', Walk.cons _ q, hu'.1, hv''', _, _, _ ⟩ <;> simp_all [ Walk.support_cons ];
    · have h_adj : (G.contractEdge x y).Adj ⟦u'⟧ ⟦v'⟧ := by
        grind;
      apply contractEdge_adj_lift G x y u' v';
      · grind;
      · intro h; simp_all
      · exact h_adj;
    · tauto;
    · grind

/-
Define deleting a single edge and prove it reduces edge count if the edge exists.
-/
def deleteEdge (G : SimpleGraph V) (x y : V) : SimpleGraph V :=
  G.deleteEdges {s(x, y)}

lemma deleteEdge_card_edges_lt [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) (h : G.Adj x y) :
  (G.deleteEdge x y).edgeFinset.card < G.edgeFinset.card := by
    refine' Finset.card_lt_card _;
    rw [ssubset_iff_subset_ne]
    constructor
    · simp [deleteEdge, deleteEdges]
    · simpa [deleteEdge]

end SimpleGraph
-- #exit

/-
A path in the contracted graph avoiding the contracted vertex lifts to a path in the original graph avoiding the contracted edge's endpoints (subset support).
-/
lemma SimpleGraph.lift_path_avoiding_contraction_AB (G : SimpleGraph V) (A B : Set V) (x y : V)
    {u v : Quotient (SimpleGraph.contractEdgeSetoid x y)} (p : (G.contractEdge x y).Walk u v)
    (hp_avoid : SimpleGraph.contractEdge_vertex x y ∉ p.support)
    (hu : u ∈ SimpleGraph.contractEdge_liftSet x y A) (hv : v ∈ SimpleGraph.contractEdge_liftSet x y B) :
  ∃ (u' v' : V) (q : G.Walk u' v'), u' ∈ A ∧ v' ∈ B ∧
    ⟦u'⟧ = u ∧ ⟦v'⟧ = v ∧ q.IsPath ∧
    (q.support.toFinset.image (⟦·⟧)) ⊆ p.support.toFinset ∧
    x ∉ q.support ∧ y ∉ q.support := by
  have := @SimpleGraph.lift_walk_avoiding_contraction V G x y u v p hp_avoid;
  obtain ⟨ u', v', q, hu', hv', hq ⟩ := this;
  refine' ⟨ u', v', q.toPath, _, _, hu', hv', _, _, _ ⟩
  · simp [contractEdge_liftSet] at hu
    obtain ⟨ w, hw, rfl ⟩ := hu;
    cases h1 : eq_or_ne u' x <;> cases h2 : eq_or_ne u' y <;> cases h3 : eq_or_ne w x <;> cases h4 : eq_or_ne w y
    all_goals subst_eqs
    all_goals simp_all [Quotient.eq, contractEdgeSetoid ];
  · simp [contractEdge_liftSet] at hv
    obtain ⟨ w, hw ⟩ := hv;
    have h_inj : ∀ a b : V, (⟦a⟧ : contractType x y) = ⟦b⟧ → a = b ∨ a = x ∧ b = y ∨ a = y ∧ b = x := by
      intro a b hab; erw [ Quotient.eq ] at hab; aesop;
    cases h_inj _ _ ( hv'.trans hw.2.symm ) <;> aesop;
  · simp_all [ SimpleGraph.Walk.isPath_def ];
  · rw [ ← hq.1 ];
    simp [ Finset.subset_iff ];
    intro a ha;
    exact ⟨ a, by simpa using SimpleGraph.Walk.support_toPath_subset q ha, rfl ⟩;
  · exact ⟨ fun h => hq.2.1 <| by simpa using q.support_bypass_subset h, fun h => hq.2.2 <| by simpa using q.support_bypass_subset h ⟩

/-
If a vertex is adjacent to the contracted vertex in the quotient graph, then it is adjacent to one of the endpoints of the contracted edge in the original graph.
-/
lemma SimpleGraph.contractEdge_adj_lift_vertex (G : SimpleGraph V) (x y : V) (u : V)
  (hu : ⟦u⟧ ≠ SimpleGraph.contractEdge_vertex x y) :
  (G.contractEdge x y).Adj ⟦u⟧ (SimpleGraph.contractEdge_vertex x y) → G.Adj u x ∨ G.Adj u y := by
    rintro ⟨ a, ha ⟩;
    rcases ha with ( ⟨ a', b', ha', hb', hab ⟩ | ⟨ a', b', ha', hb', hab ⟩ );
    · simp_all [ Quotient.eq, contractEdge_vertex ];
      unfold contractEdgeSetoid at *; aesop;
    · rw [ eq_comm ] at ha' hb';
      cases eq_or_ne a' x <;> cases eq_or_ne a' y <;> cases eq_or_ne b' x <;> cases eq_or_ne b' y
      all_goals simp_all [ SimpleGraph.contractEdge_vertex, Quotient.eq, contractEdgeSetoid, SimpleGraph.adj_comm ];

/-
The number of edges in the contracted graph is strictly less than in the original graph.
-/
lemma SimpleGraph.contractEdge_edge_card_lt [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) (h : G.Adj x y) :
  (G.contractEdge x y).edgeFinset.card < G.edgeFinset.card := by
    have h_inter : Finset.card (G.contractEdge x y).edgeFinset ≤ Finset.card (G.edgeFinset \ {s(x, y)}) := by
      have h_inter : (G.contractEdge x y).edgeFinset ⊆ Finset.image
          (fun e => Sym2.map (⟦·⟧) e) (G.edgeFinset \ {s(x, y)}) := by
        intro e he; simp_all [ SimpleGraph.contractEdge ] ;
        rcases e with ⟨ a, b ⟩ ; simp_all [ fromRel ] ;
        rcases he.2 with ( ⟨ a', rfl, b', rfl, hab ⟩ | ⟨ a', rfl, b', rfl, hab ⟩ ) <;> use s(a', b') <;> simp_all [ Sym2.eq_swap ];
        · simp_all [Quotient.eq, contractEdgeSetoid]
        · simp_all [Quotient.eq, contractEdgeSetoid] ; aesop
      exact le_trans ( Finset.card_le_card h_inter ) ( Finset.card_image_le );
    exact lt_of_le_of_lt h_inter ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.sdiff_subset, by aesop ⟩ ) )

/-
If a walk's support intersects {x, y} only at v (or not at all), then the walk does not use the edge xy.
-/
lemma SimpleGraph.Walk.edges_no_xy_of_support_inter_subset_one {G : SimpleGraph V}
  {u v : V} (p : G.Walk u v) (x y : V) (hxy : x ≠ y)
  (h : p.support.toFinset ∩ {x, y} ⊆ {v}) :
  s(x, y) ∉ p.edges := by
    contrapose! h;
    simp_all [ Finset.eq_singleton_iff_unique_mem ];
    have h_support : x ∈ p.support ∧ y ∈ p.support := by
      induction p <;> aesop;
    aesop

/-
If a walk intersects X, there is a prefix walk ending in X that avoids X internally.
-/
lemma SimpleGraph.Walk.exists_walk_prefix_avoiding_set {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (X : Set V) (h : ∃ w ∈ p.support, w ∈ X) :
  ∃ (w : V) (q : G.Walk u w), w ∈ X ∧ q.support.toFinset ⊆ p.support.toFinset ∧ (∀ z ∈ q.support, z ∈ X → z = w) := by
    revert h p;
    intro p hp
    induction' p with u v p ih;
    · simp_all [ SimpleGraph.Walk.support ];
      exact ⟨ u, hp, SimpleGraph.Walk.nil, by simp ⟩;
    · rename_i h₁ h₂ h₃;
      by_cases h : v ∈ X;
      · refine' ⟨ v, SimpleGraph.Walk.nil, h, _, _ ⟩ <;> simp [ h ];
      · rcases h₃ ( by cases hp; aesop ) with ⟨ w, q, hw, hq₁, hq₂ ⟩ ; use w, cons h₁ q ; aesop;

/-
If a path intersects X, there is a prefix path ending in X that avoids X internally.
-/
lemma SimpleGraph.Walk.exists_path_prefix_avoiding_set {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
    (X : Set V) (h : ∃ w ∈ p.support, w ∈ X) :
    ∃ (w : V) (q : G.Walk u w), w ∈ X ∧ q.IsPath ∧ q.support.toFinset ⊆ p.support.toFinset ∧ (∀ z ∈ q.support, z ∈ X → z = w) := by
    obtain ⟨w, hw₁, hw₂⟩ := h
    obtain ⟨w', q, hw'X, hq_support, hq_unique⟩ :=
      p.exists_walk_prefix_avoiding_set X ⟨w, hw₁, hw₂⟩
    refine ⟨w', q.toPath, hw'X, ?_, ?_, ?_⟩
    · simp
    · refine subset_trans ?_ hq_support
      simp [toPath, Finset.subset_iff]
      exact fun x hx => SimpleGraph.Walk.support_bypass_subset q hx
    · intro z hz hzX
      exact hq_unique z (by simpa using q.support_bypass_subset hz) hzX

/-
If X separates A and B in G and contains x and y, then any separator of A and X in G-xy is also a separator of A and B in G.
-/
lemma SimpleGraph.separator_in_G_of_separator_in_G_delete_edge (G : SimpleGraph V) (A B : Set V)
    (x y : V) (X : G.Separator A B) (S : (G.deleteEdge x y).Separator A X.1) (hx : x ∈ X.1) (hy : y ∈ X.1)
    (hxy : x ≠ y) : G.Separates A B S.1 := by
    classical
    intro u hu v hv p
    have h_sep := X.2 u hu v hv p
    obtain ⟨w, q, hwX, hqpath, hq_support, hq_avoid⟩ :=
      SimpleGraph.Walk.exists_path_prefix_avoiding_set p X.1 h_sep
    have hq_avoid_xy : s(x, y) ∉ q.edges := by
      apply SimpleGraph.Walk.edges_no_xy_of_support_inter_subset_one q x y hxy
      simp only [Finset.subset_iff, Finset.mem_inter, List.mem_toFinset, Finset.mem_insert,
        Finset.mem_singleton]
      intro z ⟨hz_mem, hz_xy⟩
      exact hq_avoid z hz_mem (by rcases hz_xy with rfl | rfl <;> assumption)
    have hq_path_G_minus_xy : ∃ q' : (G.deleteEdge x y).Walk u w, q'.IsPath ∧ q'.support.toFinset ⊆ q.support.toFinset := by
      have : ∀ {u v : V} (q : G.Walk u v), q.IsPath → s(x, y) ∉ q.edges → ∃ q' : (G.deleteEdge x y).Walk u v, q'.IsPath ∧ q'.support.toFinset ⊆ q.support.toFinset := by
        intro u v q hq hq_avoid_xy
        induction' q with u v q ih;
        · exact ⟨ SimpleGraph.Walk.nil, by simp ⟩;
        · rename_i h₁ h₂ h₃;
          simp_all [ SimpleGraph.Walk.cons_isPath_iff ];
          obtain ⟨ q', hq'_path, hq'_support ⟩ := h₃;
          refine' ⟨ SimpleGraph.Walk.cons _ q', _, _ ⟩ <;> simp_all [ Finset.subset_iff ];
          · unfold SimpleGraph.deleteEdge; aesop;
          · exact fun h => hq.2 ( by simpa using hq'_support ( by simpa using h ) );
          · intro a ha; specialize hq'_support ( List.mem_toFinset.mpr ha ) ; aesop;
      exact this q hqpath hq_avoid_xy;
    obtain ⟨ q', hq'_path, hq'_support ⟩ := hq_path_G_minus_xy;
    have := S.2 u hu w hwX q';  simp_all [ SimpleGraph.Walk.isPath_def ] ;
    obtain ⟨ z, hz₁, hz₂ ⟩ := this; exact ⟨ z, by simpa using hq'_support ( by simpa using hz₁ ) |> fun h => hq_support h, hz₂ ⟩ ;

/-
If a separator in the contracted graph has size strictly less than the minimum separator size of the original graph, then it must contain the contracted vertex.
-/
theorem SimpleGraph.contractEdge_separator_contains_vertex (G : SimpleGraph V) (A B : Set V) (x y : V) (k : ℕ∞)
  (h_min : G.mincut A B = k)
  (Y : (G.contractEdge x y).Separator (SimpleGraph.contractEdge_liftSet x y A) (SimpleGraph.contractEdge_liftSet x y B))
  (hY_card : Y.1.encard < k)
  (hxy : x ≠ y) :
  SimpleGraph.contractEdge_vertex x y ∈ Y.1 := by
    contrapose! hY_card
    have h_sep : G.Separates A B (SimpleGraph.contractEdge_preimage x y Y.1) := by
      simpa using contractEdge_preimage_separates Y
    have h_encard : (SimpleGraph.contractEdge_preimage x y Y.1).encard ≤ Y.1.encard := by
      apply Set.encard_le_encard_of_injOn (f := (⟦·⟧))
      · intro v hv; exact (mem_contractEdge_preimage).1 hv
      · intro v hv w _ hvw
        by_contra h_ne
        have h_rel := Quotient.exact hvw
        simp at h_rel
        rcases h_rel with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact h_ne rfl
        · exact hY_card ((mem_contractEdge_preimage).1 hv)
        · exact hY_card (by rw [contractEdge_vertex_eq]; exact (mem_contractEdge_preimage).1 hv)
    calc k = G.mincut A B := h_min.symm
      _ ≤ (SimpleGraph.contractEdge_preimage x y Y.1).encard := iInf_le_of_le ⟨_, h_sep⟩ le_rfl
      _ ≤ Y.1.encard := h_encard

/-
If P is a set of disjoint paths from A to X with size equal to X, then every vertex in X is the endpoint of exactly one path in P, and that path intersects X only at its endpoint.
-/
lemma SimpleGraph.disjoint_paths_prop (G : SimpleGraph V) (A X : Set V) (hX_fin : X.Finite)
    (P : G.Joiner A X) (hP_card : P.1.encard = X.encard) :
  ∀ x ∈ X, ∃! p ∈ P.1, p.v = x ∧ p.support ∩ X = {x} := by
  have h_inj : Set.InjOn (fun p : G.ABPath A X => p.v.1) P.1 := by
    intro p hp q hq (h_eq : p.v.1 = q.v.1)
    by_contra hneq
    have : p.v.1 ∈ q.support := h_eq ▸ q.p.1.end_mem_support
    exact Set.disjoint_left.mp (P.2 hp hq hneq) (p.p.1.end_mem_support) this
  have h_img_eq : (fun p : G.ABPath A X => p.v.1) '' P.1 = X := by
    have h_sub : (fun p : G.ABPath A X => p.v.1) '' P.1 ⊆ X := Set.image_subset_iff.mpr fun p _ => p.v.2
    have h_encard : ((fun p : G.ABPath A X => p.v.1) '' P.1).encard = X.encard := by
      rw [h_inj.encard_image, hP_card]
    exact (hX_fin.subset h_sub).eq_of_subset_of_encard_le h_sub (h_encard ▸ le_refl _)
  have h_surj : ∀ x ∈ X, ∃ p ∈ P.1, (p : G.ABPath A X).v.1 = x := by
    intro x hx; rw [← h_img_eq] at hx; exact hx
  intro x hx
  obtain ⟨p, hp, hpv⟩ := h_surj x hx
  by_contra h_contra
  obtain ⟨z, hzP, hzX, hzne⟩ : ∃ z ∈ p.p.1.support, z ∈ X ∧ z ≠ x := by
    by_contra h_all
    push_neg at h_all
    apply h_contra
    refine ⟨p, ⟨hp, hpv, ?_⟩, fun q ⟨hq1, hq2, _⟩ => ?_⟩
    · ext z; simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
      exact ⟨fun ⟨hz1, hz2⟩ => h_all z hz1 hz2, fun hz => hz ▸ ⟨hpv ▸ p.p.1.end_mem_support, hx⟩⟩
    · exact (h_inj hp hq1 (show p.v.1 = q.v.1 by rw [hpv, hq2])).symm
  obtain ⟨q, hqP, hqv⟩ := h_surj z hzX
  have hneq : p ≠ q := by
    intro h_eq; rw [h_eq, hqv] at hpv; exact hzne hpv
  exact Set.disjoint_left.mp (P.2 hp hqP hneq) (show z ∈ p.support from hzP)
    (show z ∈ q.support from by simp only [ABPath.support, Set.mem_setOf_eq]; rw [← hqv]; exact q.p.1.end_mem_support)

/-
If an A-X path intersects X only at its endpoint, then any prefix ending at a vertex not in X avoids X entirely.
-/
lemma SimpleGraph.ABPath_prefix_avoids_X (G : SimpleGraph V) (A X : Set V) (X_fin : Set V)
  (p : G.ABPath A X)
  (hp_X : p.support ∩ X_fin = {p.v.1})
  (z : V)
  (hz : z ∈ p.p.1.support)
  (hzX : z ∉ X_fin) :
  (↑(p.p.1.takeUntil z hz).support.toFinset : Set V) ∩ X_fin = ∅ := by
    simp only [Set.eq_empty_iff_forall_notMem, Set.mem_inter_iff, Finset.mem_coe, not_and]
    intro a ha haX
    have ha_support : a ∈ p.p.1.support :=
      Walk.support_takeUntil_subset p.p.1 hz (List.mem_toFinset.mp ha)
    have ha_eq : a = p.v.1 := by
      have h1 : a ∈ p.support ∩ X_fin := ⟨ha_support, haX⟩
      rw [hp_X] at h1
      exact h1
    rw [ha_eq] at ha
    have hne : p.v.1 ≠ z := by
      intro heq; rw [← heq] at hzX
      have : p.v.1 ∈ p.support ∩ X_fin := by rw [hp_X]; rfl
      exact hzX this.2
    exact (SimpleGraph.Walk.endpoint_notMem_support_takeUntil p.p.2 hz hne)
      (List.mem_toFinset.mp ha)

/-
If a walk is a path, and we drop the prefix until a vertex w (where w is not the start), then the start vertex is not in the remaining suffix.
-/
lemma SimpleGraph.Walk.start_notMem_support_dropUntil {G : SimpleGraph V}
  {u v w : V} {p : G.Walk u v} (hp : p.IsPath) (hw : w ∈ p.support) (h : u ≠ w) :
  u ∉ (p.dropUntil w hw).support := by
    have h_no_repeat : ∀ v ∈ p.support, v = u → v ∉ (p.dropUntil w hw).support := by
      have h_support : ∀ v ∈ p.support, v = u → v ∉ (p.dropUntil w hw).support := by
        intro v hv hvu
        have h_lift : ∀ w' ∈ p.support, w' ∉ (p.dropUntil w hw).support → w' = u → v ∉ (p.dropUntil w hw).support := by
          aesop
        exact h_lift u ( by simp ) ( by
          induction p <;> simp_all [ SimpleGraph.Walk.dropUntil ];
          · cases hw;
            · contradiction;
            · contradiction;
          · exact fun h => hp.2 ( SimpleGraph.Walk.support_dropUntil_subset _ _ h ) ) rfl;
      exact h_support;
    exact h_no_repeat u ( p.start_mem_support ) rfl

/-
If an X-B path intersects X only at its start point, then any suffix starting at a vertex not in X avoids X entirely.
-/
lemma SimpleGraph.ABPath_suffix_avoids_X (G : SimpleGraph V) (B X : Set V) (X_fin : Set V)
  (q : G.ABPath X B)
  (hq_X : q.support ∩ X_fin = {q.u.1})
  (z : V)
  (hz : z ∈ q.p.1.support)
  (hzX : z ∉ X_fin) :
  (↑(q.p.1.dropUntil z hz).support.toFinset : Set V) ∩ X_fin = ∅ := by
    simp only [Set.eq_empty_iff_forall_notMem, Set.mem_inter_iff, Finset.mem_coe, not_and]
    intro a ha haX
    have ha_support : a ∈ q.p.1.support :=
      q.p.1.support_dropUntil_subset hz (List.mem_toFinset.mp ha)
    have ha_eq : a = q.u.1 := by
      have h1 : a ∈ q.support ∩ X_fin := ⟨ha_support, haX⟩
      rw [hq_X] at h1
      exact h1
    rw [ha_eq] at ha
    have : q.u.1 ≠ z := by
      intro heq; rw [← heq] at hzX
      have : q.u.1 ∈ q.support ∩ X_fin := by rw [hq_X]; rfl
      exact hzX this.2
    exact (SimpleGraph.Walk.start_notMem_support_dropUntil q.p.2 hz this)
      (List.mem_toFinset.mp ha)

/-
If X separates A and B, and p is an A-X path hitting X only at the end, and q is an X-B path hitting X only at the start, then p and q intersect only at their common endpoint in X (if any).
-/
lemma SimpleGraph.path_intersection_of_separator (X : G.Separator A B) (p : G.ABPath A X.1)
    (q : G.ABPath X.1 B) (hp_X : p.support ∩ X.1 = {p.v.1})
    (hq_X : q.support ∩ X.1 = {q.u.1}) :
    p.p.1.support.toFinset ∩ q.p.1.support.toFinset ⊆ {p.v.1} ∩ {q.u.1} := by
  intro z hz
  simp only [Finset.mem_inter, List.mem_toFinset] at hz
  by_cases hzX : z ∈ X.1
  · simp only [Finset.mem_inter, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · have h1 : z ∈ p.support ∩ X.1 := ⟨hz.1, hzX⟩
      rw [hp_X] at h1; exact h1
    · have h2 : z ∈ q.support ∩ X.1 := ⟨hz.2, hzX⟩
      rw [hq_X] at h2; exact h2
  · exfalso
    have hw1 := SimpleGraph.ABPath_prefix_avoids_X G A X.1 X.1 p hp_X z hz.1 hzX
    have hw2 := SimpleGraph.ABPath_suffix_avoids_X G B X.1 X.1 q hq_X z hz.2 hzX
    have h_walk := X.2 p.u.1 p.u.2 q.v.1 q.v.2
      ((p.p.1.takeUntil z hz.1).append (q.p.1.dropUntil z hz.2))
    obtain ⟨w, hw_mem, hw_X⟩ := h_walk
    rw [SimpleGraph.Walk.support_append] at hw_mem
    rcases List.mem_append.mp hw_mem with hw_mem | hw_mem
    · have : w ∈ (↑(p.p.1.takeUntil z hz.1).support.toFinset : Set V) ∩ X.1 :=
        ⟨Finset.mem_coe.mpr (List.mem_toFinset.mpr hw_mem), hw_X⟩
      rw [hw1] at this; exact this
    · have hw_supp : w ∈ (q.p.1.dropUntil z hz.2).support := List.tail_subset _ hw_mem
      have : w ∈ (↑(q.p.1.dropUntil z hz.2).support.toFinset : Set V) ∩ X.1 :=
        ⟨Finset.mem_coe.mpr (List.mem_toFinset.mpr hw_supp), hw_X⟩
      rw [hw2] at this; exact this

/-
If P is a set of disjoint paths from X to B with size equal to X, then every vertex in X is the start of exactly one path in P, and that path intersects X only at its start.
-/
lemma SimpleGraph.disjoint_paths_prop_start (G : SimpleGraph V) (X B : Set V) (hX_fin : X.Finite)
    (P : G.Joiner X B) (hP_card : P.1.encard = X.encard) :
  ∀ x ∈ X, ∃! p ∈ P.1, p.u = x ∧ p.support ∩ X = {x} := by
  have h_distinct_start : Set.InjOn (fun p : G.ABPath X B => p.u.1) P.1 := by
    intro p hp q hq (h_eq : p.u.1 = q.u.1)
    by_contra hneq
    exact Set.disjoint_left.mp (P.2 hp hq hneq) p.p.1.start_mem_support (h_eq ▸ q.p.1.start_mem_support)
  have h_img_eq : (fun p : G.ABPath X B => p.u.1) '' P.1 = X := by
    have h_sub : (fun p : G.ABPath X B => p.u.1) '' P.1 ⊆ X := Set.image_subset_iff.mpr fun p _ => p.u.2
    have h_encard : ((fun p : G.ABPath X B => p.u.1) '' P.1).encard = X.encard := by
      rw [h_distinct_start.encard_image, hP_card]
    exact (hX_fin.subset h_sub).eq_of_subset_of_encard_le h_sub (h_encard ▸ le_refl _)
  have h_unique_start : ∀ x ∈ X, ∃ p ∈ P.1, (p : G.ABPath X B).u.1 = x := by
    intro x hx; rw [← h_img_eq] at hx; exact hx
  have h_path_X : ∀ x ∈ X, ∀ p ∈ P.1, (p : G.ABPath X B).u.1 = x → p.support ∩ X = {x} := by
    intro x hx p hp hp_start
    ext z; simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · intro ⟨hz1, hz2⟩
      by_contra h_contra
      obtain ⟨q, hqP, hq_start⟩ := h_unique_start z hz2
      have : p ≠ q := by intro h_eq; rw [h_eq, hq_start] at hp_start; exact h_contra hp_start
      exact Set.disjoint_left.mp (P.2 hp hqP this) hz1 (hq_start ▸ q.p.1.start_mem_support)
    · intro hz; exact hz ▸ ⟨hp_start ▸ p.p.1.start_mem_support, hx⟩
  exact fun x hx => by
    obtain ⟨p, hp₁, hp₂⟩ := h_unique_start x hx
    exact ⟨p, ⟨hp₁, hp₂, h_path_X x hx p hp₁ hp₂⟩,
      fun q ⟨hq1, hq2, _⟩ => (h_distinct_start hp₁ hq1 (show p.u.1 = q.u.1 by rw [hp₂, hq2])).symm⟩

/-
If p and q are paths that intersect only at the join point, their concatenation is a path.
-/
lemma SimpleGraph.Walk.IsPath_append_of_support_inter_subset_one {G : SimpleGraph V}
  {u v w : V} (p : G.Walk u v) (q : G.Walk v w)
  (hp : p.IsPath) (hq : q.IsPath)
  (h_inter : p.support.toFinset ∩ q.support.toFinset ⊆ {v}) :
  (p.append q).IsPath := by
    have hpq_distinct : ∀ x ∈ p.support, x ≠ v → x ∉ q.support := by
      intro x hx hxv hxq; specialize h_inter ( Finset.mem_inter_of_mem ( List.mem_toFinset.mpr hx ) ( List.mem_toFinset.mpr hxq ) ) ; aesop;
    cases p <;> cases q <;> simp_all [ SimpleGraph.Walk.isPath_def ];
    simp_all [ SimpleGraph.Walk.support_append ];
    rw [ List.nodup_append ] ; aesop

/-
If p is an A-X path ending at x, and q is an X-B path starting at x, and both intersect X only at x, then their concatenation is a path.
-/
lemma SimpleGraph.joined_path_is_path (G : SimpleGraph V) (A B : Set V)
  (X : G.Separator A B)
  (x : V)
  (p : G.ABPath A X.1) (h_p : p.v = x) (h_p_X : p.support ∩ X.1 = {x})
  (q : G.ABPath X.1 B) (h_q : q.u = x) (h_q_X : q.support ∩ X.1 = {x}) :
  ((p.p.1.copy rfl h_p).append (q.p.1.copy h_q rfl)).IsPath := by
    have h_support_inter : (p.p.1.copy rfl h_p).support.toFinset ∩ (q.p.1.copy h_q rfl).support.toFinset ⊆ {x} := by
      have h := path_intersection_of_separator X p q
        (by rw [show (p.v : V) = x from h_p]; exact h_p_X)
        (by rw [show (q.u : V) = x from h_q]; exact h_q_X)
      simp only [SimpleGraph.Walk.support_copy]
      exact h.trans (by simp [show (p.v : V) = x from h_p, show (q.u : V) = x from h_q])
    apply_rules [ SimpleGraph.Walk.IsPath_append_of_support_inter_subset_one ];
    · exact (p.p.1.isPath_copy rfl h_p).mpr p.p.2
    · exact (q.p.1.isPath_copy h_q rfl).mpr q.p.2

/-
If we have two pairs of paths (px, qx) and (py, qy) meeting at x and y respectively, and the pairs are disjoint from each other, and cross-intersections are empty due to separation, then the joined paths are disjoint.
-/
lemma SimpleGraph.joined_paths_disjoint (G : SimpleGraph V) (A B : Set V) (X : G.Separator A B)
  (x y : V) (hxy : x ≠ y)
  (px : G.ABPath A X.1) (hpx : px.v = x) (hpx_X : px.support ∩ X.1 = {x})
  (py : G.ABPath A X.1) (hpy : py.v = y) (hpy_X : py.support ∩ X.1 = {y})
  (qx : G.ABPath X.1 B) (hqx : qx.u = x) (hqx_X : qx.support ∩ X.1 = {x})
  (qy : G.ABPath X.1 B) (hqy : qy.u = y) (hqy_X : qy.support ∩ X.1 = {y})
  (hp_disj : Disjoint px.support py.support)
  (hq_disj : Disjoint qx.support qy.support) :
  Disjoint (px.support ∪ qx.support) (py.support ∪ qy.support) := by
    rw [Set.disjoint_iff]
    intro z ⟨hz_left, hz_right⟩
    simp only [Set.mem_union] at hz_left hz_right
    rcases hz_left with hz_px | hz_qx <;> rcases hz_right with hz_py | hz_qy
    · exact (Set.disjoint_left.mp hp_disj hz_px) hz_py
    · -- z ∈ px.support ∩ qy.support
      have h := path_intersection_of_separator X px qy
        (by rw [show (px.v : V) = x from hpx]; exact hpx_X)
        (by rw [show (qy.u : V) = y from hqy]; exact hqy_X)
      have hz_fin : z ∈ px.p.1.support.toFinset ∩ qy.p.1.support.toFinset :=
        Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hz_px, List.mem_toFinset.mpr hz_qy⟩
      have := h hz_fin
      simp only [Finset.mem_inter, Finset.mem_singleton] at this
      exact hxy ((hpx.symm.trans this.1.symm).trans (this.2.trans hqy))
    · -- z ∈ qx.support ∩ py.support
      have h := path_intersection_of_separator X py qx
        (by rw [show (py.v : V) = y from hpy]; exact hpy_X)
        (by rw [show (qx.u : V) = x from hqx]; exact hqx_X)
      have hz_fin : z ∈ py.p.1.support.toFinset ∩ qx.p.1.support.toFinset :=
        Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hz_py, List.mem_toFinset.mpr hz_qx⟩
      have := h hz_fin
      simp only [Finset.mem_inter, Finset.mem_singleton] at this
      exact hxy ((hqx.symm.trans this.2.symm).trans (this.1.trans hpy))
    · exact (Set.disjoint_left.mp hq_disj hz_qx) hz_qy

/-
If X separates A and B, and we have k disjoint paths from A to X and k disjoint paths from X to B, then we can combine them to form k disjoint paths from A to B.
-/
theorem SimpleGraph.disjoint_paths_join (G : SimpleGraph V) (A B : Set V) (X : G.Separator A B) (k : ℕ∞)
  (hX_fin : X.1.Finite)
  (hX_card : X.1.encard = k) (P_A : G.Joiner A X.1) (hP_A_card : P_A.1.encard = k) (P_B : G.Joiner X.1 B)
  (hP_B_card : P_B.1.encard = k) : ∃ P : G.Joiner A B, P.1.encard = k := by
  have h_end := disjoint_paths_prop G A X.1 hX_fin P_A (hP_A_card.trans hX_card.symm)
  have h_start := disjoint_paths_prop_start G X.1 B hX_fin P_B (hP_B_card.trans hX_card.symm)
  have h_end_ex : ∀ x ∈ X.1, ∃ p ∈ P_A.1, (p : G.ABPath A X.1).v.1 = x ∧ p.support ∩ X.1 = {x} :=
    fun x hx => let ⟨p, ⟨hp1, hp2, hp3⟩, _⟩ := h_end x hx; ⟨p, hp1, hp2, hp3⟩
  have h_start_ex : ∀ x ∈ X.1, ∃ q ∈ P_B.1, (q : G.ABPath X.1 B).u.1 = x ∧ q.support ∩ X.1 = {x} :=
    fun x hx => let ⟨q, ⟨hq1, hq2, hq3⟩, _⟩ := h_start x hx; ⟨q, hq1, hq2, hq3⟩
  choose pa hpa_mem hpa_end hpa_inter using h_end_ex
  choose qb hqb_mem hqb_start hqb_inter using h_start_ex
  -- Build joined path for each x ∈ X.1
  let joinPath : X.1 → G.ABPath A B := fun ⟨x, hx⟩ =>
    ⟨(pa x hx).u, (qb x hx).v,
     (pa x hx).p.1.copy rfl (hpa_end x hx) |>.append ((qb x hx).p.1.copy (hqb_start x hx) rfl),
     joined_path_is_path G A B X x (pa x hx) (hpa_end x hx) (hpa_inter x hx)
                           (qb x hx) (hqb_start x hx) (hqb_inter x hx)⟩
  -- Membership in join support decomposes into sub-path supports
  have h_mem_join : ∀ (x : V) (hx : x ∈ X.1) (z : V),
      z ∈ (joinPath ⟨x, hx⟩).support → z ∈ (pa x hx).p.1.support ∨ z ∈ (qb x hx).p.1.support := by
    intro x hx z hz
    simp only [joinPath, ABPath.support, Set.mem_setOf_eq] at hz
    rw [Walk.mem_support_append_iff, Walk.support_copy, Walk.support_copy] at hz
    exact hz
  -- pa x ≠ pa y when x ≠ y
  have hpa_ne : ∀ x hx y hy, x ≠ y → pa x hx ≠ pa y hy := fun x hx y hy hxy h_eq =>
    hxy ((hpa_end x hx).symm.trans (congrArg (fun p => p.v.1) h_eq |>.trans (hpa_end y hy)))
  -- qb x ≠ qb y when x ≠ y
  have hqb_ne : ∀ x hx y hy, x ≠ y → qb x hx ≠ qb y hy := fun x hx y hy hxy h_eq =>
    hxy ((hqb_start x hx).symm.trans (congrArg (fun p => p.u.1) h_eq |>.trans (hqb_start y hy)))
  -- Injectivity of joinPath
  have h_inj : Function.Injective joinPath := by
    intro ⟨x, hx⟩ ⟨y, hy⟩ h_eq
    simp only [Subtype.mk.injEq]
    have h_u_eq : (pa x hx).u.1 = (pa y hy).u.1 := by
      have := congrArg (fun p => (ABPath.u p).1) h_eq
      simp only [joinPath] at this; exact this
    have h_pa_eq : pa x hx = pa y hy := by
      by_contra h_ne
      exact Set.disjoint_left.mp (P_A.2 (hpa_mem x hx) (hpa_mem y hy) h_ne)
        (pa x hx).p.1.start_mem_support (h_u_eq ▸ (pa y hy).p.1.start_mem_support)
    exact (hpa_end x hx).symm.trans (congrArg (fun p => p.v.1) h_pa_eq |>.trans (hpa_end y hy))
  -- Pairwise disjointness
  have h_disj : disjointPaths (Set.range joinPath) := by
    rintro p ⟨⟨x, hx⟩, rfl⟩ q ⟨⟨y, hy⟩, rfl⟩ hpq
    have hxy : x ≠ y := fun h => by subst h; exact hpq rfl
    rw [Set.disjoint_left]; intro z hz1 hz2
    rcases h_mem_join x hx z hz1, h_mem_join y hy z hz2 with ⟨hzpx | hzqx, hzpy | hzqy⟩
    · exact Set.disjoint_left.mp (P_A.2 (hpa_mem x hx) (hpa_mem y hy) (hpa_ne x hx y hy hxy)) hzpx hzpy
    · have h := path_intersection_of_separator X (pa x hx) (qb y hy)
        (by rw [show ((pa x hx).v : V) = x from hpa_end x hx]; exact hpa_inter x hx)
        (by rw [show ((qb y hy).u : V) = y from hqb_start y hy]; exact hqb_inter y hy)
      have hz_mem := h (Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hzpx, List.mem_toFinset.mpr hzqy⟩)
      simp only [Finset.mem_inter, Finset.mem_singleton] at hz_mem
      have h1 : z = x := hz_mem.1.trans (hpa_end x hx)
      have h2 : z = y := hz_mem.2.trans (hqb_start y hy)
      exact hxy (h1.symm.trans h2)
    · have h := path_intersection_of_separator X (pa y hy) (qb x hx)
        (by rw [show ((pa y hy).v : V) = y from hpa_end y hy]; exact hpa_inter y hy)
        (by rw [show ((qb x hx).u : V) = x from hqb_start x hx]; exact hqb_inter x hx)
      have hz_mem := h (Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hzpy, List.mem_toFinset.mpr hzqx⟩)
      simp only [Finset.mem_inter, Finset.mem_singleton] at hz_mem
      have h1 : z = y := hz_mem.1.trans (hpa_end y hy)
      have h2 : z = x := hz_mem.2.trans (hqb_start x hx)
      exact hxy (h2.symm.trans h1)
    · exact Set.disjoint_left.mp (P_B.2 (hqb_mem x hx) (hqb_mem y hy) (hqb_ne x hx y hy hxy)) hzqx hzqy
  have h_card : (Set.range joinPath).encard = k := by
    rw [show Set.range joinPath = joinPath '' Set.univ from Set.image_univ.symm,
        h_inj.injOn.encard_image]; simp [hX_card]
  exact ⟨⟨Set.range joinPath, h_disj⟩, h_card⟩

/-
The size of the preimage of a set Y containing the contracted vertex is |Y| + 1.
-/
lemma SimpleGraph.contractEdge_separator_lift_card (x y : V) (hxy : x ≠ y)
  (Y : Set (Quotient (SimpleGraph.contractEdgeSetoid x y)))
  (h_ve : SimpleGraph.contractEdge_vertex x y ∈ Y) :
  (SimpleGraph.contractEdge_preimage x y Y).encard = Y.encard + 1 := by
  simp [encard_preimage_contractEdge hxy, h_ve]

/-
If a walk is a path and the start is not the end, it can be decomposed into a prefix path avoiding the end vertex, and a final edge.
-/
lemma SimpleGraph.Walk.exists_prefix_path_of_path_ne {G : SimpleGraph V}
  {u v : V} (p : G.Walk u v) (hp : p.IsPath) (h_ne : u ≠ v) :
  ∃ (w : V) (q : G.Walk u w),
    G.Adj w v ∧
    q.IsPath ∧
    v ∉ q.support ∧
    q.support.toFinset ⊆ p.support.toFinset := by
      simp +zetaDelta at *;
      induction' p with u v p ih;
      · contradiction;
      · rename_i h₁ h₂ h₃;
        by_cases h : p = ih;
        · aesop;
        · obtain ⟨ w, hw₁, q, hq₁, hq₂, hq₃ ⟩ := h₃ ( by
            cases h₂ <;> aesop ) h;
          refine' ⟨ w, hw₁, cons h₁ q, _, _, _ ⟩ <;> simp_all
          · exact fun h => hp.2 ( by simpa using hq₃ ( by simpa using h ) );
          · grind

/-
The preimages of disjoint sets in the contracted graph are disjoint in the original graph.
-/
lemma SimpleGraph.contractEdge_preimage_disjoint (x y : V) (s t : Set (Quotient (SimpleGraph.contractEdgeSetoid x y))) (h : Disjoint s t) :
  Disjoint (SimpleGraph.contractEdge_preimage x y s) (SimpleGraph.contractEdge_preimage x y t) := by
    refine Set.disjoint_left.mpr ?_
    intro v hv ht
    exact Set.disjoint_left.mp h
      ((mem_contractEdge_preimage (x := x) (y := y) (Y := s) (v := v)).1 hv)
      ((mem_contractEdge_preimage (x := x) (y := y) (Y := t) (v := v)).1 ht)

/-
If two vertices are adjacent to the endpoints of an edge, there is a path between them using only the endpoints of the edge and themselves.
-/
lemma SimpleGraph.exists_path_between_neighbors_of_edge (G : SimpleGraph V) (x y a b : V) (hxy : G.Adj x y) (ha : G.Adj a x ∨ G.Adj a y) (hb : G.Adj b x ∨ G.Adj b y) (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y) (hbx : b ≠ x) (hby : b ≠ y) : ∃ p : G.Walk a b, p.IsPath ∧ p.support.toFinset ⊆ {a, b, x, y} := by
  rcases ha with ha | ha <;> rcases hb with hb | hb;
  · use SimpleGraph.Walk.cons ha (SimpleGraph.Walk.cons hb.symm SimpleGraph.Walk.nil);
    aesop_cat;
  · use SimpleGraph.Walk.cons ha (SimpleGraph.Walk.cons hxy (SimpleGraph.Walk.cons hb.symm SimpleGraph.Walk.nil));
    aesop_cat;
  · use SimpleGraph.Walk.cons ha (SimpleGraph.Walk.cons hxy.symm (SimpleGraph.Walk.cons hb.symm SimpleGraph.Walk.nil));
    aesop_cat;
  · refine' ⟨ SimpleGraph.Walk.cons ha ( SimpleGraph.Walk.cons hb.symm SimpleGraph.Walk.nil ), _, _ ⟩ <;> simp_all [ SimpleGraph.Walk.isPath_def ];
    · grind;
    · simp [ Finset.insert_subset_iff ]

/-
Extending a path that avoids x and y by an edge to x (or y) results in a path.
-/
lemma SimpleGraph.path_extension_to_contraction_endpoint {G : SimpleGraph V} {u w : V} (x y : V) (v : V)
  (q : G.Walk u w) (hq_path : q.IsPath)
  (hx_avoid : x ∉ q.support) (hy_avoid : y ∉ q.support)
  (hv : v = x ∨ v = y)
  (h_adj : G.Adj w v) :
  (q.append (SimpleGraph.Walk.cons h_adj SimpleGraph.Walk.nil)).IsPath := by
    cases hv <;> simp_all [ SimpleGraph.Walk.isPath_def ];
    · rw [ SimpleGraph.Walk.support_append ];
      rw [ List.nodup_append ] ; aesop;
    · simp_all [ SimpleGraph.Walk.support_append ];
      rw [ List.nodup_append ] ; aesop

/-
If the projection of a set is contained in another set, and the contracted vertex is in that other set, then extending the first set by an endpoint of the contracted edge keeps it within the preimage.
-/
lemma SimpleGraph.support_subset_preimage_extension (x y : V)
  (q_support : Set V) (p'_support : Set (Quotient (SimpleGraph.contractEdgeSetoid x y))) (v : V)
  (h_subset : (⟦·⟧) '' q_support ⊆ p'_support)
  (h_ve : SimpleGraph.contractEdge_vertex x y ∈ p'_support)
  (hv : v = x ∨ v = y) :
  (q_support ∪ {v}) ⊆ SimpleGraph.contractEdge_preimage x y p'_support := by
    intro u hu
    simp only [Set.mem_union, Set.mem_singleton_iff] at hu
    simp only [contractEdge_preimage, Set.mem_setOf_eq]
    rcases hu with hu | hu
    · exact h_subset ⟨u, hu, rfl⟩
    · subst hu
      rcases hv with rfl | rfl
      · exact h_ve
      · rwa [contractEdge_vertex_eq] at h_ve

/-
If a path ends at a vertex whose projection is adjacent to the contracted vertex, and the path avoids the contracted edge's endpoints, it can be extended to one of the endpoints.
-/
lemma SimpleGraph.lift_path_extension_step (G : SimpleGraph V) (x y : V)
  (u w : V) (q : G.Walk u w)
  (hq_path : q.IsPath)
  (hx_avoid : x ∉ q.support) (hy_avoid : y ∉ q.support)
  (hw_proj_adj : (G.contractEdge x y).Adj ⟦w⟧ (SimpleGraph.contractEdge_vertex x y)) :
  ∃ (v : V) (p : G.Walk u v),
    (v = x ∨ v = y) ∧
    p.IsPath ∧
    p.support.toFinset ⊆ q.support.toFinset ∪ {v} ∧
    p.support.toFinset ∩ {x, y} = {v} := by
      have h_w_adj : G.Adj w x ∨ G.Adj w y := by
        have := SimpleGraph.contractEdge_adj_lift_vertex G x y w ?_ hw_proj_adj <;> aesop;
      cases' h_w_adj with h h;
      · refine' ⟨ x, q.append ( SimpleGraph.Walk.cons h SimpleGraph.Walk.nil ), Or.inl rfl, _, _, _ ⟩ <;> simp_all [ SimpleGraph.Walk.isPath_def ];
        · simp_all [ SimpleGraph.Walk.support_append ];
          rw [ List.nodup_append ] ; aesop;
        · simp [ SimpleGraph.Walk.support_append ];
        · ext ; aesop;
      · use y;
        use q.append (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil);
        simp_all [ SimpleGraph.Walk.isPath_def ];
        simp_all [ SimpleGraph.Walk.support_append ];
        rw [ List.nodup_append ] ; aesop

/-
A path in the contracted graph ending at the contracted vertex can be lifted to a path in the original graph ending at one of the contracted edge's endpoints.
-/
lemma SimpleGraph.lift_path_to_contraction_end (G : SimpleGraph V) (A : Set V) (x y : V)
  (u' : Quotient (SimpleGraph.contractEdgeSetoid x y))
  (p' : (G.contractEdge x y).Walk u' (SimpleGraph.contractEdge_vertex x y))
  (hp'_path : p'.IsPath)
  (hu' : u' ∈ SimpleGraph.contractEdge_liftSet x y A)
  (h_ne : u' ≠ SimpleGraph.contractEdge_vertex x y) :
  ∃ (u v : V) (p : G.Walk u v),
    u ∈ A ∧
    (v = x ∨ v = y) ∧
    p.IsPath ∧
    (↑p.support.toFinset : Set V) ⊆ SimpleGraph.contractEdge_preimage x y (↑p'.support.toFinset : Set _) ∧
    p.support.toFinset ∩ {x, y} = {v} := by
  obtain ⟨ w', q', hq'_adj, hq'_path, hq'_avoid, hq'_sub ⟩ :=
    SimpleGraph.Walk.exists_prefix_path_of_path_ne p' hp'_path h_ne;
  -- Normalize Finset subset to List level to avoid DecidableEq instance mismatch on quotient
  simp only [Finset.subset_iff, List.mem_toFinset] at hq'_sub
  obtain ⟨u, w, q, hu, hw, hq_path, hq_support⟩ : ∃ u w : V, ∃ q : G.Walk u w,
      u ∈ A ∧ ⟦u⟧ = u' ∧ ⟦w⟧ = w' ∧ q.IsPath ∧ (∀ z, z ∈ q.support → ⟦z⟧ ∈ q'.support) ∧
      x ∉ q.support ∧ y ∉ q.support := by
    obtain ⟨u, w, q, hu, _, hw1, hw2, hq_path, hq_img, hx, hy⟩ :=
      SimpleGraph.lift_path_avoiding_contraction_AB G A Set.univ x y q' hq'_avoid hu'
        ⟨Classical.choose (Quotient.exists_rep w'), trivial, Classical.choose_spec (Quotient.exists_rep w')⟩
    simp only [Finset.subset_iff, Finset.mem_image, List.mem_toFinset] at hq_img
    exact ⟨u, w, q, hu, hw1, hw2, hq_path, fun z hz => hq_img ⟨z, hz, rfl⟩, hx, hy⟩
  obtain ⟨v, p, hv, hp_path, hp_support, hp_xy⟩ : ∃ v : V, ∃ p : G.Walk u v, (v = x ∨ v = y) ∧ p.IsPath ∧ p.support.toFinset ⊆ q.support.toFinset ∪ {v} ∧ p.support.toFinset ∩ {x, y} = {v} := by
    have := SimpleGraph.lift_path_extension_step G x y u w q hq_support.1 hq_support.2.2.1 hq_support.2.2.2 ?_ <;> aesop;
  refine ⟨u, v, p, hu, hv, hp_path, ?_, hp_xy⟩
  -- Show support subset of preimage
  intro z hz
  simp only [Finset.mem_coe, List.mem_toFinset] at hz
  have hz_fin : z ∈ q.support.toFinset ∪ {v} := hp_support (List.mem_toFinset.mpr hz)
  rcases Finset.mem_union.mp hz_fin with hz_q | hz_v
  · -- z is in q's support
    have h1 : ⟦z⟧ ∈ q'.support := hq_support.2.1 z (List.mem_toFinset.mp hz_q)
    have h2 : ⟦z⟧ ∈ p'.support := hq'_sub h1
    simp only [contractEdge_preimage, Set.mem_setOf_eq, Finset.mem_coe]
    exact List.mem_toFinset.mpr h2
  · -- z = v (which is x or y)
    simp only [Finset.mem_singleton] at hz_v
    simp only [contractEdge_preimage, Set.mem_setOf_eq, Finset.mem_coe]
    have h_end := p'.end_mem_support
    rcases hv with rfl | rfl
    · rw [hz_v]; exact List.mem_toFinset.mpr h_end
    · rw [hz_v, ← contractEdge_vertex_eq]; exact List.mem_toFinset.mpr h_end

/-
A path in the contracted graph starting at the contracted vertex can be lifted to a path in the original graph starting at one of the contracted edge's endpoints.
-/
lemma SimpleGraph.lift_path_from_contraction_start (G : SimpleGraph V) (B : Set V) (x y : V)
  (v' : Quotient (SimpleGraph.contractEdgeSetoid x y))
  (p' : (G.contractEdge x y).Walk (SimpleGraph.contractEdge_vertex x y) v')
  (hp'_path : p'.IsPath)
  (hv' : v' ∈ SimpleGraph.contractEdge_liftSet x y B)
  (h_ne : v' ≠ SimpleGraph.contractEdge_vertex x y) :
  ∃ (u v : V) (p : G.Walk u v),
    (u = x ∨ u = y) ∧
    v ∈ B ∧
    p.IsPath ∧
    (↑p.support.toFinset : Set V) ⊆ SimpleGraph.contractEdge_preimage x y (↑p'.support.toFinset : Set _) ∧
    p.support.toFinset ∩ {x, y} = {u} := by
      have h_lift_reversed : ∃ u v : V, ∃ p : G.Walk u v, u ∈ B ∧
        (v = x ∨ v = y) ∧
        p.IsPath ∧
        (↑p.support.toFinset : Set V) ⊆ SimpleGraph.contractEdge_preimage x y (↑p'.reverse.support.toFinset : Set _) ∧
        p.support.toFinset ∩ {x, y} = {v} := by
          apply_rules [ SimpleGraph.lift_path_to_contraction_end ];
          · exact (Walk.isPath_reverse_iff p').mpr hp'_path;
      obtain ⟨ u, v, p, hu, hv, hp, hp', hp'' ⟩ := h_lift_reversed; use v, u, p.reverse; aesop;

/-
Two paths ending and starting at the endpoints of an edge can be joined into a single path if they are otherwise disjoint and avoid the edge's endpoints internally.
-/
lemma SimpleGraph.join_paths_through_edge (G : SimpleGraph V) (x y : V) (hxy : G.Adj x y)
  {u_start u_end v_start v_end : V}
  (p1 : G.Walk u_start u_end) (p2 : G.Walk v_start v_end)
  (hp1_path : p1.IsPath) (hp2_path : p2.IsPath)
  (hu_end : u_end = x ∨ u_end = y)
  (hv_start : v_start = x ∨ v_start = y)
  (hp1_end : p1.support.toFinset ∩ {x, y} = {u_end})
  (hp2_start : p2.support.toFinset ∩ {x, y} = {v_start})
  (h_disjoint : Disjoint (p1.support.toFinset \ {x, y}) (p2.support.toFinset \ {x, y})) :
  ∃ (q : G.Walk u_start v_end), q.IsPath ∧ q.support.toFinset ⊆ p1.support.toFinset ∪ p2.support.toFinset := by
    by_cases h_cases : u_end = v_start;
    · refine' ⟨ p1.append ( h_cases ▸ p2 ), _, _ ⟩ <;> simp_all
      · have h_concat_path : (p1.append (h_cases ▸ p2)).IsPath := by
          have h_disjoint : Disjoint (p1.support.toFinset \ {v_start}) (p2.support.toFinset \ {v_start}) := by
            simp_all [ Finset.disjoint_left ];
            intro a ha ha' ha''; specialize h_disjoint ha; simp_all [ Finset.eq_singleton_iff_unique_mem ] ;
            grind +ring
          apply SimpleGraph.Walk.IsPath_append_of_support_inter_subset_one;
          · assumption;
          · aesop;
          · intro v hv; simp_all [ Finset.disjoint_left ] ;
            grind;
        exact h_concat_path;
      · intro v hv; aesop;
    · obtain ⟨h_edge, h_cases⟩ : G.Adj u_end v_start ∧ (u_end = x ∧ v_start = y ∨ u_end = y ∧ v_start = x) := by
        cases hu_end <;> cases hv_start <;> simp_all [ SimpleGraph.adj_comm ];
      use p1.append (SimpleGraph.Walk.cons h_edge p2);
      simp_all [ Finset.subset_iff, SimpleGraph.Walk.isPath_def ];
      simp_all [ Finset.disjoint_left ];
      simp_all [ Finset.ext_iff, SimpleGraph.Walk.support_append ];
      grind

/-
A path can be split at any vertex in its support into two paths that intersect only at that vertex.
-/
lemma SimpleGraph.Walk.split_at_vertex {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (hp : p.IsPath) (z : V) (hz : z ∈ p.support) :
  ∃ (p1 : G.Walk u z) (p2 : G.Walk z v),
    p1.IsPath ∧ p2.IsPath ∧
    p1.support.toFinset ∩ p2.support.toFinset = {z} ∧
    p1.support.toFinset ∪ p2.support.toFinset = p.support.toFinset := by
      simp +zetaDelta at *;
      obtain ⟨p1, p2, hp1, hp2, hp_split⟩ : ∃ p1 : G.Walk u z, ∃ p2 : G.Walk z v, p = p1.append p2 ∧ p1.IsPath ∧ p2.IsPath := by
        exact ⟨ p.takeUntil z hz, p.dropUntil z hz, by rw [ SimpleGraph.Walk.take_spec ], by exact hp.takeUntil _, by exact hp.dropUntil _ ⟩;
      refine' ⟨ p1, hp2, p2, hp_split, _, _ ⟩ <;> simp_all [ Finset.ext_iff ];
      intro a; constructor <;> intro ha ; simp_all [ SimpleGraph.Walk.isPath_def ] ;
      · induction' p1 with u' p1 ih generalizing a ; induction' p2 with v' p2 ih' ; aesop;
        · aesop;
        · simp_all [ SimpleGraph.Walk.support ];
          grind +ring;
      · aesop

/-
If a walk is a path, its support intersects the singleton set of its endpoint exactly at that point.
-/
lemma SimpleGraph.Walk.IsPath.support_inter_singleton_eq_of_end {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (_hp : p.IsPath) :
  p.support.toFinset ∩ {v} = {v} := by
    cases p <;> simp

/-
The support of a walk intersects the singleton set of its start point exactly at that point.
-/
lemma SimpleGraph.Walk.IsPath.support_inter_singleton_eq_of_start {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
  p.support.toFinset ∩ {u} = {u} := by
    ext; simp

/-
If two sets in the contracted graph are disjoint away from the contracted vertex, their preimages in the original graph are disjoint away from the endpoints of the contracted edge.
-/
lemma SimpleGraph.contractEdge_preimage_disjoint_away_from_endpoints (x y : V)
  (s t : Set (Quotient (SimpleGraph.contractEdgeSetoid x y)))
  (h_disj : Disjoint (s \ {SimpleGraph.contractEdge_vertex x y}) (t \ {SimpleGraph.contractEdge_vertex x y})) :
  Disjoint (SimpleGraph.contractEdge_preimage x y s \ {x, y}) (SimpleGraph.contractEdge_preimage x y t \ {x, y}) := by
    refine Set.disjoint_left.mpr ?_
    intro a ha hb
    rcases ha with ⟨ha_pre, ha_not⟩
    rcases hb with ⟨hb_pre, _⟩
    have hproj_ne : ⟦a⟧ ≠ SimpleGraph.contractEdge_vertex x y := by
      intro hproj
      have hxy : a = x ∨ a = y := (SimpleGraph.contractEdgeProj_eq_vertex_iff x y a).1 hproj
      exact ha_not (by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hxy)
    have ha_s : ⟦a⟧ ∈ s :=
      (mem_contractEdge_preimage (x := x) (y := y) (Y := s) (v := a)).1 ha_pre
    have hb_t : ⟦a⟧ ∈ t :=
      (mem_contractEdge_preimage (x := x) (y := y) (Y := t) (v := a)).1 hb_pre
    have ha_s' : ⟦a⟧ ∈ s \ {SimpleGraph.contractEdge_vertex x y} :=
      ⟨ha_s, hproj_ne⟩
    have hb_t' : ⟦a⟧ ∈ t \ {SimpleGraph.contractEdge_vertex x y} :=
      ⟨hb_t, hproj_ne⟩
    exact (Set.disjoint_left.mp h_disj) ha_s' hb_t'

/-
If two paths in the contracted graph intersect only at the contracted vertex, their lifted paths in the original graph are disjoint away from the endpoints of the contracted edge.
-/
lemma SimpleGraph.lifted_paths_disjoint (G : SimpleGraph V) (x y : V)
  (p1' : (G.contractEdge x y).Walk ⟦x⟧ (SimpleGraph.contractEdge_vertex x y)) -- start doesn't matter much
  (p2' : (G.contractEdge x y).Walk (SimpleGraph.contractEdge_vertex x y) ⟦x⟧) -- end doesn't matter much
  (h_inter : p1'.support.toFinset ∩ p2'.support.toFinset = {SimpleGraph.contractEdge_vertex x y})
  (p1 : G.Walk x x) -- endpoints don't matter for support
  (p2 : G.Walk x x) -- endpoints don't matter for support
  (h_sub1 : (↑p1.support.toFinset : Set V) ⊆ SimpleGraph.contractEdge_preimage x y (↑p1'.support.toFinset : Set _))
  (h_sub2 : (↑p2.support.toFinset : Set V) ⊆ SimpleGraph.contractEdge_preimage x y (↑p2'.support.toFinset : Set _)) :
  Disjoint (p1.support.toFinset \ {x, y}) (p2.support.toFinset \ {x, y}) := by
    have h_disj_sets : Disjoint ((↑p1'.support.toFinset : Set _) \ {SimpleGraph.contractEdge_vertex x y}) ((↑p2'.support.toFinset : Set _) \ {SimpleGraph.contractEdge_vertex x y}) := by
      rw [Set.disjoint_left]
      intro z ⟨hz1, hz_ne⟩ ⟨hz2, _⟩
      have : z ∈ p1'.support.toFinset ∩ p2'.support.toFinset :=
        Finset.mem_inter.mpr ⟨Finset.mem_coe.mp hz1, Finset.mem_coe.mp hz2⟩
      rw [h_inter] at this
      exact hz_ne (Finset.mem_singleton.mp this ▸ Set.mem_singleton _)
    have h_preimage_disj := SimpleGraph.contractEdge_preimage_disjoint_away_from_endpoints x y _ _ h_disj_sets
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    simp only [Finset.mem_sdiff, List.mem_toFinset, Finset.mem_insert, Finset.mem_singleton] at hz1 hz2
    have hz1_set : z ∈ SimpleGraph.contractEdge_preimage x y (↑p1'.support.toFinset) \ ({x, y} : Set V) :=
      ⟨h_sub1 (Finset.mem_coe.mpr (List.mem_toFinset.mpr hz1.1)), by simp [Set.mem_insert_iff]; tauto⟩
    have hz2_set : z ∈ SimpleGraph.contractEdge_preimage x y (↑p2'.support.toFinset) \ ({x, y} : Set V) :=
      ⟨h_sub2 (Finset.mem_coe.mpr (List.mem_toFinset.mpr hz2.1)), by simp [Set.mem_insert_iff]; tauto⟩
    exact Set.disjoint_left.mp h_preimage_disj hz1_set hz2_set

/-
If two paths in the contracted graph meet only at the contracted vertex, they can be lifted to paths in the original graph that are disjoint away from the contracted edge's endpoints.
-/
lemma SimpleGraph.lift_split_paths (G : SimpleGraph V) (A B : Set V) (x y : V)
  (u' v' : Quotient (SimpleGraph.contractEdgeSetoid x y))
  (p1' : (G.contractEdge x y).Walk u' (SimpleGraph.contractEdge_vertex x y))
  (p2' : (G.contractEdge x y).Walk (SimpleGraph.contractEdge_vertex x y) v')
  (hp1'_path : p1'.IsPath)
  (hp2'_path : p2'.IsPath)
  (h_inter : p1'.support.toFinset ∩ p2'.support.toFinset = {SimpleGraph.contractEdge_vertex x y})
  (h_u_ne : u' ≠ SimpleGraph.contractEdge_vertex x y)
  (h_v_ne : v' ≠ SimpleGraph.contractEdge_vertex x y)
  (hu' : u' ∈ SimpleGraph.contractEdge_liftSet x y A)
  (hv' : v' ∈ SimpleGraph.contractEdge_liftSet x y B) :
  ∃ (u_start u_end : V) (p1 : G.Walk u_start u_end) (v_start v_end : V) (p2 : G.Walk v_start v_end),
    u_start ∈ A ∧ v_end ∈ B ∧
    (u_end = x ∨ u_end = y) ∧ (v_start = x ∨ v_start = y) ∧
    p1.IsPath ∧ p2.IsPath ∧
    (↑p1.support.toFinset : Set V) ⊆ SimpleGraph.contractEdge_preimage x y (↑p1'.support.toFinset : Set _) ∧
    (↑p2.support.toFinset : Set V) ⊆ SimpleGraph.contractEdge_preimage x y (↑p2'.support.toFinset : Set _) ∧
    p1.support.toFinset ∩ {x, y} = {u_end} ∧
    p2.support.toFinset ∩ {x, y} = {v_start} ∧
    Disjoint (p1.support.toFinset \ {x, y}) (p2.support.toFinset \ {x, y}) := by
  obtain ⟨u_start, u_end, p1, hu_start_A, hu_end_xy, hp1_path, hp1_sub, hp1_xy⟩ :=
    SimpleGraph.lift_path_to_contraction_end G A x y u' p1' hp1'_path hu' h_u_ne
  obtain ⟨v_start, v_end, p2, hv_start_xy, hv_end_B, hp2_path, hp2_sub, hp2_xy⟩ :=
    SimpleGraph.lift_path_from_contraction_start G B x y v' p2' hp2'_path hv' h_v_ne
  refine ⟨u_start, u_end, p1, v_start, v_end, p2, hu_start_A, hv_end_B, hu_end_xy, hv_start_xy,
    hp1_path, hp2_path, hp1_sub, hp2_sub, hp1_xy, hp2_xy, ?_⟩
  have h_disj_sets : Disjoint ((↑p1'.support.toFinset : Set _) \ {SimpleGraph.contractEdge_vertex x y})
      ((↑p2'.support.toFinset : Set _) \ {SimpleGraph.contractEdge_vertex x y}) := by
    rw [Set.disjoint_left]
    intro z ⟨hz1, hz_ne⟩ ⟨hz2, _⟩
    have : z ∈ p1'.support.toFinset ∩ p2'.support.toFinset :=
      Finset.mem_inter.mpr ⟨Finset.mem_coe.mp hz1, Finset.mem_coe.mp hz2⟩
    rw [h_inter] at this
    exact hz_ne (Finset.mem_singleton.mp this ▸ Set.mem_singleton _)
  have h_preimage_disj := SimpleGraph.contractEdge_preimage_disjoint_away_from_endpoints x y _ _ h_disj_sets
  rw [Finset.disjoint_left]
  intro z hz1 hz2
  simp only [Finset.mem_sdiff, List.mem_toFinset, Finset.mem_insert, Finset.mem_singleton] at hz1 hz2
  have hz1_set : z ∈ SimpleGraph.contractEdge_preimage x y (↑p1'.support.toFinset) \ ({x, y} : Set V) :=
    ⟨hp1_sub (Finset.mem_coe.mpr (List.mem_toFinset.mpr hz1.1)), by simp [Set.mem_insert_iff]; tauto⟩
  have hz2_set : z ∈ SimpleGraph.contractEdge_preimage x y (↑p2'.support.toFinset) \ ({x, y} : Set V) :=
    ⟨hp2_sub (Finset.mem_coe.mpr (List.mem_toFinset.mpr hz2.1)), by simp [Set.mem_insert_iff]; tauto⟩
  exact Set.disjoint_left.mp h_preimage_disj hz1_set hz2_set

/-
A path in the contracted graph passing through the contracted vertex can be lifted to a path in the original graph.
-/
lemma SimpleGraph.lift_path_through_contraction_internal (G : SimpleGraph V) (A B : Set V) (x y : V) (hxy : G.Adj x y)
  (u' v' : Quotient (SimpleGraph.contractEdgeSetoid x y))
  (p' : (G.contractEdge x y).Walk u' v')
  (hp'_path : p'.IsPath)
  (h_ve_mem : SimpleGraph.contractEdge_vertex x y ∈ p'.support)
  (h_u_ne : u' ≠ SimpleGraph.contractEdge_vertex x y)
  (h_v_ne : v' ≠ SimpleGraph.contractEdge_vertex x y)
  (hu' : u' ∈ SimpleGraph.contractEdge_liftSet x y A)
  (hv' : v' ∈ SimpleGraph.contractEdge_liftSet x y B) :
  ∃ (u v : V) (p : G.Walk u v),
    u ∈ A ∧ v ∈ B ∧
    p.IsPath ∧
    (↑p.support.toFinset : Set V) ⊆ SimpleGraph.contractEdge_preimage x y (↑p'.support.toFinset : Set _) := by
      have h_split : ∃ (p1' : (G.contractEdge x y).Walk u' (SimpleGraph.contractEdge_vertex x y))
        (p2' : (G.contractEdge x y).Walk (SimpleGraph.contractEdge_vertex x y) v'),
        p1'.IsPath ∧
        p2'.IsPath ∧
        p1'.support.toFinset ∩ p2'.support.toFinset = {SimpleGraph.contractEdge_vertex x y} ∧
        p1'.support.toFinset ∪ p2'.support.toFinset = p'.support.toFinset := by
          have := SimpleGraph.Walk.split_at_vertex p' hp'_path _ h_ve_mem;
          obtain ⟨p1, p2, hp1, hp2, h1, h2⟩ := this
          refine ⟨p1, p2, hp1, hp2, ?_, ?_⟩
          convert h1 ; convert h2
      obtain ⟨p1', p2', hp1'_path, hp2'_path, h_inter, h_union⟩ := h_split;
      obtain ⟨u_start, u_end, p1, v_start, v_end, p2, hp1, hp2, h_disjoint⟩ :=
        lift_split_paths G A B x y u' v' p1' p2' hp1'_path hp2'_path h_inter h_u_ne h_v_ne hu' hv'
      obtain ⟨q, hq⟩ : ∃ q : G.Walk u_start v_end, q.IsPath ∧ q.support.toFinset ⊆ p1.support.toFinset ∪ p2.support.toFinset := by
        apply SimpleGraph.join_paths_through_edge G x y hxy p1 p2 h_disjoint.2.2.1 h_disjoint.2.2.2.1 h_disjoint.1 h_disjoint.2.1 h_disjoint.2.2.2.2.2.2.1 h_disjoint.2.2.2.2.2.2.2.1 h_disjoint.2.2.2.2.2.2.2.2;
      refine ⟨u_start, v_end, q, hp1, hp2, hq.1, ?_⟩
      intro z hz
      simp only [Finset.mem_coe, List.mem_toFinset] at hz
      have hz_fin := hq.2 (List.mem_toFinset.mpr hz)
      simp only [contractEdge_preimage, Set.mem_setOf_eq, Finset.mem_coe]
      rcases Finset.mem_union.mp hz_fin with h1 | h2
      · have := h_disjoint.2.2.2.2.1 (Finset.mem_coe.mpr h1)
        simp only [contractEdge_preimage, Set.mem_setOf_eq, Finset.mem_coe] at this
        exact h_union ▸ Finset.mem_union.mpr (Or.inl this)
      · have := h_disjoint.2.2.2.2.2.1 (Finset.mem_coe.mpr h2)
        simp only [contractEdge_preimage, Set.mem_setOf_eq, Finset.mem_coe] at this
        exact h_union ▸ Finset.mem_union.mpr (Or.inr this)

/-
A path in the contracted graph that avoids the contracted vertex can be lifted to a path in the original graph that avoids the endpoints of the contracted edge.
-/
lemma SimpleGraph.exists_lifted_ABPath_avoiding (G : SimpleGraph V) (A B : Set V) (x y : V)
  (p' : (G.contractEdge x y).ABPath (SimpleGraph.contractEdge_liftSet x y A) (SimpleGraph.contractEdge_liftSet x y B))
  (hp'_avoid : SimpleGraph.contractEdge_vertex x y ∉ p'.p.1.support) :
  ∃ p : G.ABPath A B, ⟦p.u.1⟧ = p'.u.1 ∧ ⟦p.v.1⟧ = p'.v.1 ∧
    p.p.1.support.toFinset.image (⟦·⟧) ⊆ p'.p.1.support.toFinset ∧
    x ∉ p.p.1.support ∧ y ∉ p.p.1.support := by
      obtain ⟨u, v, q, hu, hv, hq_isPath, hq_support⟩ : ∃ u v : V, ∃ q : G.Walk u v, (u ∈ A ∧ v ∈ B ∧
      ⟦u⟧ = p'.u.1 ∧ ⟦v⟧ = p'.v.1 ∧ q.IsPath ∧ (q.support.toFinset.image (⟦·⟧)) ⊆ p'.p.1.support.toFinset ∧ x ∉ q.support ∧ y ∉ q.support) := by
        rcases p' with ⟨ u', v', p', hp'_path ⟩;
        obtain ⟨ u, v, q, hq ⟩ := SimpleGraph.lift_path_avoiding_contraction_AB G A B x y p' hp'_avoid u'.2 v'.2;
        exact ⟨ u, v, q, hq ⟩;
      refine ⟨⟨⟨u, hu⟩, ⟨v, hv⟩, q, hq_support.2.1⟩, ?_, ?_, ?_, ?_⟩ <;> aesop

/-
The contracted vertex is in the lifted set of A if and only if x or y is in A.
-/
lemma SimpleGraph.mem_liftSet_contraction_vertex_iff (A : Set V) (x y : V) :
  SimpleGraph.contractEdge_vertex x y ∈ SimpleGraph.contractEdge_liftSet x y A ↔ x ∈ A ∨ y ∈ A := by
    unfold SimpleGraph.contractEdge_liftSet SimpleGraph.contractEdge_vertex
    constructor <;> intro h;
    · simp at h
      cases' h with z hz;
      simp [Quotient.eq, contractEdgeSetoid] at hz;
      aesop;
    · simp
      cases' h with hx hy;
      · exact ⟨ x, hx, rfl ⟩;
      · exact ⟨ y, hy, by simp [ Quotient.eq, SimpleGraph.contractEdgeSetoid ] ⟩

/-
If a path starts at one of the endpoints of the contracted edge, and the contracted vertex is in the lifted set of A, we can adjust the path to start in A.
-/
lemma SimpleGraph.adjust_path_start_to_A (G : SimpleGraph V) (A : Set V) (x y : V) (hxy : G.Adj x y)
  (u v : V) (p : G.Walk u v) (hp_path : p.IsPath)
  (hu : u = x ∨ u = y)
  (hp_support : p.support.toFinset ∩ {x, y} = {u})
  (h_liftA : SimpleGraph.contractEdge_vertex x y ∈ SimpleGraph.contractEdge_liftSet x y A) :
  ∃ (u' : V) (p' : G.Walk u' v),
    u' ∈ A ∧
    p'.IsPath ∧
    (p'.support.toFinset.image (⟦·⟧) : Finset (Quotient (contractEdgeSetoid x y)))
      ⊆ p.support.toFinset.image (⟦·⟧) := by
      by_cases hx : x ∈ A;
      · rcases hu with ( rfl | rfl );
        · exact ⟨ u, p, hx, hp_path, Finset.Subset.refl _ ⟩;
        · refine ⟨ x, SimpleGraph.Walk.cons hxy p, hx, ?_, ?_ ⟩ <;> simp_all [ SimpleGraph.Walk.cons_isPath_iff ];
          · rw [ Finset.ext_iff ] at hp_support ; specialize hp_support x ; aesop;
          · simp_all [ Finset.Subset.antisymm_iff, Finset.subset_iff ];
            use u;
            exact ⟨ p.start_mem_support, by exact Quotient.sound ( by tauto ) ⟩;
      · by_cases hy : y ∈ A;
        · cases hu <;> simp_all [ Finset.subset_iff ];
          · refine ⟨ y, hy, ?_, ?_, ?_ ⟩;
            exact SimpleGraph.Walk.cons hxy.symm ( p.copy ( by simp [ * ] ) rfl );
            · replace hp_support := Finset.ext_iff.mp hp_support y; aesop;
            · simp [ SimpleGraph.Walk.support_cons ];
              simp [ Finset.eq_singleton_iff_unique_mem] at hp_support ⊢;
              exact ⟨ ⟨ x, hp_support.1, by simp_all [Quotient.eq, SimpleGraph.contractEdgeSetoid ] ⟩,
              fun a ha => ⟨ a, ha, by tauto ⟩ ⟩;
          · grind;
        · simp_all [ contractEdge_liftSet ];
          obtain ⟨ u', hu', hu'' ⟩ := h_liftA;
          have := SimpleGraph.contractEdgeProj_eq_vertex_iff x y u';
            cases this.mp hu'' <;> simp_all [ Finset.ext_iff ]
lemma SimpleGraph.adjust_path_end_to_B (G : SimpleGraph V) (B : Set V) (x y : V) (hxy : G.Adj x y)
  (u v : V) (p : G.Walk u v) (hp_path : p.IsPath)
  (hv : v = x ∨ v = y)
  (hp_support : p.support.toFinset ∩ {x, y} = {v})
  (h_liftB : SimpleGraph.contractEdge_vertex x y ∈ SimpleGraph.contractEdge_liftSet x y B) :
  ∃ (v' : V) (p' : G.Walk u v'),
    v' ∈ B ∧
    p'.IsPath ∧
    (p'.support.toFinset.image (⟦·⟧) : Finset (Quotient (contractEdgeSetoid x y)))
      ⊆ p.support.toFinset.image (⟦·⟧) := by
      rcases hv with ( rfl | rfl );
      · by_cases hy : y ∈ B;
        · refine ⟨ y, ?_, hy, ?_, ?_ ⟩;
          exact p.append ( SimpleGraph.Walk.cons hxy SimpleGraph.Walk.nil );
          · simp_all [ Finset.ext_iff, SimpleGraph.Walk.isPath_def ];
            rw [ SimpleGraph.Walk.support_append ];
            simp_all [ List.nodup_append ];
            intro a ha ha'; specialize hp_support a ha ha'; aesop;
          · simp [ Finset.subset_iff, SimpleGraph.Walk.support_append ];
            use v;
            simp_all [ Finset.eq_singleton_iff_unique_mem ];
            exact Quotient.sound ( by tauto );
        · have hvB : v ∈ B := by
            exact Or.resolve_right ( SimpleGraph.mem_liftSet_contraction_vertex_iff B v y |>.1 h_liftB ) hy;
          exact ⟨ v, p, hvB, hp_path, Finset.Subset.refl _ ⟩;
      · by_cases hv : v ∈ B;
        · exact ⟨ v, p, hv, hp_path, Finset.Subset.refl _ ⟩;
        · have hx : x ∈ B := by
            contrapose! h_liftB; simp_all [ contractEdge_liftSet ] ;
            intro w hw; rw [SimpleGraph.contractEdge_vertex ] ; simp_all [ Quotient.eq, SimpleGraph.contractEdgeSetoid ] ;
            grind;
          refine ⟨ x, p.append ( SimpleGraph.Walk.cons hxy.symm SimpleGraph.Walk.nil ), hx, ?_, ?_ ⟩;
          · refine SimpleGraph.Walk.IsPath_append_of_support_inter_subset_one _ _ hp_path ?_ ?_;
            · aesop;
            · rw [ Finset.eq_singleton_iff_unique_mem ] at hp_support ; aesop;
          · simp_all [ Finset.subset_iff ];
            rintro a ( ha | rfl | rfl )
            · exact ⟨ a, ha, by rfl ⟩;
            · exact ⟨ a, by cases p <;> aesop ⟩;
            · exact ⟨ v, by simp, by simp [Quotient.eq, SimpleGraph.contractEdgeSetoid]⟩

/-
Helper lemma: A path starting at the contracted vertex can be lifted to an A-B path if the contracted vertex is in the lifted set of A.
-/
lemma SimpleGraph.lift_path_start_eq_vertex (G : SimpleGraph V) (A B : Set V) (x y : V) (hxy : G.Adj x y)
  (v' : Quotient (SimpleGraph.contractEdgeSetoid x y))
  (p' : (G.contractEdge x y).Walk (SimpleGraph.contractEdge_vertex x y) v')
  (hp'_path : p'.IsPath)
  (hv' : v' ∈ SimpleGraph.contractEdge_liftSet x y B)
  (h_end_ne : v' ≠ SimpleGraph.contractEdge_vertex x y)
  (h_liftA : SimpleGraph.contractEdge_vertex x y ∈ SimpleGraph.contractEdge_liftSet x y A) :
  ∃ p : G.ABPath A B,
    p.p.1.support.toFinset.image (⟦·⟧) ⊆ p'.support.toFinset := by
      obtain ⟨u, v, q, hu_xy, hvB, hq_path, hq_pre, hq_xy⟩ :=
        SimpleGraph.lift_path_from_contraction_start G B x y v' p' hp'_path hv' h_end_ne
      obtain ⟨u', q', hu'A, hq'_path, hq'_support⟩ :=
        SimpleGraph.adjust_path_start_to_A G A x y hxy u v q hq_path hu_xy hq_xy h_liftA
      refine ⟨⟨⟨u', hu'A⟩, ⟨v, hvB⟩, q', hq'_path⟩, ?_⟩
      refine hq'_support.trans ?_
      intro a ha
      rcases Finset.mem_image.mp ha with ⟨w, hw, rfl⟩
      have hw' : w ∈ SimpleGraph.contractEdge_preimage x y (↑p'.support.toFinset) := hq_pre (Finset.mem_coe.mpr hw)
      exact (SimpleGraph.mem_contractEdge_preimage (x := x) (y := y) (Y := ↑p'.support.toFinset) (v := w)).1 hw'
lemma SimpleGraph.lift_path_end_eq_vertex (G : SimpleGraph V) (A B : Set V) (x y : V) (hxy : G.Adj x y)
  (u' : Quotient (SimpleGraph.contractEdgeSetoid x y))
  (p' : (G.contractEdge x y).Walk u' (SimpleGraph.contractEdge_vertex x y))
  (hp'_path : p'.IsPath)
  (hu' : u' ∈ SimpleGraph.contractEdge_liftSet x y A)
  (h_start_ne : u' ≠ SimpleGraph.contractEdge_vertex x y)
  (h_liftB : SimpleGraph.contractEdge_vertex x y ∈ SimpleGraph.contractEdge_liftSet x y B) :
  ∃ p : G.ABPath A B,
    p.p.1.support.toFinset.image (⟦·⟧) ⊆ p'.support.toFinset := by
      obtain ⟨ u, v, p, hu, hv, hp, hp', hp'' ⟩ :=
        SimpleGraph.lift_path_to_contraction_end G A x y u' p' hp'_path hu' h_start_ne
      obtain ⟨ v', q, hv', hq, hq' ⟩ :=
        SimpleGraph.adjust_path_end_to_B G B x y hxy u v p hp hv hp'' h_liftB
      have h_final : Finset.image (⟦·⟧) q.support.toFinset ⊆ p'.support.toFinset := by
        refine hq'.trans ?_
        rw [ Finset.image_subset_iff ]
        intro z hz
        have hz' : z ∈ SimpleGraph.contractEdge_preimage x y (↑p'.support.toFinset) := hp' (Finset.mem_coe.mpr hz)
        exact (mem_contractEdge_preimage (x := x) (y := y) (Y := ↑p'.support.toFinset) (v := z)).1 hz'
      exact ⟨ ⟨ ⟨ u, hu ⟩, ⟨ v', hv' ⟩, q, hq ⟩, h_final ⟩

/-
Helper lemma: A nil path at the contracted vertex can be lifted to an A-B path if the contracted vertex is in the lifted sets of A and B.
-/
lemma SimpleGraph.lift_path_nil_eq_vertex (G : SimpleGraph V) (A B : Set V) (x y : V) (hxy : G.Adj x y)
  (p' : (G.contractEdge x y).Walk (SimpleGraph.contractEdge_vertex x y) (SimpleGraph.contractEdge_vertex x y))
  (hp'_path : p'.IsPath)
  (h_liftA : SimpleGraph.contractEdge_vertex x y ∈ SimpleGraph.contractEdge_liftSet x y A)
  (h_liftB : SimpleGraph.contractEdge_vertex x y ∈ SimpleGraph.contractEdge_liftSet x y B) :
  ∃ p : G.ABPath A B,
    p.p.1.support.toFinset.image (⟦·⟧) ⊆ p'.support.toFinset := by
      simp [contractEdge_liftSet] at h_liftA h_liftB
      obtain ⟨x_1, hx_1_A, hx_1⟩ := h_liftA
      obtain ⟨x_2, hx_2_B, hx_2⟩ := h_liftB
      have hx_1_eq : x_1 = x ∨ x_1 = y := by
        contrapose! hx_1; simp_all [ Quotient.eq, SimpleGraph.contractEdge_vertex] ;
        unfold contractEdgeSetoid; aesop;
      have hx_2_eq : x_2 = x ∨ x_2 = y := by
        rw [ SimpleGraph.contractEdge_vertex ] at hx_2;
        rw [ Quotient.eq ] at hx_2;
        cases hx_2 <;> aesop;
      cases hx_1_eq <;> cases hx_2_eq <;> simp_all [ contractEdge_vertex ];
      · refine ⟨ ?_, ?_ ⟩;
        constructor;
        rotate_left;
        exact ⟨ x, hx_1_A ⟩;
        exact ⟨ x, hx_2_B ⟩;
        simp [Finset.image]
        swap
        exact SimpleGraph.Path.nil;
        all_goals simp [*];
      · refine ⟨⟨⟨x, hx_1_A⟩, ⟨y, hx_2_B⟩, SimpleGraph.Walk.cons hxy SimpleGraph.Walk.nil,
            by simp [SimpleGraph.Walk.cons_isPath_iff, hxy.ne]⟩, ?_⟩;
        simp;
        aesop;
      · refine ⟨ ?_, ?_ ⟩;
        constructor;
        rotate_left;
        exact ⟨ y, hx_1_A ⟩;
        exact ⟨ x, hx_2_B ⟩;
        swap
        constructor
        swap
        exact SimpleGraph.Walk.cons hxy.symm SimpleGraph.Walk.nil;
        simp
        exact hxy.ne.symm
        simp [Finset.image];
        by_cases h : y = x <;> simp_all
      · refine ⟨ ?_, ?_ ⟩;
        constructor;
        rotate_left;
        exact ⟨ y, hx_1_A ⟩;
        exact ⟨ y, hx_2_B ⟩;
        swap
        exact SimpleGraph.Path.nil;
        all_goals simp_all
lemma SimpleGraph.exists_lifted_ABPath_through (G : SimpleGraph V) (A B : Set V) (x y : V) (hxy : G.Adj x y)
  (p' : (G.contractEdge x y).ABPath (SimpleGraph.contractEdge_liftSet x y A) (SimpleGraph.contractEdge_liftSet x y B))
  (hp'_mem : SimpleGraph.contractEdge_vertex x y ∈ p'.p.1.support) :
  ∃ p : G.ABPath A B,
    p.p.1.support.toFinset.image (⟦·⟧) ⊆ p'.p.1.support.toFinset := by
      by_cases hu' : p'.u = SimpleGraph.contractEdge_vertex x y;
      · by_cases hv' : p'.v = SimpleGraph.contractEdge_vertex x y;
        · have h_lift_nil : SimpleGraph.contractEdge_vertex x y ∈ SimpleGraph.contractEdge_liftSet x y A ∧ SimpleGraph.contractEdge_vertex x y ∈ SimpleGraph.contractEdge_liftSet x y B := by
            grind;
          obtain ⟨ p, hp ⟩ := SimpleGraph.lift_path_nil_eq_vertex G A B x y hxy ( SimpleGraph.Walk.nil ) ( by simp ) h_lift_nil.1 h_lift_nil.2;
          exact ⟨ p, hp.trans ( by simp [ hp'_mem ] ) ⟩;
        · cases p';
          have := SimpleGraph.lift_path_start_eq_vertex G A B x y hxy;
          grind;
      · cases' p' with u' hv' p;
        rcases hv' with ⟨ v', hv' ⟩;
        by_cases hv' : v' = SimpleGraph.contractEdge_vertex x y;
        · convert SimpleGraph.lift_path_end_eq_vertex G A B x y hxy _ _ _ _ _ _;
          rotate_left;
          any_goals tauto;
          convert p.1
          all_goals norm_num [ hv' ];
          · grind;
          · grind;
        · rename_i hp;
          obtain ⟨ u, v, lifted_p, hp₁, hp₂, hp₃, hp₄ ⟩ := SimpleGraph.lift_path_through_contraction_internal G A B x y hxy u' v' p p.2 hp'_mem hu' hv' u'.2 ‹_›;
          refine ⟨ ⟨ ⟨u, hp₁⟩, ⟨v, hp₂⟩, lifted_p, hp₃ ⟩, ?_ ⟩;
          intro a ha; rcases Finset.mem_image.mp ha with ⟨w, hw, rfl⟩
          have := hp₄ (Finset.mem_coe.mpr hw)
          exact (mem_contractEdge_preimage (x := x) (y := y) (Y := ↑p.1.support.toFinset) (v := w)).1 this
lemma SimpleGraph.exists_disjoint_paths_lift (G : SimpleGraph V) (A B : Set V) (x y : V)
    (hxy : G.Adj x y)
    (P' : ((G.contractEdge x y).Joiner (contractEdge_liftSet x y A) (contractEdge_liftSet x y B))) :
  ∃ P : G.Joiner A B, P.1.encard = P'.1.encard := by
    have h_lift : ∀ (p' : (G.contractEdge x y).ABPath (SimpleGraph.contractEdge_liftSet x y A) (SimpleGraph.contractEdge_liftSet x y B)), ∃ p : G.ABPath A B, p.p.1.support.toFinset.image (⟦·⟧) ⊆ p'.p.1.support.toFinset := by
      intro p'
      by_cases hp'_avoid : SimpleGraph.contractEdge_vertex x y ∉ p'.p.1.support;
      · rcases SimpleGraph.exists_lifted_ABPath_avoiding G A B x y p' hp'_avoid with ⟨p, hp⟩
        exact ⟨p, hp.2.2.1⟩
      · rcases SimpleGraph.exists_lifted_ABPath_through G A B x y hxy p' (by aesop) with ⟨p, hp⟩
        exact ⟨p, hp⟩
    choose f hf using h_lift
    refine ⟨⟨f '' P'.1, ?_⟩, ?_⟩
    · intro p hp q hq hpq
      rcases (Set.mem_image f P'.1 p).mp hp with ⟨p', hp', rfl⟩
      rcases (Set.mem_image f P'.1 q).mp hq with ⟨q', hq', rfl⟩
      have hpq' : p' ≠ q' := fun h' => hpq (by simp [h'])
      have h_disj := P'.2 hp' hq' hpq'
      show Disjoint (f p').support (f q').support
      rw [Set.disjoint_left]
      intro v hv hv'
      -- v is in both (f p').support and (f q').support, so ⟦v⟧ is in both p' and q' supports
      have hfp := hf p' (Finset.mem_image.mpr ⟨v, List.mem_toFinset.mpr hv, rfl⟩)
      have hfq := hf q' (Finset.mem_image.mpr ⟨v, List.mem_toFinset.mpr hv', rfl⟩)
      exact Set.disjoint_left.mp h_disj (List.mem_toFinset.mp hfp) (List.mem_toFinset.mp hfq)
    · exact (Set.InjOn.encard_image (fun p' hp' q' hq' h_eq => by
        by_contra hneq
        have h_disj := P'.2 hp' hq' hneq
        have hfp_start := hf p' (Finset.mem_image.mpr ⟨(f p').u.1, List.mem_toFinset.mpr (f p').p.1.start_mem_support, rfl⟩)
        have hfq_start : ⟦(f p').u.1⟧ ∈ q'.p.1.support.toFinset := by
          have h_support_eq : (f p').p.1.support = (f q').p.1.support := by
            simpa using congrArg (fun r => r.p.1.support) h_eq
          have : (f p').u.1 ∈ (f q').p.1.support := h_support_eq ▸ (f p').p.1.start_mem_support
          exact hf q' (Finset.mem_image.mpr ⟨(f p').u.1, List.mem_toFinset.mpr this, rfl⟩)
        exact Set.disjoint_left.mp h_disj (List.mem_toFinset.mp hfp_start) (List.mem_toFinset.mp hfq_start)))

/-
If min_sep(G/e) < k, then there exists a separator X in G such that |X|=k, x in X, and y in X.
-/
lemma SimpleGraph.Menger_case2_exists_X (G : SimpleGraph V) (A B : Set V) (x y : V) (hxy : x ≠ y)
  (k : ℕ∞)
  (h_min : G.mincut A B = k)
  (h_contract_min : (G.contractEdge x y).mincut (SimpleGraph.contractEdge_liftSet x y A) (SimpleGraph.contractEdge_liftSet x y B) < k) :
  ∃ X : G.Separator A B, X.1.encard = k ∧ x ∈ X.1 ∧ y ∈ X.1 := by
  -- Extract a separator Y in G/e with |Y| < k
  obtain ⟨⟨Y, hY_sep⟩, hY_card⟩ : ∃ Y : (G.contractEdge x y).Separator
      (contractEdge_liftSet x y A) (contractEdge_liftSet x y B), Y.1.encard < k := by
    by_contra h_all; push_neg at h_all
    exact absurd (le_iInf h_all) (not_le.mpr h_contract_min)
  -- The contracted vertex must be in Y
  have h_ve : contractEdge_vertex x y ∈ Y :=
    contractEdge_separator_contains_vertex G A B x y k h_min ⟨Y, hY_sep⟩ hY_card hxy
  -- Lift Y to a separator X in G
  have h_sep : G.Separates A B (contractEdge_preimage x y Y) :=
    contractEdge_preimage_separates ⟨Y, hY_sep⟩
  have h_lift_card : (contractEdge_preimage x y Y).encard = Y.encard + 1 :=
    contractEdge_separator_lift_card x y hxy Y h_ve
  -- X has encard ≥ k (since it's a separator of G)
  have h_ge_k : (contractEdge_preimage x y Y).encard ≥ k := by
    calc k = G.mincut A B := h_min.symm
      _ ≤ (contractEdge_preimage x y Y).encard := iInf_le_of_le ⟨_, h_sep⟩ le_rfl
  -- X has encard ≤ k (since |Y| < k, so |Y| + 1 ≤ k)
  have h_le_k : (contractEdge_preimage x y Y).encard ≤ k := by
    rw [h_lift_card]
    have : Y.encard ≠ ⊤ := ne_top_of_lt (lt_of_lt_of_le hY_card le_top)
    exact (ENat.add_one_le_iff this).mpr hY_card
  refine ⟨⟨_, h_sep⟩, le_antisymm h_le_k h_ge_k, ?_, ?_⟩
  · exact mem_contractEdge_preimage.mpr h_ve
  · exact mem_contractEdge_preimage.mpr (contractEdge_vertex_eq x y ▸ h_ve)

/-
If a path intersects X, there is a suffix starting in X that avoids X internally.
-/
lemma SimpleGraph.Walk.exists_suffix_path_avoiding_set {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
    (X : Set V) (h : ∃ w ∈ p.support, w ∈ X) :
    ∃ (w : V) (q : G.Walk w v), w ∈ X ∧ q.IsPath ∧ q.support.toFinset ⊆ p.support.toFinset ∧ (∀ z ∈ q.support, z ∈ X → z = w) := by
    obtain ⟨w, q, hwX, hq_path, hq_support, hq_unique⟩ :=
      SimpleGraph.Walk.exists_path_prefix_avoiding_set (p := p.reverse) X
        (by simpa [SimpleGraph.Walk.support_reverse] using h)
    refine ⟨w, q.reverse, hwX, ?_, ?_, ?_⟩
    · exact (Walk.isPath_reverse_iff q).mpr hq_path
    · simpa [SimpleGraph.Walk.support_reverse] using hq_support
    · simpa [SimpleGraph.Walk.support_reverse] using hq_unique

/-
If X separates A and B in G and contains x and y, then any separator of X and B in G-xy is also a separator of A and B in G.
-/
lemma SimpleGraph.separator_in_G_of_separator_in_G_delete_edge_right (G : SimpleGraph V) (A B : Set V)
    (x y : V) (X : G.Separator A B) (hx : x ∈ X.1) (hy : y ∈ X.1) (hxy : x ≠ y)
    (S : (G.deleteEdge x y).Separator X.1 B) : G.Separates A B S.1 := by
    let X_rev : G.Separator B A := ⟨X.1, fun u hu v hv p => by
      obtain ⟨w, hw, hwX⟩ := X.2 v hv u hu p.reverse
      exact ⟨w, by simpa using hw, hwX⟩⟩
    let S_rev : (G.deleteEdge x y).Separator B X_rev.1 := ⟨S.1, fun u hu v hv p => by
      obtain ⟨w, hw, hwS⟩ := S.2 v hv u hu p.reverse
      exact ⟨w, by simpa using hw, hwS⟩⟩
    have := SimpleGraph.separator_in_G_of_separator_in_G_delete_edge G B A x y X_rev S_rev hx hy hxy
    intro u hu v hv p
    obtain ⟨w, hw, hwS⟩ := this v hv u hu p.reverse
    exact ⟨w, by simpa using hw, hwS⟩

/-
If X separates A and B in G and contains x and y, then the minimum separator size of A and X in G-xy is at least k.
-/
lemma SimpleGraph.min_sep_delete_ge_k_left (G : SimpleGraph V) (A B : Set V) (x y : V)
  (k : ℕ∞) (h_min : G.mincut A B = k) (X : G.Separator A B) (hx : x ∈ X.1) (hy : y ∈ X.1) (hxy : x ≠ y) :
  (G.deleteEdge x y).mincut A X.1 ≥ k := by
    rw [← h_min, ge_iff_le, mincut]
    apply le_iInf
    intro S
    exact iInf_le_of_le ⟨S.1, separator_in_G_of_separator_in_G_delete_edge G A B x y X S hx hy hxy⟩ le_rfl

/-
If X separates A and B in G and contains x and y, then the minimum separator size of X and B in G-xy is at least k.
-/
lemma SimpleGraph.min_sep_delete_ge_k_right (G : SimpleGraph V) (A B : Set V) (x y : V)
  (k : ℕ∞) (h_min : G.mincut A B = k) (X : G.Separator A B) (hx : x ∈ X.1) (hy : y ∈ X.1) (hxy : x ≠ y) :
  (G.deleteEdge x y).mincut X.1 B ≥ k := by
    rw [← h_min, ge_iff_le, mincut]
    apply le_iInf
    intro S
    exact iInf_le_of_le ⟨S.1, separator_in_G_of_separator_in_G_delete_edge_right G A B x y X hx hy hxy S⟩ le_rfl

/-
If G' is a subgraph of G, then any set of disjoint paths in G' can be lifted to a set of disjoint paths in G with the same size.
-/
lemma SimpleGraph.lift_disjoint_paths_le (G G' : SimpleGraph V) (h : G' ≤ G) (A B : Set V)
    (P : G'.Joiner A B) : ∃ Q : G.Joiner A B, Q.1.encard = P.1.encard := by
  obtain ⟨P, hP⟩ := P
  let f : G'.ABPath A B → G.ABPath A B := fun p =>
    ⟨p.u, p.v, p.p.1.mapLe h, p.p.2.mapLe h⟩
  have hf_inj : Set.InjOn f P := by
    intro p hp q hq hpq
    by_contra hneq
    have hdisj : Disjoint p.support q.support := hP hp hq hneq
    have h_support_eq : p.p.1.support = q.p.1.support := by
      have h_support_eq_map : (p.p.1.mapLe h).support = (q.p.1.mapLe h).support := by
        simpa [f] using congrArg (fun r => r.p.1.support) hpq
      simpa [SimpleGraph.Walk.support_mapLe_eq_support] using h_support_eq_map
    have hp_mem : (p.u : V) ∈ p.p.1.support := p.p.1.start_mem_support
    have hq_mem : (p.u : V) ∈ q.p.1.support := by simpa [h_support_eq] using hp_mem
    exact (Set.disjoint_left.mp hdisj (show (p.u : V) ∈ p.support from hp_mem)) hq_mem
  refine ⟨⟨f '' P, ?_⟩, ?_⟩
  · intro p hp q hq hpq
    rcases (Set.mem_image f P p).mp hp with ⟨p', hp', rfl⟩
    rcases (Set.mem_image f P q).mp hq with ⟨q', hq', rfl⟩
    have hpq' : p' ≠ q' := fun h' => hpq (by simp [f, h'])
    have hdisj0 : Disjoint p'.support q'.support := hP hp' hq' hpq'
    show Disjoint (f p').support (f q').support
    simp only [ABPath.support, f, SimpleGraph.Walk.support_mapLe_eq_support]
    exact hdisj0
  · show (f '' P).encard = P.encard
    exact hf_inj.encard_image

/-
Helper: if k ≤ ⨆ f and k ≠ ⊤, there exists i with k ≤ f i.
-/
private lemma exists_le_of_le_iSup {ι : Type*} [Nonempty ι] (f : ι → ℕ∞) {k : ℕ∞} (hk : k ≠ ⊤)
    (h : k ≤ ⨆ i, f i) : ∃ i, k ≤ f i := by
  by_contra h_all; push_neg at h_all
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, ↑n = k := WithTop.ne_top_iff_exists.mp hk
  cases n with
  | zero => exact absurd (h_all (Classical.arbitrary ι)) (not_lt.mpr (zero_le _))
  | succ m =>
    have hle : ∀ i, f i ≤ ↑m := fun i =>
      (ENat.lt_add_one_iff (by exact WithTop.coe_ne_top)).mp (by exact_mod_cast h_all i)
    exact absurd h (not_le.mpr (lt_of_le_of_lt (iSup_le hle)
      (ENat.coe_lt_coe.mpr (Nat.lt_succ_of_le le_rfl))))

/-
If there exists a separator X of size k containing x and y, then G has k disjoint A-B paths.
-/
lemma SimpleGraph.Menger_case2_imp_paths (G : SimpleGraph V) (A B : Set V) (x y : V)
    (hxy : G.Adj x y)
    (k : ℕ∞) (hk : k ≠ ⊤) (h_min : G.mincut A B = k) (X : G.Separator A B) (hX_card : X.1.encard = k) (hx : x ∈ X.1)
    (hy : y ∈ X.1) (IH_delete : ∀ A' B', (G.deleteEdge x y).mincut A' B' ≤ (G.deleteEdge x y).maxflow A' B') :
    k ≤ G.maxflow A B := by
  have hX_fin : X.1.Finite := Set.encard_ne_top_iff.mp (hX_card ▸ hk)
  have h_del_A : k ≤ (G.deleteEdge x y).maxflow A X.1 :=
    le_trans (min_sep_delete_ge_k_left G A B x y k h_min X hx hy hxy.ne) (IH_delete A X.1)
  have h_del_B : k ≤ (G.deleteEdge x y).maxflow X.1 B :=
    le_trans (min_sep_delete_ge_k_right G A B x y k h_min X hx hy hxy.ne) (IH_delete X.1 B)
  have h_subgraph : G.deleteEdge x y ≤ G := fun _ _ huv => huv.1
  -- Extract joiner witness from ⨆ using helper
  suffices h : ∃ P : G.Joiner A B, P.1.encard = k by
    obtain ⟨P, hP⟩ := h
    exact hP ▸ le_iSup_of_le P le_rfl
  -- Get A→X joiner of size k in G
  have h_exists_PA : ∃ P_A : G.Joiner A X.1, P_A.1.encard = k := by
    obtain ⟨P_A', hP_A'⟩ := exists_le_of_le_iSup _ hk h_del_A
    obtain ⟨t, ht_sub, ht_card⟩ := Set.exists_subset_encard_eq hP_A'
    have ht_disj : disjointPaths t := fun p hp q hq hpq => P_A'.2 (ht_sub hp) (ht_sub hq) hpq
    obtain ⟨Q, hQ⟩ := lift_disjoint_paths_le G _ h_subgraph A X.1 ⟨t, ht_disj⟩
    exact ⟨Q, hQ.trans ht_card⟩
  -- Get X→B joiner of size k in G
  have h_exists_PB : ∃ P_B : G.Joiner X.1 B, P_B.1.encard = k := by
    obtain ⟨P_B', hP_B'⟩ := exists_le_of_le_iSup _ hk h_del_B
    obtain ⟨t, ht_sub, ht_card⟩ := Set.exists_subset_encard_eq hP_B'
    have ht_disj : disjointPaths t := fun p hp q hq hpq => P_B'.2 (ht_sub hp) (ht_sub hq) hpq
    obtain ⟨Q, hQ⟩ := lift_disjoint_paths_le G _ h_subgraph X.1 B ⟨t, ht_disj⟩
    exact ⟨Q, hQ.trans ht_card⟩
  obtain ⟨P_A, hP_A_card⟩ := h_exists_PA
  obtain ⟨P_B, hP_B_card⟩ := h_exists_PB
  exact disjoint_paths_join G A B X k hX_fin hX_card P_A hP_A_card P_B hP_B_card

/-
Inductive step for Menger's theorem.
-/
lemma SimpleGraph.Menger_inductive_step (G : SimpleGraph V) (A B : Set V) (x y : V)
    (hxy : G.Adj x y) (hk : G.mincut A B ≠ ⊤)
    (IH_contract : (G.contractEdge x y).mincut (SimpleGraph.contractEdge_liftSet x y A)
      (SimpleGraph.contractEdge_liftSet x y B) ≤
      (G.contractEdge x y).maxflow (SimpleGraph.contractEdge_liftSet x y A) (SimpleGraph.contractEdge_liftSet x y B))
    (IH_delete : ∀ A' B', (G.deleteEdge x y).mincut A' B' ≤ (G.deleteEdge x y).maxflow A' B') :
    G.mincut A B ≤ G.maxflow A B := by
  by_cases h : (G.contractEdge x y).mincut (contractEdge_liftSet x y A) (contractEdge_liftSet x y B) < G.mincut A B
  · -- Case 1: contraction has smaller mincut → separator containing both x and y
    obtain ⟨⟨X, hX_sep⟩, hX_card, hx_mem, hy_mem⟩ :=
      Menger_case2_exists_X G A B x y hxy.ne (G.mincut A B) rfl h
    exact Menger_case2_imp_paths G A B x y hxy (G.mincut A B) hk rfl ⟨X, hX_sep⟩ hX_card hx_mem hy_mem IH_delete
  · -- Case 2: contraction mincut ≥ G.mincut → lift paths from contracted graph
    push_neg at h
    obtain ⟨P', hP'⟩ := exists_le_of_le_iSup _ hk (le_trans h IH_contract)
    obtain ⟨P, hP⟩ := exists_disjoint_paths_lift G A B x y hxy P'
    calc G.mincut A B ≤ P'.1.encard := hP'
      _ = P.1.encard := hP.symm
      _ ≤ G.maxflow A B := le_iSup_of_le P le_rfl

/-
Auxiliary lemma for Menger's theorem: The theorem holds for any graph with n edges, proved by strong induction on n.
-/
theorem SimpleGraph.Menger_strong_aux [Fintype V] (n : ℕ) :
  G.edgeFinset.card = n → G.mincut A B ≤ G.maxflow A B := by
  induction n using Nat.strongRecOn generalizing V with
  | _ n ih =>
  intro h_card
  by_cases h_empty : G.edgeFinset = ∅
  · exact Menger_strong_base G A B (by simpa [edgeSet_eq_empty] using h_empty)
  · obtain ⟨x, y, hxy⟩ : ∃ x y : V, G.Adj x y := by
      simp +zetaDelta at *
      contrapose! h_empty
      ext x y; simp [h_empty]
    have h_contract : (G.contractEdge x y).edgeFinset.card < n :=
      h_card ▸ contractEdge_edge_card_lt G x y hxy
    have h_delete : (G.deleteEdge x y).edgeFinset.card < n := by
      apply lt_of_lt_of_le (deleteEdge_card_edges_lt G x y hxy)
      omega
    have hk : G.mincut A B ≠ ⊤ := by
      have := iInf_le (fun S : G.Separator A B => S.1.encard) ⟨A, fun u hu _ _ p => ⟨u, p.start_mem_support, hu⟩⟩
      exact ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr (Set.toFinite A)) this
    exact Menger_inductive_step G A B x y hxy hk
      (ih _ h_contract rfl) (fun A' B' => ih _ h_delete rfl)

/-
Menger's theorem: The minimum number of vertices separating A from B in G is equal to the maximum number of disjoint A--B paths in G. (This is the strong direction: min separator <= max paths)
-/
theorem SimpleGraph.Menger_strong [Fintype V] : G.mincut A B ≤ G.maxflow A B :=
  Menger_strong_aux _ rfl

/-
Menger's theorem: The minimum number of vertices separating A from B in G is equal to the maximum number of disjoint A--B paths in G.
-/
theorem SimpleGraph.Menger [Fintype V] : G.mincut A B = G.maxflow A B :=
  le_antisymm SimpleGraph.Menger_strong SimpleGraph.Menger_weak

/-
Menger's theorem: there exist a separator set `S` between `A` and `B` and a set
`P`of disjoint A-B paths such that `S` is formed of exactly one vertez vrom each
path in `P`.

This version would actually be true without the `[Fintype S]` assumption.
-/
theorem SimpleGraph.Menger' [Fintype V] : ∃ P : G.Joiner A B, ∃ S : G.Separator A B, ∃ φ : P.1 ≃ S.1,
    ∀ p : P.1, (φ p).1 ∈ p.1.p.1.support := by
  have h_maxflow_lt : G.maxflow A B < ⊤ :=
    lt_of_le_of_lt (iSup_le (fun P => Joiner.encard_le P)) (Set.toFinite A).encard_lt_top
  obtain ⟨P, hP⟩ := ENat.exists_eq_iSup_of_lt_top h_maxflow_lt
  use P
  obtain ⟨S, hS⟩ := ENat.exists_eq_iInf (fun S : G.Separator A B => S.1.encard)
  use S
  have key (p : P.1) : ∃ x : S.1, x.1 ∈ p.1.p.1.support := by
    obtain ⟨x, h1, h2⟩ := S.2 p.1.u p.1.u.2 p.1.v p.1.v.2 p.1.p.1
    exact ⟨⟨x, h2⟩, h1⟩
  choose f hf using key
  have hf_inj : f.Injective := by
    intro p q hpq
    by_contra h
    have h1 := P.2 p.2 q.2 (fun heq => h (Subtype.ext heq))
    exact Set.disjoint_left.mp h1 (hf p) (hpq ▸ hf q)
  have hP_fin : P.1.Finite :=
    Set.encard_ne_top_iff.mp (ne_top_of_le_ne_top
      (Set.encard_ne_top_iff.mpr (Set.toFinite A)) (Joiner.encard_le P))
  haveI : Fintype P.1 := hP_fin.fintype
  haveI : Fintype S.1 := (Set.toFinite S.1).fintype
  have h_card_eq : Fintype.card P.1 = Fintype.card S.1 := by
    have h_eq : P.1.encard = S.1.encard := by
      calc P.1.encard = G.maxflow A B := hP
        _ = G.mincut A B := Menger.symm
        _ = S.1.encard := hS.symm
    rw [Set.encard_eq_coe_toFinset_card, Set.toFinset_card] at h_eq
    rw [Set.encard_eq_coe_toFinset_card, Set.toFinset_card] at h_eq
    exact WithTop.coe_injective h_eq
  exact ⟨.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf_inj, h_card_eq⟩), hf⟩

#print axioms SimpleGraph.Menger
-- #lint
