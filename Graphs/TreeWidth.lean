import Graphs.Basic
import Graphs.Minor
import Graphs.TreeDecomposition
import Mathlib.Combinatorics.SimpleGraph.Walks.Traversal
import Mathlib.Combinatorics.SimpleGraph.Paths

open Classical Set SimpleGraph

universe u

variable {α β : Type u} {G : SimpleGraph α} {H : SimpleGraph β} {n : ℕ}

private lemma encard_three_ne {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Set α).encard = 3 := by
  rw [encard_insert_of_notMem (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]; exact ⟨hab, hac⟩),
    encard_insert_of_notMem (by simp only [Set.mem_singleton_iff]; exact hbc), encard_singleton]
  rfl

private lemma exists_transition {ι : Type*} {T : SimpleGraph ι} (htree : T.IsTree)
    {P : ι → Prop} {u w : ι}
    (p : T.Walk u w) (hp : p.IsPath) (hPu : P u) (hPw : ¬P w) :
    ∃ t₁ t₂ : ι, T.Adj t₁ t₂ ∧ P t₁ ∧ ¬P t₂ ∧ htree.ordered t₁ t₂ w ∧ htree.ordered u t₁ w := by
  induction p with
  | nil => exact absurd hPu hPw
  | @cons u' v' w' h' rest ih =>
    by_cases hPv : P v'
    · obtain ⟨t₁, t₂, hadj, hPt₁, hPt₂, hord12w, hordv't₁w⟩ := ih hp.of_cons hPv hPw
      refine ⟨t₁, t₂, hadj, hPt₁, hPt₂, hord12w, ?_⟩
      simp only [IsTree.ordered, htree.path_spec' ⟨Walk.cons h' rest, hp⟩, Walk.support_cons,
        List.mem_cons]
      right; rwa [IsTree.ordered, htree.path_spec' ⟨rest, hp.of_cons⟩] at hordv't₁w
    · exact ⟨u', v', h', hPu, hPv,
        by simp [IsTree.ordered, htree.path_spec' ⟨Walk.cons h' rest, hp⟩],
        by simp [IsTree.ordered, htree.path_spec' ⟨Walk.cons h' rest, hp⟩]⟩

noncomputable def treeWidth (G : SimpleGraph α) : ℕ∞ :=
  sInf {w | ∃ D : TreeDecomposition G, D.width = w}

theorem treeWidth_ge_one (h : G ≠ ⊥) : 1 ≤ treeWidth G := by
  refine le_csInf ⟨_, .trivial, rfl⟩ ?_
  rintro w ⟨D, rfl⟩
  obtain ⟨u, v, huv⟩ : ∃ u v : α, G.Adj u v := by contrapose! h; aesop
  obtain ⟨t, ht⟩ := D.edge_mem_bag huv
  refine' le_trans _ ( le_iSup _ t )
  have h1 : {u, v} ⊆ D.V t := by grind
  have h2 := encard_mono h1
  have h3 : ({u, v} : Set _).encard = 2 := by
    rw [encard_insert_of_notMem]
    · simp +decide
    · simpa using huv.ne
  convert tsub_le_tsub_right h2 1
  simp +decide [h3]

theorem bot_treeWidth : treeWidth (⊥ : SimpleGraph α) = 0 := by
  refine le_antisymm ?_ bot_le
  suffices : ∃ D : TreeDecomposition (⊥ : SimpleGraph α), D.width = 0
  · obtain ⟨D, hD⟩ := this ; exact sInf_le ⟨D, hD⟩
  by_cases hne : Nonempty α
  · obtain ⟨a⟩ := hne ; use .botAt a
    simp [TreeDecomposition.botAt, TreeDecomposition.width]
  · letI : IsEmpty α := not_nonempty_iff.mp hne ; use .trivial
    have := ENat.card_eq_zero_iff_empty α |>.2 this
    simp [TreeDecomposition.width, TreeDecomposition.trivial, this]

theorem treeWidth_tree_le_one (hG : G.IsTree) : treeWidth G ≤ 1 := by
  by_cases hG' : G = ⊥
  · simp [hG', bot_treeWidth]
  · obtain ⟨r, -⟩ : ∃ x : α, True := by contrapose! hG' ; aesop
    exact csInf_le_of_le (OrderBot.bddBelow _) (by simp) (treeDecompositionOfTree_width hG r)

theorem tree_treeWidth (hG : G.IsTree) (hG' : G ≠ ⊥) : treeWidth G = 1 :=
  le_antisymm (treeWidth_tree_le_one hG) (treeWidth_ge_one hG')

theorem treeWidth_le {H : SimpleGraph α} (h : H ≤ G) : treeWidth H ≤ treeWidth G := by
  apply sInf_le_sInf
  rintro w ⟨D, rfl⟩
  exact ⟨D.restrict' h, rfl⟩

theorem treeWidth_mono {H : G.Subgraph} : treeWidth H.coe ≤ treeWidth G := by
  unfold treeWidth
  refine le_csInf ⟨_, TreeDecomposition.trivial, rfl⟩ ?_
  rintro w ⟨D, rfl⟩
  exact le_trans (sInf_le ⟨D.restrict H, rfl⟩) (D.width_restrict_le H)

theorem treeWidth_contract (h : G ≼c H) : treeWidth G ≤ treeWidth H := by
  rcases h with ⟨φ, hφs, hφa, rfl⟩
  unfold treeWidth
  refine le_csInf ⟨_, TreeDecomposition.trivial, rfl⟩ ?_
  rintro w ⟨D, rfl⟩
  exact le_trans (sInf_le ⟨D.map φ hφs hφa, rfl⟩) (D.width_map_le φ hφs hφa)

theorem treeWidth_minor (h : G ≼ H) : treeWidth G ≤ treeWidth H := by
  rcases h with ⟨K, hK⟩
  exact le_trans (treeWidth_contract hK) (treeWidth_mono (H := K))

theorem treeWidth_le_one [Nonempty α] : treeWidth G ≤ 1 ↔ G.IsAcyclic := by
  constructor
  · intro htw
    have hne : {w | ∃ D : TreeDecomposition G, D.width = w}.Nonempty := ⟨_, .trivial, rfl⟩
    obtain ⟨D, hD_width⟩ := csInf_mem hne
    have hD1 : D.width ≤ 1 := hD_width ▸ htw
    have hbag : ∀ t : D.ι, (D.V t).encard ≤ 2 := fun t => by
      have h := (iSup_le_iff.mp hD1) t; rw [tsub_le_iff_right] at h; exact_mod_cast h
    intro v c hc
    have hlen := hc.three_le_length
    have hab : G.Adj v c.snd := by
      simpa using c.adj_getVert_succ (Walk.not_nil_iff_lt_length.mp hc.not_nil)
    have hda : G.Adj c.penultimate v := c.adj_penultimate hc.not_nil
    have hvsnd_ne : v ≠ c.snd := by
      simp only [Walk.snd]; intro h
      exact absurd (hc.getVert_injOn'
        (Set.mem_setOf_eq.mpr (by omega : 0 ≤ c.length - 1))
        (Set.mem_setOf_eq.mpr (by omega : 1 ≤ c.length - 1))
        (by simpa using h)) (by omega)
    have hvpen_ne : v ≠ c.penultimate := by
      intro h
      exact absurd (hc.getVert_injOn'
        (Set.mem_setOf_eq.mpr (by omega : 0 ≤ c.length - 1))
        (Set.mem_setOf_eq.mpr (Nat.le_refl _))
        (by simpa [Walk.penultimate] using h)) (by omega)
    obtain ⟨tab, htab_v, htab_b⟩ := D.edge_mem_bag hab
    obtain ⟨tda, htda_d, htda_v⟩ := D.edge_mem_bag hda
    have hb_notda : c.snd ∉ D.V tda := fun hb =>
      absurd (encard_three_ne hvsnd_ne hvpen_ne hc.snd_ne_penultimate ▸
        (encard_mono (Set.insert_subset_iff.mpr ⟨htda_v,
          Set.insert_subset_iff.mpr ⟨hb, Set.singleton_subset_iff.mpr htda_d⟩⟩)).trans (hbag tda))
        (by decide)
    obtain ⟨t₁, t₂, hadj12, hbt₁, hbt₂, hord12tda, hord_tab_t₁_tda⟩ :=
      exists_transition D.tree (P := (c.snd ∈ D.V ·))
        (D.tree.path tab tda).1 (D.tree.path tab tda).2 htab_b hb_notda
    have hord_tab_t₂_tda : D.tree.ordered tab t₂ tda := by
      simp only [IsTree.ordered] at *
      rw [D.tree.path_split hord_tab_t₁_tda, Walk.mem_support_append_iff]; exact Or.inr hord12tda
    have hv_t₁ : v ∈ D.V t₁ := D.bag_inter hord_tab_t₁_tda ⟨htab_v, htda_v⟩
    have hv_t₂ : v ∈ D.V t₂ := D.bag_inter hord_tab_t₂_tda ⟨htab_v, htda_v⟩
    have hb_U1 : c.snd ∈ D.U₁ t₁ t₂ :=
      Set.mem_biUnion (by simp [IsTree.left, IsTree.ordered_left]) hbt₁
    have hd_U2 : c.penultimate ∈ D.U₂ t₁ t₂ :=
      Set.mem_biUnion (by simp [IsTree.right, hord12tda]) htda_d
    have hsep := D.separates_singletons_of_mem_sides hadj12 hb_U1 hd_U2
    have hadhesion : D.V t₁ ∩ D.V t₂ ⊆ {v} := fun x ⟨hx_t₁, hx_t₂⟩ => by
      simp only [Set.mem_singleton_iff]; by_contra hxv
      by_cases hxb : x = c.snd
      · exact hbt₂ (hxb ▸ hx_t₂)
      · exact absurd (encard_three_ne hvsnd_ne (Ne.symm hxv) (Ne.symm hxb) ▸
          (encard_mono (Set.insert_subset_iff.mpr ⟨hv_t₁,
            Set.insert_subset_iff.mpr ⟨hbt₁, Set.singleton_subset_iff.mpr hx_t₁⟩⟩)).trans
          (hbag t₁)) (by decide)
    have hd_tail : c.penultimate ∈ c.tail.support := by
      have hd : c.penultimate ∈ c.support :=
        (List.dropLast_sublist _).subset (Walk.penultimate_mem_dropLast_support hc.not_nil)
      rw [← Walk.cons_support_tail c hc.not_nil] at hd
      exact (List.mem_cons.mp hd).resolve_left hvpen_ne.symm
    let bwd := c.tail.takeUntil c.penultimate hd_tail
    have hv_not_bwd : v ∉ bwd.support :=
      Walk.endpoint_notMem_support_takeUntil hc.isPath_tail hd_tail hvpen_ne
    obtain ⟨x, hx_supp, hx_sep⟩ := hsep c.snd rfl c.penultimate rfl bwd
    exact hv_not_bwd (Set.mem_singleton_iff.mp (hadhesion hx_sep) ▸ hx_supp)
  · intro h
    obtain ⟨H, h1, h2⟩ := exists_maximal_isAcyclic_of_le_isAcyclic le_top h
    simp at h2
    trans (treeWidth H)
    · apply treeWidth_le h1
    · apply treeWidth_tree_le_one h2

theorem treeWidth_loop_le_two (h : 2 < n) : treeWidth (cycleGraph n) ≤ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  exact csInf_le_of_le (OrderBot.bddBelow _) ⟨td_cycle m, td_cycle_width⟩ le_rfl

#print axioms treeWidth_minor
