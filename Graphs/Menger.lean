import Architect
import Graphs.Map
import Graphs.Util
import Graphs.Separation
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Int.Star
import Mathlib.Data.Set.Card

set_option maxHeartbeats 0

open Classical Set

variable {V W : Type*} {G : SimpleGraph V} {x y u v w : V} {e : G.Adj x y} {A B X : Set V} {n : ℕ}

namespace SimpleGraph

def Separator (G : SimpleGraph V) (A B : Set V) := { S : Set V // G.Separates A B S }

lemma Separates.swap (hS : G.Separates A B X) : G.Separates B A X := by
  intro u hu v hv p
  obtain ⟨w, hw, hwX⟩ := hS v hv u hu p.reverse
  exact ⟨w, by simpa using hw, hwX⟩

namespace Separator

instance nonempty (G : SimpleGraph V) (A B : Set V) : Nonempty (G.Separator A B) :=
  ⟨A, fun u hu _ _ p => ⟨u, p.start_mem_support, hu⟩⟩

def swap (S : G.Separator A B) : G.Separator B A := ⟨S.1, S.2.swap⟩

def of_vertex_cover (S : Set V) (hS : ∀ e ∈ G.edgeSet, ∃ v ∈ S, v ∈ e) : G.Separator A B := by
  refine ⟨A ∩ B ∪ S, ?_⟩
  intro u hu v hv p
  by_cases hp : p.Nil
  · exact ⟨u, p.start_mem_support, Or.inl ⟨hu, Walk.Nil.eq hp ▸ hv⟩⟩
  · rw [Walk.not_nil_iff] at hp
    obtain ⟨w, e, q, rfl⟩ := hp
    have hmem : s(u, w) ∈ (Walk.cons e q).edges := by simp [Walk.edges]
    obtain ⟨z, hz_S, hz_e⟩ := hS s(u, w) (Walk.edges_subset_edgeSet _ hmem)
    rw [Sym2.mem_iff] at hz_e
    rcases hz_e with rfl | rfl
    · exact ⟨z, Walk.start_mem_support _, Or.inr hz_S⟩
    · exact ⟨z, List.mem_cons_of_mem _ q.start_mem_support, Or.inr hz_S⟩

end Separator

structure ABPath (G : SimpleGraph V) (A B : Set V) where
  u : A
  v : B
  p : G.Path u v

namespace ABPath

abbrev support (P : G.ABPath A B) : Set V := {v | v ∈ P.p.1.support}

end ABPath

def disjointPaths (P : Set (G.ABPath A B)) : Prop := P.Pairwise (Disjoint ·.support ·.support)

def Joiner (G : SimpleGraph V) (A B : Set V) := { P : Set (G.ABPath A B) // disjointPaths P }

namespace Joiner

variable {P : G.Joiner A B}

instance : Nonempty (G.Joiner A B) := ⟨⟨∅, Set.pairwise_empty _⟩⟩

theorem le_separator (P : G.Joiner A B) (S : G.Separator A B) : P.1.encard ≤ S.1.encard := by
  have key (p : G.ABPath A B) : ∃ x ∈ p.support, x ∈ S.1 := S.2 p.u p.u.2 p.v p.v.2 p.p
  choose f hf_supp hf_sep using key
  have hf_inj : Set.InjOn f P.1 := by
    intro p hp q hq hpq
    by_contra h
    exact Set.disjoint_left.mp (P.2 hp hq h) (hf_supp p) (hpq ▸ hf_supp q)
  exact Set.encard_le_encard_of_injOn (fun _ hp => hf_sep _) hf_inj

theorem le_A (P : G.Joiner A B) : P.1.encard ≤ A.encard :=
  P.le_separator ⟨A, fun u hu _ _ p => ⟨u, p.start_mem_support, hu⟩⟩

end Joiner

noncomputable def mincut (G : SimpleGraph V) (A B : Set V) := ⨅ S : G.Separator A B, S.1.encard

noncomputable def maxflow (G : SimpleGraph V) (A B : Set V) := ⨆ P : G.Joiner A B, P.1.encard

lemma mincut_le_encard (S : G.Separator A B) : G.mincut A B ≤ S.1.encard :=
  iInf_le_of_le S le_rfl

lemma mincut_le_encard_of_separates (hS : G.Separates A B X) : G.mincut A B ≤ X.encard :=
  mincut_le_encard ⟨X, hS⟩

lemma encard_le_maxflow_of_joiner (P : G.Joiner A B) : P.1.encard ≤ G.maxflow A B :=
  le_iSup_of_le P le_rfl

lemma exists_separator_of_mincut_lt {k : ℕ∞} (h : G.mincut A B < k) :
    ∃ S : G.Separator A B, S.1.encard < k := by
  by_contra h_all
  push_neg at h_all
  exact absurd (le_iInf h_all) (not_le.mpr h)

@[blueprint "thm:maxflow_le_mincut"
  (statement := /-- The maximum number of disjoint A-B paths is at most the
    minimum size of an A-B separator. -/)]
theorem maxflow_le_mincut : G.maxflow A B ≤ G.mincut A B := by
  apply iSup_le; intro P; apply le_iInf; intro S; exact P.le_separator S

private lemma exists_new_disjoint_path (P : Set (G.ABPath A B))
    (h_not_sep : ¬ G.Separates A B (⋃ p ∈ P, p.support)) :
    ∃ q : G.ABPath A B, ∀ p ∈ P, Disjoint q.support p.support := by
  simp only [Separates, not_forall] at h_not_sep
  obtain ⟨u, hu, v, hv, w, hw⟩ := h_not_sep
  push_neg at hw
  refine ⟨⟨⟨u, hu⟩, ⟨v, hv⟩, w.toPath⟩, fun p hp => ?_⟩
  rw [Set.disjoint_left]
  intro z hz hp'
  exact hw z (Walk.support_toPath_subset w hz) (Set.mem_biUnion hp hp')

private lemma ABPath.support_finite (p : G.ABPath A B) : p.support.Finite :=
  Set.Finite.ofFinset p.p.1.support.toFinset (by simp)

private lemma finite_not_separates_of_mincut_top (h : G.mincut A B = ⊤) (S : Set V) (hS : S.Finite) :
    ¬ G.Separates A B S := by
  intro h_sep
  have : (⊤ : ℕ∞) ≤ S.encard :=
    h ▸ mincut_le_encard_of_separates h_sep
  exact absurd (lt_of_le_of_lt this hS.encard_lt_top) (lt_irrefl _)

private lemma extend_joiner_of_mincut_top (h : G.mincut A B = ⊤) (P : G.Joiner A B) (hP_fin : P.1.Finite) :
    ∃ Q : G.Joiner A B, P.1.encard + 1 ≤ Q.1.encard := by
  have h_not_sep : ¬ G.Separates A B (⋃ p ∈ P.1, p.support) :=
    finite_not_separates_of_mincut_top h _
      (Set.Finite.biUnion hP_fin (fun p _ => ABPath.support_finite p))
  obtain ⟨q, hq_disj⟩ := exists_new_disjoint_path P.1 h_not_sep
  have hq_not_mem : q ∉ P.1 := by
    intro hq_mem
    exact Set.disjoint_left.mp (hq_disj q hq_mem)
      q.p.1.start_mem_support q.p.1.start_mem_support
  refine ⟨⟨insert q P.1, ?_⟩, ?_⟩
  · intro a ha b hb hab
    simp only [Set.mem_insert_iff] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact absurd rfl hab
    · exact hq_disj b hb
    · exact (hq_disj a ha).symm
    · exact P.2 ha hb hab
  · rw [Set.encard_insert_of_notMem hq_not_mem]

theorem maxflow_infinite_of_mincut_infinite (h : G.mincut A B = ⊤) : G.maxflow A B = ⊤ := by
  rw [maxflow, iSup_eq_top]
  intro b hb
  obtain ⟨n, rfl⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hb)
  suffices ∀ k : ℕ, ∃ P : G.Joiner A B, (k : ℕ∞) ≤ P.1.encard by
    obtain ⟨P, hP⟩ := this (n + 1)
    exact ⟨P, lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by omega)) hP⟩
  intro k
  induction k with
  | zero => exact ⟨⟨∅, Set.pairwise_empty _⟩, zero_le _⟩
  | succ m ih =>
    obtain ⟨P, hP⟩ := ih
    by_cases hP_top : P.1.encard = ⊤
    · exact ⟨P, hP_top ▸ le_top⟩
    · have hP_fin : P.1.Finite := Set.encard_ne_top_iff.mp hP_top
      obtain ⟨Q, hQ⟩ := extend_joiner_of_mincut_top h P hP_fin
      exact ⟨Q, le_trans (by push_cast; exact add_le_add hP le_rfl) hQ⟩

theorem Menger_of_mincut_top (h : G.mincut A B = ⊤) : G.mincut A B = G.maxflow A B :=
  h ▸ (maxflow_infinite_of_mincut_infinite h).symm

lemma mincut_le_inter_add_edgeSet : G.mincut A B ≤ (A ∩ B).encard + G.edgeSet.encard := by
  have exists_vertex_cover : ∃ S : Set V, (∀ e ∈ G.edgeSet, ∃ v ∈ S, v ∈ e) ∧
      S.encard ≤ G.edgeSet.encard := by
    refine ⟨(fun e : Sym2 V => (Quot.out e).1) '' G.edgeSet, ?_, Set.encard_image_le _ _⟩
    intro e he
    exact ⟨(Quot.out e).1, ⟨e, he, rfl⟩, Sym2.out_fst_mem e⟩
  obtain ⟨S, hS_cover, hS_card⟩ := exists_vertex_cover
  exact le_trans
    (mincut_le_encard (Separator.of_vertex_cover S hS_cover))
    (le_trans (Set.encard_union_le _ _) (add_le_add_right hS_card _))

lemma inter_subset_separator (S : G.Separator A B) : A ∩ B ⊆ S.1 := by
  intro v ⟨hv_A, hv_B⟩
  obtain ⟨w, hw_supp, hw_S⟩ := S.2 v hv_A v hv_B Walk.nil
  simp at hw_supp; exact hw_supp ▸ hw_S

lemma inter_le_mincut : (A ∩ B).encard ≤ G.mincut A B :=
  le_iInf fun S => Set.encard_le_encard (inter_subset_separator S)

lemma inter_le_maxflow : (A ∩ B).encard ≤ G.maxflow A B := by
  let γ : ↥(A ∩ B) → G.ABPath A B := fun a =>
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
  calc (A ∩ B).encard = (Set.range γ).encard := by
          rw [← Set.image_univ, hγ_inj.encard_image]; simp
    _ ≤ G.maxflow A B := encard_le_maxflow_of_joiner ⟨_, h_joiner⟩

lemma Menger_strong_base (h : G.edgeSet = ∅) : G.mincut A B ≤ G.maxflow A B := by
  simp at h ; subst G
  have h_mincut_le : mincut ⊥ A B ≤ (A ∩ B).encard :=
    mincut_le_encard ⟨A ∩ B, fun a ha b hb p => ⟨a, p.start_mem_support, by
      have := (show ∀ u v, (⊥ : SimpleGraph V).Walk u v → u = v by
        intro u v p; induction p <;> aesop) a b p
      simp [← this] at hb; simp [ha, hb]⟩⟩
  exact h_mincut_le.trans inter_le_maxflow

/-
Definitions for edge contraction: the setoid identifying the endpoints, the
contracted graph, and the projection map.
-/
def contractSetoid (_ : G.Adj x y) : Setoid V :=
  Setoid.mk (fun a b => a = b ∨ (a = x ∧ b = y) ∨ (a = y ∧ b = x)) (by constructor <;> aesop)

abbrev contractType (V : Type*) {G : SimpleGraph V} {x y : V} (e : G.Adj x y) := Quotient (contractSetoid e)

infix:60 " / " => contractType

def contract (G : SimpleGraph V) (e : G.Adj x y) : SimpleGraph (V / e) :=
  fromRel (fun a b => ∃ a' b', ⟦a'⟧ = a ∧ ⟦b'⟧ = b ∧ G.Adj a' b')

infix:60 " / " => contract

lemma contract_eq_map (e : G.Adj x y) : G / e = G.map (⟦·⟧) := by
  ext a b
  simp [SimpleGraph.map, Relation.Map, contract, Quotient.mk_eq_iff_out]
  intro h ; constructor ; rintro (⟨a', h1, b', h2, h3⟩ | ⟨a', h1, b', h2, h3⟩)
  all_goals { grind [Adj.symm] }

def contract_image (S : Set V) (e : G.Adj x y) : Set (V / e) := (⟦·⟧) '' S

infix:60 " / " => contract_image

@[simp] lemma mem_contract_image {S : Set V} {q : V / e} : q ∈ S / e ↔ ∃ v ∈ S, ⟦v⟧ = q := by rfl

lemma finite_inter_contract_image (hAB : (A ∩ B).Finite) : ((A / e) ∩ (B / e)).Finite := by
  apply Set.Finite.subset ((hAB.image (⟦·⟧)).union (Set.finite_singleton (⟦x⟧)))
  intro q ⟨⟨a, ha, haq⟩, b, hb, hbq⟩
  simp at haq hbq
  have hab_q : (⟦a⟧ : V / e) = ⟦b⟧ := by rw [haq, hbq]
  by_cases hab : a = b
  · exact Or.inl ⟨a, ⟨ha, hab ▸ hb⟩, haq⟩
  · right
    rw [Set.mem_singleton_iff, ← haq]
    rw [Quotient.eq] at hab_q
    rcases hab_q with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hab
    · rfl
    · grind

-- TODO use `SimpleGraph.map`
lemma Walk.contract (p : G.Walk u v) (e : G.Adj x y) :
    ∃ w : (G / e).Walk ⟦u⟧ ⟦v⟧, w.support.toFinset ⊆ p.support.toFinset.image (⟦·⟧) := by
  induction' p with u v p ih
  · exact ⟨Walk.nil, by simp⟩
  · simp +zetaDelta at *
    cases' ‹∃ w, _› with w hw
    by_cases h : (⟦v⟧ : V / e) = ⟦p⟧
    · grind
    · have h_adj : (G / e).Adj ⟦v⟧ ⟦p⟧ := by
        simp [_root_.SimpleGraph.contract]
        grind
      refine' ⟨ Walk.cons h_adj w, _ ⟩
      simp_all [ Finset.subset_iff ]

noncomputable abbrev contract_preimage (Y : Set (V / e)) : Set V := {v | ⟦v⟧ ∈ Y}

lemma mem_contract_preimage {Y : Set (V / e)} : v ∈ contract_preimage Y ↔ ⟦v⟧ ∈ Y := by rfl

lemma contract_preimage_separates (Y : (G / e).Separator (A / e) (B / e)) :
    G.Separates A B (contract_preimage Y.1) := by
  intro u hu v hv p
  obtain ⟨ w, hw ⟩ := Walk.contract p e
  obtain ⟨ z, hzY, hzw ⟩ : ∃ z ∈ Y.1, z ∈ w.support := by
    have := Y.2 ⟦u⟧
      (by exact Set.mem_image_of_mem _ hu)
      ⟦v⟧
      (by exact Set.mem_image_of_mem _ hv)
      w.toPath
    exact this |> fun ⟨z, hz₁, hz₂ ⟩ => ⟨ z, hz₂, by simpa using Walk.support_bypass_subset _ hz₁ ⟩
  have := hw ( by simpa using hzw )
  simp only [Finset.mem_image, List.mem_toFinset] at this
  grind [mem_contract_preimage]

@[simp] lemma contract_same : (⟦y⟧ : V / e) = ⟦x⟧ := by
  simp [Quotient.eq, contractSetoid]

lemma contractEdgeProj_eq_vertex_iff : (⟦u⟧ : V / e) = ⟦x⟧ ↔ u = x ∨ u = y := by
  simp [contractSetoid, Quotient.eq] ; grind

lemma contractEdge_adj_lift (hu : (⟦u⟧ : V / e) ≠ ⟦x⟧) (hv : (⟦v⟧ : V / e) ≠ ⟦x⟧) :
    (G / e).Adj ⟦u⟧ ⟦v⟧ → G.Adj u v := by
  rintro ⟨ a, b, ha, hb, hab ⟩
  · simp_all [ Quotient.eq ]
    unfold contractSetoid at *; aesop
  · have h_adj : (⟦v⟧ : V / e) ≠ ⟦x⟧ → (⟦u⟧ : V / e) ≠ ⟦x⟧ → (G / e).Adj ⟦v⟧ ⟦u⟧ → G.Adj v u := by
      simp_all [ Quotient.eq ]
      unfold contractSetoid at *; aesop
    simp_all [ adj_comm ]
    unfold contract at *; aesop

private lemma quot_injOn_away {Y : Set (V / e)} (hv : ⟦x⟧ ∉ Y) :
    Set.InjOn (fun v => (⟦v⟧ : V / e)) (contract_preimage Y) := by
  intro a ha b hb hab
  simp only [contract_preimage, Set.mem_setOf_eq] at ha hb
  simp only [Quotient.eq, contractSetoid] at hab
  grind

@[simp] private lemma quot_image_preimage (Y : Set (V / e)) :
    (fun v : V => (⟦v⟧ : V / e)) '' (contract_preimage Y) = Y := by
  ext z
  simp only [Set.mem_image, contract_preimage, Set.mem_setOf_eq]
  constructor
  · rintro ⟨v, hv, rfl⟩; exact hv
  · intro hz; obtain ⟨v, rfl⟩ := Quotient.exists_rep z; exact ⟨v, hz, rfl⟩

@[simp] lemma encard_preimage_contractEdge {Y : Set (V / e)} (hx : ⟦x⟧ ∈ Y) :
    (contract_preimage Y).encard = Y.encard + 1 := by
  change (_ ⁻¹' _).encard = _
  rw [← diff_union_of_subset (singleton_subset_iff.mpr hx)]
  simp only [preimage_union]
  rw [encard_union_eq disjoint_sdiff_left, encard_union_eq (by simp [disjoint_sdiff_left]), add_assoc]
  congr 1
  · change (contract_preimage _).encard = _
    nth_rewrite 2 [← quot_image_preimage (Y \ {⟦x⟧})]
    refine (InjOn.encard_image ?_).symm
    exact quot_injOn_away (notMem_diff_of_mem rfl)
  · convert_to ({x, y} : Set V).encard = 2
    · congr 1 ; ext z ; simp [contractEdgeProj_eq_vertex_iff]
    · simp +decide
    · have : x ∉ ({y} : Set V) := e.ne
      simp +decide [encard_insert_of_notMem this]

lemma lift_walk_avoiding_contraction {u v : V / e} (p : (G / e).Walk u v) (hp : ⟦x⟧ ∉ p.support) :
    ∃ (u' v' : V) (q : G.Walk u' v'), ⟦u'⟧ = u ∧ ⟦v'⟧ = v ∧
      (q.support.toFinset.image (⟦·⟧)) = p.support.toFinset ∧
      x ∉ q.support ∧ y ∉ q.support := by
  induction' p with u v p ih
  · obtain ⟨ u', rfl ⟩ := Quotient.exists_rep u
    have hu_not_x : u' ≠ x := by
      intro hux
      apply hp
      simp [hux]
    have hu_not_y : u' ≠ y := by
      intro huy
      apply hp
      simp [huy]
    refine ⟨u', u', Walk.nil, rfl, rfl, by simp, ?_, ?_⟩ <;> aesop
  · rename_i h₁ h₂
    obtain ⟨u', hu'⟩ : ∃ u' : V, ⟦u'⟧ = v ∧ u' ≠ x ∧ u' ≠ y := by
      rcases Quotient.exists_rep v with ⟨ u', rfl ⟩
      refine' ⟨ u', rfl, _, _ ⟩ <;> contrapose! hp <;> simp_all
    obtain ⟨ v', hv' ⟩ := h₂ ( by intro h; simp_all [ Walk.support_cons ] )
    obtain ⟨ v'', q, hv'', hv''', hq, hx, hy ⟩ := hv'
    refine' ⟨ u', v'', Walk.cons _ q, hu'.1, hv''', _, _, _ ⟩ <;> simp_all [ Walk.support_cons ];
    · have h_adj : (G / e).Adj ⟦u'⟧ ⟦v'⟧ := by
        grind
      refine contractEdge_adj_lift ?_ ?_ h_adj
      · grind
      · intro h; simp_all
    · tauto
    · grind

def deleteEdge (G : SimpleGraph V) (_e : G.Adj x y) : SimpleGraph V := G.deleteEdges {s(x, y)}

infix:60 " - " => deleteEdge

lemma deleteEdge_le : G - e ≤ G := fun _ _ huv => huv.1

lemma deleteEdge_edgeSet_encard_lt (hfin : G.edgeSet.Finite) : (G - e).edgeSet.encard < G.edgeSet.encard := by
  rw [deleteEdge, edgeSet_deleteEdges]
  exact (hfin.subset Set.diff_subset).encard_lt_encard (Set.diff_singleton_ssubset.mpr e)

/-
A path in the contracted graph avoiding the contracted vertex lifts to a path in the original graph avoiding the contracted edge's endpoints (subset support).
-/
lemma lift_path_avoiding_contraction_AB (A B : Set V) {u v : V / e} (p : (G / e).Walk u v)
      (hp_avoid : ⟦x⟧ ∉ p.support) (hu : u ∈ A / e) (hv : v ∈ B / e) :
    ∃ (u' v' : V) (q : G.Walk u' v'), u' ∈ A ∧ v' ∈ B ∧ ⟦u'⟧ = u ∧ ⟦v'⟧ = v ∧ q.IsPath ∧
      (q.support.toFinset.image (⟦·⟧)) ⊆ p.support.toFinset ∧ x ∉ q.support ∧ y ∉ q.support := by
  obtain ⟨u', v', q, hu', hv', hq⟩ := @lift_walk_avoiding_contraction V G x y e u v p hp_avoid
  refine' ⟨ u', v', q.toPath, _, _, hu', hv', _, _, _ ⟩
  · simp at hu
    obtain ⟨ w, hw, rfl ⟩ := hu
    cases h1 : eq_or_ne u' x <;> cases h2 : eq_or_ne u' y <;> cases h3 : eq_or_ne w x <;> cases h4 : eq_or_ne w y
    all_goals subst_eqs
    all_goals simp_all [Quotient.eq, contractSetoid ]
  · simp at hv
    obtain ⟨ w, hw ⟩ := hv
    have h_inj : ∀ a b : V, (⟦a⟧ : V / e) = ⟦b⟧ → a = b ∨ a = x ∧ b = y ∨ a = y ∧ b = x := by
      intro a b hab; erw [ Quotient.eq ] at hab; aesop
    cases h_inj _ _ ( hv'.trans hw.2.symm ) <;> aesop;
  · exact q.toPath.isPath
  · rw [ ← hq.1 ]
    simp [ Finset.subset_iff ]
    intro a ha
    exact ⟨ a, by simpa using Walk.support_toPath_subset q ha, rfl ⟩
  · exact ⟨ fun h => hq.2.1 <| by simpa using q.support_bypass_subset h, fun h => hq.2.2 <|
      by simpa using q.support_bypass_subset h ⟩

lemma contractEdge_adj_lift_vertex (hu : (⟦u⟧ : V / e) ≠ ⟦x⟧) : (G / e).Adj ⟦u⟧ ⟦x⟧ → G.Adj u x ∨ G.Adj u y := by
  rintro ⟨ a, ⟨ a', b', ha', hb', hab ⟩ | ⟨ a', b', ha', hb', hab ⟩ ⟩
  · simp [ Quotient.eq, contractSetoid ] at * ; grind
  · rw [ eq_comm ] at ha' hb'
    cases eq_or_ne a' x <;> cases eq_or_ne a' y <;> cases eq_or_ne b' x <;> cases eq_or_ne b' y
    all_goals { simp [ Quotient.eq, contractSetoid, adj_comm ] at * ; grind }

lemma contract_encard_lt (hfin : G.edgeSet.Finite) : (G / e).edgeSet.encard < G.edgeSet.encard := by
  have hxy : (⟦x⟧ : V / e) = ⟦y⟧ := by simp
  have h_sub : (G / e).edgeSet ⊆ Sym2.map (⟦·⟧) '' (G.edgeSet \ {s(x, y)}) := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      simp only [mem_edgeSet, contract, fromRel_adj] at he
      obtain ⟨hab, (⟨a', b', ha', hb', hadj⟩ | ⟨a', b', ha', hb', hadj⟩)⟩ := he
      all_goals {
        refine ⟨s(a', b'), ⟨hadj, fun heq => hab ?_⟩,
          by simp [Sym2.map_mk, ha', hb', Sym2.eq_swap]⟩
        have : (⟦a'⟧ : V / e) = ⟦b'⟧ := by
          have heq' : s(a', b') = s(x, y) := by simpa using heq
          rcases Sym2.eq_iff.mp heq' with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact hxy
          · exact hxy.symm
        rw [← ha', ← hb']
        first | exact this | exact this.symm }
  calc (G / e).edgeSet.encard
    ≤ (Sym2.map (⟦·⟧) '' (G.edgeSet \ {s(x, y)})).encard := Set.encard_le_encard h_sub
    _ ≤ (G.edgeSet \ {s(x, y)}).encard := Set.encard_image_le _ _
    _ < G.edgeSet.encard :=
        (hfin.subset Set.diff_subset).encard_lt_encard (Set.diff_singleton_ssubset.mpr e)

lemma Walk.edges_no_xy_of_support_inter_subset_one {p : G.Walk u v} (hxy : x ≠ y)
    (h : p.support.toFinset ∩ {x, y} ⊆ {v}) :
    s(x, y) ∉ p.edges := by
  contrapose! h
  have h1 := p.fst_mem_support_of_mem_edges h
  have h2 := p.snd_mem_support_of_mem_edges h
  simp [ Finset.eq_singleton_iff_unique_mem ]
  aesop

noncomputable def Walk.firstVisit (X : Set V) : ∀ {u v} (p : G.Walk u v), (∃ w ∈ p.support, w ∈ X) → V
  | u, _, Walk.nil, hp => u
  | u, v, Walk.cons h p, hp => if h : u ∈ X then u else p.firstVisit X (by grind)

theorem firstVisit_mem_support {X : Set V} {p : G.Walk u v} {hp : ∃ w ∈ p.support, w ∈ X} :
    p.firstVisit X hp ∈ p.support := by
  induction' p ; simp [Walk.firstVisit] ; grind [Walk.firstVisit]

theorem firstVisit_mem_X {X : Set V} {p : G.Walk u v} {hp : ∃ w ∈ p.support, w ∈ X} :
    p.firstVisit X hp ∈ X := by
  induction' p ; simpa [Walk.firstVisit] using hp ; grind [Walk.firstVisit]

theorem firstVisit_mem_takeUntil {X : Set V} {p : G.Walk u v} (h1 : w ∈ p.support) (h2 : w ∈ X) :
    p.firstVisit X ⟨w, h1, h2⟩ ∈ (p.takeUntil _ h1).support := by
  induction' p with u u ; simp [Walk.firstVisit, Walk.takeUntil]
  by_cases h3 : u ∈ X ; simp [Walk.firstVisit, Walk.takeUntil, h3]
  grind [Walk.firstVisit, Walk.takeUntil]

noncomputable def Walk.takeUntilFirst (X : Set V) (p : G.Walk u v) (hp : ∃ w ∈ p.support, w ∈ X) :
    G.Walk u (p.firstVisit X hp) :=
  p.takeUntil _ firstVisit_mem_support

theorem takeUntilFirst_subset_support {X : Set V} {p : G.Walk u v} {hp : ∃ w ∈ p.support, w ∈ X} :
    (p.takeUntilFirst X hp).support ⊆ p.support :=
  (Walk.isSubwalk_takeUntil _ _).support_subset

lemma Walk.exists_walk_prefix_avoiding_set {X : Set V} {p : G.Walk u v} (hp : ∃ w ∈ p.support, w ∈ X) :
    ∃ (w : V) (q : G.Walk u w), w ∈ X ∧ q.support ⊆ p.support ∧ (∀ z ∈ q.support, z ∈ X → z = w) := by
  refine ⟨p.firstVisit X hp, p.takeUntilFirst X hp, firstVisit_mem_X, takeUntilFirst_subset_support, ?_⟩
  intro z hz hzX
  have hz' : z ∈ p.support := takeUntilFirst_subset_support hz
  contrapose! hz
  apply Walk.notMem_support_takeUntil_support_takeUntil_subset hz.symm hz'
  exact firstVisit_mem_takeUntil hz' hzX

lemma Walk.exists_path_prefix_avoiding_set {X : Set V} {p : G.Walk u v} (h : ∃ w ∈ p.support, w ∈ X) :
    ∃ (w : V) (q : G.Walk u w), w ∈ X ∧ q.IsPath ∧ q.support ⊆ p.support ∧ (∀ z ∈ q.support, z ∈ X → z = w) := by
  obtain ⟨w', q, hw'X, hq_support, hq_unique⟩ := p.exists_walk_prefix_avoiding_set h
  refine ⟨w', q.bypass, hw'X, q.bypass_isPath, ?_, ?_⟩ <;> grind [q.support_bypass_subset]

lemma separates_of_separates_delete (A B : Set V) (e : G.Adj x y) (X : G.Separator A B)
    (S : (G - e).Separator A X.1) (hx : x ∈ X.1) (hy : y ∈ X.1) : G.Separates A B S.1 := by
  intro u hu v hv p
  have h_sep := X.2 u hu v hv p
  obtain ⟨w, q, hwX, hqpath, hq_support, hq_avoid⟩ := Walk.exists_path_prefix_avoiding_set h_sep
  have hq_avoid_xy : s(x, y) ∉ q.edges := by
    grind [Walk.edges_no_xy_of_support_inter_subset_one e.ne, List.mem_toFinset]
  let q' := q.toDeleteEdge _ hq_avoid_xy
  have h2 : q'.support ⊆ q.support := by simp [q', Walk.toDeleteEdge, Walk.toDeleteEdges]
  have h3 := S.2 u hu w hwX q'
  grind

theorem vertex_mem_contract_separator (Y : (G / e).Separator (A / e) (B / e))
    (hY_card : Y.1.encard < G.mincut A B) : ⟦x⟧ ∈ Y.1 := by
  contrapose! hY_card
  have h_sep : G.Separates A B (contract_preimage Y.1) := contract_preimage_separates Y
  have h_encard : (contract_preimage Y.1).encard ≤ Y.1.encard := by
    apply Set.encard_le_encard_of_injOn (f := (⟦·⟧))
    · intro ; grind
    · rintro v hv w - hvw ; simp [Quotient.eq, contractSetoid] at hvw ; aesop
  calc G.mincut A B ≤ (contract_preimage Y.1).encard := mincut_le_encard_of_separates h_sep
    _ ≤ Y.1.encard := h_encard

/- --------------- REVIEW --------------- -/

lemma disjoint_paths_prop (hX_fin : X.Finite) {P : G.Joiner A X} (hP_card : P.1.encard = X.encard) :
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
lemma ABPath_prefix_avoids_X {A X : Set V} (p : G.ABPath A X)
  (hp_X : p.support ∩ X = {p.v.1})
  (z : V)
  (hz : z ∈ p.p.1.support)
  (hzX : z ∉ X) :
  (↑(p.p.1.takeUntil z hz).support.toFinset : Set V) ∩ X = ∅ := by
    simp only [Set.eq_empty_iff_forall_notMem, Set.mem_inter_iff, Finset.mem_coe, not_and]
    intro a ha haX
    have ha_support : a ∈ p.p.1.support :=
      Walk.support_takeUntil_subset p.p.1 hz (List.mem_toFinset.mp ha)
    have ha_eq : a = p.v.1 := by
      have h1 : a ∈ p.support ∩ X := ⟨ha_support, haX⟩
      rw [hp_X] at h1
      exact h1
    rw [ha_eq] at ha
    have hne : p.v.1 ≠ z := by
      intro heq; rw [← heq] at hzX
      have : p.v.1 ∈ p.support ∩ X := by rw [hp_X]; rfl
      exact hzX this.2
    exact (Walk.endpoint_notMem_support_takeUntil p.p.2 hz hne)
      (List.mem_toFinset.mp ha)

/-
If a walk is a path, and we drop the prefix until a vertex w (where w is not the start), then the start vertex is not in the remaining suffix.
-/
lemma Walk.start_notMem_support_dropUntil {p : G.Walk u v} (hp : p.IsPath) (hw : w ∈ p.support) (h : u ≠ w) :
    u ∉ (p.dropUntil w hw).support := by
  cases p with
  | nil => simp at hw ; grind
  | cons e p =>
    contrapose hp ; simp [Walk.dropUntil, h] at hp ; simp [h.symm] at hw ; simp [p.support_dropUntil_subset hw hp]

/-
If an X-B path intersects X only at its start point, then any suffix starting at a vertex not in X avoids X entirely.
-/
lemma ABPath_suffix_avoids_X {B X : Set V} (q : G.ABPath X B)
  (hq_X : q.support ∩ X = {q.u.1})
  (z : V)
  (hz : z ∈ q.p.1.support)
  (hzX : z ∉ X) :
  (↑(q.p.1.dropUntil z hz).support.toFinset : Set V) ∩ X = ∅ := by
    simp only [Set.eq_empty_iff_forall_notMem, Set.mem_inter_iff, Finset.mem_coe, not_and]
    intro a ha haX
    have ha_support : a ∈ q.p.1.support :=
      q.p.1.support_dropUntil_subset hz (List.mem_toFinset.mp ha)
    have ha_eq : a = q.u.1 := by
      have h1 : a ∈ q.support ∩ X := ⟨ha_support, haX⟩
      rw [hq_X] at h1
      exact h1
    rw [ha_eq] at ha
    have : q.u.1 ≠ z := by
      intro heq; rw [← heq] at hzX
      have : q.u.1 ∈ q.support ∩ X := by rw [hq_X]; rfl
      exact hzX this.2
    exact (Walk.start_notMem_support_dropUntil q.p.2 hz this)
      (List.mem_toFinset.mp ha)

/-
If X separates A and B, and p is an A-X path hitting X only at the end, and q is an X-B path hitting X only at the start, then p and q intersect only at their common endpoint in X (if any).
-/
lemma path_intersection_of_separator (X : G.Separator A B) (p : G.ABPath A X.1)
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
    have hw1 := ABPath_prefix_avoids_X p hp_X z hz.1 hzX
    have hw2 := ABPath_suffix_avoids_X q hq_X z hz.2 hzX
    have h_walk := X.2 p.u.1 p.u.2 q.v.1 q.v.2
      ((p.p.1.takeUntil z hz.1).append (q.p.1.dropUntil z hz.2))
    obtain ⟨w, hw_mem, hw_X⟩ := h_walk
    rw [Walk.support_append] at hw_mem
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
lemma disjoint_paths_prop_start (X B : Set V) (hX_fin : X.Finite)
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
lemma Walk.IsPath_append_of_support_inter_subset_one {G : SimpleGraph V}
  {u v w : V} (p : G.Walk u v) (q : G.Walk v w)
  (hp : p.IsPath) (hq : q.IsPath)
  (h_inter : p.support.toFinset ∩ q.support.toFinset ⊆ {v}) :
  (p.append q).IsPath := by
    have hpq_distinct : ∀ x ∈ p.support, x ≠ v → x ∉ q.support := by
      intro x hx hxv hxq; specialize h_inter ( Finset.mem_inter_of_mem ( List.mem_toFinset.mpr hx ) ( List.mem_toFinset.mpr hxq ) ) ; aesop
    cases p <;> cases q <;> simp_all [ Walk.isPath_def ];
    simp_all [ Walk.support_append ]
    rw [ List.nodup_append ] ; aesop

/-
If p is an A-X path ending at x, and q is an X-B path starting at x, and both intersect X only at x, then their concatenation is a path.
-/
lemma joined_path_is_path (A B : Set V)
  (X : G.Separator A B)
  (x : V)
  (p : G.ABPath A X.1) (h_p : p.v = x) (h_p_X : p.support ∩ X.1 = {x})
  (q : G.ABPath X.1 B) (h_q : q.u = x) (h_q_X : q.support ∩ X.1 = {x}) :
  ((p.p.1.copy rfl h_p).append (q.p.1.copy h_q rfl)).IsPath := by
    have h_support_inter : (p.p.1.copy rfl h_p).support.toFinset ∩ (q.p.1.copy h_q rfl).support.toFinset ⊆ {x} := by
      have h := path_intersection_of_separator X p q
        (by rw [show (p.v : V) = x from h_p]; exact h_p_X)
        (by rw [show (q.u : V) = x from h_q]; exact h_q_X)
      simp only [Walk.support_copy]
      exact h.trans (by simp [show (p.v : V) = x from h_p, show (q.u : V) = x from h_q])
    apply_rules [ Walk.IsPath_append_of_support_inter_subset_one ]
    · exact (p.p.1.isPath_copy rfl h_p).mpr p.p.2
    · exact (q.p.1.isPath_copy h_q rfl).mpr q.p.2

/-
If X separates A and B, and we have k disjoint paths from A to X and k disjoint paths from X to B, then we can combine them to form k disjoint paths from A to B.
-/
theorem disjoint_paths_join (A B : Set V) (X : G.Separator A B) (k : ℕ∞)
  (hX_fin : X.1.Finite)
  (hX_card : X.1.encard = k) (P_A : G.Joiner A X.1) (hP_A_card : P_A.1.encard = k) (P_B : G.Joiner X.1 B)
  (hP_B_card : P_B.1.encard = k) : ∃ P : G.Joiner A B, P.1.encard = k := by
  have h_end := disjoint_paths_prop hX_fin (hP_A_card.trans hX_card.symm)
  have h_start := disjoint_paths_prop_start X.1 B hX_fin P_B (hP_B_card.trans hX_card.symm)
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
     joined_path_is_path A B X x (pa x hx) (hpa_end x hx) (hpa_inter x hx)
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
If a walk is a path and the start is not the end, it can be decomposed into a prefix path avoiding the end vertex, and a final edge.
-/
lemma Walk.exists_prefix_path_of_path_ne {G : SimpleGraph V}
  {u v : V} (p : G.Walk u v) (hp : p.IsPath) (h_ne : u ≠ v) :
  ∃ (w : V) (q : G.Walk u w),
    G.Adj w v ∧
    q.IsPath ∧
    v ∉ q.support ∧
    q.support.toFinset ⊆ p.support.toFinset := by
      simp +zetaDelta at *
      induction' p with u v p ih
      · contradiction
      · rename_i h₁ h₂ h₃
        by_cases h : p = ih
        · aesop
        · obtain ⟨ w, hw₁, q, hq₁, hq₂, hq₃ ⟩ := h₃ ( by
            cases h₂ <;> aesop ) h;
          refine' ⟨ w, hw₁, cons h₁ q, _, _, _ ⟩ <;> simp_all
          · exact fun h => hp.2 ( by simpa using hq₃ ( by simpa using h ) )
          · grind

/-
If a path ends at a vertex whose projection is adjacent to the contracted vertex, and the path avoids the contracted edge's endpoints, it can be extended to one of the endpoints.
-/
lemma lift_path_extension_step {x y : V} (e : G.Adj x y)
  (u w : V) (q : G.Walk u w)
  (hq_path : q.IsPath)
  (hx_avoid : x ∉ q.support) (hy_avoid : y ∉ q.support)
  (hw_proj_adj : (G / e).Adj ⟦w⟧ ⟦x⟧) :
  ∃ (v : V) (p : G.Walk u v),
    (v = x ∨ v = y) ∧
    p.IsPath ∧
    p.support.toFinset ⊆ q.support.toFinset ∪ {v} ∧
    p.support.toFinset ∩ {x, y} = {v} := by
      have h_w_adj : G.Adj w x ∨ G.Adj w y := by
        have := contractEdge_adj_lift_vertex ?_ hw_proj_adj <;> aesop;
      cases' h_w_adj with h h
      · refine' ⟨ x, q.append ( Walk.cons h Walk.nil ), Or.inl rfl, _, _, _ ⟩ <;> simp_all [ Walk.isPath_def ];
        · simp_all [ Walk.support_append ]
          rw [ List.nodup_append ] ; aesop
        · simp [ Walk.support_append ]
        · ext ; aesop
      · use y
        use q.append (Walk.cons h Walk.nil)
        simp_all [ Walk.isPath_def ]
        simp_all [ Walk.support_append ]
        rw [ List.nodup_append ] ; aesop

/-
A path in the contracted graph ending at the contracted vertex can be lifted to a path in the original graph ending at one of the contracted edge's endpoints.
-/
lemma lift_path_to_contraction_end (A : Set V) {x y : V} (e : G.Adj x y)
  (u' : V / e)
  (p' : (G / e).Walk u' ⟦x⟧)
  (hp'_path : p'.IsPath)
  (hu' : u' ∈ A / e)
  (h_ne : u' ≠ ⟦x⟧) :
  ∃ (u v : V) (p : G.Walk u v),
    u ∈ A ∧
    (v = x ∨ v = y) ∧
    p.IsPath ∧
    (↑p.support.toFinset : Set V) ⊆ contract_preimage (Y := (↑p'.support.toFinset : Set (V / e))) ∧
    p.support.toFinset ∩ {x, y} = {v} := by
  obtain ⟨ w', q', hq'_adj, hq'_path, hq'_avoid, hq'_sub ⟩ :=
    Walk.exists_prefix_path_of_path_ne p' hp'_path h_ne
  -- Normalize Finset subset to List level to avoid DecidableEq instance mismatch on quotient
  simp only [Finset.subset_iff, List.mem_toFinset] at hq'_sub
  obtain ⟨u, w, q, hu, hw, hq_path, hq_support⟩ : ∃ u w : V, ∃ q : G.Walk u w,
      u ∈ A ∧ ⟦u⟧ = u' ∧ ⟦w⟧ = w' ∧ q.IsPath ∧ (∀ z, z ∈ q.support → ⟦z⟧ ∈ q'.support) ∧
      x ∉ q.support ∧ y ∉ q.support := by
    obtain ⟨u, w, q, hu, _, hw1, hw2, hq_path, hq_img, hx, hy⟩ :=
      lift_path_avoiding_contraction_AB A Set.univ q' hq'_avoid hu'
        ⟨Classical.choose (Quotient.exists_rep w'), trivial, Classical.choose_spec (Quotient.exists_rep w')⟩
    simp only [Finset.subset_iff, Finset.mem_image, List.mem_toFinset] at hq_img
    exact ⟨u, w, q, hu, hw1, hw2, hq_path, fun z hz => hq_img ⟨z, hz, rfl⟩, hx, hy⟩
  obtain ⟨v, p, hv, hp_path, hp_support, hp_xy⟩ : ∃ v : V, ∃ p : G.Walk u v, (v = x ∨ v = y) ∧ p.IsPath ∧ p.support.toFinset ⊆ q.support.toFinset ∪ {v} ∧ p.support.toFinset ∩ {x, y} = {v} := by
    have := lift_path_extension_step e u w q hq_support.1 hq_support.2.2.1 hq_support.2.2.2 ?_ <;> aesop;
  refine ⟨u, v, p, hu, hv, hp_path, ?_, hp_xy⟩
  -- Show support subset of preimage
  intro z hz
  simp only [Finset.mem_coe, List.mem_toFinset] at hz
  have hz_fin : z ∈ q.support.toFinset ∪ {v} := hp_support (List.mem_toFinset.mpr hz)
  rcases Finset.mem_union.mp hz_fin with hz_q | hz_v
  · -- z is in q's support
    have h1 : ⟦z⟧ ∈ q'.support := hq_support.2.1 z (List.mem_toFinset.mp hz_q)
    have h2 : ⟦z⟧ ∈ p'.support := hq'_sub h1
    simp only [contract_preimage, Set.mem_setOf_eq, Finset.mem_coe]
    exact List.mem_toFinset.mpr h2
  · -- z = v (which is x or y)
    simp only [Finset.mem_singleton] at hz_v
    simp only [contract_preimage, Set.mem_setOf_eq, Finset.mem_coe]
    have h_end := p'.end_mem_support
    rcases hv with rfl | rfl
    · rw [hz_v]; exact List.mem_toFinset.mpr h_end
    · rw [hz_v, contract_same]; exact List.mem_toFinset.mpr h_end

/-
A path in the contracted graph starting at the contracted vertex can be lifted to a path in the original graph starting at one of the contracted edge's endpoints.
-/
lemma lift_path_from_contraction_start (B : Set V) {x y : V} (e : G.Adj x y)
  (v' : V / e)
  (p' : (G / e).Walk ⟦x⟧ v')
  (hp'_path : p'.IsPath)
  (hv' : v' ∈ B / e)
  (h_ne : v' ≠ ⟦x⟧) :
  ∃ (u v : V) (p : G.Walk u v),
    (u = x ∨ u = y) ∧
    v ∈ B ∧
    p.IsPath ∧
    (↑p.support.toFinset : Set V) ⊆ contract_preimage (Y := (↑p'.support.toFinset : Set (V / e))) ∧
    p.support.toFinset ∩ {x, y} = {u} := by
      have h_lift_reversed : ∃ u v : V, ∃ p : G.Walk u v, u ∈ B ∧
        (v = x ∨ v = y) ∧
        p.IsPath ∧
        (↑p.support.toFinset : Set V) ⊆ contract_preimage (Y := (↑p'.reverse.support.toFinset : Set (V / e))) ∧
        p.support.toFinset ∩ {x, y} = {v} := by
          apply_rules [ lift_path_to_contraction_end ]
          · exact (Walk.isPath_reverse_iff p').mpr hp'_path
      obtain ⟨ u, v, p, hu, hv, hp, hp', hp'' ⟩ := h_lift_reversed; use v, u, p.reverse; aesop

/-
Two paths ending and starting at the endpoints of an edge can be joined into a single path if they are otherwise disjoint and avoid the edge's endpoints internally.
-/
lemma join_paths_through_edge {x y : V} (e : G.Adj x y)
  {u_start u_end v_start v_end : V}
  (p1 : G.Walk u_start u_end) (p2 : G.Walk v_start v_end)
  (hp1_path : p1.IsPath) (hp2_path : p2.IsPath)
  (hu_end : u_end = x ∨ u_end = y)
  (hv_start : v_start = x ∨ v_start = y)
  (hp1_end : p1.support.toFinset ∩ {x, y} = {u_end})
  (hp2_start : p2.support.toFinset ∩ {x, y} = {v_start})
  (h_disjoint : Disjoint (p1.support.toFinset \ {x, y}) (p2.support.toFinset \ {x, y})) :
  ∃ (q : G.Walk u_start v_end), q.IsPath ∧ q.support.toFinset ⊆ p1.support.toFinset ∪ p2.support.toFinset := by
    by_cases h_cases : u_end = v_start
    · refine' ⟨ p1.append ( h_cases ▸ p2 ), _, _ ⟩ <;> simp_all
      · have h_concat_path : (p1.append (h_cases ▸ p2)).IsPath := by
          have h_disjoint : Disjoint (p1.support.toFinset \ {v_start}) (p2.support.toFinset \ {v_start}) := by
            simp_all [ Finset.disjoint_left ]
            intro a ha ha' ha''; specialize h_disjoint ha; simp_all [ Finset.eq_singleton_iff_unique_mem ]
            grind +ring
          apply Walk.IsPath_append_of_support_inter_subset_one
          · assumption
          · aesop
          · intro v hv; simp_all [ Finset.disjoint_left ]
            grind
        exact h_concat_path
      · intro v hv; aesop
    · obtain ⟨h_edge, h_cases⟩ : G.Adj u_end v_start ∧ (u_end = x ∧ v_start = y ∨ u_end = y ∧ v_start = x) := by
        cases hu_end <;> cases hv_start <;> simp_all [ adj_comm ];
      use p1.append (Walk.cons h_edge p2)
      simp_all [ Finset.subset_iff, Walk.isPath_def ]
      simp_all [ Finset.disjoint_left ]
      simp_all [ Finset.ext_iff, Walk.support_append ]
      grind

/-
A path can be split at any vertex in its support into two paths that intersect only at that vertex.
-/
lemma Walk.split_at_vertex {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (hp : p.IsPath) (z : V) (hz : z ∈ p.support) :
  ∃ (p1 : G.Walk u z) (p2 : G.Walk z v),
    p1.IsPath ∧ p2.IsPath ∧
    p1.support.toFinset ∩ p2.support.toFinset = {z} ∧
    p1.support.toFinset ∪ p2.support.toFinset = p.support.toFinset := by
      simp +zetaDelta at *
      obtain ⟨p1, p2, hp1, hp2, hp_split⟩ : ∃ p1 : G.Walk u z, ∃ p2 : G.Walk z v, p = p1.append p2 ∧ p1.IsPath ∧ p2.IsPath := by
        exact ⟨ p.takeUntil z hz, p.dropUntil z hz, by rw [ Walk.take_spec ], by exact hp.takeUntil _, by exact hp.dropUntil _ ⟩
      refine' ⟨ p1, hp2, p2, hp_split, _, _ ⟩ <;> simp_all [ Finset.ext_iff ];
      intro a; constructor <;> intro ha ; simp_all [ Walk.isPath_def ] ;
      · induction' p1 with u' p1 ih generalizing a ; induction' p2 with v' p2 ih' ; aesop
        · aesop
        · simp_all [ Walk.support ]
          grind +ring
      · aesop

/-
If two sets in the contracted graph are disjoint away from the contracted vertex, their preimages in the original graph are disjoint away from the endpoints of the contracted edge.
-/
lemma contract_preimage_disjoint_away_from_endpoints {x y : V} (e : G.Adj x y)
  (s t : Set (V / e))
  (h_disj : Disjoint (s \ {⟦x⟧}) (t \ {⟦x⟧})) :
  Disjoint (contract_preimage s \ {x, y}) (contract_preimage t \ {x, y}) := by
    refine Set.disjoint_left.mpr ?_
    intro a ha hb
    rcases ha with ⟨ha_pre, ha_not⟩
    rcases hb with ⟨hb_pre, _⟩
    have hproj_ne : (⟦a⟧ : V/e) ≠ ⟦x⟧ := by
      intro hproj
      have hxy : a = x ∨ a = y := (contractEdgeProj_eq_vertex_iff (u := a)).1 hproj
      exact ha_not (by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hxy)
    have ha_s : ⟦a⟧ ∈ s := (mem_contract_preimage (Y := s) (v := a)).1 ha_pre
    have hb_t : ⟦a⟧ ∈ t := (mem_contract_preimage (Y := t) (v := a)).1 hb_pre
    have ha_s' : ⟦a⟧ ∈ s \ {⟦x⟧} :=
      ⟨ha_s, hproj_ne⟩
    have hb_t' : ⟦a⟧ ∈ t \ {⟦x⟧} :=
      ⟨hb_t, hproj_ne⟩
    exact (Set.disjoint_left.mp h_disj) ha_s' hb_t'

/-
If two paths in the contracted graph meet only at the contracted vertex, they can be lifted to paths in the original graph that are disjoint away from the contracted edge's endpoints.
-/
lemma lift_split_paths (A B : Set V) {x y : V} (e : G.Adj x y)
  (u' v' : V / e)
  (p1' : (G / e).Walk u' ⟦x⟧)
  (p2' : (G / e).Walk ⟦x⟧ v')
  (hp1'_path : p1'.IsPath)
  (hp2'_path : p2'.IsPath)
  (h_inter : p1'.support.toFinset ∩ p2'.support.toFinset = {⟦x⟧})
  (h_u_ne : u' ≠ ⟦x⟧)
  (h_v_ne : v' ≠ ⟦x⟧)
  (hu' : u' ∈ A / e)
  (hv' : v' ∈ B / e) :
  ∃ (u_start u_end : V) (p1 : G.Walk u_start u_end) (v_start v_end : V) (p2 : G.Walk v_start v_end),
    u_start ∈ A ∧ v_end ∈ B ∧
    (u_end = x ∨ u_end = y) ∧ (v_start = x ∨ v_start = y) ∧
    p1.IsPath ∧ p2.IsPath ∧
    (↑p1.support.toFinset : Set V) ⊆ contract_preimage (Y := (↑p1'.support.toFinset : Set (V / e))) ∧
    (↑p2.support.toFinset : Set V) ⊆ contract_preimage (Y := (↑p2'.support.toFinset : Set (V / e))) ∧
    p1.support.toFinset ∩ {x, y} = {u_end} ∧
    p2.support.toFinset ∩ {x, y} = {v_start} ∧
    Disjoint (p1.support.toFinset \ {x, y}) (p2.support.toFinset \ {x, y}) := by
  obtain ⟨u_start, u_end, p1, hu_start_A, hu_end_xy, hp1_path, hp1_sub, hp1_xy⟩ :=
    lift_path_to_contraction_end A e u' p1' hp1'_path hu' h_u_ne
  obtain ⟨v_start, v_end, p2, hv_start_xy, hv_end_B, hp2_path, hp2_sub, hp2_xy⟩ :=
    lift_path_from_contraction_start B e v' p2' hp2'_path hv' h_v_ne
  refine ⟨u_start, u_end, p1, v_start, v_end, p2, hu_start_A, hv_end_B, hu_end_xy, hv_start_xy,
    hp1_path, hp2_path, hp1_sub, hp2_sub, hp1_xy, hp2_xy, ?_⟩
  have h_disj_sets : Disjoint ((↑p1'.support.toFinset : Set _) \ {⟦x⟧})
      ((↑p2'.support.toFinset : Set (V/e)) \ {⟦x⟧}) := by
    rw [Set.disjoint_left]
    intro z ⟨hz1, hz_ne⟩ ⟨hz2, _⟩
    have : z ∈ p1'.support.toFinset ∩ p2'.support.toFinset :=
      Finset.mem_inter.mpr ⟨Finset.mem_coe.mp hz1, Finset.mem_coe.mp hz2⟩
    rw [h_inter] at this
    exact hz_ne (Finset.mem_singleton.mp this ▸ Set.mem_singleton _)
  have h_preimage_disj := contract_preimage_disjoint_away_from_endpoints e _ _ h_disj_sets
  rw [Finset.disjoint_left]
  intro z hz1 hz2
  simp only [Finset.mem_sdiff, List.mem_toFinset, Finset.mem_insert, Finset.mem_singleton] at hz1 hz2
  have hz1_set : z ∈ contract_preimage (Y := (↑p1'.support.toFinset : Set (V / e))) \ ({x, y} : Set V) :=
    ⟨hp1_sub (Finset.mem_coe.mpr (List.mem_toFinset.mpr hz1.1)), by simp [Set.mem_insert_iff]; tauto⟩
  have hz2_set : z ∈ contract_preimage (Y := (↑p2'.support.toFinset : Set (V / e))) \ ({x, y} : Set V) :=
    ⟨hp2_sub (Finset.mem_coe.mpr (List.mem_toFinset.mpr hz2.1)), by simp [Set.mem_insert_iff]; tauto⟩
  exact Set.disjoint_left.mp h_preimage_disj hz1_set hz2_set

/-
A path in the contracted graph passing through the contracted vertex can be lifted to a path in the original graph.
-/
lemma lift_path_through_contraction_internal (A B : Set V) {x y : V} (e : G.Adj x y)
  (u' v' : V / e)
  (p' : (G / e).Walk u' v')
  (hp'_path : p'.IsPath)
  (h_ve_mem : ⟦x⟧ ∈ p'.support)
  (h_u_ne : u' ≠ ⟦x⟧)
  (h_v_ne : v' ≠ ⟦x⟧)
  (hu' : u' ∈ A / e)
  (hv' : v' ∈ B / e) :
  ∃ (u v : V) (p : G.Walk u v),
    u ∈ A ∧ v ∈ B ∧
    p.IsPath ∧
    (↑p.support.toFinset : Set V) ⊆ contract_preimage (Y := (↑p'.support.toFinset : Set (V / e))) := by
      have h_split : ∃ (p1' : (G / e).Walk u' ⟦x⟧)
        (p2' : (G / e).Walk ⟦x⟧ v'),
        p1'.IsPath ∧
        p2'.IsPath ∧
        p1'.support.toFinset ∩ p2'.support.toFinset = {⟦x⟧} ∧
        p1'.support.toFinset ∪ p2'.support.toFinset = p'.support.toFinset := by
          have := Walk.split_at_vertex p' hp'_path _ h_ve_mem
          obtain ⟨p1, p2, hp1, hp2, h1, h2⟩ := this
          refine ⟨p1, p2, hp1, hp2, ?_, ?_⟩
          convert h1 ; convert h2
      obtain ⟨p1', p2', hp1'_path, hp2'_path, h_inter, h_union⟩ := h_split
      obtain ⟨u_start, u_end, p1, v_start, v_end, p2, hp1, hp2, h_disjoint⟩ :=
        lift_split_paths A B e u' v' p1' p2' hp1'_path hp2'_path h_inter h_u_ne h_v_ne hu' hv'
      obtain ⟨q, hq⟩ : ∃ q : G.Walk u_start v_end, q.IsPath ∧ q.support.toFinset ⊆ p1.support.toFinset ∪ p2.support.toFinset := by
        apply join_paths_through_edge e p1 p2 h_disjoint.2.2.1 h_disjoint.2.2.2.1 h_disjoint.1 h_disjoint.2.1 h_disjoint.2.2.2.2.2.2.1 h_disjoint.2.2.2.2.2.2.2.1 h_disjoint.2.2.2.2.2.2.2.2
      refine ⟨u_start, v_end, q, hp1, hp2, hq.1, ?_⟩
      intro z hz
      simp only [Finset.mem_coe, List.mem_toFinset] at hz
      have hz_fin := hq.2 (List.mem_toFinset.mpr hz)
      simp only [contract_preimage, Set.mem_setOf_eq, Finset.mem_coe]
      rcases Finset.mem_union.mp hz_fin with h1 | h2
      · have := h_disjoint.2.2.2.2.1 (Finset.mem_coe.mpr h1)
        simp only [contract_preimage, Set.mem_setOf_eq, Finset.mem_coe] at this
        exact h_union ▸ Finset.mem_union.mpr (Or.inl this)
      · have := h_disjoint.2.2.2.2.2.1 (Finset.mem_coe.mpr h2)
        simp only [contract_preimage, Set.mem_setOf_eq, Finset.mem_coe] at this
        exact h_union ▸ Finset.mem_union.mpr (Or.inr this)

/-
A path in the contracted graph that avoids the contracted vertex can be lifted to a path in the original graph that avoids the endpoints of the contracted edge.
-/
lemma exists_lifted_ABPath_avoiding (A B : Set V) {x y : V} (e : G.Adj x y)
  (p' : (G / e).ABPath (A / e) (B / e))
  (hp'_avoid : ⟦x⟧ ∉ p'.p.1.support) :
  ∃ p : G.ABPath A B, ⟦p.u.1⟧ = p'.u.1 ∧ ⟦p.v.1⟧ = p'.v.1 ∧
    p.p.1.support.toFinset.image (⟦·⟧) ⊆ p'.p.1.support.toFinset ∧
    x ∉ p.p.1.support ∧ y ∉ p.p.1.support := by
      obtain ⟨u, v, q, hu, hv, hq_isPath, hq_support⟩ : ∃ u v : V, ∃ q : G.Walk u v, (u ∈ A ∧ v ∈ B ∧
      ⟦u⟧ = p'.u.1 ∧ ⟦v⟧ = p'.v.1 ∧ q.IsPath ∧ (q.support.toFinset.image (⟦·⟧)) ⊆ p'.p.1.support.toFinset ∧ x ∉ q.support ∧ y ∉ q.support) := by
        rcases p' with ⟨ u', v', p', hp'_path ⟩
        obtain ⟨ u, v, q, hq ⟩ := lift_path_avoiding_contraction_AB A B p' hp'_avoid u'.2 v'.2
        exact ⟨ u, v, q, hq ⟩
      refine ⟨⟨⟨u, hu⟩, ⟨v, hv⟩, q, hq_support.2.1⟩, ?_, ?_, ?_, ?_⟩ <;> aesop

/-
The contracted vertex is in the lifted set of A if and only if x or y is in A.
-/
lemma mem_liftSet_contraction_vertex_iff (A : Set V) {x y : V} (e : G.Adj x y) :
  ⟦x⟧ ∈ A / e ↔ x ∈ A ∨ y ∈ A := by
    constructor <;> intro h;
    · simp at h
      cases' h with z hz
      rw [Quotient.eq, contractSetoid] at hz
      aesop
    · simp
      cases' h with hx hy
      · exact ⟨ x, hx, rfl ⟩
      · exact ⟨ y, hy, by { simp } ⟩

/-
If a path starts at one of the endpoints of the contracted edge, and the contracted vertex is in the lifted set of A, we can adjust the path to start in A.
-/
lemma adjust_path_start_to_A (A : Set V) {x y : V} (e : G.Adj x y)
  (u v : V) (p : G.Walk u v) (hp_path : p.IsPath)
  (hu : u = x ∨ u = y)
  (hp_support : p.support.toFinset ∩ {x, y} = {u})
  (h_liftA : ⟦x⟧ ∈ A / e) :
  ∃ (u' : V) (p' : G.Walk u' v),
    u' ∈ A ∧
    p'.IsPath ∧
    (p'.support.toFinset.image (⟦·⟧) : Finset (V / e))
      ⊆ p.support.toFinset.image (⟦·⟧) := by
      by_cases hx : x ∈ A
      · rcases hu with ( rfl | rfl )
        · exact ⟨ u, p, hx, hp_path, Finset.Subset.refl _ ⟩
        · refine ⟨ x, Walk.cons e p, hx, ?_, ?_ ⟩ <;> simp_all [ Walk.cons_isPath_iff ];
          · intro hxmem
            have hx_in : x ∈ p.support.toFinset ∩ {x, u} := by
              exact Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hxmem, by simp⟩
            have hx_eq_u : x = u := by
              have : x ∈ ({u} : Finset V) := by simpa [hp_support] using hx_in
              simpa using this
            exact e.ne hx_eq_u
          · simp_all [ Finset.Subset.antisymm_iff, Finset.subset_iff ]
            use u
            exact ⟨ p.start_mem_support, by exact Quotient.sound ( by tauto ) ⟩
      · by_cases hy : y ∈ A
        · cases hu <;> simp_all [ Finset.subset_iff ];
          · refine ⟨ y, hy, ?_, ?_, ?_ ⟩
            exact Walk.cons e.symm ( p.copy ( by simp [ * ] ) rfl )
            · replace hp_support := Finset.ext_iff.mp hp_support y; aesop
            · simp [ Walk.support_cons ]
              simp [ Finset.eq_singleton_iff_unique_mem] at hp_support ⊢
              exact ⟨ ⟨ x, hp_support.1, by simp_all ⟩,
              fun a ha => ⟨ a, ha, by tauto ⟩ ⟩
          · grind
        · simp_all
          obtain ⟨ u', hu', hu'' ⟩ := h_liftA
          rw [contractEdgeProj_eq_vertex_iff] at hu''
          cases hu'' <;> simp_all [ Finset.ext_iff ]

lemma adjust_path_end_to_B (B : Set V) {x y : V} (e : G.Adj x y)
  (u v : V) (p : G.Walk u v) (hp_path : p.IsPath)
  (hv : v = x ∨ v = y)
  (hp_support : p.support.toFinset ∩ {x, y} = {v})
  (h_liftB : ⟦x⟧ ∈ B / e) :
  ∃ (v' : V) (p' : G.Walk u v'),
    v' ∈ B ∧
    p'.IsPath ∧
    (p'.support.toFinset.image (⟦·⟧) : Finset (V / e))
      ⊆ p.support.toFinset.image (⟦·⟧) := by
      rcases hv with ( rfl | rfl )
      · by_cases hy : y ∈ B
        · refine ⟨ y, ?_, hy, ?_, ?_ ⟩
          exact p.append ( Walk.cons e Walk.nil )
          · simp_all [ Finset.ext_iff, Walk.isPath_def ]
            rw [ Walk.support_append ]
            simp_all [ List.nodup_append ]
            intro a ha ha'
            have hyv : y = v := hp_support a ha ha'
            exact e.ne hyv.symm
          · simp [ Finset.subset_iff, Walk.support_append ]
            use v
            simp_all [ Finset.eq_singleton_iff_unique_mem ]
            exact Quotient.sound ( by tauto )
        · have hvB : v ∈ B := by
            exact Or.resolve_right
              ((mem_liftSet_contraction_vertex_iff (e := e) B).1 h_liftB) hy
          exact ⟨ v, p, hvB, hp_path, Finset.Subset.refl _ ⟩
      · by_cases hv : v ∈ B
        · exact ⟨ v, p, hv, hp_path, Finset.Subset.refl _ ⟩
        · have hx : x ∈ B := by
            contrapose! h_liftB; simp_all
            intro w hw
            rw [ Quotient.eq, contractSetoid ]
            grind
          refine ⟨ x, p.append ( Walk.cons e.symm Walk.nil ), hx, ?_, ?_ ⟩
          · refine Walk.IsPath_append_of_support_inter_subset_one _ _ hp_path ?_ ?_
            · aesop
            · rw [ Finset.eq_singleton_iff_unique_mem ] at hp_support ; aesop
          · simp_all [ Finset.subset_iff ]
            rintro a ( ha | rfl | rfl )
            · exact ⟨ a, ha, by rfl ⟩
            · exact ⟨ a, by cases p <;> aesop ⟩;
            · exact ⟨v, by simp, Quotient.sound (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩

/-
Helper lemma: A path starting at the contracted vertex can be lifted to an A-B path if the contracted vertex is in the lifted set of A.
-/
lemma lift_path_start_eq_vertex (A B : Set V) {x y : V} (e : G.Adj x y)
  (v' : V / e)
  (p' : (G / e).Walk ⟦x⟧ v')
  (hp'_path : p'.IsPath)
  (hv' : v' ∈ B / e)
  (h_end_ne : v' ≠ ⟦x⟧)
  (h_liftA : ⟦x⟧ ∈ A / e) :
  ∃ p : G.ABPath A B,
    p.p.1.support.toFinset.image (⟦·⟧) ⊆ p'.support.toFinset := by
      obtain ⟨u, v, q, hu_xy, hvB, hq_path, hq_pre, hq_xy⟩ :=
        lift_path_from_contraction_start B e v' p' hp'_path hv' h_end_ne
      obtain ⟨u', q', hu'A, hq'_path, hq'_support⟩ :=
        adjust_path_start_to_A A e u v q hq_path hu_xy hq_xy h_liftA
      refine ⟨⟨⟨u', hu'A⟩, ⟨v, hvB⟩, q', hq'_path⟩, ?_⟩
      refine hq'_support.trans ?_
      intro a ha
      rcases Finset.mem_image.mp ha with ⟨w, hw, rfl⟩
      have hw' : w ∈ contract_preimage (Y := (↑p'.support.toFinset : Set (V / e))) := hq_pre (Finset.mem_coe.mpr hw)
      exact (mem_contract_preimage (Y := (↑p'.support.toFinset : Set (V / e))) (v := w)).1 hw'

lemma lift_path_end_eq_vertex (A B : Set V) {x y : V} (e : G.Adj x y)
  (u' : V / e)
  (p' : (G / e).Walk u' ⟦x⟧)
  (hp'_path : p'.IsPath)
  (hu' : u' ∈ A / e)
  (h_start_ne : u' ≠ ⟦x⟧)
  (h_liftB : ⟦x⟧ ∈ B / e) :
  ∃ p : G.ABPath A B,
    p.p.1.support.toFinset.image (⟦·⟧) ⊆ p'.support.toFinset := by
      obtain ⟨ u, v, p, hu, hv, hp, hp', hp'' ⟩ :=
        lift_path_to_contraction_end A e u' p' hp'_path hu' h_start_ne
      obtain ⟨ v', q, hv', hq, hq' ⟩ :=
        adjust_path_end_to_B B e u v p hp hv hp'' h_liftB
      have h_final : Finset.image (⟦·⟧) q.support.toFinset ⊆ p'.support.toFinset := by
        refine hq'.trans ?_
        rw [ Finset.image_subset_iff ]
        intro z hz
        have hz' : z ∈ contract_preimage (Y := (↑p'.support.toFinset : Set (V / e))) := hp' (Finset.mem_coe.mpr hz)
        exact (mem_contract_preimage (Y := (↑p'.support.toFinset : Set (V / e))) (v := z)).1 hz'
      exact ⟨ ⟨ ⟨ u, hu ⟩, ⟨ v', hv' ⟩, q, hq ⟩, h_final ⟩

/-
Helper lemma: A nil path at the contracted vertex can be lifted to an A-B path if the contracted vertex is in the lifted sets of A and B.
-/
lemma lift_path_nil_eq_vertex (A B : Set V) {x y : V} (e : G.Adj x y)
  (p' : (G / e).Walk ⟦x⟧ ⟦x⟧)
  (hp'_path : p'.IsPath)
  (h_liftA : ⟦x⟧ ∈ A / e)
  (h_liftB : ⟦x⟧ ∈ B / e) :
  ∃ p : G.ABPath A B,
    p.p.1.support.toFinset.image (⟦·⟧) ⊆ p'.support.toFinset := by
      simp at h_liftA h_liftB
      obtain ⟨x_1, hx_1_A, hx_1⟩ := h_liftA
      obtain ⟨x_2, hx_2_B, hx_2⟩ := h_liftB
      have hx_1_eq : x_1 = x ∨ x_1 = y := by
        contrapose! hx_1; simp_all [ Quotient.eq ]
        unfold contractSetoid; aesop
      have hx_2_eq : x_2 = x ∨ x_2 = y := by
        rw [ Quotient.eq ] at hx_2
        cases hx_2 <;> aesop;
      cases hx_1_eq <;> cases hx_2_eq <;> simp_all
      · refine ⟨ ?_, ?_ ⟩
        constructor
        rotate_left
        exact ⟨ x, hx_1_A ⟩
        exact ⟨ x, hx_2_B ⟩
        simp [Finset.image]
        swap
        exact Path.nil
        all_goals simp [*]
      · refine ⟨⟨⟨x, hx_1_A⟩, ⟨y, hx_2_B⟩, Walk.cons e Walk.nil,
            by simp [Walk.cons_isPath_iff, e.ne]⟩, ?_⟩
        simp
      · refine ⟨ ?_, ?_ ⟩
        constructor
        rotate_left
        exact ⟨ y, hx_1_A ⟩
        exact ⟨ x, hx_2_B ⟩
        swap
        constructor
        swap
        exact Walk.cons e.symm Walk.nil
        simp
        exact e.ne.symm
        simp [Finset.image]
        by_cases h : y = x <;> simp_all
      · refine ⟨ ?_, ?_ ⟩
        constructor
        rotate_left
        exact ⟨ y, hx_1_A ⟩
        exact ⟨ y, hx_2_B ⟩
        swap
        exact Path.nil
        all_goals simp_all

lemma exists_lifted_ABPath_through (A B : Set V) {x y : V} (e : G.Adj x y)
  (p' : (G / e).ABPath (A / e) (B / e))
  (hp'_mem : ⟦x⟧ ∈ p'.p.1.support) :
  ∃ p : G.ABPath A B,
    p.p.1.support.toFinset.image (⟦·⟧) ⊆ p'.p.1.support.toFinset := by
      by_cases hu' : p'.u = (⟦x⟧ : V/e)
      · by_cases hv' : p'.v = (⟦x⟧ : V/e)
        · have h_lift_nil : ⟦x⟧ ∈ A / e ∧ ⟦x⟧ ∈ B / e := by
            grind
          obtain ⟨ p, hp ⟩ := lift_path_nil_eq_vertex A B e ( Walk.nil ) ( by simp ) h_lift_nil.1 h_lift_nil.2
          exact ⟨ p, hp.trans ( by simp [ hp'_mem ] ) ⟩
        · cases p'
          have := lift_path_start_eq_vertex A B e
          grind
      · cases' p' with u' hv' p
        rcases hv' with ⟨ v', hv' ⟩
        by_cases hv' : v' = (⟦x⟧ : V/e)
        · convert lift_path_end_eq_vertex A B e _ _ _ _ _ _
          rotate_left
          any_goals tauto
          convert p.1
          all_goals norm_num [ hv' ]
          · aesop
          · aesop
        · rename_i hp
          obtain ⟨ u, v, lifted_p, hp₁, hp₂, hp₃, hp₄ ⟩ := lift_path_through_contraction_internal A B e u' v' p p.2 hp'_mem hu' hv' u'.2 ‹_›
          refine ⟨ ⟨ ⟨u, hp₁⟩, ⟨v, hp₂⟩, lifted_p, hp₃ ⟩, ?_ ⟩
          intro a ha; rcases Finset.mem_image.mp ha with ⟨w, hw, rfl⟩
          have := hp₄ (Finset.mem_coe.mpr hw)
          exact (mem_contract_preimage (Y := (↑p.1.support.toFinset : Set (V / e))) (v := w)).1 this

lemma exists_disjoint_paths_lift (P' : (G / e).Joiner (A / e) (B / e)) :
    ∃ P : G.Joiner A B, P.1.encard = P'.1.encard := by
  have h_lift : ∀ p' : (G / e).ABPath (A / e) (B / e),
      ∃ p : G.ABPath A B, p.p.1.support.toFinset.image (⟦·⟧) ⊆ p'.p.1.support.toFinset := by
    intro p'
    by_cases hp'_avoid : ⟦x⟧ ∉ p'.p.1.support
    · rcases exists_lifted_ABPath_avoiding A B e p' hp'_avoid with ⟨p, hp⟩
      exact ⟨p, hp.2.2.1⟩
    · rcases exists_lifted_ABPath_through A B e p' (by aesop) with ⟨p, hp⟩
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
lemma Menger_case2_exists_X (k : ℕ∞) (h_min : G.mincut A B = k) (h_contract_min : (G / e).mincut (A / e) (B / e) < k) :
    ∃ X : G.Separator A B, X.1.encard = k ∧ x ∈ X.1 ∧ y ∈ X.1 := by
  obtain ⟨⟨Y, hY_sep⟩, hY_card⟩ := exists_separator_of_mincut_lt (G := G / e) (A := A / e) (B := B / e) h_contract_min
  have h_ve : ⟦x⟧ ∈ Y := vertex_mem_contract_separator ⟨Y, hY_sep⟩ (h_min ▸ hY_card)
  have h_sep : G.Separates A B (contract_preimage Y) := contract_preimage_separates ⟨Y, hY_sep⟩
  have h_lift_card : (contract_preimage Y).encard = Y.encard + 1 := encard_preimage_contractEdge h_ve
  have h_ge_k : (contract_preimage Y).encard ≥ k := by
    calc k = G.mincut A B := h_min.symm
      _ ≤ (contract_preimage Y).encard := mincut_le_encard_of_separates h_sep
  have h_le_k : (contract_preimage Y).encard ≤ k := by
    rw [h_lift_card]
    have : Y.encard ≠ ⊤ := ne_top_of_lt (lt_of_lt_of_le hY_card le_top)
    exact (ENat.add_one_le_iff this).mpr hY_card
  refine ⟨⟨_, h_sep⟩, le_antisymm h_le_k h_ge_k, ?_, ?_⟩
  · exact (mem_contract_preimage (v := x)).2 h_ve
  · exact (mem_contract_preimage (v := y)).2 (contract_same (e := e) ▸ h_ve)

/-
If X separates A and B in G and contains x and y, then any separator of X and B in G-xy is also a separator of A and B in G.
-/
lemma separator_in_G_of_separator_in_G_delete_edge_right (X : G.Separator A B) (hx : x ∈ X.1) (hy : y ∈ X.1)
    (S : (G - e).Separator X.1 B) : G.Separates A B S.1 := by
  exact (separates_of_separates_delete (A := B) (B := A) (e := e) X.swap S.swap hx hy).swap

lemma min_sep_delete_ge_k_left (X : G.Separator A B) (hx : x ∈ X.1) (hy : y ∈ X.1) :
    G.mincut A B ≤ (G - e).mincut A X.1 := by
  apply le_iInf
  intro S
  exact mincut_le_encard ⟨S.1, separates_of_separates_delete A B e X S hx hy⟩

/-
If X separates A and B in G and contains x and y, then the minimum separator size of X and B in G-xy is at least k.
-/
lemma min_sep_delete_ge_k_right (X : G.Separator A B) (hx : x ∈ X.1) (hy : y ∈ X.1) :
    (G - e).mincut X.1 B ≥ G.mincut A B := by
  rw [ge_iff_le, mincut]
  apply le_iInf
  intro S
  exact mincut_le_encard ⟨S.1, separator_in_G_of_separator_in_G_delete_edge_right X hx hy S⟩

/-
If G' is a subgraph of G, then any set of disjoint paths in G' can be lifted to a set of disjoint paths in G with the same size.
-/
lemma lift_disjoint_paths_le (G G' : SimpleGraph V) (h : G' ≤ G) (A B : Set V)
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
      simpa [Walk.support_mapLe_eq_support] using h_support_eq_map
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
    simp only [ABPath.support, f, Walk.support_mapLe_eq_support]
    exact hdisj0
  · show (f '' P).encard = P.encard
    exact hf_inj.encard_image

def abPath_to_fromEdgeSet (p : G.ABPath A B) (E : Set (Sym2 V)) (hE : p.p.1.edgeSet ⊆ E) :
    (fromEdgeSet E).ABPath A B := by
  let hp : ∀ e, e ∈ p.p.1.edges → e ∈ (fromEdgeSet E).edgeSet := by
    intro e he
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    refine ⟨hE he, ?_⟩
    have heG : e ∈ G.edgeSet := p.p.1.edges_subset_edgeSet he
    simpa [Set.mem_compl_iff, Sym2.mem_diagSet] using (G.not_isDiag_of_mem_edgeSet heG)
  exact ⟨p.u, p.v, p.p.1.transfer (fromEdgeSet E) hp, p.p.2.transfer hp⟩

@[simp] lemma support_abPath_to_fromEdgeSet (A B : Set V)
    (p : G.ABPath A B) (E : Set (Sym2 V)) (hE : p.p.1.edgeSet ⊆ E) :
    (abPath_to_fromEdgeSet p E hE).support = p.support := by
  simp [abPath_to_fromEdgeSet, ABPath.support, Walk.support_transfer]

lemma ABPath.edgeSet_finite (p : G.ABPath A B) : p.p.1.edgeSet.Finite := by
  exact Set.Finite.ofFinset (p.p.1.edges.toFinset) (by simp [SimpleGraph.Walk.edgeSet])

lemma ABPath.edgeSet_subset_graphEdgeSet (p : G.ABPath A B) : p.p.1.edgeSet ⊆ G.edgeSet := by
  intro e he
  have he_edges : e ∈ p.p.1.edges := by simpa [SimpleGraph.Walk.edgeSet] using he
  exact p.p.1.edges_subset_edgeSet he_edges

lemma exists_abPath_avoiding_of_not_separates (S : Set V) (hS : ¬ G.Separates A B S) :
    ∃ q : G.ABPath A B, ∀ x ∈ q.support, x ∉ S := by
  simp [SimpleGraph.Separates] at hS
  rcases hS with ⟨u, hu, v, hv, w, hw⟩
  refine ⟨⟨⟨u, hu⟩, ⟨v, hv⟩, w.toPath⟩, ?_⟩
  intro x hx hxS
  exact hw x (Walk.support_toPath_subset w hx) hxS

lemma restrict_joiner_to_fromEdgeSet (P : G.Joiner A B) (E : Set (Sym2 V))
    (h_edges : ∀ p ∈ P.1, p.p.1.edgeSet ⊆ E) :
    ∃ PH : (fromEdgeSet E).Joiner A B, PH.1.encard = P.1.encard := by
  let H : SimpleGraph V := fromEdgeSet E
  let f : P.1 → H.ABPath A B := fun p => by
    simpa [H] using abPath_to_fromEdgeSet p.1 E (h_edges p.1 p.2)
  have h_disj : disjointPaths (Set.range f) := by
    rintro p ⟨p', rfl⟩ q ⟨q', rfl⟩ hpq
    have hpq' : p' ≠ q' := fun h => hpq (by simp [h])
    have hdisj : Disjoint p'.1.support q'.1.support := by
      exact P.2 p'.2 q'.2 (fun h => hpq' (Subtype.ext h))
    show Disjoint (f p').support (f q').support
    rw [Set.disjoint_left]
    intro v hv hv'
    have hvp : v ∈ p'.1.support := by
      simpa [f, H] using hv
    have hvq : v ∈ q'.1.support := by
      simpa [f, H] using hv'
    exact Set.disjoint_left.mp hdisj hvp hvq
  have h_inj : Function.Injective f := by
    intro p q hpq
    by_contra hneq
    have hdisj : Disjoint p.1.support q.1.support := by
      exact P.2 p.2 q.2 (fun h => hneq (Subtype.ext h))
    have hp_mem : (p.1.u : V) ∈ p.1.p.1.support := p.1.p.1.start_mem_support
    have hp_mem_f : (p.1.u : V) ∈ (f p).support := by simp [f, H, hp_mem]
    have hq_mem_f : (p.1.u : V) ∈ (f q).support := by
      exact hpq ▸ hp_mem_f
    have hq_mem : (p.1.u : V) ∈ q.1.p.1.support := by simpa [f, H] using hq_mem_f
    exact (Set.disjoint_left.mp hdisj hp_mem) hq_mem
  have h_card : (Set.range f).encard = P.1.encard := by
    rw [show Set.range f = f '' Set.univ from Set.image_univ.symm, h_inj.injOn.encard_image]
    simp
  exact ⟨⟨Set.range f, h_disj⟩, h_card⟩

/-
Helper: if k ≤ ⨆ f and k ≠ ⊤, there exists i with k ≤ f i.
-/
private lemma exists_le_of_le_iSup {ι : Type*} [Nonempty ι] (f : ι → ℕ∞) {k : ℕ∞} (hk : k ≠ ⊤)
    (h : k ≤ ⨆ i, f i) : ∃ i, k ≤ f i := by
  obtain (h' | h') := eq_top_or_lt_top (⨆ i, f i)
  · grind [iSup_eq_top, lt_top_iff_ne_top.2 hk]
  · grind [ENat.exists_eq_iSup_of_lt_top h']

lemma exists_joiner_of_le_maxflow_of_subgraph {G' : SimpleGraph V} (k : ℕ∞) (hk : k ≠ ⊤)
    (hsub : G' ≤ G) (hmax : k ≤ G'.maxflow A B) : ∃ P : G.Joiner A B, P.1.encard = k := by
  obtain ⟨P', hP'⟩ := exists_le_of_le_iSup _ hk hmax
  obtain ⟨t, ht_sub, ht_card⟩ := Set.exists_subset_encard_eq hP'
  have ht_disj : disjointPaths t := fun p hp q hq hpq => P'.2 (ht_sub hp) (ht_sub hq) hpq
  obtain ⟨Q, hQ⟩ := lift_disjoint_paths_le G G' hsub A B ⟨t, ht_disj⟩
  exact ⟨Q, hQ.trans ht_card⟩

/-
If there exists a separator X of size k containing x and y, then G has k disjoint A-B paths.
-/
lemma Menger_case2_imp_paths (k : ℕ∞) (hk : k ≠ ⊤) (h_min : G.mincut A B = k) (X : G.Separator A B) (hX_card : X.1.encard = k) (hx : x ∈ X.1)
    (hy : y ∈ X.1) (IH_delete : ∀ (A' B' : Set V), (A' ∩ B').Finite → (G - e).mincut A' B' ≤ (G - e).maxflow A' B') :
    k ≤ G.maxflow A B := by
  have hX_fin : X.1.Finite := Set.encard_ne_top_iff.mp (hX_card ▸ hk)
  have h_del_A : k ≤ (G - e).maxflow A X.1 :=
    le_trans (h_min ▸ min_sep_delete_ge_k_left X hx hy)
      (IH_delete A X.1 (hX_fin.inter_of_right _))
  have h_del_B : k ≤ (G - e).maxflow X.1 B :=
    le_trans (h_min ▸ min_sep_delete_ge_k_right X hx hy)
      (IH_delete X.1 B (hX_fin.inter_of_left _))
  obtain ⟨P_A, hP_A_card⟩ := exists_joiner_of_le_maxflow_of_subgraph (G' := G - e) k hk deleteEdge_le h_del_A
  obtain ⟨P_B, hP_B_card⟩ := exists_joiner_of_le_maxflow_of_subgraph (G' := G - e) k hk deleteEdge_le h_del_B
  obtain ⟨P, hP_card⟩ := disjoint_paths_join A B X k hX_fin hX_card P_A hP_A_card P_B hP_B_card
  exact hP_card ▸ encard_le_maxflow_of_joiner P

/-
Inductive step for Menger's theorem.
-/
lemma Menger_inductive_step (hk : G.mincut A B ≠ ⊤)
    (IH_contract : (G / e).mincut (A / e) (B / e) ≤ (G / e).maxflow (A / e) (B / e))
    (IH_delete : ∀ (A' B' : Set V), (A' ∩ B').Finite → (G - e).mincut A' B' ≤ (G - e).maxflow A' B') :
    G.mincut A B ≤ G.maxflow A B := by
  by_cases h : (G / e).mincut (A / e) (B / e) < G.mincut A B
  · obtain ⟨⟨X, hX_sep⟩, hX_card, hx_mem, hy_mem⟩ := Menger_case2_exists_X (G.mincut A B) rfl h
    exact Menger_case2_imp_paths (G.mincut A B) hk rfl ⟨X, hX_sep⟩ hX_card hx_mem hy_mem IH_delete
  · push_neg at h
    obtain ⟨P', hP'⟩ := exists_le_of_le_iSup _ hk (le_trans h IH_contract)
    obtain ⟨P, hP⟩ := exists_disjoint_paths_lift (e := e) P'
    calc G.mincut A B ≤ P'.1.encard := hP'
      _ = P.1.encard := hP.symm
      _ ≤ G.maxflow A B := encard_le_maxflow_of_joiner P

/-
Auxiliary lemma for Menger's theorem: The theorem holds for any graph with n edges, proved by strong induction on n.
-/
theorem Menger_strong_aux (hAB : (A ∩ B).Finite) : G.edgeSet.encard = ↑n → G.mincut A B ≤ G.maxflow A B := by
  induction' n using Nat.strongRecOn with n ih generalizing V
  intro h_card
  by_cases h_empty : G.edgeSet = ∅
  · exact Menger_strong_base h_empty
  · obtain ⟨x, y, e⟩ : ∃ x y : V, G.Adj x y := by
      obtain ⟨e, he⟩ := Set.nonempty_iff_ne_empty.mpr h_empty
      induction e using Sym2.ind with
      | _ a b => exact ⟨a, b, he⟩
    have hfin : G.edgeSet.Finite := Set.finite_of_encard_eq_coe h_card
    have h_contract_lt : (G / e).edgeSet.encard < n := (contract_encard_lt hfin).trans_eq h_card
    have h_delete_lt : (G - e).edgeSet.encard < ↑n := (deleteEdge_edgeSet_encard_lt hfin).trans_eq h_card
    obtain ⟨mc, hmc⟩ := (Set.finite_of_encard_le_coe h_contract_lt.le).exists_encard_eq_coe
    obtain ⟨md, hmd⟩ := (Set.finite_of_encard_le_coe h_delete_lt.le).exists_encard_eq_coe
    have hk : G.mincut A B ≠ ⊤ :=
      ne_top_of_le_ne_top (WithTop.add_ne_top.mpr
        ⟨Set.encard_ne_top_iff.mpr hAB, h_card ▸ WithTop.coe_ne_top⟩) mincut_le_inter_add_edgeSet
    have hAB_contract : ((A / e) ∩ (B / e)).Finite := finite_inter_contract_image (e := e) hAB
    exact Menger_inductive_step hk
      (ih _ (by rw [hmc] at h_contract_lt; exact WithTop.coe_lt_coe.mp h_contract_lt)
        hAB_contract hmc)
      (fun A' B' hAB' => ih _ (by rw [hmd] at h_delete_lt; exact WithTop.coe_lt_coe.mp h_delete_lt)
        hAB' hmd)

theorem Menger_infinite (hAB : (A ∩ B).Infinite) : G.mincut A B = G.maxflow A B := by
  have h_top : (A ∩ B).encard = ⊤ := Set.encard_eq_top hAB
  have hmin : G.mincut A B = ⊤ := top_le_iff.mp (h_top ▸ inter_le_mincut)
  have hmax : G.maxflow A B = ⊤ := top_le_iff.mp (h_top ▸ inter_le_maxflow)
  rw [hmin, hmax]

theorem Menger_strong (hG : G.edgeSet.Finite) :
    G.mincut A B = G.maxflow A B := by
  by_cases hAB : (A ∩ B).Finite
  · exact le_antisymm (Menger_strong_aux hAB hG.encard_eq_coe) maxflow_le_mincut
  · exact Menger_infinite hAB

theorem Menger_finite [Fintype V] : G.mincut A B = G.maxflow A B :=
  Menger_strong (Set.toFinite _)

/-
Menger's theorem: there exist a separator set `S` between `A` and `B` and a set
`P`of disjoint A-B paths such that `S` is formed of exactly one vertez vrom each
path in `P`.

This version would actually be true without the `[Fintype S]` assumption.
-/
theorem Menger_equiv [Fintype V] : ∃ P : G.Joiner A B, ∃ S : G.Separator A B, ∃ φ : P.1 ≃ S.1,
    ∀ p : P.1, (φ p).1 ∈ p.1.p.1.support := by
  have h_maxflow_lt : G.maxflow A B < ⊤ :=
    lt_of_le_of_lt (iSup_le (fun P => P.le_A)) (Set.toFinite A).encard_lt_top
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
      (Set.encard_ne_top_iff.mpr (Set.toFinite A)) (P.le_A))
  haveI : Fintype P.1 := hP_fin.fintype
  haveI : Fintype S.1 := (Set.toFinite S.1).fintype
  have h_card_eq : Fintype.card P.1 = Fintype.card S.1 := by
    have h_eq : P.1.encard = S.1.encard := by
      calc P.1.encard = G.maxflow A B := hP
        _ = G.mincut A B := Menger_finite.symm
        _ = S.1.encard := hS.symm
    rw [Set.encard_eq_coe_toFinset_card, Set.toFinset_card] at h_eq
    rw [Set.encard_eq_coe_toFinset_card, Set.toFinset_card] at h_eq
    exact WithTop.coe_injective h_eq
  exact ⟨.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf_inj, h_card_eq⟩), hf⟩

private lemma encard_range_choice_eq (P : G.Joiner A B) (σ : ∀ p : P.1, {x : V // x ∈ p.1.support}) :
    (Set.range (fun p : P.1 => (σ p).1)).encard = P.1.encard := by
  have h_inj : Function.Injective (fun p : P.1 => (σ p).1) := by
    intro p q (hpq : (σ p).1 = (σ q).1)
    by_contra hpq'
    have hdisj : Disjoint p.1.support q.1.support := by
      exact P.2 p.2 q.2 (fun h => hpq' (Subtype.ext h))
    have hqmem : (σ p).1 ∈ q.1.support := by simp [hpq]
    exact Set.disjoint_left.mp hdisj (σ p).2 hqmem
  simpa [Set.image_univ] using (h_inj.injOn.encard_image (s := Set.univ))

private lemma exists_abPath_avoiding_of_encard_eq (P : G.Joiner A B) (h : P.1.encard < G.mincut A B)
    (S : Set V) (hS : S.encard = P.1.encard) :
    ∃ q : G.ABPath A B, ∀ x ∈ q.support, x ∉ S := by
  apply exists_abPath_avoiding_of_not_separates (S := S)
  contrapose! h
  simpa [hS] using mincut_le_encard_of_separates (X := S) h

private abbrev ChoicePoints (P : G.Joiner A B) := ∀ p : P.1, {x : V // x ∈ p.1.support}

private def choiceSet {P : G.Joiner A B} (σ : ChoicePoints P) : Set V :=
  Set.range (fun p : P.1 => (σ p).1)

private lemma choiceSet_encard (P : G.Joiner A B) (σ : ChoicePoints P) :
    (choiceSet σ).encard = P.1.encard := by
  simpa [choiceSet] using encard_range_choice_eq (P := P) σ

private lemma exists_abPath_avoiding_choiceSet (P : G.Joiner A B) (h : P.1.encard < G.mincut A B)
    (σ : ChoicePoints P) :
    ∃ q : G.ABPath A B, ∀ x ∈ q.support, x ∉ choiceSet σ := by
  exact exists_abPath_avoiding_of_encard_eq (P := P) h _ (choiceSet_encard (P := P) σ)

/-- Create an Erdös-style finite graph from a joiner that is too small. -/
noncomputable def erdos_graph (P : G.Joiner A B) (h : P.1.encard < G.mincut A B) : SimpleGraph V := by
  let C := ChoicePoints P
  have h_witness (σ : C) : ∃ q : G.ABPath A B, ∀ x ∈ q.support, x ∉ choiceSet σ := by
    exact exists_abPath_avoiding_choiceSet (P := P) h σ
  choose q hq using h_witness
  let EP : Set (Sym2 V) := ⋃ p ∈ P.1, (p : G.ABPath A B).p.1.edgeSet
  let EQ : Set (Sym2 V) := ⋃ σ : C, (q σ).p.1.edgeSet
  let E : Set (Sym2 V) := EP ∪ EQ
  exact fromEdgeSet E

variable {P : G.Joiner A B} {h : P.1.encard < G.mincut A B}

theorem erdos_graph_finite : (erdos_graph P h).edgeSet.Finite := by
  haveI : Fintype P.1 := Set.encard_lt_top_iff.mp (lt_top_of_lt h) |>.fintype
  simp [erdos_graph, ChoicePoints, choiceSet] ; constructor <;> apply Set.Finite.diff
  · exact Set.Finite.biUnion this.finite (by simp [ABPath.edgeSet_finite])
  · exact Set.finite_iUnion (by simp [ABPath.edgeSet_finite])

theorem erdos_graph_le : (erdos_graph P h) ≤ G := by
  refine (fromEdgeSet_le _).2 (diff_subset.trans $ union_subset ?_ ?_)
  · apply iUnion₂_subset ; grind [ABPath.edgeSet_subset_graphEdgeSet]
  · apply iUnion_subset ; grind [ABPath.edgeSet_subset_graphEdgeSet]

private lemma erdos_graph_joiner : ∃ PH : (erdos_graph P h).Joiner A B, PH.1.encard = P.1.encard := by
  apply restrict_joiner_to_fromEdgeSet
  intro p hp
  refine subset_trans ?_ subset_union_left
  apply subset_iUnion₂ p hp

private lemma erdos_graph_separator : ∀ SH : (erdos_graph P h).Separator A B, SH.1.encard ≠ P.1.encard := by
  let C := ChoicePoints P
  let Schoice : C → Set V := choiceSet
  have hSchoice_card (σ : C) : (Schoice σ).encard = P.1.encard := by
    exact choiceSet_encard (P := P) σ
  have h_witness (σ : C) : ∃ q : G.ABPath A B, ∀ x ∈ q.support, x ∉ Schoice σ := by
    exact exists_abPath_avoiding_choiceSet (P := P) h σ
  let q σ := (h_witness σ).choose
  let hq σ : ∀ x ∈ (q σ).support, x ∉ Schoice σ := (h_witness σ).choose_spec
  let EP : Set (Sym2 V) := ⋃ p ∈ P.1, (p : G.ABPath A B).p.1.edgeSet
  let EQ : Set (Sym2 V) := ⋃ σ : C, (q σ).p.1.edgeSet
  let E : Set (Sym2 V) := EP ∪ EQ
  have hPE p (hp : p ∈ P.1) : p.p.1.edgeSet ⊆ E := by
    apply (subset_iUnion₂ p hp).trans subset_union_left
  intro SH hcard
  let f (p : P.1) : (fromEdgeSet E).ABPath A B := abPath_to_fromEdgeSet p.1 E (hPE p.1 p.2)
  have h_hit_SH (p : P.1) : ∃ x : {x : V // x ∈ (p.1 : G.ABPath A B).support}, x.1 ∈ SH.1 := by
    obtain ⟨x, hx, hxSH⟩ := SH.2 (f p).u (f p).u.2 (f p).v (f p).v.2 (f p).p.1
    refine ⟨⟨x, ?_⟩, hxSH⟩
    simpa [f] using (show x ∈ (f p).support from hx)
  choose σ hσ using h_hit_SH
  have hSchoice_eq : Schoice σ = SH.1 := by
    have hSchoice_subset : Schoice σ ⊆ SH.1 := by
      rintro x ⟨p, rfl⟩
      exact hσ p
    have hSchoice_fin : (Schoice σ).Finite := by
      refine Set.encard_ne_top_iff.mp ?_
      have hP_fin : P.1.Finite := Set.encard_lt_top_iff.mp (lt_top_of_lt h)
      simpa [hSchoice_card σ] using (Set.encard_ne_top_iff.mpr hP_fin)
    apply hSchoice_fin.eq_of_subset_of_encard_le hSchoice_subset
    simp [hcard, hSchoice_card σ]
  have hqE : (q σ).p.1.edgeSet ⊆ E := by
    intro e he
    exact Or.inr (Set.mem_iUnion.mpr ⟨σ, he⟩)
  let qH : (fromEdgeSet E).ABPath A B := abPath_to_fromEdgeSet (q σ) E hqE
  obtain ⟨x, hxqH, hxSH⟩ := SH.2 qH.u qH.u.2 qH.v qH.v.2 qH.p.1
  have hxq : x ∈ (q σ).support := by
    have hsupp : qH.support = (q σ).support := by
      simp [qH]
    have hxqH' : x ∈ qH.support := by
      simpa [ABPath.support] using hxqH
    simpa [hsupp] using hxqH'
  have hx_not_Schoice : x ∉ Schoice σ := hq σ x hxq
  have hx_not_SH : x ∉ SH.1 := by simpa [hSchoice_eq] using hx_not_Schoice
  exact hx_not_SH hxSH

theorem Menger_finite_mincut (hk : G.mincut A B ≠ ⊤) : G.mincut A B = G.maxflow A B := by
  refine le_antisymm ?_ maxflow_le_mincut
  obtain ⟨k, hk'⟩ : ∃ k : ℕ, (k : ℕ∞) = G.mincut A B := WithTop.ne_top_iff_exists.mp hk
  have hmax_lt_top : G.maxflow A B < ⊤ := by
    exact lt_of_le_of_lt maxflow_le_mincut (hk' ▸ (by simp : (k : ℕ∞) < ⊤))
  rw [← hk']
  obtain ⟨P, (hP : P.1.encard = G.maxflow A B)⟩ := ENat.exists_eq_iSup_of_lt_top hmax_lt_top
  by_contra! hk_gt
  have P_lt_mincut : P.1.encard < G.mincut A B := by simpa [hP, hk'] using hk_gt
  let H : SimpleGraph V := erdos_graph P P_lt_mincut
  have hH_le : H ≤ G := erdos_graph_le
  obtain ⟨PH, hPH_card⟩ := erdos_graph_joiner (P := P) (h := P_lt_mincut)
  have hNoEq : ∀ SH : H.Separator A B, SH.1.encard ≠ P.1.encard := erdos_graph_separator (P := P) (h := P_lt_mincut)
  have hHmenger : H.mincut A B = H.maxflow A B := Menger_strong erdos_graph_finite
  obtain ⟨SH, hSH⟩ := ENat.exists_eq_iInf (fun S : H.Separator A B => S.1.encard)
  have hHmax_eq : H.maxflow A B = P.1.encard := by
    apply le_antisymm
    · apply iSup_le
      intro Q
      obtain ⟨QG, hQG_card⟩ := lift_disjoint_paths_le G H hH_le A B Q
      calc Q.1.encard = QG.1.encard := hQG_card.symm
        _ ≤ G.maxflow A B := encard_le_maxflow_of_joiner QG
        _ = P.1.encard := hP.symm
    · rw [← hPH_card]
      exact encard_le_maxflow_of_joiner PH
  have hSH_card : SH.1.encard = P.1.encard := by
    calc SH.1.encard = H.mincut A B := by simpa [mincut] using hSH
      _ = H.maxflow A B := hHmenger
      _ = P.1.encard := hHmax_eq
  exact (hNoEq SH) hSH_card

@[blueprint "thm:menger"
  (statement := /-- Menger's theorem: The minimum number of vertices separating
      $A$ from $B$ in a graph $G$ is equal to the maximum number of disjoint
      $A--B$ paths in $G$. -/)]
theorem Menger : G.mincut A B = G.maxflow A B := by
  by_cases h : G.mincut A B = ⊤
  · exact Menger_of_mincut_top h
  · exact Menger_finite_mincut h

#print axioms Menger

end SimpleGraph
