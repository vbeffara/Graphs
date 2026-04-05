import Architect
import Graphs.Map
import Graphs.Util
import Graphs.Separation
import Mathlib.Combinatorics.SimpleGraph.Paths

variable {V : Type*} {G : SimpleGraph V} {u v w x y z : V} {p : G.Walk u v} {q : G.Walk v w} {A B X : Set V}

open Classical

namespace SimpleGraph

namespace Walk

lemma edges_no_xy_of_support_inter_subset_one (hxy : x ≠ y)
    (h : ({a | a ∈ p.support} : Set V) ∩ {x, y} ⊆ ({v} : Set V)) :
    s(x, y) ∉ p.edges := by
  intro hxy_mem
  have hx_support : x ∈ p.support := p.fst_mem_support_of_mem_edges hxy_mem
  have hy_support : y ∈ p.support := p.snd_mem_support_of_mem_edges hxy_mem
  have hxv : x = v := Set.mem_singleton_iff.mp (h ⟨hx_support, by simp⟩)
  have hyv : y = v := Set.mem_singleton_iff.mp (h ⟨hy_support, by simp⟩)
  exact hxy (hxv.trans hyv.symm)

noncomputable def firstVisit : ∀ {u v} (p : G.Walk u v), (∃ w ∈ p.support, w ∈ X) → V
  | u, _, Walk.nil, hp => u
  | u, v, Walk.cons h p, hp => if h : u ∈ X then u else p.firstVisit (by grind)

theorem firstVisit_mem_support {hp : ∃ w ∈ p.support, w ∈ X} : p.firstVisit hp ∈ p.support := by
  induction p ; simp [Walk.firstVisit] ; grind [Walk.firstVisit]

theorem firstVisit_mem_X {hp : ∃ w ∈ p.support, w ∈ X} : p.firstVisit hp ∈ X := by
  induction' p ; simpa [Walk.firstVisit] using hp ; grind [Walk.firstVisit]

theorem firstVisit_mem_takeUntil (h1 : w ∈ p.support) (h2 : w ∈ X) :
    p.firstVisit ⟨w, h1, h2⟩ ∈ (p.takeUntil _ h1).support := by
  induction' p with u u ; simp [Walk.firstVisit, Walk.takeUntil]
  by_cases h3 : u ∈ X ; simp [Walk.firstVisit, Walk.takeUntil, h3]
  grind [Walk.firstVisit, Walk.takeUntil]

noncomputable def takeUntilFirst (hp : ∃ w ∈ p.support, w ∈ X) : G.Walk u (p.firstVisit hp) :=
  p.takeUntil _ firstVisit_mem_support

theorem takeUntilFirst_subset_support {hp : ∃ w ∈ p.support, w ∈ X} :
    (p.takeUntilFirst hp).support ⊆ p.support :=
  (Walk.isSubwalk_takeUntil _ _).support_subset

theorem takeUntilFirst_spec {hp : ∃ w ∈ p.support, w ∈ X} (hz : z ∈ (p.takeUntilFirst hp).support)
    (hzX : z ∈ X) : z = p.firstVisit hp := by
  have hz' : z ∈ p.support := takeUntilFirst_subset_support hz
  contrapose! hz
  apply Walk.notMem_support_takeUntil_support_takeUntil_subset hz.symm hz'
  exact firstVisit_mem_takeUntil hz' hzX

lemma exists_walk_prefix_avoiding_set (hp : ∃ w ∈ p.support, w ∈ X) :
    ∃ (w : V) (q : G.Walk u w), w ∈ X ∧ q.support ⊆ p.support ∧ (∀ {z}, z ∈ q.support → z ∈ X → z = w) :=
  ⟨p.firstVisit hp, p.takeUntilFirst hp, firstVisit_mem_X, takeUntilFirst_subset_support, takeUntilFirst_spec⟩

lemma exists_path_prefix_avoiding_set {X : Set V} {p : G.Walk u v} (h : ∃ w ∈ p.support, w ∈ X) :
    ∃ (w : V) (q : G.Walk u w), w ∈ X ∧ q.IsPath ∧ q.support ⊆ p.support ∧ (∀ z ∈ q.support, z ∈ X → z = w) := by
  obtain ⟨w', q, hw'X, hq_support, hq_unique⟩ := p.exists_walk_prefix_avoiding_set h
  refine ⟨w', q.bypass, hw'X, q.bypass_isPath, ?_, ?_⟩ <;> grind [q.support_bypass_subset]

lemma start_notMem_support_dropUntil (hp : p.IsPath) (hw : w ∈ p.support) (h : u ≠ w) :
    u ∉ (p.dropUntil w hw).support := by
  cases p with
  | nil => simp at hw ; grind
  | cons e p =>
    contrapose hp ; simp [Walk.dropUntil, h] at hp ; simp [h.symm] at hw ; simp [p.support_dropUntil_subset hw hp]

lemma prefix_avoids_X (hp : p.IsPath) (hp_X : {z | z ∈ p.support} ∩ X = {v}) (hz : z ∈ p.support)
    (hzX : z ∉ X) : ({a | a ∈ (p.takeUntil z hz).support} : Set V) ∩ X = ∅ := by
  simp only [Set.eq_empty_iff_forall_notMem, Set.mem_inter_iff, not_and]
  intro a ha haX
  have ha_support : a ∈ p.support := p.support_takeUntil_subset hz ha
  have h1 : a ∈ {z | z ∈ p.support} ∩ X := ⟨ha_support, haX⟩
  simp [hp_X] at h1 ; subst a
  exact p.endpoint_notMem_support_takeUntil hp hz (by grind) ha

lemma suffix_avoids_X (hp : p.IsPath) (hp_X : {z | z ∈ p.support} ∩ X = {u}) (hz : z ∈ p.support)
    (hzX : z ∉ X) : ({a | a ∈ (p.dropUntil z hz).support} : Set V) ∩ X = ∅ := by
  simp only [Set.eq_empty_iff_forall_notMem, Set.mem_inter_iff, not_and]
  intro a ha haX
  have ha_support : a ∈ p.support := p.support_dropUntil_subset hz ha
  have h1 : a ∈ {x | x ∈ p.support} ∩ X := ⟨ha_support, haX⟩
  simp [hp_X] at h1 ; subst a
  exact Walk.start_notMem_support_dropUntil hp hz (by grind) ha

lemma isPath_append_of_inter (hp : p.IsPath) (hq : q.IsPath)
    (h_inter : ∀ z ∈ p.support, z ∈ q.support → z = v) : (p.append q).IsPath := by
  induction p <;> aesop

lemma exists_prefix_path_of_ne (p : G.Walk u v) (h_ne : u ≠ v) : ∃ (w : V) (q : G.Walk u w),
    G.Adj w v ∧ q.IsPath ∧ v ∉ q.support ∧ q.support ⊆ p.support := by
  induction p with
  | nil => contradiction
  | cons h p ih =>
    rename_i a b c
    by_cases hbc : b = c
    · aesop
    · obtain ⟨w, q, h1, h2, h3, h4⟩ := ih hbc
      refine ⟨w, (cons h q).bypass, h1, ?_, ?_, ?_⟩
      · exact bypass_isPath (cons h q)
      · grind [support_bypass_subset]
      · simp ; grind [support_bypass_subset]

lemma join_paths_through_edge (e : G.Adj x y) {u1 v1 u2 v2 : V} (p1 : G.Walk u1 v1) (p2 : G.Walk u2 v2)
    (hv1 : v1 = x ∨ v1 = y) (hu2 : u2 = x ∨ u2 = y) :
    ∃ (q : G.Walk u1 v2), q.IsPath ∧ q.support ⊆ p1.support ∪ p2.support := by
  obtain (rfl | h) := eq_or_ne v1 u2
  · refine ⟨_, bypass_isPath (p1.append p2), ?_⟩
    apply (support_bypass_subset _).trans ; intro a ; simp
  · have e' : G.Adj v1 u2 := by grind [adj_comm]
    have : (v1 = x ∧ u2 = y ∨ v1 = y ∧ u2 = x) := by grind
    refine ⟨p1.append (Walk.cons e' p2) |>.bypass, bypass_isPath _, ?_⟩
    apply (support_bypass_subset _).trans
    intro a ; simp ; grind [p1.end_mem_support]

theorem support_inter_support (hp : (p.append q).IsPath) (ha : x ∈ p.support ∧ x ∈ q.support) :
    x = v := by
  replace hp := hp.2
  by_contra!
  suffices x ∈ q.support.tail by grind [Walk.support_append, List.nodup_append]
  cases q <;> simp_all

/-
A path can be split at any vertex in its support into two paths that intersect only at that vertex.
-/
lemma split_at_vertex (hp : p.IsPath) {z : V} (hz : z ∈ p.support) :
    ∃ (p1 : G.Walk u z) (p2 : G.Walk z v), p1.IsPath ∧ p2.IsPath ∧
      p1.support.toFinset ∩ p2.support.toFinset = {z} ∧
      p1.support.toFinset ⊆ p.support.toFinset ∧
      p2.support.toFinset ⊆ p.support.toFinset := by
  rw [← p.take_spec hz]
  refine ⟨_, _, hp.takeUntil hz, hp.dropUntil hz, ?_, ?_, ?_⟩
  · simp [Finset.ext_iff] ; intro a ; constructor
    · apply Walk.support_inter_support ; simpa
    · simp +contextual
  · intro a ; simp ; grind [Walk.support_takeUntil_subset]
  · intro a ; simp ; grind [Walk.support_dropUntil_subset]

end Walk

end SimpleGraph
