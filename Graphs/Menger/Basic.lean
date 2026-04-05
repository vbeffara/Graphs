import Architect
import Graphs.Map
import Graphs.Util
import Graphs.Separation
import Mathlib.Combinatorics.SimpleGraph.Paths

variable {V : Type*} {G : SimpleGraph V} {u v w x y z : V} {p : G.Walk u v} {X : Set V}

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

lemma prefix_avoids_X (hp : p.IsPath) (hp_X : {z | z ∈ p.support} ∩ X = {v}) (hz : z ∈ p.support)
    (hzX : z ∉ X) : ({a | a ∈ (p.takeUntil z hz).support} : Set V) ∩ X = ∅ := by
  simp [Set.eq_empty_iff_forall_notMem, Set.mem_inter_iff, not_and]
  intro a ha haX
  have ha_support : a ∈ p.support := p.support_takeUntil_subset hz ha
  have h1 : a ∈ {z | z ∈ p.support} ∩ X := ⟨ha_support, haX⟩
  simp [hp_X] at h1 ; subst a
  exact p.endpoint_notMem_support_takeUntil hp hz (by grind) ha

end Walk

end SimpleGraph
