import Mathlib
import Graphs.Separation

open Classical Set SimpleGraph

namespace SimpleGraph.IsTree

variable {α : Type*} {G : SimpleGraph α} {a b u v w : α} (h : G.IsTree)

noncomputable def path (u v : α) : G.Path u v := by
  choose p hp₁ hp₂ using h.existsUnique_path u v
  refine ⟨p, hp₁⟩

def ordered (a b c : α) : Prop := b ∈ (h.path a c).1.support

def left (u v : α) : Set α := {w | h.ordered w u v}

def right (u v : α) : Set α := {w | h.ordered u v w}

lemma path_adj (huv : G.Adj u v) : h.path u v = Walk.nil.cons huv := by
  have := h.existsUnique_path u v
  have h_unique_path : ∀ p : G.Path u v, p = ⟨Walk.cons huv Walk.nil, by aesop⟩ := by
    intro p
    generalize_proofs at *;
    cases this ; aesop
  exact congr_arg Subtype.val (h_unique_path _)

lemma path_split (hv : h.ordered u v w) : h.path u w = (h.path u v).1.append (h.path v w).1 := by
  have h_split : ∀ (p : G.Walk u w), v ∈ p.support → ∃ q : G.Walk u v, ∃ r : G.Walk v w, p = q.append r := by
    intro p hp;
    use p.takeUntil v hp;
    exact ⟨ p.dropUntil v hp, by simp +decide ⟩;
  obtain ⟨q, r, hp⟩ := h_split (h.path u w).1 hv
  have hq : q = (h.path u v).1 := by
    have := h.existsUnique_path u v;
    have hq : q.IsPath := by
      have hq : (h.path u w).1.IsPath := by
        exact ( h.path u w ).2
      generalize_proofs at *; (
      rw [ hp ] at hq; exact hq.of_append_left;)
    have hr : (h.path u v).1.IsPath := by
      grind
    have hq_eq : q = (h.path u v).1 := by
      exact ExistsUnique.unique ‹∃! p : G.Walk u v, p.IsPath› hq hr
    exact hq_eq.symm ▸ rfl
  have hr : r = (h.path v w).1 := by
    have := h.existsUnique_path v w;
    -- Since $r$ is a path from $v$ to $w$ and the tree's path from $v$ to $w$ is unique, they must be the same path.
    have hr_unique : r.IsPath := by
      have := (h.path u w).2;
      rw [hp] at this; exact this.of_append_right;
    exact this.unique hr_unique ( h.path v w |>.2 )
  rw [hp, hq, hr]

lemma not_mem_of_adj_mem (huv : G.Adj u v) (hw : h.ordered u v w) : u ∉ (h.path v w).1.support := by
  have h_unique : ∀ p : G.Walk v w, p.IsPath → u ∉ p.support := by
    intro p hp hpu
    have h_unique : p = (h.path v w).val := by
      have := h.existsUnique_path v w; cases this; aesop;
    generalize_proofs at *; (
    have h_unique : (h.path u w).val = (huv).toWalk.append (h.path v w).val := by
      convert path_split h hw using 1
      generalize_proofs at *; (
      rw [ path_adj h huv ])
    generalize_proofs at *; (
    replace h_unique := congr_arg ( fun p => p.support ) h_unique ; simp_all +decide [ Walk.support_append ] ;
    have := h_unique.symm; simp_all +decide [ Walk.isPath_def ] ;
    replace this := congr_arg List.Nodup this ; simp_all +decide [ List.nodup_cons ] ;));
  exact h_unique _ ( h.path v w |>.2 )

theorem left_right_disjoint (huv : G.Adj u v) : h.left u v ∩ h.right u v = ∅ := by
    -- Assume for contradiction that there exists a vertex `w` in both `leftPart` and `rightPart`.
    by_contra h_contra;
    simp_all +decide [ Set.ext_iff, ordered ];
    obtain ⟨ w, hw₁, hw₂ ⟩ := h_contra;
    -- By definition of `leftPart` and `rightPart`, we have `v ∈ (h.thePath u w).val.support` and `u ∈ (h.thePath w v).val.support`.
    have hvw : v ∈ (h.path u w).val.support := by exact?
    have huw : u ∈ (h.path w v).val.support := by exact?;
    convert not_mem_of_adj_mem h huv hvw using 1;
    simp +decide [ path_split, path_adj, huv ];
    have huw_rev : (h.path w v).val = (h.path v w).val.reverse := by
      have := h.existsUnique_path w v;
      refine' this.unique _ _ <;> aesop;
    aesop

theorem left_union_right (huv : G.Adj u v) : h.left u v ∪ h.right u v = univ := by
    unfold left right
    ext w
    simp [ordered];
    -- Since there's a unique path between any two vertices in a tree, if u is not in the path from w to v, then v must be in the path from u to w.
    have h_unique_path : ∀ u v w : α, ∃ p : G.Walk u w, p.IsPath := by
      -- By definition of IsTree, the graph is connected.
      have h_connected : G.Connected := by
        exact h.1;
      exact?;
    -- By the uniqueness of paths in a tree, if u is not in the path from w to v, then v must be in the path from u to w.
    by_cases hu : u ∈ (h.path w v).1.support;
    · exact Or.inl hu;
    · -- Since the path from u to w is unique and includes u and w, and we know that u is not in the path from w to v, it must be that the path from u to w includes v.
      have h_unique_path_uw : ∃ p : G.Walk u w, p.IsPath ∧ v ∈ p.support := by
        obtain ⟨p, hp⟩ : ∃ p : G.Walk w v, p.IsPath ∧ u∉p.support := by
          exact ⟨ _, h.path w v |>.2, hu ⟩
        generalize_proofs at *; (
        -- Since u and v are adjacent, we can create a path from u to w by taking the path from u to v and then appending the path from v to w.
        use Walk.cons huv p.reverse; simp [hp]);
      -- Since there's a unique path between any two vertices in a tree, if there's a path from u to w that includes v, then that path must be the same as the one from u to w.
      have h_unique_path_uw : ∀ p : G.Walk u w, p.IsPath → v ∈ p.support → v ∈ (h.path u w).1.support := by
        intros p hp hpv
        have h_unique_path_uw : p = (h.path u w).1 := by
          have := h.existsUnique_path u w
          generalize_proofs at *; (
          exact this.unique hp ( h.path u w |>.2 ) ▸ rfl)
        rw [h_unique_path_uw] at hpv
        exact hpv;
      grind +ring

theorem left_right_ordered (huv : G.Adj u v) (ha : a ∈ h.left u v) (hb : b ∈ h.right u v) :
    h.ordered a u b ∧ h.ordered a v b := by
  sorry

theorem left_right_separates (huv : G.Adj u v) :
    G.Separates (h.left u v) (h.right u v) {u} ∧ G.Separates (h.left u v) (h.right u v) {v} := by
  sorry

end SimpleGraph.IsTree
