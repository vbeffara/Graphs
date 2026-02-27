import Mathlib
import Graphs.Separation

open Classical Set SimpleGraph

namespace SimpleGraph.IsTree

variable {α : Type*} {G : SimpleGraph α} {a b u v w : α} (h : G.IsTree)

noncomputable def path (u v : α) : G.Path u v := by
  have := h.existsUnique_path u v
  exact ⟨this.choose, this.choose_spec.1⟩

theorem path_spec' (p : G.Path u v) : p.1 = (h.path u v).1 := by
  exact (h.existsUnique_path u v).choose_spec.2 p p.2

theorem path_spec (p : G.Path u v) : p = h.path u v := by
  ext ; exact h.path_spec' p

def ordered (a b c : α) : Prop := b ∈ (h.path a c).1.support

def left (u v : α) : Set α := {w | h.ordered w u v}

def right (u v : α) : Set α := {w | h.ordered u v w}

lemma path_adj (huv : G.Adj u v) : h.path u v = huv.toWalk := by
  exact h.path_spec' ⟨_, Walk.IsPath.of_adj huv⟩ |>.symm

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
    replace h_unique := congr_arg ( fun p => p.support ) h_unique
    simp_all +decide
    have := h_unique.symm; simp_all +decide
    replace this := congr_arg List.Nodup this ; simp_all +decide [ List.nodup_cons ] ;));
  exact h_unique _ ( h.path v w |>.2 )

theorem left_right_disjoint (huv : G.Adj u v) : h.left u v ∩ h.right u v = ∅ := by
    -- Assume for contradiction that there exists a vertex `w` in both `leftPart` and `rightPart`.
    by_contra h_contra;
    simp_all +decide [ Set.ext_iff ];
    obtain ⟨ w, hw₁, hw₂ ⟩ := h_contra;
    -- By definition of `leftPart` and `rightPart`, we have `v ∈ (h.thePath u w).val.support` and `u ∈ (h.thePath w v).val.support`.
    have hvw : v ∈ (h.path u w).val.support := by exact Multiset.mem_coe.mp hw₂
    have huw : u ∈ (h.path w v).val.support := by exact Multiset.mem_coe.mp hw₁;
    convert not_mem_of_adj_mem h huv hvw using 1;
    simp +decide
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
      exact fun u v w ↦ Connected.exists_isPath h_connected u w;
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

lemma path_mem_left (huv : G.Adj u v) (ha : a ∈ h.left u v) {x : α} (hx : x ∈ (h.path a u).1.support) : x ∈ h.left u v := by
  have hx_left : h.path a v = (h.path a x).1.append (h.path x v).1 := by
    apply h.path_split; exact (by
    have h_ordered : h.path a v = (h.path a u).1.append (h.path u v).1 := by
      convert h.path_split ha using 1;
    unfold SimpleGraph.IsTree.ordered at *; aesop;)
  have hx_left' : h.path a u = (h.path a x).1.append (h.path x u).1 := by
    convert h.path_split _ using 1 ; aesop;
  have hx_support : x ∈ (h.path x v).1.support := by
    simp +decide
  have hx_support : u ∈ (h.path a v).1.support := by
    exact Multiset.mem_coe.mp ha;
  have hx_support : u ∈ (h.path a x).1.support ∨ u ∈ (h.path x v).1.support := by
    aesop;
  cases hx_support <;> simp_all +decide
  · have hx_support : h.path a x = (h.path a u).1.append (h.path u x).1 := by
      apply path_split;
      (expose_names; exact ((fun a ↦ h_1) ∘ fun a ↦ α) α);
    have := congr_arg SimpleGraph.Walk.length hx_support; norm_num at this;
    rw [ hx_left' ] at this ; simp +decide at this;
    simp +decide [ add_assoc ] at this;
    cases h : ( h.path x u : G.Walk x u ) <;> simp +decide [ h ] at this ⊢;
    simp +decide [ SimpleGraph.IsTree.left ] at *;
    simp +decide [ SimpleGraph.IsTree.ordered ] at *;
  · have := h.left_right_disjoint huv; simp_all +decide [ Set.ext_iff ] ;
    specialize this u ; aesop

/-
If b is in the right set of u v (meaning v is on the path from u to b), and x is on the path from v to b, then x is also in the right set (meaning v is on the path from u to x).
-/
lemma path_mem_right (hb : b ∈ h.right u v) {x : α} (hx : x ∈ (h.path v b).1.support) : x ∈ h.right u v := by
  -- By definition of $h.path$, we know that $x$ is on the path from $v$ to $b$.
  have h_append : (h.path v b).1 = (h.path v x).1.append (h.path x b).1 := by
    convert h.path_split _ using 1 ; aesop;
  -- By definition of $h.path$, we know that $x$ is on the path from $u$ to $b$.
  have h_append : (h.path u b).1 = (h.path u v).1.append ((h.path v x).1.append (h.path x b).1) := by
    rw [ ← h_append, ← path_split ] ; aesop;
  unfold SimpleGraph.IsTree.right at *;
  unfold SimpleGraph.IsTree.ordered at *; simp_all +decide
  have h_append : (h.path u x).1 = (h.path u v).1.append (h.path v x).1 := by
    have h_unique : ∀ p q : G.Walk u x, p.IsPath → q.IsPath → p = q := by
      have := h.existsUnique_path u x;
      exact fun p q hp hq => this.unique hp hq
    apply h_unique;
    · exact h.path u x |>.2;
    · have h_append : (h.path u b).1.IsPath := by
        exact h.path u b |>.2;
      simp_all +decide [ SimpleGraph.Walk.isPath_def ];
      simp_all +decide [ SimpleGraph.Walk.support_append ];
      exact h_append.sublist ( by simp +decide );
  aesop

/-
If a is in the left set and b is in the right set of an edge uv, then the path from a to b is the concatenation of the path from a to u, the edge uv, and the path from v to b.
-/
lemma path_eq_append_of_adj (huv : G.Adj u v) (ha : a ∈ h.left u v) (hb : b ∈ h.right u v) : (h.path a b).1 = (h.path a u).1.append ((h.path u v).1.append (h.path v b).1) := by
  obtain ⟨ p₁, hp₁ ⟩ := h.existsUnique_path a b;
  obtain ⟨ p₂, hp₂ ⟩ := h.existsUnique_path a u
  obtain ⟨ p₃, hp₃ ⟩ := h.existsUnique_path v b
  have h_path : p₁ = p₂.append (SimpleGraph.Walk.cons huv p₃) := by
    refine' hp₁.2 _ _ ▸ rfl;
    simp_all +decide [ SimpleGraph.Walk.isPath_def ];
    simp_all +decide [ SimpleGraph.Walk.support_append, List.nodup_append ];
    intro x hx y hy hxy;
    have h_contradiction : x ∈ (h.path a u).1.support ∧ x ∈ (h.path v b).1.support := by
      aesop;
    have h_contradiction : x ∈ h.left u v ∧ x ∈ h.right u v := by
      exact ⟨ path_mem_left h huv ha h_contradiction.1, path_mem_right h hb h_contradiction.2 ⟩;
    exact absurd ( left_right_disjoint h huv ) ( Set.Nonempty.ne_empty ⟨ x, h_contradiction ⟩ );
  have h_path_eq : h.path a b = p₁ ∧ h.path a u = p₂ ∧ h.path v b = p₃ ∧ h.path u v = SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil := by
    refine' ⟨ _, _, _, _ ⟩;
    · exact hp₁.2 _ ( h.path a b |>.2 );
    · exact hp₂.2 _ ( h.path a u |>.2 );
    · exact hp₃.2 _ ( h.path v b |>.2 );
    · convert path_adj h huv;
  aesop

theorem left_right_ordered (huv : G.Adj u v) (ha : a ∈ h.left u v) (hb : b ∈ h.right u v) :
    h.ordered a u b ∧ h.ordered a v b := by
  -- By `path_eq_append_of_adj`, the path from `a` to `b` is the concatenation of the path from `a` to `u`, the edge `uv`, and the path from `v` to `b`. Thus, the support of the path from `a` to `b` contains the support of the path from `a` to `u` (which contains `u`) and the support of the path from `v` to `b` (which contains `v`).
  have h_support : (h.path a b).1.support.contains u ∧ (h.path a b).1.support.contains v := by
    rw [ path_eq_append_of_adj ];
    any_goals assumption;
    aesop;
  aesop

theorem left_right_separates (huv : G.Adj u v) :
    G.Separates (h.left u v) (h.right u v) {u} ∧ G.Separates (h.left u v) (h.right u v) {v} := by
  constructor <;> intro a ha b hb p;
  · have := h.left_right_ordered huv ha hb;
    have h_unique_path : ∀ p q : G.Walk a b, p.IsPath → q.IsPath → p = q := by
      have := h.existsUnique_path a b;
      exact fun p q hp hq => this.unique hp hq;
    -- Since p is a walk, we can find a subwalk that is a path.
    obtain ⟨q, hq⟩ : ∃ q : G.Walk a b, q.IsPath ∧ q.support ⊆ p.support := by
      have h_subwalk : ∀ p : G.Walk a b, ∃ q : G.Walk a b, q.IsPath ∧ q.support ⊆ p.support := by
        intro p
        obtain ⟨q, hq⟩ : ∃ q : G.Walk a b, q.IsPath ∧ q.support ⊆ p.support := by
          have h_walk : ∀ p : G.Walk a b, ∃ q : G.Walk a b, q.IsPath ∧ q.support ⊆ p.support := by
            intro p
            exact ⟨p.toPath, by
              grind, by
              -- Since $p.toPath$ is a path, its support is a subset of $p$'s support.
              apply SimpleGraph.Walk.support_toPath_subset⟩
          exact h_walk p;
        use q;
      exact h_subwalk p;
    specialize h_unique_path q ( h.path a b ) ; aesop;
  · -- Since p is a path from a to b and v is ordered between a and b, v must be in the support of p.
    have h_v_in_support : v ∈ p.support := by
      -- Since $p$ is a walk from $a$ to $b$, and $a$ is in the left set and $b$ is in the right set, the path from $a$ to $b$ must pass through $v$.
      have h_path : v ∈ (h.path a b).1.support := by
        have := h.left_right_ordered huv ha hb;
        exact this.2;
      have h_unique_path : ∀ p q : G.Walk a b, p.IsPath → q.IsPath → p = q := by
        -- Since G is a tree, there is a unique path between any two vertices. Therefore, any two paths between a and b must be equal.
        have h_unique_path : ∀ p q : G.Walk a b, p.IsPath → q.IsPath → p = q := by
          intro p q hp hq
          have h_unique : ∃! p : G.Walk a b, p.IsPath := by
            exact h.existsUnique_path a b
          exact h_unique.unique hp hq;
        exact h_unique_path;
      contrapose! h_unique_path;
      refine' ⟨ p.toPath, h.path a b, _, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.Walk.isPath_def ];
      intro h_eq; simp_all +decide [ SimpleGraph.Walk.toPath ] ;
      replace h_eq := congr_arg ( fun q => v ∈ q.support ) h_eq ; simp_all +decide
      exact h_unique_path ( by simpa using SimpleGraph.Walk.support_bypass_subset _ h_eq );
    aesop

/-
In a tree rooted at `root`, for any edge `(u, v)`, either `u` is ordered before `v`
or `v` is ordered before `u`.
-/
lemma adj_ordered_cases (hG : G.IsTree) (root : α) {u v : α} (huv : G.Adj u v) :
    hG.ordered root u v ∨ hG.ordered root v u := by
  obtain ⟨p₁, hp₁⟩ := hG.existsUnique_path root u
  obtain ⟨p₂, hp₂⟩ := hG.existsUnique_path root v
  have h_intersect : p₁.IsPath ∧ p₂.IsPath → u ∈ p₂.support ∨ v ∈ p₁.support := by
    intro h_paths
    by_contra h_contra
    have h_path_root_u_v : ∃ p : G.Walk root u, p.IsPath ∧ v ∈ p.support := by
      use p₂.append (SimpleGraph.Walk.cons huv.symm SimpleGraph.Walk.nil)
      simp_all +decide [SimpleGraph.Walk.isPath_def]
      simp_all +decide [SimpleGraph.Walk.support_append]
      rw [List.nodup_append]
      aesop
    grind +ring
  unfold SimpleGraph.IsTree.ordered
  aesop

/-
In a rooted tree, a node has at most one parent.
-/
lemma parent_unique (hG : G.IsTree) (root : α) (t : α) (p₁ p₂ : α)
    (h₁ : G.Adj t p₁ ∧ hG.ordered root p₁ t)
    (h₂ : G.Adj t p₂ ∧ hG.ordered root p₂ t) : p₁ = p₂ := by
  have h_path : ∀ {p : α}, G.Adj t p → hG.ordered root p t →
      ∀ {q : α}, G.Adj t q → hG.ordered root q t → p = q := by
    intro p hp hpath_p q hq hpath_q
    have h_path_eq :
        (hG.path root t).1 = (hG.path root p).1.append (hG.path p t).1 ∧
        (hG.path root t).1 = (hG.path root q).1.append (hG.path q t).1 := by
      exact ⟨hG.path_split hpath_p, hG.path_split hpath_q⟩
    have h_support_eq : (hG.path p t).1.support = [p, t] ∧ (hG.path q t).1.support = [q, t] := by
      have h_support_eq' : ∀ {p : α}, G.Adj t p → (hG.path p t).1.support = [p, t] := by
        intro p hp
        have := hG.path_adj hp.symm
        aesop
      exact ⟨h_support_eq' hp, h_support_eq' hq⟩
    have h_support_eq :
        (hG.path root t).1.support = (hG.path root p).1.support ++ [t] ∧
        (hG.path root t).1.support = (hG.path root q).1.support ++ [t] := by
      have := congr_arg SimpleGraph.Walk.support h_path_eq.1
      have := congr_arg SimpleGraph.Walk.support h_path_eq.2
      simp_all +decide [SimpleGraph.Walk.support_append]
    have h_support_eq :
        (hG.path root p).1.support.getLast? = some p ∧
        (hG.path root q).1.support.getLast? = some q := by
      have h_support_eq' : ∀ {u v : α} (p : G.Walk u v), p.support.getLast? = some v := by
        intro u v p
        induction p <;> simp +decide [*]
        grind
      exact ⟨h_support_eq' _, h_support_eq' _⟩
    aesop
  exact h_path h₁.1 h₁.2 h₂.1 h₂.2

/-
Transitivity of the ordered relation in a rooted tree.
-/
lemma ordered_trans (hG : G.IsTree) (root : α) {a b c : α}
    (hab : hG.ordered root a b) (hbc : hG.ordered root b c) : hG.ordered root a c := by
  have h_concat : (hG.path root c).1 = (hG.path root b).1.append (hG.path b c).1 := by
    exact path_split hG hbc
  unfold SimpleGraph.IsTree.ordered at *
  aesop

/-
Antisymmetry of the ordered relation in a rooted tree.
-/
lemma ordered_antisymm (hG : G.IsTree) (root : α) {a b : α}
    (hab : hG.ordered root a b) (hba : hG.ordered root b a) : a = b := by
  have h_path_eq : (hG.path root b).1 = (hG.path root a).1.append (hG.path a b).1 := by
    exact path_split hG hab
  have h_path_eq' : (hG.path root a).1 = (hG.path root b).1.append (hG.path b a).1 := by
    exact path_split hG hba
  replace h_path_eq' := congr_arg (fun p => p.support) h_path_eq'
  simp_all +decide [SimpleGraph.Walk.support_append]
  cases h : (hG.path a b : G.Walk a b) <;> aesop

end SimpleGraph.IsTree
