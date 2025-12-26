import Untitled.Graphs.Contraction

set_option autoImplicit false

namespace List

variable {V : Type*}

def init (l : List V) : List V := l.take (l.length - 1)

lemma init_prefix {l l' : List V} (h : l <+: l') : l.init <+: l'.init := by
  have h1 : length l ≤ length l' := List.IsPrefix.length_le h
  have h2 : length l - 1 ≤ length l' - 1 := Nat.sub_le_sub_right h1 1
  have h3 : (length l - 1) ≤ (length l') := h2.trans <| Nat.sub_le (length l') 1
  rw [List.prefix_iff_eq_take] at h
  rw [h, List.prefix_iff_eq_take]
  simp [init, h1, List.take_take, List.take_take, min_eq_left h3, min_eq_left h2]

end List

open Classical SimpleGraph List Finset

namespace SimpleGraph

variable {V V' : Type*} {a b c d : V} {G G' : SimpleGraph V} {f : V → V'} {p : G.Walk a b}

namespace Walk

def init₀ {a b} : G.Walk a b → List V
  | nil => []
  | cons _ p => a :: p.init₀

@[simp] lemma init₀_cons {e : G.Adj c a} : (cons e p).init₀ = c :: p.init₀ := rfl

@[simp] lemma init₀_copy {h1 : a = c} {h2 : b = d} : (p.copy h1 h2).init₀ = p.init₀ := by
  subst_vars ; rfl

def tail₀ {a b} : G.Walk a b → List V
  | nil => []
  | cons _ p => by rename_i c _ ; exact c :: p.tail₀

@[simp] lemma tail₀_cons {e : G.Adj c a} : (cons e p).tail₀ = p.support := by
  induction p generalizing c with
  | nil => rfl
  | cons h p ih => simpa [tail₀] using ih (e := h)

lemma support_eq_init₀_union_last : p.support = p.init₀ ++ [b] := by
  induction p with
  | nil => rfl
  | cons _ p ih => simp [ih]

lemma support_eq_head_union_tail₀ : p.support = a :: p.tail₀ := by
  induction p with
  | nil => rfl
  | cons _ p ih => simp [ih, Walk.tail₀]

lemma tail_eq_tail_support : p.tail₀ = p.support.tail := by
  induction p with
  | nil => rfl
  | cons _ p ih => simp [ih]

lemma init_eq_take_support : p.init₀ = p.support.init := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp [ih, _root_.List.init]

lemma init₀_prefix {p' : G.Walk a c} (h : p'.support <+: p.support) :
    p'.init₀ <+: p.init₀ := by
  simpa [init_eq_take_support] using init_prefix h

lemma init₀_subset_of_support_prefix {p' : G.Walk a c} (h : p'.support <+: p.support) :
    p'.init₀ ⊆ p.init₀ :=
  (init₀_prefix h).subset

end Walk

noncomputable def push_Walk {a b} (f : V → V') : G.Walk a b → (G.map' f).Walk (f a) (f b)
| Walk.nil => Walk.nil
| Walk.cons e p => by
  rename_i c
  by_cases h : f a = f c
  · exact (push_Walk f p).copy h.symm rfl
  · exact Walk.cons ⟨h, _, _, e, rfl, rfl⟩ (push_Walk f p)

lemma support_push_Walk : (push_Walk f p).support ⊆ List.map f p.support := by
  induction p with
  | nil => simp [push_Walk]
  | cons h p ih =>
    rename_i u v w
    by_cases h : f u = f v <;> simpa [push_Walk, h] using ih.trans <| List.subset_cons _ _

-- @[simp] lemma push_nil : push_Walk f (@Walk.nil _ _ G a) = Walk.nil (f a) := rfl

-- lemma push_cons (f : V → V') (e : G.dart) (p : G.Walk) (h : e.snd = p.a) :
--   push_Walk f (p.cons e h) = Walk.append (push_step f e) (push_Walk f p) (by simp [h]) :=
-- by { rcases p with ⟨a,b,p⟩, rcases e with ⟨⟨u,v⟩,e⟩, simp at h, subst a, refl }

-- lemma push_cons_eq (f : V → V') (e : G.dart) (p : G.Walk) (h : e.snd = p.a) (h' : f e.fst = f e.snd) :
--   push_Walk f (p.cons e h) = push_Walk f p :=
-- begin
--   have : push_step f e = Walk.nil (f e.fst) := by simp [push_step,push_step_aux,h'],
--   rw [push_cons], simp only [this], exact append_nil_left
-- end

-- lemma push_cons_ne (f : V → V') (e : G.dart) (p : G.Walk) (h : e.snd = p.a) (h' : f e.fst ≠ f e.snd) :
--   push_Walk f (p.cons e h) = Walk.cons ⟨⟨_,_⟩,⟨h',e.fst,e.snd,e.is_adj,rfl,rfl⟩⟩ (push_Walk f p) (by simp [h]) :=
-- begin
--   have : push_step f e = Walk.step ⟨⟨_,_⟩,⟨h',e.fst,e.snd,e.is_adj,rfl,rfl⟩⟩ :=
--     by simp [push_step,push_step_aux,h'],
--   rw [push_cons], simp [this,step]
-- end

lemma push_append (q : G.Walk b c) :
    push_Walk f (p.append q) = (push_Walk f p).append (push_Walk f q) := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    rename_i u v w
    by_cases huv : f u = f v <;> simp [push_Walk, huv, ih q]
    rw [← Walk.append_copy_copy]
    congr

lemma push_eq_nil' {w : V'} (hp : ∀ z ∈ p.support, f z = w) :
    (push_Walk f p).copy (hp _ p.start_mem_support) (hp _ p.end_mem_support) = Walk.nil := by
  induction p with
  | nil => simp at hp ; subst hp ; rfl
  | cons h p ih =>
    simp at hp ; obtain ⟨h1, hp⟩ := hp
    subst_vars
    simpa [push_Walk, hp _ (Walk.start_mem_support _)] using ih hp

lemma tata {q : G.Walk c d} {h1 : a = c} {h2 : b = d} :
    p.copy h1 h2 = q ↔ p = q.copy h1.symm h2.symm := by
  constructor <;> rintro rfl <;> simp

lemma push_eq_nil {x y} (f : V → V') (w : V') (p : G.Walk x y) (hp : ∀ z ∈ p.support, f z = w) :
    (push_Walk f p).Nil := by
  simp [tata.mp <| push_eq_nil' hp]

noncomputable def pwa2 (f : V → V') (hf : G.Adapted f) (x y : V) (x' y' : V') (hx : f x = x')
    (hy : f y = y') (p' : (G.map' f).Walk x' y') :
    {q : G.Walk x y // (push_Walk f q).copy hx hy = p'} := by
  induction p' generalizing x y with
  | nil =>
    choose p hp using hf (hx.trans hy.symm)
    exact ⟨p, hy ▸ push_eq_nil' hp⟩
  | cons h p ih =>
    choose l m h4 h5 h6 using id h.2
    subst_vars
    set p1 := Classical.choose <| hf h5.symm
    have h8 := push_eq_nil' <| Classical.choose_spec <| hf h5.symm
    specialize ih m y rfl rfl
    use p1.append (ih.val.cons h4)
    simp [push_append, hf, push_Walk, h5.trans_ne h.1, tata.mp h8, tata.mp ih.prop]
    rw [← Walk.copy_rfl_rfl (Walk.cons _ _), Walk.append_copy_copy]
    simp [Walk.copy_cons]

noncomputable def pwa' (f : V → V') (hf : G.Adapted f) (x y : V)
    (p' : (G.map' f).Walk (f x) (f y)) : G.Walk x y :=
  pwa2 f hf x y (f x) (f y) rfl rfl p'

example (f : V → V') (hf : G.Adapted f) (x y : V)
    (p' : (G.map' f).Walk (f x) (f y)) : push_Walk f (pwa' f hf x y p') = p' :=
  (pwa2 f hf x y (f x) (f y) rfl rfl p').prop

noncomputable def pull_Walk_aux (f : V → V') (hf : G.Adapted f) (x y : V)
    (p' : (G.map' f).Walk (f x) (f y)) : {w : G.Walk x y // push_Walk f w = p'} := by
  exact pwa2 f hf x y (f x) (f y) rfl rfl p'

noncomputable def pull_Walk (f : V → V') (hf : G.Adapted f) (x y : V)
    (p' : (G.map' f).Walk (f x) (f y)) : G.Walk x y :=
  pull_Walk_aux f hf x y p'

@[simp] lemma pull_Walk_push {hf x y} {p' : (G.map' f).Walk (f x) (f y)} :
    push_Walk f (pull_Walk f hf x y p') = p' :=
  (pull_Walk_aux f hf x y p').prop

lemma head_or_exists_tail₀ {P : V → Prop} (h : ∃ v ∈ p.support, P v) : P a ∨
    (¬ P a ∧ ∃ v ∈ p.tail₀, P v) := by
  by_cases h1 : P a
  · left ; assumption
  · right ; simp [h1] ; by_cases h2 : p.Nil
    · cases h2 ; simp at h ; contradiction
    · cases p
      · cases h2 Walk.nil_nil
      · simpa [h1] using h

noncomputable def takeUntil_aux {a b} (p : G.Walk a b) (P : V → Prop) (h : ∃ v ∈ p.support, P v) :
    (c : Subtype P) × {q : G.Walk a c // q.support <+: p.support ∧ ∀ v ∈ q.init₀, ¬ P v} := by
  induction p with
  | nil => simp at h ; refine ⟨⟨_, h⟩, Walk.nil, prefix_rfl, by simp [Walk.init₀]⟩
  | cons h p ih =>
    rename_i u v w e
    apply (head_or_exists_tail₀ h).by_cases <;> intro h1
    · refine ⟨⟨u, h1⟩, Walk.nil, prefix_iff_eq_take.mpr rfl, by simp [Walk.init₀]⟩
    · choose h2 h4 using h1
      simp at h4
      cases ih h4 with | mk c q =>
        exact ⟨c, Walk.cons e q, by simp [cons_prefix_iff, q.prop.1], by simpa [h2] using q.prop.2⟩

noncomputable def entrance (p : G.Walk a b) (P : V → Prop) (h : ∃ v ∈ p.support, P v) : V :=
  (takeUntil_aux p P h).1

lemma entrance_prop {p : G.Walk a b} {P : V → Prop} {h : ∃ v ∈ p.support, P v} :
    P (entrance p P h) :=
  (takeUntil_aux p P h).1.prop

noncomputable def takeUntil (p : G.Walk a b) (P : V → Prop) (h : ∃ v ∈ p.support, P v) :
    G.Walk a (entrance p P h) := (takeUntil_aux p P h).2.1

-- noncomputable def exit (p : G.Walk a b) (X : Finset V) (hX : (p.range ∩ X).Nonempty) :
--     {x : V // x ∈ X ∧ x ∈ p.support } := by
--   let y := entrance p.reverse X (by simpa using hX)
--   convert y using 3 ; simp

-- noncomputable def after (p : G.Walk) (X : finset V) (hX : (p.range ∩ X).nonempty) :
--   {q : G.Walk // q.a ∈ X ∧ q.b = p.b ∧
--     q.range ⊆ p.range ∧ q.init ⊆ p.init ∧ q.tail ⊆ p.tail ∧ q.tail ∩ X = ∅} :=
-- begin
--   revert p, refine rec₀ _ _,
--   { rintro u hu,
--     exact ⟨nil u, finset.singleton_inter_nonempty.mp hu, rfl, by refl, by refl, by refl, rfl⟩ },
--   { rintro e p h₁ ih h₂, by_cases (p.range ∩ X).nonempty,
--     { rcases ih h with ⟨q, hq₁, hq₂, hq₃, hq₄, hq₅, hq₆⟩,
--       refine ⟨q, hq₁, hq₂, _, _, _, hq₆⟩,
--       { simp, apply hq₃.trans, apply finset.subset_union_right },
--       { simp, apply hq₄.trans, apply finset.subset_union_right },
--       { simp, apply hq₅.trans, rw range_eq_start_union_tail, apply finset.subset_union_right }
--     },
--     { refine ⟨cons e p h₁, _, rfl, by refl, _⟩,
--       { simp at h₂ ⊢, rcases h₂ with ⟨z,hz⟩, simp at hz, cases hz with hz₁ hz₂,
--         cases hz₁, subst z, exact hz₂, exfalso, apply h, use z, simp, exact ⟨hz₁,hz₂⟩ },
--       { simp at h ⊢, exact h } } }
-- end

namespace Walk

section transport

variable {V : Type*} {G G' : SimpleGraph V} {a b : V} {p : G.Walk a b}

def transportable_to (G' : SimpleGraph V) (p : G.Walk a b) : Prop :=
  ∀ e ∈ p.darts, G'.Adj e.fst e.snd

lemma transportable_to_of_le (G_le : G ≤ G') : transportable_to G' p := by
  induction p with
  | nil => simp [transportable_to]
  | cons h p ih => simpa [transportable_to, G_le h] using ih

noncomputable def transport (hp : transportable_to G' p) :
    {q : G'.Walk a b // q.support = p.support} := by
  induction p with
  | nil => exact ⟨Walk.nil, rfl⟩
  | cons h p' ih =>
    simp [transportable_to] at hp ih
    specialize ih hp.2
    refine ⟨Walk.cons hp.1 ih.1, by simpa using ih.2⟩

end transport

end SimpleGraph.Walk
