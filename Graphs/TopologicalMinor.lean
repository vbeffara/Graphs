import Mathlib

open Set SimpleGraph Function

variable {α β γ : Type*} {G G₁ : SimpleGraph α} {H G₂ : SimpleGraph β} {G₃ : SimpleGraph γ}

structure PathEmbedding (G : SimpleGraph α) (H : SimpleGraph β) where
  f : α ↪ β
  df (e : G.Dart) : H.Path (f e.fst) (f e.snd)
  --
  symm e : df e.symm = (df e).reverse
  ends {e x} : f x ∈ (df e).1.support ↔ x = e.fst ∨ x = e.snd
  disj {e e' v} : v ∈ (df e).1.support → v ∈ (df e').1.support → e = e' ∨ v ∈ range f

def IsTopologicalMinor (G : SimpleGraph α) (H : SimpleGraph β) := Nonempty (PathEmbedding G H)

infix:50 " ≼t " => IsTopologicalMinor

namespace PathEmbedding

variable {φ : PathEmbedding G H} {x y z : α} {p : G.Walk x y} {p' : G.Walk y z} {u : β}

def self (G : SimpleGraph α) : PathEmbedding G G where
  f := .refl α
  df e := .singleton e.adj
  symm _ := rfl
  ends := by simp
  disj := by simp

theorem refl (G : SimpleGraph α) : G ≼t G := ⟨self G⟩

def follow (φ : PathEmbedding G H) : ∀ {x y : α}, G.Walk x y → H.Walk (φ.f x) (φ.f y)
  | _, _, Walk.nil      => Walk.nil
  | _, _, Walk.cons h p => (φ.df ⟨(_, _), h⟩).1.append (φ.follow p)

@[simp] lemma follow_nil : φ.follow (Walk.nil (u := x)) = Walk.nil := rfl

@[simp] lemma follow_cons {h : G.Adj z x} : φ.follow (Walk.cons h p) =
    (φ.df ⟨(_, _), h⟩).1.append (φ.follow p) :=
  rfl

@[simp] lemma follow_append : φ.follow (p.append p') = (φ.follow p).append (φ.follow p') := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [ih, Walk.append_assoc]

@[simp] lemma follow_reverse : φ.follow (p.reverse) = (φ.follow p).reverse := by
  induction p with
  | nil => rfl
  | cons h p ih => have := φ.symm ⟨(_, _), h⟩ ; simp_all

lemma mem_follow (hp : 0 < p.length) :
    u ∈ (φ.follow p).support ↔ ∃ e ∈ p.darts, u ∈ (φ.df e).1.support := by
  induction p with
  | nil => contradiction
  | cons e p ih => cases p <;> simp_all

theorem append_isPath (hp : p.IsPath) (hp' : p'.IsPath)
    (hpp' : ∀ a, a ∈ p.support → a ∈ p'.support → a = y) :
    (p.append p').IsPath := by
  induction p with
  | nil => simpa
  | cons h p ih =>
    simp_all
    have := p.end_mem_support
    grind

theorem isPath_follow (hp : p.IsPath) : (φ.follow p).IsPath := by
  induction p with
  | nil => simp
  | cons h p ih =>
    wlog hp₀ : 0 < p.length ; cases p <;> simp_all
    rw [follow_cons]
    obtain ⟨hp₁, hp₂⟩ := (Walk.cons_isPath_iff _ _).1 hp
    refine append_isPath (φ.df _).isPath (ih hp₁) ?_
    intro u hu hu'
    contrapose hp₂
    obtain ⟨e, he₁, he₂⟩ := (mem_follow hp₀).1 hu'
    have h7 := p.dart_fst_mem_support_of_mem_darts he₁
    rcases φ.disj he₂ hu with rfl | ⟨x, rfl⟩ ; assumption
    rcases φ.ends.1 hu with rfl | rfl ; swap ; contradiction
    rcases φ.ends.1 he₂ with rfl | rfl ; assumption
    exact p.dart_snd_mem_support_of_mem_darts he₁

def follow_path (p : G.Path x y) : H.Path (φ.f x) (φ.f y) :=
  ⟨φ.follow p.1, φ.isPath_follow p.isPath⟩

def trans (φ : PathEmbedding G₁ G₂) (ψ : PathEmbedding G₂ G₃) : PathEmbedding G₁ G₃ where
  f := φ.f.trans ψ.f
  df e := ⟨ψ.follow (φ.df e), isPath_follow (φ.df e).isPath⟩
  symm e := by congr ; simp [φ.symm]
  ends := sorry
  disj := sorry

-- def comp (F : path_embedding G G') (F' : path_embedding G' G'') : path_embedding G G'' :=
-- { f := ⟨F'.f ∘ F.f, injective.comp F'.f.inj' F.f.inj'⟩,
--   df := λ e, follow F' (F.df e),
--   --
--   nodup := λ e, (follow_nodup F') (F.nodup _),
--   sym := by { intro e, rewrite F.sym e, apply follow_rev },
--   --
--   endpoint := by {
--     intros e x h1, obtain ⟨e',h4,h5⟩ := mem_follow F' (nop F) h1,
--     exact F.endpoint ((walk.mem_of_edges (nop _)).mpr ⟨e',h4,F'.endpoint h5⟩)
--   },
--   --
--   disjoint := by {
--     intros e e' z h1 h2,
--     replace h1 := mem_follow _ (nop _) h1, obtain ⟨e1,h3,h4⟩ := h1,
--     replace h2 := mem_follow _ (nop _) h2, obtain ⟨e2,h5,h6⟩ := h2,
--     have h7 := F'.disjoint h4 h6, cases h7,
--     { left, clear h4 h6, replace h3 := walk.mem_edges h3, replace h5 := walk.mem_edges h5,
--       replace h5 : e1.fst ∈ (F.df e').support ∧ e1.snd ∈ (F.df e').support :=
--       by { cases (dart_edge_eq_iff e1 e2).mp h7; subst e1,
--         exact h5, simp only [dart.symm], exact h5.symm },
--       cases F.disjoint h3.1 h5.1 with h10 h10, exact h10, obtain ⟨x,h10⟩ := h10, rw h10 at h3 h5,
--       cases F.disjoint h3.2 h5.2 with h11 h11, exact h11, obtain ⟨y,h11⟩ := h11, rw h11 at h3 h5,
--       have h12 := F.endpoint h3.1, have h13 := F.endpoint h3.2,
--       have h14 := F.endpoint h5.1, have h15 := F.endpoint h5.2,
--       have h16 : x ≠ y := by { intro h, apply G'.ne_of_adj e1.is_adj, convert congr_arg F.f h },
--       exact sym2.eq_of_ne_mem h16 h12 h13 h14 h15 },
--     { obtain ⟨y,h8⟩ := h7, subst z, replace h4 := F'.endpoint h4, replace h6 := F'.endpoint h6,
--       replace h3 := walk.mem_edges h3, replace h5 := walk.mem_edges h5,
--       replace h3 : y ∈ (F.df e).support, by { simp only [dart.edge, sym2.mem_iff] at h4,
--         rcases e1 with ⟨⟨e1x,e1y⟩,e1h⟩, simp at h4,
--         cases h4; subst h4, exact h3.1, exact h3.2 },
--       replace h5 : y ∈ (F.df e').support, by { simp only [dart.edge, sym2.mem_iff] at h6,
--         rcases e2 with ⟨⟨e2x,e2y⟩,e2h⟩, simp at h6,
--         cases h6; subst h6, exact h5.1, exact h5.2 },
--       cases F.disjoint h3 h5 with h9 h9,
--       { left, exact h9 },
--       { obtain ⟨x,h9⟩ := h9, subst h9, right, use x, refl } } } }

-- theorem trans : embeds_into G G' → embeds_into G' G'' → embeds_into G G'' :=
-- λ ⟨F⟩ ⟨F'⟩, ⟨comp F F'⟩

def of_hom (f : G →g H) (hf : Injective f) : PathEmbedding G H where
  f := ⟨f, hf⟩
  df e := .singleton $ f.map_rel e.adj
  symm e := rfl
  ends := by simp ; grind
  disj := by simp

end PathEmbedding
