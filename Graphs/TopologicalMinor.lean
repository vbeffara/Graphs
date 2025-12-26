import Mathlib

open Set SimpleGraph Function

variable {α β γ : Type*} {G G₁ : SimpleGraph α} {H G₂ : SimpleGraph β} {G₃ : SimpleGraph γ}

structure PathEmbedding (G : SimpleGraph α) (H : SimpleGraph β) where
  f : α ↪ β
  df (e : G.Dart) : H.Path (f e.fst) (f e.snd)
  --
  symm e : df e.symm = (df e).reverse
  ends {e x} : f x ∈ (df e).1.support ↔ x = e.fst ∨ x = e.snd
  disj {e e' v} : v ∈ (df e).1.support → v ∈ (df e').1.support → (e = e' ∨ e = e'.symm) ∨ v ∈ range f

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
    have h8 := p.dart_snd_mem_support_of_mem_darts he₁
    rcases φ.disj he₂ hu with h | ⟨x, rfl⟩ ; rcases h with rfl | rfl <;> assumption
    rcases φ.ends.1 hu with rfl | rfl ; swap ; contradiction
    rcases φ.ends.1 he₂ with rfl | rfl ; assumption
    exact p.dart_snd_mem_support_of_mem_darts he₁

def follow_path (p : G.Path x y) : H.Path (φ.f x) (φ.f y) :=
  ⟨φ.follow p.1, φ.isPath_follow p.isPath⟩

theorem toto {w : G.Walk x y} (hw : 0 < w.length) :
    z ∈ w.support ↔ ∃ e ∈ w.darts, z = e.fst ∨ z = e.snd := by
  induction w with
  | nil => contradiction
  | cons h p ih =>
    wlog h : 0 < p.length
    · cases p with
      | nil => simp
      | cons h p => simp at h
    simp only [Walk.support_cons, List.mem_cons, Walk.darts_cons, exists_eq_or_imp, ← ih h]
    grind [p.start_mem_support]

theorem length_pos {p : G.Walk x y} (h : x ≠ y) : 0 < p.length := by
  contrapose! h ; cases p ; rfl ; contradiction

theorem df_length_pos {e : G.Dart} : 0 < (φ.df e).1.length :=
  length_pos $ φ.f.injective.ne e.fst_ne_snd

def trans (φ : PathEmbedding G₁ G₂) (ψ : PathEmbedding G₂ G₃) : PathEmbedding G₁ G₃ where
  f := φ.f.trans ψ.f
  df e := ⟨ψ.follow (φ.df e), isPath_follow (φ.df e).isPath⟩
  symm e := by congr ; simp [φ.symm]
  ends := by simp [mem_follow df_length_pos, ψ.ends, ← toto df_length_pos, φ.ends]
  disj {e₁ e₂ a ha₁ ha₂} := by
    rw [mem_follow df_length_pos] at ha₁ ha₂
    obtain ⟨e'₁, he'₁, h'e'₁⟩ := ha₁
    obtain ⟨e'₂, he'₂, h'e'₂⟩ := ha₂
    have h1 := Walk.dart_fst_mem_support_of_mem_darts _ he'₁
    have h2 := Walk.dart_snd_mem_support_of_mem_darts _ he'₁
    have h3 := Walk.dart_fst_mem_support_of_mem_darts _ he'₂
    have h4 := Walk.dart_snd_mem_support_of_mem_darts _ he'₂
    rcases ψ.disj h'e'₁ h'e'₂ with (rfl | rfl) | ⟨x, rfl⟩
    · rcases φ.disj h1 h3 with (rfl | rfl) | ⟨x, h5⟩ ; simp ; simp
      rcases φ.disj h2 h4 with (rfl | rfl) | ⟨y, h6⟩ ; simp ; simp
      rw [← h5] at h1 h3 ; rw [← h6] at h2 h4 ; rw [φ.ends] at h1 h2 h3 h4
      have h7 := G₁.ne_of_adj e₁.adj ; have h8 := G₁.ne_of_adj e₂.adj
      rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> cases h3 <;> cases h4 <;>
        simp_all [Dart.ext_iff, Prod.ext_iff]
    · rcases φ.disj h1 h4 with (rfl | rfl) | ⟨x, h5⟩ ; simp ; simp
      rcases φ.disj h2 h3 with (rfl | rfl) | ⟨y, h6⟩ ; simp ; simp
      simp_all ; rw [← h5] at h1 h4 ; rw [← h6] at h2 h3 ; rw [φ.ends] at h1 h2 h3 h4
      have h7 := G₁.ne_of_adj e₁.adj ; have h8 := G₁.ne_of_adj e₂.adj
      rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> cases h3 <;> cases h4 <;>
        simp_all [Dart.ext_iff, Prod.ext_iff]
    · rw [ψ.ends] at h'e'₁ h'e'₂
      have h7 : x ∈ (φ.df e₁).1.support := by rcases h'e'₁ with rfl | rfl <;> assumption
      have h8 : x ∈ (φ.df e₂).1.support := by rcases h'e'₂ with rfl | rfl <;> assumption
      rcases φ.disj h7 h8 with (rfl | rfl) | ⟨y, rfl⟩ <;> simp

theorem IsTopologicalMinor.trans (h₁₂ : G₁ ≼t G₂) (h₂₃ : G₂ ≼t G₃) : G₁ ≼t G₃ := by
  obtain ⟨φ⟩ := h₁₂ ; obtain ⟨ψ⟩ := h₂₃ ; exact ⟨φ.trans ψ⟩

def of_hom (f : G →g H) (hf : Injective f) : PathEmbedding G H where
  f := ⟨f, hf⟩
  df e := .singleton $ f.map_rel e.adj
  symm e := rfl
  ends := by simp ; grind
  disj := by simp

end PathEmbedding
