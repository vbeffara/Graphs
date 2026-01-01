import Graphs.Contraction

open SimpleGraph Subgraph

variable {α β β : Type*} {G G' : SimpleGraph α} {H : SimpleGraph β} {K : SimpleGraph β}

def IsMinor (G : SimpleGraph α) (H : SimpleGraph β) : Prop :=
  ∃ K : Subgraph H, G ≼c K.coe

def IsForbidden (G : SimpleGraph α) (H : SimpleGraph β) : Prop :=
  ¬ (IsMinor G H)

infix:50 " ≼ " => IsMinor
infix:50 " ⋠ " => IsForbidden

namespace IsMinor

@[refl] theorem refl : G ≼ G := ⟨⊤, .iso_left Subgraph.topIso.symm .refl⟩

theorem ofIso (h : G ≃g H) : G ≼ H := by
  refine ⟨⊤, .ofIso $ topIso.symm.comp h⟩

theorem ofSubgraph (K : Subgraph H) : K.coe ≼ H := ⟨K, .refl⟩

theorem ofContraction (h : G ≼c H) : G ≼ H := ⟨⊤, .iso_right h Subgraph.topIso.symm⟩

theorem contract_left (h1 : G ≼c H) (h2 : H ≼ K) : G ≼ K := by
  obtain ⟨L, hL⟩ := h2
  refine ⟨L, h1.trans hL⟩

theorem subgraph_left (K : Subgraph G) (h : G ≼ H) : K.coe ≼ H := by
  obtain ⟨L, φ, hφ₁, hφ₂, rfl⟩ := h
  refine ⟨Adapted.L' φ K, Adapted.ψ φ K, ?_, ?_, ?_⟩
  · intro ⟨v, hv⟩
    obtain ⟨a, ha'⟩ := hφ₁ v
    refine ⟨⟨a, ?_⟩, by simp only [Adapted.ψ, ha']⟩
    simp [Adapted.key', ha', hv]
  · exact Adapted.restrict _ hφ₂ _
  · ext ⟨x, hx⟩ ⟨y, hy⟩
    constructor
    · intro h
      obtain ⟨hxy, a, b, h1, rfl, rfl⟩ := K.adj_sub h
      simp [Adapted.L', comap'_subgraph', comap'_subgraph, subgraph_inter]
      simp only [Subgraph.coe_adj] at h
      refine ⟨by simpa, ⟨a, by simp [hx]⟩, ⟨b, by simp [hy]⟩, ?_, rfl, rfl⟩
      simpa [hx, hy, h1.ne, h] using h1
    · unfold Adapted.ψ
      rintro ⟨h, ⟨a, ha⟩, ⟨b, hb⟩, hab, h1, h2⟩
      obtain ⟨c, d, ⟨⟨h3, h4, h5, h6⟩⟩, rfl, rfl⟩ := hab
      simp_all

theorem trans (h1 : G ≼ H) (h2 : H ≼ K) : G ≼ K := by
  obtain ⟨L₁, hL₁⟩ := h1
  obtain ⟨L', hL'⟩ := subgraph_left L₁ h2
  exact ⟨L', hL₁.trans hL'⟩

end IsMinor

-- universe u
-- variables {V V' V'' : Type u}
-- variables {G H : simple_graph V} {G' : simple_graph V'} {G'' : simple_graph V''}

-- namespace is_minor

-- lemma le_left : G ≤ H -> H ≼ G' -> G ≼ G' :=
-- begin
--   rintro h₁ ⟨U,H',h₂,h₃⟩,
--   obtain ⟨H'',h₄,h₅⟩ := h₂.le_left h₁,
--   exact ⟨_,_,h₄,h₃.le_left h₅⟩
-- end

-- lemma select_left {P : V → Prop} : G ≼ G' -> select P G ≼ G' :=
-- begin
--   rintro ⟨U,H',h₂,h₃⟩,
--   obtain ⟨P,h₄⟩ := h₂.select_left,
--   exact ⟨_,_,h₄,h₃.select_left⟩
-- end

-- lemma smaller_left : G ≼s G' -> G' ≼ G'' -> G ≼ G'' :=
-- begin
--   rintro ⟨f₁,h₁⟩ h₂,
--   let H := embed f₁ G,
--   let H' := select (set.range f₁) G',
--   have h₃ : H' ≼ G'' := select_left h₂,
--   have h₄ : H ≼ G'' := le_left (embed.le_select h₁) h₃,
--   exact iso_left (embed.iso h₁) h₄
-- end

-- lemma contract_left : G ≼c G' -> G' ≼ G'' -> G ≼ G'' :=
-- λ h₁ ⟨U,H,h₂,h₃⟩, ⟨_,_,h₁.trans h₂,h₃⟩

-- @[refl] lemma refl : G ≼ G
-- := ⟨_,G,is_contraction.refl,is_smaller.refl⟩

-- @[trans] lemma trans : G ≼ G' -> G' ≼ G'' -> G ≼ G'' :=
-- λ ⟨U,H,h1,h2⟩ h3, is_minor.contract_left h1 (is_minor.smaller_left h2 h3)

-- end is_minor
-- end simple_graph
