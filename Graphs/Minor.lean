import Graphs.Contraction

open SimpleGraph

variable {α β β : Type*} {G G' : SimpleGraph α} {H : SimpleGraph β} {K : SimpleGraph β}

def IsMinor (G : SimpleGraph α) (H : SimpleGraph β) : Prop :=
  ∃ K : Subgraph H, G ≼c K.coe

def IsForbidden (G : SimpleGraph α) (H : SimpleGraph β) : Prop :=
  ¬ (IsMinor G H)

infix:50 " ≼ " => IsMinor
infix:50 " ⋠ " => IsForbidden

namespace IsMinor

@[refl] theorem refl : G ≼ G := ⟨⊤, .iso_left Subgraph.topIso.symm .refl⟩

theorem iso_left : G ≃g H → H ≼ K → G ≼ K :=
  fun h1 ⟨L, hL⟩ => ⟨L, .iso_left h1 hL⟩

theorem ofIso (h : G ≃g H) : G ≼ H :=
  iso_left h .refl

theorem ofSubgraph (K : Subgraph H) : K.coe ≼ H := ⟨K, .refl⟩

theorem ofContraction (h : G ≼c H) : G ≼ H := ⟨⊤, .iso_right h Subgraph.topIso.symm⟩

theorem contract_left (h1 : G ≼c H) (h2 : H ≼ K) : G ≼ K := by
  obtain ⟨L, hL⟩ := h2
  refine ⟨L, h1.trans hL⟩

@[simp] theorem key₀ {φ : β → α} {K : G.Subgraph} :
    (comap'_subgraph φ K).verts = φ ⁻¹' K.verts := by
  rfl

@[simp] theorem key₀' {φ : β → α} {K : (map' φ H).Subgraph} :
    (comap'_subgraph' K).verts = φ ⁻¹' K.verts := by
  rfl

theorem key {φ : β → α} (K : (map' φ H).Subgraph) {b : β} :
    b ∈ (comap'_subgraph' K).verts ↔ φ b ∈ K.verts := by
  simp

def Adapted.L' {L : H.Subgraph} (φ : ↑L.verts → α) (K : (map' φ L.coe).Subgraph) : H.Subgraph :=
    Subgraph.coeSubgraph (comap'_subgraph' K)

theorem Adapted.hL' {L : H.Subgraph} (φ : ↑L.verts → α) (K : (map' φ L.coe).Subgraph) :
    (L' φ K).verts ⊆ L.verts := by
  simp [L']

theorem Adapted.key' {L : H.Subgraph} (φ : ↑L.verts → α) (K : (map' φ L.coe).Subgraph) ⦃b : β⦄ :
    b ∈ (L' φ K).verts ↔ ∃ (h : b ∈ L.verts), φ ⟨b, h⟩ ∈ K.verts := by
  simp [L']

def Adapted.ψ {L : H.Subgraph} (φ : ↑L.verts → α) (K : (map' φ L.coe).Subgraph) :
    (L' φ K).verts → K.verts :=
  fun x ↦ ⟨φ ⟨x, hL' φ K x.2⟩, (key' φ K).1 x.2 |>.2⟩

theorem Adapted.restrict₀ {φ : β → α} (hφ₂ : H.Adapted φ) (K : (map' φ H).Subgraph) :
    (comap'_subgraph' K).coe.Adapted (fun x ↦ (⟨φ x, x.2⟩ : K.verts)) := by
  rintro ⟨u, hu⟩ ⟨v, hv⟩ huv
  simp at huv
  obtain ⟨p, hp⟩ := hφ₂ huv
  have hp'1 z (hz : z ∈ p.support) : z ∈ (comap'_subgraph' K).verts := by simpa [hz, hp _] using hv
  have hp'2 e (he : e ∈ p.darts) : (comap'_subgraph' K).Adj e.toProd.1 e.toProd.2 := by
    refine ⟨?_, Dart.adj e⟩
    have h1 := hp _ $ SimpleGraph.Walk.dart_fst_mem_support_of_mem_darts p he
    have h2 := hp _ $ SimpleGraph.Walk.dart_snd_mem_support_of_mem_darts p he
    simpa [comap'_subgraph, h1, h2] using hv
  exact ⟨(comap'_subgraph' K).attach p hp'1 hp'2, by { simp ; grind }⟩

-- This looks too similar to the previous one, should merge?
theorem Adapted.restrict {L : H.Subgraph} (φ : ↑L.verts → α) (hφ₂ : L.coe.Adapted φ)
    (K : (map' φ L.coe).Subgraph) :
    (L' φ K).coe.Adapted (ψ φ K) := by
  rintro ⟨u, hu⟩ ⟨v, hv⟩ huv
  simp [ψ] at huv
  obtain ⟨p, hp⟩ := hφ₂ huv
  refine ⟨Subgraph.attach _ (p.map L.hom) ?_ ?_, ?_⟩
  · simp [L'] at hv ⊢ ; grind
  · simp [L'] at hv ⊢
    rintro e he
    have h1 := hp _ $ SimpleGraph.Walk.dart_fst_mem_support_of_mem_darts p he
    have h2 := hp _ $ SimpleGraph.Walk.dart_snd_mem_support_of_mem_darts p he
    simpa [comap'_subgraph', comap'_subgraph, subgraph_inter, h1, hv.2, h2] using e.adj
  · simp [ψ] ; grind

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
