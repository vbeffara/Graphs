import Graphs.Contraction

open SimpleGraph

variable {α β γ : Type*} {G G' : SimpleGraph α} {H : SimpleGraph β} {K : SimpleGraph γ}

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

noncomputable def walk_in_subgraph {H : G.Subgraph} {x y} (hx : x ∈ H.verts) (hy : y ∈ H.verts)
    (p : G.Walk x y) (hp1 : ∀ z ∈ p.support, z ∈ H.verts) (hp2 : ∀ e ∈ p.darts, H.Adj e.fst e.snd) :
    H.coe.Walk ⟨x, hx⟩ ⟨y, hy⟩ := by
  induction p with
  | nil => exact Walk.nil
  | cons h p ih =>
    simp at hp1 hp2
    specialize ih (hp1.2 _ (Walk.start_mem_support _)) hy hp1.2 hp2.2
    refine Walk.cons ?_ ih
    simp [hp2]

theorem walk_in_support {H : G.Subgraph} {x y z} {hx : x ∈ H.verts} {hy} {p : G.Walk x y} {hp1 hp2}
    (h : z ∈ (walk_in_subgraph hx hy p hp1 hp2).support) :
    z.1 ∈ p.support := by
  induction p with
  | nil => simp [walk_in_subgraph] at h ; simp [h]
  | cons h p ih =>
    simp only [walk_in_subgraph, Walk.support_nil, Walk.darts_nil, Walk.support_cons,
      Walk.darts_cons, List.mem_cons] at h
    cases h with
    | inl h => simp only [Walk.support_cons, h, List.mem_cons, true_or]
    | inr h => simp only [Walk.support_cons, List.mem_cons, ih h, or_true]

theorem Adapted.restrict {α : Type u_1} {β : Type u_2} {H : SimpleGraph β}
  (L : H.Subgraph) (φ : ↑L.verts → α) (hφ₁ : Function.Surjective φ) (hφ₂ : L.coe.Adapted φ)
  (K : (map' φ L.coe).Subgraph) :
  let L' := Subgraph.coeSubgraph (comap'_subgraph' K);
  ∀ (hL' : L'.verts ⊆ L.verts) (key : ∀ {b : β}, b ∈ L'.verts ↔ ∃ (h : b ∈ L.verts), φ ⟨b, h⟩ ∈ K.verts),
    let ψ : L'.verts → K.verts := fun x ↦ ⟨φ ⟨x, hL' x.2⟩, key.1 x.2 |>.2⟩;
    L'.coe.Adapted ψ := by
  intro L' hL' key ψ
  rintro ⟨u, hu⟩ ⟨v, hv⟩ huv
  simp only [ψ] at *
  simp at huv
  obtain ⟨p, hp⟩ := hφ₂ huv
  let p' : H.Walk u v := p.map L.hom
  have hp'1 : ∀ z ∈ p'.support, z ∈ L'.verts := by
    simp [p']
    rintro z hz hzp
    simp [key, hz, hp _ hzp] at hv ⊢
    exact hv.2
  have hp'2 : ∀ e ∈ p'.darts, L'.Adj e.toProd.1 e.toProd.2 := by
    simp [p']
    rintro e he
    have h1 := hp _ $ SimpleGraph.Walk.dart_fst_mem_support_of_mem_darts p he
    have h2 := hp _ $ SimpleGraph.Walk.dart_snd_mem_support_of_mem_darts p he
    simp [key] at hu hv
    simpa [L', comap'_subgraph', comap'_subgraph, subgraph_inter, h1, hv.2, h2] using e.adj
  refine ⟨walk_in_subgraph hu hv p' hp'1 hp'2, ?_⟩
  simp [p', key]
  rintro w hw hw' hw''
  have := walk_in_support hw''
  simp only [Walk.support_map, Subgraph.coe_hom, List.map_subtype, List.map_id_fun', id_eq,
    List.mem_unattach] at this
  exact hp _ this.2

theorem subgraph_left (K : Subgraph G) (h : G ≼ H) : K.coe ≼ H := by
  obtain ⟨L, φ, hφ₁, hφ₂, rfl⟩ := h
  let L' := Subgraph.coeSubgraph (comap'_subgraph' K)
  have hL' : L'.verts ⊆ L.verts := by simp [L']
  have key {b : β} : b ∈ L'.verts ↔ ∃ h : b ∈ L.verts, φ ⟨b, h⟩ ∈ K.verts := by
    simp [L', comap'_subgraph', comap'_subgraph, subgraph_inter]
  let ψ (x : L'.verts) : K.verts := ⟨φ ⟨x, hL' x.2⟩, key.1 x.2 |>.2⟩
  refine ⟨L', ψ, ?_, ?_, ?_⟩
  · intro ⟨v, hv⟩
    obtain ⟨a, ha'⟩ := hφ₁ v
    refine ⟨⟨a, ?_⟩, by simp only [ψ, ha']⟩
    simp [key, ha', hv]
  · exact Adapted.restrict _ _ hφ₁ hφ₂ _ _ key
  · ext ⟨x, hx⟩ ⟨y, hy⟩
    constructor
    · intro h
      obtain ⟨hxy, a, b, h1, rfl, rfl⟩ := K.adj_sub h
      simp [L', comap'_subgraph', comap'_subgraph, subgraph_inter]
      simp only [Subgraph.coe_adj] at h
      refine ⟨by simpa, ⟨a, by simp [hx]⟩, ⟨b, by simp [hy]⟩, ?_, rfl, rfl⟩
      simpa [hx, hy, h1.ne, h] using h1
    · simp only [ψ]
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
