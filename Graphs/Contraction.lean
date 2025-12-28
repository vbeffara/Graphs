import Mathlib
import Graphs.Map

open Function Set

variable {V V' V'' : Type*} {x y z : V} {x' y' z' : V'} {f : V → V'} {g : V' → V''}
variable {G H : SimpleGraph V} {G' H' : SimpleGraph V'} {G'' : SimpleGraph V''}

namespace SimpleGraph

/-! A function is adapted to a graph if its level sets are connected -/
def Adapted' (G : SimpleGraph V) (f : V → V') : Prop :=
  ∀ ⦃x y : V⦄, f x = f y → ∃ p : Walk G x y, ∀ z ∈ p.support, f z = f y

def Adapted (G : SimpleGraph V) (f : V → V') : Prop :=
  ∀ v, Preconnected (G.induce (f ⁻¹' {v}))

theorem adapted_iff_adapted' : Adapted G f ↔ Adapted' G f := by
  constructor
  · intro h x y hxy
    obtain ⟨p⟩ := h (f y) ⟨x, hxy⟩ ⟨y, rfl⟩
    use Walk.map (Embedding.induce _).toHom p
    simp only [Walk.support_map, List.mem_map]
    rintro z ⟨a, ha1, rfl⟩
    exact a.2
  · intro h x' ⟨x, hx⟩ ⟨y, hy⟩
    simp at hx hy
    subst hy
    obtain ⟨p, hp⟩ := h hx
    use p.induce (f ⁻¹' {f y}) hp

-- lemma merge_edge_adapted [DecidableEq V] {e : G.Dart} : G.Adapted (merge_edge e) := by
--   rintro x y hxy
--   by_cases hx : x = e.snd <;> by_cases hy : y = e.snd <;>
--     simp [merge_edge, Function.update, hx, hy] at hxy ⊢ <;> subst_vars
--   · use Walk.nil ; simp
--   · use Walk.nil.cons e.symm.is_adj ; simp
--   · use Walk.nil.cons e.is_adj ; simp
--   · use Walk.nil ; simp [hy]

namespace Adapted

lemma of_injective' (h : Injective f) : Adapted' G f := by
  rintro x y hxy ; rw [h hxy] ; exact ⟨Walk.nil, by simp⟩

lemma of_injective (h : Injective f) : Adapted G f := by
  rintro v ⟨x, hx⟩ ⟨y, hy⟩ ; simp only [h $ Eq.trans hx hy.symm, Reachable.rfl]

lemma id : Adapted G id := of_injective injective_id

noncomputable def lift_path (hf : Adapted G f) (p : Walk (map' f G) x' y') :
    ∀ x y, f x = x' → f y = y' → { q : Walk G x y // ∀ z ∈ q.support, f z ∈ p.support } := by
  rw [adapted_iff_adapted'] at hf
  induction p with
  | nil =>
    rintro x y hxy rfl
    choose q hq using hf hxy
    refine ⟨q, by simpa⟩
  | cons h p ih =>
    rintro x y rfl rfl
    obtain ⟨h1, h2⟩ := h
    have := h2 ; choose a b h3 h4 h5 using this
    subst h5
    obtain ⟨q₂, hq₂⟩ := ih b y rfl rfl
    choose q₁ hq₁ using hf h4.symm
    refine ⟨q₁.append (q₂.cons h3), ?_⟩
    intro z hz
    simp only [Walk.mem_support_append_iff, Walk.support_cons, List.mem_cons] at hz
    obtain h | h | h := hz <;> simp_all

noncomputable def lift_path' (hf : Adapted G f) (p : Walk (map' f G) (f x) (f y)) :
    { q : Walk G x y // ∀ z ∈ q.support, f z ∈ p.support } :=
  lift_path hf p x y rfl rfl

theorem comp (hf : Adapted G f) (hg : Adapted (map' f G) g) : Adapted G (g ∘ f) := by
  rw [adapted_iff_adapted'] at hg ⊢
  intro x y hxy
  obtain ⟨p, hp⟩ := hg hxy
  exact ⟨lift_path' hf p, by grind⟩

-- -- lemma connected (hf : Adapted f G) (hc : connected (map f G)) : preconnected G :=
-- -- begin
-- --   intros x y, obtain ⟨p⟩ := hc (f x) (f y), use lift_path' hf p
-- -- end

-- -- lemma fmap (hf : Adapted f G) {P} : Adapted (select.fmap f P) (select (P ∘ f) G) :=
-- -- begin
-- --   rintro ⟨x,hx⟩ ⟨y,hy⟩ hxy, simp only [select.fmap, subtype.coe_mk] at hxy,
-- --   obtain ⟨p,hp⟩ := hf hxy, refine ⟨select.push_walk p _, _⟩,
-- --   { rintro z hz, rw ← hp z hz at hy, exact hy },
-- --   rintro ⟨z,hz⟩ h, simp only [select.fmap, subtype.coe_mk],
-- --   exact hp z (select.mem_push_walk.mp h)
-- -- end

-- -- lemma comp_push : Adapted f G → Adapted g (map f G) → Adapted (g ∘ f) G :=
-- -- begin
-- --   rintro hf hg x y hxy, obtain ⟨p, hp⟩ := hg hxy,
-- --   exact ⟨Adapted.lift_path' hf p, λ z hz, hp (f z) (Adapted.mem_lift_path' hz)⟩,
-- -- end

end Adapted

def IsContraction (G : SimpleGraph V) (G' : SimpleGraph V') : Prop :=
∃ φ : V' → V, Surjective φ ∧ Adapted G' φ ∧ G = G'.map' φ

infix:50 " ≼c " => IsContraction

namespace IsContraction

@[refl] theorem refl : G ≼c G := ⟨id, surjective_id, Adapted.id, map'_id.symm⟩

lemma iso_left (h1 : G ≃g G') (h2 : G' ≼c G'') : G ≼c G'' := by
  obtain ⟨φ, h3, h4, rfl⟩ := h2
  refine ⟨h1.toEquiv.symm ∘ φ, by simpa using h3, ?_, ?_⟩
  · intro v
    rw [preimage_comp, ← Equiv.image_eq_preimage_symm, image_singleton]
    apply h4
  · ext x y
    constructor
    · intro h
      have := h1.map_rel_iff.2 h
      obtain ⟨huv, u, v, h5, h6, h7⟩ := this
      refine ⟨h.ne, u, v, h5, ?_, ?_⟩
      · simp [h6]
        exact h1.symm_apply_apply x
      · simp [h7]
        exact h1.symm_apply_apply y
    · rintro ⟨h5, u, v, h6, rfl, rfl⟩
      rw [← h1.map_rel_iff]
      refine ⟨h1.injective.ne h5, u, v, h6, ?_, ?_⟩
      · exact h1.apply_symm_apply (φ u) |>.symm
      · exact h1.apply_symm_apply (φ v) |>.symm

lemma iso_right (h1 : G ≼c G') (h2 : G' ≃g G'') : G ≼c G'' := by
  obtain ⟨φ, h3, h4, rfl⟩ := h1
  refine ⟨φ ∘ h2.toEquiv.symm, by simp [h3], ?_⟩

  all_goals sorry

-- -- lemma of_iso : G ≃g G' → G ≼c G' :=
-- -- λ φ, let ψ := φ.symm in ⟨ψ, ψ.surjective, Adapted.of_injective ψ.injective, map.from_iso ψ⟩

-- -- @[trans] lemma trans : G ≼c G' → G' ≼c G'' → G ≼c G'' :=
-- -- begin
-- --   rintros ⟨φ,h₁,h₂,rfl⟩ ⟨ψ,h₄,h₅,rfl⟩,
-- --   exact ⟨φ ∘ ψ, h₁.comp h₄, h₅.comp_push h₂, congr_fun map.comp.symm G''⟩,
-- -- end

-- -- lemma iso_left : G ≃g G' -> G' ≼c G'' -> G ≼c G'' :=
-- -- trans ∘ of_iso

-- -- lemma le_left_aux {f : V → V'} : H' ≤ map f G → H' = map f (G ⊓ pull' f H') :=
-- -- begin
-- --   intro h₁, ext x' y', split,
-- --   { intro h, rcases h₁ h with ⟨h₄,x,y,h₅,rfl,rfl⟩,
-- --     exact ⟨h₄,x,y,⟨h₅,h₄ ∘ congr_arg f,or.inr h⟩,rfl,rfl⟩ },
-- --   { rintros ⟨h₄,x,y,⟨-,-,h₇⟩,rfl,rfl⟩, cases h₇, contradiction, exact h₇ }
-- -- end

-- -- lemma le_left_aux2 {f : V → V'} (h₁ : H' ≤ map f G) (h₂ : surjective f) (h₃ : Adapted f G) :
-- --   H' ≼c G ⊓ pull' f H' :=
-- -- begin
-- --   refine ⟨f,h₂,_,le_left_aux h₁⟩,
-- --   intros x' y' h₄, specialize h₃ h₄,
-- --   cases h₃ with p hp, induction p with a a b c h₅ p ih,
-- --   { use walk.nil, exact hp },
-- --   { have h₆ : f b = f c := by { apply hp, right, exact walk.start_mem_support p },
-- --     have h₇ : ∀ (z : V), z ∈ p.support → f z = f c := by { intros z h, apply hp, right, exact h},
-- --     have h₈ : (G ⊓ pull' f H').adj a b :=
-- --       by { split, exact h₅, refine ⟨G.ne_of_adj h₅,_⟩, left, rwa h₆ },
-- --     specialize ih h₆ h₇, cases ih with q h₉, use walk.cons h₈ q,
-- --     intros z h, cases h, rwa h, exact h₉ z h }
-- -- end

-- -- lemma le_left : H ≤ G → G ≼c G' → ∃ H' : SimpleGraph V', H ≼c H' ∧ H' ≤ G' :=
-- -- by { rintros h₁ ⟨f,h₂,h₃,rfl⟩, exact ⟨G' ⊓ pull' f H, le_left_aux2 h₁ h₂ h₃, λ x y h, h.1⟩ }

-- -- lemma select_left {P : V → Prop} : G ≼c G' -> ∃ P' : V' → Prop, select P G ≼c select P' G' :=
-- -- begin
-- --   rintros ⟨f,h₁,h₂,h₃⟩, use (λ x, P (f x)), refine ⟨select.fmap f P, _, h₂.fmap, _⟩,
-- --   { rintro ⟨x,py⟩, cases h₁ x with x', refine ⟨⟨x',_⟩,_⟩, rwa h, ext, exact h },
-- --   { ext ⟨x,hx⟩ ⟨y,hy⟩, simp only [select, pull, on_fun, subtype.val_eq_coe], split,
-- --     { intro h₄, rw h₃ at h₄, rcases h₄ with ⟨h₄,x',y',h₅,h₆,h₇⟩,
-- --       simp only [subtype.coe_mk] at h₆ h₇, substs h₆ h₇,
-- --       refine ⟨_,⟨x',hx⟩,⟨y',hy⟩,h₅,rfl,rfl⟩,
-- --       intro h, rw subtype.ext_iff at h, contradiction },
-- --     { rintros ⟨h₄,⟨x',hx⟩,⟨y',hy⟩,h₅,h₆,h₇⟩, rw h₃, refine ⟨_,x',y',h₅,_,_⟩,
-- --       { intro h, rw ←subtype.ext_iff at h, contradiction },
-- --       { simp only [select.fmap, subtype.map] at h₆, exact h₆ },
-- --       { simp only [select.fmap, subtype.map] at h₇, exact h₇ } } }
-- -- end

end IsContraction

end SimpleGraph
