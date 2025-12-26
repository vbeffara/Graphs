import Mathlib

set_option autoImplicit false

open Function Classical Set Finset

variable {V V' V'' : Type*}
variable {G H : SimpleGraph V} {G' : SimpleGraph V'} {G'' : SimpleGraph V''}

namespace SimpleGraph

def is_smaller (G : SimpleGraph V) (G' : SimpleGraph V') : Prop :=
  ∃ f : G →g G', Injective f

infix:50 " ≼s " => is_smaller

namespace is_smaller

lemma of_le (h : G ≤ H) : G ≼s H := ⟨⟨id, (h ·)⟩, injective_id⟩

lemma of_iso : G ≃g G' → G ≼s G' := λ ⟨⟨f, _, h1, _⟩, h3⟩ => ⟨⟨f, h3.2⟩, h1.injective⟩

@[refl] lemma refl : G ≼s G := ⟨⟨id, id⟩, injective_id⟩

@[trans] lemma trans : G ≼s G' → G' ≼s G'' → G ≼s G'' :=
  λ ⟨f₁, h₁⟩ ⟨f₂, h₂⟩ => ⟨f₂.comp f₁, h₂.comp h₁⟩

lemma iso_left (h1 : G ≃g G') (h2 : G' ≼s G'') : G ≼s G'' := of_iso h1 |>.trans h2

lemma le_left (h1 : G ≤ H) (h2 : H ≼s G') : G ≼s G' := of_le h1 |>.trans h2

lemma iso_right (h1 : G ≼s G') (h2 : G' ≃g G'') : G ≼s G'' := h1.trans (of_iso h2)
