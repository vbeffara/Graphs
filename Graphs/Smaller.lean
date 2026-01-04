import Mathlib.Combinatorics.SimpleGraph.Subgraph

open Function Classical Set Finset SimpleGraph

variable {α β γ : Type*}
variable {G G' : SimpleGraph α} {H : SimpleGraph β} {K : SimpleGraph γ}

namespace SimpleGraph

def IsSmaller (G : SimpleGraph α) (H : SimpleGraph β) : Prop :=
  ∃ f : G →g H, Injective f

infix:50 " ≼s " => IsSmaller

namespace IsSmaller

lemma of_le (h : G ≤ G') : G ≼s G' := ⟨⟨id, (h ·)⟩, injective_id⟩

lemma of_iso : G ≃g H → G ≼s H := λ ⟨⟨f, _, h1, _⟩, h3⟩ => ⟨⟨f, h3.2⟩, h1.injective⟩

@[refl] lemma refl : G ≼s G := ⟨⟨id, id⟩, injective_id⟩

@[trans] lemma trans : G ≼s H → H ≼s K → G ≼s K :=
  λ ⟨f₁, h₁⟩ ⟨f₂, h₂⟩ => ⟨f₂.comp f₁, h₂.comp h₁⟩

lemma iso_left (h1 : G ≃g H) (h2 : H ≼s K) : G ≼s K := of_iso h1 |>.trans h2

lemma le_left (h1 : G ≤ G') (h2 : G' ≼s H) : G ≼s H := of_le h1 |>.trans h2

lemma iso_right (h1 : G ≼s H) (h2 : H ≃g K) : G ≼s K := h1.trans (of_iso h2)

end IsSmaller

end SimpleGraph
