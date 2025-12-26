import Mathlib

set_option autoImplicit false

variable {V : Type*} {G : SimpleGraph V}

namespace Finset

@[simp] lemma singleton_inter_nonempty [DecidableEq V] {a : V} {X : Finset V} :
    ({a} ∩ X).Nonempty ↔ a ∈ X where
  mp := by
    simp [nonempty_iff_ne_empty]
    contrapose!
    exact singleton_inter_of_not_mem
  mpr h := by use a ; simp [h]

end Finset

namespace SimpleGraph

lemma reachable.step {x y : V} : G.Adj x y → Reachable G x y := Adj.reachable

end SimpleGraph
