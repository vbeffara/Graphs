import Mathlib.Combinatorics.SimpleGraph.Basic
import Untitled.Graphs.Map

set_option autoImplicit false

open Classical

variable {V : Type*} {S : Set V}

namespace Set

def merge_rel (S : Set V) (x y : V) : Prop := x = y ∨ (x ∈ S ∧ y ∈ S)

@[simp] lemma merge_equiv : Equivalence (merge_rel S) := by
  refine ⟨by simp [merge_rel], ?symm, ?trans⟩
  · rintro x y (rfl | h) <;> simp [*, Set.pair_comm _ x, merge_rel]
  · rintro x y z (rfl | h) (rfl | h) <;> simp [*, Set.pair_comm _ x, merge_rel]

def merge (S : Set V) : Type _ := Quotient ⟨merge_rel S, merge_equiv⟩

def merge_map (S : Set V) : V → S.merge := Quotient.mk''

end Set

namespace SimpleGraph

def merge (G : SimpleGraph V) (S : Set V) : SimpleGraph S.merge := G.map' S.merge_map

end SimpleGraph
