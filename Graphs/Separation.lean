import Mathlib.Combinatorics.SimpleGraph.Walks.Basic
import Mathlib.Tactic

open SimpleGraph Set

variable {V : Type*} {G : SimpleGraph V} {A B S : Set V}

namespace SimpleGraph

/-
A set of vertices S separates A from B in G if every A-B path in G contains a vertex from S.
-/
def Separates (G : SimpleGraph V) (A B : Set V) (S : Set V) : Prop :=
  ∀ u ∈ A, ∀ v ∈ B, ∀ p : G.Walk u v, ∃ x ∈ p.support, x ∈ S

theorem separates_cover (h : A ∪ B = univ) : G.Separates A B S ↔
    ((A ∩ B ⊆ S) ∧ (∀ u ∈ A, ∀ v ∈ B, G.Adj u v → u ∈ S ∨ v ∈ S)) := by
  constructor <;> intro h_separates <;> simp_all +decide [ Set.ext_iff ];
  · refine' ⟨ fun x hx => _, fun u hu v hv huv => _ ⟩;
    · specialize h_separates x hx.1 x hx.2 ( SimpleGraph.Walk.nil ) ; aesop;
    · cases h_separates u hu v hv ( SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil ) ; aesop;
  · intro u hu v hv p
    induction' p with u v p ih
    · aesop
    · cases h p <;> simp_all +decide [ SimpleGraph.Walk.support_cons ];
      cases h_separates.2 v hu p ‹_› ‹_› <;> aesop

end SimpleGraph
