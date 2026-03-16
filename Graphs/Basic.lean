import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Prod

namespace SimpleGraph

variable {α : Type*} {n : ℕ}

def Line : SimpleGraph ℤ where
  Adj x y := y = x + 1 ∨ y = x - 1
  loopless := ⟨fun x => by grind⟩

def Plane : SimpleGraph (ℤ × ℤ) := Line □ Line

def K5 := completeGraph (Fin 5)

def K33 := completeBipartiteGraph (Fin 3) (Fin 3)

def Star (a : α) : SimpleGraph α where
  Adj x y := x ≠ y ∧ (x = a ∨ y = a)

namespace Star

theorem reachable {a u : α} : (Star a).Reachable a u := by
  obtain (rfl | h) := eq_or_ne a u
  · rfl
  · exact ⟨Adj.toWalk ⟨h, .inl rfl⟩⟩

theorem isTree {a : α} : IsTree (Star a) := by
  have : Nonempty α := ⟨a⟩
  refine ⟨⟨fun u v => reachable.symm.trans reachable⟩, ?_⟩
  rw [isAcyclic_iff_forall_adj_isBridge]
  rintro u v ⟨h1, h2⟩
  wlog h : u = a ; grind [Sym2.eq_swap]
  subst u
  rw [Sym2.eq_swap]
  simp [IsBridge, Star, h1.symm]
  rintro ⟨p⟩
  cases p <;> simp at * ; grind

end Star

end SimpleGraph
