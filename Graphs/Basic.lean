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
  intro u p hp
  cases p with
  | nil => simp at hp
  | cons h1 p =>
    simp [Star, Walk.cons_isCycle_iff] at h1 hp
    cases p with
    | nil => simp at h1
    | cons h2 p =>
      simp [Star] at h2 p hp
      cases p with
      | nil =>
        simp at hp
      | cons h3 p =>
        cases p with
        | nil => simp at * ; grind
        | cons h4 p => simp at * ; grind

end Star

end SimpleGraph
