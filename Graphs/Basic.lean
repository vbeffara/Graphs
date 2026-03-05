import Mathlib

namespace SimpleGraph

variable {n : ℕ}

def Line : SimpleGraph ℤ where
  Adj x y := y = x + 1 ∨ y = x - 1
  loopless x := by grind

def Plane : SimpleGraph (ℤ × ℤ) := Line □ Line

def K5 := completeGraph (Fin 5)

def K33 := completeBipartiteGraph (Fin 3) (Fin 3)

def Star {α : Type*} (a : α) : SimpleGraph α where
  Adj x y := x ≠ y ∧ (x = a ∨ y = a)

end SimpleGraph
