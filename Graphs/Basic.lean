import Mathlib

namespace SimpleGraph

variable {n : ℕ}

def Segment (n : ℕ) : SimpleGraph (Fin n) where
  Adj x y := x.val + 1 = y.val ∨ x.val = y.val + 1
  loopless x := by grind

theorem Segment.isTree : (Segment n).IsTree := by
  sorry

def Cycle (n : ℕ) : SimpleGraph (Fin n) where
  Adj x y := x ≠ y ∧ (x.val + 1 ≡ y.val [MOD n] ∨ y.val + 1 ≡ x.val [MOD n])
  loopless x := by tauto

def Line : SimpleGraph ℤ where
  Adj x y := y = x + 1 ∨ y = x - 1
  loopless x := by grind

def Plane : SimpleGraph (ℤ × ℤ) := Line □ Line

def K5 := completeGraph (Fin 5)

def K33 := completeBipartiteGraph (Fin 3) (Fin 3)

end SimpleGraph
