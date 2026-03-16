import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Prod
import Graphs.Tree

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

theorem isTree (a : α) : IsTree (Star a) := by
  have : Nonempty α := ⟨a⟩
  refine ⟨⟨fun u v => reachable.symm.trans reachable⟩, ?_⟩
  rw [isAcyclic_iff_forall_adj_isBridge]
  rintro u v ⟨h1, h2⟩
  wlog h : v = a ; grind [Sym2.eq_swap]
  subst v
  simp [IsBridge, Star, h1]
  rintro ⟨p⟩
  cases p <;> simp at * ; grind

@[simp] theorem path_to_root {u a : α} (h1 : u ≠ a) : ((isTree a).path u a).1.support = [u, a] := by
  let p : (Star a).Walk u a := .cons ⟨h1, .inr rfl⟩ .nil
  simp [(isTree a).path_spec ⟨p, by simp [p] ; grind⟩, p]

@[simp] theorem path_of_ne {u v a : α} (h1 : u ≠ a) (h2 : v ≠ a) (h3 : u ≠ v) :
    ((isTree a).path u v).1.support = [u, a, v] := by
  let p : (Star a).Walk u v := .cons ⟨h1, .inr rfl⟩ $ .cons ⟨h2.symm, .inl rfl⟩ .nil
  simp [(isTree a).path_spec ⟨p, by simp [p] ; grind⟩, p]

@[simp] theorem between {a x y z : α} : (isTree (a := a)).ordered x y z ↔
    (x = y) ∨ (y = z) ∨ (x ≠ z ∧ y = a) := by
  obtain (rfl | h1) := eq_or_ne x y ; simp ; simp [h1]
  obtain (rfl | h2) := eq_or_ne y z ; simp ; simp [h2]
  obtain (rfl | h3) := eq_or_ne x z ; simp [h2] ; simp [IsTree.ordered]
  obtain (rfl | h5) := eq_or_ne a z ; simp [h3, h1.symm]
  obtain (rfl | h6) := eq_or_ne a x ; simp [IsTree.path_symm (u := a), h3.symm, h2, h3]
  simp [path_of_ne, h6.symm, h5.symm, h3, h1.symm, h2]

end Star

end SimpleGraph
