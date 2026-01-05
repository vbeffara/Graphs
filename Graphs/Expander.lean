import Mathlib
import Graphs.Basic

open SimpleGraph Matrix Classical Filter

variable {α : Type*} [Fintype α] [DecidableEq α] {i j : α} {G : SimpleGraph α}

namespace SimpleGraph

noncomputable def degreeMatrix (G : SimpleGraph α) (V : Type*) [NatCast V] [Zero V] : Matrix α α V :=
  of fun i j => if i = j then G.degree i else 0

noncomputable def laplacianMatrix (G : SimpleGraph α) (V : Type*) [NatCast V] [Zero V] [One V] [Sub V] :
    Matrix α α V :=
  G.degreeMatrix V - G.adjMatrix V

def edgeBoundary (G : SimpleGraph α) (S : Set α) : Set G.Dart := { e | e.fst ∈ S ∧ e.snd ∉ S }

def innerBoundary (G : SimpleGraph α) (S : Set α) : Set α := { y ∈ S | ∃ x ∉ S, G.Adj x y }

def outerBoundary (G : SimpleGraph α) (S : Set α) : Set α := { y ∉ S | ∃ x ∈ S, G.Adj x y }

def edgeExpandWith (G : SimpleGraph α) (h : ℝ) : Prop :=
  ∀ S : Finset α, S.Nonempty → 2 * S.card ≤ Fintype.card α →
    (G.edgeBoundary S).ncard ≥ h * Fintype.card S

def IsExpanderFamilyWith (G : ℕ → FiniteGraph) (h : ℝ) : Prop :=
  Tendsto (fun n => (G n).n) atTop atTop ∧ ∀ n, (G n).graph.edgeExpandWith h

theorem existExpander : ∃ (G : ℕ → FiniteGraph) (h : ℝ), IsExpanderFamilyWith G h := by
  -- Placeholder proof; the actual construction of expander families is nontrivial.
  sorry

-- The type is `Fin (Fintype.card (Fin G.n)) → ℝ` where `Fin G.n → ℝ` would be nicer but it requires
-- a cast, or I am missing something
noncomputable def eigenvalues (G : SimpleGraph α) :=
  isHermitian_iff_isSelfAdjoint.mpr (G.isSymm_adjMatrix (α := ℝ)) |>.eigenvalues₀

def spectrallyBoundedWith (G : SimpleGraph α) (Λ : ℝ) : Prop :=
  ∀ i, 0 < i.val → |G.eigenvalues i| < Λ

structure ndΛGraph (n d : ℕ) (Λ : ℝ) where
  G : SimpleGraph (Fin n)
  hd : ∀ i, G.degree i = d
  hΛ : spectrallyBoundedWith G Λ

end SimpleGraph
