import Mathlib
import Graphs.Basic

open SimpleGraph Matrix Classical Filter

variable {α : Type*} {i j : α} {G : SimpleGraph α} {β : ℕ → Type*} [∀ n, Fintype (β n)]

namespace SimpleGraph

noncomputable def degreeMatrix (G : SimpleGraph α) [LocallyFinite G]
    (V : Type*) [NatCast V] [Zero V] : Matrix α α V :=
  of fun i j => if i = j then G.degree i else 0

noncomputable def laplacianMatrix (G : SimpleGraph α) [LocallyFinite G]
    (V : Type*) [NatCast V] [Zero V] [One V] [Sub V] : Matrix α α V :=
  G.degreeMatrix V - G.adjMatrix V

def dartsBetween (G : SimpleGraph α) (S T : Set α) : Set G.Dart := { e | e.fst ∈ S ∧ e.snd ∈ T }

def edgeBoundary (G : SimpleGraph α) (S : Set α) : Set G.Dart := G.dartsBetween S Sᶜ

def innerBoundary (G : SimpleGraph α) (S : Set α) : Set α := { y ∈ S | ∃ x ∉ S, G.Adj x y }

def outerBoundary (G : SimpleGraph α) (S : Set α) : Set α := { y ∉ S | ∃ x ∈ S, G.Adj x y }

def edgeExpandWith [Fintype α] (G : SimpleGraph α) (h : ℝ) : Prop :=
  ∀ S : Finset α, S.Nonempty → 2 * S.card ≤ Fintype.card α →
    (G.edgeBoundary S).ncard ≥ h * Fintype.card S

def IsExpanderFamilyWith (G : ∀ n, SimpleGraph (β n)) (h : ℝ) : Prop :=
  Tendsto (fun n => Fintype.card (β n)) atTop atTop ∧ ∀ n, (G n).edgeExpandWith h

theorem existExpander :
    ∃ (α : ℕ → Type*) (hα : ∀ n, Fintype (α n)) (G : ∀ n, SimpleGraph (α n)) (h : ℝ),
    0 < h ∧ IsExpanderFamilyWith G h := by
  -- Placeholder proof; the actual construction of expander families is nontrivial.
  sorry

-- The type is `Fin (Fintype.card (Fin G.n)) → ℝ` where `Fin G.n → ℝ` would be nicer but it requires
-- a cast, or I am missing something
noncomputable def eigenvalues [Fintype α] (G : SimpleGraph α):=
  isHermitian_iff_isSelfAdjoint.mpr (G.isSymm_adjMatrix (α := ℝ)) |>.eigenvalues₀

def IsSpectrallyBoundedWith [Fintype α] (G : SimpleGraph α) (Λ : ℝ) : Prop :=
  ∀ i, 0 < i.val → |G.eigenvalues i| < Λ

def IsNDΛGraph [Fintype α] (n d : ℕ) (Λ : ℝ) (G : SimpleGraph α) : Prop :=
  (Fintype.card α = n) ∧ (G.IsRegularOfDegree d) ∧ (G.IsSpectrallyBoundedWith Λ)

end SimpleGraph
