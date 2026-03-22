import Mathlib.Combinatorics.SimpleGraph.Acyclic

open SimpleGraph Set Function

structure RTree where
  {support : Type*}
  root : support
  T : SimpleGraph support
  isTree : T.IsTree

namespace RTree

@[simp]
lemma map_tail {V W : Type*} {a b : V} {G : SimpleGraph V} {G' : SimpleGraph W} {p : G.Walk a b}
    {f : G →g G'} : (p.map f).tail = Walk.copy (p.tail.map f) (by simp) rfl := by
  induction p <;> simp

def subtree (T : RTree) (r : T.T.neighborSet T.root) : RTree := by
  let V : Set T.support := {T.root}ᶜ
  set G : SimpleGraph V := T.T.induce V
  let C := G.connectedComponentMk ⟨r, r.prop.ne.symm⟩
  refine ⟨⟨_, ConnectedComponent.connectedComponentMk_mem⟩, C.toSimpleGraph, ?_⟩
  constructor
  · exact C.connected_toSimpleGraph
  · let f := (induceUnivIso T.T).toHom |>.comp (induceHom .id (by tauto)) |>.comp C.toSimpleGraph_hom
    have hf : Injective f := by intro x y h ; ext ; exact h
    rintro u p
    have := T.isTree.2 (p.map f)
    simp [Walk.isCycle_iff_isPath_tail_and_le_length] at this ⊢
    grind [Walk.map_isPath_of_injective]

def subtrees (T : RTree) : Set RTree := range (subtree T)

end RTree
