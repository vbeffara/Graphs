import Mathlib

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
  let g : V := ⟨r, r.prop.ne.symm⟩
  let C := G.connectedComponentMk g
  refine ⟨⟨g, ConnectedComponent.connectedComponentMk_mem⟩, C.toSimpleGraph, ?_⟩
  constructor
  · exact C.connected_toSimpleGraph
  · let f1 : C.toSimpleGraph →g G := C.toSimpleGraph_hom
    let f2 : G →g T.T.induce ⊤ := induceHom .id (by tauto)
    let f3 : T.T.induce ⊤ →g T.T := induceUnivIso T.T
    let f : C.toSimpleGraph →g T.T := f3.comp (f2.comp f1)
    have hf : Injective f := by
      intro x y
      simp [f, f1, f2, f3, induceHom, ConnectedComponent.toSimpleGraph_hom]
      grind
    rintro u p
    have key := T.isTree.2
    let q := p.map f
    have := key q
    simp [q, Walk.isCycle_iff_isPath_tail_and_le_length] at this ⊢
    grind [Walk.map_isPath_of_injective]

def subtrees (T : RTree) : Set RTree := range (subtree T)

end RTree
