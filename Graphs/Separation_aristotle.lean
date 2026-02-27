/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 88416cec-5262-4c1f-8fba-74d98fdee2c6

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem separates_cover (h : A ∪ B = univ) : G.Separates A B S ↔
    ((A ∩ B ⊆ S) ∧ (∀ u ∈ A, ∀ v ∈ B, G.Adj u v → u ∈ S ∨ v ∈ S))
-/

import Mathlib


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
    aesop;
    cases h p <;> simp_all +decide [ SimpleGraph.Walk.support_cons ];
    cases h_separates.2 v hu p ‹_› ‹_› <;> aesop

end SimpleGraph