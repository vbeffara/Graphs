/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: c3da253a-f840-4a15-8c73-59efe48a8cae

The following was proved by Aristotle:

- theorem Higman (h : WellQuasiOrderedLE α) : WellQuasiOrdered (FinsetLE (α
-/

import Mathlib
import Batteries.Tactic.GeneralizeProofs
import Graphs.WQO

open List

variable {α : Type*} [PartialOrder α] {s t : Finset α} {l1 l2 : List α}

lemma lemma_1 (h : SublistForall₂ (· ≤ ·) l1 l2) : ∃ f : Fin l1.length ↪ Fin l2.length,
    StrictMono f ∧ ∀ i, l1[i] ≤ l2[f i] := by
  obtain ⟨l, h1, h2⟩ := sublistForall₂_iff.mp h
  obtain ⟨f, h3⟩ := sublist_iff_exists_fin_orderEmbedding_get_eq.mp h2
  obtain h4 := h1.length_eq
  refine ⟨⟨f ∘ Fin.cast h4, ?_⟩, ?_, fun i => ?_⟩
  · simp_all [Function.Injective]
  · simp_all [StrictMono]
  · let i' := i.cast h4; exact le_of_le_of_eq ((forall₂_iff_get.mp h1).2 i i.2 i'.2) (h3 i')

lemma lemma_2 (h : SublistForall₂ (· ≤ ·) s.toList t.toList) :
    ∃ f : Fin s.card → Fin t.card, StrictMono f ∧ ∀ i, s.toList[i] ≤ t.toList[f i] := by
  obtain ⟨is, his⟩ := lemma_1 h
  refine ⟨Fin.cast (by simp) ∘ is ∘ Fin.cast (by simp), ?_, fun i => ?_⟩
  · simp_all [Fin.cast, StrictMono]
  · exact his.2 (Fin.cast (by simp) i)

lemma lemma_3 (h : SublistForall₂ (· ≤ ·) s.toList t.toList) :
    ∃ f : Fin s.card → t, Function.Injective f ∧ ∀ i, s.toList[i] ≤ f i := by
  obtain ⟨is, his, his'⟩ := lemma_2 h
  use fun i => ⟨t.toList[is i], Finset.mem_toList.mp (by simp)⟩
  simp_all +decide [ Function.Injective, Fin.ext_iff ];
  intro i j h_eq;
  have := nodup_iff_injective_get.mp ( Finset.nodup_toList t ) h_eq;
  simpa [ Fin.ext_iff ] using his.injective ( Fin.ext <| by injection this );

lemma FinsetLE.ofSublistForall₂ (h : SublistForall₂ (· ≤ ·) s.toList t.toList) : FinsetLE s t := by
  have h1 (x : s) : ∃ i : Fin s.card, s.toList[i] = x := by
    obtain ⟨i, hi⟩ := mem_iff_get.mp <| Finset.mem_toList.mpr x.2
    exact ⟨⟨i, by simpa using i.2⟩, hi⟩
  choose g hg using h1
  have h2 : g.Injective := by intro x y; have := hg x; have := hg y; aesop;
  obtain ⟨f, hf₁, hf₂⟩ := lemma_3 h;
  exact ⟨⟨f ∘ g, fun x y hxy => by simpa [hg] using h2 (hf₁ hxy)⟩,
    fun x => by simpa [hg] using hf₂ (g x) ⟩;

theorem Higman' (h : WellQuasiOrderedLE α) : WellQuasiOrdered (FinsetLE (α := α)) := by
  intro f
  have h1 := Set.partiallyWellOrderedOn_univ_iff.mpr h.wqo
  have h2 := Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂ _ h1
  obtain ⟨m, n, hmn, h_sub⟩ := h2 (fun n => ⟨(f n).toList, by tauto⟩)
  exact ⟨m, n, hmn, FinsetLE.ofSublistForall₂ h_sub⟩
