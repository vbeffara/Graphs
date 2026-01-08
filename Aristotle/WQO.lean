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

open Classical

variable {α : Type*} [PartialOrder α] {s t : Finset α} {l1 l2 : List α}

lemma lemma_1 (h : List.SublistForall₂ (· ≤ ·) l1 l2) : ∃ is : Fin l1.length ↪ Fin l2.length,
    StrictMono is ∧ ∀ i, l1[i] ≤ l2[is i] := by
  induction h with
  | nil => simp [StrictMono]
  | cons h h' ih =>
    obtain ⟨is, his₁, his₂⟩ := ih
    refine ⟨⟨Fin.cases ⟨0, by simp⟩ (fun i => (is i).succ), ?_⟩, ?_⟩
    · simp [Fin.forall_fin_succ, Function.Injective] ; grind
    · simp_all [Fin.forall_fin_succ, StrictMono]
  | cons_right h ih =>
    obtain ⟨is, his₁, his₂⟩ := ih
    exact ⟨is.trans <| Fin.succEmb _, by simp_all [StrictMono]⟩

lemma SublistForall2_imp_FinsetLE (h : List.SublistForall₂ (· ≤ ·) s.toList t.toList) : FinsetLE s t := by
  obtain ⟨is, his⟩ := lemma_1 h
  have h_sublist : ∃ is : Fin s.card → Fin t.card, StrictMono is ∧ ∀ i, s.toList[i] ≤ t.toList[is i] := by
    refine ⟨Fin.cast (by simp) ∘ is ∘ Fin.cast (by simp), ?_, fun i => ?_⟩
    · simp_all [Fin.cast, StrictMono]
    · exact his.2 (Fin.cast (by simp) i)
  choose is his his' using h_sublist;
  have h_inj : ∃ f : Fin s.card → t, Function.Injective f ∧ ∀ i, s.toList[i] ≤ f i := by
    use fun i => ⟨t.toList[is i], Finset.mem_toList.mp (by simp)⟩
    simp_all +decide [ Function.Injective, Fin.ext_iff ];
    intro i j h_eq;
    have := List.nodup_iff_injective_get.mp ( Finset.nodup_toList t ) h_eq;
    simpa [ Fin.ext_iff ] using his.injective ( Fin.ext <| by injection this );
  obtain ⟨ f, hf₁, hf₂ ⟩ := h_inj;
  have h_inj (x : s) : ∃ i : Fin s.card, s.toList[i] = x := by
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp <| Finset.mem_toList.mpr x.2
    exact ⟨⟨i, by simpa using i.2⟩, hi⟩
  have h_inj' : ∃ g : s ≃ Fin s.card, ∀ x : s, s.toList[g x] = x := by
    choose g hg using h_inj;
    have h_inj : Function.Injective g := by intro x y; have := hg x; have := hg y; aesop;
    have h_surj : Function.Surjective g := by
      exact ( Fintype.bijective_iff_injective_and_card g ).mpr ⟨ h_inj, by simp +decide ⟩ |>.2;
    exact ⟨ Equiv.ofBijective g ⟨ h_inj, h_surj ⟩, hg ⟩;
  obtain ⟨ g, hg ⟩ := h_inj';
  exact ⟨ ⟨ fun x => f ( g x ), fun x y hxy => by simpa [ hg ] using g.injective ( hf₁ hxy ) ⟩, fun x => by simpa [ hg ] using hf₂ ( g x ) ⟩;

theorem Higman' (h : WellQuasiOrderedLE α) : WellQuasiOrdered (FinsetLE (α := α)) := by
  intro f
  have h1 := Set.partiallyWellOrderedOn_univ_iff.mpr h.wqo
  have h2 := Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂ _ h1
  obtain ⟨m, n, hmn, h_sub⟩ := h2 (fun n => ⟨(f n).toList, by tauto⟩)
  exact ⟨m, n, hmn, SublistForall2_imp_FinsetLE h_sub⟩
