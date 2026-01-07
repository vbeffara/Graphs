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

variable {α : Type*} [PartialOrder α] {s t : Finset α}

lemma SublistForall2_imp_FinsetLE (h : List.SublistForall₂ (· ≤ ·) s.toList t.toList) : FinsetLE s t := by
  have h1 {l1 l2 : List α} (h_sublist : List.SublistForall₂ (· ≤ ·) l1 l2) :
      ∃ is : Fin l1.length ↪ Fin l2.length, StrictMono is ∧ ∀ i, l1[i] ≤ l2[is i] := by
    induction' h_sublist with l1 l2 h_sublist ih;
    · simp [StrictMono]
    · rename_i l2 ih h_sublist ih';
      obtain ⟨ is, his₁, his₂ ⟩ := ih';
      refine' ⟨ ⟨ fun i => Fin.cases ⟨ 0, _ ⟩ ( fun i => ⟨ is i + 1, _ ⟩ ) i, _ ⟩, _, _ ⟩ <;> simp_all [ Fin.forall_fin_succ, StrictMono ];
      all_goals simp_all [Fin.forall_fin_succ, Function.Injective, StrictMono]
      exacts [ fun i j hij => is.injective <| Fin.ext hij, fun i => Nat.succ_pos _, his₂ ];
    · rcases ‹_› with ⟨ is, his, h ⟩;
      refine' ⟨ ⟨ fun i => Fin.succ ( is i ), fun i j hij => _ ⟩, _, _ ⟩ <;> simp_all [StrictMono];
  have h_sublist : ∃ is : Fin s.card → Fin t.card, StrictMono is ∧ ∀ i, s.toList[i] ≤ t.toList[is i] := by
    obtain ⟨ is, his ⟩ := h1 h;
    exact ⟨ fun i => ⟨ is ⟨ i, by simp ⟩, by simpa using Fin.is_lt ( is ⟨ i, by simp ⟩ ) ⟩, fun i j hij => by simpa using his.1 ( by simpa using hij ), fun i => his.2 ⟨ i, by simp ⟩ ⟩
  choose is his his' using h_sublist;
  have h_inj : ∃ f : Fin s.card → t, Function.Injective f ∧ ∀ i, s.toList[i] ≤ f i := by
    use fun i => ⟨t.toList[is i], by
      exact Finset.mem_toList.mp ( by simp )⟩
    generalize_proofs at *;
    simp_all +decide [ Function.Injective, Fin.ext_iff ];
    intro i j h_eq;
    have := List.nodup_iff_injective_get.mp ( Finset.nodup_toList t ) h_eq;
    simpa [ Fin.ext_iff ] using his.injective ( Fin.ext <| by injection this );
  obtain ⟨ f, hf₁, hf₂ ⟩ := h_inj;
  have h_inj : ∃ g : s ≃ Fin s.card, ∀ x : s, s.toList[g x] = x := by
    have h_inj : ∀ x : s, ∃ i : Fin s.card, s.toList[i] = x := by
      intro x
      have h_mem : x.val ∈ s.toList := by
        aesop;
      obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp h_mem;
      exact ⟨ ⟨ i, by simpa using i.2 ⟩, hi ⟩;
    choose g hg using h_inj;
    have h_inj : Function.Injective g := by
      intro x y; have := hg x; have := hg y; aesop;
    have h_surj : Function.Surjective g := by
      exact ( Fintype.bijective_iff_injective_and_card g ).mpr ⟨ h_inj, by simp +decide ⟩ |>.2;
    exact ⟨ Equiv.ofBijective g ⟨ h_inj, h_surj ⟩, hg ⟩;
  obtain ⟨ g, hg ⟩ := h_inj;
  exact ⟨ ⟨ fun x => f ( g x ), fun x y hxy => by simpa [ hg ] using g.injective ( hf₁ hxy ) ⟩, fun x => by simpa [ hg ] using hf₂ ( g x ) ⟩;

theorem Higman' (h : WellQuasiOrderedLE α) : WellQuasiOrdered (FinsetLE (α := α)) := by
  intro f
  obtain ⟨m, n, hmn, h_sub⟩ : ∃ m n : ℕ, m < n ∧ List.SublistForall₂ (· ≤ ·) (f m).toList (f n).toList := by
    have h_sublist : Set.PartiallyWellOrderedOn {l : List α | ∀ x ∈ l, x ∈ Set.univ} (List.SublistForall₂ (· ≤ ·)) := by
      apply_rules [ Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂ ];
      exact Set.partiallyWellOrderedOn_univ_iff.mpr h.wqo
    have := h_sublist ( fun n => ⟨ f n |> Finset.toList, fun x hx => trivial ⟩ );
    aesop;
  exact ⟨ m, n, hmn, SublistForall2_imp_FinsetLE h_sub ⟩
