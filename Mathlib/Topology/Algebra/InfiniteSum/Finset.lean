/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Infinite sums over finite support

This file collects small lemmas for reducing infinite sums to sums over a finset.
-/

public section

open Finset

variable {α : Type*}

lemma summable_of_eq_zero_not_mem_finset (s : Finset α) (u : α → ℝ)
    (hu : ∀ a, a ∉ s → u a = 0) :
    Summable u := by
  classical
  refine summable_of_hasFiniteSupport ?_
  refine (Finset.finite_toSet s).subset ?_
  intro a ha
  by_contra hs
  exact ha (hu a hs)

lemma summable_ite_mem_finset [DecidableEq α] (s : Finset α) (u : α → ℝ) :
    Summable (fun a => if a ∈ s then u a else 0) :=
  summable_of_eq_zero_not_mem_finset s _ (by intro a ha; simp [ha])

lemma tsum_ite_mem_finset [DecidableEq α] (s : Finset α) (u : α → ℝ) :
    (∑' a, if a ∈ s then u a else 0) = ∑ a ∈ s, u a := by
  simpa using
    (tsum_eq_sum (s := s) (f := fun a => if a ∈ s then u a else 0)
      (by intro a ha; simp [ha]))

lemma tsum_add_four (u₁ u₂ u₃ u₄ : α → ℝ)
    (h₁ : Summable u₁) (h₂ : Summable u₂) (h₃ : Summable u₃) (h₄ : Summable u₄) :
    tsum (fun a => ((u₁ a + u₂ a) + u₃ a) + u₄ a)
      = tsum u₁ + tsum u₂ + tsum u₃ + tsum u₄ := by
  have h12 :
      tsum (fun a => u₁ a + u₂ a) = tsum u₁ + tsum u₂ :=
    Summable.tsum_add h₁ h₂
  have h34 :
      tsum (fun a => u₃ a + u₄ a) = tsum u₃ + tsum u₄ :=
    Summable.tsum_add h₃ h₄
  calc
    tsum (fun a => ((u₁ a + u₂ a) + u₃ a) + u₄ a)
        = tsum (fun a => (u₁ a + u₂ a) + (u₃ a + u₄ a)) := by
            simp [add_comm, add_left_comm]
    _ = tsum (fun a => u₁ a + u₂ a) + tsum (fun a => u₃ a + u₄ a) :=
        Summable.tsum_add (h₁.add h₂) (h₃.add h₄)
    _ = tsum u₁ + tsum u₂ + tsum u₃ + tsum u₄ := by
        rw [h12, h34]
        ring
