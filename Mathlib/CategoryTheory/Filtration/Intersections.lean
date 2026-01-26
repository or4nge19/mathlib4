/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Jonathan Washburn
-/

module

public import Mathlib.CategoryTheory.Filtration.Opposed
public import Mathlib.Tactic.Linarith

/-!
## Intersections of opposed filtrations

This file contains the first half of Deligne's Proposition (1.2.5)(i): under finiteness and
`gr₂`-vanishing opposedness hypotheses, off-diagonal intersections vanish.

More precisely, in an abelian category, if `F` and `G` are finite decreasing `ℤ`-filtrations on
`X` and are `n`-opposed in the `gr₂`-vanishing sense, then for all `p q` with `p+q>n` we have
`F.step p ⊓ G.step q = ⊥` as subobjects of `X`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory

universe v u
variable {C : Type u} [Category.{v} C]

namespace Filtration
namespace DecFiltration

variable {X : C}

section
variable [Abelian C]

/-- Extract the `⊥`-bound from finiteness: for a finite filtration `F`, there exists `b` such that
`F.step n = ⊥` for all `n ≥ b`. -/
lemma IsFinite.exists_bot_bound (F : Filtration.DecFiltration (C := C) X)
    (hF : IsFinite (C := C) (X := X) F) :
    ∃ b : ℤ, ∀ n : ℤ, b ≤ n → F.step n = ⊥ := by
  rcases hF with ⟨a, b, ha, hb⟩
  refine ⟨b, ?_⟩
  intro n hn
  exact hb n hn

/-- If `gr₂ F G p q` is zero, then the defining quotient equality holds:
`F^p ∩ G^q = (F^{p+1} ∩ G^q) + (F^p ∩ G^{q+1})` as subobjects of `X`. -/
lemma inf_eq_sup_next_of_isZero_gr₂ (F G : Filtration.DecFiltration (C := C) X) (p q : ℤ)
    (h : IsZero (gr₂ (C := C) (X := X) F G p q)) :
    F.step p ⊓ G.step q =
      (F.step (p + 1) ⊓ G.step q) ⊔ (F.step p ⊓ G.step (q + 1)) := by
  classical
  let Xpq : Subobject X := F.step p ⊓ G.step q
  let Ypq : Subobject X := (F.step (p + 1) ⊓ G.step q) ⊔ (F.step p ⊓ G.step (q + 1))
  have hY : Ypq ≤ Xpq := by
    refine sup_le ?_ ?_
    · have hp : F.step (p + 1) ≤ F.step p := by
        exact step_le_step_of_le (C := C) (X := X) F (show p ≤ p + 1 from by linarith)
      exact inf_le_inf hp le_rfl
    · have hq : G.step (q + 1) ≤ G.step q := by
        exact step_le_step_of_le (C := C) (X := X) G (show q ≤ q + 1 from by linarith)
      exact inf_le_inf le_rfl hq
  have hzero : IsZero (cokernel (Subobject.ofLE Ypq Xpq hY)) := by
    simpa [gr₂, Xpq, Ypq] using h
  have hπ : cokernel.π (Subobject.ofLE Ypq Xpq hY) = 0 :=
    hzero.eq_of_tgt _ _
  haveI : Epi (Subobject.ofLE Ypq Xpq hY) :=
    CategoryTheory.Abelian.epi_of_cokernel_π_eq_zero (f := Subobject.ofLE Ypq Xpq hY) hπ
  haveI : IsIso (Subobject.ofLE Ypq Xpq hY) :=
    isIso_of_mono_of_epi (Subobject.ofLE Ypq Xpq hY)
  have hYX : Ypq = Xpq :=
    Subobject.eq_of_comm (f := asIso (Subobject.ofLE Ypq Xpq hY)) (by simp)
  simpa [Xpq, Ypq] using hYX.symm

/-- Base case: if `p+q` is beyond the sum of `⊥`-bounds of `F` and `G`, then `F^p ∩ G^q = 0`. -/
lemma inf_eq_bot_of_large (F G : Filtration.DecFiltration (C := C) X) (bF bG p q : ℤ)
    (hF : ∀ n : ℤ, bF ≤ n → F.step n = ⊥)
    (hG : ∀ n : ℤ, bG ≤ n → G.step n = ⊥)
    (hpq : bF + bG ≤ p + q) :
    F.step p ⊓ G.step q = ⊥ := by
  have hp_or_hq : bF ≤ p ∨ bG ≤ q := by
    by_contra h
    have hp : p < bF := lt_of_not_ge (by
      intro hp; exact h (Or.inl hp))
    have hq : q < bG := lt_of_not_ge (by
      intro hq; exact h (Or.inr hq))
    have : p + q < bF + bG := by linarith
    exact not_lt_of_ge hpq this
  cases hp_or_hq with
  | inl hp =>
      simp [hF p hp]
  | inr hq =>
      simp [hG q hq]

/-- Main descending induction: if `F` and `G` are finite and `n`-opposed, then
`F^p ∩ G^q = 0` whenever `p+q>n`. -/
theorem inf_eq_bot_of_sum_gt (F G : Filtration.DecFiltration (C := C) X) (n : ℤ)
    (hF : IsFinite (C := C) (X := X) F) (hG : IsFinite (C := C) (X := X) G)
    (hOpp : IsNOpposedGr₂ (C := C) (X := X) F G n) :
    ∀ p q : ℤ, n < p + q → F.step p ⊓ G.step q = ⊥ := by
  classical
  rcases IsFinite.exists_bot_bound (C := C) (X := X) F hF with ⟨bF, hbF⟩
  rcases IsFinite.exists_bot_bound (C := C) (X := X) G hG with ⟨bG, hbG⟩
  let B : ℤ := bF + bG
  have main :
      ∀ k : ℕ, ∀ p q : ℤ, p + q = B - k → n < p + q → F.step p ⊓ G.step q = ⊥ := by
    intro k
    induction k with
    | zero =>
    · intro p q hpq hn
      have : B ≤ p + q := by simp [hpq]
      exact inf_eq_bot_of_large (C := C) (X := X) F G bF bG p q hbF hbG this
    | succ k ih =>
      intro p q hpq hn
      have hneq : p + q ≠ n := ne_of_gt hn
      have hz : IsZero (gr₂ (C := C) (X := X) F G p q) := hOpp p q hneq
      have hrec :
          F.step p ⊓ G.step q =
            (F.step (p + 1) ⊓ G.step q) ⊔ (F.step p ⊓ G.step (q + 1)) :=
        inf_eq_sup_next_of_isZero_gr₂ (C := C) (X := X) F G p q hz
      have hpq1 : (p + 1) + q = B - k := by
        have h' := congrArg (fun t : ℤ => t + 1) hpq
        simpa [add_assoc, add_left_comm, add_comm, sub_eq_add_neg,
          Nat.cast_add, Nat.cast_one] using h'
      have hpq2 : p + (q + 1) = B - k := by
        have h' := congrArg (fun t : ℤ => t + 1) hpq
        simpa [add_assoc, add_left_comm, add_comm, sub_eq_add_neg,
          Nat.cast_add, Nat.cast_one] using h'
      have hn1 : n < (p + 1) + q := by linarith
      have hn2 : n < p + (q + 1) := by linarith
      have hbot1 : F.step (p + 1) ⊓ G.step q = ⊥ := ih p.succ q hpq1 hn1
      have hbot2 : F.step p ⊓ G.step (q + 1) = ⊥ := ih p (q.succ) hpq2 hn2
      simp [hrec, hbot1, hbot2]
  intro p q hn
  by_cases hB : B ≤ p + q
  · exact inf_eq_bot_of_large (C := C) (X := X) F G bF bG p q hbF hbG hB
  · have hnonneg : 0 ≤ B - (p + q) := by linarith
    let k : ℕ := Int.toNat (B - (p + q))
    have hk : (k : ℤ) = B - (p + q) := by
      simpa [k] using (Int.toNat_of_nonneg hnonneg)
    have hpq : p + q = B - k := by
      linarith [hk]
    exact main k p q hpq hn

/-- Specialized to the `n+1` line: if `p+q=n+1`, then `F^p ∩ G^q = 0`. -/
theorem inf_eq_bot_on_succ_line (F G : Filtration.DecFiltration (C := C) X) (n : ℤ)
    (hF : IsFinite (C := C) (X := X) F) (hG : IsFinite (C := C) (X := X) G)
    (hOpp : IsNOpposedGr₂ (C := C) (X := X) F G n) :
    ∀ p q : ℤ, p + q = n + 1 → F.step p ⊓ G.step q = ⊥ := by
  intro p q hpq
  have : n < p + q := by linarith
  exact inf_eq_bot_of_sum_gt (C := C) (X := X) F G n hF hG hOpp p q this

end

end DecFiltration
end Filtration

end CategoryTheory
