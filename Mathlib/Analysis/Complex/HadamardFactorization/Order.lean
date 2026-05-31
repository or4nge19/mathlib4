/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Complex.HadamardFactorization.Growth

/-!
## Hadamard factorization for finite-order entire functions

This file upgrades the intrinsic growth-form Hadamard factorization theorem to Tao's finite-order
formulation: an entire function has order at most `ρ` if it satisfies an `ε`-family of exponential
growth bounds.
-/

@[expose] public section

noncomputable section

open Set Filter Asymptotics
open scoped Topology BigOperators

namespace Complex.Hadamard

/-- An entire function has order at most `ρ` if it satisfies Tao's `ε`-family growth bound. -/
def EntireOfOrderAtMost (ρ : ℝ) (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧
    ∀ ε : ℝ, 0 < ε →
      ∃ C > 0, ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (ρ + ε))

namespace EntireOfOrderAtMost

theorem differentiable {ρ : ℝ} {f : ℂ → ℂ} (h : EntireOfOrderAtMost ρ f) :
    Differentiable ℂ f :=
  h.1

theorem exists_bound {ρ ε : ℝ} {f : ℂ → ℂ} (h : EntireOfOrderAtMost ρ f)
    (hε : 0 < ε) :
    ∃ C > 0, ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (ρ + ε)) :=
  h.2 ε hε

/-- A single exponential bound of order `ρ` implies Tao's ε-family order bound. -/
theorem of_norm_le_exp {ρ : ℝ} {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hbound : ∃ C > 0, ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ ρ)) :
    EntireOfOrderAtMost ρ f := by
  refine ⟨hf, ?_⟩
  rintro ε hε
  rcases hbound with ⟨C, hC, hCbound⟩
  refine ⟨C, hC, ?_⟩
  exact norm_le_exp_mul_rpow_of_exponent_le (f := f)
    (r := fun z : ℂ => 1 + ‖z‖) hC.le
    (fun z => by linarith [norm_nonneg z]) (by linarith : ρ ≤ ρ + ε) hCbound

end EntireOfOrderAtMost

theorem hadamard_factorization_of_order {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hnot : ∃ z : ℂ, f z ≠ 0)
    (horder : EntireOfOrderAtMost ρ f) :
    ∃ (P : Polynomial ℂ),
      P.degree ≤ Nat.floor ρ ∧
      ∀ z : ℂ,
        f z =
          Complex.exp (Polynomial.eval z P) *
            z ^ (analyticOrderNatAt f 0) *
            divisorCanonicalProduct (Nat.floor ρ) f (Set.univ : Set ℂ) z := by
  classical
  let hentire : Differentiable ℂ f := horder.differentiable
  set m : ℕ := Nat.floor ρ
  rcases exists_between_self_and_floor_add_one_same_floor hρ with
    ⟨τ, hτ, hτ_lt, hτ_nonneg, hfloorτ'⟩
  have hfloorτ : Nat.floor τ = m := by
    simpa [m] using hfloorτ'
  have hε : 0 < τ - ρ := sub_pos.2 hτ
  rcases horder.exists_bound hε with ⟨C, hCpos, hC⟩
  have hgrowthτ :
      ∃ C' > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C' * (1 + ‖z‖) ^ τ := by
    have hnorm : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ) := by
      intro z
      simpa [sub_add_cancel] using (hC z)
    exact log_growth_of_norm_le_exp_mul_rpow (f := f)
      (r := fun z : ℂ => 1 + ‖z‖) hCpos hτ_nonneg
      (fun z => by linarith [norm_nonneg z]) hnorm
  rcases hadamard_factorization_of_growth (f := f) (ρ := τ) hτ_nonneg
      hentire hnot hgrowthτ with
    ⟨P, hdeg, hfac⟩
  refine ⟨P, ?_, ?_⟩
  · simpa [m, hfloorτ] using hdeg
  · intro z
    simpa [m, hfloorτ] using hfac z

/-- Reindexed form of `hadamard_factorization_of_order`, for any index type equivalent to the
nonzero divisor indices. -/
theorem hadamard_factorization_of_order_reindex {ι : Type*} {f : ℂ → ℂ} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hnot : ∃ z : ℂ, f z ≠ 0)
    (horder : EntireOfOrderAtMost ρ f)
    (e : ι ≃ divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ),
      P.degree ≤ Nat.floor ρ ∧
      ∀ z : ℂ,
        f z =
          Complex.exp (Polynomial.eval z P) *
            z ^ (analyticOrderNatAt f 0) *
            (∏' i : ι, weierstrassFactor (Nat.floor ρ)
              (z / divisorZeroIndex₀_val (e i))) := by
  classical
  rcases hadamard_factorization_of_order (f := f) (ρ := ρ) hρ hnot horder with
    ⟨P, hdeg, hfac⟩
  refine ⟨P, hdeg, ?_⟩
  intro z
  simpa [divisorCanonicalProduct_eq_tprod_of_equiv (m := Nat.floor ρ)
      (f := f) (U := Set.univ) e z] using hfac z

/-- Sequence-indexed form of `hadamard_factorization_of_order`, for an enumeration of the nonzero
divisor indices by `ℕ`. -/
theorem hadamard_factorization_of_order_sequence {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hnot : ∃ z : ℂ, f z ≠ 0)
    (horder : EntireOfOrderAtMost ρ f)
    (e : ℕ ≃ divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ),
      P.degree ≤ Nat.floor ρ ∧
      ∀ z : ℂ,
        f z =
          Complex.exp (Polynomial.eval z P) *
            z ^ (analyticOrderNatAt f 0) *
            Complex.canonicalProduct (Nat.floor ρ)
              (fun n : ℕ => divisorZeroIndex₀_val (e n)) z := by
  classical
  rcases hadamard_factorization_of_order_reindex (f := f) (ρ := ρ) hρ hnot horder e with
    ⟨P, hdeg, hfac⟩
  refine ⟨P, hdeg, ?_⟩
  intro z
  simpa [Complex.canonicalProduct_def] using hfac z

end Complex.Hadamard
