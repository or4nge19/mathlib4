/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Complex.HadamardFactorization.Order
public import Mathlib.NumberTheory.LSeries.ZetaFiniteOrder
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.Analysis.Real.Pi.Irrational


/-!
## Intrinsic Hadamard factorization for the completed Riemann zeta function

This file applies the intrinsic Hadamard factorization theorem to the entire completed zeta
function `completedRiemannZeta₀`.  The analytic input is the Tao-style order-one bound proved in
`ZetaFiniteOrder.lean`; the product is the divisor-indexed canonical product, so multiplicities are
those of `completedRiemannZeta₀` itself.
-/

@[expose] public section

noncomputable section

open Complex Set

namespace Riemann

open scoped BigOperators

/-!
## Zeta specialization: intrinsic Hadamard factorization for `completedRiemannZeta₀`

The sharp order-one estimate for Λ₀ is recorded as
`Complex.Hadamard.EntireOfOrderAtMost`; Hadamard factorization then gives the intrinsic product
over its divisor.
-/

/-- The completed Riemann zeta factor has value `π / 6` at `2`. -/
theorem completedRiemannZeta_two :
    completedRiemannZeta (2 : ℂ) = (Real.pi : ℂ) / 6 := by
  have hs : (1 : ℝ) < Complex.re (2 : ℂ) := by norm_num
  have hpi0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have htsum :
      completedRiemannZeta (2 : ℂ) = (Real.pi : ℂ)⁻¹ * (∑' n : ℕ, ((n : ℂ) ^ 2)⁻¹) := by
    simpa [Complex.cpow_neg_one] using
      (completedZeta_eq_tsum_of_one_lt_re (s := (2 : ℂ)) hs)
  have hzeta : riemannZeta (2 : ℂ) = ∑' n : ℕ, ((n : ℂ) ^ 2)⁻¹ := by
    simpa using (zeta_eq_tsum_one_div_nat_cpow (s := (2 : ℂ)) hs)
  have hζ2 : riemannZeta (2 : ℂ) = (Real.pi : ℂ) ^ 2 / 6 := by
    simpa using (riemannZeta_two : riemannZeta (2 : ℂ) = (Real.pi : ℂ) ^ 2 / 6)
  have hΛ2' : completedRiemannZeta (2 : ℂ) = (Real.pi : ℂ)⁻¹ * riemannZeta (2 : ℂ) := by
    simpa [hzeta] using htsum
  calc
    completedRiemannZeta (2 : ℂ)
        = (Real.pi : ℂ)⁻¹ * ((Real.pi : ℂ) ^ 2 / 6) := by
            simpa [hζ2] using hΛ2'
    _ = (Real.pi : ℂ) / 6 := by
            field_simp [hpi0]

/-- The entire completed zeta function `Λ₀` has value `(π - 3) / 6` at `2`. -/
theorem completedRiemannZeta₀_two :
    completedRiemannZeta₀ (2 : ℂ) = ((Real.pi : ℂ) - 3) / 6 := by
  have h := completedRiemannZeta_eq (2 : ℂ)
  have h' :
      completedRiemannZeta (2 : ℂ) + (1 : ℂ) / 2 + (1 : ℂ) / (1 - (2 : ℂ)) =
        completedRiemannZeta₀ (2 : ℂ) := by
    have := congrArg (fun x => x + (1 : ℂ) / 2 + (1 : ℂ) / (1 - (2 : ℂ))) h
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  have h'' :
      completedRiemannZeta₀ (2 : ℂ) =
        completedRiemannZeta (2 : ℂ) + (1 : ℂ) / 2 + (1 : ℂ) / (1 - (2 : ℂ)) := by
    simpa [add_assoc, add_left_comm, add_comm] using h'.symm
  have hden : (1 : ℂ) / (1 - (2 : ℂ)) = (-1 : ℂ) := by norm_num
  simpa [h'', completedRiemannZeta_two, hden] using (by ring :
    (Real.pi : ℂ) / 6 + (1 : ℂ) / 2 + (-1 : ℂ) = ((Real.pi : ℂ) - 3) / 6)

/-- The entire completed zeta function `Λ₀` is not identically zero. -/
theorem completedRiemannZeta₀_nontrivial : ∃ z : ℂ, completedRiemannZeta₀ z ≠ 0 := by
  refine ⟨(2 : ℂ), ?_⟩
  have hpi_ne3 : (Real.pi : ℂ) ≠ (3 : ℂ) := by
    intro h'
    have hpi' : (Real.pi : ℝ) = (3 : ℝ) := by
      simpa using congrArg Complex.re h'
    have hirr : Irrational Real.pi := by simp
    exact (hirr.ne_nat 3) (by simp at hpi')
  have hnum : ((Real.pi : ℂ) - 3) ≠ 0 := sub_ne_zero.2 hpi_ne3
  have hden : (6 : ℂ) ≠ 0 := by norm_num
  have : ((Real.pi : ℂ) - 3) / 6 ≠ 0 := div_ne_zero hnum hden
  simpa [completedRiemannZeta₀_two] using this

/-- The entire completed zeta function `Λ₀` has order at most one. -/
theorem completedRiemannZeta₀_entireOfOrderAtMost_one :
    Complex.Hadamard.EntireOfOrderAtMost (1 : ℝ) completedRiemannZeta₀ := by
  refine ⟨differentiable_completedZeta₀, ?_⟩
  intro ε hε
  simpa [add_comm, add_left_comm, add_assoc] using
    (Complex.completedRiemannZeta₀_order_one ε hε)

theorem completedRiemannZeta₀_hadamard_factorization_intrinsic :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, completedRiemannZeta₀ z =
        Complex.exp (Polynomial.eval z P) * z ^ (analyticOrderNatAt completedRiemannZeta₀ 0) *
      Complex.Hadamard.divisorCanonicalProduct 1 completedRiemannZeta₀ (Set.univ : Set ℂ) z := by
  rcases
      (Complex.Hadamard.hadamard_factorization_of_order
        (f := completedRiemannZeta₀) (ρ := (1 : ℝ))
        (by norm_num) completedRiemannZeta₀_nontrivial
        completedRiemannZeta₀_entireOfOrderAtMost_one) with
    ⟨P, hdeg, hfac⟩
  refine ⟨P, ?_, ?_⟩
  · simpa using hdeg
  · intro z
    simpa using hfac z

/-- Reindexed Hadamard factorization for Λ₀, for any type equivalent to its nonzero divisor
indices. -/
theorem completedRiemannZeta₀_hadamard_factorization_reindex
    {ι : Type*}
    (e : ι ≃ Complex.Hadamard.divisorZeroIndex₀ completedRiemannZeta₀ (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, completedRiemannZeta₀ z =
        Complex.exp (Polynomial.eval z P) * z ^ (analyticOrderNatAt completedRiemannZeta₀ 0) *
      (∏' i : ι, Complex.weierstrassFactor 1
        (z / Complex.Hadamard.divisorZeroIndex₀_val (e i))) := by
  rcases
      (Complex.Hadamard.hadamard_factorization_of_order_reindex
        (f := completedRiemannZeta₀) (ρ := (1 : ℝ))
        (by norm_num) completedRiemannZeta₀_nontrivial
        completedRiemannZeta₀_entireOfOrderAtMost_one e) with
    ⟨P, hdeg, hfac⟩
  refine ⟨P, ?_, ?_⟩
  · simpa using hdeg
  · intro z
    simpa using hfac z

/-- Sequence-indexed Hadamard factorization for Λ₀, for an enumeration of its nonzero divisor
indices by `ℕ`. -/
theorem completedRiemannZeta₀_hadamard_factorization_sequence
    (e : ℕ ≃ Complex.Hadamard.divisorZeroIndex₀ completedRiemannZeta₀ (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, completedRiemannZeta₀ z =
        Complex.exp (Polynomial.eval z P) * z ^ (analyticOrderNatAt completedRiemannZeta₀ 0) *
      Complex.canonicalProduct 1
        (fun n : ℕ => Complex.Hadamard.divisorZeroIndex₀_val (e n)) z := by
  rcases
      (Complex.Hadamard.hadamard_factorization_of_order_sequence
        (f := completedRiemannZeta₀) (ρ := (1 : ℝ))
        (by norm_num) completedRiemannZeta₀_nontrivial
        completedRiemannZeta₀_entireOfOrderAtMost_one e) with
    ⟨P, hdeg, hfac⟩
  refine ⟨P, ?_, ?_⟩
  · simpa using hdeg
  · intro z
    simpa using hfac z

end Riemann
