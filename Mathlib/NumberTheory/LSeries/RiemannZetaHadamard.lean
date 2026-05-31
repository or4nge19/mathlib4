/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Complex.HadamardFactorization
public import Mathlib.NumberTheory.LSeries.ZetaFiniteOrder
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.Analysis.Real.Pi.Irrational


/-!
## Intrinsic Hadamard factorization for the completed Riemann zeta function

This is the zeta-facing theorem that uses the intrinsic divisor-indexed canonical product and
`Mathlib/Analysis/Complex/HadamardFactorization.lean`.

The analytic input is the growth bound proved in `ZetaFiniteOrder.lean`, and the structural input
is the intrinsic Hadamard factorization theorem `Complex.Hadamard.hadamard_factorization_of_order`.
-/

@[expose] public section

noncomputable section

open Complex Set

namespace Riemann

open scoped BigOperators

/-!
## Zeta specialization: intrinsic Hadamard factorization for `completedRiemannZeta₀`

This is the zeta-facing corollary: we combine the sharp order-one `ε`-family bound
`Complex.completedRiemannZeta₀_order_one` (proved in `ZetaFiniteOrder.lean`) with the intrinsic
Hadamard factorization theorem `Complex.Hadamard.hadamard_factorization_of_order`.
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

theorem completedRiemannZeta₀_hadamard_factorization_intrinsic :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, completedRiemannZeta₀ z =
        Complex.exp (Polynomial.eval z P) * z ^ (analyticOrderNatAt completedRiemannZeta₀ 0) *
      Complex.Hadamard.divisorCanonicalProduct 1 completedRiemannZeta₀ (Set.univ : Set ℂ) z := by
  have hentire : Differentiable ℂ completedRiemannZeta₀ := differentiable_completedZeta₀
  have hρ : (0 : ℝ) ≤ (1 : ℝ) := by norm_num
  have horder :
      ∀ ε : ℝ, 0 < ε →
        ∃ C > 0, ∀ z : ℂ,
          ‖completedRiemannZeta₀ z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ ((1 : ℝ) + ε)) := by
    intro ε hε
    simpa [add_comm, add_left_comm, add_assoc] using (Complex.completedRiemannZeta₀_order_one ε hε)
  rcases
      (Complex.Hadamard.hadamard_factorization_of_order
        (f := completedRiemannZeta₀) (ρ := (1 : ℝ))
        hρ hentire completedRiemannZeta₀_nontrivial (by
          intro ε hε
          rcases horder ε hε with ⟨C, hCpos, hC⟩
          exact ⟨C, hCpos, by
            intro z
            simpa [add_comm, add_left_comm, add_assoc] using (hC z)⟩)) with
    ⟨P, hdeg, hfac⟩
  refine ⟨P, ?_, ?_⟩
  · simpa using hdeg
  · intro z
    simpa using hfac z

end Riemann
