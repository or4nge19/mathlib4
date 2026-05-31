/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.BinetFormula

/-!
# Gamma bounds from Binet's formula

This file records namespace-level consequences of the Gamma bounds proved in
`Mathlib.Analysis.SpecialFunctions.Gamma.BinetFormula`.

The main estimate is DLMF 5.6.7:
`‖Γ z‖ ≤ Γ (re z)` for `0 < re z`.  Squared norm variants are kept here for callers
that need them in finite-order estimates.
-/

open Complex

@[expose] public section

noncomputable section

namespace Complex

/-- **DLMF 5.6.7**: for `0 < re z`, `‖Γ z‖ ≤ Γ (re z)`. -/
theorem norm_Gamma_le_Gamma_re {z : ℂ} (hz : 0 < z.re) :
    ‖Gamma z‖ ≤ Real.Gamma z.re :=
  Binet.norm_Gamma_le_Gamma_re hz

/-- Squared form of `Complex.norm_Gamma_le_Gamma_re`. -/
theorem norm_sq_Gamma_le_Gamma_re {z : ℂ} (hz : 0 < z.re) :
    ‖Gamma z‖ ^ 2 ≤ (Real.Gamma z.re) ^ 2 := by
  have h := norm_Gamma_le_Gamma_re hz
  have hΓ : 0 ≤ Real.Gamma z.re := (Real.Gamma_pos_of_pos hz).le
  simpa [pow_two] using mul_le_mul h h (norm_nonneg _) hΓ

/-- For Re(z) ≥ 1 / 2, |Γ(z)|² ≤ |Γ(Re(z))|².
This is the precise statement of DLMF 5.6.7. -/
theorem norm_sq_Gamma_le_norm_sq_Gamma_re {z : ℂ} (hz : 1 / 2 ≤ z.re) :
    ‖Gamma z‖ ^ 2 ≤ ‖Gamma z.re‖ ^ 2 := by
  have hz_pos : 0 < z.re := by linarith
  have h := norm_sq_Gamma_le_Gamma_re hz_pos
  have habs : ‖Gamma (z.re : ℂ)‖ = Real.Gamma z.re := by
    rw [Complex.Gamma_ofReal z.re]
    rw [Complex.norm_real]
    exact abs_of_pos (Real.Gamma_pos_of_pos hz_pos)
  rw [habs]
  exact h

end Complex

end
