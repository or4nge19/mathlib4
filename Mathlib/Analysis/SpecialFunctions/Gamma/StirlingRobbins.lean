/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.BinetFormula
public import Mathlib.Analysis.SpecialFunctions.Stirling



/-!
# Robbins' Bounds for Stirling's Approximation

This file proves Robbins' sharp two-sided bounds for the factorial:

  √(2πn) (n/e)^n e^{1/(12n+1)} ≤ n! ≤ √(2πn) (n/e)^n e^{1/(12n)}

These bounds are derived from Binet's formula and the bounds on the Binet integral `J`.  This is
separate from the Weierstrass-product route to `Γ` discussed in Tao 246B Notes 1; the Binet
closed-form theorem used here still relies on Mathlib's existing Stirling limit to normalize its
integration constant.

## Main Results

* `Stirling.factorial_upper_robbins`: n! ≤ √(2πn)(n/e)^n e^{1/(12n)}
* `Stirling.factorial_lower_robbins`: n! ≥ √(2πn)(n/e)^n e^{1/(12n+1)}
* `Stirling.log_factorial_theta`: log(n!) = n log n - n + log(2πn)/2 + θ/(12n)
* `Stirling.factorial_asymptotic`: n! ~ √(2πn)(n/e)^n

The proof applies Binet's formula to `Γ n`, uses `Γ(n + 1) = n * Γ n`, and bounds the Binet
correction term via `Binet.re_J_robbins_bounds` and
`Binet.re_J_robbins_bounds_strict_upper`.

## References

* [robbins1955] for the sharp factorial bounds
* [feller1968] for the classical probability-text presentation of Stirling's formula
* [DLMF], §5.11 for Stirling asymptotic background and explicit error terms
-/

open Real Set MeasureTheory Filter Topology
open scoped BigOperators Nat

@[expose] public section

noncomputable section

namespace Stirling

/-! ## Section 1: Setup and basic facts -/

/-- For `n ≥ 1`, `log(n!) = log n + log Γ(n)`. -/
lemma log_factorial_eq_log_nat_add_log_Gamma {n : ℕ} (hn : 0 < n) :
    Real.log (n.factorial : ℝ) = Real.log (n : ℝ) + Real.log (Real.Gamma n) := by
  rw [← Real.log_mul
    (Nat.cast_ne_zero.mpr (ne_of_gt hn))
    (Real.Gamma_pos_of_pos (Nat.cast_pos.mpr hn)).ne']
  rw [← Real.Gamma_add_one (Nat.cast_ne_zero.mpr (ne_of_gt hn))]
  rw [Real.Gamma_nat_eq_factorial]

/-! ## Section 2: The theta parameter -/

/-- For n ≥ 1, there exists θ ∈ (0, 1) such that
log(n!) = n log n - n + log(2πn)/2 + θ/(12n).

This is the precise form of Stirling's approximation with explicit error, as in [robbins1955]. -/
theorem log_factorial_theta {n : ℕ} (hn : 0 < n) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      Real.log (n.factorial : ℝ) =
        n * Real.log n - n + Real.log (2 * Real.pi * n) / 2 + θ / (12 * n) := by
  have h_fact : Real.log (n.factorial) = Real.log n + Real.log (Real.Gamma n) :=
    log_factorial_eq_log_nat_add_log_Gamma hn
  let x : ℝ := n
  have hx : 0 < x := Nat.cast_pos.mpr hn
  have h_binet :
      Real.log (Real.Gamma x) =
        (x - 1/2) * Real.log x - x + Real.log (2 * Real.pi) / 2 + (Binet.J x).re := by
    exact Binet.log_Gamma_real_eq hx
  have hJ_pos : 0 < (Binet.J x).re := Binet.re_J_pos hx
  have hJ_ub : (Binet.J x).re < 1 / (12 * x) :=
    (Binet.re_J_robbins_bounds_strict_upper hx).2
  let θ := 12 * x * (Binet.J x).re
  use θ
  constructor
  · exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 12) hx) hJ_pos
  constructor
  · have h12x_pos : 0 < 12 * x := mul_pos (by norm_num : (0 : ℝ) < 12) hx
    have h12x_ne : (12 * x) ≠ 0 := ne_of_gt h12x_pos
    calc θ = 12 * x * (Binet.J x).re := rfl
      _ < 12 * x * (1 / (12 * x)) := by
          exact mul_lt_mul_of_pos_left hJ_ub h12x_pos
      _ = 1 := by
          field_simp [h12x_ne]
  rw [h_fact, h_binet]
  have h_theta : θ / (12 * x) = (Binet.J x).re := by field_simp [θ]; ring
  rw [h_theta]
  have h_log_term :
      Real.log (2 * Real.pi * n) / 2 =
        Real.log (2 * Real.pi) / 2 + Real.log n / 2 := by
    rw [Real.log_mul (by positivity) (by positivity)]
    ring
  rw [h_log_term]
  ring

/-! ## Section 3: Upper bound -/

/-- Helper for `exp(log x / 2) = sqrt x`. -/
private lemma exp_half_log {x : ℝ} (hx : 0 < x) :
    Real.exp (Real.log x / 2) = Real.sqrt x := by
  rw [Real.sqrt_eq_rpow]
  rw [Real.rpow_def_of_pos hx]
  congr 1
  ring

/-- Logarithm of the main Stirling factor `√(2πn) (n/e)^n`. -/
lemma log_stirlingFactor {n : ℕ} (hn : 0 < n) :
    Real.log (Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n) =
      n * Real.log n - n + Real.log (2 * Real.pi * n) / 2 := by
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by nlinarith [Real.pi_pos]
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [Real.log_mul (Real.sqrt_pos.mpr (mul_pos h2pi_pos hn_pos)).ne'
    (pow_pos (div_pos hn_pos (Real.exp_pos 1)) n).ne']
  rw [Real.log_sqrt (le_of_lt (mul_pos h2pi_pos hn_pos))]
  rw [Real.log_pow, Real.log_div (Nat.cast_ne_zero.mpr (ne_of_gt hn)) (Real.exp_pos 1).ne']
  rw [Real.log_exp]
  ring

/-- Exponentiating the Stirling formula with `θ < 1` gives Robbins' upper bound. -/
theorem factorial_upper_robbins (n : ℕ) (hn : 0 < n) :
    (n.factorial : ℝ) ≤
      Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n * Real.exp (1 / (12 * n)) := by
  obtain ⟨θ, hθ_pos, hθ_lt_one, hlog⟩ := log_factorial_theta hn
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h_log_le : Real.log (n.factorial : ℝ) ≤
      n * Real.log n - n + Real.log (2 * Real.pi * n) / 2 + 1 / (12 * n) := by
    rw [hlog]
    apply add_le_add_right
    apply div_le_div_of_nonneg_right (le_of_lt hθ_lt_one)
    exact mul_nonneg (by norm_num) hn_pos.le
  have h_exp := Real.exp_le_exp.mpr h_log_le
  rw [Real.exp_log (Nat.cast_pos.mpr (Nat.factorial_pos n))] at h_exp
  have h_pow_eq : (n : ℝ) ^ (n : ℝ) / Real.exp n = ((n : ℝ) / Real.exp 1) ^ n := by
    have h1 : Real.exp n = (Real.exp 1) ^ n := by rw [← Real.exp_one_rpow, Real.rpow_natCast]
    rw [h1]
    have h2 : (n : ℝ) ^ (n : ℝ) = (n : ℝ) ^ n := Real.rpow_natCast n n
    rw [h2, div_pow]
  have h_exp_n : Real.exp ((n : ℝ) * Real.log n) = (n : ℝ) ^ (n : ℝ) := by
    rw [mul_comm, Real.rpow_def_of_pos hn_pos]
  have h_sqrt : Real.exp (Real.log (2 * Real.pi * n) / 2) = Real.sqrt (2 * Real.pi * n) :=
    exp_half_log (by positivity : 0 < 2 * Real.pi * n)
  convert h_exp using 1
  rw [Real.exp_add]
  have hexp_ne : Real.exp (1 / (12 * (n : ℝ))) ≠ 0 := Real.exp_ne_zero _
  apply mul_right_cancel₀ hexp_ne
  have hA :
      (n : ℝ) * Real.log n - n + Real.log (2 * Real.pi * n) / 2
        = ((n : ℝ) * Real.log n - n) + Real.log (2 * Real.pi * n) / 2 := by
    ring
  rw [hA, Real.exp_add, h_sqrt]
  have hExpMain :
      Real.exp ((n : ℝ) * Real.log n - n) = ((n : ℝ) / Real.exp 1) ^ n := by
    rw [Real.exp_sub]
    rw [h_exp_n]
    simpa [div_eq_mul_inv, Real.exp_nat_mul] using h_pow_eq
  simp [hExpMain, mul_left_comm, mul_comm]

/-! ## Section 4: Lower bound -/

/-- The Robbins lower bound. -/
theorem factorial_lower_robbins (n : ℕ) (hn : 0 < n) :
    Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n * Real.exp (1 / (12 * n + 1)) ≤
      n.factorial := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h_J_ge : (1 + (n : ℝ) * 12)⁻¹ ≤ (Binet.J n).re := by
    have := (Binet.re_J_robbins_bounds hn_pos).1
    convert this using 1
    ring
  have h_log_ge :
      n * Real.log n - n + Real.log (2 * Real.pi * n) / 2 + 1 / (12 * n + 1) ≤
        Real.log (n.factorial : ℝ) := by
    have h_fact : Real.log (n.factorial) = Real.log n + Real.log (Real.Gamma n) := by
      exact log_factorial_eq_log_nat_add_log_Gamma hn
    have h_binet :
        Real.log (Real.Gamma n) =
          (n - 1/2) * Real.log n - n + Real.log (2 * Real.pi) / 2 + (Binet.J n).re := by
      exact Binet.log_Gamma_real_eq hn_pos
    rw [h_fact, h_binet]
    have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by nlinarith [Real.pi_pos]
    rw [Real.log_mul h2pi_pos.ne' (Nat.cast_pos.mpr hn).ne']
    ring_nf
    simp only [add_le_add_iff_left]
    exact h_J_ge
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by nlinarith [Real.pi_pos]
  have h_sqrt_pos : 0 < Real.sqrt (2 * Real.pi * n) := by
    apply Real.sqrt_pos.mpr
    simpa [mul_assoc] using (mul_pos h2pi_pos hn_pos)
  rw [← Real.log_le_log_iff
    (mul_pos (mul_pos h_sqrt_pos (pow_pos (div_pos hn_pos (Real.exp_pos 1)) n)) (Real.exp_pos _))
    (Nat.cast_pos.mpr (Nat.factorial_pos n))]
  calc
    Real.log
        (Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n *
          Real.exp (1 / (12 * n + 1))) =
        n * Real.log n - n + Real.log (2 * Real.pi * n) / 2 + 1 / (12 * n + 1) := by
      rw [Real.log_mul
        (mul_pos h_sqrt_pos (pow_pos (div_pos hn_pos (Real.exp_pos 1)) n)).ne'
        (Real.exp_pos _).ne']
      rw [Real.log_exp, log_stirlingFactor hn]
    _ ≤ Real.log (n.factorial : ℝ) := h_log_ge

/-! ## Section 5: Two-sided bound -/

/-- The complete Robbins bound of [robbins1955]. -/
theorem factorial_robbins (n : ℕ) (hn : 0 < n) :
    Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n * Real.exp (1 / (12 * n + 1)) ≤
      n.factorial ∧
    (n.factorial : ℝ) ≤
      Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n * Real.exp (1 / (12 * n)) :=
  ⟨factorial_lower_robbins n hn, factorial_upper_robbins n hn⟩

/-! ## Section 6: Robbins bounds for the Stirling sequence -/

private lemma stirlingSeq_den_pos (n : ℕ) (hn : 0 < n) :
    0 < Real.sqrt (2 * n) * (n / Real.exp 1) ^ n := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  exact mul_pos (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 2 * n))
    (pow_pos (div_pos hn_pos (Real.exp_pos 1)) n)

private lemma sqrt_two_pi_factor_eq_sqrt_pi_mul (n : ℕ) :
    Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n =
      Real.sqrt Real.pi * (Real.sqrt (2 * n) * (n / Real.exp 1) ^ n) := by
  simp [Real.sqrt_mul']
  ring

/-- Robbins' lower bound, normalized as a lower bound for the Stirling sequence. -/
theorem sqrt_pi_mul_exp_inv_twelve_mul_add_one_le_stirlingSeq
    (n : ℕ) (hn : 0 < n) :
    Real.sqrt Real.pi * Real.exp (1 / (12 * n + 1)) ≤ stirlingSeq n := by
  have h := factorial_lower_robbins n hn
  have hden_pos := stirlingSeq_den_pos n hn
  rw [stirlingSeq]
  refine (le_div_iff₀ hden_pos).2 ?_
  calc
    Real.sqrt Real.pi * Real.exp (1 / (12 * n + 1)) *
        (Real.sqrt (2 * n) * (n / Real.exp 1) ^ n)
        = Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n *
            Real.exp (1 / (12 * n + 1)) := by
          rw [sqrt_two_pi_factor_eq_sqrt_pi_mul]
          ring
    _ ≤ (n.factorial : ℝ) := h

/-- Robbins' upper bound, normalized as an upper bound for the Stirling sequence. -/
theorem stirlingSeq_le_sqrt_pi_mul_exp_inv_twelve_mul
    (n : ℕ) (hn : 0 < n) :
    stirlingSeq n ≤ Real.sqrt Real.pi * Real.exp (1 / (12 * n)) := by
  have h := factorial_upper_robbins n hn
  have hden_pos := stirlingSeq_den_pos n hn
  rw [stirlingSeq]
  refine (div_le_iff₀ hden_pos).2 ?_
  calc
    (n.factorial : ℝ)
        ≤ Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n *
            Real.exp (1 / (12 * n)) := h
    _ = Real.sqrt Real.pi * Real.exp (1 / (12 * n)) *
        (Real.sqrt (2 * n) * (n / Real.exp 1) ^ n) := by
          rw [sqrt_two_pi_factor_eq_sqrt_pi_mul]
          ring

/-- Robbins' lower bound for `stirlingSeq n / √π`. -/
theorem exp_inv_twelve_mul_add_one_le_stirlingSeq_div_sqrt_pi
    (n : ℕ) (hn : 0 < n) :
    Real.exp (1 / (12 * n + 1)) ≤ stirlingSeq n / Real.sqrt Real.pi := by
  rw [le_div_iff₀ (Real.sqrt_pos.mpr Real.pi_pos)]
  simpa [mul_comm] using sqrt_pi_mul_exp_inv_twelve_mul_add_one_le_stirlingSeq n hn

/-- Robbins' upper bound for `stirlingSeq n / √π`. -/
theorem stirlingSeq_div_sqrt_pi_le_exp_inv_twelve_mul
    (n : ℕ) (hn : 0 < n) :
    stirlingSeq n / Real.sqrt Real.pi ≤ Real.exp (1 / (12 * n)) := by
  rw [div_le_iff₀ (Real.sqrt_pos.mpr Real.pi_pos)]
  simpa [mul_comm] using stirlingSeq_le_sqrt_pi_mul_exp_inv_twelve_mul n hn

/-- The complete Robbins bound for the Stirling sequence. -/
theorem stirlingSeq_robbins (n : ℕ) (hn : 0 < n) :
    Real.sqrt Real.pi * Real.exp (1 / (12 * n + 1)) ≤ stirlingSeq n ∧
      stirlingSeq n ≤ Real.sqrt Real.pi * Real.exp (1 / (12 * n)) :=
  ⟨sqrt_pi_mul_exp_inv_twelve_mul_add_one_le_stirlingSeq n hn,
    stirlingSeq_le_sqrt_pi_mul_exp_inv_twelve_mul n hn⟩

/-- The complete Robbins bound for the normalized ratio `stirlingSeq n / √π`. -/
theorem stirlingSeq_div_sqrt_pi_robbins (n : ℕ) (hn : 0 < n) :
    Real.exp (1 / (12 * n + 1)) ≤ stirlingSeq n / Real.sqrt Real.pi ∧
      stirlingSeq n / Real.sqrt Real.pi ≤ Real.exp (1 / (12 * n)) :=
  ⟨exp_inv_twelve_mul_add_one_le_stirlingSeq_div_sqrt_pi n hn,
    stirlingSeq_div_sqrt_pi_le_exp_inv_twelve_mul n hn⟩

/-! ## Section 7: Asymptotic equivalence -/

/-- The ratio n! / (√(2πn)(n/e)^n) → 1 as n → ∞. -/
theorem factorial_asymptotic :
    Tendsto (fun n : ℕ => (n.factorial : ℝ) /
      (Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n)) atTop (𝓝 1) := by
  let lower (n : ℕ) := (1 : ℝ)
  let upper (n : ℕ) := Real.exp (1 / (12 * n))
  have h_squeeze :
      ∀ᶠ n in atTop,
        lower n ≤
          (n.factorial : ℝ) / (Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n) ∧
        (n.factorial : ℝ) /
            (Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n) ≤ upper n := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    obtain ⟨θ, hθ_pos, hθ_lt_one, hlog⟩ := log_factorial_theta hn
    let stirling := Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n
    have h_stirling_pos : 0 < stirling := by
      apply mul_pos
      · have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by nlinarith [Real.pi_pos]
        have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
        exact Real.sqrt_pos.mpr (mul_pos h2pi_pos hn_pos)
      · apply pow_pos; apply div_pos (Nat.cast_pos.mpr hn) (Real.exp_pos 1)
    rw [le_div_iff₀ h_stirling_pos, div_le_iff₀ h_stirling_pos]
    have h_log_stirling :
        Real.log stirling = n * Real.log n - n + Real.log (2 * Real.pi * n) / 2 := by
      simpa [stirling] using log_stirlingFactor hn
    constructor
    · dsimp [lower]
      rw [one_mul]
      rw [← Real.log_le_log_iff h_stirling_pos (Nat.cast_pos.mpr (Nat.factorial_pos n)),
        h_log_stirling]
      rw [hlog]
      simp only [le_add_iff_nonneg_right]
      positivity
    · dsimp [upper]
      rw [← Real.log_le_log_iff (Nat.cast_pos.mpr (Nat.factorial_pos n))
        (mul_pos (Real.exp_pos _) h_stirling_pos)]
      rw [Real.log_mul (Real.exp_pos _).ne' h_stirling_pos.ne', Real.log_exp,
        h_log_stirling]
      rw [hlog]
      have hn' : (0 : ℝ) < 12 * (n : ℝ) := by
        have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
        nlinarith
      have hθle : θ ≤ 1 := le_of_lt hθ_lt_one
      have hθ_div : θ / (12 * (n : ℝ)) ≤ 1 / (12 * (n : ℝ)) :=
        div_le_div_of_nonneg_right hθle (le_of_lt hn')
      set c : ℝ := (n : ℝ) * Real.log n - n + Real.log (2 * Real.pi * n) / 2
      have hc : c + θ / (12 * (n : ℝ)) ≤ c + 1 / (12 * (n : ℝ)) := by
        simpa [c, add_assoc, add_left_comm, add_comm] using add_le_add_left hθ_div c
      simpa [one_div, c, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm,
        mul_comm] using hc
  refine (tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (f := fun n : ℕ =>
      (n.factorial : ℝ) / (Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n))
    (g := lower) (h := upper) tendsto_const_nhds ?_ ?_ ?_)
  · have h_lim : Tendsto (fun n : ℕ => 1 / (12 * (n : ℝ))) atTop (𝓝 (0 : ℝ)) := by
      have h_to : Tendsto (fun n : ℕ => (12 : ℝ) * (n : ℝ)) atTop atTop := by
        have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := by
          simpa using (tendsto_natCast_atTop_atTop : Tendsto (Nat.cast : ℕ → ℝ) atTop atTop)
        simpa [mul_comm] using
          (Filter.Tendsto.const_mul_atTop (β := ℕ) (α := ℝ) (r := (12 : ℝ)) (by positivity) hn)
      have h_inv : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 (0 : ℝ)) := by
        simpa using (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 (0 : ℝ)))
      have : Tendsto (fun n : ℕ => ((12 : ℝ) * (n : ℝ))⁻¹) atTop (𝓝 (0 : ℝ)) :=
        h_inv.comp h_to
      simpa [one_div] using this
    have h_exp : Tendsto Real.exp (𝓝 (0 : ℝ)) (𝓝 (Real.exp (0 : ℝ))) :=
      Real.continuous_exp.tendsto (0 : ℝ)
    have : Tendsto (fun n : ℕ => Real.exp (1 / (12 * (n : ℝ)))) atTop (𝓝 (Real.exp (0 : ℝ))) :=
      h_exp.comp h_lim
    simpa [upper, Real.exp_zero] using this
  · filter_upwards [h_squeeze] with n hn
    exact hn.1
  · filter_upwards [h_squeeze] with n hn
    exact hn.2

/-- Stirling's approximation: `n! ~ √(2πn)(n/e)^n`.

This derives the usual asymptotic equivalence from the Robbins squeeze proof above; compare
`factorial_isEquivalent_stirling` in `Mathlib.Analysis.SpecialFunctions.Stirling`. -/
theorem stirling_asymptotic :
    Asymptotics.IsEquivalent atTop
      (fun n : ℕ => (n.factorial : ℝ))
      (fun n : ℕ => Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n) := by
  rw [Asymptotics.isEquivalent_iff_tendsto_one]
  · exact factorial_asymptotic
  · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    apply ne_of_gt
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    apply mul_pos (Real.sqrt_pos.mpr _) (pow_pos _ _)
    · positivity
    · have : 0 < n / Real.exp 1 := div_pos hn_pos (Real.exp_pos 1)
      linarith

end Stirling

/-! ## Section 8: Convenient API -/

namespace Nat

/-- Upper bound: n! ≤ √(2πn)(n/e)^n · e^{1/(12n)} for n ≥ 1. -/
theorem factorial_le_stirling_upper (n : ℕ) (hn : 0 < n) :
    (n.factorial : ℝ) ≤
      Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n * Real.exp (1 / (12 * n)) :=
  Stirling.factorial_upper_robbins n hn

/-- Lower bound: √(2πn)(n/e)^n · e^{1/(12n+1)} ≤ n! for n ≥ 1. -/
theorem factorial_ge_stirling_lower (n : ℕ) (hn : 0 < n) :
    Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n * Real.exp (1 / (12 * n + 1)) ≤
      n.factorial :=
  Stirling.factorial_lower_robbins n hn

/-- Robbins' two-sided factorial estimate, bundled for use outside the `Stirling` namespace. -/
theorem factorial_robbins (n : ℕ) (hn : 0 < n) :
    Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n * Real.exp (1 / (12 * n + 1)) ≤
        n.factorial ∧
      (n.factorial : ℝ) ≤
        Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n * Real.exp (1 / (12 * n)) :=
  ⟨factorial_ge_stirling_lower n hn, factorial_le_stirling_upper n hn⟩

end Nat

end
