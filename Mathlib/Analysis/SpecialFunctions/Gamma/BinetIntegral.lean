/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.BinetKernel

/-!
# The Binet Integral

This file defines the Binet correction integral
`J z = ∫₀^∞ K̃(t) exp (-t z) dt` and proves its basic norm estimates.

## References

* [DLMF], §5.9.10_2 for Binet's first integral formula
* [DLMF], §5.11 for the surrounding Stirling asymptotic estimates
* [whittakerWatson1927], Chapter XII for the classical Gamma-function background
-/

open Real Complex Set MeasureTheory Filter Topology BinetKernel

@[expose] public section

noncomputable section

namespace Binet

/-- The Binet integral `J(z) = ∫₀^∞ K̃(t) e^{-tz} dt`.

This is the correction term in Binet's formula for `log Γ`. It is defined to be zero off the
right half-plane as a Mathlib auxiliary convention; the Binet and Robbins estimates use
arguments with positive real part. -/
def J (z : ℂ) : ℂ :=
  if 0 < z.re then
    ∫ t in Set.Ioi (0 : ℝ), (Ktilde t : ℂ) * Complex.exp (-t * z)
  else 0

/-- The Binet integral is integrable on the right half-plane. -/
lemma J_well_defined {z : ℂ} (hz : 0 < z.re) :
    Integrable (fun t : ℝ => (Ktilde t : ℂ) * Complex.exp (-t * z))
      (volume.restrict (Set.Ioi 0)) :=
  BinetKernel.integrable_Ktilde_exp_complex hz

/-- On the right half-plane, `J` is the defining integral. -/
lemma J_eq_integral {z : ℂ} (hz : 0 < z.re) :
    J z = ∫ t in Set.Ioi (0 : ℝ), (Ktilde t : ℂ) * Complex.exp (-t * z) := by
  simp only [J, if_pos hz]

/-- Off the right half-plane, the auxiliary Binet integral is defined to be zero. -/
lemma J_eq_zero_of_re_nonpos {z : ℂ} (hz : z.re ≤ 0) : J z = 0 := by
  simp [J, not_lt.mpr hz]

/-- Norm of the Binet integrand. -/
lemma norm_Ktilde_mul_exp {z : ℂ} (t : ℝ) (ht : 0 < t) :
    ‖(Ktilde t : ℂ) * Complex.exp (-t * z)‖ = Ktilde t * Real.exp (-t * z.re) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Ktilde_nonneg (le_of_lt ht)), Complex.norm_exp]
  congr 1
  have : ((-↑t * z).re) = -t * z.re := by
    simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [this]

/-- `K̃(t) * exp (-t*x)` is integrable on `(0, ∞)` for `x > 0`. -/
lemma integrable_Ktilde_mul_exp_real {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => Ktilde t * Real.exp (-t * x)) (Set.Ioi 0) := by
  exact BinetKernel.integrable_Ktilde_exp hx

/-- `(1/12) * exp (-t*x)` is integrable on `(0, ∞)` for `x > 0`. -/
lemma integrable_const_mul_exp {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => (1 / 12 : ℝ) * Real.exp (-t * x)) (Set.Ioi 0) := by
  apply Integrable.const_mul
  have h := integrableOn_exp_mul_Ioi (neg_neg_of_pos hx) 0
  refine h.congr_fun ?_ measurableSet_Ioi
  intro t _
  ring_nf

/-- Pointwise bound for the Binet kernel against the elementary exponential majorant. -/
lemma Ktilde_mul_exp_le {x : ℝ} (t : ℝ) (ht : 0 < t) :
    Ktilde t * Real.exp (-t * x) ≤ (1 / 12 : ℝ) * Real.exp (-t * x) :=
  mul_le_mul_of_nonneg_right (Ktilde_le (le_of_lt ht)) (Real.exp_nonneg _)

/-- The integral of `exp (-t*x)` on `(0, ∞)`. -/
lemma integral_exp_neg_mul_Ioi {x : ℝ} (hx : 0 < x) :
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t * x) = 1 / x := by
  have h := integral_exp_mul_Ioi (neg_neg_of_pos hx) 0
  simp only [mul_zero, Real.exp_zero] at h
  have heq : (fun t => Real.exp (-t * x)) = (fun t => Real.exp (-x * t)) := by
    ext t
    ring_nf
  rw [heq, h]
  field_simp

/-- The fundamental estimate `‖J z‖ ≤ 1 / (12 * re z)` on the right half-plane. -/
theorem J_norm_le_re {z : ℂ} (hz : 0 < z.re) : ‖J z‖ ≤ 1 / (12 * z.re) := by
  rw [J_eq_integral hz]
  calc ‖∫ t in Set.Ioi (0 : ℝ), (Ktilde t : ℂ) * Complex.exp (-t * z)‖
      ≤ ∫ t in Set.Ioi (0 : ℝ), ‖(Ktilde t : ℂ) * Complex.exp (-t * z)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t in Set.Ioi (0 : ℝ), Ktilde t * Real.exp (-t * z.re) := by
        apply MeasureTheory.setIntegral_mono_on
        · exact (J_well_defined hz).norm
        · exact integrable_Ktilde_mul_exp_real hz
        · exact measurableSet_Ioi
        · intro t ht
          rw [norm_Ktilde_mul_exp t ht]
    _ ≤ ∫ t in Set.Ioi (0 : ℝ), (1 / 12 : ℝ) * Real.exp (-t * z.re) := by
        apply MeasureTheory.setIntegral_mono_on
        · exact integrable_Ktilde_mul_exp_real hz
        · exact integrable_const_mul_exp hz
        · exact measurableSet_Ioi
        · intro t ht
          exact Ktilde_mul_exp_le t ht
    _ = (1 / 12 : ℝ) * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t * z.re) := by
        rw [← MeasureTheory.integral_const_mul]
    _ = (1 / 12 : ℝ) * (1 / z.re) := by
        rw [integral_exp_neg_mul_Ioi hz]
    _ = 1 / (12 * z.re) := by ring

/-- Real positive specialization of `Binet.J_norm_le_re`. -/
theorem J_norm_le_real {x : ℝ} (hx : 0 < x) : ‖J (x : ℂ)‖ ≤ 1 / (12 * x) := by
  have hre : (0 : ℝ) < (x : ℂ).re := by simp [hx]
  have h := J_norm_le_re hre
  simp only [Complex.ofReal_re] at h
  exact h

end Binet
