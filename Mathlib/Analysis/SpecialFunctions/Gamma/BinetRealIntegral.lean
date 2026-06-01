/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.BinetIntegral

/-!
# Real specialization of the Binet integral

Identifies `re (J x)` with the real kernel integral for `x > 0`.
-/

open Real Complex Set MeasureTheory BinetKernel

@[expose] public section

noncomputable section

namespace Binet

/-- For `x > 0`, the real part of `J x` is the real Binet kernel integral. -/
theorem re_J_eq_integral_Ktilde {x : ℝ} (hx : 0 < x) :
    (Binet.J (x : ℂ)).re = ∫ t in Set.Ioi (0 : ℝ), BinetKernel.Ktilde t * Real.exp (-t * x) := by
  have hx' : 0 < (x : ℂ).re := by simpa using hx
  -- unfold `J`
  rw [Binet.J_eq_integral (z := (x : ℂ)) hx']
  -- move `re` inside the integral
  have hInt :
      Integrable (fun t : ℝ => (BinetKernel.Ktilde t : ℂ) * Complex.exp (-t * (x : ℂ)))
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
    Binet.J_well_defined (z := (x : ℂ)) hx'
  have hre :
      ∫ t in Set.Ioi (0 : ℝ),
          ((BinetKernel.Ktilde t : ℂ) * Complex.exp (-t * (x : ℂ))).re
        = (∫ t in Set.Ioi (0 : ℝ),
              (BinetKernel.Ktilde t : ℂ) * Complex.exp (-t * (x : ℂ))).re := by
    simpa using
      (integral_re (μ := volume.restrict (Set.Ioi (0 : ℝ)))
        (f := fun t : ℝ => (BinetKernel.Ktilde t : ℂ) * Complex.exp (-t * (x : ℂ))) hInt)
  -- rewrite `re (∫ ...)` using `hre`
  rw [← hre]
  -- pointwise simplification to a real integrand
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
  intro t _ht
  dsimp
  have hexp : Complex.exp (-t * (x : ℂ)) = (Real.exp (-t * x) : ℂ) := by
    have harg : (-t * (x : ℂ)) = ((-t * x : ℝ) : ℂ) := by simp
    calc
      Complex.exp (-t * (x : ℂ)) = Complex.exp ((-t * x : ℝ) : ℂ) := by simp [harg]
      _ = (Real.exp (-t * x) : ℂ) := by simp
  rw [hexp]
  simp [-Complex.ofReal_exp]

end Binet

