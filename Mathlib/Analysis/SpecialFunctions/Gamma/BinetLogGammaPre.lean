/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.SpecialFunctions.Gamma.BinetRealIntegral

/-!
# Binet's formula for `log Γ` on the positive real axis

Algebraic helpers, the correction term `R`, and kernel identities for Binet's formula for `log Γ`.
The recurrence for `re (J x)` is in `BinetLogGammaRecurrence`; the limit and closed form are in
`BinetLogGamma`.
-/

open Real Complex Set Filter Topology MeasureTheory BinetKernel
open scoped BigOperators Nat

@[expose] public section

noncomputable section

namespace Binet

/-!
### Small algebraic helpers

Elementary estimates used in the real-variable part of Binet's formula.
-/

lemma one_div_cast_sub_le_two_div_cast (n : ℕ) (hn2 : 2 ≤ n) :
    (1 : ℝ) / ((n - 1 : ℕ) : ℝ) ≤ (2 : ℝ) / (n : ℝ) := by
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hn2))
  have hn1_pos : 0 < ((n - 1 : ℕ) : ℝ) := by
    have : 0 < n - 1 := Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hn2)
    exact_mod_cast this
  refine (div_le_div_iff₀ hn1_pos hn_pos).2 ?_
  have hn1_ge1 : (1 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
    have : (1 : ℕ) ≤ n - 1 := Nat.sub_le_sub_right hn2 1
    exact_mod_cast this
  have hn_nat_pos : 0 < n := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hn2
  have hnat : (n - 1 : ℕ) + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn_nat_pos)
  have hcast : (n : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast hnat.symm
  nlinarith [hn1_ge1, hcast]

/-! ## Binet's formula for log Γ -/

/-!
### About a complex `log Γ` statement

Be careful: a statement of the form

`Complex.log (Complex.Gamma z) = (z - 1/2) * Complex.log z - z + log(2π)/2 + J z`

using the *principal* complex logarithm `Complex.log` is **not valid on all of** `{z | 0 < re z}`:
`Γ` crosses the negative real axis infinitely many times in the right half-plane, so the composite
`Complex.log ∘ Complex.Gamma` cannot be holomorphic there.  A complex formulation should instead use
a holomorphic branch of `log Γ`
(often called `logGamma`) on a suitable simply-connected domain.
-/

/-- The Stirling main terms for real `x`. -/
def stirlingMainReal (x : ℝ) : ℝ :=
  (x - 1 / 2) * Real.log x - x + Real.log (2 * Real.pi) / 2

/-- The (real) Stirling correction term:
`R(x) := log Γ(x) - ((x - 1/2) log x - x + log(2π)/2)`. -/
def R (x : ℝ) : ℝ :=
  Real.log (Real.Gamma x) - stirlingMainReal x

private lemma stirlingMainReal_add_one_sub {x : ℝ} (hx : 0 < x) :
    stirlingMainReal (x + 1) - stirlingMainReal x =
      Real.log x + (x + 1 / 2) * Real.log (1 + 1 / x) - 1 := by
  unfold stirlingMainReal
  have hx1 : 0 < x + 1 := by linarith
  have hlog_sum : Real.log (x + 1) = Real.log x + Real.log (1 + 1 / x) := by
    have hx0 : x ≠ 0 := ne_of_gt hx
    have h1 : x + 1 = x * (1 + 1 / x) := by
      calc
        x + 1 = x + x * (1 / x) := by simp [hx0]
        _ = x * (1 + 1 / x) := by ring
    -- `Real.log_mul` is valid for nonzero factors (since `Real.log` is `log ∘ abs`).
    rw [h1, Real.log_mul hx0 (by
      -- `1 + 1/x ≠ 0` since it is positive
      have : 0 < (1 + 1 / x) := by
        have : 0 < (1 / x : ℝ) := by positivity
        linarith
      exact ne_of_gt this)]
  rw [hlog_sum]
  ring

lemma R_sub_R_add_one {x : ℝ} (hx : 0 < x) :
    R x - R (x + 1) = (x + 1 / 2) * Real.log (1 + 1 / x) - 1 := by
  unfold R
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hΓ_diff :
      Real.log (Real.Gamma (x + 1)) - Real.log (Real.Gamma x) = Real.log x := by
    -- Γ(x+1) = x·Γ(x)
    have hΓ : Real.Gamma (x + 1) = x * Real.Gamma x := Real.Gamma_add_one (s := x) hx0
    have hΓx_ne : Real.Gamma x ≠ 0 := (Real.Gamma_pos_of_pos hx).ne'
    -- take logs and subtract
    calc
      Real.log (Real.Gamma (x + 1)) - Real.log (Real.Gamma x)
          = (Real.log x + Real.log (Real.Gamma x)) - Real.log (Real.Gamma x) := by
              simp [hΓ, Real.log_mul hx0 hΓx_ne]
      _ = Real.log x := by ring
  have hS := stirlingMainReal_add_one_sub (x := x) hx
  -- rearrange
  calc
    (Real.log (Real.Gamma x) - stirlingMainReal x)
        - (Real.log (Real.Gamma (x + 1)) - stirlingMainReal (x + 1))
        = (stirlingMainReal (x + 1) - stirlingMainReal x) -
            (Real.log (Real.Gamma (x + 1)) - Real.log (Real.Gamma x)) := by ring
    _ = (Real.log x + (x + 1 / 2) * Real.log (1 + 1 / x) - 1) - Real.log x := by
          simpa [hΓ_diff] using congrArg (fun t => t - Real.log x) hS
    _ = (x + 1 / 2) * Real.log (1 + 1 / x) - 1 := by ring

/-- Auxiliary identity: for `t > 0`,
`K̃(t) * (1 - exp(-t)) = ∫_{u∈[0,1]} (1/2 - u) * exp(-u*t) du`. -/
lemma Ktilde_mul_one_sub_exp_eq_integral {t : ℝ} (ht : 0 < t) :
    BinetKernel.Ktilde t * (1 - Real.exp (-t)) =
      ∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t) := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  -- Rewrite the set integral over `Icc` as an interval integral `0..1`.
  have hIcc :
      (∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t)) =
        ∫ u in (0 : ℝ)..1, (1 / 2 - u) * Real.exp (-u * t) := by
    -- `Icc` and `Ioc` have the same integral for `volume`, then use
    -- `intervalIntegral.integral_of_le`.
    have hIccIoc :
        (∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t)) =
          ∫ u in Set.Ioc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t) := by
      simpa using
        (MeasureTheory.integral_Icc_eq_integral_Ioc
          (μ := (volume : Measure ℝ)) (f := fun u : ℝ => (1 / 2 - u) * Real.exp (-u * t))
          (x := (0 : ℝ)) (y := (1 : ℝ)))
    have hIoc :
        ∫ u in Set.Ioc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t) =
          ∫ u in (0 : ℝ)..1, (1 / 2 - u) * Real.exp (-u * t) := by
      -- `intervalIntegral.integral_of_le` gives the other direction.
      simpa using
        (intervalIntegral.integral_of_le (μ := (volume : Measure ℝ))
          (a := (0 : ℝ)) (b := (1 : ℝ))
          (f := fun u : ℝ => (1 / 2 - u) * Real.exp (-u * t))
          (by norm_num : (0 : ℝ) ≤ 1)).symm
    exact hIccIoc.trans hIoc
  -- Compute the interval integral explicitly.
  rw [hIcc]
  -- Split into two integrals.
  have hInt_exp : IntervalIntegrable (fun u : ℝ => Real.exp (-u * t)) volume (0 : ℝ) 1 := by
    have hcont : Continuous (fun u : ℝ => Real.exp (-u * t)) := by
      fun_prop
    exact hcont.intervalIntegrable (μ := (volume : Measure ℝ)) (0 : ℝ) 1
  have hInt_u_exp :
      IntervalIntegrable (fun u : ℝ => u * Real.exp (-u * t)) volume (0 : ℝ) 1 :=
    by
    have hcont : Continuous (fun u : ℝ => u * Real.exp (-u * t)) := by
      fun_prop
    exact hcont.intervalIntegrable (μ := (volume : Measure ℝ)) (0 : ℝ) 1
  have h_split :
      (∫ u in (0 : ℝ)..1, (1 / 2 - u) * Real.exp (-u * t)) =
        (1 / 2 : ℝ) * (∫ u in (0 : ℝ)..1, Real.exp (-u * t)) -
          (∫ u in (0 : ℝ)..1, u * Real.exp (-u * t)) := by
    -- expand `(1/2 - u) * exp` and use linearity
    have hlin :
        (fun u : ℝ => (1 / 2 - u) * Real.exp (-u * t)) =
          (fun u : ℝ => (1 / 2 : ℝ) * Real.exp (-u * t)) -
            fun u : ℝ => u * Real.exp (-u * t) := by
      funext u
      simp [sub_mul]
    rw [hlin]
    -- apply `intervalIntegral.integral_sub`
    have hInt1 :
        IntervalIntegrable (fun u : ℝ => (1 / 2 : ℝ) * Real.exp (-u * t)) volume (0 : ℝ) 1 :=
      hInt_exp.const_mul (1 / 2 : ℝ)
    -- now linearity
    simpa [intervalIntegral.integral_const_mul] using
      (intervalIntegral.integral_sub (μ := (volume : Measure ℝ)) hInt1 hInt_u_exp)
  rw [h_split]
  -- First interval integral: ∫ exp(-u*t) du from 0 to 1.
  have h_exp :
      (∫ u in (0 : ℝ)..1, Real.exp (-u * t)) = (1 - Real.exp (-t)) / t := by
    -- FTC with antiderivative `u ↦ -(exp(-u*t))/t`.
    have hab : (0 : ℝ) ≤ 1 := by norm_num
    have hcont :
        ContinuousOn (fun u : ℝ => -(Real.exp (-u * t) / t)) (Set.Icc (0 : ℝ) 1) := by
      have hcont' : Continuous (fun u : ℝ => -(Real.exp (-u * t) / t)) := by
        fun_prop
      exact hcont'.continuousOn
    have hderiv :
        ∀ u ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun u : ℝ => -(Real.exp (-u * t) / t))
          (Real.exp (-u * t)) u := by
      intro u _hu
      -- derivative of `exp(-u*t)` is `(-t)*exp(-u*t)`
      have h_inner : HasDerivAt (fun u : ℝ => -u * t) (-t) u := by
        simpa [mul_assoc] using ((hasDerivAt_id u).mul_const (-t))
      have h_exp' : HasDerivAt (fun u : ℝ => Real.exp (-u * t))
          ((-t) * Real.exp (-u * t)) u := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using
          (Real.hasDerivAt_exp (-u * t)).comp u h_inner
      -- divide by `t` then negate
      have : HasDerivAt (fun u : ℝ => Real.exp (-u * t) / t)
          (((-t) * Real.exp (-u * t)) / t) u :=
        h_exp'.div_const t
      have : HasDerivAt (fun u : ℝ => -(Real.exp (-u * t) / t))
          (-(((-t) * Real.exp (-u * t)) / t)) u :=
        this.neg
      -- simplify derivative (commutativity of multiplication in ℝ)
      simpa [ht0, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
    have hint : IntervalIntegrable (fun u : ℝ => Real.exp (-u * t)) volume (0 : ℝ) 1 := hInt_exp
    have hFTC :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv hint
    -- Evaluate endpoints and simplify.
    have h' : (∫ u in (0 : ℝ)..1, Real.exp (-u * t)) = -(Real.exp (-t) / t) + t⁻¹ := by
      simpa [Real.exp_zero, ht0] using hFTC
    -- rewrite to the desired closed form
    calc
      (∫ u in (0 : ℝ)..1, Real.exp (-u * t)) = -(Real.exp (-t) / t) + t⁻¹ := h'
      _ = (1 - Real.exp (-t)) / t := by
          -- purely algebraic
          field_simp [ht0]
          ring
  -- Second interval integral: ∫ u * exp(-u*t) du from 0 to 1.
  have h_u_exp :
      (∫ u in (0 : ℝ)..1, u * Real.exp (-u * t)) =
        (1 - Real.exp (-t) * (t + 1)) / (t ^ 2) := by
    have hab : (0 : ℝ) ≤ 1 := by norm_num
    -- antiderivative `u ↦ -(u * exp(-u*t))/t - exp(-u*t)/t^2`
    let F : ℝ → ℝ := fun u =>
      -(u * Real.exp (-u * t)) / t - (Real.exp (-u * t)) / (t ^ 2)
    have hcont : ContinuousOn F (Set.Icc (0 : ℝ) 1) := by
      -- continuous on ℝ, hence on Icc
      refine (Continuous.continuousOn ?_)
      have hcont' : Continuous F := by
        -- all operations are continuous on ℝ since `t` is a constant and division is by constants
        fun_prop [F]
      exact hcont'
    have hderiv : ∀ u ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt F (u * Real.exp (-u * t)) u := by
      intro u _hu
      have h_inner : HasDerivAt (fun u : ℝ => -u * t) (-t) u := by
        simpa [mul_assoc] using ((hasDerivAt_id u).mul_const (-t))
      have h_exp' : HasDerivAt (fun u : ℝ => Real.exp (-u * t))
          ((-t) * Real.exp (-u * t)) u := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using
          (Real.hasDerivAt_exp (-u * t)).comp u h_inner
      have h_mul : HasDerivAt (fun u : ℝ => u * Real.exp (-u * t))
          (Real.exp (-u * t) + u * ((-t) * Real.exp (-u * t))) u := by
        simpa [mul_assoc, add_comm, add_left_comm, add_assoc] using (hasDerivAt_id u).mul h_exp'
      -- Differentiate the two summands of `F`.
      have hF1 :
          HasDerivAt (fun u : ℝ => -(u * Real.exp (-u * t)) / t)
            (-(Real.exp (-u * t) + u * ((-t) * Real.exp (-u * t))) / t) u := by
        have h_neg : HasDerivAt (fun x => -(x * Real.exp (-x * t)))
            (-(Real.exp (-u * t) + u * ((-t) * Real.exp (-u * t)))) u := h_mul.neg
        have h_div : HasDerivAt (fun x => -(x * Real.exp (-x * t)) / t)
            (-(Real.exp (-u * t) + u * ((-t) * Real.exp (-u * t))) / t) u := h_neg.div_const t
        simpa using h_div
      have hF2 :
          HasDerivAt (fun u : ℝ => (Real.exp (-u * t)) / (t ^ 2))
            (((-t) * Real.exp (-u * t)) / (t ^ 2)) u := by
        exact h_exp'.div_const (t ^ 2)
      have hF : HasDerivAt F
          (-(Real.exp (-u * t) + u * ((-t) * Real.exp (-u * t))) / t -
              ((-t) * Real.exp (-u * t)) / (t ^ 2)) u := by
        simpa [F] using hF1.sub hF2
      -- simplify the derivative to `u * exp(-u*t)`
      have : (-(Real.exp (-u * t) + u * ((-t) * Real.exp (-u * t))) / t -
              ((-t) * Real.exp (-u * t)) / (t ^ 2))
            = u * Real.exp (-u * t) := by
        have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
        field_simp [ht0, ht2]
        ring
      convert hF using 1
      have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
      field_simp [ht0, ht2]
      ring
    have hint :
        IntervalIntegrable (fun u : ℝ => u * Real.exp (-u * t)) volume (0 : ℝ) 1 :=
      hInt_u_exp
    have hFTC :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv hint
    -- evaluate `F` at endpoints and simplify
    have : (∫ u in (0 : ℝ)..1, u * Real.exp (-u * t)) = F 1 - F 0 := hFTC
    -- compute `F 1 - F 0`, then rewrite to the stated rational expression
    have h_eval :
        (∫ u in (0 : ℝ)..1, u * Real.exp (-u * t)) =
          (-(Real.exp (-t) / t) - Real.exp (-t) / (t ^ 2) + 1 / (t ^ 2)) := by
      simpa [F, ht0, pow_two, div_eq_mul_inv, sub_eq_add_neg,
        mul_assoc, mul_comm, mul_left_comm] using this
    have h_simp :
        (-(Real.exp (-t) / t) - Real.exp (-t) / (t ^ 2) + 1 / (t ^ 2)) =
          (1 - Real.exp (-t) * (t + 1)) / (t ^ 2) := by
      have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
      field_simp [ht0, ht2]
      ring
    exact h_eval.trans h_simp
  -- Put the explicit formulas together and simplify to match the kernel expression.
  -- Now rewrite the LHS using `Ktilde_pos` and simplify algebraically.
  have hkernel : BinetKernel.Ktilde t = (1 / (Real.exp t - 1) - 1 / t + 1 / 2) / t := by
    simpa [one_div] using (BinetKernel.Ktilde_pos (t := t) ht)
  -- Reduce to a purely algebraic identity.
  -- We use the computed expressions for the interval integrals.
  rw [h_exp, h_u_exp, hkernel]
  have h_exp_ne : Real.exp t - 1 ≠ 0 := ne_of_gt (BinetKernel.exp_sub_one_pos ht)
  -- `field_simp` with these denominators clears fractions.
  field_simp [ht0, h_exp_ne, Real.exp_neg, pow_two]
  have h_exp_mul : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
  ring_nf
  simp only [h_exp_mul]
  ring_nf; grind

end Binet

