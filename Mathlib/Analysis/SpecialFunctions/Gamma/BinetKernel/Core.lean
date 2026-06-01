/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module


public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Tactic.NormNum.NatFactorial




/-!
# The Binet kernel

The kernel `K(t) = 1 / (exp t - 1) - 1 / t + 1 / 2` and its normalization `Ktilde` used in Binet's
formula for `log Γ`.

## Main definitions

* `BinetKernel.K`, `BinetKernel.Ktilde` : the Binet kernel and `K(t) / t` for `t > 0`

## Main results

* `BinetKernel.Ktilde_nonneg`, `BinetKernel.Ktilde_le` : `0 ≤ Ktilde t ≤ 1/12` for `t ≥ 0`
* `BinetKernel.K_eq_alt` : equivalent rational form of `K`
-/

open Real Set Filter MeasureTheory Topology
open scoped Topology

@[expose] public section

namespace BinetKernel

/-! ### General monotonicity and positivity lemmas -/

/-- If a function has nonnegative derivative on `[0, ∞)`, it is monotone there. -/
lemma monotoneOn_of_deriv_nonneg_Ici {f : ℝ → ℝ}
    (hf : DifferentiableOn ℝ f (Set.Ici 0))
    (hderiv : ∀ x ∈ Set.Ici 0, 0 ≤ deriv f x) :
    MonotoneOn f (Set.Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hf.continuousOn (hf.mono interior_subset)
  intro x hx
  rw [interior_Ici] at hx
  exact hderiv x (Set.mem_Ici.mpr (le_of_lt hx))

/-- If `deriv f ≥ 0` on `[0, ∞)` and `f 0 = 0`, then `f x ≥ 0` for `x ≥ 0`. -/
lemma nonneg_of_deriv_nonneg_Ici {f : ℝ → ℝ}
    (hf : DifferentiableOn ℝ f (Set.Ici 0))
    (hderiv : ∀ x ∈ Set.Ici 0, 0 ≤ deriv f x) (h0 : f 0 = 0) :
    ∀ {x}, 0 ≤ x → 0 ≤ f x := by
  intro x hx
  have hmono := monotoneOn_of_deriv_nonneg_Ici hf hderiv
  have hx' : x ∈ Set.Ici 0 := hx
  have h0' : (0 : ℝ) ∈ Set.Ici 0 := by simp
  have hle := hmono h0' hx' hx
  simpa [h0] using hle

/-! ### Taylor-type lower bounds for exp

These are already in Mathlib as `Real.sum_le_exp_of_nonneg` and `Real.quadratic_le_exp_of_nonneg`.
We provide convenient aliases with the naming convention used here.
-/

/-- The function `exp x - 1 - x` is nonnegative for `x ≥ 0`.
This is the error term in the first-order Taylor approximation.
Alias for the consequence of `Real.add_one_le_exp`. -/
lemma exp_sub_one_sub_x_nonneg {x : ℝ} (_hx : 0 ≤ x) : 0 ≤ Real.exp x - 1 - x := by
  have h := Real.add_one_le_exp x
  linarith

/-- For `t ≥ 0`, we have `exp t ≥ 1 + t + t²/2`.
This is `Real.quadratic_le_exp_of_nonneg` from Mathlib. -/
lemma exp_ge_one_add_sq {t : ℝ} (ht : 0 ≤ t) : 1 + t + t ^ 2 / 2 ≤ Real.exp t :=
  Real.quadratic_le_exp_of_nonneg ht

/-- For `t ≥ 0`, we have `exp t ≥ 1 + t + t²/2 + t³/6`.
Uses `Real.sum_le_exp_of_nonneg` with n = 4. -/
lemma exp_ge_one_add_cu {t : ℝ} (ht : 0 ≤ t) :
    1 + t + t ^ 2 / 2 + t ^ 3 / 6 ≤ Real.exp t := by
  have h := Real.sum_le_exp_of_nonneg ht 4
  simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
    pow_zero, Nat.cast_one, div_one, pow_one, Nat.factorial] at h
  convert h using 1; ring

/-- For `t ≥ 0`, we have `exp t ≥ 1 + t + t²/2 + t³/6 + t⁴/24`.
Uses `Real.sum_le_exp_of_nonneg` with n = 5. -/
lemma exp_ge_one_add_quartic {t : ℝ} (ht : 0 ≤ t) :
    1 + t + t ^ 2 / 2 + t ^ 3 / 6 + t ^ 4 / 24 ≤ Real.exp t := by
  have h := Real.sum_le_exp_of_nonneg ht 5
  simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
    pow_zero, Nat.cast_one, div_one, pow_one, Nat.factorial] at h
  convert h using 1; ring

/-! ## Section 1: Basic definitions and elementary properties -/

/-- The unnormalized Binet kernel: K(t) = 1/(e^t - 1) - 1/t + 1/2 for t > 0. -/
noncomputable def K (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else 1/(Real.exp t - 1) - 1/t + 1/2

/-- The normalized Binet kernel: K̃(t) = K(t)/t for t > 0.
This is the kernel that appears in the Binet integral. -/
noncomputable def Ktilde (t : ℝ) : ℝ :=
  if t ≤ 0 then 1/12 else (1/(Real.exp t - 1) - 1/t + 1/2) / t

/-- For t > 0, K has the explicit formula. -/
lemma K_pos {t : ℝ} (ht : 0 < t) : K t = 1/(Real.exp t - 1) - 1/t + 1/2 := by
  simp [K, not_le.mpr ht]

/-- For t > 0, K̃ has the explicit formula. -/
lemma Ktilde_pos {t : ℝ} (ht : 0 < t) :
    Ktilde t = (1/(Real.exp t - 1) - 1/t + 1/2) / t := by
  simp [Ktilde, not_le.mpr ht]

/-- K̃(0) = 1/12 by definition (the limit value). -/
lemma Ktilde_zero : Ktilde 0 = 1/12 := by simp [Ktilde]

/-! ## Section 2: The key identity for the kernel -/

/-- For t > 0, e^t > 1, so e^t - 1 > 0. -/
lemma exp_sub_one_pos {t : ℝ} (ht : 0 < t) : 0 < Real.exp t - 1 := by
  have h1 : Real.exp 0 = 1 := Real.exp_zero
  have h2 : Real.exp t > Real.exp 0 := Real.exp_lt_exp.mpr ht
  linarith

/-- K̃ is continuous on (0, ∞). -/
lemma continuousOn_Ktilde_Ioi : ContinuousOn Ktilde (Set.Ioi 0) := by
  intro t ht
  have hne_t : t ≠ 0 := ne_of_gt ht
  have hne_exp : Real.exp t - 1 ≠ 0 := ne_of_gt (exp_sub_one_pos ht)
  have h1 : ContinuousAt (fun x => 1 / (Real.exp x - 1)) t :=
    continuousAt_const.div (Real.continuous_exp.continuousAt.sub continuousAt_const) hne_exp
  have h2 : ContinuousAt (fun x => 1 / x) t := continuousAt_const.div continuousAt_id hne_t
  have h3 : ContinuousAt (fun x => 1 / (Real.exp x - 1) - 1 / x + 1 / 2) t :=
    (h1.sub h2).add continuousAt_const
  have h4 : ContinuousAt (fun x => (1 / (Real.exp x - 1) - 1 / x + 1 / 2) / x) t :=
    h3.div continuousAt_id hne_t
  apply h4.continuousWithinAt.congr
  · intro y hy
    unfold Ktilde
    rw [if_neg (not_le.mpr hy)]
  · unfold Ktilde
    rw [if_neg (not_le.mpr ht)]



/-- Key algebraic identity: For t > 0,
  K(t) = 1/(e^t - 1) - 1/t + 1/2 = (t - (e^t - 1) + t(e^t - 1)/2) / (t(e^t - 1))
This helps analyze the sign and bounds. -/
lemma K_eq_alt {t : ℝ} (ht : 0 < t) :
    K t = (t - (Real.exp t - 1) + t * (Real.exp t - 1) / 2) / (t * (Real.exp t - 1)) := by
  rw [K_pos ht]
  have hexp : Real.exp t - 1 > 0 := exp_sub_one_pos ht
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have hexp_ne : Real.exp t - 1 ≠ 0 := ne_of_gt hexp
  field_simp

/-- Alternative form: K(t) = (e^t(t-2) + t + 2) / (2t(e^t - 1)) -/
lemma K_eq_alt' {t : ℝ} (ht : 0 < t) :
    K t = (Real.exp t * (t - 2) + t + 2) / (2 * t * (Real.exp t - 1)) := by
  rw [K_pos ht]
  have hexp : Real.exp t - 1 > 0 := exp_sub_one_pos ht
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have hexp_ne : Real.exp t - 1 ≠ 0 := ne_of_gt hexp
  field_simp
  ring

end BinetKernel

