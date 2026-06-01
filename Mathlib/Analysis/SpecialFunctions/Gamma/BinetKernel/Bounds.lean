/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.BinetKernel.Core

/-!
# Taylor and Robbins bounds for the Binet kernel

Sign analysis, upper bounds, and the Robbins lower bound for `Ktilde`.
-/

open Real Set Filter MeasureTheory Topology
open scoped Topology

@[expose] public section

namespace BinetKernel

/-! ## Section 3: Sign analysis -/

/-- The function f(t) = e^t(t-2) + t + 2 that appears in the numerator.
We need to show f(t) ≥ 0 for t ≥ 0. -/
noncomputable def f (t : ℝ) : ℝ := Real.exp t * (t - 2) + t + 2

lemma f_zero : f 0 = 0 := by simp [f]

/-- The derivative of f(t) = e^t(t-2) + t + 2 is f'(t) = e^t(t-1) + 1. -/
lemma f_deriv (t : ℝ) : HasDerivAt f (Real.exp t * (t - 1) + 1) t := by
  unfold f
  -- f(t) = e^t * (t - 2) + t + 2
  -- f'(t) = e^t(t-2) + e^t + 1 = e^t(t-1) + 1
  have h1 : HasDerivAt Real.exp (Real.exp t) t := Real.hasDerivAt_exp t
  have h2 : HasDerivAt (fun x => x - 2) 1 t := (hasDerivAt_id t).sub_const 2
  have h3 : HasDerivAt (fun x => Real.exp x * (x - 2)) (Real.exp t * (t - 2) + Real.exp t * 1) t :=
    h1.mul h2
  have h4 : HasDerivAt (fun x => x + 2) 1 t := (hasDerivAt_id t).add_const 2
  have h5 := h3.add h4
  convert h5 using 1
  · ext x; simp only [Pi.add_apply]; ring
  · ring

lemma f_deriv' (t : ℝ) : deriv f t = Real.exp t * (t - 1) + 1 :=
  (f_deriv t).deriv

/-- f has a minimum at t = 1, where f(1) = 3 - e. -/
lemma f_at_one : f 1 = 3 - Real.exp 1 := by simp [f]; ring

/-- e < 3, so f(1) = 3 - e > 0. -/
lemma f_one_pos : 0 < f 1 := by
  rw [f_at_one]
  have h : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
  linarith

/-- For t > 0, e^t(1-t) < 1. This is because g(t) = e^t(1-t) is strictly decreasing
with g(0) = 1, so g(t) < 1 for t > 0.

Proof: g'(t) = e^t(1-t) + e^t(-1) = e^t(-t) = -te^t < 0 for t > 0.
By MVT: g(t) - g(0) = g'(c) * t < 0 for some c ∈ (0, t), so g(t) < g(0) = 1. -/
lemma exp_mul_one_sub_lt_one {t : ℝ} (ht : 0 < t) : Real.exp t * (1 - t) < 1 := by
  -- g(t) = e^t(1-t), g(0) = 1, and g is strictly decreasing for t > 0
  -- This can be proved via MVT or by direct analysis
  have hg_deriv : ∀ s, HasDerivAt (fun x => Real.exp x * (1 - x)) (-Real.exp s * s) s := by
    intro s
    have h1 : HasDerivAt Real.exp (Real.exp s) s := Real.hasDerivAt_exp s
    have h2 : HasDerivAt (fun x => 1 - x) (-1) s := by
      have := (hasDerivAt_const s 1).sub (hasDerivAt_id s)
      simp only at this
      convert this using 1; ring
    have h3 := h1.mul h2
    convert h3 using 1; ring
  -- Use strict monotonicity: g'(t) = -te^t < 0 for t > 0
  have hg_mono : StrictAntiOn (fun x => Real.exp x * (1 - x)) (Set.Ici 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici 0)
    · exact (Real.continuous_exp.mul (continuous_const.sub continuous_id)).continuousOn
    · intro x hx
      rw [interior_Ici, Set.mem_Ioi] at hx
      rw [(hg_deriv x).deriv]
      have hexp_pos : 0 < Real.exp x := Real.exp_pos x
      nlinarith
  have h0 : (0 : ℝ) ∈ Set.Ici 0 := Set.mem_Ici.mpr (le_refl 0)
  have ht' : t ∈ Set.Ici 0 := Set.mem_Ici.mpr (le_of_lt ht)
  have := hg_mono h0 ht' ht
  simp at this
  linarith

/-- Key lemma: f'(t) > 0 for t > 0.
Since f'(t) = e^t(t-1) + 1 > 0 ⟺ 1 > e^t(1-t), which holds for t > 0. -/
lemma f_deriv_pos {t : ℝ} (ht : 0 < t) : 0 < deriv f t := by
  rw [f_deriv' t]
  have h : Real.exp t * (1 - t) < 1 := exp_mul_one_sub_lt_one ht
  have : Real.exp t * (t - 1) = -(Real.exp t * (1 - t)) := by ring
  linarith

/-- Key lemma: f(t) ≥ 0 for all t ≥ 0.
Proof: f(0) = 0 and f'(t) > 0 for t > 0, so f is strictly increasing. -/
lemma f_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ f t := by
  rcases eq_or_lt_of_le ht with rfl | hpos
  · simp [f_zero]
  · -- f(t) > f(0) = 0 since f is strictly increasing
    have hf_diff : Differentiable ℝ f := fun x => (f_deriv x).differentiableAt
    have h_pos_deriv : ∀ x ∈ Set.Ioo 0 t, 0 < deriv f x := fun x hx => f_deriv_pos hx.1
    have h_mono := strictMonoOn_of_deriv_pos (convex_Icc 0 t)
      (hf_diff.continuous.continuousOn) (fun x hx => by
        rw [interior_Icc] at hx
        exact h_pos_deriv x hx)
    have h0 : (0 : ℝ) ∈ Set.Icc 0 t := left_mem_Icc.mpr (le_of_lt hpos)
    have ht' : t ∈ Set.Icc 0 t := right_mem_Icc.mpr (le_of_lt hpos)
    have := h_mono h0 ht' hpos
    rw [f_zero] at this
    exact le_of_lt this

/-- The Binet kernel K(t) is nonnegative for t > 0. -/
theorem K_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ K t := by
  rw [K_eq_alt' ht]
  have hexp : 0 < Real.exp t - 1 := exp_sub_one_pos ht
  have hdenom : 0 < 2 * t * (Real.exp t - 1) := by positivity
  apply div_nonneg _ hdenom.le
  -- The numerator is f(t) ≥ 0
  exact f_nonneg (le_of_lt ht)

/-- The normalized kernel K̃(t) is nonnegative for t ≥ 0. -/
theorem Ktilde_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Ktilde t := by
  rcases eq_or_lt_of_le ht with rfl | hpos
  · rw [Ktilde_zero]; norm_num
  · rw [Ktilde_pos hpos]
    have hK : 0 ≤ K t := K_nonneg hpos
    rw [K_pos hpos] at hK
    exact div_nonneg hK (le_of_lt hpos)

/-! ## Section 4: Upper bound -/

/-! ### Auxiliary function g for the Ktilde bound -/

/-- The auxiliary function g(t) = (t² - 6t + 12)e^t - (t² + 6t + 12).
We show g(t) ≥ 0 for t ≥ 0, which implies the bound Ktilde t ≤ 1/12. -/
noncomputable def g_aux (t : ℝ) : ℝ :=
  (t ^ 2 - 6 * t + 12) * Real.exp t - (t ^ 2 + 6 * t + 12)

/-- First derivative: g'(t) = (t² - 4t + 6)e^t - (2t + 6) -/
noncomputable def g_aux' (t : ℝ) : ℝ :=
  (t ^ 2 - 4 * t + 6) * Real.exp t - (2 * t + 6)

/-- Second derivative: g''(t) = (t² - 2t + 2)e^t - 2 -/
noncomputable def g_aux'' (t : ℝ) : ℝ :=
  (t ^ 2 - 2 * t + 2) * Real.exp t - 2

/-- Third derivative: g'''(t) = t²e^t -/
noncomputable def g_aux''' (t : ℝ) : ℝ := t ^ 2 * Real.exp t

lemma g_aux_zero : g_aux 0 = 0 := by simp [g_aux]
lemma g_aux'_zero : g_aux' 0 = 0 := by simp [g_aux']
lemma g_aux''_zero : g_aux'' 0 = 0 := by simp [g_aux'']

/-- g'''(t) = t²e^t ≥ 0 for all t ≥ 0. -/
lemma g_aux'''_nonneg {t : ℝ} (_ht : 0 ≤ t) : 0 ≤ g_aux''' t := by
  simp only [g_aux''']
  exact mul_nonneg (sq_nonneg t) (Real.exp_pos t).le

lemma g_aux'''_pos {t : ℝ} (ht : 0 < t) : 0 < g_aux''' t := by
  simp [g_aux''', sq_pos_of_ne_zero (ne_of_gt ht), Real.exp_pos]

/-! #### Derivative relations for g_aux hierarchy -/

/-- g'' has derivative g''' -/
lemma hasDerivAt_g_aux'' (t : ℝ) : HasDerivAt g_aux'' (g_aux''' t) t := by
  unfold g_aux'' g_aux'''
  -- d/dt [(t² - 2t + 2)e^t - 2] = (2t - 2)e^t + (t² - 2t + 2)e^t = t²e^t
  have h1 : HasDerivAt (fun x => x^2 - 2*x + 2) (2*t - 2) t := by
    have := (hasDerivAt_pow 2 t).sub ((hasDerivAt_id t).const_mul 2)
    convert this.add (hasDerivAt_const t 2) using 1; ring
  have h2 : HasDerivAt Real.exp (Real.exp t) t := Real.hasDerivAt_exp t
  have h3 : HasDerivAt (fun x => (x^2 - 2*x + 2) * Real.exp x)
      ((2*t - 2) * Real.exp t + (t^2 - 2*t + 2) * Real.exp t) t := h1.mul h2
  have h4 : HasDerivAt (fun x => (x^2 - 2*x + 2) * Real.exp x - 2)
      ((2*t - 2) * Real.exp t + (t^2 - 2*t + 2) * Real.exp t - 0) t :=
    h3.sub (hasDerivAt_const t 2)
  simp only [sub_zero] at h4
  convert h4 using 1
  ring

/-- g' has derivative g'' -/
lemma hasDerivAt_g_aux' (t : ℝ) : HasDerivAt g_aux' (g_aux'' t) t := by
  unfold g_aux' g_aux''
  -- d/dt [(t² - 4t + 6)e^t - (2t + 6)] = (2t - 4)e^t + (t² - 4t + 6)e^t - 2
  --                                    = (t² - 2t + 2)e^t - 2
  have h1 : HasDerivAt (fun x => x^2 - 4*x + 6) (2*t - 4) t := by
    have := (hasDerivAt_pow 2 t).sub ((hasDerivAt_id t).const_mul 4)
    convert this.add (hasDerivAt_const t 6) using 1; ring
  have h2 : HasDerivAt Real.exp (Real.exp t) t := Real.hasDerivAt_exp t
  have h3 : HasDerivAt (fun x => (x^2 - 4*x + 6) * Real.exp x)
      ((2*t - 4) * Real.exp t + (t^2 - 4*t + 6) * Real.exp t) t := h1.mul h2
  have h4 : HasDerivAt (fun x => 2*x + 6) 2 t := by
    convert (hasDerivAt_id t).const_mul 2 |>.add (hasDerivAt_const t 6) using 1
    ring
  have h5 : HasDerivAt (fun x => (x^2 - 4*x + 6) * Real.exp x - (2*x + 6))
      ((2*t - 4) * Real.exp t + (t^2 - 4*t + 6) * Real.exp t - 2) t := h3.sub h4
  convert h5 using 1
  ring

/-- g has derivative g' -/
lemma hasDerivAt_g_aux (t : ℝ) : HasDerivAt g_aux (g_aux' t) t := by
  unfold g_aux g_aux'
  -- d/dt [(t² - 6t + 12)e^t - (t² + 6t + 12)]
  --   = (2t - 6)e^t + (t² - 6t + 12)e^t - (2t + 6)
  --   = (t² - 4t + 6)e^t - (2t + 6)
  have h1 : HasDerivAt (fun x => x^2 - 6*x + 12) (2*t - 6) t := by
    have := (hasDerivAt_pow 2 t).sub ((hasDerivAt_id t).const_mul 6)
    convert this.add (hasDerivAt_const t 12) using 1; ring
  have h2 : HasDerivAt Real.exp (Real.exp t) t := Real.hasDerivAt_exp t
  have h3 : HasDerivAt (fun x => (x^2 - 6*x + 12) * Real.exp x)
      ((2*t - 6) * Real.exp t + (t^2 - 6*t + 12) * Real.exp t) t := h1.mul h2
  have h4 : HasDerivAt (fun x => x^2 + 6*x + 12) (2*t + 6) t := by
    have := (hasDerivAt_pow 2 t).add ((hasDerivAt_id t).const_mul 6)
    convert this.add (hasDerivAt_const t 12) using 1; ring
  have h5 : HasDerivAt (fun x => (x^2 - 6*x + 12) * Real.exp x - (x^2 + 6*x + 12))
      ((2*t - 6) * Real.exp t + (t^2 - 6*t + 12) * Real.exp t - (2*t + 6)) t := h3.sub h4
  convert h5 using 1
  ring

/-! #### Non-negativity proofs for g_aux hierarchy -/

/-- g'' is differentiable on [0, ∞) -/
lemma differentiableOn_g_aux'' : DifferentiableOn ℝ g_aux'' (Set.Ici 0) := fun x _ =>
  (hasDerivAt_g_aux'' x).differentiableAt.differentiableWithinAt

/-- g' is differentiable on [0, ∞) -/
lemma differentiableOn_g_aux' : DifferentiableOn ℝ g_aux' (Set.Ici 0) := fun x _ =>
  (hasDerivAt_g_aux' x).differentiableAt.differentiableWithinAt

/-- g is differentiable on [0, ∞) -/
lemma differentiableOn_g_aux : DifferentiableOn ℝ g_aux (Set.Ici 0) := fun x _ =>
  (hasDerivAt_g_aux x).differentiableAt.differentiableWithinAt

/-- g''(t) ≥ 0 for t ≥ 0. Follows from g''(0) = 0 and g''' ≥ 0. -/
lemma g_aux''_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ g_aux'' t := by
  apply nonneg_of_deriv_nonneg_Ici differentiableOn_g_aux''
  · intro x hx
    rw [(hasDerivAt_g_aux'' x).deriv]
    exact g_aux'''_nonneg hx
  · exact g_aux''_zero
  · exact ht

lemma g_aux''_pos {t : ℝ} (ht : 0 < t) : 0 < g_aux'' t := by
  have hdiff : Differentiable ℝ g_aux'' := fun x => (hasDerivAt_g_aux'' x).differentiableAt
  have h_pos_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) t, 0 < deriv g_aux'' x := fun x hx => by
    -- `deriv g_aux'' x = g_aux''' x`
    simpa [(hasDerivAt_g_aux'' x).deriv] using g_aux'''_pos (t := x) hx.1
  have h_mono :=
    strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) t)
      (hdiff.continuous.continuousOn) (fun x hx => by
        rw [interior_Icc] at hx
        exact h_pos_deriv x hx)
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, le_of_lt ht⟩
  have ht' : t ∈ Set.Icc (0 : ℝ) t := ⟨le_of_lt ht, le_rfl⟩
  have := h_mono h0 ht' ht
  simpa [g_aux''_zero] using this

/-- g'(t) ≥ 0 for t ≥ 0. Follows from g'(0) = 0 and g'' ≥ 0. -/
lemma g_aux'_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ g_aux' t := by
  apply nonneg_of_deriv_nonneg_Ici differentiableOn_g_aux'
  · intro x hx
    rw [(hasDerivAt_g_aux' x).deriv]
    exact g_aux''_nonneg hx
  · exact g_aux'_zero
  · exact ht

lemma g_aux'_pos {t : ℝ} (ht : 0 < t) : 0 < g_aux' t := by
  have hdiff : Differentiable ℝ g_aux' := fun x => (hasDerivAt_g_aux' x).differentiableAt
  have h_pos_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) t, 0 < deriv g_aux' x := fun x hx => by
    simpa [(hasDerivAt_g_aux' x).deriv] using g_aux''_pos (t := x) hx.1
  have h_mono :=
    strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) t)
      (hdiff.continuous.continuousOn) (fun x hx => by
        rw [interior_Icc] at hx
        exact h_pos_deriv x hx)
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, le_of_lt ht⟩
  have ht' : t ∈ Set.Icc (0 : ℝ) t := ⟨le_of_lt ht, le_rfl⟩
  have := h_mono h0 ht' ht
  simpa [g_aux'_zero] using this

/-- g(t) ≥ 0 for t ≥ 0. This is the key inequality for proving Ktilde t ≤ 1/12.
Follows from g(0) = 0 and g' ≥ 0. -/
lemma g_aux_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ g_aux t := by
  apply nonneg_of_deriv_nonneg_Ici differentiableOn_g_aux
  · intro x hx
    rw [(hasDerivAt_g_aux x).deriv]
    exact g_aux'_nonneg hx
  · exact g_aux_zero
  · exact ht

lemma g_aux_pos {t : ℝ} (ht : 0 < t) : 0 < g_aux t := by
  have hdiff : Differentiable ℝ g_aux := fun x => (hasDerivAt_g_aux x).differentiableAt
  have h_pos_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) t, 0 < deriv g_aux x := fun x hx => by
    simpa [(hasDerivAt_g_aux x).deriv] using g_aux'_pos (t := x) hx.1
  have h_mono :=
    strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) t)
      (hdiff.continuous.continuousOn) (fun x hx => by
        rw [interior_Icc] at hx
        exact h_pos_deriv x hx)
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, le_of_lt ht⟩
  have ht' : t ∈ Set.Icc (0 : ℝ) t := ⟨le_of_lt ht, le_rfl⟩
  have := h_mono h0 ht' ht
  simpa [g_aux_zero] using this

/-- The Taylor expansion shows K(t) = t/12 - t³/720 + O(t⁵), so K(t)/t → 1/12 as t → 0⁺.
Since K(t) < t/12 for t > 0 (the higher order terms are negative), we have K(t)/t < 1/12.

The proof uses the algebraic identity K(t) = f(t)/(2t(e^t-1)) and bounds on f. -/
theorem Ktilde_le {t : ℝ} (ht : 0 ≤ t) : Ktilde t ≤ 1/12 := by
  rcases eq_or_lt_of_le ht with rfl | hpos
  · -- t = 0: Ktilde 0 = 1/12 by definition
    rw [Ktilde_zero]
  · -- t > 0: Use K(t) = f(t)/(2t(e^t-1)) where f(t) = e^t(t-2) + t + 2
    have hexp : 0 < Real.exp t - 1 := exp_sub_one_pos hpos
    have hdenom : 0 < 2 * t * (Real.exp t - 1) := by positivity
    have hf_nonneg : 0 ≤ f t := f_nonneg (le_of_lt hpos)
    -- Ktilde t = K t / t = f(t) / (2t²(e^t-1))
    calc Ktilde t = (1 / (Real.exp t - 1) - 1 / t + 1 / 2) / t := Ktilde_pos hpos
      _ = (Real.exp t * (t - 2) + t + 2) / (2 * t * (Real.exp t - 1)) / t := by
          rw [← K_pos hpos, K_eq_alt' hpos]
      _ = f t / (2 * t ^ 2 * (Real.exp t - 1)) := by
          unfold f
          field_simp
      _ ≤ 1 / 12 := by
          rw [div_le_div_iff₀
            (by positivity : (0 : ℝ) < 2 * t ^ 2 * (Real.exp t - 1))
            (by norm_num : (0 : ℝ) < 12)]
          have h_nonneg : 0 ≤ g_aux t := g_aux_nonneg (le_of_lt hpos)
          have hgoal : 0 ≤ 2 * g_aux t := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) h_nonneg
          unfold g_aux at hgoal
          unfold f
          linarith [hgoal, Real.exp_pos t, sq_nonneg t]

theorem Ktilde_lt {t : ℝ} (ht : 0 < t) : Ktilde t < 1 / 12 := by
  have hexp : 0 < Real.exp t - 1 := exp_sub_one_pos ht
  calc
    Ktilde t
        = f t / (2 * t ^ 2 * (Real.exp t - 1)) := by
            have hdenom : 0 < 2 * t * (Real.exp t - 1) := by positivity
            calc
              Ktilde t = (1 / (Real.exp t - 1) - 1 / t + 1 / 2) / t := Ktilde_pos ht
              _ = (Real.exp t * (t - 2) + t + 2) / (2 * t * (Real.exp t - 1)) / t := by
                    rw [← K_pos ht, K_eq_alt' ht]
              _ = f t / (2 * t ^ 2 * (Real.exp t - 1)) := by
                    unfold f
                    field_simp
    _ < 1 / 12 := by
          have hdenom : (0 : ℝ) < 2 * t ^ 2 * (Real.exp t - 1) := by positivity
          have h12 : (0 : ℝ) < (12 : ℝ) := by norm_num
          rw [div_lt_div_iff₀ hdenom h12]
          have hpos_g : 0 < g_aux t := g_aux_pos ht
          have hpos : 0 < 2 * g_aux t := mul_pos (by norm_num) hpos_g
          unfold g_aux at hpos
          unfold f
          linarith [hpos, Real.exp_pos t, sq_nonneg t]

/-! ## Section 4b: Robbins-type lower bound for `Ktilde` -/

/-!
Robbins' sharpened factorial lower bound is equivalent (via Binet's integral) to a pointwise
lower bound on the Binet kernel:

`(1/12) * exp(-t/12) ≤ Ktilde t` for all `t > 0`.

We prove this by reducing it to positivity of an explicit auxiliary function and then using a
derivative-chain argument (similar to the proof of `Ktilde_le`).
-/

noncomputable def robbinsAux (t : ℝ) : ℝ :=
  12 * Real.exp (t * (13 / 12 : ℝ)) * (t - 2)
    + 12 * Real.exp (t * (1 / 12 : ℝ)) * (t + 2)
    - 2 * t ^ 2 * Real.exp t + 2 * t ^ 2

noncomputable def robbinsAux' (t : ℝ) : ℝ :=
  Real.exp (t * (13 / 12 : ℝ)) * (13 * t - 14)
    + Real.exp (t * (1 / 12 : ℝ)) * (t + 14)
    - 2 * Real.exp t * (t * (t + 2)) + 4 * t

noncomputable def robbinsAux'' (t : ℝ) : ℝ :=
  Real.exp (t * (13 / 12 : ℝ)) * ((169 * t - 26) / 12)
    + Real.exp (t * (1 / 12 : ℝ)) * ((t + 26) / 12)
    - 2 * Real.exp t * (t ^ 2 + 4 * t + 2) + 4

noncomputable def robbinsAux''' (t : ℝ) : ℝ :=
  Real.exp (t * (13 / 12 : ℝ)) * ((2197 * t + 1690) / 144)
    + Real.exp (t * (1 / 12 : ℝ)) * ((t + 38) / 144)
    - 2 * Real.exp t * (t ^ 2 + 6 * t + 6)

noncomputable def robbinsAux'''' (t : ℝ) : ℝ :=
  Real.exp (t * (13 / 12 : ℝ)) * ((28561 * t + 48334) / 1728)
    + Real.exp (t * (1 / 12 : ℝ)) * ((t + 50) / 1728)
    - 2 * Real.exp t * (t ^ 2 + 8 * t + 12)

lemma robbinsAux_zero : robbinsAux 0 = 0 := by
  simp [robbinsAux]

lemma robbinsAux'_zero : robbinsAux' 0 = 0 := by
  simp [robbinsAux']

lemma robbinsAux''_zero : robbinsAux'' 0 = 0 := by
  simp [robbinsAux'']
  norm_num

lemma robbinsAux'''_zero : robbinsAux''' 0 = 0 := by
  simp [robbinsAux''']
  norm_num

lemma hasDerivAt_robbinsAux (t : ℝ) : HasDerivAt robbinsAux (robbinsAux' t) t := by
  -- Differentiate term-by-term; using the fact `d/dt (exp (t*c)) = exp (t*c) * c`.
  have hexp13 : HasDerivAt (fun x : ℝ => Real.exp (x * (13 / 12 : ℝ)))
      (Real.exp (t * (13 / 12 : ℝ)) * (13 / 12 : ℝ)) t := by
    have hlin : HasDerivAt (fun x : ℝ => x * (13 / 12 : ℝ)) (13 / 12 : ℝ) t := by
      simpa using (hasDerivAt_id t).mul_const (13 / 12 : ℝ)
    simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_exp (t * (13 / 12 : ℝ))).comp t hlin
  have hexp1 : HasDerivAt (fun x : ℝ => Real.exp (x * (1 / 12 : ℝ)))
      (Real.exp (t * (1 / 12 : ℝ)) * (1 / 12 : ℝ)) t := by
    have hlin : HasDerivAt (fun x : ℝ => x * (1 / 12 : ℝ)) (1 / 12 : ℝ) t := by
      simpa using (hasDerivAt_id t).mul_const (1 / 12 : ℝ)
    simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_exp (t * (1 / 12 : ℝ))).comp t hlin
  have hA :
      HasDerivAt (fun x : ℝ => 12 * Real.exp (x * (13 / 12 : ℝ)) * (x - 2))
        (Real.exp (t * (13 / 12 : ℝ)) * (13 * t - 14)) t := by
    have hpoly : HasDerivAt (fun x : ℝ => x - 2) 1 t := (hasDerivAt_id t).sub_const 2
    have hmul :
        HasDerivAt (fun x : ℝ => Real.exp (x * (13 / 12 : ℝ)) * (x - 2))
          (Real.exp (t * (13 / 12 : ℝ)) * (13 / 12 : ℝ) * (t - 2) +
            Real.exp (t * (13 / 12 : ℝ)) * 1) t :=
      (hexp13.mul hpoly)
    have h := hmul.const_mul (12 : ℝ)
    convert h using 1 <;> ring_nf
  have hB :
      HasDerivAt (fun x : ℝ => 12 * Real.exp (x * (1 / 12 : ℝ)) * (x + 2))
        (Real.exp (t * (1 / 12 : ℝ)) * (t + 14)) t := by
    have hpoly : HasDerivAt (fun x : ℝ => x + 2) 1 t := (hasDerivAt_id t).add_const 2
    have hmul :
        HasDerivAt (fun x : ℝ => Real.exp (x * (1 / 12 : ℝ)) * (x + 2))
          (Real.exp (t * (1 / 12 : ℝ)) * (1 / 12 : ℝ) * (t + 2) +
            Real.exp (t * (1 / 12 : ℝ)) * 1) t :=
      (hexp1.mul hpoly)
    have h := hmul.const_mul (12 : ℝ)
    convert h using 1 <;> ring_nf
  have hC :
      HasDerivAt (fun x : ℝ => -2 * x ^ 2 * Real.exp x)
        (-2 * (Real.exp t * (t * (t + 2)))) t := by
    have hpow : HasDerivAt (fun x : ℝ => x ^ 2) ((2 : ℝ) * t) t := by
      simpa using (hasDerivAt_pow 2 t)
    have hexp : HasDerivAt Real.exp (Real.exp t) t := Real.hasDerivAt_exp t
    have hmul : HasDerivAt (fun x : ℝ => x ^ 2 * Real.exp x)
        ((2 : ℝ) * t * Real.exp t + t ^ 2 * Real.exp t) t := hpow.mul hexp
    have h := hmul.const_mul (-2 : ℝ)
    convert h using 1 <;> ring_nf
  have hD :
      HasDerivAt (fun x : ℝ => 2 * x ^ 2) (4 * t) t := by
    have hpow : HasDerivAt (fun x : ℝ => x ^ 2) ((2 : ℝ) * t) t := by
      simpa using (hasDerivAt_pow 2 t)
    have h := hpow.const_mul (2 : ℝ)
    convert h using 1; ring_nf
  have h := ((hA.add hB).add (hC.add hD))
  unfold robbinsAux robbinsAux'
  convert h using 1
  · funext x
    simp [Pi.add_apply, sub_eq_add_neg, add_assoc, add_comm, mul_assoc, mul_comm]
  · ring_nf

lemma hasDerivAt_robbinsAux' (t : ℝ) : HasDerivAt robbinsAux' (robbinsAux'' t) t := by
  have hexp13 : HasDerivAt (fun x : ℝ => Real.exp (x * (13 / 12 : ℝ)))
      (Real.exp (t * (13 / 12 : ℝ)) * (13 / 12 : ℝ)) t := by
    have hlin : HasDerivAt (fun x : ℝ => x * (13 / 12 : ℝ)) (13 / 12 : ℝ) t := by
      simpa using (hasDerivAt_id t).mul_const (13 / 12 : ℝ)
    simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_exp (t * (13 / 12 : ℝ))).comp t hlin
  have hexp1 : HasDerivAt (fun x : ℝ => Real.exp (x * (1 / 12 : ℝ)))
      (Real.exp (t * (1 / 12 : ℝ)) * (1 / 12 : ℝ)) t := by
    have hlin : HasDerivAt (fun x : ℝ => x * (1 / 12 : ℝ)) (1 / 12 : ℝ) t := by
      simpa using (hasDerivAt_id t).mul_const (1 / 12 : ℝ)
    simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_exp (t * (1 / 12 : ℝ))).comp t hlin
  have hA :
      HasDerivAt (fun x : ℝ => Real.exp (x * (13 / 12 : ℝ)) * (13 * x - 14))
        (Real.exp (t * (13 / 12 : ℝ)) * ((169 * t - 26) / 12)) t := by
    have hpoly : HasDerivAt (fun x : ℝ => 13 * x - 14) 13 t := by
      simpa [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using
        ((hasDerivAt_id t).const_mul (13 : ℝ)).sub_const 14
    have hmul := hexp13.mul hpoly
    convert hmul using 1; ring_nf
  have hB :
      HasDerivAt (fun x : ℝ => Real.exp (x * (1 / 12 : ℝ)) * (x + 14))
        (Real.exp (t * (1 / 12 : ℝ)) * ((t + 26) / 12)) t := by
    have hpoly : HasDerivAt (fun x : ℝ => x + 14) 1 t := (hasDerivAt_id t).add_const 14
    have hmul := hexp1.mul hpoly
    convert hmul using 1; ring_nf
  have hC :
      HasDerivAt (fun x : ℝ => -2 * Real.exp x * (x * (x + 2)))
        (-2 * Real.exp t * (t ^ 2 + 4 * t + 2)) t := by
    have hexp : HasDerivAt Real.exp (Real.exp t) t := Real.hasDerivAt_exp t
    have hpoly : HasDerivAt (fun x : ℝ => x * (x + 2)) (t + (t + 2)) t := by
      have h1 : HasDerivAt (fun x : ℝ => x) 1 t := hasDerivAt_id t
      have h2 : HasDerivAt (fun x : ℝ => x + 2) 1 t := (hasDerivAt_id t).add_const 2
      have := h1.mul h2
      simpa [mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using this
    have hmul := hexp.mul hpoly
    have h := hmul.const_mul (-2 : ℝ)
    convert h using 1
    · funext x
      simp [Pi.mul_apply, mul_assoc, mul_comm, mul_left_comm]
    · ring_nf
  have hD : HasDerivAt (fun x : ℝ => 4 * x) 4 t := by
    simpa [mul_comm] using (hasDerivAt_id t).const_mul (4 : ℝ)
  have h := ((hA.add hB).add (hC.add hD))
  unfold robbinsAux' robbinsAux''
  convert h using 1
  · funext x
    simp [Pi.add_apply, sub_eq_add_neg, add_assoc, add_comm, mul_assoc, mul_comm]
  · ring_nf

lemma hasDerivAt_robbinsAux'' (t : ℝ) : HasDerivAt robbinsAux'' (robbinsAux''' t) t := by
  have hexp13 : HasDerivAt (fun x : ℝ => Real.exp (x * (13 / 12 : ℝ)))
      (Real.exp (t * (13 / 12 : ℝ)) * (13 / 12 : ℝ)) t := by
    have hlin : HasDerivAt (fun x : ℝ => x * (13 / 12 : ℝ)) (13 / 12 : ℝ) t := by
      simpa using (hasDerivAt_id t).mul_const (13 / 12 : ℝ)
    simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_exp (t * (13 / 12 : ℝ))).comp t hlin
  have hexp1 : HasDerivAt (fun x : ℝ => Real.exp (x * (1 / 12 : ℝ)))
      (Real.exp (t * (1 / 12 : ℝ)) * (1 / 12 : ℝ)) t := by
    have hlin : HasDerivAt (fun x : ℝ => x * (1 / 12 : ℝ)) (1 / 12 : ℝ) t := by
      simpa using (hasDerivAt_id t).mul_const (1 / 12 : ℝ)
    simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_exp (t * (1 / 12 : ℝ))).comp t hlin
  have hA :
      HasDerivAt (fun x : ℝ => Real.exp (x * (13 / 12 : ℝ)) * ((169 * x - 26) / 12))
        (Real.exp (t * (13 / 12 : ℝ)) * ((2197 * t + 1690) / 144)) t := by
    have hpoly : HasDerivAt (fun x : ℝ => ((169 * x - 26) / 12)) (169 / 12) t := by
      have : HasDerivAt (fun x : ℝ => (169 * x - 26)) 169 t := by
        simpa [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using
          ((hasDerivAt_id t).const_mul (169 : ℝ)).sub_const 26
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this.const_mul (1 / 12 : ℝ)
    have hmul := hexp13.mul hpoly
    convert hmul using 1; ring_nf
  have hB :
      HasDerivAt (fun x : ℝ => Real.exp (x * (1 / 12 : ℝ)) * ((x + 26) / 12))
        (Real.exp (t * (1 / 12 : ℝ)) * ((t + 38) / 144)) t := by
    have hpoly : HasDerivAt (fun x : ℝ => ((x + 26) / 12)) (1 / 12) t := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        ((hasDerivAt_id t).add_const 26).const_mul (1 / 12 : ℝ)
    have hmul := hexp1.mul hpoly
    convert hmul using 1; ring_nf
  have hC :
      HasDerivAt (fun x : ℝ => -2 * Real.exp x * (x ^ 2 + 4 * x + 2))
        (-2 * Real.exp t * (t ^ 2 + 6 * t + 6)) t := by
    have hexp : HasDerivAt Real.exp (Real.exp t) t := Real.hasDerivAt_exp t
    have hpoly : HasDerivAt (fun x : ℝ => x ^ 2 + 4 * x + 2) (2 * t + 4) t := by
      have h1 : HasDerivAt (fun x : ℝ => x ^ 2) ((2 : ℝ) * t) t := by
        simpa using (hasDerivAt_pow 2 t)
      have h2 : HasDerivAt (fun x : ℝ => 4 * x) 4 t := by
        simpa [mul_comm] using (hasDerivAt_id t).const_mul (4 : ℝ)
      have h3 : HasDerivAt (fun x : ℝ => (2 : ℝ)) 0 t := hasDerivAt_const t 2
      have := (h1.add (h2.add h3))
      simpa [add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using this
    have hmul := hexp.mul hpoly
    have h := hmul.const_mul (-2 : ℝ)
    convert h using 1
    · funext x
      simp [Pi.mul_apply, mul_comm, mul_left_comm]
    · ring_nf
  have hD : HasDerivAt (fun _x : ℝ => (4 : ℝ)) 0 t := hasDerivAt_const t 4
  have h := ((hA.add hB).add hC).add hD
  unfold robbinsAux'' robbinsAux'''
  convert h using 1
  · funext x
    simp [Pi.add_apply, sub_eq_add_neg, add_comm, mul_comm]
  · ring_nf

lemma hasDerivAt_robbinsAux''' (t : ℝ) : HasDerivAt robbinsAux''' (robbinsAux'''' t) t := by
  have hexp13 : HasDerivAt (fun x : ℝ => Real.exp (x * (13 / 12 : ℝ)))
      (Real.exp (t * (13 / 12 : ℝ)) * (13 / 12 : ℝ)) t := by
    have hlin : HasDerivAt (fun x : ℝ => x * (13 / 12 : ℝ)) (13 / 12 : ℝ) t := by
      simpa using (hasDerivAt_id t).mul_const (13 / 12 : ℝ)
    simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_exp (t * (13 / 12 : ℝ))).comp t hlin
  have hexp1 : HasDerivAt (fun x : ℝ => Real.exp (x * (1 / 12 : ℝ)))
      (Real.exp (t * (1 / 12 : ℝ)) * (1 / 12 : ℝ)) t := by
    have hlin : HasDerivAt (fun x : ℝ => x * (1 / 12 : ℝ)) (1 / 12 : ℝ) t := by
      simpa using (hasDerivAt_id t).mul_const (1 / 12 : ℝ)
    simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_exp (t * (1 / 12 : ℝ))).comp t hlin
  have hA :
      HasDerivAt (fun x : ℝ => Real.exp (x * (13 / 12 : ℝ)) * ((2197 * x + 1690) / 144))
        (Real.exp (t * (13 / 12 : ℝ)) * ((28561 * t + 48334) / 1728)) t := by
    have hpoly : HasDerivAt (fun x : ℝ => ((2197 * x + 1690) / 144)) (2197 / 144) t := by
      have : HasDerivAt (fun x : ℝ => (2197 * x + 1690)) 2197 t := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          ((hasDerivAt_id t).const_mul (2197 : ℝ)).add_const 1690
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this.const_mul (1 / 144 : ℝ)
    have hmul := hexp13.mul hpoly
    convert hmul using 1; ring_nf
  have hB :
      HasDerivAt (fun x : ℝ => Real.exp (x * (1 / 12 : ℝ)) * ((x + 38) / 144))
        (Real.exp (t * (1 / 12 : ℝ)) * ((t + 50) / 1728)) t := by
    have hpoly : HasDerivAt (fun x : ℝ => ((x + 38) / 144)) (1 / 144) t := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        ((hasDerivAt_id t).add_const 38).const_mul (1 / 144 : ℝ)
    have hmul := hexp1.mul hpoly
    convert hmul using 1; ring_nf
  have hC :
      HasDerivAt (fun x : ℝ => -2 * Real.exp x * (x ^ 2 + 6 * x + 6))
        (-2 * Real.exp t * (t ^ 2 + 8 * t + 12)) t := by
    have hexp : HasDerivAt Real.exp (Real.exp t) t := Real.hasDerivAt_exp t
    have hpoly : HasDerivAt (fun x : ℝ => x ^ 2 + 6 * x + 6) (2 * t + 6) t := by
      have h1 : HasDerivAt (fun x : ℝ => x ^ 2) ((2 : ℝ) * t) t := by
        simpa using (hasDerivAt_pow 2 t)
      have h2 : HasDerivAt (fun x : ℝ => 6 * x) 6 t := by
        simpa [mul_comm] using (hasDerivAt_id t).const_mul (6 : ℝ)
      have h3 : HasDerivAt (fun x : ℝ => (6 : ℝ)) 0 t := hasDerivAt_const t 6
      have := h1.add (h2.add h3)
      simpa [add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using this
    have hmul := hexp.mul hpoly
    have h := hmul.const_mul (-2 : ℝ)
    convert h using 1
    · funext x
      simp [Pi.mul_apply, mul_comm, mul_left_comm]
    · ring_nf
  have h := (hA.add hB).add hC
  unfold robbinsAux''' robbinsAux''''
  convert h using 1
  · funext x
    simp [Pi.add_apply, sub_eq_add_neg, add_comm, mul_comm]
  · ring_nf

lemma differentiableOn_robbinsAux :
    DifferentiableOn ℝ robbinsAux (Set.Ici 0) := fun x _ =>
  (hasDerivAt_robbinsAux x).differentiableAt.differentiableWithinAt

lemma differentiableOn_robbinsAux' :
    DifferentiableOn ℝ robbinsAux' (Set.Ici 0) := fun x _ =>
  (hasDerivAt_robbinsAux' x).differentiableAt.differentiableWithinAt

lemma differentiableOn_robbinsAux'' :
    DifferentiableOn ℝ robbinsAux'' (Set.Ici 0) := fun x _ =>
  (hasDerivAt_robbinsAux'' x).differentiableAt.differentiableWithinAt

lemma differentiableOn_robbinsAux''' :
    DifferentiableOn ℝ robbinsAux''' (Set.Ici 0) := fun x _ =>
  (hasDerivAt_robbinsAux''' x).differentiableAt.differentiableWithinAt

/-! ### Positivity of the fourth derivative -/

noncomputable def robbinsPoly (t : ℝ) : ℝ :=
  (3431 / 864 : ℝ) + (29645 / 10368 : ℝ) * t - (130765 / 248832 : ℝ) * t ^ 2 +
    (28561 / 497664 : ℝ) * t ^ 3

noncomputable def robbinsPoly' (t : ℝ) : ℝ :=
  (28561 / 165888 : ℝ) * t ^ 2 - (130765 / 124416 : ℝ) * t + (29645 / 10368 : ℝ)

lemma hasDerivAt_robbinsPoly (t : ℝ) : HasDerivAt robbinsPoly (robbinsPoly' t) t := by
  unfold robbinsPoly robbinsPoly'
  -- derivative of a cubic polynomial
  have h0 : HasDerivAt (fun _x : ℝ => (3431 / 864 : ℝ)) 0 t := hasDerivAt_const t _
  have h1 : HasDerivAt (fun x : ℝ => (29645 / 10368 : ℝ) * x) (29645 / 10368 : ℝ) t := by
    simpa [mul_comm] using (hasDerivAt_id t).const_mul (29645 / 10368 : ℝ)
  have h2 : HasDerivAt (fun x : ℝ => -(130765 / 248832 : ℝ) * x ^ 2)
      (-(130765 / 124416 : ℝ) * t) t := by
    have hpow : HasDerivAt (fun x : ℝ => x ^ 2) ((2 : ℝ) * t) t := by
      simpa using (hasDerivAt_pow 2 t)
    have h := hpow.const_mul (-(130765 / 248832 : ℝ))
    convert h using 1; ring_nf
  have h3 : HasDerivAt (fun x : ℝ => (28561 / 497664 : ℝ) * x ^ 3)
      ((28561 / 165888 : ℝ) * t ^ 2) t := by
    have hpow : HasDerivAt (fun x : ℝ => x ^ 3) ((3 : ℝ) * t ^ 2) t := by
      simpa using (hasDerivAt_pow 3 t)
    have h := hpow.const_mul (28561 / 497664 : ℝ)
    convert h using 1; ring_nf
  have h := (((h0.add h1).add h2).add h3)
  convert h using 1
  · funext x
    simp [Pi.add_apply]
    ring_nf
  · ring_nf

lemma robbinsPoly'_pos (t : ℝ) : 0 < robbinsPoly' t := by
  have hderiv : deriv robbinsPoly t = robbinsPoly' t := by
    simpa using (hasDerivAt_robbinsPoly t).deriv
  let a : ℝ := (28561 / 165888 : ℝ)
  let b : ℝ := (-(130765 / 124416 : ℝ))
  let c : ℝ := (29645 / 10368 : ℝ)
  have ha : 0 < a := by norm_num [a]
  have hD : b ^ 2 - 4 * a * c < 0 := by
    norm_num [a, b, c]
  have hquad :
      robbinsPoly' t = a * t ^ 2 + b * t + c := by
    simp [robbinsPoly', a, b, c, pow_two, mul_assoc, mul_comm, sub_eq_add_neg]
  have : 0 < a * t ^ 2 + b * t + c := by
    have ha0 : a ≠ 0 := ne_of_gt ha
    have hsq :
        a * t ^ 2 + b * t + c =
          a * (t + b / (2 * a)) ^ 2 + (4 * a * c - b ^ 2) / (4 * a) := by
      field_simp [ha0]
      ring
    have hconst_pos : 0 < (4 * a * c - b ^ 2) / (4 * a) := by
      have hn : 0 < 4 * a * c - b ^ 2 := by linarith
      have hd : 0 < 4 * a := by nlinarith [ha]
      exact div_pos hn hd
    have hsq_nonneg : 0 ≤ a * (t + b / (2 * a)) ^ 2 := by
      exact mul_nonneg (le_of_lt ha) (sq_nonneg _)
    have hsum_pos :
        0 < a * (t + b / (2 * a)) ^ 2 + (4 * a * c - b ^ 2) / (4 * a) :=
      lt_of_lt_of_le hconst_pos (le_add_of_nonneg_left hsq_nonneg)
    simpa [hsq] using hsum_pos
  simpa [hquad]

lemma robbinsPoly_pos {t : ℝ} (_ht : 0 ≤ t) : 0 < robbinsPoly t := by
  have hpos_deriv : ∀ x : ℝ, 0 < deriv robbinsPoly x := by
    intro x
    rw [(hasDerivAt_robbinsPoly x).deriv]
    exact robbinsPoly'_pos x
  have hmono : StrictMono robbinsPoly := strictMono_of_deriv_pos hpos_deriv
  have h0 : 0 < robbinsPoly 0 := by
    simp [robbinsPoly]
  have : 0 ≤ robbinsPoly 0 := le_of_lt h0
  have hle : robbinsPoly 0 ≤ robbinsPoly t := by
    exact (hmono.monotone (by simpa using _ht))
  exact lt_of_lt_of_le h0 hle

lemma robbinsAux''''_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ robbinsAux'''' t := by
  have hexp13 :
      Real.exp (t * (13 / 12 : ℝ)) = Real.exp t * Real.exp (t * (1 / 12 : ℝ)) := by
    have : t * (13 / 12 : ℝ) = t + t * (1 / 12 : ℝ) := by ring
    calc
      Real.exp (t * (13 / 12 : ℝ)) =
          Real.exp (t + t * (1 / 12 : ℝ)) := by
        simp [this]
      _ = Real.exp t * Real.exp (t * (1 / 12 : ℝ)) := by simp [Real.exp_add]
  have hpi : 0 ≤ Real.exp (t * (1 / 12 : ℝ)) := (Real.exp_pos _).le
  have htlin : 0 ≤ (28561 * t + 48334) / 1728 := by
    have : (0 : ℝ) ≤ 28561 * t + 48334 := by nlinarith [ht]
    nlinarith
  have hExpLower :
      robbinsPoly t ≤
        Real.exp (t * (1 / 12 : ℝ)) * ((28561 * t + 48334) / 1728) -
          2 * (t ^ 2 + 8 * t + 12) := by
    have hu : 0 ≤ t * (1 / 12 : ℝ) := by nlinarith [ht]
    have hexp_lb :
        1 + (t * (1 / 12 : ℝ)) + (t * (1 / 12 : ℝ)) ^ 2 / 2 ≤
          Real.exp (t * (1 / 12 : ℝ)) :=
      exp_ge_one_add_sq hu
    have hmul :
        (1 + (t * (1 / 12 : ℝ)) + (t * (1 / 12 : ℝ)) ^ 2 / 2) *
          ((28561 * t + 48334) / 1728)
          ≤ Real.exp (t * (1 / 12 : ℝ)) * ((28561 * t + 48334) / 1728) :=
      mul_le_mul_of_nonneg_right hexp_lb htlin
    have hsub :
        (1 + (t * (1 / 12 : ℝ)) + (t * (1 / 12 : ℝ)) ^ 2 / 2) *
          ((28561 * t + 48334) / 1728)
            - 2 * (t ^ 2 + 8 * t + 12)
          ≤ Real.exp (t * (1 / 12 : ℝ)) * ((28561 * t + 48334) / 1728) -
            2 * (t ^ 2 + 8 * t + 12) :=
      sub_le_sub_right hmul _
    have :
        (1 + (t * (1 / 12 : ℝ)) + (t * (1 / 12 : ℝ)) ^ 2 / 2) *
          ((28561 * t + 48334) / 1728)
          - 2 * (t ^ 2 + 8 * t + 12) = robbinsPoly t := by
      unfold robbinsPoly
      ring
    grind
  have hpoly_pos : 0 < robbinsPoly t := robbinsPoly_pos (t := t) ht
  have hbracket :
      0 ≤ Real.exp (t * (1 / 12 : ℝ)) * ((28561 * t + 48334) / 1728) -
        2 * (t ^ 2 + 8 * t + 12) :=
    le_of_lt (lt_of_lt_of_le hpoly_pos hExpLower)
  have hterm2 : 0 ≤ Real.exp (t * (1 / 12 : ℝ)) * ((t + 50) / 1728) := by
    have : 0 ≤ (t + 50) / 1728 := by nlinarith [ht]
    exact mul_nonneg (Real.exp_pos _).le this
  have : robbinsAux'''' t =
      Real.exp t *
        (Real.exp (t * (1 / 12 : ℝ)) * ((28561 * t + 48334) / 1728) -
          2 * (t ^ 2 + 8 * t + 12))
        + Real.exp (t * (1 / 12 : ℝ)) * ((t + 50) / 1728) := by
    unfold robbinsAux''''
    simp [hexp13, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg]
    ring
  rw [this]
  exact add_nonneg (mul_nonneg (Real.exp_pos _).le hbracket) hterm2

lemma robbinsAux'''_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ robbinsAux''' t := by
  apply nonneg_of_deriv_nonneg_Ici differentiableOn_robbinsAux'''
  · intro x hx
    rw [(hasDerivAt_robbinsAux''' x).deriv]
    exact robbinsAux''''_nonneg (t := x) hx
  · exact robbinsAux'''_zero
  · exact ht

lemma robbinsAux''_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ robbinsAux'' t := by
  apply nonneg_of_deriv_nonneg_Ici differentiableOn_robbinsAux''
  · intro x hx
    rw [(hasDerivAt_robbinsAux'' x).deriv]
    exact robbinsAux'''_nonneg (t := x) hx
  · exact robbinsAux''_zero
  · exact ht

lemma robbinsAux'_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ robbinsAux' t := by
  apply nonneg_of_deriv_nonneg_Ici differentiableOn_robbinsAux'
  · intro x hx
    rw [(hasDerivAt_robbinsAux' x).deriv]
    exact robbinsAux''_nonneg (t := x) hx
  · exact robbinsAux'_zero
  · exact ht

lemma robbinsAux_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ robbinsAux t := by
  apply nonneg_of_deriv_nonneg_Ici differentiableOn_robbinsAux
  · intro x hx
    rw [(hasDerivAt_robbinsAux x).deriv]
    exact robbinsAux'_nonneg (t := x) hx
  · exact robbinsAux_zero
  · exact ht

theorem Ktilde_ge_one_div_twelve_mul_exp_neg_div_twelve {t : ℝ} (ht : 0 < t) :
    (1 / 12 : ℝ) * Real.exp (-t / 12) ≤ Ktilde t := by
  have ht0 : 0 ≤ t := le_of_lt ht
  have hexp : 0 < Real.exp t - 1 := exp_sub_one_pos ht
  have hK : Ktilde t = f t / (2 * t ^ 2 * (Real.exp t - 1)) := by
    calc
      Ktilde t = (1 / (Real.exp t - 1) - 1 / t + 1 / 2) / t := Ktilde_pos ht
      _ = (Real.exp t * (t - 2) + t + 2) / (2 * t * (Real.exp t - 1)) / t := by
            rw [← K_pos ht, K_eq_alt' ht]
      _ = f t / (2 * t ^ 2 * (Real.exp t - 1)) := by
            unfold f
            field_simp
  rw [hK]
  have hdenom : 0 < (2 * t ^ 2 * (Real.exp t - 1)) := by positivity
  have hmain :
      2 * t ^ 2 * (Real.exp t - 1) ≤ 12 * Real.exp (t * (1 / 12 : ℝ)) * f t := by
    have h0 : 0 ≤ robbinsAux t := robbinsAux_nonneg (t := t) ht0
    have hrobbins :
        robbinsAux t = 12 * Real.exp (t * (1 / 12 : ℝ)) * f t - 2 * t ^ 2 * (Real.exp t - 1) := by
      unfold robbinsAux f
      have : t * (13 / 12 : ℝ) = t + t * (1 / 12 : ℝ) := by ring
      simp [this, Real.exp_add, mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg]
      ring
    have : 2 * t ^ 2 * (Real.exp t - 1) ≤ 12 * Real.exp (t * (1 / 12 : ℝ)) * f t := by
      have : 0 ≤ 12 * Real.exp (t * (1 / 12 : ℝ)) * f t - 2 * t ^ 2 * (Real.exp t - 1) := by
        simpa [hrobbins] using h0
      exact sub_nonneg.1 this
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have : (1 / 12 : ℝ) * Real.exp (-t / 12) ≤ f t / (2 * t ^ 2 * (Real.exp t - 1)) := by
    have : ((1 / 12 : ℝ) * Real.exp (-t / 12)) * (2 * t ^ 2 * (Real.exp t - 1)) ≤ f t := by
      have hexp' : Real.exp (-t / 12) = (Real.exp (t * (1 / 12 : ℝ)))⁻¹ := by
        have : (-t / 12 : ℝ) = -(t * (1 / 12 : ℝ)) := by ring
        simp [this, Real.exp_neg]
      have hmain' :
          ((1 / 12 : ℝ) * Real.exp (-t / 12)) * (2 * t ^ 2 * (Real.exp t - 1))
            ≤ ((1 / 12 : ℝ) * Real.exp (-t / 12)) *
              (12 * Real.exp (t * (1 / 12 : ℝ)) * f t) := by
        exact mul_le_mul_of_nonneg_left hmain (by positivity)
      calc
        ((1 / 12 : ℝ) * Real.exp (-t / 12)) * (2 * t ^ 2 * (Real.exp t - 1))
            ≤ ((1 / 12 : ℝ) * Real.exp (-t / 12)) *
              (12 * Real.exp (t * (1 / 12 : ℝ)) * f t) := hmain'
        _ = f t := by
            have hExp : Real.exp (-t / 12) * Real.exp (t * (1 / 12 : ℝ)) = 1 := by
              have : (-t / 12 : ℝ) + (t * (1 / 12 : ℝ)) = 0 := by ring
              have := congrArg Real.exp this
              simpa [Real.exp_add, Real.exp_zero] using this
            calc
              ((1 / 12 : ℝ) * Real.exp (-t / 12)) *
                  (12 * Real.exp (t * (1 / 12 : ℝ)) * f t)
                  = ((1 / 12 : ℝ) * 12) *
                    (Real.exp (-t / 12) * Real.exp (t * (1 / 12 : ℝ))) * f t := by
                      ring
              _ = (Real.exp (-t / 12) * Real.exp (t * (1 / 12 : ℝ))) * f t := by
                      simp [mul_assoc]
              _ = f t := by
                      simpa [mul_assoc] using congrArg (fun z => z * f t) hExp
    have :
        (1 / 12 : ℝ) * Real.exp (-t / 12) ≤
          f t / (2 * t ^ 2 * (Real.exp t - 1)) := by
      exact (le_div_iff₀ hdenom).2 this
    exact this
  exact this

end BinetKernel
