/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.BinetRealIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.BinetIntegral

/-!
# Real bounds for the Binet correction integral

Sharp two-sided estimates on `(J x).re` for `x > 0`, used in Robbins' Stirling bounds.
-/

open Real Complex Set MeasureTheory Filter Topology BinetKernel
open scoped BigOperators

@[expose] public section

noncomputable section

namespace Binet

open scoped BigOperators

/-- **Positivity of the Binet integral (real part).**

For `x > 0`, the Binet correction term satisfies `(Binet.J x).re > 0`. -/
theorem re_J_pos {x : ℝ} (hx : 0 < x) : 0 < (J (x : ℂ)).re := by
  have hJ : (J (x : ℂ)).re =
      ∫ t in Set.Ioi (0 : ℝ), BinetKernel.Ktilde t * Real.exp (-t * x) :=
    re_J_eq_integral_Ktilde (x := x) hx
  have hpos_event :
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), (1 / 24 : ℝ) < BinetKernel.Ktilde t := by
    have h :=
      (BinetKernel.tendsto_Ktilde_zero :
        Tendsto BinetKernel.Ktilde (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (1 / 12 : ℝ)))
    have hmem : Set.Ioi (1 / 24 : ℝ) ∈ nhds (1 / 12 : ℝ) := by
      have : (1 / 24 : ℝ) < (1 / 12 : ℝ) := by norm_num
      exact Ioi_mem_nhds this
    exact h.eventually hmem
  have hmem :
      {t : ℝ | (1 / 24 : ℝ) < BinetKernel.Ktilde t} ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    simpa [Filter.Eventually] using hpos_event
  rcases (mem_nhdsWithin).1 hmem with ⟨u, hu_open, hu0, hu_sub⟩
  rcases (Metric.mem_nhds_iff).1 (IsOpen.mem_nhds hu_open hu0) with ⟨ε, hεpos, hball⟩
  set δ : ℝ := ε / 2
  have hδpos : 0 < δ := by exact half_pos hεpos
  have hK_lower : ∀ t ∈ Set.Ioc (0 : ℝ) δ, (1 / 24 : ℝ) ≤ BinetKernel.Ktilde t := by
    intro t ht
    have ht_pos : t ∈ Set.Ioi (0 : ℝ) := ht.1
    have ht_u : t ∈ u := by
      have ht_ball : t ∈ Metric.ball (0 : ℝ) ε := by
        have ht_lt : t < ε := lt_of_le_of_lt ht.2 (half_lt_self hεpos)
        have ht_abs : |t| < ε := by simpa [abs_of_pos ht.1] using ht_lt
        simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs, sub_zero] using ht_abs
      exact hball ht_ball
    have : t ∈ {t : ℝ | (1 / 24 : ℝ) < BinetKernel.Ktilde t} := hu_sub ⟨ht_u, ht_pos⟩
    exact le_of_lt (by simpa using this)
  have hExp_lower : ∀ t ∈ Set.Ioc (0 : ℝ) δ, Real.exp (-δ * x) ≤ Real.exp (-t * x) := by
    intro t ht
    have hx0 : 0 ≤ x := le_of_lt hx
    have ht_le : t ≤ δ := ht.2
    have hmul : -δ * x ≤ -t * x := by
      nlinarith [ht_le, hx0]
    exact Real.exp_le_exp.mpr hmul
  have hconst_le :
      ∀ t ∈ Set.Ioc (0 : ℝ) δ,
        (1 / 24 : ℝ) * Real.exp (-δ * x) ≤ BinetKernel.Ktilde t * Real.exp (-t * x) := by
    intro t ht
    have h1 : (1 / 24 : ℝ) ≤ BinetKernel.Ktilde t := hK_lower t ht
    have h2 : Real.exp (-δ * x) ≤ Real.exp (-t * x) := hExp_lower t ht
    have h24 : 0 ≤ (1 / 24 : ℝ) := by norm_num
    have hK0 : 0 ≤ BinetKernel.Ktilde t := le_trans h24 h1
    have hE0 : 0 ≤ Real.exp (-t * x) := Real.exp_nonneg _
    calc
      (1 / 24 : ℝ) * Real.exp (-δ * x)
          ≤ (BinetKernel.Ktilde t) * Real.exp (-δ * x) := by
              exact mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
      _ ≤ (BinetKernel.Ktilde t) * Real.exp (-t * x) := by
              exact mul_le_mul_of_nonneg_left h2 hK0
  have hInt_on :
      IntegrableOn
        (fun t : ℝ => BinetKernel.Ktilde t * Real.exp (-t * x)) (Set.Ioi 0) volume :=
    (integrable_Ktilde_mul_exp_real (x := x) hx)
  have hInt_Ioc :
      IntegrableOn
        (fun t : ℝ => BinetKernel.Ktilde t * Real.exp (-t * x)) (Set.Ioc 0 δ) volume :=
    hInt_on.mono_set (Set.Ioc_subset_Ioi_self)
  have hμ_Ioc : (volume (Set.Ioc (0 : ℝ) δ)) ≠ (⊤ : ENNReal) := by
    simp [Real.volume_Ioc]
  have hlower_int :
      (1 / 24 : ℝ) * Real.exp (-δ * x) * (volume.real (Set.Ioc (0 : ℝ) δ))
        ≤ ∫ t in Set.Ioc (0 : ℝ) δ, BinetKernel.Ktilde t * Real.exp (-t * x) := by
    have : ((1 / 24 : ℝ) * Real.exp (-δ * x)) * volume.real (Set.Ioc (0 : ℝ) δ)
        ≤ ∫ t in Set.Ioc (0 : ℝ) δ, BinetKernel.Ktilde t * Real.exp (-t * x) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (MeasureTheory.setIntegral_ge_of_const_le_real (μ := volume)
          (s := Set.Ioc (0 : ℝ) δ) (f := fun t : ℝ => BinetKernel.Ktilde t * Real.exp (-t * x))
          (c := (1 / 24 : ℝ) * Real.exp (-δ * x)) (hs := measurableSet_Ioc)
          (hμs := hμ_Ioc) (hf := hconst_le) (hfint := hInt_Ioc))
    simpa [mul_assoc] using this
  have hIoc_le :
      ∫ t in Set.Ioc (0 : ℝ) δ, BinetKernel.Ktilde t * Real.exp (-t * x)
        ≤ ∫ t in Set.Ioi (0 : ℝ), BinetKernel.Ktilde t * Real.exp (-t * x) := by
    have hf_nonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        (fun t : ℝ => BinetKernel.Ktilde t * Real.exp (-t * x)) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      have hK0 : 0 ≤ BinetKernel.Ktilde t := BinetKernel.Ktilde_nonneg (le_of_lt ht)
      exact mul_nonneg hK0 (Real.exp_nonneg _)
    have hst : (Set.Ioc (0 : ℝ) δ) ≤ᵐ[volume] (Set.Ioi (0 : ℝ)) := by
      refine ae_of_all _ ?_
      intro t ht
      exact ht.1
    exact MeasureTheory.setIntegral_mono_set (μ := volume) (hfi := hInt_on) hf_nonneg hst
  have hμpos : 0 < volume.real (Set.Ioc (0 : ℝ) δ) := by
    have hvol : volume.real (Set.Ioc (0 : ℝ) δ) = δ := by
      simpa [sub_zero] using
        (Real.volume_real_Ioc_of_le (a := (0 : ℝ)) (b := δ) (by exact le_of_lt hδpos))
    simpa [hvol] using hδpos
  have hconst_pos : 0 < (1 / 24 : ℝ) * Real.exp (-δ * x) := by
    have : (0 : ℝ) < (1 / 24 : ℝ) := by norm_num
    exact mul_pos this (Real.exp_pos _)
  have hpos :
      0 < ∫ t in Set.Ioi (0 : ℝ), BinetKernel.Ktilde t * Real.exp (-t * x) := by
    have : 0 < (1 / 24 : ℝ) * Real.exp (-δ * x) * volume.real (Set.Ioc (0 : ℝ) δ) := by
      exact mul_pos hconst_pos hμpos
    have h1 : (1 / 24 : ℝ) * Real.exp (-δ * x) * volume.real (Set.Ioc (0 : ℝ) δ)
          ≤ ∫ t in Set.Ioi (0 : ℝ), BinetKernel.Ktilde t * Real.exp (-t * x) :=
      le_trans hlower_int hIoc_le
    exact lt_of_lt_of_le this h1
  simpa [hJ] using hpos

/-- Upper bound for the real Binet integral. -/
theorem re_J_le_one_div_twelve {x : ℝ} (hx : 0 < x) :
    (J (x : ℂ)).re ≤ 1 / (12 * x) :=
  (Complex.re_le_norm _).trans (J_norm_le_real hx)

/-- Strict upper bound for the real Binet integral. -/
theorem re_J_lt_one_div_twelve {x : ℝ} (hx : 0 < x) :
    (J (x : ℂ)).re < 1 / (12 * x) := by
  have hJ : (J (x : ℂ)).re =
      ∫ t in Set.Ioi (0 : ℝ), BinetKernel.Ktilde t * Real.exp (-t * x) :=
    re_J_eq_integral_Ktilde (x := x) hx
  let f : ℝ → ℝ := fun t => BinetKernel.Ktilde t * Real.exp (-t * x)
  let g : ℝ → ℝ := fun t => (1 / 12 : ℝ) * Real.exp (-t * x)
  let h : ℝ → ℝ := fun t => g t - f t
  have hf_int : IntegrableOn f (Set.Ioi (0 : ℝ)) volume := by
    simpa [f] using (integrable_Ktilde_mul_exp_real (x := x) hx)
  have hg_int : IntegrableOn g (Set.Ioi (0 : ℝ)) volume := by
    simpa [g] using (integrable_const_mul_exp (x := x) hx)
  have hh_nonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] h := by
    have : ∀ᵐ t ∂volume, t ∈ Set.Ioi (0 : ℝ) → 0 ≤ h t := by
      refine MeasureTheory.ae_of_all _ ?_
      intro t ht
      have hK : BinetKernel.Ktilde t ≤ (1 / 12 : ℝ) := BinetKernel.Ktilde_le (le_of_lt ht)
      have hE : 0 ≤ Real.exp (-t * x) := Real.exp_nonneg _
      dsimp [h, f, g]
      refine sub_nonneg.2 ?_
      exact mul_le_mul_of_nonneg_right hK hE
    exact (MeasureTheory.ae_restrict_iff' (μ := volume) (s := Set.Ioi (0 : ℝ))
      measurableSet_Ioi).2 this
  have hh_int : IntegrableOn h (Set.Ioi (0 : ℝ)) volume := by
    simpa [h] using (hg_int.sub hf_int)
  have hμ_support : (0 : ENNReal) < volume (Function.support h ∩ Set.Ioi (0 : ℝ)) := by
    have hsub : Set.Ioc (0 : ℝ) 1 ⊆ Function.support h ∩ Set.Ioi (0 : ℝ) := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have htI : t ∈ Set.Ioi (0 : ℝ) := ht0
      have hK : BinetKernel.Ktilde t < (1 / 12 : ℝ) := BinetKernel.Ktilde_lt ht0
      have hE : 0 < Real.exp (-t * x) := Real.exp_pos _
      have : h t ≠ 0 := by
        have : 0 < h t := by
          dsimp [h, f, g]
          have hlt :
              BinetKernel.Ktilde t * Real.exp (-t * x) <
                (1 / 12 : ℝ) * Real.exp (-t * x) := by
            exact mul_lt_mul_of_pos_right hK hE
          exact sub_pos.2 hlt
        exact ne_of_gt this
      have ht_support : t ∈ Function.support h := by
        simp [Function.mem_support, this]
      exact ⟨ht_support, htI⟩
    have hvol_pos : (0 : ENNReal) < volume (Set.Ioc (0 : ℝ) 1) := by simp
    exact lt_of_lt_of_le hvol_pos (measure_mono hsub)
  have hh_pos : 0 < ∫ t in Set.Ioi (0 : ℝ), h t := by
    have := (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae (μ := volume)
      (s := Set.Ioi (0 : ℝ)) (f := h) hh_nonneg hh_int).2 hμ_support
    simpa using this
  have hsub_eq :
      (∫ t in Set.Ioi (0 : ℝ), h t) =
        (∫ t in Set.Ioi (0 : ℝ), g t) - (∫ t in Set.Ioi (0 : ℝ), f t) := by
    simpa [h, sub_eq_add_neg] using
      (MeasureTheory.integral_sub
        (μ := volume.restrict (Set.Ioi (0 : ℝ))) (hf := hg_int) (hg := hf_int))
  have hlt_fg : (∫ t in Set.Ioi (0 : ℝ), f t) < (∫ t in Set.Ioi (0 : ℝ), g t) := by
    have : 0 < (∫ t in Set.Ioi (0 : ℝ), g t) - (∫ t in Set.Ioi (0 : ℝ), f t) := by
      simpa [hsub_eq] using hh_pos
    exact (sub_pos.mp this)
  have hg_val : (∫ t in Set.Ioi (0 : ℝ), g t) = 1 / (12 * x) := by
    have hbase : ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t * x)) = 1 / x := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using (integral_exp_neg_mul_Ioi (x := x) hx)
    calc
      (∫ t in Set.Ioi (0 : ℝ), g t)
          = (1 / 12 : ℝ) * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t * x)) := by
              simp [g, MeasureTheory.integral_const_mul, mul_comm]
      _ = (1 / 12 : ℝ) * (1 / x) := by simp [hbase]
      _ = 1 / (12 * x) := by ring
  have : (J (x : ℂ)).re < 1 / (12 * x) := by
    have : (∫ t in Set.Ioi (0 : ℝ), f t) < 1 / (12 * x) := by
      have : (∫ t in Set.Ioi (0 : ℝ), f t) < (∫ t in Set.Ioi (0 : ℝ), g t) := hlt_fg
      exact lt_of_lt_of_eq this hg_val
    simpa [hJ, f] using this
  exact this

private lemma exp_neg_div_twelve_mul_exp_neg_mul (x t : ℝ) :
    Real.exp (-t / 12) * Real.exp (-t * x) = Real.exp (-t * (x + 1 / 12)) := by
  rw [← Real.exp_add]
  congr 1
  ring

private lemma integrable_robbins_lower_majorant {x : ℝ} (hx : 0 < x) :
    IntegrableOn
      (fun t : ℝ => (1 / 12 : ℝ) * Real.exp (-t / 12) * Real.exp (-t * x))
      (Set.Ioi 0) volume := by
  have hx' : 0 < x + 1 / 12 := by linarith [hx]
  have hConst := integrable_const_mul_exp (x := x + 1 / 12) hx'
  refine hConst.congr_fun ?_ measurableSet_Ioi
  intro t _ht
  calc
    (1 / 12 : ℝ) * Real.exp (-t * (x + 1 / 12))
    _ = (1 / 12 : ℝ) * (Real.exp (-t / 12) * Real.exp (-t * x)) := by
        rw [exp_neg_div_twelve_mul_exp_neg_mul]
    _ = (1 / 12 : ℝ) * Real.exp (-t / 12) * Real.exp (-t * x) := by ring

private lemma integral_robbins_lower_majorant {x : ℝ} (hx : 0 < x) :
    ∫ t in Set.Ioi 0, (1 / 12 : ℝ) * Real.exp (-t / 12) * Real.exp (-t * x) =
      (12 * x + 1)⁻¹ := by
  have hx' : 0 < x + 1 / 12 := by linarith [hx]
  have hbase :
      ∫ t in Set.Ioi 0, Real.exp (-t * (x + 1 / 12)) = (x + 1 / 12)⁻¹ := by
    simpa using integral_exp_neg_mul_Ioi (x := x + 1 / 12) hx'
  calc
    (∫ t in Set.Ioi 0, (1 / 12 : ℝ) * Real.exp (-t / 12) * Real.exp (-t * x))
        = ∫ t in Set.Ioi 0, (1 / 12 : ℝ) * Real.exp (-t * (x + 1 / 12)) := by
            refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
            intro t _ht
            calc
              (1 / 12 : ℝ) * Real.exp (-t / 12) * Real.exp (-t * x)
                  = (1 / 12 : ℝ) * (Real.exp (-t / 12) * Real.exp (-t * x)) := by ring
              _ = (1 / 12 : ℝ) * Real.exp (-t * (x + 1 / 12)) := by
                    rw [exp_neg_div_twelve_mul_exp_neg_mul]
    _ = (1 / 12 : ℝ) * ∫ t in Set.Ioi 0, Real.exp (-t * (x + 1 / 12)) := by
        simp [MeasureTheory.integral_const_mul]
    _ = (1 / 12 : ℝ) * (x + 1 / 12)⁻¹ := by rw [hbase]
    _ = (12 * x + 1)⁻¹ := by field_simp

/-- **Robbins lower bound for the Binet integral** (real part).

For `x > 0`, `(12x + 1)⁻¹ ≤ re (J x)`. This is the kernel monotonicity input for Robbins'
lower Stirling bound; see [robbins1955]. -/
theorem re_J_ge_one_div_twelve_add_one {x : ℝ} (hx : 0 < x) :
    (12 * x + 1)⁻¹ ≤ (J (x : ℂ)).re := by
  have hJ : (J (x : ℂ)).re =
      ∫ t in Set.Ioi 0, BinetKernel.Ktilde t * Real.exp (-t * x) :=
    re_J_eq_integral_Ktilde (x := x) hx
  rw [hJ]
  have h_bound : ∀ t ∈ Set.Ioi 0,
      (1 / 12 : ℝ) * Real.exp (-t / 12) ≤ BinetKernel.Ktilde t := by
    intro t ht
    simpa using
      (BinetKernel.Ktilde_ge_one_div_twelve_mul_exp_neg_div_twelve (t := t)
        (by simpa using ht))
  have h_int_le :
      ∫ t in Set.Ioi 0, (1 / 12 : ℝ) * Real.exp (-t / 12) * Real.exp (-t * x) ≤
        ∫ t in Set.Ioi 0, BinetKernel.Ktilde t * Real.exp (-t * x) := by
    refine MeasureTheory.setIntegral_mono_ae_restrict
      (integrable_robbins_lower_majorant hx)
      (integrable_Ktilde_mul_exp_real hx) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    gcongr
    exact h_bound t ht
  have h_lhs := integral_robbins_lower_majorant hx
  rw [h_lhs] at h_int_le
  exact h_int_le

end Binet
