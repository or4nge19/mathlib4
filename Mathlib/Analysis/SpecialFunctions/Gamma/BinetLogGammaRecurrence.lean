/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.BinetLogGammaPre

/-!
# Recurrence for the real Binet integral

Proves `re_J_sub_re_J_add_one`, the key shift relation for the real part of `Binet.J`.
-/

open Real Complex Set Filter Topology MeasureTheory BinetKernel
open scoped BigOperators Nat

@[expose] public section

noncomputable section

namespace Binet
/-- Recurrence for the real part of the Binet integral. -/
theorem re_J_sub_re_J_add_one {x : ℝ} (hx : 0 < x) :
    (Binet.J (x : ℂ)).re - (Binet.J ((x : ℂ) + 1)).re =
      (x + 1 / 2) * Real.log (1 + 1 / x) - 1 := by
  -- rewrite both real parts as real integrals
  have hx1 : 0 < x + 1 := by linarith
  have hJx : (Binet.J (x : ℂ)).re =
      ∫ t in Set.Ioi (0 : ℝ), BinetKernel.Ktilde t * Real.exp (-t * x) :=
    re_J_eq_integral_Ktilde (x := x) hx
  have hJx1 : (Binet.J ((x : ℂ) + 1)).re =
      ∫ t in Set.Ioi (0 : ℝ), BinetKernel.Ktilde t * Real.exp (-t * (x + 1)) := by
    -- rewrite `((x:ℂ)+1)` as `((x+1):ℂ)` to use the real lemma
    simpa using (re_J_eq_integral_Ktilde (x := x + 1) hx1)
  -- work with the difference of integrals
  rw [hJx, hJx1]
  have hInt_x : IntegrableOn (fun t : ℝ => BinetKernel.Ktilde t * Real.exp (-t * x)) (Set.Ioi 0) :=
    integrable_Ktilde_mul_exp_real (x := x) hx
  have hInt_x1 : IntegrableOn (fun t : ℝ => BinetKernel.Ktilde t * Real.exp (-t * (x + 1))) (Set.Ioi 0) :=
    integrable_Ktilde_mul_exp_real (x := x + 1) hx1
  -- convert to integrals w.r.t. the restricted measure and combine using `integral_sub`
  have hsub :
      (∫ t in Set.Ioi (0 : ℝ), BinetKernel.Ktilde t * Real.exp (-t * x)) -
        (∫ t in Set.Ioi (0 : ℝ), BinetKernel.Ktilde t * Real.exp (-t * (x + 1))) =
        ∫ t in Set.Ioi (0 : ℝ),
          (BinetKernel.Ktilde t * Real.exp (-t * x) - BinetKernel.Ktilde t * Real.exp (-t * (x + 1))) := by
    -- `integral_sub` is stated as `∫ (f-g) = ∫ f - ∫ g`, so we use the symmetric direction.
    simpa [sub_eq_add_neg] using
      (MeasureTheory.integral_sub (μ := volume.restrict (Set.Ioi (0 : ℝ)))
        (hf := hInt_x) (hg := hInt_x1)).symm
  rw [hsub]
  -- simplify the integrand to `Ktilde t * exp(-t*x) * (1 - exp(-t))`
  have hintegrand :
      (fun t : ℝ =>
          BinetKernel.Ktilde t * Real.exp (-t * x) - BinetKernel.Ktilde t * Real.exp (-t * (x + 1)))
        = fun t : ℝ => BinetKernel.Ktilde t * Real.exp (-t * x) * (1 - Real.exp (-t)) := by
    funext t
    have : Real.exp (-t * (x + 1)) = Real.exp (-t * x) * Real.exp (-t) := by
      -- `exp (a+b) = exp a * exp b`
      have : -t * (x + 1) = (-t * x) + (-t) := by ring
      simp [this, Real.exp_add, mul_comm]
    rw [this]
    ring
  rw [hintegrand]
  -- replace `Ktilde t * (1 - exp(-t))` by the `u`-integral identity (valid on `t>0`)
  have hkernel :
      ∀ t ∈ Set.Ioi (0 : ℝ),
        BinetKernel.Ktilde t * (1 - Real.exp (-t)) =
          ∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t) := by
    intro t ht
    exact Ktilde_mul_one_sub_exp_eq_integral (t := t) ht
  -- use the pointwise identity under the integral
  have hswap1 :
      ∫ t in Set.Ioi (0 : ℝ), BinetKernel.Ktilde t * Real.exp (-t * x) * (1 - Real.exp (-t)) =
        ∫ t in Set.Ioi (0 : ℝ),
          Real.exp (-t * x) * (∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    dsimp
    -- move the `exp(-t*x)` factor to the front so we can apply `hkernel`
    have : BinetKernel.Ktilde t * Real.exp (-t * x) * (1 - Real.exp (-t)) =
        Real.exp (-t * x) * (BinetKernel.Ktilde t * (1 - Real.exp (-t))) := by ring
    rw [this, hkernel t ht]
  rw [hswap1]
  -- Swap integrals (Fubini).
  -- Define the two-variable integrand.
  let F : ℝ → ℝ → ℝ := fun t u =>
    Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t))
  have hF_int :
      Integrable (Function.uncurry F)
        ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    -- Use `integrable_prod_iff` with a simple dominating function.
    have hmeas :
        AEStronglyMeasurable (Function.uncurry F)
          ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
      -- continuous => (ae-)strongly measurable
      have hcont : Continuous (Function.uncurry F) := by
        -- `continuity` can handle this composite expression
        simpa [F] using (by
          fun_prop)
      exact hcont.aestronglyMeasurable
    -- Apply the criterion.
    refine (MeasureTheory.integrable_prod_iff hmeas).2 ?_
    constructor
    · -- for a.e. t, the `u`-section is integrable on `[0,1]`
      -- we are working under `volume.restrict (Ioi 0)`, so extract `0 < t`
      refine (MeasureTheory.ae_restrict_iff' (μ := volume) (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi).2 ?_
      refine MeasureTheory.ae_of_all _ ?_
      intro t ht
      have ht0 : 0 < t := ht
      -- bound by a constant in `u`
      haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
        -- volume of a bounded interval is finite
        have : (volume (Set.Icc (0 : ℝ) 1)) ≠ ⊤ := by simp
        exact (MeasureTheory.isFiniteMeasure_restrict).2 this
      -- show integrable by domination with a constant function
      refine (MeasureTheory.Integrable.mono' (μ := volume.restrict (Set.Icc (0 : ℝ) 1))
        (hg := MeasureTheory.integrable_const (c := (Real.exp (-t * x) / 2 : ℝ))) ?_ ?_)
      · -- measurability
        have : Continuous fun u : ℝ => F t u := by
          -- continuous in `u`
          have : Continuous fun u : ℝ => Real.exp (-t * x) := continuous_const
          have : Continuous fun u : ℝ => (1 / 2 - u) * Real.exp (-u * t) := by
            fun_prop
          -- combine
          exact continuous_const.mul this
        exact this.aestronglyMeasurable
      · -- pointwise bound on norms
        -- turn an `ae` goal on the restricted measure into an `ae` goal on `volume`
        -- with an explicit membership hypothesis `u ∈ Icc 0 1`
        refine (MeasureTheory.ae_restrict_iff' (μ := volume) (s := Set.Icc (0 : ℝ) 1) measurableSet_Icc).2 ?_
        refine MeasureTheory.ae_of_all _ ?_
        intro u hu
        have hu' : u ∈ Set.Icc (0 : ℝ) 1 := hu
        have hu0 : 0 ≤ u := hu'.1
        have hu1 : u ≤ 1 := hu'.2
        have h_abs : |(1 / 2 - u) * Real.exp (-u * t)| ≤ (1 / 2 : ℝ) := by
          have h1 : |1 / 2 - u| ≤ (1 / 2 : ℝ) := by
            -- `u ∈ [0,1]` implies `|1/2 - u| ≤ 1/2`
            -- via `abs_sub_le_iff : |a - b| ≤ c ↔ a - c ≤ b ∧ b ≤ a + c`
            refine (abs_sub_le_iff).2 ?_
            constructor <;> linarith [hu0, hu1]
          have h2 : |Real.exp (-u * t)| ≤ (1 : ℝ) := by
            have : -u * t ≤ 0 := by
              have : 0 ≤ u * t := mul_nonneg hu0 (le_of_lt ht0)
              linarith
            -- `exp` is ≤ 1 when the exponent is ≤ 0
            have := Real.exp_le_one_iff.mpr this
            -- nonneg
            have hpos : 0 ≤ Real.exp (-u * t) := (Real.exp_pos _).le
            simpa [abs_of_nonneg hpos] using this
          -- combine
          calc
            |(1 / 2 - u) * Real.exp (-u * t)| = |1 / 2 - u| * |Real.exp (-u * t)| := by
                simp [abs_mul]
            _ ≤ (1 / 2 : ℝ) * 1 := by
                gcongr
            _ = (1 / 2 : ℝ) := by ring
        -- finish: |F t u| ≤ exp(-t*x)/2
        have h_exp_nonneg : 0 ≤ Real.exp (-t * x) := (Real.exp_pos _).le
        have :
            |F t u| ≤ Real.exp (-t * x) / 2 := by
          -- `F t u = exp(-t*x) * ((1/2-u)*exp(-u*t))`
          dsimp [F]
          have : |Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t))|
              = |Real.exp (-t * x)| * |(1 / 2 - u) * Real.exp (-u * t)| := by
                simp [abs_mul]
          rw [this]
          have habs_exp : |Real.exp (-t * x)| = Real.exp (-t * x) := by
            simp
          rw [habs_exp]
          -- now use the bound `h_abs`
          have := mul_le_mul_of_nonneg_left h_abs h_exp_nonneg
          -- `exp * (1/2) = exp/2`
          simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using this
        -- integrable_prod_iff expects `‖F t u‖ ≤ g u`; for ℝ, `‖·‖ = |·|`
        simpa [Real.norm_eq_abs, abs_of_nonneg h_exp_nonneg] using this
    · -- integrability in `t` of the `u`-norm integral
      -- bound `∫‖F t u‖ du` by `(exp (-t*x))/2`
      haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
        have : (volume (Set.Icc (0 : ℝ) 1)) ≠ ⊤ := by simp
        exact (MeasureTheory.isFiniteMeasure_restrict).2 this
      have hbound :
          ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioi (0 : ℝ))),
            (∫ u : ℝ, ‖(Function.uncurry F) (t, u)‖ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
              ≤ (Real.exp (-t * x) / 2 : ℝ) := by
        -- extract the side condition `0 < t` from the restricted measure
        refine (MeasureTheory.ae_restrict_iff' (μ := volume) (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi).2 ?_
        refine MeasureTheory.ae_of_all _ ?_
        intro t ht
        have ht0 : 0 < t := ht
        -- pointwise bound on the integrand
        have h_point :
            ∀ u ∈ Set.Icc (0 : ℝ) 1,
              ‖F t u‖ ≤ (Real.exp (-t * x) / 2 : ℝ) := by
          intro u hu
          -- Pointwise version of the estimate used under the integral.
          have hu0 : 0 ≤ u := hu.1
          have hu1 : u ≤ 1 := hu.2
          have h_abs : |(1 / 2 - u) * Real.exp (-u * t)| ≤ (1 / 2 : ℝ) := by
            have h1 : |1 / 2 - u| ≤ (1 / 2 : ℝ) := by
              -- `u ∈ [0,1]` iff `|u - 1/2| ≤ 1/2`
              -- and `|1/2 - u| = |u - 1/2|`
              have : |u - (1 / 2 : ℝ)| ≤ (1 / 2 : ℝ) := by
                refine (abs_sub_le_iff).2 ?_
                constructor <;> linarith [hu0, hu1]
              simpa [abs_sub_comm] using this
            have h2 : |Real.exp (-u * t)| ≤ (1 : ℝ) := by
              have : -u * t ≤ 0 := by
                have : 0 ≤ u * t := mul_nonneg hu0 (le_of_lt ht0)
                linarith
              have hexp : Real.exp (-u * t) ≤ (1 : ℝ) := Real.exp_le_one_iff.mpr this
              have hpos : 0 ≤ Real.exp (-u * t) := (Real.exp_pos _).le
              simpa [abs_of_nonneg hpos] using hexp
            -- combine
            calc
              |(1 / 2 - u) * Real.exp (-u * t)| = |1 / 2 - u| * |Real.exp (-u * t)| := by
                  simp [abs_mul]
              _ ≤ (1 / 2 : ℝ) * 1 := by
                  gcongr
              _ = (1 / 2 : ℝ) := by ring
          have h_exp_nonneg : 0 ≤ Real.exp (-t * x) := (Real.exp_pos _).le
          have :
              |F t u| ≤ Real.exp (-t * x) / 2 := by
            dsimp [F]
            calc
              |Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t))|
                  = Real.exp (-t * x) * |(1 / 2 - u) * Real.exp (-u * t)| := by
                      simp [abs_mul]
              _ ≤ Real.exp (-t * x) * (1 / 2 : ℝ) := by
                      gcongr
              _ = Real.exp (-t * x) / 2 := by ring
          simpa [Real.norm_eq_abs] using this
        have hmono :
            (fun u : ℝ => ‖F t u‖) ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
              fun _u : ℝ => (Real.exp (-t * x) / 2 : ℝ) := by
          refine (MeasureTheory.ae_restrict_iff' (μ := volume) (s := Set.Icc (0 : ℝ) 1)
            measurableSet_Icc).2 ?_
          refine MeasureTheory.ae_of_all _ ?_
          intro u hu
          exact h_point u hu
        have hconst :
            (∫ u : ℝ, (Real.exp (-t * x) / 2 : ℝ) ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
              = Real.exp (-t * x) / 2 := by
          simp
        have hF_integrable : Integrable (fun u : ℝ => F t u) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
          apply Continuous.integrableOn_Icc
          unfold F
          fun_prop
        have hconst_integrable : Integrable (fun _u : ℝ => (Real.exp (-t * x) / 2 : ℝ)) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
          exact integrable_const _
        have habs_integrable : Integrable (fun u : ℝ => |F t u|) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
          exact hF_integrable.abs
        have hmono' :
            (fun u : ℝ => |F t u|) ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
              fun _u : ℝ => (Real.exp (-t * x) / 2 : ℝ) := by
          simp_rw [Real.norm_eq_abs] at hmono
          exact hmono
        have := MeasureTheory.integral_mono_ae habs_integrable hconst_integrable hmono'
        simpa [hconst] using this
      have hdom : Integrable (fun t : ℝ => (Real.exp (-t * x) / 2 : ℝ))
          (volume.restrict (Set.Ioi (0 : ℝ))) := by
        have hx' : 0 < x := hx
        have : IntegrableOn (fun t : ℝ => Real.exp (-t * x)) (Set.Ioi 0) := by
          have h := integrableOn_exp_mul_Ioi (a := -x) (c := (0:ℝ)) (by linarith : (-x : ℝ) < 0)
          simp only [mul_comm] at h
          grind
        have h2 : IntegrableOn (fun t => Real.exp (-t * x) / 2) (Set.Ioi 0) := by
          simp only [div_eq_mul_inv]
          exact this.mul_const (2⁻¹)
        exact h2.integrable
      refine (MeasureTheory.Integrable.mono' (μ := volume.restrict (Set.Ioi (0 : ℝ))) (hg := hdom)
        ?_ ?_)
      · have hmeas' :
            AEStronglyMeasurable
              (fun t : ℝ =>
                ∫ u : ℝ, ‖(Function.uncurry F) (t, u)‖ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
              (volume.restrict (Set.Ioi (0 : ℝ))) := by
          have hF_meas' : AEStronglyMeasurable (fun p : ℝ × ℝ => ‖Function.uncurry F p‖)
              ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
            exact AEStronglyMeasurable.norm hmeas
          exact AEStronglyMeasurable.integral_prod_right' hF_meas'
        exact hmeas'
      · filter_upwards [hbound] with t ht
        calc ‖∫ u : ℝ, ‖Function.uncurry F (t, u)‖ ∂volume.restrict (Icc 0 1)‖
            = ∫ u : ℝ, ‖Function.uncurry F (t, u)‖ ∂volume.restrict (Icc 0 1) := by
              apply Real.norm_of_nonneg
              apply MeasureTheory.integral_nonneg
              intro u
              exact norm_nonneg _
          _ ≤ rexp (-t * x) / 2 := ht
  have hswap :
      ∫ t in Set.Ioi (0 : ℝ),
          Real.exp (-t * x) * (∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t))
        =
        ∫ u in Set.Icc (0 : ℝ) 1,
          ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t)) := by
    have hswap0 :
        (∫ t in Set.Ioi (0 : ℝ), ∫ u in Set.Icc (0 : ℝ) 1, F t u) =
          ∫ u in Set.Icc (0 : ℝ) 1, ∫ t in Set.Ioi (0 : ℝ), F t u := by
      simpa [Function.uncurry] using
      (MeasureTheory.integral_integral_swap (μ := volume.restrict (Set.Ioi (0 : ℝ)))
        (ν := volume.restrict (Set.Icc (0 : ℝ) 1)) (f := fun t u => F t u) hF_int)
    have hLHS :
        (∫ t in Set.Ioi (0 : ℝ), ∫ u in Set.Icc (0 : ℝ) 1, F t u) =
          ∫ t in Set.Ioi (0 : ℝ),
            Real.exp (-t * x) * (∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t)) := by
      refine MeasureTheory.integral_congr_ae ?_
      refine (MeasureTheory.ae_restrict_iff' (μ := volume) (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi).2 ?_
      refine MeasureTheory.ae_of_all _ ?_
      intro t ht
      have :
          (∫ u in Set.Icc (0 : ℝ) 1, F t u) =
            Real.exp (-t * x) * ∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t) := by
        simp [F, MeasureTheory.integral_const_mul]
      simp [this]
    have hswap1 :
        (∫ t in Set.Ioi (0 : ℝ),
            Real.exp (-t * x) * (∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t))) =
          ∫ u in Set.Icc (0 : ℝ) 1, ∫ t in Set.Ioi (0 : ℝ), F t u := by
      calc
        (∫ t in Set.Ioi (0 : ℝ),
            Real.exp (-t * x) * (∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t)))
            =
            ∫ t in Set.Ioi (0 : ℝ), ∫ u in Set.Icc (0 : ℝ) 1, F t u := by
              simpa using hLHS.symm
        _ = ∫ u in Set.Icc (0 : ℝ) 1, ∫ t in Set.Ioi (0 : ℝ), F t u := hswap0
    simpa [F] using hswap1
  rw [hswap]
  have hx0 : x ≠ 0 := ne_of_gt hx
  have h_inner :
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t)))
          = (1 / 2 - u) * (1 / (x + u)) := by
    intro u hu
    have hu0 : 0 ≤ u := hu.1
    have hxu : 0 < x + u := by linarith [hx, hu0]
    have hmul :
        (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t))) =
          (1 / 2 - u) * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t * (x + u))) := by
      have hrew : (fun t : ℝ => Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t))) =
          fun t : ℝ => (1 / 2 - u) * Real.exp (-(t * (x + u))) := by
        funext t
        have hexp :
            Real.exp (-t * x) * Real.exp (-u * t) = Real.exp ((-t * x) + (-u * t)) := by
          simpa using (Real.exp_add (-t * x) (-u * t)).symm
        have hadd : (-t * x) + (-u * t) = -(t * (x + u)) := by ring
        calc
          Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t))
              = (1 / 2 - u) * (Real.exp (-t * x) * Real.exp (-u * t)) := by
                  ring
          _ = (1 / 2 - u) * Real.exp ((-t * x) + (-u * t)) := by
                  simp; grind
          _ = (1 / 2 - u) * Real.exp (-(t * (x + u))) := by
                  simp; grind
      have hrew_int :
          (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t))) =
            ∫ t in Set.Ioi (0 : ℝ), (1 / 2 - u) * Real.exp (-(t * (x + u))) := by
        simpa using congrArg (fun f : ℝ → ℝ => ∫ t in Set.Ioi (0 : ℝ), f t) hrew
      calc
        (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t)))
            = ∫ t in Set.Ioi (0 : ℝ), (1 / 2 - u) * Real.exp (-(t * (x + u))) := hrew_int
        _ = (1 / 2 - u) * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t * (x + u))) := by
            simp [MeasureTheory.integral_const_mul]
    have hbase : (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t * (x + u)))) = 1 / (x + u) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using (integral_exp_neg_mul_Ioi (x := x + u) hxu)
    calc
      (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t)))
          = (1 / 2 - u) * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t * (x + u))) := hmul
      _ = (1 / 2 - u) * (1 / (x + u)) := by simp [hbase]
  have h_inner_int :
      (∫ u in Set.Icc (0 : ℝ) 1,
          ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t)))
        = ∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * (1 / (x + u)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
    intro u hu
    exact h_inner u hu
  rw [h_inner_int]
  have hrew_u :
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        (1 / 2 - u) * (1 / (x + u)) = (x + 1 / 2) * (1 / (x + u)) - 1 := by
    intro u hu
    have hu0 : 0 ≤ u := hu.1
    have hx_u : x + u ≠ 0 := by
      have : 0 < x + u := by linarith [hx, hu0]
      exact ne_of_gt this
    field_simp [hx_u]
    ring_nf
  have hrew_u_int :
      (∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * (1 / (x + u))) =
        ∫ u in Set.Icc (0 : ℝ) 1, ((x + 1 / 2) * (1 / (x + u)) - 1) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
    intro u hu
    simpa using hrew_u u hu
  rw [hrew_u_int]
  have hxpos : 0 < x := hx
  have h_shift :
      (∫ u in Set.Icc (0 : ℝ) 1, (1 / (x + u) : ℝ)) = Real.log (1 + 1 / x) := by
    have hIcc :
        (∫ u in Set.Icc (0 : ℝ) 1, (1 / (x + u) : ℝ)) = ∫ u in (0 : ℝ)..1, (1 / (x + u) : ℝ) := by
      have hIccIoc :
          (∫ u in Set.Icc (0 : ℝ) 1, (1 / (x + u) : ℝ)) =
            ∫ u in Set.Ioc (0 : ℝ) 1, (1 / (x + u) : ℝ) := by
        simpa using
          (MeasureTheory.integral_Icc_eq_integral_Ioc
            (μ := (volume : Measure ℝ)) (f := fun u : ℝ => (1 / (x + u) : ℝ))
            (x := (0 : ℝ)) (y := (1 : ℝ)))
      have hIoc :
          ∫ u in Set.Ioc (0 : ℝ) 1, (1 / (x + u) : ℝ) = ∫ u in (0 : ℝ)..1, (1 / (x + u) : ℝ) := by
        simpa using
          (intervalIntegral.integral_of_le (μ := (volume : Measure ℝ))
            (a := (0 : ℝ)) (b := (1 : ℝ)) (f := fun u : ℝ => (1 / (x + u) : ℝ))
            (by norm_num : (0 : ℝ) ≤ 1)).symm
      exact hIccIoc.trans hIoc
    rw [hIcc]
    have hshift' :
        (∫ u in (0 : ℝ)..1, (1 / (x + u) : ℝ)) = ∫ u in x..(x + 1), (1 / u : ℝ) := by
      simp
    rw [hshift']
    have hx0' : (0 : ℝ) ∉ Set.uIcc x (x + 1) := by
      intro hxmem
      have hxle : x ≤ x + 1 := by linarith
      have hxmem' : (0 : ℝ) ∈ Set.Icc x (x + 1) := by
        simpa [Set.uIcc, hxle, min_eq_left hxle, max_eq_right hxle] using hxmem
      have hx_le0 : x ≤ (0 : ℝ) := (Set.mem_Icc.1 hxmem').1
      linarith [hxpos, hx_le0]
    have hinv : (∫ u in x..(x + 1), (u : ℝ)⁻¹) = Real.log ((x + 1) / x) := by
      simpa [one_div] using (integral_inv (a := x) (b := x + 1) hx0')
    have hdiv : (x + 1) / x = 1 + 1 / x := by
      field_simp [hx0]
    simpa [one_div, hdiv] using hinv
  have hI1 : (∫ u in Set.Icc (0 : ℝ) 1, (1 : ℝ)) = 1 := by simp
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hInt_inv :
      Integrable (fun u : ℝ => (x + u)⁻¹) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    refine (MeasureTheory.Integrable.mono' (μ := volume.restrict (Set.Icc (0 : ℝ) 1))
      (hg := MeasureTheory.integrable_const (c := ‖(x⁻¹ : ℝ)‖)) ?_ ?_)
    · exact (Measurable.inv ((measurable_const.add measurable_id))).aestronglyMeasurable
    · refine (MeasureTheory.ae_restrict_iff' (μ := volume) (s := Set.Icc (0 : ℝ) 1) measurableSet_Icc).2 ?_
      refine MeasureTheory.ae_of_all _ ?_
      intro u hu
      have hu0 : 0 ≤ u := hu.1
      have hxle : x ≤ x + u := by linarith
      have hxpos' : 0 < x := hxpos
      have hxupos : 0 < x + u := lt_of_lt_of_le hxpos' hxle
      have : (x + u)⁻¹ ≤ x⁻¹ := by
        simpa [one_div] using one_div_le_one_div_of_le hxpos' hxle
      have hnorm1 : ‖(x + u)⁻¹‖ = (x + u)⁻¹ := by
        simp [Real.norm_eq_abs, abs_of_pos hxupos]
      have hnorm2 : ‖(x⁻¹ : ℝ)‖ = x⁻¹ := by
        simp [Real.norm_eq_abs, abs_of_pos hxpos']
      simpa [hnorm1, hnorm2] using this
  have hInt_mul :
      Integrable (fun u : ℝ => (x + (1 / 2 : ℝ)) * (x + u)⁻¹) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    hInt_inv.const_mul (x + (1 / 2 : ℝ))
  have hInt_const :
      Integrable (fun _u : ℝ => (-1 : ℝ)) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    integrable_const _
  have hadd :
      (∫ u in Set.Icc (0 : ℝ) 1, (-1 : ℝ) + (x + (1 / 2 : ℝ)) * (x + u)⁻¹) =
        (∫ u in Set.Icc (0 : ℝ) 1, (-1 : ℝ)) +
          ∫ u in Set.Icc (0 : ℝ) 1, (x + (1 / 2 : ℝ)) * (x + u)⁻¹ := by
    simpa using
      (MeasureTheory.integral_add (μ := volume.restrict (Set.Icc (0 : ℝ) 1)) hInt_const hInt_mul)
  have hmul_shift :
      (∫ u in Set.Icc (0 : ℝ) 1, (x + (1 / 2 : ℝ)) * (x + u)⁻¹)
        = (x + (1 / 2 : ℝ)) * Real.log (1 + 1 / x) := by
    calc
      (∫ u in Set.Icc (0 : ℝ) 1, (x + (1 / 2 : ℝ)) * (x + u)⁻¹)
          = (x + (1 / 2 : ℝ)) * ∫ u in Set.Icc (0 : ℝ) 1, (x + u)⁻¹ := by
              simp [MeasureTheory.integral_const_mul]
      _ = (x + (1 / 2 : ℝ)) * Real.log (1 + 1 / x) := by
              simpa [one_div] using congrArg (fun z => (x + (1 / 2 : ℝ)) * z) h_shift
  have hconst : (∫ u in Set.Icc (0 : ℝ) 1, (-1 : ℝ)) = -1 := by simp
  have hrew_goal :
      (∫ u in Set.Icc (0 : ℝ) 1, (x + (1 / 2 : ℝ)) * (1 / (x + u)) - 1) =
        ∫ u in Set.Icc (0 : ℝ) 1, (-1 : ℝ) + (x + (1 / 2 : ℝ)) * (x + u)⁻¹ := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
    intro u hu
    simp [one_div, sub_eq_add_neg, add_comm, mul_comm]
  rw [hrew_goal]
  calc
    ∫ u in Set.Icc (0 : ℝ) 1, (-1 : ℝ) + (x + (1 / 2 : ℝ)) * (x + u)⁻¹
        = (-1) + (x + (1 / 2 : ℝ)) * Real.log (1 + 1 / x) := by
            rw [hadd, hconst, hmul_shift]
    _ = (x + (1 / 2 : ℝ)) * Real.log (1 + 1 / x) - 1 := by ring
