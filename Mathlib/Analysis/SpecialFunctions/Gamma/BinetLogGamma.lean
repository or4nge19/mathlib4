/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.BinetLogGammaPre
public import Mathlib.Analysis.SpecialFunctions.Gamma.BinetLogGammaRecurrence

/-!
# Binet's formula for `log Γ` on the positive real axis

This module aggregates the development in `BinetLogGammaPre` and `BinetLogGammaRecurrence`,
and proves the limiting and closed-form statements (`log_Gamma_real_eq`, etc.).
-/

open Real Complex Set Filter Topology MeasureTheory BinetKernel
open scoped BigOperators Nat

@[expose] public section

noncomputable section

namespace Binet

/-- The correction difference `R x - re (J x)` is invariant under `x ↦ x + 1`. -/
private lemma R_sub_re_J_add_one {x : ℝ} (hx : 0 < x) :
    R x - (Binet.J (x : ℂ)).re =
      R (x + 1) - (Binet.J ((x + 1 : ℝ) : ℂ)).re := by
  have hRrec := R_sub_R_add_one (x := x) hx
  have hJrec := re_J_sub_re_J_add_one (x := x) hx
  have hdiff :
      R x - R (x + 1) =
        (Binet.J (x : ℂ)).re - (Binet.J ((x : ℂ) + 1)).re := by
    calc
      R x - R (x + 1)
          = (x + 1 / 2) * Real.log (1 + 1 / x) - 1 := hRrec
      _ = (Binet.J (x : ℂ)).re - (Binet.J ((x : ℂ) + 1)).re := by
          simpa using hJrec.symm
  have :
      R x - (Binet.J (x : ℂ)).re =
        R (x + 1) - (Binet.J ((x : ℂ) + 1)).re := by
    linarith [hdiff]
  simpa using this

/-- The real part of the Binet correction tends to zero on the positive real axis. -/
theorem tendsto_re_J_atTop_zero :
    Tendsto (fun y : ℝ => (Binet.J (y : ℂ)).re) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨(1 / (12 * ε) : ℝ) + 1, ?_⟩
  intro y hy
  have hy_pos : 0 < y := by
    have : 0 < (1 / (12 * ε) : ℝ) := by positivity
    have : 0 < (1 / (12 * ε) : ℝ) + 1 := by linarith
    exact this.trans_le hy
  have hbound : |(Binet.J (y : ℂ)).re| ≤ 1 / (12 * y) := by
    exact le_trans (Complex.abs_re_le_norm (Binet.J (y : ℂ))) (J_norm_le_real (x := y) hy_pos)
  have h1 : 1 / (12 * y) < ε := by
    have hy' : 0 < 12 * y := by positivity
    have hy_gt : (1 / (12 * ε) : ℝ) < y := by linarith
    have hpos : 0 < (12 * ε : ℝ) := by positivity
    have hmul :
        (12 * ε : ℝ) * (1 / (12 * ε) : ℝ) < (12 * ε : ℝ) * y :=
      mul_lt_mul_of_pos_left hy_gt hpos
    have hleft : (12 * ε : ℝ) * (1 / (12 * ε) : ℝ) = 1 := by field_simp
    rw [hleft] at hmul
    have hbig : (1 : ℝ) < ε * (12 * y) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    exact (div_lt_iff₀ hy').2 (by simpa [mul_assoc] using hbig)
  have : |(Binet.J (y : ℂ)).re - 0| < ε := by
    simpa using lt_of_le_of_lt hbound h1
  simpa [Real.dist_eq] using this

private lemma R_nat_eq_log_stirlingSeq_sub_log_pi_half {n : ℕ} (hn : 0 < n) :
    R (n : ℝ) = Real.log (Stirling.stirlingSeq n) - Real.log Real.pi / 2 := by
  have hGamma_n : Real.Gamma (n : ℝ) = ((n - 1)! : ℝ) := by
    have hn_succ : (n - 1).succ = n := Nat.succ_pred_eq_of_pos hn
    have hcast : ((n - 1 : ℕ) : ℝ) + 1 = n := by
      have := congrArg (fun k : ℕ => (k : ℝ)) hn_succ
      simpa [Nat.cast_succ] using this
    have hGamma := Real.Gamma_nat_eq_factorial (n - 1)
    simpa [hcast, Nat.cast_add, Nat.cast_one, add_assoc] using hGamma
  have hlogGamma :
      Real.log (Real.Gamma (n : ℝ)) = Real.log (n ! : ℝ) - Real.log (n : ℝ) := by
    have hpred_fact_ne : (((n - 1)! : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.factorial_ne_zero (n - 1))
    have hn_ne : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn)
    have hfac : (n ! : ℝ) = (n : ℝ) * ((n - 1)! : ℝ) := by
      have hn' : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn)
      have hnat : ((n - 1 + 1) ! : ℕ) = (n - 1 + 1) * (n - 1)! :=
        Nat.factorial_succ (n - 1)
      have := congrArg (fun k : ℕ => (k : ℝ)) hnat
      simpa [hn', Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_assoc, mul_comm,
        mul_left_comm] using this
    have hlog_mul :
        Real.log (n ! : ℝ) = Real.log (n : ℝ) + Real.log ((n - 1)! : ℝ) := by
      have h : Real.log ((n : ℝ) * ((n - 1)! : ℝ)) =
          Real.log (n : ℝ) + Real.log ((n - 1)! : ℝ) := by
        simpa using
          Real.log_mul (x := (n : ℝ)) (y := ((n - 1)! : ℝ)) hn_ne hpred_fact_ne
      simpa [hfac, mul_comm, add_comm, add_left_comm, add_assoc] using h
    have : Real.log ((n - 1)! : ℝ) = Real.log (n ! : ℝ) - Real.log (n : ℝ) := by
      linarith
    simp [hGamma_n, this]
  unfold R stirlingMainReal
  have hlog_pi2 : Real.log (Real.pi * 2) = Real.log Real.pi + Real.log 2 := by
    simpa [mul_comm] using Real.log_mul (Real.pi_pos.ne') (by norm_num : (2 : ℝ) ≠ 0)
  have hlogst_formula' :
      Real.log (Stirling.stirlingSeq n) =
        Real.log (n ! : ℝ) - (1 / 2 : ℝ) * (Real.log 2 + Real.log (n : ℝ))
          - (n : ℝ) * (Real.log (n : ℝ) - 1) := by
    have hn_pos_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hn_ne : (n : ℝ) ≠ 0 := hn_pos_real.ne'
    have h2_ne : (2 : ℝ) ≠ 0 := by norm_num
    have hlog_2n : Real.log (2 * (n : ℝ)) = Real.log 2 + Real.log (n : ℝ) := by
      simpa using Real.log_mul h2_ne hn_ne
    have hlog_div : Real.log ((n : ℝ) / Real.exp 1) = Real.log (n : ℝ) - 1 := by
      simpa [Real.log_exp, sub_eq_add_neg] using
        (Real.log_div hn_ne (Real.exp_pos 1).ne')
    have h0 :
        Real.log (Stirling.stirlingSeq n) =
          Real.log (n ! : ℝ) - (1 / 2 : ℝ) * Real.log (2 * (n : ℝ))
            - (n : ℝ) * Real.log ((n : ℝ) / Real.exp 1) := by
      simpa [Stirling.stirlingSeq, sub_eq_add_neg, one_div, mul_assoc, mul_left_comm,
        mul_comm, add_assoc, add_left_comm, add_comm] using
          Stirling.log_stirlingSeq_formula n
    calc
      Real.log (Stirling.stirlingSeq n)
          = Real.log (n ! : ℝ) - (1 / 2 : ℝ) * Real.log (2 * (n : ℝ))
              - (n : ℝ) * Real.log ((n : ℝ) / Real.exp 1) := h0
      _ = Real.log (n ! : ℝ) - (1 / 2 : ℝ) * (Real.log 2 + Real.log (n : ℝ))
            - (n : ℝ) * (Real.log (n : ℝ) - 1) := by
          simp [hlog_2n, hlog_div]
  simp [hlogGamma, hlogst_formula', hlog_pi2, sub_eq_add_neg, mul_add, add_mul,
    mul_comm]
  ring_nf

private lemma stirlingMainReal_floor_lower_step {y : ℝ} {n : ℕ}
    (hn_pos : 0 < (n : ℝ)) (hy1 : 0 ≤ y - (1 / 2 : ℝ))
    (ha_nonneg : 0 ≤ y - (n : ℝ)) (ha_le : y - (n : ℝ) ≤ 1)
    (hlogy_ub : Real.log y ≤ Real.log (n : ℝ) + (y - (n : ℝ)) / (n : ℝ))
    (hlognm1 : Real.log ((n - 1 : ℕ) : ℝ) ≥
      Real.log (n : ℝ) - (2 : ℝ) / (n : ℝ)) :
    stirlingMainReal (n : ℝ) +
        (y - (n : ℝ)) * Real.log ((n - 1 : ℕ) : ℝ) - stirlingMainReal y ≥
      - (3 / (n : ℝ)) := by
  unfold stirlingMainReal
  have hlogy_mul :
      (y - (1 / 2 : ℝ)) * Real.log y ≤
        (y - (1 / 2 : ℝ)) *
          (Real.log (n : ℝ) + (y - (n : ℝ)) / (n : ℝ)) :=
    mul_le_mul_of_nonneg_left hlogy_ub hy1
  have hlognm1_mul :
      (y - (n : ℝ)) * (Real.log (n : ℝ) - (2 : ℝ) / (n : ℝ)) ≤
        (y - (n : ℝ)) * Real.log ((n - 1 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hlognm1 ha_nonneg
  set a : ℝ := y - (n : ℝ) with ha
  have ha0 : 0 ≤ a := by simpa [a] using ha_nonneg
  have ha1 : a ≤ 1 := by simpa [a] using ha_le
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hy_a : y = (n : ℝ) + a := by
    dsimp [a]
    ring
  have hrew0 :
      ((n - 1 / 2) * Real.log (n : ℝ) - (n : ℝ) + Real.log (2 * π) / 2
          + (y - (n : ℝ)) * Real.log ((n - 1 : ℕ) : ℝ)
          - ((y - 1 / 2) * Real.log y - y + Real.log (2 * π) / 2)) =
        ((n - 1 / 2) * Real.log (n : ℝ) - (n : ℝ)
          + a * Real.log ((n - 1 : ℕ) : ℝ)
          + (-((y - 1 / 2) * Real.log y)) + y) := by
    ring
  have h1 :
      a * (Real.log (n : ℝ) - (2 : ℝ) / (n : ℝ)) ≤
        a * Real.log ((n - 1 : ℕ) : ℝ) := by
    simpa [a] using hlognm1_mul
  have h2 :
      -((y - 1 / 2) * (Real.log (n : ℝ) + a / (n : ℝ))) ≤
        -((y - 1 / 2) * Real.log y) := by
    simpa [a] using neg_le_neg hlogy_mul
  have hmain_lower :
      ((n - 1 / 2) * Real.log (n : ℝ) - (n : ℝ)
          + a * Real.log ((n - 1 : ℕ) : ℝ)
          + (-((y - 1 / 2) * Real.log y)) + y) ≥
        ((n - 1 / 2) * Real.log (n : ℝ) - (n : ℝ)
          + a * (Real.log (n : ℝ) - (2 : ℝ) / (n : ℝ))
          + (-((y - 1 / 2) * (Real.log (n : ℝ) + a / (n : ℝ)))) + y) := by
    linarith [h1, h2]
  have hsimp :
      ((n - 1 / 2) * Real.log (n : ℝ) - (n : ℝ)
          + a * (Real.log (n : ℝ) - (2 : ℝ) / (n : ℝ))
          + (-((y - 1 / 2) * (Real.log (n : ℝ) + a / (n : ℝ)))) + y) =
        a * (1 / 2 - a) / (n : ℝ) - 2 * a / (n : ℝ) := by
    rw [hy_a]
    field_simp [hn0]
    ring
  have hfinal : a * (1 / 2 - a) / (n : ℝ) - 2 * a / (n : ℝ) ≥
      - (3 / (n : ℝ)) := by
    have hnum : (-3 : ℝ) ≤ a * (1 / 2 - a) - 2 * a := by
      nlinarith [ha0, ha1]
    have hdiv :
        (-3 : ℝ) / (n : ℝ) ≤ (a * (1 / 2 - a) - 2 * a) / (n : ℝ) :=
      div_le_div_of_nonneg_right hnum (le_of_lt hn_pos)
    have hrew :
        a * (1 / 2 - a) / (n : ℝ) - 2 * a / (n : ℝ) =
          (a * (1 / 2 - a) - 2 * a) / (n : ℝ) := by
      field_simp [hn0]
    calc
      - (3 / (n : ℝ)) = (-3 : ℝ) / (n : ℝ) := by simp [neg_div]
      _ ≤ (a * (1 / 2 - a) - 2 * a) / (n : ℝ) := hdiv
      _ = a * (1 / 2 - a) / (n : ℝ) - 2 * a / (n : ℝ) := hrew.symm
  calc
    ((n - 1 / 2) * Real.log (n : ℝ) - (n : ℝ) + Real.log (2 * π) / 2
        + (y - (n : ℝ)) * Real.log ((n - 1 : ℕ) : ℝ)
        - ((y - 1 / 2) * Real.log y - y + Real.log (2 * π) / 2))
        = ((n - 1 / 2) * Real.log (n : ℝ) - (n : ℝ)
            + a * Real.log ((n - 1 : ℕ) : ℝ)
            + (-((y - 1 / 2) * Real.log y)) + y) := hrew0
    _ ≥ ((n - 1 / 2) * Real.log (n : ℝ) - (n : ℝ)
            + a * (Real.log (n : ℝ) - (2 : ℝ) / (n : ℝ))
            + (-((y - 1 / 2) * (Real.log (n : ℝ) + a / (n : ℝ)))) + y) :=
          hmain_lower
    _ = a * (1 / 2 - a) / (n : ℝ) - 2 * a / (n : ℝ) := hsimp
    _ ≥ - (3 / (n : ℝ)) := hfinal

private lemma eq_zero_of_tendsto_atTop_periodic_add_one {h : ℝ → ℝ} {x : ℝ}
    (hx : 0 < x) (h_periodic : ∀ y, 0 < y → h y = h (y + 1))
    (hlim : Tendsto h atTop (𝓝 0)) :
    h x = 0 := by
  have hxseq : Tendsto (fun n : ℕ => h (x + n)) atTop (𝓝 0) := by
    have hxadd : Tendsto (fun n : ℕ => (x + n : ℝ)) atTop atTop := by
      have hnx : Tendsto (fun n : ℕ => ((n : ℝ) + x)) atTop atTop :=
        Filter.Tendsto.atTop_add tendsto_natCast_atTop_atTop tendsto_const_nhds
      simpa [add_assoc, add_comm, add_left_comm] using hnx
    exact hlim.comp hxadd
  have hconst : (fun n : ℕ => h (x + n)) = fun _ => h x := by
    funext n
    induction n with
    | zero => simp
    | succ n ih =>
        have hxpos : 0 < x + n := by linarith [hx]
        have hstep : h (x + (n + 1)) = h (x + n) := by
          simpa [add_assoc, add_comm, add_left_comm] using (h_periodic (x + n) hxpos).symm
        simpa [ih] using hstep
  rw [hconst] at hxseq
  exact tendsto_const_nhds_iff.mp hxseq

/-- Binet's formula for real arguments. -/
theorem log_Gamma_real_eq {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma x) =
      (x - 1/2) * Real.log x - x + Real.log (2 * Real.pi) / 2 + (J x).re := by
  have hR : R x = (Binet.J (x : ℂ)).re := by
    let h : ℝ → ℝ := fun y => R y - (Binet.J (y : ℂ)).re
    have h_periodic : ∀ y, 0 < y → h y = h (y + 1) := by
      intro y hy
      dsimp [h]
      exact R_sub_re_J_add_one hy
    have hRlim : Tendsto R atTop (𝓝 0) := by
      have hnat : Tendsto (fun n : ℕ => R (n : ℝ)) atTop (𝓝 0) := by
        have hst : Tendsto Stirling.stirlingSeq atTop (𝓝 (Real.sqrt Real.pi)) :=
          Stirling.tendsto_stirlingSeq_sqrt_pi
        have hlogst : Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n))
            atTop (𝓝 (Real.log (Real.sqrt Real.pi))) :=
          (Real.continuousAt_log (by
            have : (0 : ℝ) < Real.sqrt Real.pi := by
              have : (0 : ℝ) < Real.pi := Real.pi_pos
              simpa using Real.sqrt_pos.2 this
            exact ne_of_gt this)).tendsto.comp hst
        have hπ : Real.log (Real.sqrt Real.pi) = Real.log Real.pi / 2 := by
          simpa using (Real.log_sqrt (x := Real.pi) (by exact le_of_lt Real.pi_pos))
        have hR_eq :
            (fun n : ℕ => R (n : ℝ)) =ᶠ[atTop]
              fun n : ℕ => Real.log (Stirling.stirlingSeq n) - Real.log Real.pi / 2 := by
          filter_upwards [eventually_gt_atTop 0] with n hn
          exact R_nat_eq_log_stirlingSeq_sub_log_pi_half hn
        have h_tendsto :
            Tendsto
              (fun n : ℕ => Real.log (Stirling.stirlingSeq n) - Real.log Real.pi / 2)
              atTop (𝓝 0) :=
          by simpa [hπ, sub_eq_add_neg, add_assoc] using hlogst.sub_const (Real.log Real.pi / 2)
        exact (tendsto_congr' hR_eq).2 h_tendsto
      rw [Metric.tendsto_atTop]
      intro ε hε
      have hnat' := (Metric.tendsto_atTop).1 hnat (ε / 2) (by positivity)
      rcases hnat' with ⟨N1, hN1⟩
      have h_inv : Tendsto (fun n : ℕ => (3 : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
        have : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 (0 : ℝ)) :=
          tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
        simpa [div_eq_mul_inv, mul_assoc] using (this.const_mul (3 : ℝ))
      have h_inv' := (Metric.tendsto_atTop).1 h_inv (ε / 2) (by positivity)
      rcases h_inv' with ⟨N2, hN2⟩
      let N : ℕ := max (max N1 N2) 2
      refine ⟨(N : ℝ) + 1, ?_⟩
      intro y hy
      have hy0 : 0 ≤ y := by linarith
      let n : ℕ := ⌊y⌋₊
      have hn_le : (n : ℝ) ≤ y := Nat.floor_le hy0
      have hy_lt : y < (n : ℝ) + 1 := Nat.lt_floor_add_one y
      have hn_ge : N ≤ n := by
        by_contra h
        have hn_lt : n < N := Nat.lt_of_not_ge h
        have : y < (N : ℝ) := (Nat.floor_lt hy0).1 hn_lt
        linarith
      have hn2 : 2 ≤ n := le_trans (by exact le_max_right _ _) hn_ge
      have hn_pos : 0 < (n : ℝ) := by
        have : (0 : ℝ) < (2 : ℝ) := by norm_num
        exact this.trans_le (by exact_mod_cast hn2)
      have hn1_pos : 0 < (n - 1 : ℕ) := by
        exact Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by norm_num : 1 < 2) hn2)
      have ha0 : 0 ≤ y - n := sub_nonneg.2 hn_le
      have ha1 : y - n < 1 := by
        have : y < (n : ℝ) + 1 := hy_lt
        linarith
      have ha_le : y - n ≤ 1 := le_of_lt ha1
      have hf := Real.convexOn_log_Gamma
      have h_upper :
          Real.log (Real.Gamma y) ≤
            Real.log (Real.Gamma (n : ℝ)) + (y - n) * Real.log (n : ℝ) := by
        by_cases hy_eq : y = (n : ℝ)
        · have hy_sub : y - n = 0 := by linarith [hy_eq]
          simp [hy_eq]
        · have hn_mem : (n : ℝ) ∈ Set.Ioi (0 : ℝ) := hn_pos
          have hy_mem : y ∈ Set.Ioi (0 : ℝ) := lt_of_lt_of_le hn_pos hn_le
          have hn1_mem : (n : ℝ) + 1 ∈ Set.Ioi (0 : ℝ) := by
            change (0 : ℝ) < (n : ℝ) + 1
            exact Nat.cast_add_one_pos n
          have hn1_ne : (n : ℝ) + 1 ≠ (n : ℝ) := by norm_num
          have hsec :=
            ConvexOn.secant_mono (f := fun z : ℝ => Real.log (Real.Gamma z)) hf
              hn_mem hy_mem hn1_mem hy_eq hn1_ne (le_of_lt hy_lt)
          have hdiff :
              (Real.log (Real.Gamma y) - Real.log (Real.Gamma (n : ℝ))) / (y - n) ≤
                Real.log (Real.Gamma ((n : ℝ) + 1)) - Real.log (Real.Gamma (n : ℝ)) := by
            simpa using hsec
          have hy_n_pos : 0 < y - n := sub_pos.2 (lt_of_le_of_ne hn_le (Ne.symm hy_eq))
          have := (div_le_iff₀ hy_n_pos).1 hdiff
          have hstep :
              Real.log (Real.Gamma ((n : ℝ) + 1)) - Real.log (Real.Gamma (n : ℝ)) =
                Real.log (n : ℝ) := by
            have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
            have hΓ : Real.Gamma ((n : ℝ) + 1) = (n : ℝ) * Real.Gamma (n : ℝ) :=
              Real.Gamma_add_one (s := (n : ℝ)) hn_ne
            have hΓn_ne : Real.Gamma (n : ℝ) ≠ 0 := (Real.Gamma_pos_of_pos hn_pos).ne'
            calc
              Real.log (Real.Gamma ((n : ℝ) + 1)) - Real.log (Real.Gamma (n : ℝ))
                  = (Real.log (n : ℝ) + Real.log (Real.Gamma (n : ℝ))) -
                      Real.log (Real.Gamma (n : ℝ)) := by
                      simp [hΓ, Real.log_mul hn_ne hΓn_ne]
              _ = Real.log (n : ℝ) := by ring
          have hmul :
              Real.log (Real.Gamma y) - Real.log (Real.Gamma (n : ℝ)) ≤
                Real.log (n : ℝ) * (y - n) := by
            simpa [hstep] using this
          have := add_le_add_left hmul (Real.log (Real.Gamma (n : ℝ)))
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
            mul_assoc, mul_left_comm, mul_comm] using this
      have h_lower :
          Real.log (Real.Gamma y) ≥
            Real.log (Real.Gamma (n : ℝ)) + (y - n) * Real.log ((n - 1 : ℕ) : ℝ) := by
        by_cases hy_eq : y = (n : ℝ)
        · have hy_sub : y - n = 0 := by linarith [hy_eq]
          simp [hy_eq]
        · have hn_1_mem : ((n - 1 : ℕ) : ℝ) ∈ Set.Ioi (0 : ℝ) := by
            have : (0 : ℝ) < (n - 1 : ℕ) := by exact_mod_cast hn1_pos
            simpa using this
          have hn_mem : (n : ℝ) ∈ Set.Ioi (0 : ℝ) := hn_pos
          have hy_mem : y ∈ Set.Ioi (0 : ℝ) := lt_of_lt_of_le hn_pos hn_le
          have hn_nat_pos : 0 < n := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hn2
          have hn1_ne : ((n - 1 : ℕ) : ℝ) ≠ (n : ℝ) := by
            have hlt : n - 1 < n := Nat.sub_lt_self (Nat.succ_pos 0) hn_nat_pos
            exact ne_of_lt (by exact_mod_cast hlt : ((n - 1 : ℕ) : ℝ) < (n : ℝ))
          have hn1_le_n : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
            exact_mod_cast (Nat.sub_le n 1)
          have hn1_le_y : ((n - 1 : ℕ) : ℝ) ≤ y := le_trans hn1_le_n hn_le
          have hsec :=
            ConvexOn.secant_mono (f := fun z : ℝ => Real.log (Real.Gamma z)) hf
              hn_mem hn_1_mem hy_mem hn1_ne hy_eq hn1_le_y
          have hdiff :
              (Real.log (Real.Gamma ((n - 1 : ℕ) : ℝ)) - Real.log (Real.Gamma (n : ℝ))) /
                    (((n - 1 : ℕ) : ℝ) - (n : ℝ)) ≤
                (Real.log (Real.Gamma y) - Real.log (Real.Gamma (n : ℝ))) / (y - n) := by
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsec
          have hy_n_pos : 0 < y - n := sub_pos.2 (lt_of_le_of_ne hn_le (Ne.symm hy_eq))
          have hy_gt_n : (n : ℝ) < y := lt_of_le_of_ne hn_le (Ne.symm hy_eq)
          have hleft :
              (Real.log (Real.Gamma ((n - 1 : ℕ) : ℝ)) - Real.log (Real.Gamma (n : ℝ))) /
                    (((n - 1 : ℕ) : ℝ) - (n : ℝ)) =
                Real.log ((n - 1 : ℕ) : ℝ) := by
            have hn1_ne0 : ((n - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn1_pos)
            have hΓ :
                Real.Gamma (n : ℝ) =
                  ((n - 1 : ℕ) : ℝ) * Real.Gamma ((n - 1 : ℕ) : ℝ) := by
              have hnat : (n - 1 : ℕ) + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn_nat_pos)
              have hcast : (n : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
                exact_mod_cast hnat.symm
              have hΓ' := Real.Gamma_add_one (s := ((n - 1 : ℕ) : ℝ)) hn1_ne0
              simpa [hcast, add_comm, add_left_comm, add_assoc] using hΓ'
            have hΓn1_ne : Real.Gamma ((n - 1 : ℕ) : ℝ) ≠ 0 :=
              (Real.Gamma_pos_of_pos (by exact_mod_cast hn1_pos)).ne'
            have hlog :
                Real.log (Real.Gamma (n : ℝ)) =
                  Real.log ((n - 1 : ℕ) : ℝ) + Real.log (Real.Gamma ((n - 1 : ℕ) : ℝ)) := by
              simp [hΓ, Real.log_mul hn1_ne0 hΓn1_ne]
            have hnum :
                Real.log (Real.Gamma ((n - 1 : ℕ) : ℝ)) - Real.log (Real.Gamma (n : ℝ)) =
                  - Real.log ((n - 1 : ℕ) : ℝ) := by
              linarith [hlog]
            have hden : (((n - 1 : ℕ) : ℝ) - (n : ℝ)) = (-1 : ℝ) := by
              have hnat : (n - 1 : ℕ) + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn_nat_pos)
              have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by exact_mod_cast hnat
              linarith
            simp [hnum, hden]
          have hmul := (le_div_iff₀ hy_n_pos).1 (by simpa [hleft] using hdiff)
          have := add_le_add_left hmul (Real.log (Real.Gamma (n : ℝ)))
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
            mul_assoc, mul_left_comm, mul_comm] using this
      have hn0' : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
      have hR_upper : R y ≤ R (n : ℝ) + 1 / (n : ℝ) := by
        have hy_pos : 0 < y := lt_of_lt_of_le hn_pos hn_le
        have hy_ne : y ≠ 0 := ne_of_gt hy_pos
        have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
        have hlog_ge :
            (y - (n : ℝ)) / y ≤ Real.log y - Real.log (n : ℝ) := by
          have hx_pos : 0 < y / (n : ℝ) := div_pos hy_pos hn_pos
          have h0 : 1 - (y / (n : ℝ))⁻¹ ≤ Real.log (y / (n : ℝ)) :=
            Real.one_sub_inv_le_log_of_pos (x := y / (n : ℝ)) hx_pos
          have hL : 1 - (y / (n : ℝ))⁻¹ = (y - (n : ℝ)) / y := by
            field_simp [hy_ne, hn_ne]
          have hR : Real.log (y / (n : ℝ)) = Real.log y - Real.log (n : ℝ) := by
            simpa using (Real.log_div (x := y) (y := (n : ℝ)) hy_ne hn_ne)
          have h0' : (y - (n : ℝ)) / y ≤ Real.log y - Real.log (n : ℝ) := by
            have h0'' : (y - (n : ℝ)) / y ≤ Real.log (y / (n : ℝ)) := by
              have htmp := h0
              rw [hL] at htmp
              exact htmp
            simpa [hR] using h0''
          exact h0'
        have hΔ :
            stirlingMainReal (n : ℝ) + (y - (n : ℝ)) * Real.log (n : ℝ) - stirlingMainReal y ≤
              1 / (n : ℝ) := by
          have hΔ_eq :
              stirlingMainReal (n : ℝ) + (y - (n : ℝ)) * Real.log (n : ℝ) - stirlingMainReal y =
                (y - (n : ℝ)) - (y - (1 / 2 : ℝ)) * (Real.log y - Real.log (n : ℝ)) := by
            unfold stirlingMainReal
            ring
          have hy1 : 0 ≤ y - (1 / 2 : ℝ) := by linarith [hy]
          have hΔ_le :
              (y - (n : ℝ)) - (y - (1 / 2 : ℝ)) * (Real.log y - Real.log (n : ℝ)) ≤
                (y - (n : ℝ)) - (y - (1 / 2 : ℝ)) * ((y - (n : ℝ)) / y) := by
            have hmul := mul_le_mul_of_nonneg_left hlog_ge hy1
            linarith
          have hΔ_simp :
              (y - (n : ℝ)) - (y - (1 / 2 : ℝ)) * ((y - (n : ℝ)) / y) =
                (y - (n : ℝ)) / (2 * y) := by
            field_simp [hy_ne]
            ring
          have hΔ_bound : (y - (n : ℝ)) / (2 * y) ≤ 1 / (n : ℝ) := by
            have h2y_pos : 0 < 2 * y := by nlinarith [hy_pos]
            have h2n_pos : 0 < 2 * (n : ℝ) := by nlinarith [hn_pos]
            have hstep1 :
                (y - (n : ℝ)) / (2 * y) ≤ 1 / (2 * y) := by
              refine div_le_div_of_nonneg_right ?_ (le_of_lt h2y_pos)
              linarith [ha_le]
            have hstep2 :
                (1 : ℝ) / (2 * y) ≤ 1 / (2 * (n : ℝ)) := by
              have hle : 2 * (n : ℝ) ≤ 2 * y := by nlinarith [hn_le]
              exact one_div_le_one_div_of_le h2n_pos hle
            have hstep3 :
                (1 : ℝ) / (2 * (n : ℝ)) ≤ 1 / (n : ℝ) := by
              have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
              have hnonneg : 0 ≤ (1 / (n : ℝ) : ℝ) := one_div_nonneg.2 (le_of_lt hn_pos)
              have hrew : (1 : ℝ) / (2 * (n : ℝ)) = (1 / (n : ℝ)) / 2 := by
                field_simp [hn0]
              have : (1 / (n : ℝ)) / 2 ≤ (1 / (n : ℝ)) :=
                div_le_self hnonneg (by norm_num : (1 : ℝ) ≤ 2)
              rw [hrew]
              exact this
            exact le_trans hstep1 (le_trans hstep2 hstep3)
          calc
            stirlingMainReal (n : ℝ) + (y - (n : ℝ)) * Real.log (n : ℝ) - stirlingMainReal y
                = (y - (n : ℝ)) - (y - (1 / 2 : ℝ)) * (Real.log y - Real.log (n : ℝ)) := hΔ_eq
            _ ≤ (y - (n : ℝ)) - (y - (1 / 2 : ℝ)) * ((y - (n : ℝ)) / y) := hΔ_le
            _ = (y - (n : ℝ)) / (2 * y) := hΔ_simp
            _ ≤ 1 / (n : ℝ) := hΔ_bound
        have : Real.log (Real.Gamma y) - stirlingMainReal y ≤
            (Real.log (Real.Gamma (n : ℝ)) - stirlingMainReal (n : ℝ)) + 1 / (n : ℝ) :=
          by linarith [h_upper, hΔ]
        simpa [R, sub_eq_add_neg, add_assoc] using this
      have hR_lower : R y ≥ R (n : ℝ) - 3 / (n : ℝ) := by
        -- Coarse  bound: use the convex lower bound on `log Γ` and very rough log estimates.
        have hy_pos : 0 < y := lt_of_lt_of_le hn_pos hn_le
        have hy_ne : y ≠ 0 := ne_of_gt hy_pos
        have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
        have hn2' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
        -- Upper bound for `log y` via `log (y/n) ≤ y/n - 1`.
        have hlogy_ub : Real.log y ≤ Real.log (n : ℝ) + (y - (n : ℝ)) / (n : ℝ) := by
          have hx_pos : 0 < y / (n : ℝ) := div_pos hy_pos hn_pos
          have hlog : Real.log (y / (n : ℝ)) ≤ y / (n : ℝ) - 1 :=
            Real.log_le_sub_one_of_pos (x := y / (n : ℝ)) hx_pos
          have hlog_div : Real.log (y / (n : ℝ)) = Real.log y - Real.log (n : ℝ) := by
            simpa using (Real.log_div (x := y) (y := (n : ℝ)) hy_ne hn_ne)
          have hrhs : y / (n : ℝ) - 1 = (y - (n : ℝ)) / (n : ℝ) := by
            field_simp [hn_ne]
          have : Real.log y - Real.log (n : ℝ) ≤ (y - (n : ℝ)) / (n : ℝ) := by
            simpa [hlog_div, hrhs] using hlog
          linarith
        -- Lower bound for `log(n-1)` in terms of `log n`.
        have hlognm1 :
            Real.log ((n - 1 : ℕ) : ℝ) ≥ Real.log (n : ℝ) - (2 : ℝ) / (n : ℝ) := by
          have hn_nat_pos : 0 < n := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hn2
          have hn1_pos_real : 0 < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hn1_pos
          have hn1_ne0 : ((n - 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hn1_pos_real
          have hlognm1' :
              Real.log ((n - 1 : ℕ) : ℝ) ≥
                Real.log (n : ℝ) - 1 / ((n - 1 : ℕ) : ℝ) := by
            have hx_pos : 0 < (n : ℝ) / ((n - 1 : ℕ) : ℝ) := div_pos hn_pos hn1_pos_real
            have hlog :
                Real.log ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) ≤
                  (n : ℝ) / ((n - 1 : ℕ) : ℝ) - 1 :=
              Real.log_le_sub_one_of_pos (x := (n : ℝ) / ((n - 1 : ℕ) : ℝ)) hx_pos
            have hlog' :
                Real.log ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) =
                  Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ) := by
              simpa using
                (Real.log_div (x := (n : ℝ)) (y := ((n - 1 : ℕ) : ℝ)) hn_ne hn1_ne0)
            have hrhs :
                (n : ℝ) / ((n - 1 : ℕ) : ℝ) - 1 = 1 / ((n - 1 : ℕ) : ℝ) := by
              field_simp [hn1_ne0]
              have hnat : (n - 1 : ℕ) + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn_nat_pos)
              have hcast : ((n : ℝ) : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
                exact_mod_cast hnat.symm
              linarith [hcast]
            have :
                Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ) ≤
                  1 / ((n - 1 : ℕ) : ℝ) := by
              have htmp := hlog
              rw [hlog'] at htmp
              rw [hrhs] at htmp
              exact htmp
            have h1 :
                Real.log (n : ℝ) ≤ Real.log ((n - 1 : ℕ) : ℝ) + 1 / ((n - 1 : ℕ) : ℝ) := by
              have h1' : Real.log (n : ℝ) ≤ 1 / ((n - 1 : ℕ) : ℝ) + Real.log ((n - 1 : ℕ) : ℝ) :=
                (sub_le_iff_le_add).1 this
              have h1'' := h1'
              rw [add_comm] at h1''
              exact h1''
            exact (sub_le_iff_le_add).2 h1
          have hfrac : (1 : ℝ) / ((n - 1 : ℕ) : ℝ) ≤ (2 : ℝ) / (n : ℝ) :=
            one_div_cast_sub_le_two_div_cast n hn2
          have hcomp :
              Real.log (n : ℝ) - (2 : ℝ) / (n : ℝ) ≤ Real.log (n : ℝ) - 1 / ((n - 1 : ℕ) : ℝ) := by
            exact sub_le_sub_left hfrac (Real.log (n : ℝ))
          exact le_trans hcomp hlognm1'
        have hy_le' : y ≤ (n : ℝ) + 1 := le_of_lt hy_lt
        have hy1 : 0 ≤ y - (1 / 2 : ℝ) := by
          have hN2_nat : (2 : ℕ) ≤ N := le_max_right (max N1 N2) 2
          have hN2 : (2 : ℝ) ≤ (N : ℝ) := by
            have h : ((2 : ℕ) : ℝ) ≤ (N : ℝ) := (Nat.cast_le (α := ℝ)).2 hN2_nat
            exact h
          have hy3 : (3 : ℝ) ≤ y := by
            have h3' : (2 : ℝ) + 1 ≤ (N : ℝ) + 1 := add_le_add_left hN2 1
            have h3 : (3 : ℝ) ≤ (N : ℝ) + 1 := by
              have h21 : (2 : ℝ) + 1 = 3 := by norm_num
              have h3'' := h3'
              rw [h21] at h3''
              exact h3''
            have hy' : (N : ℝ) + 1 ≤ y := hy
            exact le_trans h3 hy'
          have : (1 / 2 : ℝ) ≤ y := by
            have hhalf : (1 / 2 : ℝ) ≤ 3 := by norm_num
            exact le_trans hhalf hy3
          exact sub_nonneg.2 this
        have ha_nonneg : 0 ≤ y - (n : ℝ) := ha0
        have hlogGamma_lb :
            Real.log (Real.Gamma y) ≥
              Real.log (Real.Gamma (n : ℝ)) +
                (y - (n : ℝ)) * Real.log ((n - 1 : ℕ) : ℝ) := by
          exact h_lower
        have hmain :
            stirlingMainReal (n : ℝ) +
                (y - (n : ℝ)) * Real.log ((n - 1 : ℕ) : ℝ) - stirlingMainReal y ≥
              - (3 / (n : ℝ)) := by
          exact stirlingMainReal_floor_lower_step hn_pos hy1 ha_nonneg ha_le hlogy_ub hlognm1
        have : Real.log (Real.Gamma y) - stirlingMainReal y ≥
            (Real.log (Real.Gamma (n : ℝ)) - stirlingMainReal (n : ℝ)) -
              3 / (n : ℝ) := by
          linarith [hlogGamma_lb, hmain]
        simpa [R] using this
      have hR_abs : |R y| ≤ |R (n : ℝ)| + 3 / (n : ℝ) := by
        have hlower : -(|R (n : ℝ)| + 3 / (n : ℝ)) ≤ R y := by
          have h1 : R (n : ℝ) - 3 / (n : ℝ) ≤ R y := hR_lower
          have h2 : -|R (n : ℝ)| - 3 / (n : ℝ) ≤ R (n : ℝ) - 3 / (n : ℝ) :=
            sub_le_sub_right (neg_abs_le (R (n : ℝ))) (3 / (n : ℝ))
          have h3 : -|R (n : ℝ)| - 3 / (n : ℝ) ≤ R y := le_trans h2 h1
          have hneg :
              -(|R (n : ℝ)| + 3 / (n : ℝ)) = -|R (n : ℝ)| - 3 / (n : ℝ) := by
            ring
          simpa [hneg] using h3
        have hupper : R y ≤ |R (n : ℝ)| + 3 / (n : ℝ) := by
          have hn_pos' : 0 < (n : ℝ) := hn_pos
          have hRn : R (n : ℝ) ≤ |R (n : ℝ)| := le_abs_self _
          have hdiv : (1 : ℝ) / (n : ℝ) ≤ (3 : ℝ) / (n : ℝ) :=
            div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 3) (le_of_lt hn_pos')
          have hstep :
              R (n : ℝ) + (1 : ℝ) / (n : ℝ) ≤
                |R (n : ℝ)| + (3 : ℝ) / (n : ℝ) := by
            exact add_le_add hRn hdiv
          exact le_trans hR_upper hstep
        exact abs_le.2 ⟨hlower, hupper⟩
      have hRn_small : |R (n : ℝ)| < ε / 2 := by
        have hN1_le_N : N1 ≤ N := by
          exact le_trans (le_max_left N1 N2) (le_max_left (max N1 N2) 2)
        have hn_ge1 : N1 ≤ n := le_trans hN1_le_N hn_ge
        have hdist : dist (R (n : ℝ)) 0 < ε / 2 := hN1 n hn_ge1
        simpa [Real.dist_eq] using hdist
      have h3n_small : 3 / (n : ℝ) < ε / 2 := by
        have hN2_le_N : N2 ≤ N := by
          exact le_trans (le_max_right N1 N2) (le_max_left (max N1 N2) 2)
        have hn_ge2 : N2 ≤ n := le_trans hN2_le_N hn_ge
        have hdist : dist ((3 : ℝ) / (n : ℝ)) 0 < ε / 2 := hN2 n hn_ge2
        simpa [Real.dist_eq] using hdist
      have : |R y| < ε := by
        have hsum : |R (n : ℝ)| + 3 / (n : ℝ) < ε := by
          have : |R (n : ℝ)| + 3 / (n : ℝ) < ε / 2 + ε / 2 := add_lt_add hRn_small h3n_small
          simpa [add_halves] using this
        exact lt_of_le_of_lt hR_abs hsum
      simpa [Real.dist_eq, abs_sub_comm] using this
    have hJlim : Tendsto (fun y : ℝ => (Binet.J (y : ℂ)).re) atTop (𝓝 0) :=
      tendsto_re_J_atTop_zero
    have hlim : Tendsto h atTop (𝓝 0) := by
      simpa [h, sub_eq_add_neg] using hRlim.add (hJlim.neg)
    have hx0' : h x = 0 := eq_zero_of_tendsto_atTop_periodic_add_one hx h_periodic hlim
    dsimp [h] at hx0'
    linarith
  have hmain : Real.log (Real.Gamma x) = stirlingMainReal x + (Binet.J (x : ℂ)).re := by
    have hR' : R x + stirlingMainReal x = (Binet.J (x : ℂ)).re + stirlingMainReal x :=
      congrArg (fun r : ℝ => r + stirlingMainReal x) hR
    have hlog : Real.log (Real.Gamma x) = (Binet.J (x : ℂ)).re + stirlingMainReal x := by
      have hR'' := hR'
      dsimp [R] at hR''
      rw [sub_add_cancel] at hR''
      exact hR''
    have hlog' := hlog
    rw [add_comm] at hlog'
    exact hlog'
  have hmain' := hmain
  dsimp [stirlingMainReal] at hmain'
  exact hmain'

end Binet
