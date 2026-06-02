/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.MetricSpace.Basic

/-!
# Abel-summation continuation of the Riemann zeta function

For `s ≠ 1` in the half-plane `{re s > σ₀}` with `σ₀ = 1/10`, the Riemann zeta function equals the
Abel-summation tail formula from [`Mathlib.NumberTheory.AbelSummation`]: writing `{u}` for the
fractional part of `u > 0` and `K_s(u) = {u} · u^{-s-1}`, one has

`ζ(s) = 1 + (s - 1)⁻¹ - s ∫_{(1,∞)} K_s(u) du`.

The threshold `σ₀`, the domain, the kernel, and the renormalized integral are bundled in
`zetaAbelContinuationReLower`, `zetaAbelContinuationDomain`, `zetaAbelFractKernel`, and
`zetaAbelContinuationFormula`. The equality with `riemannZeta` on that domain is proved by analytic
continuation from `re s > 1`, where the formula is the classical Abel partial-sum limit.

Used in `RiemannZetaConvexity` for strip bounds and in the finite-order pipeline.

## Main results

* `zetaAbelFractKernel`, `zetaAbelContinuationFormula` : fractional-part kernel and Abel formula
* `zetaAbelContinuationDomain` : domain `{s ≠ 1 ∧ re s > 1/10}` of the continuation theorem
* `riemannZeta_eq_zetaAbelContinuationFormula` : identification with `riemannZeta`
* `norm_zetaAbelContinuationFormula_le`, `norm_zetaAbelFractKernel_le` : strip and kernel bounds
* `analyticOn_zetaAbelContinuationFormula` : analyticity of the Abel formula on the domain

## Tags

Riemann zeta function, Abel summation, fractional part
-/

@[expose] public section

open scoped BigOperators Topology

open Real Set Filter Topology MeasureTheory Complex

/-- Lower threshold on `re s` for the Abel integral continuation of `ζ`. -/
noncomputable def zetaAbelContinuationReLower : ℝ := 1 / 10

theorem zetaAbelContinuationReLower_pos : 0 < zetaAbelContinuationReLower := by
  norm_num [zetaAbelContinuationReLower]

theorem one_lt_zetaAbelContinuationReLower : zetaAbelContinuationReLower < (1 : ℝ) := by
  norm_num [zetaAbelContinuationReLower]

theorem one_sub_zetaAbelContinuationReLower :
    (1 - zetaAbelContinuationReLower : ℝ) = 9 / 10 := by
  norm_num [zetaAbelContinuationReLower]

theorem zetaAbelContinuationReLower_lt_half : zetaAbelContinuationReLower < (2⁻¹ : ℝ) := by
  norm_num [zetaAbelContinuationReLower]

/-- Domain `{s : ℂ | s ≠ 1 ∧ re s > 1/10}` where the Abel continuation of `ζ` is proved. -/
def zetaAbelContinuationDomain : Set ℂ :=
  {s | s ≠ (1 : ℂ) ∧ zetaAbelContinuationReLower < s.re}

theorem isOpen_zetaAbelContinuationDomain : IsOpen zetaAbelContinuationDomain := by
  change IsOpen ({s : ℂ | s ≠ 1} ∩ {s : ℂ | zetaAbelContinuationReLower < s.re})
  exact isOpen_compl_singleton.inter (isOpen_lt continuous_const Complex.continuous_re)

theorem isPreconnected_zetaAbelContinuationDomain :
    IsPreconnected zetaAbelContinuationDomain := by
  convert (Complex.isPathConnected_halfSpace_re_gt_diff_singleton
      (a := zetaAbelContinuationReLower) (p := (1 : ℂ)) one_lt_zetaAbelContinuationReLower).isConnected.isPreconnected
    using 1
  ext z; simp [zetaAbelContinuationDomain, Set.mem_diff, Set.mem_singleton_iff, and_comm]

theorem two_mem_zetaAbelContinuationDomain : (2 : ℂ) ∈ zetaAbelContinuationDomain := by
  norm_num [zetaAbelContinuationDomain, zetaAbelContinuationReLower]

theorem zetaAbelContinuationDomain_re_pos {s : ℂ} (hs : s ∈ zetaAbelContinuationDomain) :
    0 < s.re := lt_trans zetaAbelContinuationReLower_pos hs.2

theorem mem_zetaAbelContinuationDomain_of_re {s : ℂ} (hs_ne : s ≠ 1)
    (hs_re : zetaAbelContinuationReLower < s.re) : s ∈ zetaAbelContinuationDomain :=
  ⟨hs_ne, hs_re⟩

/-- On `zetaAbelContinuationDomain`, `‖z‖ / re z ≤ 10 * ‖z‖`. -/
theorem norm_div_re_le_ten_mul_norm_of_mem {z : ℂ} (hz : z ∈ zetaAbelContinuationDomain) :
    ‖z‖ / z.re ≤ 10 * ‖z‖ := by
  calc
    ‖z‖ / z.re = ‖z‖ * (1 / z.re) := by rw [div_eq_mul_inv, one_div]
    _ ≤ ‖z‖ * 10 := mul_le_mul_of_nonneg_left
        (by
          simpa [zetaAbelContinuationReLower] using
            one_div_le_one_div_of_le zetaAbelContinuationReLower_pos (le_of_lt hz.2))
        (norm_nonneg z)
    _ = 10 * ‖z‖ := by rw [mul_comm]

/-- Fractional-part kernel `{u} · u^{-s-1}` (`K_s` in the module doc). -/
noncomputable def zetaAbelFractKernel (s : ℂ) (u : ℝ) : ℂ :=
  ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)

/-- Abel renormalization `1 + (s-1)⁻¹ - s ∫_{(1,∞)} K_s`. -/
noncomputable def zetaAbelContinuationFormula (s : ℂ) : ℂ :=
  1 + 1 / (s - 1) - s * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u

/-- `{u} · u^{-s-1}` is dominated by `u^{- re s - 1}` for `u ≥ 1`. -/
theorem norm_zetaAbelFractKernel_le (u : ℝ) (hu : 1 ≤ u) (s : ℂ) :
    ‖zetaAbelFractKernel s u‖ ≤ u ^ (-s.re - 1) := by
  set a : ℂ := ((Int.fract u : ℝ) : ℂ)
  set b : ℂ := (u : ℂ) ^ (-s - 1)
  have hfract_le1 : ‖a‖ ≤ 1 := by simpa [a, Complex.norm_real] using Int.fract_abs_le_one u
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hle : ‖a * b‖ ≤ ‖b‖ := by
    calc
      ‖a * b‖ = ‖a‖ * ‖b‖ := by simp [a, b]
      _ ≤ 1 * ‖b‖ := mul_le_mul_of_nonneg_right hfract_le1 (norm_nonneg _)
      _ = ‖b‖ := one_mul _
  have hb : ‖b‖ = u ^ (-s.re - 1) := by
    have := Complex.norm_cpow_eq_rpow_re_of_pos (x := u) (hx := hu0) (y := -s - 1)
    simp [b, sub_eq_add_neg] at this ⊢
    exact this
  calc
    ‖zetaAbelFractKernel s u‖ = ‖a * b‖ := by simp [zetaAbelFractKernel, a, b]
    _ ≤ ‖b‖ := hle
    _ = u ^ (-s.re - 1) := hb

/-- Partial sum of the Dirichlet series defining `ζ` for `re s > 1`. -/
private noncomputable def zetaPartialSum (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, (n + 1 : ℂ) ^ (-s)

private theorem continuousOn_ofReal_cpow {r : ℂ} {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun u : ℝ => (u : ℂ) ^ r) (Set.Icc a b) :=
  (Complex.continuous_ofReal.continuousOn.cpow continuousOn_const
    (fun _ hu => (Complex.ofReal_mem_slitPlane).2 (lt_of_lt_of_le ha hu.1))).mono
    Set.Subset.rfl

private lemma differentiable_integrable_cpow_on_Icc (s : ℂ) (a b : ℝ) (h0 : 0 < a) (hle : a ≤ b) :
  (∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (fun u : ℝ => (u : ℂ) ^ (-s)) t)
  ∧ IntegrableOn (deriv (fun u : ℝ => (u : ℂ) ^ (-s))) (Set.Icc a b) := by
  classical
  set f : ℝ → ℂ := fun u => (u : ℂ) ^ (-s)
  set g : ℝ → ℂ := fun u => -s * (u : ℂ) ^ (-s - 1)
  have hpos_of_mem : ∀ {t : ℝ}, t ∈ Set.Icc a b → 0 < t := by
    intro t ht
    exact lt_of_lt_of_le h0 ht.1
  have hdiff_at : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t := by
    intro t ht
    have ht_ne : t ≠ 0 := ne_of_gt (hpos_of_mem ht)
    by_cases hs : s = 0
    · simp [f, hs]
    · exact (hasDerivAt_ofReal_cpow_const (x := t) (hx := ht_ne) (r := -s)
        (hr := neg_ne_zero.mpr hs)).differentiableAt
  have hcont_pow : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (-s - 1)) (Set.Icc a b) :=
    continuousOn_ofReal_cpow (r := -s - 1) (ha := h0)
  have hcont_g : ContinuousOn g (Set.Icc a b) := by
    have hmul :=
      (continuousOn_const : ContinuousOn (fun _ : ℝ => (-s : ℂ)) (Set.Icc a b)).mul hcont_pow
    exact hmul.congr (by intro u _; simp [g, neg_mul])
  have hEqOn : EqOn (deriv f) g (Set.Icc a b) := by
    intro u hu
    by_cases hs : s = 0
    · simp [f, g, hs, deriv_const]
    · simpa [f, g] using
        Complex.deriv_ofReal_cpow_const (ne_of_gt (hpos_of_mem hu)) (neg_ne_zero.mpr hs)
  have hcont_deriv : ContinuousOn (deriv f) (Set.Icc a b) := by
    have hg_restr : Continuous ((Set.Icc a b).restrict g) := hcont_g.restrict
    have hEqRestr : (Set.Icc a b).restrict (deriv f) = (Set.Icc a b).restrict g := by
      funext x; exact hEqOn x.property
    have hderiv_restr : Continuous ((Set.Icc a b).restrict (deriv f)) := by
      simpa [hEqRestr] using hg_restr
    simpa [continuousOn_iff_continuous_restrict] using hderiv_restr
  exact ⟨hdiff_at, hcont_deriv.integrableOn_compact isCompact_Icc⟩

/-- Apply Abel's summation to the zeta partial sum. -/
private lemma zetaPartialSum_abel_summation (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N
      = (N : ℂ) * (N : ℂ) ^ (-s)
        - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
  classical
  set f : ℝ → ℂ := fun u => (u : ℂ) ^ (-s)
  let c : ℕ → ℂ := fun k => if k = 0 then 0 else (1 : ℂ)
  have hle : (1 : ℝ) ≤ (N : ℝ) := mod_cast hN
  obtain ⟨hdiff, hint⟩ :=
    differentiable_integrable_cpow_on_Icc (s := s) (a := (1 : ℝ)) (b := (N : ℝ)) zero_lt_one hle
  have habel :=
    sum_mul_eq_sub_integral_mul₀' (c := c) (f := f) (m := N)
      (hc := by simp [c])
      (hf_diff := fun t ht => hdiff t ht)
      (hf_int := hint)
  have hLHS : (∑ k ∈ Finset.Icc 0 N, f k * c k) = zetaPartialSum s N := by
    rw [Finset.sum_Icc_zero_eq_sum_range_succ (m := N) (f := fun k => f k * c k) (by simp [c])]
    simp [zetaPartialSum, f, c, Nat.succ_ne_zero]
  have hset_to_interval :
      (∫ t in Set.Ioc (1 : ℝ) N, deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k)
        = ∫ u in (1 : ℝ)..N, deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k :=
    (intervalIntegral.integral_of_le
      (f := fun u => deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k) (μ := volume) hle).symm
  have hInt_congr :
      (∫ u in (1 : ℝ)..N, deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k)
        = ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
    apply intervalIntegral.integral_congr_Ioc_of_le (a := (1 : ℝ)) (b := (N : ℝ)) (hab := hle)
      (f := fun u => deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k)
      (g := fun u => (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)))
    intro u hu
    have hderiv : deriv f u = -s * (u : ℂ) ^ (-s - 1) := by
      by_cases hs : s = 0
      · simp [f, hs]
      · simpa [f] using
          Complex.deriv_ofReal_cpow_const (ne_of_gt (lt_trans zero_lt_one hu.1))
            (neg_ne_zero.mpr hs)
    rw [sum_Icc_zero_floor_eq_sum_range (hc0 := by simp [c]) u, hderiv]
    simp [c, Finset.sum_const, Finset.card_range, mul_comm, mul_left_comm, mul_assoc]
  have hMain : f N * (∑ k ∈ Finset.Icc 0 N, c k) = (N : ℂ) * f N := by
    rw [Finset.sum_Icc_zero_eq_sum_range_succ (m := N) (f := c) (by simp [c])]
    simp [c, Finset.sum_const, Finset.card_range, mul_comm]
  calc
    zetaPartialSum s N
        = f N * (∑ k ∈ Finset.Icc 0 N, c k)
            - ∫ t in Set.Ioc (1 : ℝ) N, deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k := by
          simpa [hLHS] using habel
    _ = f N * (∑ k ∈ Finset.Icc 0 N, c k)
            - ∫ u in (1 : ℝ)..N, deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k := by
          rw [hset_to_interval]
    _ = f N * (∑ k ∈ Finset.Icc 0 N, c k)
            - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
          rw [hInt_congr]
    _ = (N : ℂ) * (N : ℂ) ^ (-s)
            - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
          rw [hMain]; simp [f, Nat.cast_id]

/-- Simplified partial-sum formula after Abel summation. -/
private lemma zetaPartialSum_abel_split (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N = (N : ℂ) ^ (1 - s) + s * ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1) := by
  have happly := zetaPartialSum_abel_summation s N hN
  -- Pull out the constant -s from the integral
  have hInt :
      ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1))
        = (-s) * ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1) := by
    have hInt' :
        ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1))
          = ∫ u in (1 : ℝ)..N, (-s) * ((Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1)) := by
      refine intervalIntegral.integral_congr_Ioc_of_le (a := (1 : ℝ)) (b := (N : ℝ)) (hab := by exact_mod_cast hN)
        (f := fun u => (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)))
        (g := fun u => (-s) * ((Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1))) ?_
      intro u hu
      simp [neg_mul, mul_comm, mul_left_comm, mul_assoc]
    rw [hInt']
    exact intervalIntegral.integral_const_mul (-s) (fun u => (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1))
  calc
    zetaPartialSum s N
        = (N : ℂ) * (N : ℂ) ^ (-s)
          - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
          simpa using happly
    _ = (N : ℂ) * (N : ℂ) ^ (-s)
          - ((-s) * ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1)) := by
          rw [hInt]
    _ = (N : ℂ) * (N : ℂ) ^ (-s)
          + s * ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1) := by
          simp [sub_eq_add_neg, neg_mul, mul_comm, mul_left_comm, mul_assoc]
    _ = (N : ℂ) ^ (1 - s)
          + s * ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1) := by
          have hpos : 0 < N := (Nat.succ_le_iff).mp hN
          have hNz : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hpos)
          have hpow : (N : ℂ) * (N : ℂ) ^ (-s) = (N : ℂ) ^ (1 - s) := by
            calc
              (N : ℂ) * (N : ℂ) ^ (-s) = (N : ℂ) ^ (1 : ℂ) * (N : ℂ) ^ (-s) := by
                simp [Complex.cpow_one]
              _ = (N : ℂ) ^ (1 + (-s)) := by
                simpa using (Complex.cpow_add (x := (N : ℂ)) (y := (1 : ℂ)) (z := (-s)) hNz).symm
              _ = (N : ℂ) ^ (1 - s) := by simp [sub_eq_add_neg]
          simp [hpow]

private lemma intervalIntegrable_mul_cpow_id (s : ℂ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) volume a b := by
  have hcont1 : ContinuousOn (fun u : ℝ => (u : ℂ)) (Set.Icc a b) :=
    Complex.continuous_ofReal.continuousOn
  have hcont2 : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (-s - 1)) (Set.Icc a b) :=
    continuousOn_ofReal_cpow (ha := lt_of_lt_of_le zero_lt_one ha)
  have hcont : ContinuousOn (fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) (Set.Icc a b) :=
    hcont1.mul hcont2
  have hint_on : IntegrableOn (fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) (Set.Icc a b) :=
    hcont.integrableOn_compact isCompact_Icc
  simpa using
    (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := volume) (a := a) (b := b)
      (f := fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) hab).2 hint_on

private lemma zetaAbelFractKernel_intervalIntegrable (s : ℂ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u => zetaAbelFractKernel s u) volume a b := by
  classical
  let μ := volume.restrict (Icc a b)
  set g : ℝ → ℝ := fun u => ‖(u : ℂ) ^ (-s - 1)‖
  have hmeas : AEStronglyMeasurable (fun u => zetaAbelFractKernel s u) μ := by
    refine (measurable_fract.complex_ofReal.mul ?_).aestronglyMeasurable
    simpa using Complex.measurable_ofReal.pow_const (-s - 1)
  have hbound_ae : ∀ᵐ u ∂μ, ‖zetaAbelFractKernel s u‖ ≤ g u := by
    refine ((ae_restrict_iff' (μ := volume) (s := Icc a b)
      (p := fun u => ‖zetaAbelFractKernel s u‖ ≤ g u) measurableSet_Icc)).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro u huIcc
    have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one (ha.trans huIcc.1)
    have hg_eq : u ^ (-s.re - 1) = g u := by
      simp [g, Complex.norm_cpow_eq_rpow_re_of_pos hu0, sub_eq_add_neg]
    exact (norm_zetaAbelFractKernel_le u (ha.trans huIcc.1) s).trans (le_of_eq hg_eq)
  have hg : Integrable g μ := by
    simpa [μ, g] using
      (continuousOn_ofReal_cpow (ha := lt_of_lt_of_le zero_lt_one ha)).norm.integrableOn_compact
        isCompact_Icc
  have hf0 : Integrable (fun _ : ℝ => (0 : ℂ)) μ := by simp [μ]
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 <|
    MeasureTheory.integrable_of_norm_sub_le hmeas hf0 hg
      (by simpa [sub_eq_add_neg, norm_neg, μ, g] using hbound_ae)

/-- Split `⌊u⌋ · u^{-s-1}` into the main term and the fractional-part kernel integral. -/
private lemma zetaPartialSum_integral_split_fract (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1)
      = (∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s))
        - ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u := by
  have hab : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hcongr1 :
      (∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1))
        = ∫ u in (1 : ℝ)..N,
            ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 1) := by
    apply intervalIntegral.integral_congr_Ioc_of_le (a := (1 : ℝ)) (b := (N : ℝ)) (hab := hab)
    intro u hu
    have hu0 : 0 ≤ u := le_trans (by norm_num) (le_of_lt hu.1)
    have hfloorR : (Nat.floor u : ℝ) = (Int.floor u : ℝ) := by
      simpa using (natCast_floor_eq_intCast_floor (R := ℝ) (a := u) hu0)
    have hfloorC : (Nat.floor u : ℂ) = ((Int.floor u : ℝ) : ℂ) := by
      simpa using congrArg (fun x : ℝ => (x : ℂ)) hfloorR
    have hIFR : (Int.floor u : ℝ) = u - Int.fract u := (eq_sub_iff_add_eq).2 (Int.floor_add_fract u)
    have hIFC : ((Int.floor u : ℝ) : ℂ) = ((u - Int.fract u : ℝ) : ℂ) :=
      congrArg (fun x : ℝ => (x : ℂ)) hIFR
    have : (Nat.floor u : ℂ) = ((u - Int.fract u : ℝ) : ℂ) := hfloorC.trans hIFC
    simp [this, Complex.ofReal_sub, sub_eq_add_neg]
  have hcongr2 :
      (∫ u in (1 : ℝ)..N,
          ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 1))
        = (∫ u in (1 : ℝ)..N, (u : ℂ) * (u : ℂ) ^ (-s - 1))
          - ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u := by
    have hI1 : IntervalIntegrable (fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) volume (1 : ℝ) (N : ℝ) :=
      intervalIntegrable_mul_cpow_id (s := s) (a := (1 : ℝ)) (b := (N : ℝ)) (ha := le_rfl) (hab := hab)
    have hI2 : IntervalIntegrable (fun u => zetaAbelFractKernel s u) volume (1 : ℝ) (N : ℝ) :=
      zetaAbelFractKernel_intervalIntegrable (s := s) (a := (1 : ℝ)) (b := (N : ℝ)) (ha := le_rfl) (hab := hab)
    have :
        (∫ u in (1 : ℝ)..N,
            ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 1))
          = ∫ u in (1 : ℝ)..N,
              ((u : ℂ) * (u : ℂ) ^ (-s - 1) - zetaAbelFractKernel s u) := by
      apply intervalIntegral.integral_congr_Ioc_of_le (a := (1 : ℝ)) (b := (N : ℝ)) (hab := hab)
      intro u hu; simp [sub_mul, zetaAbelFractKernel]
    calc
      (∫ u in (1 : ℝ)..N,
          ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 1))
          = ∫ u in (1 : ℝ)..N,
              ((u : ℂ) * (u : ℂ) ^ (-s - 1) - zetaAbelFractKernel s u) := this
      _ = (∫ u in (1 : ℝ)..N, (u : ℂ) * (u : ℂ) ^ (-s - 1))
            - ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u :=
        intervalIntegral.integral_sub (μ := volume) (a := (1 : ℝ)) (b := (N : ℝ)) hI1 hI2
  have hpow :
      (∫ u in (1 : ℝ)..N, (u : ℂ) * (u : ℂ) ^ (-s - 1))
        = ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s) := by
    apply intervalIntegral.integral_congr_Ioc_of_le (a := (1 : ℝ)) (b := (N : ℝ)) (hab := hab)
    intro u hu
    have hu_pos : 0 < u := lt_trans zero_lt_one hu.1
    have hux0 : (u : ℝ) ≠ 0 := ne_of_gt hu_pos
    have hcx0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hux0
    calc
      (u : ℂ) * (u : ℂ) ^ (-s - 1)
          = (u : ℂ) ^ (1 : ℂ) * (u : ℂ) ^ (-s - 1) := by simp [Complex.cpow_one]
      _ = (u : ℂ) ^ (1 + (-s - 1)) := by
        simpa using
          (Complex.cpow_add (x := (u : ℂ)) (y := (1 : ℂ)) (z := (-s - 1)) hcx0).symm
      _ = (u : ℂ) ^ (-s) := by
        simp [add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
  calc
    ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1)
        = ∫ u in (1 : ℝ)..N,
            ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 1) := hcongr1
    _ = (∫ u in (1 : ℝ)..N, (u : ℂ) * (u : ℂ) ^ (-s - 1))
          - ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u := hcongr2
    _ = (∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s))
          - ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u := by
      simp [hpow]

/-- Lemma: Simplified `ζ_N` formula 2. -/
private lemma zetaPartialSum_abel_sub_fract (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N
      = (N : ℂ) ^ (1 - s)
        + (s * ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s))
        - (s * ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u) := by
  have hstep1 := zetaPartialSum_abel_split s N hN
  rw [zetaPartialSum_integral_split_fract s N hN] at hstep1
  rw [mul_sub] at hstep1
  simpa [add_sub_assoc] using hstep1

/-- Lemma: Evaluate the main integral. -/
private lemma zetaPartialSum_cpow_integral (s : ℂ) (hs : s ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    s * ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s) = s / (1 - s) * ((N : ℂ) ^ (1 - s) - 1) := by
  have h01leN : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h0notIcc : (0 : ℝ) ∉ Set.Icc (1 : ℝ) (N : ℝ) := by
    intro hx
    exact (not_le.mpr (by norm_num : (0 : ℝ) < 1)) hx.1
  have h0not : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (N : ℝ) := by
    simp [uIcc_of_le h01leN]
  have hrne : -s ≠ (-1 : ℂ) := by
    intro h
    apply hs
    simpa using congrArg Neg.neg h
  have hint : ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s)
      = ((N : ℂ) ^ ((-s) + 1) - (1 : ℂ) ^ ((-s) + 1)) / ((-s) + 1) := by
    have hcond : (-1 < (-s).re) ∨ (-s ≠ -1 ∧ (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (N : ℝ)) := by
      exact Or.inr ⟨hrne, h0not⟩
    simpa using (integral_cpow (a := (1 : ℝ)) (b := (N : ℝ)) (r := -s) hcond)
  have hmul : s * ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s)
      = s * (((N : ℂ) ^ ((-s) + 1) - (1 : ℂ) ^ ((-s) + 1)) / ((-s) + 1)) := by
    simpa using congrArg (fun x => s * x) hint
  have hrewrite :
      s * (((N : ℂ) ^ ((-s) + 1) - (1 : ℂ) ^ ((-s) + 1)) / ((-s) + 1))
        = s * (((N : ℂ) ^ (1 - s) - 1) / (1 - s)) := by
    have : s * (((N : ℂ) ^ ((-s) + 1) - (1 : ℂ) ^ ((-s) + 1)) / ((-s) + 1))
          = s * (((N : ℂ) ^ (1 - s) - (1 : ℂ) ^ (1 - s)) / (1 - s)) := by
      simp [add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
    have h1pow : (1 : ℂ) ^ (1 - s) = 1 := by simp
    simpa [h1pow] using this
  have hsplit : s * (((N : ℂ) ^ (1 - s) - 1) / (1 - s))
      = s / (1 - s) * ((N : ℂ) ^ (1 - s) - 1) := by
    have h1 : s * (((N : ℂ) ^ (1 - s) - 1) / (1 - s))
        = (s * ((N : ℂ) ^ (1 - s) - 1)) / (1 - s) := by
      simpa using (mul_div_assoc s ((N : ℂ) ^ (1 - s) - 1) (1 - s)).symm
    have h2 : (s * ((N : ℂ) ^ (1 - s) - 1)) / (1 - s)
        = (s / (1 - s)) * ((N : ℂ) ^ (1 - s) - 1) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (div_mul_eq_mul_div (a := s) (b := (1 - s)) (c := ((N : ℂ) ^ (1 - s) - 1))).symm
    exact h1.trans h2
  calc
    s * ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s)
        = s * (((N : ℂ) ^ ((-s) + 1) - (1 : ℂ) ^ ((-s) + 1)) / ((-s) + 1)) := hmul
    _ = s * (((N : ℂ) ^ (1 - s) - 1) / (1 - s)) := hrewrite
    _ = s / (1 - s) * ((N : ℂ) ^ (1 - s) - 1) := hsplit

/-- Abel tail formula for `re s > 1`. -/
private lemma zetaPartialSum_abel_formula (s : ℂ) (hs : s ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N
      = (N : ℂ) ^ (1 - s) / (1 - s) + 1 + 1 / (s - 1)
        - s * ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u := by
  have hstep := zetaPartialSum_abel_sub_fract s N hN
  rw [zetaPartialSum_cpow_integral s hs N hN] at hstep
  have hden : (1 - s) ≠ 0 := by
    intro h
    have h1 : 1 = s := by simpa [sub_eq_zero] using h
    have h2 : s = 1 := h1.symm
    exact hs h2
  let A := (N : ℂ) ^ (1 - s)
  have h1 : (1 - s) * (A + s / (1 - s) * (A - 1)) = A - s := by
    calc
      (1 - s) * (A + s / (1 - s) * (A - 1))
          = (1 - s) * A + (1 - s) * (s / (1 - s) * (A - 1)) := by ring
      _ = (1 - s) * A + s * (A - 1) := by field_simp [hden]
      _ = A - s := by ring
  have h2 : (1 - s) * (A / (1 - s) + 1 + 1 / (s - 1)) = A - s := by
    have hne : s - 1 ≠ 0 := by simpa [sub_eq_zero] using hs
    field_simp [hden, hne]; ring
  have halg : A + s / (1 - s) * (A - 1) = A / (1 - s) + 1 + 1 / (s - 1) :=
    mul_left_cancel₀ hden (h1.trans h2.symm)
  rw [halg] at hstep
  exact hstep

private lemma tendsto_natCast_cpow_zero_of_neg_re (w : ℂ) (hw : w.re < 0) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ w) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : (fun N : ℕ => (N : ℝ) ^ w.re) =ᶠ[atTop] fun N : ℕ => ‖(N : ℂ) ^ w‖ := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [Complex.norm_natCast_cpow_of_pos hN w]
  rw [tendsto_congr' (EventuallyEq.symm h1)]
  have hw_pos : 0 < -w.re := neg_pos.mpr hw
  have h_eq : w.re = -(-w.re) := by ring
  rw [h_eq]
  exact (tendsto_rpow_neg_atTop hw_pos).comp tendsto_natCast_atTop_atTop

private lemma tendsto_nat_rpow_neg (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ (-ε)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop hε).comp tendsto_natCast_atTop_atTop

private lemma intervalIntegrable_rpow_neg {ε : ℝ} {a b : ℝ} (hε : 0 < ε) (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => u ^ (-1 - ε)) volume a b := by
  have h0notIcc : (0 : ℝ) ∉ Set.Icc a b := by
    intro hx
    exact (not_le.mpr (lt_of_lt_of_le zero_lt_one ha)) hx.1
  have h0not : (0 : ℝ) ∉ Set.uIcc a b := by simpa [uIcc_of_le hab] using h0notIcc
  exact intervalIntegral.intervalIntegrable_rpow (μ := volume) (a := a) (b := b) (r := -1 - ε)
    (Or.inr h0not)

private lemma integrableOn_rpow_neg_Ioc {ε : ℝ} (hε : 0 < ε) {m n : ℝ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    IntegrableOn (fun u : ℝ => u ^ (-1 - ε)) (Ioc m n) volume :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le (f := fun u => u ^ (-1 - ε)) hmn).1
    (intervalIntegrable_rpow_neg hε hm hmn)

private lemma aestronglyMeasurable_zetaAbelFractKernel_Ioc (s : ℂ) {m n : ℝ} :
    AEStronglyMeasurable (fun u => zetaAbelFractKernel s u) (volume.restrict (Ioc m n)) := by
  refine (measurable_fract.complex_ofReal.mul ?_).aestronglyMeasurable
  simpa using Complex.measurable_ofReal.pow_const (-s - 1)

private lemma ae_bound_zetaAbelFractKernel_Ioc {ε : ℝ} (_hε : 0 < ε) (s : ℂ) (hs : ε ≤ s.re)
    {m n : ℝ} (hm : 1 ≤ m) :
    ∀ᵐ u ∂(volume.restrict (Ioc m n)), ‖zetaAbelFractKernel s u‖ ≤ u ^ (-1 - ε) := by
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall ?_)
  intro u hu
  have hu1 : 1 ≤ u := hm.trans (le_of_lt hu.1)
  calc
    ‖zetaAbelFractKernel s u‖ ≤ u ^ (-s.re - 1) := norm_zetaAbelFractKernel_le u hu1 s
    _ ≤ u ^ (-1 - ε) := Real.rpow_le_rpow_of_exponent_le hu1 (by linarith [hs])

private lemma zetaAbelFractKernel_intervalIntegrable_Ioc (ε : ℝ) (hε : 0 < ε) (s : ℂ) (hs : ε ≤ s.re)
    {m n : ℝ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    IntervalIntegrable (fun u => zetaAbelFractKernel s u) volume m n := by
  set gR : ℝ → ℝ := fun u => u ^ (-1 - ε)
  have hintOn : IntegrableOn (fun u => zetaAbelFractKernel s u) (Ioc m n) volume :=
    IntegrableOn.mono' (integrableOn_rpow_neg_Ioc hε hm hmn)
      (aestronglyMeasurable_zetaAbelFractKernel_Ioc s)
      (ae_bound_zetaAbelFractKernel_Ioc hε s hs hm)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (f := fun u => zetaAbelFractKernel s u) hmn).2
    hintOn

private lemma zetaAbelFractKernel_norm_integral_le_Ioc (ε : ℝ) (hε : 0 < ε) (s : ℂ) (hs : ε ≤ s.re)
    {m n : ℝ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    ‖∫ u in m..n, zetaAbelFractKernel s u‖ ≤ ∫ u in m..n, u ^ (-1 - ε) := by
  exact intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := m) (b := n)
    (f := fun u => zetaAbelFractKernel s u) (g := fun u => u ^ (-1 - ε)) (hab := hmn)
    ((ae_restrict_iff' (μ := volume) (s := Ioc m n) measurableSet_Ioc).1
      (ae_bound_zetaAbelFractKernel_Ioc hε s hs hm))
    (intervalIntegrable_rpow_neg hε hm hmn)

private lemma zetaAbelFractKernel_integral_convergence (ε : ℝ) (hε : 0 < ε) (s : ℂ) (hs : ε ≤ s.re) :
    ∃ I : ℂ,
      Tendsto (fun N : ℕ => ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u) atTop (𝓝 I)
      ∧ ‖I‖ ≤ (1 / ε) := by
  classical
  let a : ℕ → ℂ := fun N => ∫ u in (1 : ℝ)..(N : ℝ), zetaAbelFractKernel s u
  let b : ℕ → ℝ := fun m => (1 / ε) * (m : ℝ) ^ (-ε)
  have hb_nonneg : ∀ m, 0 ≤ b m := fun m => by simp [b]; positivity
  have hb_tendsto : Tendsto b atTop (𝓝 0) := by
    convert (Tendsto.const_mul (1 / ε) (tendsto_nat_rpow_neg ε hε)) using 1
    ext m; simp [b]
  have h_tail_pointwise : ∀ m n : ℕ, 1 ≤ m → m ≤ n → ‖a n - a m‖ ≤ b m := by
    intro m n hm1 hmn
    have hmR : (1 : ℝ) ≤ (m : ℝ) := mod_cast hm1
    have hmnR : (m : ℝ) ≤ (n : ℝ) := mod_cast hmn
    have hInt_f_1n := zetaAbelFractKernel_intervalIntegrable_Ioc ε hε s hs (m := (1 : ℝ)) (n := (n : ℝ))
      (hm := le_rfl) (hmn := mod_cast (le_trans hm1 hmn))
    have hInt_f_1m := zetaAbelFractKernel_intervalIntegrable_Ioc ε hε s hs (m := (1 : ℝ)) (n := (m : ℝ))
      (hm := le_rfl) (hmn := hmR)
    have hsub : a n - a m = ∫ u in (m : ℝ)..(n : ℝ), zetaAbelFractKernel s u := by
      simpa [a] using
        intervalIntegral.integral_interval_sub_left (μ := volume)
          (f := fun u => zetaAbelFractKernel s u) (a := (1 : ℝ)) (b := (n : ℝ)) (c := (m : ℝ))
          hInt_f_1n hInt_f_1m
    have h1 := zetaAbelFractKernel_norm_integral_le_Ioc ε hε s hs (m := (m : ℝ)) (n := (n : ℝ)) hmR hmnR
    have h3 := integral_interval_rpow_neg_le (ε := ε) hε (m := (m : ℝ)) (n := (n : ℝ)) hmR hmnR
    exact le_trans (by simpa [hsub] using h1) (by simpa [b] using h3)
  have hCauchy : CauchySeq a := cauchySeq_of_dist_le_of_one_le hb_nonneg hb_tendsto
    (fun m n hm hmn => by simpa [dist_eq_norm] using h_tail_pointwise m n hm hmn)
  rcases cauchySeq_tendsto_of_complete hCauchy with ⟨I, hT⟩
  have h_eventual_bound : ∀ᶠ N in atTop, ‖a N‖ ≤ (1 / ε) := by
    refine (eventually_ge_atTop 1).mono ?_
    intro N hNge1
    have h1N : (1 : ℝ) ≤ (N : ℝ) := mod_cast hNge1
    have h1 := zetaAbelFractKernel_norm_integral_le_Ioc ε hε s hs (m := (1 : ℝ)) (n := (N : ℝ))
      (hm := by norm_num) h1N
    have h3 := integral_interval_rpow_neg_le (ε := ε) hε (m := (1 : ℝ)) (n := (N : ℝ)) (hm := by norm_num) h1N
    exact le_trans (by simpa [a] using h1) (by simpa [one_div, Real.one_rpow, one_mul] using h3)
  have hIle : ‖I‖ ≤ (1 / ε) := by
    have hnorm : Tendsto (fun n => ‖a n‖) atTop (𝓝 ‖I‖) := (Filter.Tendsto.norm hT)
    exact le_of_tendsto hnorm h_eventual_bound
  refine ⟨I, ?_, hIle⟩
  simpa [a] using hT

/-- Lemma: Zeta formula for `Re(s) > 1`. -/
private lemma tendsto_zetaPartialSum_riemannZeta (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => zetaPartialSum s N) atTop (𝓝 (riemannZeta s)) := by
  classical
  set g : ℕ → ℂ := fun n => if n = 0 then 0 else (n : ℂ) ^ (-s)
  set h : ℕ → ℂ := fun n => (n + 1 : ℂ) ^ (-s)
  have hsne : s ≠ 0 := by
    intro h0
    have : (0 : ℝ) < s.re := lt_trans (show (0 : ℝ) < 1 by norm_num) hs
    simpa [h0] using (ne_of_gt this)
  have hsum_div : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) :=
    (Complex.summable_one_div_nat_cpow (p := s)).2 hs
  have hgSumm : Summable g := by
    simpa [g, one_div_natCast_cpow_eq_ite_cpow_neg s hsne] using hsum_div
  have h_eq_tail : (fun n => g (n + 1)) = h := by
    funext n; simp [g, h]
  have hhSumm : Summable h := by
    have : Summable (fun n : ℕ => g (n + 1)) := (summable_nat_add_iff (f := g) (k := 1)).2 hgSumm
    simpa [h_eq_tail] using this
  have hg0 : g 0 = 0 := by simp [g]
  have h_tsum_eq : (∑' n : ℕ, h n) = ∑' n : ℕ, g n := by
    have hzero_add := (Summable.tsum_eq_zero_add (f := g) hgSumm)
    have : (∑' n : ℕ, g n) = ∑' n : ℕ, g (n + 1) := by
      simpa [hg0, add_comm] using hzero_add
    simpa [h_eq_tail] using this.symm
  have hzeta : riemannZeta s = ∑' n : ℕ, g n := by
    simpa [g, one_div_natCast_cpow_eq_ite_cpow_neg s hsne] using
      (zeta_eq_tsum_one_div_nat_cpow (s := s) hs)
  have h_tendsto : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, h n) atTop (𝓝 (∑' n, h n)) :=
    (Summable.tendsto_sum_tsum_nat hhSumm)
  have htsumeq : (∑' n, h n) = riemannZeta s := h_tsum_eq.trans hzeta.symm
  simpa [zetaPartialSum, htsumeq, h] using h_tendsto

private lemma aestronglyMeasurable_zetaAbelFractKernel_Ioi (s : ℂ) :
    AEStronglyMeasurable (fun u : ℝ => zetaAbelFractKernel s u)
      (volume.restrict (Ioi (1 : ℝ))) := by
  refine (measurable_fract.complex_ofReal.mul ?_).aestronglyMeasurable
  simpa using Complex.measurable_ofReal.pow_const (-s - 1)

private lemma ae_bound_zetaAbelFractKernel_Ioi (s : ℂ) :
    ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))),
      ‖zetaAbelFractKernel s u‖ ≤ u ^ (-s.re - 1) := by
  refine (ae_restrict_iff' measurableSet_Ioi).2 (MeasureTheory.ae_of_all _ ?_)
  intro u hu
  exact norm_zetaAbelFractKernel_le u (le_of_lt hu) s

private lemma intervalIntegral_tendstoIoi_zetaAbelFractKernel (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u) atTop
      (𝓝 (∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u)) := by
  have hlt : (-s.re - 1) < (-1 : ℝ) := by linarith
  exact intervalIntegral.tendsto_integral_Ioi_of_ae_norm_le (f := fun u => zetaAbelFractKernel s u)
    (g := fun u => u ^ (-s.re - 1)) one_pos (aestronglyMeasurable_zetaAbelFractKernel_Ioi s)
    (ae_bound_zetaAbelFractKernel_Ioi s) (integrableOn_Ioi_rpow_of_lt hlt one_pos)

private lemma tendsto_scaled_cpow_div (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ (1 - s) / (1 - s)) atTop (𝓝 0) := by
  simpa [div_eq_mul_inv, mul_comm] using
    (Tendsto.const_mul (1 / (1 - s))
      (tendsto_natCast_cpow_zero_of_neg_re (1 - s)
        (by simp only [Complex.sub_re, Complex.one_re]; linarith)))

private lemma riemannZeta_abel_integral (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s = zetaAbelContinuationFormula s := by
  classical
  have hsne : s ≠ 1 := by
    intro h
    have hlt : (1 : ℝ) < (1 : ℝ) := by simpa [h, Complex.one_re] using hs
    exact lt_irrefl _ hlt
  set G : ℕ → ℂ := fun N =>
    (N : ℂ) ^ (1 - s) / (1 - s) + 1 + 1 / (s - 1)
      - s * ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u
  have hEv : ∀ᶠ N in atTop, zetaPartialSum s N = G N :=
    (eventually_ge_atTop 1).mono fun N hN => by
      calc zetaPartialSum s N
          _ = (N : ℂ) ^ (1 - s) / (1 - s) + 1 + 1 / (s - 1)
              - s * ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u :=
            zetaPartialSum_abel_formula s hsne N hN
          _ = G N := rfl
  have hG_to_zeta : Tendsto G atTop (𝓝 (riemannZeta s)) :=
    (tendsto_congr' hEv).mp (tendsto_zetaPartialSum_riemannZeta s hs)
  have hA := tendsto_scaled_cpow_div s hs
  have hK : Tendsto (fun _ : ℕ => (1 + 1 / (s - 1) : ℂ)) atTop (𝓝 (1 + 1 / (s - 1))) :=
    tendsto_const_nhds
  have hInt := intervalIntegral_tendstoIoi_zetaAbelFractKernel s hs
  have hIntMul := hInt.const_mul s
  set Aseq : ℕ → ℂ := fun N => (N : ℂ) ^ (1 - s) / (1 - s)
  set Kseq : ℕ → ℂ := fun _ => (1 + 1 / (s - 1) : ℂ)
  set Iseq : ℕ → ℂ := fun N => s * ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u
  have hSum : Tendsto (fun N => Aseq N + Kseq N) atTop (𝓝 (1 + 1 / (s - 1))) := by
    have hpair := hA.prodMk_nhds hK
    simpa using ((continuous_fst.add continuous_snd).tendsto _).comp hpair
  have hG_limit : Tendsto G atTop
      (𝓝 ((1 + 1 / (s - 1)) - s * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u)) := by
    have hSub : Tendsto (fun N => Aseq N + Kseq N - Iseq N) atTop
        (𝓝 ((1 + 1 / (s - 1)) - s * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u)) := by
      have hpair := hSum.prodMk_nhds hIntMul.neg
      simpa [sub_eq_add_neg] using
        ((continuous_fst.add continuous_snd).tendsto _).comp hpair
    have hGdef : (fun N => Aseq N + Kseq N - Iseq N) = G := by
      funext N; simp [Aseq, Kseq, Iseq, G, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
    simpa [hGdef] using hSub
  have huniq := tendsto_nhds_unique hG_to_zeta hG_limit
  simpa [zetaAbelContinuationFormula, sub_eq_add_neg] using huniq

private lemma aestronglyMeasurable_kernel_param_deriv (z : ℂ) :
  AEStronglyMeasurable (fun u : ℝ => -((Real.log u) : ℂ) * zetaAbelFractKernel z u)
    (volume.restrict (Ioi (1 : ℝ))) := by
  have hmeas : Measurable (fun u : ℝ => zetaAbelFractKernel z u) := by
    refine (measurable_fract.complex_ofReal.mul ?_)
    simpa using Complex.measurable_ofReal.pow_const (-z - 1)
  simpa using
    (Real.measurable_log.complex_ofReal.mul hmeas).neg.aestronglyMeasurable

private lemma kernel_deriv_norm_bound_on_ball (ε : ℝ) (u : ℝ) (hu : 1 < u) (x : ℂ) (hx : ε ≤ x.re) :
    ‖-((Real.log u) : ℂ) * zetaAbelFractKernel x u‖ ≤ Real.log u * u ^ (-1 - ε) := by
  have hu1 : (1 : ℝ) ≤ u := le_of_lt hu
  have hinner : ‖zetaAbelFractKernel x u‖ ≤ u ^ (-1 - ε) :=
    (norm_zetaAbelFractKernel_le u hu1 x).trans (Real.rpow_le_rpow_of_exponent_le hu1 (by linarith))
  have hlognorm : ‖-((Real.log u) : ℂ)‖ = Real.log u := by
    have hnonneg : 0 ≤ Real.log u := le_of_lt (Real.log_pos hu)
    simp [norm_neg, Complex.norm_real, abs_of_nonneg hnonneg]
  calc
    ‖-((Real.log u) : ℂ) * zetaAbelFractKernel x u‖
        = Real.log u * ‖zetaAbelFractKernel x u‖ := by rw [norm_mul, hlognorm]
    _ ≤ Real.log u * u ^ (-1 - ε) := mul_le_mul_of_nonneg_left hinner (le_of_lt (Real.log_pos hu))

private lemma integrable_zetaAbelFractKernel_at_param (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun u => zetaAbelFractKernel s u) (volume.restrict (Ioi (1 : ℝ))) := by
  classical
  set ε : ℝ := s.re / 2
  set g : ℝ → ℝ := fun u => u ^ (-1 - ε)
  have hfm := aestronglyMeasurable_zetaAbelFractKernel_Ioi s
  have hε : 0 < ε := half_pos hs
  have hεle : ε ≤ s.re := half_le_self (le_of_lt hs)
  have hbound : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), ‖zetaAbelFractKernel s u‖ ≤ g u := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (MeasureTheory.ae_of_all _ ?_)
    intro u hu
    have hx : (1 : ℝ) ≤ u := le_of_lt hu
    exact (norm_zetaAbelFractKernel_le u hx s).trans (Real.rpow_le_rpow_of_exponent_le hx (by linarith))
  have hgint : IntegrableOn g (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  simpa [IntegrableOn] using IntegrableOn.mono' hgint hfm hbound

/-- On `zetaAbelContinuationDomain`, the Abel formula satisfies the standard strip bound. -/
theorem norm_zetaAbelContinuationFormula_le (s : ℂ) (hs : s ∈ zetaAbelContinuationDomain) :
    ‖zetaAbelContinuationFormula s‖ ≤ 1 + ‖1 / (s - 1)‖ + ‖s‖ / s.re := by
  set g : ℝ → ℝ := fun u => u ^ (-s.re - 1)
  let μ := (volume : Measure ℝ).restrict (Ioi (1 : ℝ))
  have hs_re := zetaAbelContinuationDomain_re_pos hs
  have hsplit :
      ‖zetaAbelContinuationFormula s‖ ≤
        1 + ‖(s - 1)⁻¹‖ + ‖s‖ * ‖∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u‖ := by
    simp only [zetaAbelContinuationFormula, one_div]
    calc
      ‖1 + (s - 1)⁻¹ - s * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u‖
          ≤ ‖1 + (s - 1)⁻¹‖ + ‖-s * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u‖ := by
            simpa [sub_eq_add_neg] using
              norm_add_le (1 + (s - 1)⁻¹) (-s * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u)
      _ ≤ 1 + ‖(s - 1)⁻¹‖ + ‖s‖ * ‖∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u‖ := by
        gcongr
        · simpa [norm_one] using norm_add_le (1 : ℂ) ((s - 1)⁻¹)
        · simpa [norm_neg] using norm_mul_le
  have hint :
      ‖s‖ * ‖∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u‖ ≤ ‖s‖ / s.re :=
    mul_le_mul_of_nonneg_left
      ((MeasureTheory.norm_integral_le_of_norm_le (μ := μ)
        (f := fun u => zetaAbelFractKernel s u) (g := g)
        (by simp [μ, IntegrableOn]; exact integrableOn_Ioi_rpow_of_lt (by linarith) one_pos)
        (by
          refine (ae_restrict_iff' measurableSet_Ioi).2 (MeasureTheory.ae_of_all _ ?_)
          intro u hu
          simpa [g] using norm_zetaAbelFractKernel_le u (le_of_lt hu) s)).trans
        (by simpa [g, one_div] using
          (le_of_eq (by simp [μ, integral_Ioi_rpow_neg_re_sub_one (s := s) hs_re]))))
      (norm_nonneg s)
  calc
    ‖zetaAbelContinuationFormula s‖
        ≤ 1 + ‖(s - 1)⁻¹‖ + ‖s‖ * ‖∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u‖ := hsplit
    _ ≤ 1 + ‖(s - 1)⁻¹‖ + ‖s‖ / s.re := add_le_add_right hint _
    _ ≤ 1 + ‖1 / (s - 1)‖ + ‖s‖ / s.re := by
      gcongr
      simp [one_div]

private lemma eventually_aestronglyMeasurable_kernel_param (s : ℂ) :
    ∀ᶠ z in 𝓝 s,
      AEStronglyMeasurable (fun u : ℝ => zetaAbelFractKernel z u) (volume.restrict (Ioi (1 : ℝ))) :=
  Filter.Eventually.of_forall aestronglyMeasurable_zetaAbelFractKernel_Ioi

private lemma hasDerivAt_zetaAbelFractKernel_in_param (u : ℝ) (hu : 1 < u) (z : ℂ) :
    HasDerivAt (fun w => zetaAbelFractKernel w u)
      (-((Real.log u) : ℂ) * zetaAbelFractKernel z u) z := by
  have h := HasDerivAt.const_mul_ofReal_cpow_neg_sub_one ((Int.fract u : ℝ) : ℂ)
    (lt_trans zero_lt_one hu) z
  have hfun : (fun w => zetaAbelFractKernel w u) = fun w => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-w - 1) := by
    ext w; simp [zetaAbelFractKernel]
  exact (h.congr_of_eventuallyEq (EventuallyEq.of_eq hfun)).congr_deriv (by
    simp [zetaAbelFractKernel, Complex.ofReal_log (x := u) (hx := le_of_lt (lt_trans zero_lt_one hu)),
      mul_comm, mul_assoc, mul_left_comm])

private lemma hasDerivAt_integral_param_dominated_Ioi
  (F F' : ℂ → ℝ → ℂ) (s : ℂ) (δ : ℝ) (hδ : 0 < δ)
  (hmeas : ∀ᶠ z in 𝓝 s, AEStronglyMeasurable (F z) (MeasureTheory.volume.restrict (Ioi (1 : ℝ))))
  (hFint : Integrable (F s) (MeasureTheory.volume.restrict (Ioi (1 : ℝ))))
  (hF'meas : AEStronglyMeasurable (F' s) (MeasureTheory.volume.restrict (Ioi (1 : ℝ))))
  (bound : ℝ → ℝ)
  (hbound_int : Integrable bound (MeasureTheory.volume.restrict (Ioi (1 : ℝ))))
  (hbound : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Ioi (1 : ℝ))), ∀ z ∈ Metric.ball s δ, ‖F' z u‖ ≤ bound u)
  (hderiv : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Ioi (1 : ℝ))), ∀ z ∈ Metric.ball s δ, HasDerivAt (fun w => F w u) (F' z u) z)
  :
  HasDerivAt (fun z => ∫ u in Ioi (1 : ℝ), F z u) (∫ u in Ioi (1 : ℝ), F' s u) s := by
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := MeasureTheory.volume.restrict (Ioi (1 : ℝ)))
      (F := F) (F' := F') (x₀ := s)
      (s := Metric.ball s δ) (bound := bound) (Metric.ball_mem_nhds s hδ)
      (hF_meas := hmeas) (hF_int := hFint)
      (hF'_meas := hF'meas)
      (h_bound := hbound) (bound_integrable := hbound_int)
      (h_diff := hderiv)
  rcases h with ⟨_hint, hDeriv⟩
  simpa using hDeriv

private lemma zetaAbelFractKernel_integral_analytic (s : ℂ)
    (hs : zetaAbelContinuationReLower < s.re) :
    AnalyticAt ℂ (fun z : ℂ => ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel z u) s := by
  classical
  have hspos : 0 < s.re := lt_trans zetaAbelContinuationReLower_pos hs
  set ε : ℝ := s.re / 2
  have hεpos : 0 < ε := half_pos hspos
  have hεlt : ε < s.re := half_lt_self hspos
  rcases Complex.exists_pos_radius_forall_mem_ball_re_ge (z₀ := s) (a := ε) hεlt with ⟨δ, hδpos, hδprop⟩
  let F : ℂ → ℝ → ℂ := fun z u => zetaAbelFractKernel z u
  let F' : ℂ → ℝ → ℂ := fun z u => -((Real.log u) : ℂ) * F z u
  let bound : ℝ → ℝ := fun u => (2 / ε) * u ^ (-1 - ε / 2)
  have hbound_int : Integrable bound (volume.restrict (Ioi (1 : ℝ))) := by
    have hlt : (-1 - ε / 2) < (-1 : ℝ) := by linarith [half_pos hεpos]
    have hpow_int : IntegrableOn (fun u : ℝ => u ^ (-1 - ε / 2)) (Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt hlt (c := (1 : ℝ)) one_pos
    have hconst : IntegrableOn (fun u : ℝ => (2 / ε) * u ^ (-1 - ε / 2)) (Ioi (1 : ℝ)) :=
      hpow_int.const_mul (2 / ε)
    simpa [IntegrableOn, bound] using hconst
  have hDiff_eventually : ∀ᶠ z in 𝓝 s,
      DifferentiableAt ℂ (fun z0 => ∫ u in Ioi (1 : ℝ), F z0 u) z := by
    have hball : Metric.ball s (δ / 2) ∈ 𝓝 s :=
      Metric.ball_mem_nhds _ (by simpa using half_pos hδpos)
    refine Filter.eventually_of_mem hball ?_
    intro z hz
    have hz_lt_δ : dist z s < δ :=
      lt_trans (by simpa [Metric.mem_ball] using hz) (by simpa using half_lt_self hδpos)
    have hRe_inner : ∀ y, y ∈ Metric.ball z (δ / 2) → ε ≤ y.re := by
      intro y hy
      have hy_lt_δ : dist y z < δ :=
        lt_trans (by simpa [Metric.mem_ball] using hy) (by simpa using half_lt_self hδpos)
      exact hδprop z y hz_lt_δ hy_lt_δ
    have hmeas_z : ∀ᶠ w in 𝓝 z,
        AEStronglyMeasurable (F w) (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) :=
      eventually_aestronglyMeasurable_kernel_param (s := z)
    have hzRe_ge : ε ≤ z.re := by
      have hss : dist s s < δ := by simpa [dist_self] using hδpos
      have hz_lt_δ' : dist z s < δ := hz_lt_δ
      exact hδprop s z hss hz_lt_δ'
    have hzpos : 0 < z.re := lt_of_lt_of_le hεpos hzRe_ge
    have hFint_z : Integrable (F z) (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) := by
      simpa [F] using integrable_zetaAbelFractKernel_at_param (s := z) hzpos
    have hF'meas_z : AEStronglyMeasurable (F' z) (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) := by
      simpa [F, F'] using aestronglyMeasurable_kernel_param_deriv (z := z)
    have hbound_z : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Ioi (1 : ℝ))),
        ∀ w ∈ Metric.ball z (δ/2), ‖F' w u‖ ≤ bound u := by
      have hAll : ∀ u ∈ Ioi (1 : ℝ), ∀ w ∈ Metric.ball z (δ / 2), ‖F' w u‖ ≤ bound u := by
        intro u hu w hw
        have hF'le : ‖F' w u‖ ≤ Real.log u * u ^ (-1 - ε) :=
          kernel_deriv_norm_bound_on_ball ε u hu w (hRe_inner w hw)
        exact hF'le.trans (by simpa [bound] using Real.log_mul_rpow_neg_le_two_div_mul_rpow_neg hεpos hu)
      have hiff :=
        (MeasureTheory.ae_restrict_iff' (μ := MeasureTheory.volume) (s := Ioi (1 : ℝ))
          (p := fun u : ℝ => ∀ w ∈ Metric.ball z (δ/2), ‖F' w u‖ ≤ bound u) measurableSet_Ioi)
      exact hiff.mpr (MeasureTheory.ae_of_all _ hAll)
    -- AE differentiability of the parameter integrand on the ball around z
    have hderiv_z : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Ioi (1 : ℝ))),
        ∀ w ∈ Metric.ball z (δ/2), HasDerivAt (fun w0 => F w0 u) (F' w u) w := by
      -- Holds pointwise for all u > 1; lift to AE
      have hAll : ∀ u ∈ Ioi (1 : ℝ), ∀ w ∈ Metric.ball z (δ/2),
          HasDerivAt (fun w0 => F w0 u) (F' w u) w := by
        intro u hu w hw
        simpa [F, F'] using hasDerivAt_zetaAbelFractKernel_in_param u hu w
      -- lift to AE on the restricted measure
      have hiff :=
        (MeasureTheory.ae_restrict_iff' (μ := MeasureTheory.volume) (s := Ioi (1 : ℝ))
          (p := fun u : ℝ => ∀ w ∈ Metric.ball z (δ/2),
            HasDerivAt (fun w0 => F w0 u) (F' w u) w) measurableSet_Ioi)
      exact hiff.mpr (MeasureTheory.ae_of_all _ hAll)
    -- Apply dominated differentiation theorem at point z with radius δ/2
    have hD := hasDerivAt_integral_param_dominated_Ioi
      (F := F) (F' := F') (s := z) (δ := δ/2) (hδ := by simpa using (half_pos hδpos))
      (hmeas := hmeas_z) (hFint := hFint_z) (hF'meas := hF'meas_z)
      (bound := bound) (hbound_int := hbound_int) (hbound := hbound_z) (hderiv := hderiv_z)
    simpa using hD.differentiableAt
  exact (Complex.analyticAt_iff_eventually_differentiableAt
    (f := fun z => ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel z u) (c := s)).2 hDiff_eventually

/-- The Abel continuation formula is analytic on `zetaAbelContinuationDomain`. -/
theorem analyticOn_zetaAbelContinuationFormula :
    AnalyticOn ℂ zetaAbelContinuationFormula zetaAbelContinuationDomain := by
  simp only [AnalyticOn, zetaAbelContinuationDomain, Set.mem_setOf_eq, zetaAbelContinuationFormula]
  intro s ⟨hs_ne, hs_re⟩
  apply AnalyticAt.analyticWithinAt
  have h_linear : AnalyticAt ℂ (fun z => 1 + 1 / (z - 1)) s := by
    refine analyticAt_const.add (analyticAt_const.div (analyticAt_id.sub analyticAt_const) ?_)
    rwa [sub_ne_zero]
  exact h_linear.sub (analyticAt_id.mul (zetaAbelFractKernel_integral_analytic s hs_re))

/-- The Abel integral formula agrees with `ζ` on `zetaAbelContinuationDomain`. -/
theorem riemannZeta_eq_zetaAbelContinuationFormula (s : ℂ) (hs : s ∈ zetaAbelContinuationDomain) :
    riemannZeta s = zetaAbelContinuationFormula s := by
  let U := zetaAbelContinuationDomain
  have hUo := isOpen_zetaAbelContinuationDomain
  have h_subset : U ⊆ ({1} : Set ℂ)ᶜ := by
    intro z hz; simp [U, zetaAbelContinuationDomain, Set.mem_setOf_eq] at hz; exact hz.1
  have hζ : AnalyticOnNhd ℂ riemannZeta U := by
    rw [← hUo.analyticOn_iff_analyticOnNhd]
    exact AnalyticOn.mono analyticOn_riemannZeta_compl_one h_subset
  have hF : AnalyticOnNhd ℂ zetaAbelContinuationFormula U := by
    rw [← hUo.analyticOn_iff_analyticOnNhd]
    exact analyticOn_zetaAbelContinuationFormula
  have h_eqOn := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hζ hF
    isPreconnected_zetaAbelContinuationDomain two_mem_zetaAbelContinuationDomain ?_
  · exact h_eqOn hs
  · filter_upwards [hUo.mem_nhds two_mem_zetaAbelContinuationDomain,
      ContinuousAt.eventually_lt continuousAt_const Complex.continuous_re.continuousAt (by norm_num : (1 : ℝ) < 2)]
      with w _ hw_re using riemannZeta_abel_integral w hw_re
