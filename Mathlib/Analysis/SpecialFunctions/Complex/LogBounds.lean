/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll. Matteo Cipollina
-/
module

public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.SpecificLimits.RCLike

/-!
# Estimates for the complex logarithm

We show that `log (1+z)` differs from its Taylor polynomial up to degree `n` by at most
`‖z‖^(n+1)/((n+1)*(1-‖z‖))` when `‖z‖ < 1`; see `Complex.norm_log_sub_logTaylor_le`.

To this end, we derive the representation of `log (1+z)` as the integral of `1/(1+tz)`
over the unit interval (`Complex.log_eq_integral`) and introduce notation
`Complex.logTaylor n` for the Taylor polynomial up to degree `n-1`.

We also record the `tsum` form of the series for `-log (1 - z)` on the unit disk; see
`Complex.neg_log_one_sub_eq_tsum`, together with the associated partial sums and tails
`Complex.partialLogSum` and `Complex.logTail`.

We also record `Real.pow_div_one_sub_le_two_mul` (a convenient bound when `r ≤ 1 / 2`) and
`Complex.norm_logTail_le_two_mul_norm_pow`, which packages it with `Complex.norm_logTail_le`.

The coefficient-identification lemmas later in the file connect `logTaylor` to the generic
analytic/Taylor-series API. The remainder bounds themselves remain specialized to `log (1 + z)`.
-/

@[expose] public section

namespace Real

/-- If `0 ≤ r ≤ 1 / 2`, then the geometric-factor denominator is bounded by `2`. -/
lemma pow_div_one_sub_le_two_mul {r : ℝ} (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) (m : ℕ) :
    r ^ (m + 1) / (1 - r) ≤ 2 * r ^ (m + 1) := by
  have hpow : 0 ≤ r ^ (m + 1) := pow_nonneg hr _
  have hhalf' : (1 / 2 : ℝ) ≤ 1 - r := by linarith
  calc
    r ^ (m + 1) / (1 - r) ≤ r ^ (m + 1) / (1 / 2 : ℝ) := by
      exact div_le_div_of_nonneg_left hpow (by positivity) hhalf'
    _ = 2 * r ^ (m + 1) := by ring

end Real

namespace Complex

/-!
### Integral representation of the complex log
-/

set_option backward.isDefEq.respectTransparency false in
lemma continuousOn_one_add_mul_inv {z : ℂ} (hz : 1 + z ∈ slitPlane) :
    ContinuousOn (fun t : ℝ ↦ (1 + t • z)⁻¹) (Set.Icc 0 1) :=
  ContinuousOn.inv₀ (by fun_prop)
    (fun _ ht ↦ slitPlane_ne_zero <| StarConvex.add_smul_mem starConvex_one_slitPlane hz ht.1 ht.2)

set_option backward.isDefEq.respectTransparency false in
open intervalIntegral in
/-- Represent `log (1 + z)` as an integral over the unit interval -/
lemma log_eq_integral {z : ℂ} (hz : 1 + z ∈ slitPlane) :
    log (1 + z) = z * ∫ (t : ℝ) in (0 : ℝ)..1, (1 + t • z)⁻¹ := by
  convert (integral_unitInterval_deriv_eq_sub (continuousOn_one_add_mul_inv hz)
    (fun _ ht ↦ hasDerivAt_log <|
      StarConvex.add_smul_mem starConvex_one_slitPlane hz ht.1 ht.2)).symm using 1
  simp only [log_one, sub_zero]

set_option backward.isDefEq.respectTransparency false in
/-- Represent `log (1 - z)⁻¹` as an integral over the unit interval -/
lemma log_inv_eq_integral {z : ℂ} (hz : 1 - z ∈ slitPlane) :
    log (1 - z)⁻¹ = z * ∫ (t : ℝ) in (0 : ℝ)..1, (1 - t • z)⁻¹ := by
  rw [sub_eq_add_neg 1 z] at hz ⊢
  rw [log_inv _ <| slitPlane_arg_ne_pi hz, neg_eq_iff_eq_neg, ← neg_mul]
  convert log_eq_integral hz using 5
  rw [sub_eq_add_neg, smul_neg]

/-!
### The Taylor polynomials of the logarithm
-/

/-- The coefficients of the Taylor series of `log (1 + z)` at `0`. -/
private noncomputable def logPowerSeriesCoeff (n : ℕ) : ℂ := (-1) ^ (n + 1) / n

private lemma norm_logPowerSeriesCoeff_le_one (n : ℕ) : ‖logPowerSeriesCoeff n‖ ≤ 1 := by
  cases n with
  | zero =>
      simp [logPowerSeriesCoeff]
  | succ n =>
      rw [logPowerSeriesCoeff, norm_div, norm_pow, norm_neg, norm_one, one_pow,
        Complex.norm_natCast]
      have hpos : (0 : ℝ) < n + 1 := by positivity
      have hge_nat : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
      have hge : (1 : ℝ) ≤ n + 1 := by exact_mod_cast hge_nat
      simpa [abs_of_pos hpos] using (inv_le_one₀ hpos).2 hge

private lemma summable_norm_logPowerSeriesCoeff_mul_half_pow :
    Summable (fun n : ℕ => ‖logPowerSeriesCoeff n‖ * (1 / 2 : ℝ) ^ n) := by
  have hhalf : 0 ≤ (1 / 2 : ℝ) := by norm_num
  refine Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_)
    (by simpa [one_div] using summable_geometric_two)
  simpa using mul_le_mul_of_nonneg_right (norm_logPowerSeriesCoeff_le_one n)
    (pow_nonneg hhalf n)

private noncomputable def halfNNReal : NNReal := ⟨1 / 2, by positivity⟩

private noncomputable def halfENNReal : ENNReal := halfNNReal

/-- The `n`th Taylor polynomial of `log` at `1`, as a function `ℂ → ℂ` -/
noncomputable
def logTaylor (n : ℕ) : ℂ → ℂ := fun z ↦ ∑ j ∈ Finset.range n, (-1) ^ (j + 1) * z ^ j / j

lemma logTaylor_zero : logTaylor 0 = fun _ ↦ 0 := by
  funext
  simp only [logTaylor, Finset.range_zero,
    Finset.sum_empty]

lemma logTaylor_succ (n : ℕ) :
    logTaylor (n + 1) = logTaylor n + (fun z : ℂ ↦ (-1) ^ (n + 1) * z ^ n / n) := by
  funext
  simpa only [logTaylor] using Finset.sum_range_succ ..

lemma logTaylor_succ_neg (n : ℕ) (z : ℂ) :
    logTaylor (n + 1) (-z) = logTaylor n (-z) - z ^ n / n := by
  rw [logTaylor_succ, Pi.add_apply]
  have hsign : (-1 : ℂ) ^ (n + 1) * (-z) ^ n = -z ^ n := by
    have hzpow : (-z) ^ n = (((-1 : ℂ) * z) ^ n) := by simp
    rw [hzpow, mul_pow, ← mul_assoc, ← pow_add]
    have hpow : (-1 : ℂ) ^ (n + 1 + n) = (-1 : ℂ) := by
      rw [show n + 1 + n = 2 * n + 1 by omega, pow_add, pow_mul]
      norm_num
    rw [hpow]
    ring
  rw [show (-1 : ℂ) ^ (n + 1) * (-z) ^ n / n = -(z ^ n / n) by
    rw [hsign]
    ring]
  abel

lemma logTaylor_at_zero (n : ℕ) : logTaylor n 0 = 0 := by
  induction n with
  | zero => simp [logTaylor_zero]
  | succ n ih => simpa [logTaylor_succ, ih] using ne_or_eq n 0

lemma hasDerivAt_logTaylor (n : ℕ) (z : ℂ) :
    HasDerivAt (logTaylor (n + 1)) (∑ j ∈ Finset.range n, (-1) ^ j * z ^ j) z := by
  induction n with
  | zero => simp [logTaylor_succ, logTaylor_zero, Pi.add_def, hasDerivAt_const]
  | succ n ih =>
    rw [logTaylor_succ]
    simp only [Nat.cast_add, Nat.cast_one,
      Finset.sum_range_succ]
    refine HasDerivAt.add ih ?_
    simp only [mul_div_assoc]
    have : HasDerivAt (fun x : ℂ ↦ (x ^ (n + 1) / (n + 1))) (z ^ n) z := by
      simp_rw [div_eq_mul_inv]
      convert HasDerivAt.mul_const (hasDerivAt_pow (n + 1) z) (((n : ℂ) + 1)⁻¹) using 1
      simp [field]
    convert HasDerivAt.const_mul _ this using 2
    ring

/-!
### Bounds for the difference between log and its Taylor polynomials
-/

lemma hasDerivAt_log_sub_logTaylor (n : ℕ) {z : ℂ} (hz : 1 + z ∈ slitPlane) :
    HasDerivAt (fun z : ℂ ↦ log (1 + z) - logTaylor (n + 1) z) ((-z) ^ n * (1 + z)⁻¹) z := by
  convert ((hasDerivAt_log hz).comp_const_add 1 z).sub (hasDerivAt_logTaylor n z) using 1
  have hz' : -z ≠ 1 := by
    intro H
    rw [neg_eq_iff_eq_neg] at H
    simp only [H, add_neg_cancel] at hz
    exact slitPlane_ne_zero hz rfl
  simp_rw [← mul_pow, neg_one_mul, geom_sum_eq hz', ← neg_add', div_neg, add_comm z]
  simp [field]

/-- Give a bound on `‖(1 + t * z)⁻¹‖` for `0 ≤ t ≤ 1` and `‖z‖ < 1`. -/
lemma norm_one_add_mul_inv_le {t : ℝ} (ht : t ∈ Set.Icc 0 1) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖(1 + t * z)⁻¹‖ ≤ (1 - ‖z‖)⁻¹ := by
  rw [Set.mem_Icc] at ht
  rw [norm_inv]
  refine inv_anti₀ (by linarith) ?_
  calc 1 - ‖z‖
    _ ≤ 1 - t * ‖z‖ := by
      nlinarith [norm_nonneg z]
    _ = 1 - ‖t * z‖ := by
      rw [norm_mul, Complex.norm_of_nonneg ht.1]
    _ ≤ ‖1 + t * z‖ := by
      rw [← norm_neg (t * z), ← sub_neg_eq_add]
      convert norm_sub_norm_le 1 (-(t * z))
      exact norm_one.symm

lemma integrable_pow_mul_norm_one_add_mul_inv (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    IntervalIntegrable (fun t : ℝ ↦ t ^ n * ‖(1 + t * z)⁻¹‖) MeasureTheory.volume 0 1 := by
  have := continuousOn_one_add_mul_inv <| mem_slitPlane_of_norm_lt_one hz
  rw [← Set.uIcc_of_le zero_le_one] at this
  exact ContinuousOn.intervalIntegrable (by fun_prop)

set_option backward.isDefEq.respectTransparency false in
open intervalIntegral in
/-- The difference of `log (1+z)` and its `(n+1)`st Taylor polynomial can be bounded in
terms of `‖z‖`. -/
lemma norm_log_sub_logTaylor_le (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖log (1 + z) - logTaylor (n + 1) z‖ ≤ ‖z‖ ^ (n + 1) * (1 - ‖z‖)⁻¹ / (n + 1) := by
  have help : IntervalIntegrable (fun t : ℝ ↦ t ^ n * (1 - ‖z‖)⁻¹) MeasureTheory.volume 0 1 :=
    IntervalIntegrable.mul_const (Continuous.intervalIntegrable (by fun_prop) 0 1) (1 - ‖z‖)⁻¹
  let f (z : ℂ) : ℂ := log (1 + z) - logTaylor (n + 1) z
  let f' (z : ℂ) : ℂ := (-z) ^ n * (1 + z)⁻¹
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f' (0 + t * z)) (0 + t * z) := by
    intro t ht
    rw [zero_add]
    exact hasDerivAt_log_sub_logTaylor n <|
      StarConvex.add_smul_mem starConvex_one_slitPlane (mem_slitPlane_of_norm_lt_one hz) ht.1 ht.2
  have hcont : ContinuousOn (fun t : ℝ ↦ f' (0 + t * z)) (Set.Icc 0 1) := by
    simp only [zero_add]
    exact (Continuous.continuousOn (by fun_prop)).mul <|
      continuousOn_one_add_mul_inv <| mem_slitPlane_of_norm_lt_one hz
  have H : f z = z * ∫ t in (0 : ℝ)..1, (-(t * z)) ^ n * (1 + t * z)⁻¹ := by
    convert (integral_unitInterval_deriv_eq_sub hcont hderiv).symm using 1
    · simp only [f, zero_add, add_zero, log_one, logTaylor_at_zero, sub_self, sub_zero]
    · simp only [f', real_smul, zero_add,
        smul_eq_mul]
  unfold f at H
  simp only [H, norm_mul]
  simp_rw [neg_pow (_ * z) n, mul_assoc, intervalIntegral.integral_const_mul, mul_pow,
    mul_comm _ (z ^ n), mul_assoc, intervalIntegral.integral_const_mul, norm_mul, norm_pow,
    norm_neg, norm_one, one_pow, one_mul, ← mul_assoc, ← pow_succ', mul_div_assoc]
  gcongr _ * ?_
  calc ‖∫ t in (0 : ℝ)..1, (t : ℂ) ^ n * (1 + t * z)⁻¹‖
    _ ≤ ∫ t in (0 : ℝ)..1, t ^ n * (1 - ‖z‖)⁻¹ := by
      refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one ?_ help
      filter_upwards with t ⟨ht₀, ht₁⟩
      rw [norm_mul, norm_pow, Complex.norm_of_nonneg ht₀.le]
      gcongr
      exact norm_one_add_mul_inv_le ⟨ht₀.le, ht₁⟩ hz
    _ = (1 - ‖z‖)⁻¹ / (n + 1) := by
      rw [intervalIntegral.integral_mul_const, mul_comm, integral_pow]
      simp [field]

/-- The difference `log (1+z) - z` is bounded by `‖z‖^2/(2*(1-‖z‖))` when `‖z‖ < 1`. -/
lemma norm_log_one_add_sub_self_le {z : ℂ} (hz : ‖z‖ < 1) :
    ‖log (1 + z) - z‖ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 := by
  convert norm_log_sub_logTaylor_le 1 hz using 2
  · simp [logTaylor_succ, logTaylor_zero, sub_eq_add_neg]
  · norm_num

set_option linter.style.whitespace false in -- manual alignment is not recognised
open scoped Topology in
lemma log_sub_logTaylor_isBigO (n : ℕ) :
    (fun z ↦ log (1 + z) - logTaylor (n + 1) z) =O[𝓝 0] fun z ↦ z ^ (n + 1) := by
  rw [Asymptotics.isBigO_iff]
  use 2 / (n + 1)
  filter_upwards [
    eventually_norm_sub_lt 0 one_pos,
    eventually_norm_sub_lt 0 (show 0 < 1 / 2 by simp)] with z hz1 hz12
  rw [sub_zero] at hz1 hz12
  have : (1 - ‖z‖)⁻¹ ≤ 2 := by rw [inv_le_comm₀ (sub_pos_of_lt hz1) two_pos]; linarith
  apply (norm_log_sub_logTaylor_le n hz1).trans
  rw [mul_div_assoc, mul_comm, norm_pow]
  gcongr

open scoped Topology in
lemma log_sub_self_isBigO :
    (fun z ↦ log (1 + z) - z) =O[𝓝 0] fun z ↦ z ^ 2 := by
  convert log_sub_logTaylor_isBigO 1
  simp [logTaylor_succ, logTaylor_zero]

lemma norm_log_one_add_le {z : ℂ} (hz : ‖z‖ < 1) :
    ‖log (1 + z)‖ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 + ‖z‖ := by
  rw [← sub_add_cancel (log (1 + z)) z]
  exact norm_add_le_of_le (Complex.norm_log_one_add_sub_self_le hz) le_rfl

/-- For `‖z‖ ≤ 1/2`, the complex logarithm is bounded by `(3/2) * ‖z‖`. -/
lemma norm_log_one_add_half_le_self {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : ‖log (1 + z)‖ ≤ (3 / 2) * ‖z‖ := by
  apply le_trans (norm_log_one_add_le (lt_of_le_of_lt hz one_half_lt_one))
  have hz3 : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀]
    · linarith
    · linarith
  have hz4 : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ / 2 * 2 / 2 := by
    gcongr
    · rw [inv_nonneg]
      linarith
    · rw [sq, div_eq_mul_one_div]
      gcongr
  simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    IsUnit.div_mul_cancel] at hz4
  linarith

/-- The difference of `log (1-z)⁻¹` and its `(n+1)`st Taylor polynomial can be bounded in
terms of `‖z‖`. -/
lemma norm_log_one_sub_inv_add_logTaylor_neg_le (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖log (1 - z)⁻¹ + logTaylor (n + 1) (-z)‖ ≤ ‖z‖ ^ (n + 1) * (1 - ‖z‖)⁻¹ / (n + 1) := by
  rw [sub_eq_add_neg,
    log_inv _ <| slitPlane_arg_ne_pi <| mem_slitPlane_of_norm_lt_one <| (norm_neg z).symm ▸ hz,
    ← sub_neg_eq_add, ← neg_sub', norm_neg]
  convert norm_log_sub_logTaylor_le n <| (norm_neg z).symm ▸ hz using 4 <;> rw [norm_neg]

/-- The difference `log (1-z)⁻¹ - z` is bounded by `‖z‖^2/(2*(1-‖z‖))` when `‖z‖ < 1`. -/
lemma norm_log_one_sub_inv_sub_self_le {z : ℂ} (hz : ‖z‖ < 1) :
    ‖log (1 - z)⁻¹ - z‖ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 := by
  convert norm_log_one_sub_inv_add_logTaylor_neg_le 1 hz using 2
  · simp [logTaylor_succ, logTaylor_zero, sub_eq_add_neg]
  · norm_num

set_option backward.isDefEq.respectTransparency false in
open Filter Asymptotics in
/-- The Taylor series of the complex logarithm at `1` converges to the logarithm in the
open unit disk. -/
lemma hasSum_taylorSeries_log {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ ↦ (-1) ^ (n + 1) * z ^ n / n) (log (1 + z)) := by
  refine (hasSum_iff_tendsto_nat_of_summable_norm ?_).mpr ?_
  · refine (summable_geometric_of_norm_lt_one hz).norm.of_nonneg_of_le (fun _ ↦ norm_nonneg _) ?_
    intro n
    simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_natCast]
    rcases n.eq_zero_or_pos with rfl | hn
    · simp
    conv => enter [2]; rw [← div_one (‖z‖ ^ n)]
    gcongr
    norm_cast
  · rw [← tendsto_sub_nhds_zero_iff]
    conv => enter [1, x]; rw [← div_one (_ - _), ← logTaylor]
    rw [← isLittleO_iff_tendsto fun _ h ↦ (one_ne_zero h).elim]
    refine IsLittleO.trans_isBigO ?_ <| isBigO_const_one ℂ (1 : ℝ) atTop
    have H : (fun n ↦ logTaylor n z - log (1 + z)) =O[atTop] (fun n : ℕ ↦ ‖z‖ ^ n) := by
      have (n : ℕ) : ‖logTaylor n z - log (1 + z)‖
          ≤ (max ‖log (1 + z)‖ (1 - ‖z‖)⁻¹) * ‖(‖z‖ ^ n)‖ := by
        rw [norm_sub_rev, norm_pow, norm_norm]
        cases n with
        | zero => simp [logTaylor_zero]
        | succ n =>
            refine (norm_log_sub_logTaylor_le n hz).trans ?_
            rw [mul_comm, ← div_one ((max _ _) * _)]
            gcongr
            · exact le_max_right ..
            · linarith
      exact (isBigOWith_of_le' atTop this).isBigO
    refine IsBigO.trans_isLittleO H ?_
    convert isLittleO_pow_pow_of_lt_left (norm_nonneg z) hz
    exact (one_pow _).symm

/-- The series `∑ z^n/n` converges to `-log (1-z)` on the open unit disk. -/
lemma hasSum_taylorSeries_neg_log {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ ↦ z ^ n / n) (-log (1 - z)) := by
  conv => enter [1, n]; rw [← neg_neg (z ^ n / n)]
  refine HasSum.neg ?_
  convert hasSum_taylorSeries_log (z := -z) (norm_neg z ▸ hz) using 2 with n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  simp [field, pow_add, ← mul_pow]

open scoped BigOperators in
/-- On the open unit disk, `-log (1 - z)` is the `tsum` with index shift `n ↦ n + 1`. -/
lemma neg_log_one_sub_eq_tsum {z : ℂ} (hz : ‖z‖ < 1) :
    -log (1 - z) = ∑' n : ℕ, z ^ (n + 1) / (n + 1) := by
  have h := hasSum_taylorSeries_neg_log hz
  rw [← h.tsum_eq, h.summable.tsum_eq_zero_add]
  simp only [pow_zero, Nat.cast_zero, div_zero, zero_add, Nat.cast_add, Nat.cast_one]

private lemma half_le_logPowerSeries_radius :
    halfENNReal ≤ (FormalMultilinearSeries.ofScalars ℂ logPowerSeriesCoeff).radius := by
  apply FormalMultilinearSeries.le_radius_of_summable
  simpa [halfENNReal, halfNNReal, one_div] using summable_norm_logPowerSeriesCoeff_mul_half_pow

private lemma hasFPowerSeriesOnBall_log_one_add_explicit :
    HasFPowerSeriesOnBall (fun z : ℂ ↦ log (1 + z))
      (FormalMultilinearSeries.ofScalars ℂ logPowerSeriesCoeff) 0 halfENNReal := by
  constructor
  · exact half_le_logPowerSeries_radius
  · change (0 : ENNReal) < ((1 / 2 : NNReal) : ENNReal)
    exact ENNReal.coe_pos.2 (by norm_num : (0 : NNReal) < 1 / 2)
  · intro y hy
    have hy' : ‖y‖ < 1 := by
      have hyhalfR : ‖y‖ < (1 / 2 : ℝ) := by
        simpa [halfENNReal, halfNNReal, Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm,
          coe_nnnorm] using hy
      linarith
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, logPowerSeriesCoeff, smul_eq_mul,
      div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hasSum_taylorSeries_log hy'

private lemma analyticAt_log_one_add : AnalyticAt ℂ (fun z : ℂ ↦ log (1 + z)) 0 := by
  have h1 : (1 + (0 : ℂ)) ∈ slitPlane := by
    simp
  simpa using (((analyticAt_const (v := (1 : ℂ))).add analyticAt_id).clog h1)

lemma iteratedDeriv_log_one_add_zero_div_factorial (n : ℕ) :
    iteratedDeriv n (fun z : ℂ ↦ log (1 + z)) 0 / n.factorial = (-1) ^ (n + 1) / n := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ logPowerSeriesCoeff
  let q : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ
      (fun m ↦ iteratedDeriv m (fun z : ℂ ↦ log (1 + z)) 0 / m.factorial)
  have hp : HasFPowerSeriesAt (fun z : ℂ ↦ log (1 + z)) p 0 :=
    hasFPowerSeriesOnBall_log_one_add_explicit.hasFPowerSeriesAt
  have hq : HasFPowerSeriesAt (fun z : ℂ ↦ log (1 + z)) q 0 := by
    simpa [q] using analyticAt_log_one_add.hasFPowerSeriesAt
  have hEq : p = q := hp.eq_formalMultilinearSeries hq
  have hcoeff := congrArg (FormalMultilinearSeries.coeff · n) hEq
  simpa [p, q, logPowerSeriesCoeff] using hcoeff.symm

lemma logTaylor_eq_sum_iteratedDeriv (n : ℕ) (z : ℂ) :
    logTaylor n z =
      ∑ j ∈ Finset.range n,
        (iteratedDeriv j (fun w : ℂ ↦ log (1 + w)) 0 / j.factorial) * z ^ j := by
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [iteratedDeriv_log_one_add_zero_div_factorial]
  ring

/-- The truncation of `-log (1 - z)`, expressed via `Complex.logTaylor`. -/
noncomputable
def partialLogSum (m : ℕ) (z : ℂ) : ℂ :=
  -logTaylor (m + 1) (-z)

@[simp]
lemma partialLogSum_zero (z : ℂ) : partialLogSum 0 z = 0 := by
  simp [partialLogSum, logTaylor_succ, logTaylor_zero]

@[simp]
lemma partialLogSum_at_zero (m : ℕ) : partialLogSum m 0 = 0 := by
  simp [partialLogSum, logTaylor_at_zero]

/-- Recurrence for the truncated logarithm series. -/
lemma partialLogSum_succ (m : ℕ) :
    partialLogSum (m + 1) = partialLogSum m + (fun z : ℂ ↦ z ^ (m + 1) / (m + 1)) := by
  funext z
  simpa [partialLogSum, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    congrArg Neg.neg (logTaylor_succ_neg (m + 1) z)

/-- Evaluate `logTaylor` at `-z` as a finite positive-coefficient logarithm sum. -/
lemma logTaylor_neg_eq_neg_sum (m : ℕ) (z : ℂ) :
    logTaylor (m + 1) (-z) = -∑ k ∈ Finset.range m, z ^ (k + 1) / (k + 1) := by
  induction m with
  | zero =>
      simp [logTaylor_succ, logTaylor_zero]
  | succ m hm =>
      rw [logTaylor_succ_neg, hm, Finset.sum_range_succ]
      have hcast : ((m + 1 : ℕ) : ℂ) = (1 + (m : ℂ)) := by
        simp [Nat.cast_add, Nat.cast_one, add_comm]
      rw [hcast]
      ring_nf

/-- `partialLogSum` is the partial sum `∑_{k=1}^m z^k / k`. -/
lemma partialLogSum_eq_sum (m : ℕ) (z : ℂ) :
    partialLogSum m z = ∑ k ∈ Finset.range m, z ^ (k + 1) / (k + 1) := by
  simpa [partialLogSum] using congrArg Neg.neg (logTaylor_neg_eq_neg_sum m z)

lemma hasDerivAt_partialLogSum (m : ℕ) (z : ℂ) :
    HasDerivAt (partialLogSum m) (∑ j ∈ Finset.range m, z ^ j) z := by
  cases m with
  | zero =>
      have hzero : partialLogSum 0 = fun _ : ℂ ↦ (0 : ℂ) := by
        funext w
        exact partialLogSum_zero w
      simpa [hzero] using (hasDerivAt_const z (c := (0 : ℂ)))
  | succ m =>
      have hsum :
          (∑ j ∈ Finset.range (m + 1), z ^ j) =
            ∑ j ∈ Finset.range (m + 1), (-1) ^ j * (-z) ^ j := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        symm
        calc
          (-1 : ℂ) ^ j * (-z) ^ j = (-1 : ℂ) ^ j * (((-1 : ℂ) * z) ^ j) := by simp
          _ = ((-1 : ℂ) ^ j * (-1 : ℂ) ^ j) * z ^ j := by rw [mul_pow]; ring
          _ = z ^ j := by
                rw [← pow_add, show j + j = 2 * j by omega, pow_mul]
                norm_num
      rw [hsum]
      simpa [partialLogSum] using
        (((hasDerivAt_logTaylor (m + 1) (-z)).comp z (hasDerivAt_neg z)).neg)

lemma differentiable_partialLogSum (m : ℕ) :
    Differentiable ℂ (fun z : ℂ => partialLogSum m z) := by
  intro z
  exact (hasDerivAt_partialLogSum m z).differentiableAt

/-- The tail `∑_{k>m} z^k / k`, as `∑' k, z^(m+1+k)/(m+1+k)`. -/
noncomputable
def logTail (m : ℕ) (z : ℂ) : ℂ :=
  ∑' k, z ^ (m + 1 + k) / (m + 1 + k)

lemma summable_logTail {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    Summable (fun k => z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)) := by
  have h_geom : Summable (fun k : ℕ => ‖z‖ ^ k) :=
    summable_geometric_of_lt_one (norm_nonneg z) hz
  refine Summable.of_norm_bounded (g := fun k => ‖z‖ ^ k) h_geom ?_
  intro k
  rw [norm_div, norm_pow]
  have h1 : (1 : ℝ) ≤ (m + 1 + k : ℝ) := by
    have : (0 : ℝ) ≤ (m + k : ℝ) := by positivity
    nlinarith
  have hnorm : ‖(↑m + 1 + ↑k : ℂ)‖ = (m + 1 + k : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
      (Complex.norm_natCast (m + 1 + k))
  rw [hnorm]
  calc
    ‖z‖ ^ (m + 1 + k) / (m + 1 + k : ℝ) ≤ ‖z‖ ^ (m + 1 + k) := by
      exact div_le_self (pow_nonneg (norm_nonneg z) _) h1
    _ = ‖z‖ ^ (m + 1) * ‖z‖ ^ k := by rw [pow_add]
    _ ≤ 1 * ‖z‖ ^ k := by
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (norm_nonneg z) k)
          exact pow_le_one₀ (norm_nonneg z) (le_of_lt hz)
    _ = ‖z‖ ^ k := one_mul _

lemma norm_logTail_le {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    ‖logTail m z‖ ≤ ‖z‖ ^ (m + 1) / (1 - ‖z‖) := by
  unfold logTail
  have h_rhs_summable : Summable (fun k => ‖z‖ ^ (m + 1 + k)) := by
    simpa [pow_add] using
      (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left (‖z‖ ^ (m + 1))
  have h_norm_summable : Summable (fun k => ‖z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ h_rhs_summable
    intro k
    rw [norm_div, norm_pow]
    have hnorm : ‖(↑m + 1 + ↑k : ℂ)‖ = (m + 1 + k : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
        (Complex.norm_natCast (m + 1 + k))
    rw [hnorm]
    have hm : 1 ≤ (m + 1 + k : ℝ) := by
      have : (0 : ℝ) ≤ (m + k : ℝ) := by positivity
      nlinarith
    exact div_le_self (pow_nonneg (norm_nonneg z) _) hm
  calc
    ‖∑' k, z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)‖
        ≤ ∑' k, ‖z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)‖ :=
          norm_tsum_le_tsum_norm h_norm_summable
    _ ≤ ∑' k, ‖z‖ ^ (m + 1 + k) := by
          refine h_norm_summable.tsum_le_tsum ?_ h_rhs_summable
          intro k
          rw [norm_div, norm_pow]
          have hm : 1 ≤ (m + 1 + k : ℝ) := by
            have : (0 : ℝ) ≤ (m + k : ℝ) := by positivity
            nlinarith
          have hnorm : ‖(↑m + 1 + ↑k : ℂ)‖ = (m + 1 + k : ℝ) := by
            simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
              (Complex.norm_natCast (m + 1 + k))
          rw [hnorm]
          exact div_le_self (pow_nonneg (norm_nonneg z) _) hm
    _ = ‖z‖ ^ (m + 1) / (1 - ‖z‖) := by
          have h_eq :
              (fun k => ‖z‖ ^ (m + 1 + k)) = fun k => ‖z‖ ^ (m + 1) * ‖z‖ ^ k := by
            ext k
            rw [pow_add]
          rw [h_eq, tsum_mul_left]
          have h_geom := hasSum_geometric_of_lt_one (norm_nonneg z) hz
          rw [h_geom.tsum_eq, div_eq_mul_inv]

lemma norm_logTail_le_two_mul_norm_pow {z : ℂ} (hz : ‖z‖ < 1) (hzhalf : ‖z‖ ≤ 1 / 2) (m : ℕ) :
    ‖logTail m z‖ ≤ 2 * ‖z‖ ^ (m + 1) :=
  (norm_logTail_le hz m).trans (Real.pow_div_one_sub_le_two_mul (norm_nonneg z) hzhalf m)

lemma norm_partialLogSum_le_nat_mul_max_one_norm_pow (m : ℕ) (z : ℂ) :
    ‖partialLogSum m z‖ ≤ (m : ℝ) * max 1 (‖z‖ ^ m) := by
  have hsum :
      ‖partialLogSum m z‖ ≤ ∑ k ∈ Finset.range m, ‖z ^ (k + 1) / (k + 1)‖ := by
    rw [partialLogSum_eq_sum]
    exact norm_sum_le _ _
  have hterm : ∀ k ∈ Finset.range m, ‖z ^ (k + 1) / (k + 1)‖ ≤ max 1 (‖z‖ ^ m) := by
    intro k hk
    rw [norm_div, norm_pow]
    have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have hk1_nat : (1 : ℕ) ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
      exact_mod_cast hk1_nat
    have hdenom : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
        (Complex.norm_natCast (k + 1))
    have hk_le : k + 1 ≤ m := Nat.succ_le_iff.2 (Finset.mem_range.1 hk)
    have hpow_le : ‖z‖ ^ (k + 1) ≤ max 1 (‖z‖ ^ m) := by
      have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
      by_cases hz1 : ‖z‖ ≤ (1 : ℝ)
      · have : ‖z‖ ^ (k + 1) ≤ 1 := by exact pow_le_one₀ hz0 hz1
        exact this.trans (le_max_left _ _)
      · have hz1' : (1 : ℝ) ≤ ‖z‖ := le_of_lt (lt_of_not_ge hz1)
        have : ‖z‖ ^ (k + 1) ≤ ‖z‖ ^ m := pow_le_pow_right₀ hz1' hk_le
        exact this.trans (le_max_right _ _)
    calc
      ‖z‖ ^ (k + 1) / ‖((k : ℂ) + 1)‖ = ‖z‖ ^ (k + 1) / ((k : ℝ) + 1) := by simp [hdenom]
      _ ≤ ‖z‖ ^ (k + 1) := by
            exact div_le_self (pow_nonneg (norm_nonneg z) _) hk1
      _ ≤ max 1 (‖z‖ ^ m) := hpow_le
  have hsum_le :
      (∑ k ∈ Finset.range m, ‖z ^ (k + 1) / (k + 1)‖) ≤
        ∑ _k ∈ Finset.range m, max 1 (‖z‖ ^ m) :=
    Finset.sum_le_sum (fun k hk => hterm k hk)
  have hcard : ∑ _k ∈ Finset.range m, max 1 (‖z‖ ^ m) = (m : ℝ) * max 1 (‖z‖ ^ m) := by
    simp [Finset.sum_const]
  exact hsum.trans (hsum_le.trans_eq hcard)

/-- Decompose the logarithm series into its first `m` terms and the remaining tail. -/
lemma neg_log_one_sub_eq_partialLogSum_add_logTail {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    -log (1 - z) = partialLogSum m z + logTail m z := by
  let f : ℕ → ℂ := fun k ↦ z ^ (k + 1) / ((k : ℂ) + 1)
  have h_summable : Summable f := by
    simpa [f, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
      (summable_logTail hz 0)
  have h_decomp := h_summable.sum_add_tsum_nat_add m
  rw [neg_log_one_sub_eq_tsum hz, partialLogSum_eq_sum, ← h_decomp]
  congr 1
  unfold logTail
  refine tsum_congr fun k ↦ ?_
  simp only [f, Nat.cast_add]
  ring_nf

end Complex

section Limits

/-! Limits of functions of the form `(1 + t/x + o(1/x)) ^ x` as `x → ∞`. -/

open Filter Asymptotics
open scoped Topology

namespace Complex

/-- The limit of `x * log (1 + g x)` as `(x : ℝ) → ∞` is `t`,
where `t : ℂ` is the limit of `x * g x`. -/
lemma tendsto_mul_log_one_add_of_tendsto {g : ℝ → ℂ} {t : ℂ}
    (hg : Tendsto (fun x ↦ x * g x) atTop (𝓝 t)) :
    Tendsto (fun x ↦ x * log (1 + g x)) atTop (𝓝 t) := by
  apply hg.congr_dist
  refine IsBigO.trans_tendsto ?_ tendsto_inv_atTop_zero.ofReal
  simp_rw [dist_comm (_ * g _), dist_eq, ← mul_sub, isBigO_norm_left]
  calc
    _ =O[atTop] fun x ↦ x * g x ^ 2 := by
      have hg0 := tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded hg.norm.isBoundedUnder_le
        (RCLike.tendsto_ofReal_atTop_cobounded ℂ)
      exact (isBigO_refl _ _).mul (log_sub_self_isBigO.comp_tendsto hg0)
    _ =ᶠ[atTop] fun x ↦ (x * g x) ^ 2 * x⁻¹ := by
      filter_upwards [eventually_ne_atTop 0] with x hx0
      rw [ofReal_inv, eq_mul_inv_iff_mul_eq₀ (mod_cast hx0)]
      ring
    _ =O[atTop] _ := by
      simpa using isBigO_const_of_tendsto hg (one_ne_zero (α := ℂ))
        |>.pow 2 |>.mul (isBigO_refl _ _)

/-- The limit of `(1 + g x) ^ x` as `(x : ℝ) → ∞` is `exp t`,
where `t : ℂ` is the limit of `x * g x`. -/
lemma tendsto_one_add_cpow_exp_of_tendsto {g : ℝ → ℂ} {t : ℂ}
    (hg : Tendsto (fun x ↦ x * g x) atTop (𝓝 t)) :
    Tendsto (fun x ↦ (1 + g x) ^ (x : ℂ)) atTop (𝓝 (exp t)) := by
  apply ((continuous_exp.tendsto _).comp (tendsto_mul_log_one_add_of_tendsto hg)).congr'
  have hg0 := tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded
    hg.norm.isBoundedUnder_le (RCLike.tendsto_ofReal_atTop_cobounded ℂ)
  filter_upwards [hg0.eventually_ne (show 0 ≠ -1 by simp)] with x hg1
  dsimp
  rw [cpow_def_of_ne_zero, mul_comm]
  intro hg0
  rw [← add_eq_zero_iff_neg_eq.mp hg0] at hg1
  norm_num at hg1

/-- The limit of `(1 + t/x) ^ x` as `x → ∞` is `exp t` for `t : ℂ`. -/
lemma tendsto_one_add_div_cpow_exp (t : ℂ) :
    Tendsto (fun x : ℝ ↦ (1 + t / x) ^ (x : ℂ)) atTop (𝓝 (exp t)) := by
  apply tendsto_one_add_cpow_exp_of_tendsto
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [eventually_ne_atTop 0] with x hx0
  exact mul_div_cancel₀ t (mod_cast hx0)

/-- The limit of `n * log (1 + g n)` as `(n : ℝ) → ∞` is `t`,
where `t : ℂ` is the limit of `n * g n`. -/
lemma tendsto_nat_mul_log_one_add_of_tendsto {g : ℕ → ℂ} {t : ℂ}
    (hg : Tendsto (fun n ↦ n * g n) atTop (𝓝 t)) :
    Tendsto (fun n ↦ n * log (1 + g n)) atTop (𝓝 t) :=
  tendsto_mul_log_one_add_of_tendsto (tendsto_smul_comp_nat_floor_of_tendsto_mul hg)
    |>.comp tendsto_natCast_atTop_atTop |>.congr (by simp)

/-- The limit of `(1 + g n) ^ n` as `(n : ℝ) → ∞` is `exp t`,
where `t : ℂ` is the limit of `n * g n`. -/
lemma tendsto_one_add_pow_exp_of_tendsto {g : ℕ → ℂ} {t : ℂ}
    (hg : Tendsto (fun n ↦ n * g n) atTop (𝓝 t)) :
    Tendsto (fun n ↦ (1 + g n) ^ n) atTop (𝓝 (exp t)) :=
  tendsto_one_add_cpow_exp_of_tendsto (tendsto_smul_comp_nat_floor_of_tendsto_mul hg)
    |>.comp tendsto_natCast_atTop_atTop |>.congr (by simp)

/-- The limit of `(1 + t/n) ^ n` as `n → ∞` is `exp t` for `t : ℂ`. -/
lemma tendsto_one_add_div_pow_exp (t : ℂ) :
    Tendsto (fun n : ℕ ↦ (1 + t / n) ^ n) atTop (𝓝 (exp t)) :=
  tendsto_one_add_div_cpow_exp t |>.comp tendsto_natCast_atTop_atTop |>.congr (by simp)

/-- `(1 + t/n + o(1/n)) ^ n → exp t` for `t ∈ ℂ`. -/
lemma tendsto_pow_exp_of_isLittleO_sub_add_div {f : ℕ → ℂ} (t : ℂ)
    (hf : (fun n ↦ f n - (1 + t / n)) =o[atTop] fun n ↦ 1 / (n : ℂ)) :
    Tendsto (fun n ↦ f n ^ n) atTop (𝓝 (exp t)) := by
  rw [show (fun n ↦ f n ^ n) = (fun n ↦ (1 + (f n - 1)) ^ n) by ext; simp]
  refine tendsto_one_add_pow_exp_of_tendsto (tendsto_sub_nhds_zero_iff.1 ?_)
  convert hf.tendsto_inv_smul_nhds_zero.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n h0
  simp
  field_simp [n.cast_ne_zero.2 h0]
  ring

end Complex

namespace Real

/-- The limit of `x * log (1 + g x)` as `(x : ℝ) → ∞` is `t`,
where `t : ℝ` is the limit of `x * g x`. -/
lemma tendsto_mul_log_one_add_of_tendsto {g : ℝ → ℝ} {t : ℝ}
    (hg : Tendsto (fun x ↦ x * g x) atTop (𝓝 t)) :
    Tendsto (fun x ↦ x * log (1 + g x)) atTop (𝓝 t) := by
  #adaptation_note /-- Prior to https://github.com/leanprover/lean4/pull/12179,
  `Real.cobounded_eq` was marked `@[simp]`, so didn't have to be passed explicitly here.
  Now the `simpNF` linter complains about it. -/
  have hg0 := tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded
    hg.norm.isBoundedUnder_le (tendsto_id'.mpr (by simp [Real.cobounded_eq]))
  rw [← tendsto_ofReal_iff] at hg ⊢
  push_cast at hg ⊢
  apply (Complex.tendsto_mul_log_one_add_of_tendsto hg).congr'
  filter_upwards [hg0.eventually_const_le (show (-1 : ℝ) < 0 by simp)] with x hg1
  rw [Complex.ofReal_log (by linarith), Complex.ofReal_add, Complex.ofReal_one]

theorem tendsto_mul_log_one_add_div_atTop (t : ℝ) :
    Tendsto (fun x => x * log (1 + t / x)) atTop (𝓝 t) :=
  tendsto_mul_log_one_add_of_tendsto <|
    tendsto_const_nhds.congr' <|
      (EventuallyEq.div_mul_cancel_atTop tendsto_id).symm.trans <|
        .of_eq <| funext fun _ => mul_comm _ _

/-- The limit of `(1 + g x) ^ x` as `(x : ℝ) → ∞` is `exp t`,
where `t : ℝ` is the limit of `x * g x`. -/
lemma tendsto_one_add_rpow_exp_of_tendsto {g : ℝ → ℝ} {t : ℝ}
    (hg : Tendsto (fun x ↦ x * g x) atTop (𝓝 t)) :
    Tendsto (fun x ↦ (1 + g x) ^ x) atTop (𝓝 (exp t)) := by
  #adaptation_note /-- Prior to https://github.com/leanprover/lean4/pull/12179,
  `Real.cobounded_eq` was marked `@[simp]`, so didn't have to be passed explicitly here.
  Now the `simpNF` linter complains about it. -/
  have hg0 := tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded
    hg.norm.isBoundedUnder_le (tendsto_id'.mpr (by simp [Real.cobounded_eq]))
  rw [← tendsto_ofReal_iff] at hg ⊢
  push_cast at hg ⊢
  apply (Complex.tendsto_one_add_cpow_exp_of_tendsto hg).congr'
  filter_upwards [hg0.eventually_const_le (show (-1 : ℝ) < 0 by simp)] with x hg1
  rw [Complex.ofReal_cpow (by linarith), Complex.ofReal_add, Complex.ofReal_one]

/-- The limit of `(1 + t/x) ^ x` as `x → ∞` is `exp t` for `t : ℝ`. -/
lemma tendsto_one_add_div_rpow_exp (t : ℝ) :
    Tendsto (fun x : ℝ ↦ (1 + t / x) ^ x) atTop (𝓝 (exp t)) := by
  apply tendsto_one_add_rpow_exp_of_tendsto
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [eventually_ne_atTop 0] with x hx0
  exact mul_div_cancel₀ t (mod_cast hx0)

/-- The limit of `n * log (1 + g n)` as `(n : ℝ) → ∞` is `t`,
where `t : ℝ` is the limit of `n * g n`. -/
lemma tendsto_nat_mul_log_one_add_of_tendsto {g : ℕ → ℝ} {t : ℝ}
    (hg : Tendsto (fun n ↦ n * g n) atTop (𝓝 t)) :
    Tendsto (fun n ↦ n * log (1 + g n)) atTop (𝓝 t) :=
  tendsto_mul_log_one_add_of_tendsto (tendsto_smul_comp_nat_floor_of_tendsto_mul hg) |>.comp
    tendsto_natCast_atTop_atTop |>.congr (by simp)

/-- The limit of `(1 + g n) ^ n` as `(n : ℝ) → ∞` is `exp t`,
where `t : ℝ` is the limit of `n * g n`. -/
lemma tendsto_one_add_pow_exp_of_tendsto {g : ℕ → ℝ} {t : ℝ}
    (hg : Tendsto (fun n ↦ n * g n) atTop (𝓝 t)) :
    Tendsto (fun n ↦ (1 + g n) ^ n) atTop (𝓝 (exp t)) :=
  tendsto_one_add_rpow_exp_of_tendsto (tendsto_smul_comp_nat_floor_of_tendsto_mul hg) |>.comp
    tendsto_natCast_atTop_atTop |>.congr (by simp)

/-- The limit of `(1 + t/n) ^ n` as `n → ∞` is `exp t` for `t : ℝ`. -/
lemma tendsto_one_add_div_pow_exp (t : ℝ) :
    Tendsto (fun n : ℕ ↦ (1 + t / n) ^ n) atTop (𝓝 (exp t)) :=
  tendsto_one_add_div_rpow_exp t |>.comp tendsto_natCast_atTop_atTop |>.congr (by simp)

end Real

end Limits
