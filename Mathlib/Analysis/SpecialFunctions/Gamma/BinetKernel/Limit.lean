module

public import Mathlib.Analysis.SpecialFunctions.Gamma.BinetKernel.Bounds

/-!
# Limit and integrability of the Binet kernel

* `tendsto_Ktilde_zero` : `Ktilde t → 1/12` as `t → 0⁺`
* `integrable_Ktilde_exp`, `integrable_Ktilde_exp_complex`
-/

open Real Set Filter MeasureTheory Topology
open scoped Topology

@[expose] public section

namespace BinetKernel

/-! ## Section 5: Limit at zero -/

/-- Auxiliary: (exp t - 1)/t → 1 as t → 0.
This follows from the derivative of exp at 0 being 1. -/
lemma tendsto_exp_sub_one_div :
    Tendsto (fun t => (Real.exp t - 1) / t) (𝓝[>] 0) (𝓝 1) := by
  have h := Real.hasDerivAt_exp 0
  rw [Real.exp_zero] at h
  -- HasDerivAt.tendsto_slope_zero_right gives:
  -- Tendsto (fun t => t⁻¹ • (exp(0 + t) - exp 0)) (𝓝[>] 0) (𝓝 1)
  have := h.tendsto_slope_zero_right
  simp only [zero_add, Real.exp_zero, smul_eq_mul] at this
  -- Convert t⁻¹ * (exp t - 1) to (exp t - 1) / t
  refine this.congr (fun t => ?_)
  rw [inv_mul_eq_div]

/-- The Taylor remainder `exp t - 1 - t - t² / 2`, divided by `t³`,
tends to `1 / 6` as `t → 0`. -/
lemma tendsto_exp_taylor3_div_cube :
    Tendsto (fun t => (Real.exp t - 1 - t - t ^ 2 / 2) / t ^ 3)
      (𝓝[>] 0) (𝓝 (1 / 6 : ℝ)) := by
  -- exp(t) - 1 - t - t²/2 = (exp(t) - (1 + t + t²/2 + t³/6)) + t³/6
  -- The first part is o(t³), so dividing by t³ gives 0 + 1/6
  have h_taylor :
      (fun x => Real.exp x - ∑ i ∈ Finset.range 4, x ^ i / Nat.factorial i)
        =o[𝓝 0] (· ^ 3) :=
    Real.exp_sub_sum_range_succ_isLittleO_pow 3
  -- Compute: ∑ i ∈ range 4, x^i/i! = 1 + x + x²/2 + x³/6
  have h_sum :
      ∀ x : ℝ, ∑ i ∈ Finset.range 4, x ^ i / Nat.factorial i =
        1 + x + x ^ 2 / 2 + x ^ 3 / 6 := by
    intro x; simp [Finset.sum_range_succ]; ring
  -- Rewrite: exp(t) - 1 - t - t²/2 = (exp(t) - sum) + t³/6
  have h_decomp :
      ∀ t : ℝ, Real.exp t - 1 - t - t ^ 2 / 2 =
        (Real.exp t - ∑ i ∈ Finset.range 4, t ^ i / Nat.factorial i) + t ^ 3 / 6 := by
    intro t; rw [h_sum]; ring
  -- The ratio (exp - sum)/t³ → 0 since exp - sum = o(t³)
  have h_zero :
      Tendsto
        (fun t => (Real.exp t - ∑ i ∈ Finset.range 4, t ^ i / Nat.factorial i) / t ^ 3)
        (𝓝[>] 0) (𝓝 0) := by
    have := h_taylor.tendsto_div_nhds_zero
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  -- Combine: our expression equals (o-term)/t³ + 1/6 → 0 + 1/6
  have h_add :
      Tendsto
        (fun t =>
          (Real.exp t - ∑ i ∈ Finset.range 4, t ^ i / Nat.factorial i) / t ^ 3 +
            1 / 6)
        (𝓝[>] 0) (𝓝 (0 + 1 / 6)) := h_zero.add tendsto_const_nhds
  simp only [zero_add] at h_add
  refine h_add.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hne : t ≠ 0 := ne_of_gt ht
  rw [h_decomp]
  field_simp

/-- Auxiliary: f(t)/t³ → 1/6 as t → 0⁺.
Since f(t) = exp(t)(t-2) + t + 2, Taylor expansion gives f(t) = t³/6 + O(t⁴). -/
private lemma tendsto_f_div_cube :
    Tendsto (fun t => f t / t ^ 3) (𝓝[>] 0) (𝓝 (1/6 : ℝ)) := by
  -- f(t) = exp(t)(t-2) + t + 2
  -- Using the Taylor expansion exp(t) = 1 + t + t²/2 + t³/6 + O(t⁴):
  -- f(t) = (1 + t + t²/2 + t³/6 + ...)(t-2) + t + 2 = t³/6 + O(t⁴)
  -- So f(t)/t³ → 1/6
  -- Strategy: decompose f(t) = t³/2 + h(t)(t-2) where h(t) = exp(t) - 1 - t - t²/2
  -- Then f(t)/t³ = 1/2 + (h(t)/t³)(t-2) → 1/2 + (1/6)(-2) = 1/6
  have h1 : Tendsto (fun t => (Real.exp t - 1 - t - t^2/2) / t^3 * (t - 2))
      (𝓝[>] 0) (𝓝 ((1/6 : ℝ) * (-2))) := by
    apply Tendsto.mul tendsto_exp_taylor3_div_cube
    have : Tendsto (fun x : ℝ => x - 2) (𝓝 0) (𝓝 (-2)) := by
      have h : (0 : ℝ) - 2 = -2 := by norm_num
      exact h ▸ tendsto_id.sub tendsto_const_nhds
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  have h2 : Tendsto (fun t => 1/2 + (Real.exp t - 1 - t - t^2/2) / t^3 * (t - 2))
      (𝓝[>] 0) (𝓝 (1/2 + (1/6) * (-2))) := tendsto_const_nhds.add h1
  have heq : (1/2 + (1/6) * (-2) : ℝ) = 1/6 := by norm_num
  rw [← heq]
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hne : t ≠ 0 := ne_of_gt ht
  -- f(t) = t³/2 + h(t)(t-2) where h = exp - 1 - t - t²/2
  have hdecomp : f t = t^3/2 + (Real.exp t - 1 - t - t^2/2) * (t - 2) := by unfold f; ring
  rw [hdecomp]
  field_simp

/-- The kernel K̃(t) → 1/12 as t → 0⁺.
This follows from the Taylor expansion: K(t) = t/12 - t³/720 + O(t⁵), so K(t)/t → 1/12. -/
theorem tendsto_Ktilde_zero :
    Tendsto Ktilde (𝓝[>] 0) (𝓝 (1/12 : ℝ)) := by
  -- Strategy: Ktilde t = f(t) / (2t²(exp t - 1)) for t > 0
  --         = (f(t)/t³) / (2 · (exp t - 1)/t)
  -- Since f(t)/t³ → 1/6 and (exp t - 1)/t → 1,
  -- we get Ktilde t → (1/6) / (2·1) = 1/12
  have h1 : ∀ᶠ t in 𝓝[>] 0, t ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ne_of_gt ht
  have h2 : ∀ᶠ t in 𝓝[>] 0, 0 < Real.exp t - 1 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact exp_sub_one_pos ht
  have h3 : ∀ᶠ t in 𝓝[>] 0, Ktilde t = f t / (2 * t^2 * (Real.exp t - 1)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [Ktilde_pos ht, ← K_pos ht, K_eq_alt' ht]
    unfold f; field_simp
  rw [tendsto_congr' h3]
  -- Rewrite as (f(t)/t³) / (2 · (exp t - 1)/t)
  have h4 : ∀ᶠ t in 𝓝[>] 0, f t / (2 * t^2 * (Real.exp t - 1)) =
      (f t / t^3) / (2 * ((Real.exp t - 1) / t)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hne : t ≠ 0 := ne_of_gt ht
    have hexp' : Real.exp t - 1 ≠ 0 := ne_of_gt (exp_sub_one_pos ht)
    field_simp
  rw [tendsto_congr' h4]
  -- Apply limit laws: (1/6) / (2 * 1) = 1/12
  have hlim_num := tendsto_f_div_cube
  have hlim_den := tendsto_exp_sub_one_div.const_mul 2
  have hne : (2 : ℝ) * 1 ≠ 0 := by norm_num
  convert hlim_num.div hlim_den hne using 1
  norm_num

/-- K̃ is continuous on ℝ. -/
lemma continuous_Ktilde : Continuous Ktilde := by
  -- Ktilde is continuous because:
  -- - For x > 0: continuousOn_Ktilde_Ioi
  -- - For x < 0: Ktilde is constant 1/12
  -- - At x = 0: left limit is 1/12, right limit is 1/12 (tendsto_Ktilde_zero)
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : 0 < x
  · exact continuousOn_Ktilde_Ioi.continuousAt (Ioi_mem_nhds hx)
  · push_neg at hx
    by_cases hx0 : x < 0
    · -- For x < 0, Ktilde is constant 1/12 in a neighborhood
      have hev : ∀ᶠ y in 𝓝 x, Ktilde y = 1/12 := by
        filter_upwards [Iio_mem_nhds hx0] with y hy
        unfold Ktilde; rw [if_pos (le_of_lt hy)]
      rw [ContinuousAt]
      have hval : Ktilde x = 1/12 := by unfold Ktilde; rw [if_pos (le_of_lt hx0)]
      rw [hval]
      exact tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm)
    · -- x = 0: use left/right continuity
      have hx_eq : x = 0 := le_antisymm hx (not_lt.mp hx0)
      subst hx_eq
      rw [continuousAt_iff_continuous_left'_right']
      constructor
      · -- Left continuity: Ktilde is constant 1/12 on Iio 0
        rw [ContinuousWithinAt]
        have hval : Ktilde 0 = 1/12 := Ktilde_zero
        rw [hval]
        apply tendsto_const_nhds.congr'
        filter_upwards [self_mem_nhdsWithin] with y hy
        unfold Ktilde; rw [if_pos (le_of_lt hy)]
      · -- Right continuity: from tendsto_Ktilde_zero
        rw [ContinuousWithinAt, Ktilde_zero]
        exact tendsto_Ktilde_zero

/-! ## Section 6: Integrability -/

/-- Ktilde is bounded on [0, ∞). -/
lemma Ktilde_bdd : ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ‖Ktilde t‖ ≤ C := by
  use 1/12
  intro t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (Ktilde_nonneg ht)]
  exact Ktilde_le ht

/-- The kernel K̃(t) * e^{-tx} is integrable on (0, ∞) for x > 0. -/
theorem integrable_Ktilde_exp {x : ℝ} (hx : 0 < x) :
    Integrable (fun t => Ktilde t * Real.exp (-t * x))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi 0)) := by
  -- exp(-t*x) = exp((-x)*t) is integrable on (0, ∞) since -x < 0
  have h_exp_int : IntegrableOn (fun t => Real.exp (-x * t)) (Set.Ioi 0) := by
    exact integrableOn_exp_mul_Ioi (neg_neg_of_pos hx) 0
  -- Rewrite exp(-t*x) as exp((-x)*t)
  have h_exp_eq : Set.EqOn (fun t => Real.exp (-x * t)) (fun t => Real.exp (-t * x)) (Set.Ioi 0) :=
    fun t _ => by ring_nf
  have h_exp_int' : IntegrableOn (fun t => Real.exp (-t * x)) (Set.Ioi 0) :=
    h_exp_int.congr_fun h_exp_eq measurableSet_Ioi
  -- Ktilde is bounded and continuous (hence measurable)
  have h_bdd : ∃ C, ∀ t, ‖Ktilde t‖ ≤ C := by
    use 1/12
    intro t
    by_cases ht : 0 ≤ t
    · rw [Real.norm_eq_abs, abs_of_nonneg (Ktilde_nonneg ht)]
      exact Ktilde_le ht
    · push_neg at ht
      simp only [Ktilde, if_pos (le_of_lt ht)]
      norm_num
  have h_meas : AEStronglyMeasurable Ktilde
      (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi 0)) :=
    continuous_Ktilde.aestronglyMeasurable.restrict
  -- Convert h_bdd to the ae form needed by bdd_mul
  obtain ⟨C, hC⟩ := h_bdd
  have h_bdd_ae : ∀ᵐ t ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi 0)),
      ‖Ktilde t‖ ≤ C := by
    filter_upwards with t
    exact hC t
  exact h_exp_int'.integrable.bdd_mul h_meas h_bdd_ae

/-- The Binet integral ∫₀^∞ K̃(t) e^{-tz} dt converges for Re(z) > 0. -/
theorem integrable_Ktilde_exp_complex {z : ℂ} (hz : 0 < z.re) :
    MeasureTheory.Integrable
      (fun t : ℝ => (Ktilde t : ℂ) * Complex.exp (-t * z))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi 0)) := by
  -- Complex.exp(-t*z) = Complex.exp((-z)*t) is integrable since Re(-z) < 0
  have h_neg_re : (-z).re < 0 := by simp [hz]
  have h_exp_int : IntegrableOn (fun t : ℝ => Complex.exp ((-z) * t)) (Set.Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi h_neg_re 0
  -- Rewrite exp(-t*z) as exp((-z)*t): they're equal since -z * t = -t * z
  have h_exp_eq : Set.EqOn (fun t : ℝ => Complex.exp ((-z) * t))
      (fun t : ℝ => Complex.exp (-t * z)) (Set.Ioi 0) := fun t _ => by
    have h : (-z) * (t : ℂ) = -(t : ℂ) * z := by ring
    simp only [h]
  have h_exp_int' : IntegrableOn (fun t : ℝ => Complex.exp (-t * z)) (Set.Ioi 0) :=
    h_exp_int.congr_fun h_exp_eq measurableSet_Ioi
  -- (Ktilde : ℂ) is bounded
  have h_bdd : ∃ C, ∀ t, ‖(Ktilde t : ℂ)‖ ≤ C := by
    use 1/12
    intro t
    simp only [Complex.norm_real, Real.norm_eq_abs]
    by_cases ht : 0 ≤ t
    · rw [abs_of_nonneg (Ktilde_nonneg ht)]
      exact Ktilde_le ht
    · push_neg at ht
      simp only [Ktilde, if_pos (le_of_lt ht)]
      norm_num
  -- (Ktilde : ℂ) is AE strongly measurable
  have h_meas : AEStronglyMeasurable (fun t : ℝ => (Ktilde t : ℂ))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi 0)) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      continuous_Ktilde.aestronglyMeasurable.restrict
  -- Convert h_bdd to the ae form needed by bdd_mul
  obtain ⟨C, hC⟩ := h_bdd
  have h_bdd_ae : ∀ᵐ t ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi 0)),
      ‖(Ktilde t : ℂ)‖ ≤ C := by
    filter_upwards with t
    exact hC t
  exact h_exp_int'.integrable.bdd_mul h_meas h_bdd_ae

end BinetKernel
