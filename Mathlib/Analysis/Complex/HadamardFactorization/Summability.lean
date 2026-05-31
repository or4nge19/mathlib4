/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Complex.HadamardFactorization

/-!
## Divisor summability from logarithmic growth

This file proves the dyadic shell summability estimates for the divisor of an entire function
satisfying a logarithmic growth bound.
-/

@[expose] public section

noncomputable section

open Filter Topology Set Complex
open scoped BigOperators Topology

namespace Complex.Hadamard

/-!
### Dyadic-shell summability for divisor-indexed zeros
-/

open scoped BigOperators

/-- The dyadic lower endpoint associated to `⌊log₂ x⌋` is at most `x`, for `1 ≤ x`. -/
lemma two_pow_floor_logb_le {x : ℝ} (hx : 1 ≤ x) :
    (2 : ℝ) ^ (⌊Real.logb 2 x⌋₊ : ℝ) ≤ x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx
  have hlog_nonneg : 0 ≤ Real.logb 2 x :=
    Real.logb_nonneg (b := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2) hx
  have hfloor_le : (⌊Real.logb 2 x⌋₊ : ℝ) ≤ Real.logb 2 x := by
    simpa using (Nat.floor_le hlog_nonneg)
  exact (Real.le_logb_iff_rpow_le (b := (2 : ℝ)) (x := (⌊Real.logb 2 x⌋₊ : ℝ)) (y := x)
    (by norm_num : (1 : ℝ) < 2) hx0).1 hfloor_le

/-- `x` lies below the next dyadic endpoint after `⌊log₂ x⌋`, for `1 ≤ x`. -/
lemma lt_two_pow_floor_logb_add_one {x : ℝ} (hx : 1 ≤ x) :
    x < (2 : ℝ) ^ ((⌊Real.logb 2 x⌋₊ : ℝ) + 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx
  have hlt : Real.logb 2 x < (⌊Real.logb 2 x⌋₊ : ℝ) + 1 := by
    simpa using (Nat.lt_floor_add_one (Real.logb 2 x))
  exact (Real.logb_lt_iff_lt_rpow (b := (2 : ℝ)) (x := x)
    (y := (⌊Real.logb 2 x⌋₊ : ℝ) + 1) (by norm_num : (1 : ℝ) < 2) hx0).1 hlt

/-- The number of divisor indices in a closed ball is bounded by the divisor mass there. -/
lemma card_shell_le_sum_divisor_closedBall
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (_hnot : ∃ z : ℂ, f z ≠ 0)
    {r0 R : ℝ} (hr0 : 0 < r0) (hR : r0 ≤ R) :
    (Nat.card {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) // ‖divisorZeroIndex₀_val p‖ ≤ R} : ℝ)
      ≤
      ((((Function.locallyFinsuppWithin.finiteSupport
              (Function.locallyFinsuppWithin.toClosedBall R
                (MeromorphicOn.divisor f (Set.univ : Set ℂ)))
              (isCompact_closedBall (0 : ℂ) |R|)).toFinset).filter fun z : ℂ => z ≠ 0).sum
          fun z : ℂ => (MeromorphicOn.divisor f (Set.univ : Set ℂ) z : ℝ)) := by
  classical
  set U : Set ℂ := (Set.univ : Set ℂ)
  set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  haveI :
      Fintype {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ R} := by
    classical
    have : Finite {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ R} := by
      have : Metric.closedBall (0 : ℂ) R ⊆ U := by simp [U]
      simpa using (finite_divisorZeroIndex₀_subtype_norm_le (f := f) (U := U) (B := R) this)
    exact Fintype.ofFinite _
  have hAnal : AnalyticOnNhd ℂ f U := by
    intro z hz; simpa using (hf.analyticAt z)
  have hDnonneg : 0 ≤ D := by
    simpa [D] using
      (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (𝕜 := ℂ) (f := f) (U := U) hAnal)
  let SR : Finset ℂ :=
    (Function.locallyFinsuppWithin.finiteSupport (Function.locallyFinsuppWithin.toClosedBall R D)
          (isCompact_closedBall (0 : ℂ) |R|)).toFinset
  let S : Finset ℂ := SR.filter fun z : ℂ => z ≠ 0
  let T : Type :=
    Σ z : S, Fin (Int.toNat (D z.1))
  let φ :
      {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ R} → T := fun p =>
    let z0 : ℂ := divisorZeroIndex₀_val p.1
    have hz0_memSR : z0 ∈ SR := by
      have hz0_ball : z0 ∈ Metric.closedBall (0 : ℂ) |R| := by
        have hR0 : 0 < R := lt_of_lt_of_le hr0 hR
        have : ‖z0‖ ≤ |R| := by
          have : ‖z0‖ ≤ R := p.2
          simpa [abs_of_pos hR0] using this
        simpa [Metric.mem_closedBall, dist_zero_right] using this
      have hz0_support : z0 ∈ (Function.locallyFinsuppWithin.toClosedBall R D).support := by
        have hz0_suppD : z0 ∈ D.support := by
          simpa [z0, D] using (divisorZeroIndex₀_val_mem_divisor_support (p := p.1))
        have hEq : (Function.locallyFinsuppWithin.toClosedBall R D) z0 = D z0 := by
          simpa using
            (Function.locallyFinsuppWithin.toClosedBall_eval_within (r := R) (f := D) (z := z0) hz0_ball)
        have hDz0_ne : D z0 ≠ 0 := by
          simpa [Function.mem_support] using hz0_suppD
        have : (Function.locallyFinsuppWithin.toClosedBall R D) z0 ≠ 0 := by simpa [hEq] using hDz0_ne
        simpa [Function.mem_support] using this
      exact (Set.Finite.mem_toFinset
        (Function.locallyFinsuppWithin.finiteSupport (Function.locallyFinsuppWithin.toClosedBall R D)
          (isCompact_closedBall (0 : ℂ) |R|))).2 hz0_support
    have hz0_ne0 : z0 ≠ 0 := divisorZeroIndex₀_val_ne_zero p.1
    have hz0_memS : z0 ∈ S := Finset.mem_filter.2 ⟨hz0_memSR, hz0_ne0⟩
    ⟨⟨z0, hz0_memS⟩, by
        simpa [z0, divisorZeroIndex₀_val, D] using p.1.1.2⟩
  have hφ_inj : Function.Injective φ := by
    intro p q hpq
    have hσ := (Sigma.mk.inj_iff).1 hpq
    have hzS : (φ p).1 = (φ q).1 := hσ.1
    have hz : divisorZeroIndex₀_val p.1 = divisorZeroIndex₀_val q.1 := by
      simpa [φ] using congrArg Subtype.val hzS
    apply Subtype.ext
    apply Subtype.ext
    apply Sigma.ext
    · exact hz
    · simpa [φ] using hσ.2
  have hcard_le :
      Fintype.card {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ R} ≤ Fintype.card T :=
    Fintype.card_le_of_injective φ hφ_inj
  have hT_card :
      (Fintype.card T : ℝ) =
        (S.sum fun z : ℂ => (Int.toNat (D z) : ℝ)) := by
    classical
    have hNat :
        Fintype.card T = ∑ z : S, Int.toNat (D z.1) := by
      have h1 :
          Fintype.card T = ∑ z : S, Fintype.card (Fin (Int.toNat (D z.1))) := by
        change Fintype.card (Sigma (fun z : S => Fin (Int.toNat (D z.1))))
            = ∑ z : S, Fintype.card (Fin (Int.toNat (D z.1)))
        exact (Fintype.card_sigma (ι := S) (α := fun z : S => Fin (Int.toNat (D z.1))))
      simpa using h1
    have hR :
        (Fintype.card T : ℝ) = ∑ z : S, (Int.toNat (D z.1) : ℝ) := by
      exact_mod_cast hNat
    have hR' :
        (Fintype.card T : ℝ) = S.attach.sum (fun z : S => (Int.toNat (D z.1) : ℝ)) := by
      simpa [Finset.univ_eq_attach] using hR
    calc
      (Fintype.card T : ℝ) = S.attach.sum (fun z : S => (Int.toNat (D z.1) : ℝ)) := hR'
      _ = S.sum (fun z : ℂ => (Int.toNat (D z) : ℝ)) := by
            -- `S.attach.sum (fun z => f z.1) = S.sum f`
            simpa using (Finset.sum_attach (s := S) (f := fun z : ℂ => (Int.toNat (D z) : ℝ)))
  have htoNat_le : ∀ z ∈ S, (Int.toNat (D z) : ℝ) ≤ (D z : ℝ) := by
    intro z hz
    have hDz_nonneg : 0 ≤ D z := by simpa [D] using hDnonneg z
    have hEqZ : ((Int.toNat (D z) : ℕ) : ℤ) = D z := by
      simpa using (Int.toNat_of_nonneg hDz_nonneg)
    have hEqR : (Int.toNat (D z) : ℝ) = (D z : ℝ) := by
      exact_mod_cast hEqZ
    exact le_of_eq hEqR
  calc
    (Nat.card {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ R} : ℝ)
        = (Fintype.card {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ R} : ℝ) := by
          simp [Nat.card_eq_fintype_card]
    _ ≤ (Fintype.card T : ℝ) := by exact_mod_cast hcard_le
    _ = S.sum (fun z : ℂ => (Int.toNat (D z) : ℝ)) := hT_card
    _ ≤ S.sum (fun z : ℂ => (D z : ℝ)) := by
      refine Finset.sum_le_sum ?_
      intro z hz
      exact htoNat_le z hz
    _ = ((((Function.locallyFinsuppWithin.finiteSupport
              (Function.locallyFinsuppWithin.toClosedBall R
                (MeromorphicOn.divisor f (Set.univ : Set ℂ)))
              (isCompact_closedBall (0 : ℂ) |R|)).toFinset).filter fun z : ℂ => z ≠ 0).sum
          fun z : ℂ => (MeromorphicOn.divisor f (Set.univ : Set ℂ) z : ℝ)) := by
      rfl

/-- If `k = ⌊log₂ (x / r₀)⌋`, then `r₀ * 2^k` is a lower dyadic bound for `x`. -/
lemma dyadicShell_lower_bound {r0 x : ℝ} {k : ℕ} (hr0 : 0 < r0) (hx : r0 ≤ x)
    (hk : ⌊Real.logb 2 (x / r0)⌋₊ = k) :
    r0 * (2 : ℝ) ^ (k : ℝ) ≤ x := by
  have hr0ne : r0 ≠ 0 := ne_of_gt hr0
  have hx1 : (1 : ℝ) ≤ x / r0 := by
    have : r0 / r0 ≤ x / r0 := div_le_div_of_nonneg_right hx hr0.le
    simpa [hr0ne] using this
  have hle : (2 : ℝ) ^ (k : ℝ) ≤ x / r0 := by
    have := two_pow_floor_logb_le (x := x / r0) hx1
    simpa [hk] using this
  have := mul_le_mul_of_nonneg_left hle hr0.le
  have hxEq : r0 * (x / r0) = x := by
    field_simp [hr0ne]
  simpa [mul_assoc, hxEq] using this

/-- If `k = ⌊log₂ (x / r₀)⌋`, then `x` is bounded by the next dyadic endpoint. -/
lemma dyadicShell_upper_bound {r0 x : ℝ} {k : ℕ} (hr0 : 0 < r0) (hx : r0 ≤ x)
    (hk : ⌊Real.logb 2 (x / r0)⌋₊ = k) :
    x ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1) := by
  have hr0ne : r0 ≠ 0 := ne_of_gt hr0
  have hx1 : (1 : ℝ) ≤ x / r0 := by
    have : r0 / r0 ≤ x / r0 := div_le_div_of_nonneg_right hx hr0.le
    simpa [hr0ne] using this
  have hlt : x / r0 < (2 : ℝ) ^ ((k : ℝ) + 1) := by
    have := lt_two_pow_floor_logb_add_one (x := x / r0) hx1
    simpa [hk] using this
  have := mul_lt_mul_of_pos_left hlt hr0
  have hxEq : r0 * (x / r0) = x := by
    field_simp [hr0ne]
  exact le_of_lt (by simpa [mul_assoc, hxEq] using this)

/-- A dyadic radius `r₀ 2^(k+1)` gives polynomial growth bounded by a geometric term. -/
lemma one_add_abs_two_mul_dyadicRadius_rpow_le {r0 ρ : ℝ} (k : ℕ)
    (hr0 : 0 < r0) (hρ : 0 ≤ ρ) :
    (1 + |2 * (r0 * (2 : ℝ) ^ ((k : ℝ) + 1))|) ^ ρ
      ≤ (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ k := by
  let Rk : ℝ := r0 * (2 : ℝ) ^ ((k : ℝ) + 1)
  have hRk' : |2 * Rk| = 4 * r0 * (2 : ℝ) ^ (k : ℝ) := by
    have hnonneg : 0 ≤ (2 : ℝ) * Rk := by
      have : 0 ≤ Rk := by
        dsimp [Rk]
        exact mul_nonneg hr0.le (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
      nlinarith
    have hmul : (2 : ℝ) * Rk = 4 * r0 * (2 : ℝ) ^ (k : ℝ) := by
      dsimp [Rk]
      calc
        (2 : ℝ) * (r0 * (2 : ℝ) ^ ((k : ℝ) + 1))
            = (2 * r0) * (2 : ℝ) ^ ((k : ℝ) + 1) := by ring
        _ = (2 * r0) * ((2 : ℝ) ^ (k : ℝ) * (2 : ℝ) ^ (1 : ℝ)) := by
              simp [Real.rpow_add, mul_assoc]
        _ = (2 * r0) * ((2 : ℝ) ^ (k : ℝ) * 2) := by simp [Real.rpow_one]
        _ = 4 * r0 * (2 : ℝ) ^ (k : ℝ) := by ring
    calc
      |2 * Rk| = 2 * Rk := abs_of_nonneg hnonneg
      _ = 4 * r0 * (2 : ℝ) ^ (k : ℝ) := hmul
  have hbase :
      (1 + |2 * Rk|) ≤ (1 + 4 * r0) * (2 : ℝ) ^ (k : ℝ) := by
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k : ℝ) := by
      have : (1 : ℝ) ≤ (2 : ℝ) ^ (k : ℕ) := by
        simpa using (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ (2 : ℝ)))
      simpa [Real.rpow_natCast] using this
    have habs :
        1 + |2 * Rk| ≤ (2 : ℝ) ^ (k : ℝ) + (4 * r0) * (2 : ℝ) ^ (k : ℝ) := by
      rw [hRk']
      simpa [add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using
        (add_le_add_right h1 ((4 * r0) * (2 : ℝ) ^ (k : ℝ)))
    have hfac :
        (2 : ℝ) ^ (k : ℝ) + (4 * r0) * (2 : ℝ) ^ (k : ℝ)
          = (1 + 4 * r0) * (2 : ℝ) ^ (k : ℝ) := by
      ring
    exact habs.trans (le_of_eq hfac)
  have hRnonneg : 0 ≤ (1 + |2 * Rk|) := by linarith [abs_nonneg (2 * Rk)]
  have :
      (1 + |2 * Rk|) ^ ρ ≤ ((1 + 4 * r0) * (2 : ℝ) ^ (k : ℝ)) ^ ρ :=
    Real.rpow_le_rpow hRnonneg hbase hρ
  have hsplit :
      ((1 + 4 * r0) * (2 : ℝ) ^ (k : ℝ)) ^ ρ
        = (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ (k : ℝ)) ^ ρ := by
    have h1 : 0 ≤ (1 + 4 * r0) := by nlinarith [hr0.le]
    have h2 : 0 ≤ (2 : ℝ) ^ (k : ℝ) := le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
    simpa using (Real.mul_rpow h1 h2 (z := ρ))
  have hpow : ((2 : ℝ) ^ (k : ℝ)) ^ ρ = ((2 : ℝ) ^ ρ) ^ k := by
    have h2nonneg : (0 : ℝ) ≤ 2 := by norm_num
    calc
      ((2 : ℝ) ^ (k : ℝ)) ^ ρ = (2 : ℝ) ^ ((k : ℝ) * ρ) := by
        simp [Real.rpow_mul]
      _ = ((2 : ℝ) ^ ρ) ^ (k : ℝ) := by
        simpa [mul_comm] using (Real.rpow_mul (x := (2 : ℝ)) (y := ρ) (z := (k : ℝ)) h2nonneg)
      _ = ((2 : ℝ) ^ ρ) ^ k := by
        simp [Real.rpow_natCast]
  calc
    (1 + |2 * (r0 * (2 : ℝ) ^ ((k : ℝ) + 1))|) ^ ρ
        = (1 + |2 * Rk|) ^ ρ := by rfl
    _ ≤ ((1 + 4 * r0) * (2 : ℝ) ^ (k : ℝ)) ^ ρ := this
    _ = (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ (k : ℝ)) ^ ρ := hsplit
    _ = (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ k := by
      simpa [mul_assoc] using congrArg (fun t => (1 + 4 * r0) ^ ρ * t) hpow

/-- A finite shell whose radii are bounded below contributes at most
`card * lower_radius⁻¹ ^ τ` to the inverse-power sum. -/
lemma tsum_inv_rpow_le_card_mul_of_lower_bound {α : Type*} [Fintype α] {a : α → ℝ}
    {R τ : ℝ} (hR : 0 < R) (hτ : 0 < τ) (ha_nonneg : ∀ x, 0 ≤ a x)
    (ha_lower : ∀ x, R ≤ a x) :
    (∑' x : α, (a x)⁻¹ ^ τ) ≤ (Fintype.card α : ℝ) * (R⁻¹ ^ τ) := by
  classical
  have hsum_le :
      (∑ x : α, (a x)⁻¹ ^ τ) ≤ ∑ _x : α, R⁻¹ ^ τ := by
    refine Finset.sum_le_sum ?_
    intro x _hx
    have hinv : (a x)⁻¹ ≤ R⁻¹ := by
      simpa using (inv_anti₀ hR (ha_lower x))
    exact Real.rpow_le_rpow (inv_nonneg.2 (ha_nonneg x)) hinv hτ.le
  simpa [tsum_fintype, Finset.sum_const, nsmul_eq_mul, mul_comm] using hsum_le

/-- Inverse powers of dyadic radii split into the initial radius and a geometric factor. -/
lemma inv_dyadicRadius_rpow_eq (r0 τ : ℝ) (k : ℕ) (hr0 : 0 ≤ r0) :
    (r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ =
      (r0⁻¹ : ℝ) ^ τ * ((2 : ℝ) ^ (-τ)) ^ k := by
  have h2k_nonneg : 0 ≤ (2 : ℝ) ^ (k : ℝ) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
  calc
    (r0 * (2 : ℝ) ^ (k : ℝ))⁻¹ ^ τ =
        (r0 * (2 : ℝ) ^ (k : ℝ)) ^ (-τ) := by
      simpa using (Real.rpow_neg_eq_inv_rpow (r0 * (2 : ℝ) ^ (k : ℝ)) τ).symm
    _ = r0 ^ (-τ) * (((2 : ℝ) ^ (k : ℝ)) ^ (-τ)) := by
      simpa using (Real.mul_rpow hr0 h2k_nonneg (z := -τ))
    _ = (r0⁻¹ : ℝ) ^ τ * ((2 : ℝ) ^ (-τ)) ^ k := by
      have hr0' : r0 ^ (-τ) = (r0⁻¹ : ℝ) ^ τ := by
        simp [Real.rpow_neg_eq_inv_rpow]
      have h2' : ((2 : ℝ) ^ (k : ℝ)) ^ (-τ) = ((2 : ℝ) ^ (-τ)) ^ k := by
        have h2nonneg : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
        calc
          ((2 : ℝ) ^ (k : ℝ)) ^ (-τ) = (2 : ℝ) ^ ((k : ℝ) * (-τ)) := by
            exact (Real.rpow_mul (x := (2 : ℝ)) (y := (k : ℝ)) (z := -τ)
              h2nonneg).symm
          _ = (2 : ℝ) ^ ((-τ) * (k : ℝ)) := by ring_nf
          _ = ((2 : ℝ) ^ (-τ)) ^ (k : ℝ) := by
            exact Real.rpow_mul (x := (2 : ℝ)) (y := -τ) (z := (k : ℝ)) h2nonneg
          _ = ((2 : ℝ) ^ (-τ)) ^ k := by
            simp [Real.rpow_natCast]
      calc
        r0 ^ (-τ) * (((2 : ℝ) ^ (k : ℝ)) ^ (-τ))
            = (r0⁻¹ : ℝ) ^ τ * (((2 : ℝ) ^ (k : ℝ)) ^ (-τ)) := by
              rw [hr0']
        _ = (r0⁻¹ : ℝ) ^ τ * ((2 : ℝ) ^ (-τ)) ^ k := by
              rw [h2']

-- The dyadic shell estimate combines counting, Cartan avoidance, and rpow arithmetic.
theorem summable_norm_inv_rpow_divisorZeroIndex₀_of_growth {f : ℂ → ℂ} {ρ τ : ℝ}
    (hρ : 0 ≤ ρ) (hτ : ρ < τ) (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    (hgrowth : ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) :
    Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ) := by
  classical
  have hτpos : 0 < τ := lt_of_le_of_lt hρ hτ
  rcases exists_r0_le_norm_divisorZeroIndex₀_val (f := f) hf hnot with ⟨r0, hr0pos, hr0⟩
  have hr0ne : (r0 : ℝ) ≠ 0 := ne_of_gt hr0pos
  let kfun : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℕ :=
    fun p => ⌊Real.logb 2 (‖divisorZeroIndex₀_val p‖ / r0)⌋₊
  let S : ℕ → Set (divisorZeroIndex₀ f (Set.univ : Set ℂ)) :=
    fun k => {p | kfun p = k}
  have hS : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), ∃! k : ℕ, p ∈ S k := by
    intro p
    refine ⟨kfun p, ?_, ?_⟩
    · simp [S]
    · intro k hk
      simpa [S] using hk.symm
  have hnonneg : 0 ≤ fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ := by
    intro p
    exact Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _
  have hSk_summable : ∀ k : ℕ, Summable fun p : S k => ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ := by
    intro k
    haveI : Finite (S k) := by
      have hsub :
          S k ⊆ {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) |
            ‖divisorZeroIndex₀_val p‖ ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1)} := by
        intro p hp
        have hk : kfun p = k := hp
        exact dyadicShell_upper_bound (r0 := r0) (x := ‖divisorZeroIndex₀_val p‖)
          hr0pos (hr0 p) (by simpa [kfun] using hk)
      have hfin :
          ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) |
            ‖divisorZeroIndex₀_val p‖ ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1)} : Set _).Finite := by
        have :
            Metric.closedBall (0 : ℂ) (r0 * (2 : ℝ) ^ ((k : ℝ) + 1)) ⊆
              (Set.univ : Set ℂ) := by
          simp
        simpa using
          (divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ))
            (B := r0 * (2 : ℝ) ^ ((k : ℝ) + 1)) this)
      exact (hfin.subset hsub).to_subtype
    exact Summable.of_finite
  have hshell_summable :
      Summable fun k : ℕ => ∑' p : S k, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ := by
    let q : ℝ := (2 : ℝ) ^ (ρ - τ)
    let qσ : ℝ := (2 : ℝ) ^ (-τ)
    have hq_nonneg : 0 ≤ q := le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
    have hq_lt_one : q < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (x := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
        (sub_neg.2 hτ)
    have hqσ_nonneg : 0 ≤ qσ := le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
    have hqσ_lt_one : qσ < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (x := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
        (by simpa using (neg_neg_of_pos hτpos))
    have hgeom_q : Summable (fun k : ℕ => q ^ k) :=
      summable_geometric_of_lt_one hq_nonneg hq_lt_one
    have hgeom_qσ : Summable (fun k : ℕ => qσ ^ k) :=
      summable_geometric_of_lt_one hqσ_nonneg hqσ_lt_one
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    let Cgrow : ℝ := Classical.choose hgrowth
    let Ctrail : ℝ := |Real.log ‖meromorphicTrailingCoeffAt f 0‖|
    let A : ℝ := ((Cgrow / Real.log 2) * (1 + 4 * r0) ^ ρ) * (r0⁻¹) ^ τ
    let B : ℝ := ((Ctrail / Real.log 2) + 1) * (r0⁻¹) ^ τ
    have htend : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
    have hEvent : ∀ᶠ n in atTop, (1 / r0) ≤ (2 : ℝ) ^ n :=
      (tendsto_atTop.1 htend) (1 / r0)
    rcases (eventually_atTop.1 hEvent) with ⟨k0, hk0⟩
    let A0 : ℝ := A * q ^ k0
    let B0 : ℝ := B * qσ ^ k0
    have hmajor : Summable (fun k : ℕ => A0 * q ^ k + B0 * qσ ^ k) :=
      (hgeom_q.mul_left A0).add (hgeom_qσ.mul_left B0)
    have hshell_summable_shift :
        Summable fun k : ℕ => ∑' p : S (k + k0), ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ := by
      refine hmajor.of_nonneg_of_le
        (fun k => by
          have : ∀ p : S (k + k0), 0 ≤ ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ := by
            intro p; exact Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _
          exact tsum_nonneg this)
        (fun k => by
          let kk : ℕ := k + k0
          let rk : ℝ := r0 * (2 : ℝ) ^ (kk : ℝ)
          let Rk : ℝ := r0 * (2 : ℝ) ^ ((kk : ℝ) + 1)
          have hrk_pos : 0 < rk := mul_pos hr0pos (Real.rpow_pos_of_pos (by norm_num) _)
          have hrk0 : 0 ≤ rk := le_of_lt hrk_pos
          haveI : Finite (S kk) := by
            have hsub :
                S kk ⊆ {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) |
                  ‖divisorZeroIndex₀_val p‖ ≤ Rk} := by
              intro p hp
              have hk' : kfun p = kk := hp
              simpa [Rk] using
                (dyadicShell_upper_bound (r0 := r0) (x := ‖divisorZeroIndex₀_val p‖)
                  hr0pos (hr0 p) (by simpa [kfun] using hk'))
            have hfin :
                ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) |
                    ‖divisorZeroIndex₀_val p‖ ≤ Rk} : Set _).Finite := by
              have : Metric.closedBall (0 : ℂ) Rk ⊆ (Set.univ : Set ℂ) := by simp
              simpa using
                (divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ))
                  (B := Rk) this)
            exact (hfin.subset hsub).to_subtype
          haveI : Fintype (S kk) := Fintype.ofFinite (S kk)
          have hk_upper : ∀ p : S kk, ‖divisorZeroIndex₀_val p.1‖ ≤ Rk := by
            intro p
            have hk' : kfun p.1 = kk := p.2
            simpa [Rk] using
              (dyadicShell_upper_bound (r0 := r0) (x := ‖divisorZeroIndex₀_val p.1‖)
                hr0pos (hr0 p.1) (by simpa [kfun] using hk'))
          have hk_lower : ∀ p : S kk, rk ≤ ‖divisorZeroIndex₀_val p.1‖ := by
            intro p
            have hk' : kfun p.1 = kk := p.2
            simpa [rk] using
              (dyadicShell_lower_bound (r0 := r0) (x := ‖divisorZeroIndex₀_val p.1‖)
                hr0pos (hr0 p.1) (by simpa [kfun] using hk'))
          have htsum_le :
              (∑' p : S kk, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ)
                ≤ (Fintype.card (S kk) : ℝ) * (rk⁻¹ ^ τ) := by
            classical
            exact tsum_inv_rpow_le_card_mul_of_lower_bound
              (a := fun p : S kk => ‖divisorZeroIndex₀_val p.1‖)
              hrk_pos hτpos (fun _ => norm_nonneg _) hk_lower
          have hRk_ge_one : (1 : ℝ) ≤ Rk := by
            have hpow_nat : (1 / r0) ≤ (2 : ℝ) ^ (kk + 1) := by
              have hkk : k0 ≤ kk + 1 := by
                simp [kk, Nat.add_assoc, Nat.add_comm]
              exact hk0 (kk + 1) hkk
            have hpow_rpow : (1 / r0) ≤ (2 : ℝ) ^ ((kk : ℝ) + 1) := by
              have hcast : (2 : ℝ) ^ ((kk : ℝ) + 1) = (2 : ℝ) ^ (kk + 1) := by
                calc
                  (2 : ℝ) ^ ((kk : ℝ) + 1) = (2 : ℝ) ^ ((kk + 1 : ℕ) : ℝ) := by
                    simp [Nat.cast_add, Nat.cast_one]
                  _ = (2 : ℝ) ^ (kk + 1) := by
                    simpa using (Real.rpow_natCast (2 : ℝ) (kk + 1))
              simpa [hcast] using hpow_nat
            have : (r0 * (1 / r0) : ℝ) ≤ r0 * (2 : ℝ) ^ ((kk : ℝ) + 1) :=
              mul_le_mul_of_nonneg_left hpow_rpow hr0pos.le
            simpa [Rk, one_div, hr0ne, mul_assoc] using this
          have hmass_le_growth :
              ((((Function.locallyFinsuppWithin.finiteSupport
                        (Function.locallyFinsuppWithin.toClosedBall Rk
                          (MeromorphicOn.divisor f (Set.univ : Set ℂ)))
                        (isCompact_closedBall (0 : ℂ) |Rk|)).toFinset).filter
                    fun z : ℂ => z ≠ 0).sum
                  fun z : ℂ => (MeromorphicOn.divisor f (Set.univ : Set ℂ) z : ℝ))
                ≤ (Cgrow * (1 + |2 * Rk|) ^ ρ + Ctrail) / (Real.log 2) := by
            simpa [Cgrow, Ctrail] using
              (sum_divisor_closedBall_le_of_growth (f := f) (ρ := ρ) hf hgrowth
                (R := Rk) hRk_ge_one)
          have hcard_le_mass :
              (Fintype.card (S kk) : ℝ) ≤
                ((((Function.locallyFinsuppWithin.finiteSupport
                        (Function.locallyFinsuppWithin.toClosedBall Rk
                          (MeromorphicOn.divisor f (Set.univ : Set ℂ)))
                        (isCompact_closedBall (0 : ℂ) |Rk|)).toFinset).filter
                    fun z : ℂ => z ≠ 0).sum
                    fun z : ℂ => (MeromorphicOn.divisor f (Set.univ : Set ℂ) z : ℝ)) := by
            classical
            let Aball : Type :=
              {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) // ‖divisorZeroIndex₀_val p‖ ≤ Rk}
            haveI : Fintype Aball := by
              classical
              have : Finite Aball := by
                have : Metric.closedBall (0 : ℂ) Rk ⊆ (Set.univ : Set ℂ) := by simp
                simpa using
                  (finite_divisorZeroIndex₀_subtype_norm_le (f := f)
                    (U := (Set.univ : Set ℂ)) (B := Rk) this)
              exact Fintype.ofFinite _
            have hinj :
                Function.Injective (fun p : S kk => (⟨p.1, hk_upper p⟩ : Aball)) := by
              intro p q hpq
              apply Subtype.ext
              exact congrArg (fun x : Aball => x.1) hpq
            have hcard_le : Fintype.card (S kk) ≤ Fintype.card Aball :=
              Fintype.card_le_of_injective _ hinj
            have hRk_lower : r0 ≤ Rk := by
              dsimp [Rk]
              have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ ((kk : ℝ) + 1) :=
                Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) (by linarith)
              nlinarith [hr0pos.le, hpow]
            have hAball :
                (Nat.card Aball : ℝ) ≤
                  ((((Function.locallyFinsuppWithin.finiteSupport
                          (Function.locallyFinsuppWithin.toClosedBall Rk
                            (MeromorphicOn.divisor f (Set.univ : Set ℂ)))
                          (isCompact_closedBall (0 : ℂ) |Rk|)).toFinset).filter
                      fun z : ℂ => z ≠ 0).sum
                      fun z : ℂ => (MeromorphicOn.divisor f (Set.univ : Set ℂ) z : ℝ)) :=
              card_shell_le_sum_divisor_closedBall (f := f) hf hnot (r0 := r0)
                (R := Rk) hr0pos hRk_lower
            calc
              (Fintype.card (S kk) : ℝ) ≤ (Fintype.card Aball : ℝ) := by exact_mod_cast hcard_le
              _ = (Nat.card Aball : ℝ) := by simp [Nat.card_eq_fintype_card]
              _ ≤ _ := hAball
          have htsum' :
              (∑' p : S kk, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ)
                ≤ ((Cgrow * (1 + |2 * Rk|) ^ ρ + Ctrail) / (Real.log 2)) * (rk⁻¹ ^ τ) := by
            have hcard_le_growth :
                (Fintype.card (S kk) : ℝ) ≤
                  (Cgrow * (1 + |2 * Rk|) ^ ρ + Ctrail) / (Real.log 2) :=
              le_trans hcard_le_mass hmass_le_growth
            have :=
              mul_le_mul_of_nonneg_right hcard_le_growth
                (Real.rpow_nonneg (inv_nonneg.2 hrk0) τ)
            exact le_trans htsum_le this
          have hpow_bound :
              (1 + |2 * Rk|) ^ ρ ≤ (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ kk := by
            simpa [Rk] using
              one_add_abs_two_mul_dyadicRadius_rpow_le (r0 := r0) (ρ := ρ) kk hr0pos hρ
          have hr0Inv_nonneg : 0 ≤ (r0⁻¹ : ℝ) ^ τ := by
            exact Real.rpow_nonneg (inv_nonneg.2 hr0pos.le) _
          have hmain :
              (∑' p : S kk, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ) ≤ A * q ^ kk + B * qσ ^ kk := by
            have hsplit' :
                ((Cgrow * (1 + |2 * Rk|) ^ ρ + Ctrail) / (Real.log 2)) * (rk⁻¹ ^ τ)
                  ≤ ((Cgrow / Real.log 2) * ((1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ kk)) * (rk⁻¹ ^ τ)
                    + ((Ctrail / Real.log 2) * (rk⁻¹ ^ τ)) := by
              have hmul :
                  Cgrow * (1 + |2 * Rk|) ^ ρ ≤ Cgrow * ((1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ kk) :=
                mul_le_mul_of_nonneg_left hpow_bound (le_of_lt (Classical.choose_spec hgrowth).1)
              have hnum :
                  (Cgrow * (1 + |2 * Rk|) ^ ρ + Ctrail)
                    ≤ (Cgrow * ((1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ kk) + Ctrail) :=
                add_le_add hmul (le_rfl : Ctrail ≤ Ctrail)
              have hdiv :
                  (Cgrow * (1 + |2 * Rk|) ^ ρ + Ctrail) / (Real.log 2)
                    ≤ (Cgrow * ((1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ kk) + Ctrail) / (Real.log 2) :=
                div_le_div_of_nonneg_right hnum (le_of_lt hlog2pos)
              have hmul' :=
                mul_le_mul_of_nonneg_right hdiv (Real.rpow_nonneg (inv_nonneg.2 hrk0) τ)
              have hdecomp :
                  ((Cgrow * ((1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ kk) + Ctrail) /
                      (Real.log 2)) * (rk⁻¹ ^ τ)
                    =
                    ((Cgrow / Real.log 2) *
                        ((1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ kk)) * (rk⁻¹ ^ τ)
                      + ((Ctrail / Real.log 2) * (rk⁻¹ ^ τ)) := by
                simp [div_eq_mul_inv, mul_add, mul_assoc, mul_left_comm, mul_comm]
              exact le_trans hmul' (le_of_eq hdecomp)
            have htsum'' : (∑' p : S kk, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ)
                ≤ ((Cgrow * (1 + |2 * Rk|) ^ ρ + Ctrail) / (Real.log 2)) * (rk⁻¹ ^ τ) := htsum'
            have hpre :=
              le_trans htsum'' (le_trans (le_of_eq rfl) hsplit')
            have hrk_inv : rk⁻¹ ^ τ = (r0⁻¹ : ℝ) ^ τ * (qσ ^ kk) := by
              simpa [rk, qσ] using
                inv_dyadicRadius_rpow_eq (r0 := r0) (τ := τ) kk hr0pos.le
            have hq_fac : q = ((2 : ℝ) ^ ρ) * qσ := by
              have h2pos : (0 : ℝ) < (2 : ℝ) := by norm_num
              calc
                q = (2 : ℝ) ^ (ρ - τ) := by rfl
                _ = (2 : ℝ) ^ (ρ + (-τ)) := by ring_nf
                _ = (2 : ℝ) ^ ρ * (2 : ℝ) ^ (-τ) := by
                      simp [Real.rpow_add h2pos]
                _ = ((2 : ℝ) ^ ρ) * qσ := by rfl
            have hq_pow : q ^ kk = ((2 : ℝ) ^ ρ) ^ kk * (qσ ^ kk) := by
              simp [hq_fac, mul_pow]
            have hAterm :
                ((Cgrow / Real.log 2) * ((1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ kk)) * (rk⁻¹ ^ τ)
                  = A * q ^ kk := by
              dsimp [A]
              rw [hrk_inv, hq_pow]
              ac_rfl
            have hBterm :
                ((Ctrail / Real.log 2) * (rk⁻¹ ^ τ)) ≤ B * qσ ^ kk := by
              dsimp [B]
              rw [hrk_inv]
              have hcoeff : (Ctrail / Real.log 2) ≤ (Ctrail / Real.log 2) + 1 := by linarith
              have hmul :
                  (Ctrail / Real.log 2) * ((r0⁻¹ : ℝ) ^ τ)
                    ≤ ((Ctrail / Real.log 2) + 1) * ((r0⁻¹ : ℝ) ^ τ) := by
                exact mul_le_mul_of_nonneg_right hcoeff hr0Inv_nonneg
              have hqσpow_nonneg : 0 ≤ qσ ^ kk := pow_nonneg hqσ_nonneg _
              have := mul_le_mul_of_nonneg_right hmul hqσpow_nonneg
              simpa [mul_assoc, mul_left_comm, mul_comm] using this
            have hpost :
                (∑' p : S kk, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ)
                  ≤ A * q ^ kk + B * qσ ^ kk := by
              have hAB :
                  ((Cgrow / Real.log 2) *
                      ((1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ kk)) * (rk⁻¹ ^ τ)
                    + ((Ctrail / Real.log 2) * (rk⁻¹ ^ τ))
                  ≤ A * q ^ kk + B * qσ ^ kk := by
                have hA :
                    ((Cgrow / Real.log 2) *
                        ((1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ kk)) * (rk⁻¹ ^ τ)
                    ≤ A * q ^ kk := by
                  simp [hAterm]
                have hB : ((Ctrail / Real.log 2) * (rk⁻¹ ^ τ)) ≤ B * qσ ^ kk := hBterm
                have := add_le_add hA hB
                simpa [add_assoc, add_left_comm, add_comm] using this
              exact hpre.trans (by
                simpa [add_assoc, add_left_comm, add_comm] using hAB)
            exact hpost
          have : A * q ^ kk + B * qσ ^ kk = A0 * q ^ k + B0 * qσ ^ k := by
            have hAshift : A * q ^ kk = A0 * q ^ k := by
              dsimp [A0, kk]
              rw [pow_add]
              ac_rfl
            have hBshift : B * qσ ^ kk = B0 * qσ ^ k := by
              dsimp [B0, kk]
              rw [pow_add]
              ac_rfl
            simp [hAshift, hBshift]
          simpa [kk] using (hmain.trans_eq this)
        )
    exact (summable_nat_add_iff k0).1 hshell_summable_shift
  have hpart :=
    (summable_partition (f := fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
        ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ) hnonneg (s := S) hS)
  exact (hpart.2 ⟨hSk_summable, hshell_summable⟩)

/-- Natural-power form of the divisor summability theorem. -/
theorem summable_norm_inv_pow_divisorZeroIndex₀_of_growth {f : ℂ → ℂ} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    (hgrowth : ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) :
    Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (Nat.floor ρ + 1)) := by
  classical
  have hτ : ρ < (Nat.floor ρ + 1 : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one (a := ρ))
  have hs :=
    summable_norm_inv_rpow_divisorZeroIndex₀_of_growth (f := f) (ρ := ρ)
      (τ := (Nat.floor ρ + 1 : ℝ)) hρ hτ hf hnot hgrowth
  exact hs.congr fun p => by
    have hcast : ((Nat.floor ρ : ℝ) + 1) = ((Nat.floor ρ + 1 : ℕ) : ℝ) := by
      norm_num
    rw [hcast, Real.rpow_natCast]

end Complex.Hadamard
