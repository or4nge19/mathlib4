/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Complex.HadamardFactorization.Summability
public import Mathlib.Analysis.Complex.CartanBound
public import Mathlib.Analysis.Complex.CartanInverseFactorBound
public import Mathlib.Analysis.Complex.CartanMajorantBound
public import Mathlib.Analysis.Complex.CartanProductBound
public import Mathlib.Analysis.Complex.ExpPoly.Growth

/-!
## Intrinsic Hadamard factorization from a logarithmic growth bound

This file contains the theorem-layer argument which turns the Hadamard quotient and divisor
summability machinery from `HadamardFactorization` into the growth-form Hadamard factorization.
-/

@[expose] public section

noncomputable section

open Set Filter Asymptotics
open scoped Topology BigOperators

namespace Complex.Hadamard

/-- A midpoint between `ρ` and `⌊ρ⌋ + 1` has the same floor as `ρ`. -/
lemma exists_between_self_and_floor_add_one_same_floor {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∃ τ : ℝ,
      ρ < τ ∧ τ < (Nat.floor ρ + 1 : ℝ) ∧ 0 ≤ τ ∧ Nat.floor τ = Nat.floor ρ := by
  let m : ℕ := Nat.floor ρ
  let τ : ℝ := (ρ + (m + 1 : ℝ)) / 2
  have hτ : ρ < τ := by
    have hm : ρ < (m + 1 : ℝ) := by
      simpa [m] using (Nat.lt_floor_add_one (a := ρ))
    dsimp [τ]
    linarith
  have hτ_lt : τ < (m + 1 : ℝ) := by
    have hm : ρ < (m + 1 : ℝ) := by
      simpa [m] using (Nat.lt_floor_add_one (a := ρ))
    dsimp [τ]
    linarith
  have hτ_nonneg : 0 ≤ τ := le_trans hρ (le_of_lt hτ)
  have hfloorτ : Nat.floor τ = m := by
    have hm_le_ρ : (m : ℝ) ≤ ρ := by
      have := Nat.floor_le hρ
      simpa [m] using this
    have hm_le_τ : (m : ℝ) ≤ τ := le_trans hm_le_ρ (le_of_lt hτ)
    have hτ_lt_m1 : τ < (m : ℝ) + 1 := by
      simpa [add_assoc, add_comm, add_left_comm] using hτ_lt
    exact (Nat.floor_eq_iff hτ_nonneg).2 ⟨hm_le_τ, hτ_lt_m1⟩
  exact ⟨τ, hτ, by simpa [m] using hτ_lt, hτ_nonneg, by simpa [m] using hfloorτ⟩

/-- An exponential bound with exponent `ρ` weakens to any larger exponent on bases at least `1`. -/
lemma norm_le_exp_mul_rpow_of_exponent_le {α E : Type*} [SeminormedAddCommGroup E]
    {f : α → E} {r : α → ℝ} {C ρ τ : ℝ} (hC : 0 ≤ C)
    (hr : ∀ x, 1 ≤ r x) (hρτ : ρ ≤ τ)
    (hbound : ∀ x, ‖f x‖ ≤ Real.exp (C * (r x) ^ ρ)) :
    ∀ x, ‖f x‖ ≤ Real.exp (C * (r x) ^ τ) := by
  intro x
  refine (hbound x).trans (Real.exp_le_exp.2 ?_)
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (hr x) hρτ) hC

/-- A logarithmic growth bound gives a pointwise exponential norm bound after weakening the
exponent. -/
lemma norm_le_exp_mul_rpow_of_log_growth {α E : Type*} [SeminormedAddCommGroup E]
    {f : α → E} {r : α → ℝ} {C ρ τ : ℝ} (hC : 0 ≤ C)
    (hr : ∀ x, 1 ≤ r x) (hρτ : ρ ≤ τ)
    (hlog : ∀ x, Real.log (1 + ‖f x‖) ≤ C * (r x) ^ ρ) :
    ∀ x, ‖f x‖ ≤ Real.exp (C * (r x) ^ τ) := by
  intro x
  have hpow : (r x) ^ ρ ≤ (r x) ^ τ :=
    Real.rpow_le_rpow_of_exponent_le (hr x) hρτ
  have hlogτ : Real.log (1 + ‖f x‖) ≤ C * (r x) ^ τ :=
    (hlog x).trans (mul_le_mul_of_nonneg_left hpow hC)
  exact Real.le_exp_of_log_one_add_le (norm_nonneg (f x)) hlogτ

/-- Convert a pointwise exponential norm bound into a logarithmic growth bound. -/
lemma log_growth_of_norm_le_exp_mul_rpow {α E : Type*} [SeminormedAddCommGroup E]
    {f : α → E} {r : α → ℝ} {C τ : ℝ} (hC : 0 < C) (hτ : 0 ≤ τ)
    (hr : ∀ x, 1 ≤ r x) (hbound : ∀ x, ‖f x‖ ≤ Real.exp (C * (r x) ^ τ)) :
    ∃ C' > 0, ∀ x, Real.log (1 + ‖f x‖) ≤ C' * (r x) ^ τ := by
  refine ⟨C + Real.log 2, by
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith, ?_⟩
  intro x
  have hX : (1 : ℝ) ≤ (r x) ^ τ := Real.one_le_rpow (hr x) hτ
  have hB : 0 ≤ C * (r x) ^ τ :=
    mul_nonneg hC.le (Real.rpow_nonneg (le_trans zero_le_one (hr x)) _)
  have hlog :
      Real.log (1 + ‖f x‖) ≤ C * (r x) ^ τ + Real.log 2 :=
    Real.log_one_add_le_add_log_two_of_le_exp (norm_nonneg _) hB (hbound x)
  have hlog2_nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith [hlog, hX, hlog2_nonneg]

/-- If `r ≤ 2 * max x 1`, then `1 + r` is bounded by a fixed multiple of `1 + x`. -/
lemma one_add_le_three_mul_one_add_of_le_two_mul_max {x r : ℝ} (hx : 0 ≤ x)
    (hr : r ≤ 2 * max x 1) :
    1 + r ≤ 3 * (1 + x) := by
  have hmax : max x 1 ≤ 1 + x := by
    exact max_le_iff.2 ⟨by linarith, by linarith⟩
  nlinarith

/-- The Hadamard quotient inherits a finite-order exponential norm bound. -/
theorem hadamardQuotient_norm_le_exp_rpow_of_growth {f H : ℂ → ℂ} {ρ τ : ℝ} {m : ℕ}
    (hρ : 0 ≤ ρ) (hmρ : (m : ℝ) ≤ ρ) (hτ : ρ < τ) (hτ_lt : τ < (m + 1 : ℝ))
    (hτ_nonneg : 0 ≤ τ) (hentire : Differentiable ℂ f) (hH_entire : Differentiable ℂ H)
    (hnot : ∃ z : ℂ, f z ≠ 0)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (hgrowth : ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ)
    (hfactor : ∀ z : ℂ,
      f z =
        H z * z ^ analyticOrderNatAt f 0 *
          divisorCanonicalProduct m f (Set.univ : Set ℂ) z) :
    ∃ C > 0, ∀ z : ℂ, ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ) := by
  rcases hgrowth with ⟨Cf, hCfpos, hCf⟩
  have hsumτ :
      Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
        ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ) :=
    summable_norm_inv_rpow_divisorZeroIndex₀_of_growth (f := f) (ρ := ρ) (τ := τ)
      hρ hτ hentire hnot ⟨Cf, hCfpos, hCf⟩
  let Sτ : ℝ := ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ
  have hSτ_nonneg : 0 ≤ Sτ := tsum_nonneg fun _ =>
    Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _
  let Cprod : ℝ := ((CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ + 3) * (Sτ + 1)
  have hCprod_nonneg : 0 ≤ Cprod := by
    have hS : 0 ≤ Sτ + 1 := by linarith [hSτ_nonneg]
    have hA : 0 ≤ (CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ + 3 := by
      have hCφ : 0 ≤ CartanBound.Cφ := le_of_lt CartanBound.Cφ_pos
      have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
      have h4τ : 0 ≤ (4 : ℝ) ^ τ := by positivity
      nlinarith [hCφ, hm0, h4τ]
    simpa [Cprod] using mul_nonneg hA hS
  have hf_boundτ : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (Cf * (1 + ‖z‖) ^ τ) :=
    norm_le_exp_mul_rpow_of_log_growth
      (f := f) (r := fun z : ℂ => 1 + ‖z‖) (C := Cf) (ρ := ρ) (τ := τ)
      hCfpos.le (fun z => by linarith [norm_nonneg z]) (le_of_lt hτ) hCf
  refine ⟨(Cf + Cprod + 10) * (3 : ℝ) ^ τ, by
    have h3τ : 0 < (3 : ℝ) ^ τ := by positivity
    nlinarith [hCfpos, hCprod_nonneg, h3τ], ?_⟩
  intro z
  let R : ℝ := max ‖z‖ 1
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hRle : (1 : ℝ) ≤ R := le_max_right _ _
  let smallSet : Set (divisorZeroIndex₀ f (Set.univ : Set ℂ)) :=
    {p | ‖divisorZeroIndex₀_val p‖ ≤ 4 * R}
  have hsmall_fin : smallSet.Finite := by
    have : Metric.closedBall (0 : ℂ) (4 * R) ⊆ (Set.univ : Set ℂ) := by simp
    simpa [smallSet] using
      (divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ))
        (B := 4 * R) this)
  let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
  let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀_val p‖
  have ha_pos : ∀ p ∈ small, 0 < a p := by
    intro p hp
    exact norm_pos_iff.2 (divisorZeroIndex₀_val_ne_zero p)
  let bad : Finset ℝ := small.image a
  rcases CartanBound.exists_radius_Ioc_sum_mul_phi_div_le_Cφ_mul_sum_avoid
      (s := small) (w := fun _ => (1 : ℝ)) (a := a)
      (hw := by intro _ _; norm_num) (ha := ha_pos) (bad := bad) (R := R) hRpos with
    ⟨r, hr_mem, hr_not_bad, hr_phi⟩
  have hR_le_r : R ≤ r := le_of_lt hr_mem.1
  have hr_le_2R : r ≤ 2 * R := hr_mem.2
  have hrpos : 0 < r := lt_of_lt_of_le hRpos hR_le_r
  have hcircle :
      ∀ u : ℂ, ‖u‖ = r → ‖H u‖ ≤ Real.exp ((Cf + Cprod + 10) * (1 + r) ^ τ) := by
    intro u hur
    have hden_eq :
        f u =
          H u * (u ^ analyticOrderNatAt f 0 *
            divisorCanonicalProduct m f (Set.univ : Set ℂ) u) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using (hfactor u)
    have hu0 : u ≠ 0 := by
      intro hu0
      subst hu0
      have : (0 : ℝ) = r := by simpa using hur
      exact (ne_of_gt hrpos) this.symm
    have hfu_ne : f u ≠ 0 := by
      have hr_le_4R : r ≤ 4 * R := by nlinarith [hr_le_2R, hRpos]
      have hr_not :
          ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
            ‖divisorZeroIndex₀_val p‖ ≤ 4 * R → r ≠ ‖divisorZeroIndex₀_val p‖ := by
        intro p hpB hEq
        have hp_small : p ∈ small := by
          simpa [small, smallSet] using (hsmall_fin.mem_toFinset.2 hpB)
        have : r ∈ bad := by
          exact Finset.mem_image.2 ⟨p, hp_small, by simpa [a] using hEq.symm⟩
        exact (hr_not_bad this).elim
      exact no_zero_on_sphere_of_forall_val_norm_ne (f := f) hentire hnot
        (B := 4 * R) (r := r) hrpos hr_le_4R hr_not u hur
    have hden_ne :
        (u ^ analyticOrderNatAt f 0 *
          divisorCanonicalProduct m f (Set.univ : Set ℂ) u) ≠ 0 := by
      intro hden0
      have : f u = 0 := by simpa [hden0] using hden_eq
      exact hfu_ne this
    have hHu :
        H u =
          f u / (u ^ analyticOrderNatAt f 0 *
            divisorCanonicalProduct m f (Set.univ : Set ℂ) u) := by
      have :
          (H u *
              (u ^ analyticOrderNatAt f 0 *
                divisorCanonicalProduct m f (Set.univ : Set ℂ) u)) /
            (u ^ analyticOrderNatAt f 0 *
              divisorCanonicalProduct m f (Set.univ : Set ℂ) u) = H u := by
        simpa using (mul_div_cancel_right₀ (H u) hden_ne)
      have :
          f u /
              (u ^ analyticOrderNatAt f 0 *
                divisorCanonicalProduct m f (Set.univ : Set ℂ) u) =
            H u := by
        simpa [hden_eq, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
      exact this.symm
    have hf_u : ‖f u‖ ≤ Real.exp (Cf * (1 + r) ^ τ) := by
      simpa [hur] using hf_boundτ u
    have hden_inv :
        ‖(u ^ analyticOrderNatAt f 0 *
            divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖
          ≤ Real.exp (Cprod * (1 + r) ^ τ) := by
      have hr1 : (1 : ℝ) ≤ r := le_trans hRle hR_le_r
      have hpow_inv_le1 : ‖(u ^ analyticOrderNatAt f 0)⁻¹‖ ≤ 1 := by
        have hinv : (‖u‖ : ℝ)⁻¹ ≤ 1 := by
          have : (1 : ℝ) ≤ ‖u‖ := by simpa [hur] using hr1
          exact inv_le_one_of_one_le₀ this
        have hnn : 0 ≤ (‖u‖ : ℝ)⁻¹ := by positivity
        have : (‖u‖ : ℝ)⁻¹ ^ analyticOrderNatAt f 0 ≤ 1 ^ analyticOrderNatAt f 0 :=
          pow_le_pow_left₀ hnn hinv _
        simpa [norm_inv, norm_pow] using this
      let fac : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ :=
        fun p => weierstrassFactor m (u / divisorZeroIndex₀_val p)
      have hloc :
          HasProdLocallyUniformlyOn
            (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (w : ℂ) =>
              weierstrassFactor m (w / divisorZeroIndex₀_val p))
            (divisorCanonicalProduct m f (Set.univ : Set ℂ))
            (Set.univ : Set ℂ) :=
        hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
      have hprod :
          HasProd fac (divisorCanonicalProduct m f (Set.univ : Set ℂ) u) :=
        hloc.hasProd (by simp : u ∈ (Set.univ : Set ℂ))
      let ap : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀_val p‖
      haveI : DecidablePred (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) => p ∈ small) :=
        Classical.decPred _
      let b : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ :=
        fun p =>
          if hp : p ∈ small then
            CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)
          else
            (2 : ℝ) * (r / ap p) ^ τ
      have hterm : ∀ p, ‖(fac p)⁻¹‖ ≤ Real.exp (b p) := by
        intro p
        by_cases hp : p ∈ small
        · have hval_ne : r ≠ ap p := by
            intro hEq
            have : r ∈ bad := by
              refine Finset.mem_image.2 ⟨p, hp, ?_⟩
              simp [ap, a, hEq]
            exact (hr_not_bad this).elim
          have hval0 : divisorZeroIndex₀_val p ≠ 0 := divisorZeroIndex₀_val_ne_zero p
          have hmτ : (m : ℝ) ≤ τ := le_trans hmρ (le_of_lt hτ)
          have hnear :
              ‖(weierstrassFactor m (u / divisorZeroIndex₀_val p))⁻¹‖
                ≤ Real.exp (CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)) := by
            simpa [ap] using
              (norm_inv_weierstrassFactor_le_exp_near (m := m) (τ := τ) (r := r)
                  (u := u) (a := divisorZeroIndex₀_val p)
                  (hur := hur) (ha := hval0) (hr := by simpa [ap] using hval_ne) hmτ)
          simpa [fac, b, hp] using hnear
        · have hlarge : (4 * R : ℝ) < ap p := by
            have : ¬ap p ≤ 4 * R := by
              intro hle
              have : p ∈ small := by
                simpa [small, smallSet, ap] using (hsmall_fin.mem_toFinset.2 hle)
              exact hp this
            exact lt_of_not_ge this
          have hz' : ‖u / divisorZeroIndex₀_val p‖ ≤ (1 / 2 : ℝ) := by
            have hnorm : ‖u / divisorZeroIndex₀_val p‖ = r / ap p := by
              simp [div_eq_mul_inv, hur, ap, norm_inv]
            rw [hnorm]
            have hap : 0 < ap p := by
              exact norm_pos_iff.2 (divisorZeroIndex₀_val_ne_zero p)
            have hfrac₁ : r / ap p ≤ (2 * R) / ap p :=
              div_le_div_of_nonneg_right hr_le_2R (le_of_lt hap)
            have hfrac₂ : (2 * R) / ap p ≤ (2 * R) / (4 * R) := by
              have h2R0 : 0 ≤ (2 * R : ℝ) := by nlinarith [le_of_lt hRpos]
              exact div_le_div_of_nonneg_left h2R0 (by nlinarith [hRpos]) (le_of_lt hlarge)
            have hRsimp : (2 * R) / (4 * R) = (1 / 2 : ℝ) := by
              have hRne : (R : ℝ) ≠ 0 := ne_of_gt hRpos
              field_simp [hRne]; ring
            exact (hfrac₁.trans hfrac₂).trans_eq hRsimp
          have hτ_le : τ ≤ (m + 1 : ℝ) := le_of_lt hτ_lt
          have hfar :
              ‖(weierstrassFactor m (u / divisorZeroIndex₀_val p))⁻¹‖ ≤
                Real.exp ((2 : ℝ) * (r / ap p) ^ τ) := by
            simpa [ap] using
              (norm_inv_weierstrassFactor_le_exp_far (m := m) (τ := τ) (r := r)
                  (u := u) (a := divisorZeroIndex₀_val p)
                  (hur := hur) (ha := divisorZeroIndex₀_val_ne_zero p) (hz := hz') hτ_le)
          simpa [fac, b, hp] using hfar
      have hb_le :
          ∀ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)),
            (∑ p ∈ s, b p) ≤ Cprod * (1 + r) ^ τ := by
        intro s
        have hsmallSet' :
            smallSet =
              {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) |
                ‖divisorZeroIndex₀_val p‖ ≤ 4 * R} := rfl
        simpa [small, ap, b, Sτ, Cprod, a, hsmallSet'] using
          (Complex.Hadamard.cartan_sum_majorant_le (f := f) (m := m) (τ := τ) (R := R) (r := r)
            (hRpos := hRpos) (hrpos := hrpos) (hR_le_r := hR_le_r) (hτ_nonneg := hτ_nonneg)
            (smallSet := smallSet) (hsmall_fin := hsmall_fin) (hsmallSet := hsmallSet')
            (hsumτ := hsumτ)
            (hr_phi := by
              simpa [one_mul, Finset.sum_const] using hr_phi)
            s)
      have hcprod_inv :
          ‖(divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖ ≤
            Real.exp (Cprod * (1 + r) ^ τ) := by
        refine hasProd_norm_inv_le_exp_of_pointwise_le_exp
          (α := divisorZeroIndex₀ f (Set.univ : Set ℂ)) (fac := fac)
          (F := divisorCanonicalProduct m f (Set.univ : Set ℂ) u)
          hprod (b := b) (B := Cprod * (1 + r) ^ τ) ?_ ?_
        · exact hterm
        · intro s
          exact hb_le s
      have hmul :
          ‖(u ^ analyticOrderNatAt f 0 *
              divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖
            =
          ‖(u ^ analyticOrderNatAt f 0)⁻¹‖ *
            ‖(divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖ := by
        simp [mul_inv_rev, mul_comm]
      rw [hmul]
      have :
          ‖(u ^ analyticOrderNatAt f 0)⁻¹‖ *
              ‖(divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖
            ≤ 1 * Real.exp (Cprod * (1 + r) ^ τ) :=
        mul_le_mul hpow_inv_le1 hcprod_inv (by positivity) (by positivity)
      simpa using this
    have :
        ‖H u‖ ≤
          ‖f u‖ *
            ‖(u ^ analyticOrderNatAt f 0 *
              divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖ := by
      have :
          ‖H u‖ =
            ‖f u /
              (u ^ analyticOrderNatAt f 0 *
                divisorCanonicalProduct m f (Set.univ : Set ℂ) u)‖ := by
        simp [hHu]
      simp [div_eq_mul_inv, norm_inv, this]
    have hmul :
        ‖f u‖ *
            ‖(u ^ analyticOrderNatAt f 0 *
              divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖
          ≤ Real.exp (Cf * (1 + r) ^ τ) * Real.exp (Cprod * (1 + r) ^ τ) :=
      mul_le_mul hf_u hden_inv (by positivity) (by positivity)
    have hexp :
        Real.exp (Cf * (1 + r) ^ τ) * Real.exp (Cprod * (1 + r) ^ τ)
          = Real.exp ((Cf + Cprod) * (1 + r) ^ τ) := by
      simp [Real.exp_add, add_mul, add_comm]
    have : ‖H u‖ ≤ Real.exp ((Cf + Cprod) * (1 + r) ^ τ) :=
      (this.trans hmul).trans_eq hexp
    have hslack :
        Real.exp ((Cf + Cprod) * (1 + r) ^ τ) ≤
          Real.exp ((Cf + Cprod + 10) * (1 + r) ^ τ) := by
      refine Real.exp_le_exp.2 ?_
      have hnn : 0 ≤ (1 + r) ^ τ := by positivity
      nlinarith
    exact this.trans hslack
  have hz_ball : z ∈ Metric.ball (0 : ℂ) r := by
    have : dist z (0 : ℂ) < r := by
      have hzR : ‖z‖ ≤ R := le_max_left _ _
      have : dist z (0 : ℂ) ≤ R := by simpa [dist_zero_right] using hzR
      exact lt_of_le_of_lt this hr_mem.1
    simpa [Metric.ball, dist_zero_right] using this
  have hfront :
      ∀ u : ℂ, u ∈ frontier (Metric.ball (0 : ℂ) r) →
        ‖H u‖ ≤ Real.exp ((Cf + Cprod + 10) * (1 + r) ^ τ) := by
    intro u hu
    have hur : ‖u‖ = r := by
      have hfront' : frontier (Metric.ball (0 : ℂ) r) = Metric.sphere (0 : ℂ) r := by
        simpa using (frontier_ball (x := (0 : ℂ)) (r := r) (by exact (ne_of_gt hrpos)))
      have : u ∈ Metric.sphere (0 : ℂ) r := by simpa [hfront'] using hu
      simpa [Metric.mem_sphere, dist_zero_right] using this
    exact hcircle u hur
  have hball :
      ‖H z‖ ≤ Real.exp ((Cf + Cprod + 10) * (1 + r) ^ τ) := by
    let U : Set ℂ := Metric.ball (0 : ℂ) r
    have hU : Bornology.IsBounded U := Metric.isBounded_ball
    have hd : DiffContOnCl ℂ H U := hH_entire.diffContOnCl
    have hz_cl : z ∈ closure U := subset_closure hz_ball
    have hCfront :
        ∀ w ∈ frontier U, ‖H w‖ ≤ Real.exp ((Cf + Cprod + 10) * (1 + r) ^ τ) := by
      intro w hw
      simpa [U] using hfront w (by simpa [U] using hw)
    simpa [U] using
      (Complex.norm_le_of_forall_mem_frontier_norm_le (f := H) (U := U) hU hd
        hCfront (z := z) hz_cl)
  have hr_le_3 : 1 + r ≤ 3 * (1 + ‖z‖) := by
    exact one_add_le_three_mul_one_add_of_le_two_mul_max (norm_nonneg z)
      (by simpa [R] using hr_le_2R)
  have hpow : (1 + r) ^ τ ≤ (3 : ℝ) ^ τ * (1 + ‖z‖) ^ τ := by
    have hbase : 0 ≤ 1 + r := by linarith [le_of_lt hrpos]
    have := Real.rpow_le_rpow hbase hr_le_3 hτ_nonneg
    have hmul :
        (3 * (1 + ‖z‖)) ^ τ = (3 : ℝ) ^ τ * (1 + ‖z‖) ^ τ := by
      have h3 : 0 ≤ (3 : ℝ) := by norm_num
      have h1 : 0 ≤ (1 + ‖z‖ : ℝ) := by positivity
      simpa [mul_assoc] using
        (Real.mul_rpow (x := (3 : ℝ)) (y := (1 + ‖z‖ : ℝ)) (z := τ) h3 h1)
    simpa [hmul] using this
  have hmain :
      Real.exp ((Cf + Cprod + 10) * (1 + r) ^ τ)
        ≤ Real.exp (((Cf + Cprod + 10) * (3 : ℝ) ^ τ) * (1 + ‖z‖) ^ τ) := by
    refine Real.exp_le_exp.2 ?_
    have hnn : 0 ≤ (Cf + Cprod + 10) := by nlinarith [le_of_lt hCfpos, hCprod_nonneg]
    nlinarith [hpow]
  simpa [mul_assoc] using hball.trans hmain

theorem hadamard_factorization_of_growth {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hentire : Differentiable ℂ f)
    (hnot : ∃ z : ℂ, f z ≠ 0)
    (hgrowth : ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) :
    ∃ (P : Polynomial ℂ),
      P.degree ≤ Nat.floor ρ ∧
      ∀ z : ℂ,
        f z =
          Complex.exp (Polynomial.eval z P) *
            z ^ (analyticOrderNatAt f 0) *
            divisorCanonicalProduct (Nat.floor ρ) f (Set.univ : Set ℂ) z := by
  set m : ℕ := Nat.floor ρ
  have h_sum :
      Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
        ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)) := by
    simpa [m] using
      (summable_norm_inv_pow_divisorZeroIndex₀_of_growth (f := f) (ρ := ρ)
        hρ hentire hnot hgrowth)
  rcases exists_entire_nonzero_hadamardQuotient (m := m) (f := f) hentire hnot h_sum with
    ⟨H, hH_entire, hH_ne, hfactor⟩
  rcases exists_between_self_and_floor_add_one_same_floor hρ with
    ⟨τ, hτ, hτ_lt, hτ_nonneg, hfloorτ'⟩
  have hfloorτ : Nat.floor τ = m := by
    simpa [m] using hfloorτ'
  have hmρ : (m : ℝ) ≤ ρ := by
    have := Nat.floor_le hρ
    simpa [m] using this
  have hH_bound_rpow :
      ∃ C > 0, ∀ z : ℂ, ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ) :=
    hadamardQuotient_norm_le_exp_rpow_of_growth (f := f) (H := H) (ρ := ρ) (τ := τ)
      (m := m) hρ hmρ hτ hτ_lt hτ_nonneg hentire hH_entire hnot h_sum hgrowth hfactor
  have hH_growth_nat :
      ∃ C > 0, ∀ z : ℂ, ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (m + 1)) := by
    rcases hH_bound_rpow with ⟨C, hCpos, hC⟩
    have hweak :
        ∀ z : ℂ, ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (m + 1 : ℝ)) :=
      norm_le_exp_mul_rpow_of_exponent_le
        (f := H) (r := fun z : ℂ => 1 + ‖z‖) hCpos.le
        (fun z => by linarith [norm_nonneg z]) (le_of_lt hτ_lt) hC
    refine ⟨C, hCpos, ?_⟩
    intro z
    have hcast : ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) := by norm_num
    have hpow :
        (1 + ‖z‖) ^ ((m : ℝ) + 1) = (1 + ‖z‖) ^ (m + 1) := by
      rw [hcast]
      exact Real.rpow_natCast (1 + ‖z‖) (m + 1)
    simpa [hpow] using hweak z
  rcases zero_free_polynomial_growth_is_exp_poly (H := H) (n := m + 1)
      hH_entire hH_ne hH_growth_nat with
    ⟨P, hPn, hHP⟩
  have hPnat : P.natDegree ≤ m := by
    have hlog_growth :
        ∃ C > 0, ∀ z : ℂ,
          Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) ≤ C * (1 + ‖z‖) ^ τ := by
      rcases hH_bound_rpow with ⟨C, hCpos, hC⟩
      have hbound :
          ∀ z : ℂ,
            ‖Complex.exp (Polynomial.eval z P)‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ) := by
        intro z
        simpa [hHP z] using (hC z)
      exact log_growth_of_norm_le_exp_mul_rpow
        (f := fun z : ℂ => Complex.exp (Polynomial.eval z P))
        (r := fun z : ℂ => 1 + ‖z‖) hCpos hτ_nonneg
        (fun z => by linarith [norm_nonneg z]) hbound
    have := natDegree_le_floor_of_growth_exp_eval (ρ := τ) hτ_nonneg P hlog_growth
    simpa [hfloorτ] using this
  refine ⟨P, ?_, ?_⟩
  · have : P.degree ≤ m := Polynomial.degree_le_of_natDegree_le hPnat
    simpa [m] using this
  · intro z
    have hH' : H z = Complex.exp (Polynomial.eval z P) := by simpa using (hHP z)
    simpa [hH', mul_assoc, mul_left_comm, mul_comm, m] using (hfactor z)

end Complex.Hadamard
