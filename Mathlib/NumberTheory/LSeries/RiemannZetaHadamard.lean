/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Complex.HadamardFactorization.Order
public import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
public import Mathlib.Analysis.SpecialFunctions.CompletedXi
public import Mathlib.NumberTheory.LSeries.ZetaFiniteOrder
public import Mathlib.NumberTheory.LSeries.RiemannZetaValues


/-!
# Hadamard factorization for the completed Riemann zeta function

This file specializes Tao's finite-order Hadamard factorization theorem
([tao246bComplexAnalysis], Thm. 22)
to the entire completed zeta function `completedRiemannZeta₀` (Λ₀) and to Riemann's entire
`riemannXi`. The analytic input is the order-one bound `completedRiemannZeta₀_order_one` from
`ZetaFiniteOrder`; the product is the divisor-indexed canonical Weierstrass product at genus
`⌊ρ⌋ = 1`, with multiplicities from `MeromorphicOn.divisor`.

Note: `completedRiemannZeta` (Λ with simple poles at `0` and `1`) is a different object; Hadamard
applies to Λ₀.  The negative even integers are the trivial zeros of `riemannZeta`, not zeros of
Λ₀.  Accordingly, the divisor indices in this file remain generic zeros of Λ₀; trivial-zero divisor
API belongs with `riemannZeta` or the removable entire function `(s - 1)ζ(s)`.

`RiemannZetaValues` proves `completedRiemannZeta₀_zero_ne_zero`, using the Euler-Mascheroni
formula for `Λ₀(1)` together with explicit numerical bounds.  Therefore the origin monomial in the
Λ₀ Hadamard product is also removable.

## Main results

* `completedRiemannZeta₀_entireOfOrderAtMost_one` : Λ₀ has order at most one
* `riemannXi_entireOfOrderAtMost_one` : Riemann's entire `ξ` has order at most one
* `analyticOrderNatAt_riemannXi_zero` : the origin monomial in `ξ`'s Hadamard product is absent
* `analyticOrderNatAt_completedRiemannZeta₀_zero` : the origin monomial in Λ₀'s Hadamard product
  is absent
* `completedRiemannZeta₀_hadamard_factorization` : canonical product form over divisor indices
* `completedRiemannZeta₀_hadamard_factorization_no_monomial` : Λ₀ product with the origin monomial
  removed
* `riemannXi_hadamard_factorization` : canonical product form for Riemann's entire `ξ`
* `riemannXi_hadamard_factorization_no_monomial`, `_reindex_no_monomial`,
  `_sequence_no_monomial` : xi products with the origin monomial removed
* `summable_riemannXi_divisorZeroIndex₀_norm_inv_sq` : genus-one summability of xi's nonzero
  zero divisor
* `logDeriv_exp_polynomial`, `logDeriv_weierstrassFactor_one_div` : local log-derivative
  identities needed to turn the product into Kadiri's zero-sum formula
* `logDeriv_divisorCanonicalProduct_one_eq_tsum` : logarithmic derivative of a genus-one
  divisor canonical product as a zero-indexed sum, under the explicit convergence/nonvanishing
  hypotheses needed by `logDeriv_tprod_eq_tsum`
* `logDeriv_riemannXi_divisorCanonicalProduct_one_eq_tsum` and
  `logDeriv_riemannXi_eq_polynomial_derivative_add_tsum` : xi-specialized zero-sum identities
* `exists_riemannXi_logDeriv_eq_polynomial_derivative_add_tsum` : an API-test style composition of
  the xi no-monomial factorization and the zero-sum bridge
* `completedRiemannZeta₀_hadamard_factorization_reindex`, `_sequence` : reindexed enumerations

The analytic chain is `ZetaFiniteOrder` (order-one bound) → `HadamardFactorization/Order`
(`hadamard_factorization_of_order`) → this file.

## References

* [tao246bComplexAnalysis], Theorem 22 for the finite-order Hadamard factorization strategy
* [titchmarsh1986] and [edwards1974] for the classical completed-zeta and ξ-function background
* [boas1954] and [levin1980] for the general finite-order Hadamard product theorem
* [kadiri2005] for the explicit zero-free-region motivation behind the xi/log-derivative bridge

## Tags

Riemann zeta function, Hadamard factorization, canonical product, entire function of finite order
-/

@[expose] public section

noncomputable section

open Complex Set

namespace Riemann

open scoped BigOperators

/-- The completed zeta function `Λ₀` has order at most one. -/
theorem completedRiemannZeta₀_entireOfOrderAtMost_one :
    Complex.Hadamard.EntireOfOrderAtMost (1 : ℝ) completedRiemannZeta₀ := by
  refine ⟨differentiable_completedZeta₀, ?_⟩
  intro ε hε
  simpa [add_comm, add_left_comm, add_assoc] using
    (Complex.completedRiemannZeta₀_order_one ε hε)

/-- A quadratic polynomial factor is absorbed by any positive exponential margin. -/
private lemma sq_le_exp_const_mul_rpow {b r : ℝ} (hb : 0 < b) (hr : 1 ≤ r) :
    r ^ 2 ≤ Real.exp ((4 / b) * r ^ b) := by
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  have hcoeff2 : 0 ≤ (2 / b : ℝ) := by positivity
  have hcoeff4 : 0 ≤ (4 / b : ℝ) := by positivity
  have hlog_le : Real.log r ≤ (2 / b) * r ^ (b / 2) := by
    have hle_exp : (b / 2) * Real.log r ≤ Real.exp ((b / 2) * Real.log r) :=
      Real.le_exp_self _
    calc
      Real.log r = (2 / b) * ((b / 2) * Real.log r) := by
        field_simp [ne_of_gt hb]
      _ ≤ (2 / b) * Real.exp ((b / 2) * Real.log r) :=
        mul_le_mul_of_nonneg_left hle_exp hcoeff2
      _ = (2 / b) * r ^ (b / 2) := by
        simp [Real.rpow_def_of_pos hrpos, mul_comm]
  have hpow_le : r ^ (b / 2) ≤ r ^ b :=
    Real.rpow_le_rpow_of_exponent_le hr (by linarith)
  have hlog_sq :
      Real.log (r ^ 2) ≤ (4 / b) * r ^ b := by
    calc
      Real.log (r ^ 2) = 2 * Real.log r := by
        simp [Real.log_pow]
      _ ≤ 2 * ((2 / b) * r ^ (b / 2)) :=
        mul_le_mul_of_nonneg_left hlog_le (by norm_num)
      _ = (4 / b) * r ^ (b / 2) := by ring
      _ ≤ (4 / b) * r ^ b :=
        mul_le_mul_of_nonneg_left hpow_le hcoeff4
  exact (Real.log_le_iff_le_exp (sq_pos_of_pos hrpos)).mp hlog_sq

/-- The Riemann xi function `ξ` has order at most one. -/
theorem riemannXi_entireOfOrderAtMost_one :
    Complex.Hadamard.EntireOfOrderAtMost (1 : ℝ) riemannXi := by
  refine ⟨differentiable_riemannXi, ?_⟩
  intro ε hε
  rcases completedRiemannZeta₀_entireOfOrderAtMost_one.exists_bound hε with
    ⟨C, hCpos, hΛ⟩
  let b : ℝ := 1 + ε
  let D : ℝ := 4 / b
  let C' : ℝ := C + D + 1
  have hbpos : 0 < b := by dsimp [b]; linarith
  refine ⟨C', by positivity, ?_⟩
  intro z
  let R : ℝ := 1 + ‖z‖
  have hR1 : 1 ≤ R := by dsimp [R]; linarith [norm_nonneg z]
  have hRpos : 0 < R := zero_lt_one.trans_le hR1
  have hRpow1 : 1 ≤ R ^ b :=
    Real.one_le_rpow hR1 hbpos.le
  have hpoly : ‖z * (z - 1)‖ ≤ R ^ 2 := by
    have hz : ‖z‖ ≤ R := by dsimp [R]; linarith [norm_nonneg z]
    have hz1 : ‖z - 1‖ ≤ R := by
      simpa [R] using Complex.norm_sub_one_le_one_add_norm z
    calc
      ‖z * (z - 1)‖ ≤ ‖z‖ * ‖z - 1‖ := norm_mul_le z (z - 1)
      _ ≤ R * R := mul_le_mul hz hz1 (norm_nonneg _) (by positivity)
      _ = R ^ 2 := by ring
  have hquad : R ^ 2 ≤ Real.exp (D * R ^ b) := by
    simpa [D] using sq_le_exp_const_mul_rpow (b := b) (r := R) hbpos hR1
  have hΛz : ‖completedRiemannZeta₀ z‖ ≤ Real.exp (C * R ^ b) := by
    simpa [R, b, add_assoc] using hΛ z
  have hterm :
      ‖z * (z - 1) * completedRiemannZeta₀ z‖ ≤
        Real.exp ((C + D) * R ^ b) := by
    calc
      ‖z * (z - 1) * completedRiemannZeta₀ z‖
          ≤ ‖z * (z - 1)‖ * ‖completedRiemannZeta₀ z‖ := norm_mul_le _ _
      _ ≤ (R ^ 2) * Real.exp (C * R ^ b) :=
          mul_le_mul hpoly hΛz (norm_nonneg _) (by positivity)
      _ ≤ Real.exp (D * R ^ b) * Real.exp (C * R ^ b) :=
          mul_le_mul_of_nonneg_right hquad (by positivity)
      _ = Real.exp ((C + D) * R ^ b) := by
          rw [← Real.exp_add]
          ring_nf
  have hA_nonneg : 0 ≤ (C + D) * R ^ b := by positivity
  have hone_le : (1 : ℝ) ≤ Real.exp ((C + D) * R ^ b) :=
    Real.one_le_exp_iff.mpr hA_nonneg
  have htwo_exp :
      2 * Real.exp ((C + D) * R ^ b) ≤
        Real.exp (((C + D) * R ^ b) + 1) := by
    calc
      2 * Real.exp ((C + D) * R ^ b)
          = Real.exp (Real.log 2) * Real.exp ((C + D) * R ^ b) := by
              have htwo : Real.exp (Real.log 2) = (2 : ℝ) := by
                exact Real.exp_log (by norm_num)
              rw [htwo]
      _ = Real.exp (Real.log 2 + (C + D) * R ^ b) := by
          rw [Real.exp_add]
      _ ≤ Real.exp (((C + D) * R ^ b) + 1) := by
          refine Real.exp_le_exp.2 ?_
          have hlog2 : Real.log 2 ≤ (1 : ℝ) := by
            rw [Real.log_le_iff_le_exp (by norm_num)]
            have h := Real.add_one_le_exp (1 : ℝ)
            norm_num at h
            exact h
          linarith
  have hxi :
      ‖riemannXi z‖ ≤ Real.exp (((C + D) * R ^ b) + 1) := by
    calc
      ‖riemannXi z‖
          = ‖z * (z - 1) * completedRiemannZeta₀ z + 1‖ / 2 := by
              simp [riemannXi]
      _ ≤ (‖z * (z - 1) * completedRiemannZeta₀ z‖ + 1) / 2 := by
          gcongr
          simpa using norm_add_le (z * (z - 1) * completedRiemannZeta₀ z) (1 : ℂ)
      _ ≤ ‖z * (z - 1) * completedRiemannZeta₀ z‖ + 1 := by
          nlinarith [norm_nonneg (z * (z - 1) * completedRiemannZeta₀ z)]
      _ ≤ Real.exp ((C + D) * R ^ b) + 1 := by
          gcongr
      _ ≤ 2 * Real.exp ((C + D) * R ^ b) := by
          linarith
      _ ≤ Real.exp (((C + D) * R ^ b) + 1) := htwo_exp
  exact hxi.trans (Real.exp_le_exp.2 (by
    calc
      ((C + D) * R ^ b) + 1 ≤ ((C + D) * R ^ b) + R ^ b := by
          gcongr
      _ = C' * R ^ b := by
          ring))

/-! ### Kadiri-compatible logarithmic-derivative bridge -/

/-- The genus-one summability condition for the nonzero zero divisor of Riemann's entire `ξ`.

This is the zero-counting input needed for the xi canonical product and its logarithmic derivative,
specialized from the finite-order Hadamard summability theorem. -/
theorem summable_riemannXi_divisorZeroIndex₀_norm_inv_sq :
    Summable (fun p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ) =>
      ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ ^ (2 : ℕ)) := by
  simpa using
    (Complex.Hadamard.EntireOfOrderAtMost.summable_norm_inv_pow_divisorZeroIndex₀
      (ρ := (1 : ℝ)) (f := riemannXi) riemannXi_entireOfOrderAtMost_one
      (by norm_num) riemannXi_nontrivial)

/-- Since `ξ(0) = 1 / 2`, the monomial exponent in the origin-centered Hadamard product is zero. -/
theorem analyticOrderNatAt_riemannXi_zero : analyticOrderNatAt riemannXi 0 = 0 := by
  by_contra h
  have hzero : riemannXi 0 = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero (f := riemannXi) (z₀ := 0) h
  rw [riemannXi_zero] at hzero
  norm_num at hzero

/-- Since `Λ₀(0) ≠ 0`, the monomial exponent in the origin-centered Hadamard product for Λ₀ is
zero. -/
theorem analyticOrderNatAt_completedRiemannZeta₀_zero :
    analyticOrderNatAt completedRiemannZeta₀ 0 = 0 := by
  by_contra h
  have hzero : completedRiemannZeta₀ 0 = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero (f := completedRiemannZeta₀) (z₀ := 0) h
  exact completedRiemannZeta₀_zero_ne_zero hzero

/-- The logarithmic derivative of the exponential of a polynomial is the polynomial derivative. -/
theorem logDeriv_exp_polynomial (P : Polynomial ℂ) (z : ℂ) :
    logDeriv (fun w : ℂ => Complex.exp (Polynomial.eval w P)) z =
      Polynomial.eval z P.derivative := by
  have hderiv :
      deriv (fun w : ℂ => Complex.exp (Polynomial.eval w P)) z =
        Complex.exp (Polynomial.eval z P) * Polynomial.eval z P.derivative := by
    simpa [Function.comp_def, mul_comm] using
      ((Complex.hasDerivAt_exp (Polynomial.eval z P)).comp z (P.hasDerivAt z)).deriv
  rw [logDeriv_apply, hderiv]
  field_simp [Complex.exp_ne_zero (Polynomial.eval z P)]

/-- Genus-one Weierstrass factors contribute the usual `1 / (z - a) + 1 / a` term. -/
theorem logDeriv_weierstrassFactor_one_div {a z : ℂ} (ha : a ≠ 0) (hz : z ≠ a) :
    logDeriv (fun w : ℂ => Complex.weierstrassFactor 1 (w / a)) z =
      1 / (z - a) + 1 / a :=
  Complex.logDeriv_weierstrassFactor_one_div ha hz

/-- The logarithmic derivative of a genus-one divisor canonical product is the expected sum of
zero terms, once the product and the logarithmic-derivative series are known to converge and the
evaluation point is not a zero of the product.

This is the reusable analytic bridge between the Hadamard product and Kadiri-style zero sums. -/
theorem logDeriv_divisorCanonicalProduct_one_eq_tsum
    {f : ℂ → ℂ} {z : ℂ}
    (h_sum : Summable (fun p : Complex.Hadamard.divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ ^ (2 : ℕ)))
    (hz : ∀ p : Complex.Hadamard.divisorZeroIndex₀ f (Set.univ : Set ℂ),
      z ≠ Complex.Hadamard.divisorZeroIndex₀_val p)
    (hm : Summable (fun p : Complex.Hadamard.divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
        1 / Complex.Hadamard.divisorZeroIndex₀_val p))
    (hprod_ne :
      Complex.Hadamard.divisorCanonicalProduct 1 f (Set.univ : Set ℂ) z ≠ 0) :
    logDeriv (Complex.Hadamard.divisorCanonicalProduct 1 f (Set.univ : Set ℂ)) z =
      ∑' p : Complex.Hadamard.divisorZeroIndex₀ f (Set.univ : Set ℂ),
        (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
  let Φ : Complex.Hadamard.divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℂ → ℂ :=
    fun p w => Complex.weierstrassFactor 1 (w / Complex.Hadamard.divisorZeroIndex₀_val p)
  have hf : ∀ p, Φ p z ≠ 0 := by
    intro p
    have hp0 : Complex.Hadamard.divisorZeroIndex₀_val p ≠ 0 :=
      Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p
    refine Complex.weierstrassFactor_ne_zero_of_ne_one 1 ?_
    intro h
    exact hz p ((div_eq_one_iff_eq hp0).1 h)
  have hd : ∀ p, DifferentiableOn ℂ (Φ p) (Set.univ : Set ℂ) := by
    intro p
    exact (Complex.Hadamard.differentiable_weierstrassFactor_divisorZeroIndex₀ 1 p).differentiableOn
  have hm' : Summable fun p => logDeriv (Φ p) z := by
    refine hm.congr ?_
    intro p
    have hp0 : Complex.Hadamard.divisorZeroIndex₀_val p ≠ 0 :=
      Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p
    simpa [Φ] using
      (logDeriv_weierstrassFactor_one_div
        (a := Complex.Hadamard.divisorZeroIndex₀_val p) (z := z) hp0 (hz p)).symm
  have htend : MultipliableLocallyUniformlyOn Φ (Set.univ : Set ℂ) := by
    have hprod :=
      Complex.Hadamard.hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ
        (m := 1) (f := f) h_sum
    simpa [Φ, Complex.Hadamard.divisorCanonicalProduct] using
      hprod.multipliableLocallyUniformlyOn
  have hnez : (∏' p, Φ p z) ≠ 0 := by
    simpa [Φ, Complex.Hadamard.divisorCanonicalProduct] using hprod_ne
  have hlog :
      logDeriv (∏' p, Φ p ·) z = ∑' p, logDeriv (Φ p) z :=
    logDeriv_tprod_eq_tsum (s := (Set.univ : Set ℂ)) isOpen_univ (by simp)
      hf hd hm' htend hnez
  calc
    logDeriv (Complex.Hadamard.divisorCanonicalProduct 1 f (Set.univ : Set ℂ)) z
        = ∑' p, logDeriv (Φ p) z := by
          simpa [Φ, Complex.Hadamard.divisorCanonicalProduct] using hlog
    _ = ∑' p : Complex.Hadamard.divisorZeroIndex₀ f (Set.univ : Set ℂ),
          (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
            1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
          refine tsum_congr fun p => ?_
          have hp0 : Complex.Hadamard.divisorZeroIndex₀_val p ≠ 0 :=
            Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p
          simpa [Φ] using
            logDeriv_weierstrassFactor_one_div
              (a := Complex.Hadamard.divisorZeroIndex₀_val p) (z := z) hp0 (hz p)

/-- The Kadiri-facing zero-sum formula for the logarithmic derivative of the genus-one divisor
canonical product attached to Riemann's entire `ξ`. -/
theorem logDeriv_riemannXi_divisorCanonicalProduct_one_eq_tsum
    {z : ℂ}
    (hz : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      z ≠ Complex.Hadamard.divisorZeroIndex₀_val p)
    (hm : Summable (fun p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ) =>
      1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
        1 / Complex.Hadamard.divisorZeroIndex₀_val p))
    (hprod_ne :
      Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ) z ≠ 0) :
    logDeriv (Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ)) z =
      ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
        (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p) :=
  logDeriv_divisorCanonicalProduct_one_eq_tsum
    summable_riemannXi_divisorZeroIndex₀_norm_inv_sq hz hm hprod_ne

/-- Kadiri-facing logarithmic derivative identity for a chosen `ξ` Hadamard factorization.

The divisor-product differentiability is supplied by
`Complex.Hadamard.differentiableAt_divisorCanonicalProduct_univ`, and xi zero summability is
supplied by `summable_riemannXi_divisorZeroIndex₀_norm_inv_sq`.  The remaining hypotheses are the
nonzero evaluation and point-not-a-zero assumptions needed for the logarithmic derivative and
zero-sum terms. -/
theorem logDeriv_riemannXi_eq_polynomial_derivative_add_tsum
    {P : Polynomial ℂ} {z : ℂ}
    (hfac : ∀ w : ℂ, riemannXi w =
      Complex.exp (Polynomial.eval w P) *
        Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ) w)
    (hz : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      z ≠ Complex.Hadamard.divisorZeroIndex₀_val p)
    (hm : Summable (fun p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ) =>
      1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
        1 / Complex.Hadamard.divisorZeroIndex₀_val p))
    (hprod_ne :
      Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ) z ≠ 0) :
    logDeriv riemannXi z =
      Polynomial.eval z P.derivative +
        ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
          (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
            1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
  let G : ℂ → ℂ :=
    Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ)
  have hfun : riemannXi = fun w : ℂ => Complex.exp (Polynomial.eval w P) * G w := by
    funext w
    simpa [G] using hfac w
  have hdiff_exp : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (Polynomial.eval w P)) z :=
    ((Complex.hasDerivAt_exp (Polynomial.eval z P)).comp z (P.hasDerivAt z)).differentiableAt
  calc
    logDeriv riemannXi z =
        logDeriv (fun w : ℂ => Complex.exp (Polynomial.eval w P) * G w) z := by
          rw [hfun]
    _ = logDeriv (fun w : ℂ => Complex.exp (Polynomial.eval w P)) z + logDeriv G z := by
          exact logDeriv_mul z (Complex.exp_ne_zero _) (by simpa [G] using hprod_ne)
            hdiff_exp
            (by
              simpa [G] using
                Complex.Hadamard.differentiableAt_divisorCanonicalProduct_univ
                  1 riemannXi summable_riemannXi_divisorZeroIndex₀_norm_inv_sq z)
    _ = Polynomial.eval z P.derivative +
        ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
          (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
            1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
          rw [logDeriv_exp_polynomial]
          rw [show logDeriv G z =
              ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
                (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
                  1 / Complex.Hadamard.divisorZeroIndex₀_val p) from
            by
              simpa [G] using
                logDeriv_riemannXi_divisorCanonicalProduct_one_eq_tsum
                  hz hm hprod_ne]

/-- Hadamard factorization for Riemann's entire `ξ` at genus one. -/
theorem riemannXi_hadamard_factorization :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, riemannXi z =
        Complex.exp (Polynomial.eval z P) * z ^ (analyticOrderNatAt riemannXi 0) *
      Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ) z := by
  simpa using
    (Complex.Hadamard.hadamard_factorization_of_order
      (f := riemannXi) (ρ := (1 : ℝ))
      (by norm_num) riemannXi_nontrivial
      riemannXi_entireOfOrderAtMost_one)

/-- Hadamard factorization for `ξ` with the origin monomial removed using `ξ(0) ≠ 0`. -/
theorem riemannXi_hadamard_factorization_no_monomial :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, riemannXi z =
        Complex.exp (Polynomial.eval z P) *
      Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ) z := by
  rcases riemannXi_hadamard_factorization with ⟨P, hdeg, hfac⟩
  refine ⟨P, hdeg, ?_⟩
  intro z
  simpa [analyticOrderNatAt_riemannXi_zero, mul_assoc] using hfac z

/-- A downstream-ready xi log-derivative identity obtained by combining the no-monomial Hadamard
factorization with the Kadiri zero-sum bridge.

This theorem is intentionally phrased as an existence statement for the polynomial `P`: it tests
that the factorization theorem and the logarithmic-derivative bridge compose without exposing the
origin monomial or product-differentiability details to callers. -/
theorem exists_riemannXi_logDeriv_eq_polynomial_derivative_add_tsum
    {z : ℂ}
    (hz : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      z ≠ Complex.Hadamard.divisorZeroIndex₀_val p)
    (hm : Summable (fun p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ) =>
      1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
        1 / Complex.Hadamard.divisorZeroIndex₀_val p))
    (hprod_ne :
      Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ) z ≠ 0) :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧
      logDeriv riemannXi z =
        Polynomial.eval z P.derivative +
          ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
            (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
              1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
  rcases riemannXi_hadamard_factorization_no_monomial with ⟨P, hdeg, hfac⟩
  exact ⟨P, hdeg, logDeriv_riemannXi_eq_polynomial_derivative_add_tsum hfac hz hm hprod_ne⟩

/-- Reindexed divisor Hadamard factorization for Riemann's entire `ξ`. -/
theorem riemannXi_hadamard_factorization_reindex
    {ι : Type*}
    (e : ι ≃ Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, riemannXi z =
        Complex.exp (Polynomial.eval z P) * z ^ (analyticOrderNatAt riemannXi 0) *
      (∏' i : ι, Complex.weierstrassFactor 1
        (z / Complex.Hadamard.divisorZeroIndex₀_val (e i))) := by
  simpa using
    (Complex.Hadamard.hadamard_factorization_of_order_reindex
      (f := riemannXi) (ρ := (1 : ℝ))
      (by norm_num) riemannXi_nontrivial
      riemannXi_entireOfOrderAtMost_one e)

/-- Reindexed divisor Hadamard factorization for `ξ`, with the origin monomial removed. -/
theorem riemannXi_hadamard_factorization_reindex_no_monomial
    {ι : Type*}
    (e : ι ≃ Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, riemannXi z =
        Complex.exp (Polynomial.eval z P) *
      (∏' i : ι, Complex.weierstrassFactor 1
        (z / Complex.Hadamard.divisorZeroIndex₀_val (e i))) := by
  rcases riemannXi_hadamard_factorization_reindex e with ⟨P, hdeg, hfac⟩
  refine ⟨P, hdeg, ?_⟩
  intro z
  simpa [analyticOrderNatAt_riemannXi_zero, mul_assoc] using hfac z

/-- Sequence-indexed Hadamard factorization for Riemann's entire `ξ`. -/
theorem riemannXi_hadamard_factorization_sequence
    (e : ℕ ≃ Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, riemannXi z =
        Complex.exp (Polynomial.eval z P) * z ^ (analyticOrderNatAt riemannXi 0) *
      Complex.canonicalProduct 1
        (fun n : ℕ => Complex.Hadamard.divisorZeroIndex₀_val (e n)) z := by
  simpa using
    (Complex.Hadamard.hadamard_factorization_of_order_sequence
      (f := riemannXi) (ρ := (1 : ℝ))
      (by norm_num) riemannXi_nontrivial
      riemannXi_entireOfOrderAtMost_one e)

/-- Sequence-indexed Hadamard factorization for `ξ`, with the origin monomial removed. -/
theorem riemannXi_hadamard_factorization_sequence_no_monomial
    (e : ℕ ≃ Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, riemannXi z =
        Complex.exp (Polynomial.eval z P) *
      Complex.canonicalProduct 1
        (fun n : ℕ => Complex.Hadamard.divisorZeroIndex₀_val (e n)) z := by
  rcases riemannXi_hadamard_factorization_sequence e with ⟨P, hdeg, hfac⟩
  refine ⟨P, hdeg, ?_⟩
  intro z
  simpa [analyticOrderNatAt_riemannXi_zero, mul_assoc] using hfac z

/-- Hadamard factorization for `completedRiemannZeta₀` (Λ₀) at genus one. -/
theorem completedRiemannZeta₀_hadamard_factorization :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, completedRiemannZeta₀ z =
        Complex.exp (Polynomial.eval z P) * z ^ (analyticOrderNatAt completedRiemannZeta₀ 0) *
      Complex.Hadamard.divisorCanonicalProduct 1 completedRiemannZeta₀ (Set.univ : Set ℂ) z := by
  simpa using
    (Complex.Hadamard.hadamard_factorization_of_order
      (f := completedRiemannZeta₀) (ρ := (1 : ℝ))
      (by norm_num) completedRiemannZeta₀_nontrivial
      completedRiemannZeta₀_entireOfOrderAtMost_one)

/-- Hadamard factorization for `completedRiemannZeta₀` (Λ₀), with the origin monomial removed
using `Λ₀(0) ≠ 0`. -/
theorem completedRiemannZeta₀_hadamard_factorization_no_monomial :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, completedRiemannZeta₀ z =
        Complex.exp (Polynomial.eval z P) *
      Complex.Hadamard.divisorCanonicalProduct 1 completedRiemannZeta₀ (Set.univ : Set ℂ) z := by
  rcases completedRiemannZeta₀_hadamard_factorization with ⟨P, hdeg, hfac⟩
  refine ⟨P, hdeg, ?_⟩
  intro z
  simpa [analyticOrderNatAt_completedRiemannZeta₀_zero, mul_assoc] using hfac z

/-- Reindexed divisor Hadamard factorization for Λ₀. -/
theorem completedRiemannZeta₀_hadamard_factorization_reindex
    {ι : Type*}
    (e : ι ≃ Complex.Hadamard.divisorZeroIndex₀ completedRiemannZeta₀ (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, completedRiemannZeta₀ z =
        Complex.exp (Polynomial.eval z P) * z ^ (analyticOrderNatAt completedRiemannZeta₀ 0) *
      (∏' i : ι, Complex.weierstrassFactor 1
        (z / Complex.Hadamard.divisorZeroIndex₀_val (e i))) := by
  simpa using
    (Complex.Hadamard.hadamard_factorization_of_order_reindex
      (f := completedRiemannZeta₀) (ρ := (1 : ℝ))
      (by norm_num) completedRiemannZeta₀_nontrivial
      completedRiemannZeta₀_entireOfOrderAtMost_one e)

/-- Reindexed divisor Hadamard factorization for Λ₀, with the origin monomial removed. -/
theorem completedRiemannZeta₀_hadamard_factorization_reindex_no_monomial
    {ι : Type*}
    (e : ι ≃ Complex.Hadamard.divisorZeroIndex₀ completedRiemannZeta₀ (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, completedRiemannZeta₀ z =
        Complex.exp (Polynomial.eval z P) *
      (∏' i : ι, Complex.weierstrassFactor 1
        (z / Complex.Hadamard.divisorZeroIndex₀_val (e i))) := by
  rcases completedRiemannZeta₀_hadamard_factorization_reindex e with ⟨P, hdeg, hfac⟩
  refine ⟨P, hdeg, ?_⟩
  intro z
  simpa [analyticOrderNatAt_completedRiemannZeta₀_zero, mul_assoc] using hfac z

/-- Sequence-indexed Hadamard factorization for Λ₀. -/
theorem completedRiemannZeta₀_hadamard_factorization_sequence
    (e : ℕ ≃ Complex.Hadamard.divisorZeroIndex₀ completedRiemannZeta₀ (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, completedRiemannZeta₀ z =
        Complex.exp (Polynomial.eval z P) * z ^ (analyticOrderNatAt completedRiemannZeta₀ 0) *
      Complex.canonicalProduct 1
        (fun n : ℕ => Complex.Hadamard.divisorZeroIndex₀_val (e n)) z := by
  simpa using
    (Complex.Hadamard.hadamard_factorization_of_order_sequence
      (f := completedRiemannZeta₀) (ρ := (1 : ℝ))
      (by norm_num) completedRiemannZeta₀_nontrivial
      completedRiemannZeta₀_entireOfOrderAtMost_one e)

/-- Sequence-indexed Hadamard factorization for Λ₀, with the origin monomial removed. -/
theorem completedRiemannZeta₀_hadamard_factorization_sequence_no_monomial
    (e : ℕ ≃ Complex.Hadamard.divisorZeroIndex₀ completedRiemannZeta₀ (Set.univ : Set ℂ)) :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧ ∀ z : ℂ, completedRiemannZeta₀ z =
        Complex.exp (Polynomial.eval z P) *
      Complex.canonicalProduct 1
        (fun n : ℕ => Complex.Hadamard.divisorZeroIndex₀_val (e n)) z := by
  rcases completedRiemannZeta₀_hadamard_factorization_sequence e with ⟨P, hdeg, hfac⟩
  refine ⟨P, hdeg, ?_⟩
  intro z
  simpa [analyticOrderNatAt_completedRiemannZeta₀_zero, mul_assoc] using hfac z

end Riemann
