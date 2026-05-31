/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Complex.Divisor
public import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
public import Mathlib.Analysis.Complex.CartanProductBound
public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Mathlib.Analysis.Meromorphic.TrailingCoefficient
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.Complex.CartanBound
public import Mathlib.Analysis.Complex.CartanInverseFactorBound
public import Mathlib.Analysis.Complex.CartanMajorantBound
public import Mathlib.Analysis.Complex.ExpPoly
public import Mathlib.Analysis.Complex.ExpPoly.Growth
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Annulus



/-!
## The intrinsic Hadamard quotient (entire and zero-free)

We bundle the main "quotient step": if `f` is entire, nontrivial, and we have the summability
hypothesis for the divisor-indexed canonical product of genus `m`, then there is an entire function
`H` with no zeros such that

`f z = H z * z^(ord0) * divisorCanonicalProduct m f univ z`.

Internally we define `H` as the **normal form** (`toMeromorphicNFOn`) of the meromorphic quotient
`f / (z^ord0 * divisorCanonicalProduct ...)`; this takes care of the values at zeros without any
padding/`ZeroData` tricks.
-/

@[expose] public section

noncomputable section

namespace Complex.Hadamard

open Filter Topology Set Complex

open scoped BigOperators Topology

/-- The “denominator” in the Hadamard quotient construction: the product of the origin factor
`z ^ (analyticOrderNatAt f 0)` and the canonical product built from the divisor of `f` (of genus `m`)
on `univ`. -/
noncomputable def hadamardDenom (m : ℕ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  z ^ (analyticOrderNatAt f 0) * divisorCanonicalProduct m f (Set.univ : Set ℂ) z

theorem differentiable_hadamardDenom (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    Differentiable ℂ (hadamardDenom m f) := by
  classical
  have hcprod : Differentiable ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) := by
    intro z
    have hdiffOn :
        DifferentiableOn ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) (Set.univ : Set ℂ) :=
      differentiableOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
    exact (hdiffOn z (by simp)).differentiableAt (by simp)
  simpa [hadamardDenom] using (differentiable_id.pow (analyticOrderNatAt f 0)).mul hcprod

theorem hadamardDenom_ne_zero_at {m : ℕ} {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnot : ∃ z : ℂ, f z ≠ 0)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    {z : ℂ} (hz : f z ≠ 0) :
    hadamardDenom m f z ≠ 0 := by
  classical
  have hf_not_top : ∀ w : ℂ, analyticOrderAt f w ≠ ⊤ :=
    analyticOrderAt_ne_top_of_exists_ne_zero (hf := hf) hnot
  have han_f : AnalyticAt ℂ f z := hf.analyticAt z
  have horder_f : analyticOrderNatAt f z = 0 := by
    have : analyticOrderAt f z = 0 := (han_f.analyticOrderAt_eq_zero).2 hz
    have hcast : (analyticOrderNatAt f z : ℕ∞) = analyticOrderAt f z :=
      Nat.cast_analyticOrderNatAt (f := f) (z₀ := z) (hf_not_top z)
    have : (analyticOrderNatAt f z : ℕ∞) = 0 := by simp [hcast, this]
    exact_mod_cast this
  have han_cprod : AnalyticAt ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z := by
    have hdiffOn :
        DifferentiableOn ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) (Set.univ : Set ℂ) :=
      differentiableOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
    refine (Complex.analyticAt_iff_eventually_differentiableAt).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro w
    have : DifferentiableWithinAt ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) (Set.univ : Set ℂ) w :=
      hdiffOn w (by simp)
    exact this.differentiableAt (by simp)
  by_cases hz0 : z = 0
  · subst hz0
    have hord0 : analyticOrderNatAt f 0 = 0 := by simpa using horder_f
    simp [hadamardDenom, hord0, divisorCanonicalProduct_zero]
  · have hp : z ^ (analyticOrderNatAt f 0) ≠ 0 := pow_ne_zero _ hz0
    have hcprod_order :
        analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z = 0 := by
      simpa [horder_f] using
        (analyticOrderNatAt_divisorCanonicalProduct_eq_analyticOrderNatAt (m := m) (hf := hf)
          (h_sum := h_sum) (z₀ := z) hz0)
    have hcprod_ne : divisorCanonicalProduct m f (Set.univ : Set ℂ) z ≠ 0 := by
      have hcprod_entire :
          Differentiable ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) := by
        intro w
        have hdiffOn :
            DifferentiableOn ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) (Set.univ : Set ℂ) :=
          differentiableOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
        exact (hdiffOn w (by simp)).differentiableAt (by simp)
      have hcprod_not_top : analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z ≠ ⊤ :=
        analyticOrderAt_ne_top_of_exists_ne_zero (hf := hcprod_entire)
          ⟨0, by simp [divisorCanonicalProduct_zero]⟩ z
      have hcprod_cast :
          (analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z : ℕ∞) =
            analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z :=
        Nat.cast_analyticOrderNatAt
          (f := divisorCanonicalProduct m f (Set.univ : Set ℂ)) (z₀ := z) hcprod_not_top
      have : analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z = 0 := by
        have : (analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z : ℕ∞) = 0 := by
          exact_mod_cast hcprod_order
        simp [hcprod_cast] at this
        simpa using this
      exact (han_cprod.analyticOrderAt_eq_zero).1 this
    exact mul_ne_zero hp hcprod_ne

lemma analyticOrderNatAt_divisorCanonicalProduct_zero
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 = 0 := by
  classical
  have hcprod_entire :
      Differentiable ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) := by
    intro w
    have hdiffOn :
        DifferentiableOn ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) (Set.univ : Set ℂ) :=
      differentiableOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
    exact (hdiffOn w (by simp)).differentiableAt (by simp)
  have hcprod_not_top : analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 ≠ ⊤ :=
    analyticOrderAt_ne_top_of_exists_ne_zero (hf := hcprod_entire)
      ⟨0, by simp [divisorCanonicalProduct_zero]⟩ 0
  have hcprodA : AnalyticAt ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 :=
    hcprod_entire.analyticAt 0
  have hcprod0 : divisorCanonicalProduct m f (Set.univ : Set ℂ) 0 ≠ 0 := by
    simp [divisorCanonicalProduct_zero]
  have : analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 = 0 :=
    (hcprodA.analyticOrderAt_eq_zero).2 hcprod0
  have hcast :
      (analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 : ℕ∞) =
        analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 :=
    Nat.cast_analyticOrderNatAt
      (f := divisorCanonicalProduct m f (Set.univ : Set ℂ)) (z₀ := (0 : ℂ)) hcprod_not_top
  have : (analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 : ℕ∞) = 0 := by
    simp [hcast, this]
  exact_mod_cast this

theorem analyticOrderNatAt_hadamardDenom_eq
    (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) (z : ℂ) :
    analyticOrderNatAt (hadamardDenom m f) z = analyticOrderNatAt f z := by
  classical
  by_cases hz0 : z = 0
  · subst hz0
    have hpowA : AnalyticAt ℂ (fun z : ℂ => z ^ analyticOrderNatAt f 0) 0 := by
      simpa using (analyticAt_id.pow (analyticOrderNatAt f 0))
    have hpow_not_top : analyticOrderAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) 0 ≠ ⊤ :=
      analyticOrderAt_ne_top_of_exists_ne_zero (hf := (differentiable_id.pow (analyticOrderNatAt f 0)))
        ⟨1, by simp⟩ 0
    have hcprodA : AnalyticAt ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 := by
      have hcprod_entire :
          Differentiable ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) := by
        intro w
        have hdiffOn :
            DifferentiableOn ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) (Set.univ : Set ℂ) :=
          differentiableOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
        exact (hdiffOn w (by simp)).differentiableAt (by simp)
      exact hcprod_entire.analyticAt 0
    have hcprod0 : analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 = 0 :=
      analyticOrderNatAt_divisorCanonicalProduct_zero (m := m) (f := f) h_sum
    have hid0 : analyticOrderNatAt (fun z : ℂ => z) 0 = 1 := by
      have hid_entire : Differentiable ℂ (fun z : ℂ => z) := differentiable_id
      have hdiv :
          (MeromorphicOn.divisor (fun z : ℂ => z) (Set.univ : Set ℂ)) 0 =
            (analyticOrderNatAt (fun z : ℂ => z) 0 : ℤ) := by
        simpa using (divisor_univ_eq_analyticOrderNatAt_int (f := fun z : ℂ => z) hid_entire 0)
      have hdiv1 : (MeromorphicOn.divisor (fun z : ℂ => z) (Set.univ : Set ℂ)) 0 = 1 := by
        simpa using (MeromorphicOn.divisor_sub_const_self (z₀ := (0 : ℂ)) (U := (Set.univ : Set ℂ)) (by simp))
      have : (analyticOrderNatAt (fun z : ℂ => z) 0 : ℤ) = 1 := by
        simpa [hdiv] using hdiv1
      exact_mod_cast this
    have hpow0 : analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) 0 = analyticOrderNatAt f 0 := by
      have hidA : AnalyticAt ℂ (fun z : ℂ => z) 0 := by
        simpa [id] using (analyticAt_id : AnalyticAt ℂ (id : ℂ → ℂ) 0)
      simpa [hid0] using (analyticOrderNatAt_pow (hf := hidA) (n := analyticOrderNatAt f 0))
    have hmul :
        analyticOrderNatAt (hadamardDenom m f) 0 =
          analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) 0 +
            analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 := by
      have hcprod_not_top' : analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) 0 ≠ ⊤ :=
        analyticOrderAt_ne_top_of_exists_ne_zero
          (hf := (by
            intro w
            have hdiffOn :
                DifferentiableOn ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) (Set.univ : Set ℂ) :=
              differentiableOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
            exact (hdiffOn w (by simp)).differentiableAt (by simp)))
          ⟨0, by simp [divisorCanonicalProduct_zero]⟩ 0
      simpa [hadamardDenom] using
        analyticOrderNatAt_mul (hf := hpowA) (hg := hcprodA) (hf' := hpow_not_top) (hg' := hcprod_not_top')
    simp [hmul, hpow0, hcprod0]
  · have hpowA : AnalyticAt ℂ (fun z : ℂ => z ^ analyticOrderNatAt f 0) z := by
      simpa using (analyticAt_id.pow (analyticOrderNatAt f 0))
    have hpow_not_top : analyticOrderAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z ≠ ⊤ :=
      analyticOrderAt_ne_top_of_exists_ne_zero (hf := (differentiable_id.pow (analyticOrderNatAt f 0)))
        ⟨1, by simp⟩ z
    have hpow0 : analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z = 0 := by
      have hz' : (fun z : ℂ => z ^ analyticOrderNatAt f 0) z ≠ 0 := by
        simp [hz0]
      have : analyticOrderAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z = 0 :=
        ((hpowA).analyticOrderAt_eq_zero).2 hz'
      have hcast : (analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z : ℕ∞) =
          analyticOrderAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z :=
        Nat.cast_analyticOrderNatAt (f := fun z : ℂ => z ^ analyticOrderNatAt f 0) (z₀ := z) hpow_not_top
      have : (analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z : ℕ∞) = 0 := by
        simp [hcast, this]
      exact_mod_cast this
    have hcprod_eq :
        analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z = analyticOrderNatAt f z :=
      analyticOrderNatAt_divisorCanonicalProduct_eq_analyticOrderNatAt (m := m) (hf := hf) (h_sum := h_sum) (z₀ := z) hz0
    have hcprodA : AnalyticAt ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z := by
      have hcprod_entire :
          Differentiable ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) := by
        intro w
        have hdiffOn :
            DifferentiableOn ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) (Set.univ : Set ℂ) :=
          differentiableOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
        exact (hdiffOn w (by simp)).differentiableAt (by simp)
      exact hcprod_entire.analyticAt z
    have hcprod_not_top : analyticOrderAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z ≠ ⊤ :=
      analyticOrderAt_ne_top_of_exists_ne_zero
        (hf := (by
          intro w
          have hdiffOn :
              DifferentiableOn ℂ (divisorCanonicalProduct m f (Set.univ : Set ℂ)) (Set.univ : Set ℂ) :=
            differentiableOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
          exact (hdiffOn w (by simp)).differentiableAt (by simp)))
        ⟨0, by simp [divisorCanonicalProduct_zero]⟩ z
    have hmul :
        analyticOrderNatAt (hadamardDenom m f) z =
          analyticOrderNatAt (fun z : ℂ => z ^ analyticOrderNatAt f 0) z +
            analyticOrderNatAt (divisorCanonicalProduct m f (Set.univ : Set ℂ)) z := by
      simpa [hadamardDenom] using
        analyticOrderNatAt_mul (hf := hpowA) (hg := hcprodA) (hf' := hpow_not_top) (hg' := hcprod_not_top)
    simp [hmul, hpow0, hcprod_eq]

theorem divisor_hadamardDenom_eq
    (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    MeromorphicOn.divisor (hadamardDenom m f) (Set.univ : Set ℂ) =
      MeromorphicOn.divisor f (Set.univ : Set ℂ) := by
  classical
  ext z
  have hden_entire : Differentiable ℂ (hadamardDenom m f) :=
    differentiable_hadamardDenom (m := m) f h_sum
  have hf_entire : Differentiable ℂ f := hf
  have hden :
      (MeromorphicOn.divisor (hadamardDenom m f) (Set.univ : Set ℂ)) z =
        (analyticOrderNatAt (hadamardDenom m f) z : ℤ) := by
    simpa using (divisor_univ_eq_analyticOrderNatAt_int (f := hadamardDenom m f) hden_entire z)
  have hfz :
      (MeromorphicOn.divisor f (Set.univ : Set ℂ)) z =
        (analyticOrderNatAt f z : ℤ) := by
    simpa using (divisor_univ_eq_analyticOrderNatAt_int (f := f) hf_entire z)
  simp [hden, hfz, analyticOrderNatAt_hadamardDenom_eq (m := m) (hf := hf) (h_sum := h_sum) z]

theorem divisor_hadamardQuotient_eq_zero
    (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    MeromorphicOn.divisor (fun z : ℂ => f z / hadamardDenom m f z) (Set.univ : Set ℂ) = 0 := by
  classical
  have hf_mero : MeromorphicOn f (Set.univ : Set ℂ) := by
    intro z hz
    exact (hf.analyticAt z).meromorphicAt
  have hden_entire : Differentiable ℂ (hadamardDenom m f) :=
    differentiable_hadamardDenom (m := m) f h_sum
  have hden_mero : MeromorphicOn (hadamardDenom m f) (Set.univ : Set ℂ) := by
    intro z hz
    exact (hden_entire.analyticAt z).meromorphicAt
  rcases hnot with ⟨z1, hz1⟩
  have hden1 : hadamardDenom m f z1 ≠ 0 :=
    hadamardDenom_ne_zero_at (m := m) (f := f) hf ⟨z1, hz1⟩ h_sum hz1
  have hf_order_ne_top : ∀ z ∈ (Set.univ : Set ℂ), meromorphicOrderAt f z ≠ ⊤ := by
    intro z hzU
    have hz1_ne_top : meromorphicOrderAt f z1 ≠ ⊤ := by
      have hfAt : MeromorphicAt f z1 := hf_mero z1 (by simp)
      have hcont : ContinuousAt f z1 := (hf.differentiableAt).continuousAt
      have hne_nhds : ∀ᶠ w in 𝓝 z1, f w ≠ 0 :=
        (hcont.ne_iff_eventually_ne continuousAt_const).1 hz1
      have hne_nhdsNE : ∀ᶠ w in 𝓝[≠] z1, f w ≠ 0 :=
        eventually_nhdsWithin_of_eventually_nhds hne_nhds
      exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf := hfAt)).2 hne_nhdsNE
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected (hf := hf_mero)
      (x := z1) (hU := isPreconnected_univ) (h₁x := by simp) (hy := by simp) hz1_ne_top
  have hden_order_ne_top : ∀ z ∈ (Set.univ : Set ℂ), meromorphicOrderAt (hadamardDenom m f) z ≠ ⊤ := by
    intro z hzU
    have hz1_ne_top : meromorphicOrderAt (hadamardDenom m f) z1 ≠ ⊤ := by
      have hdenAt : MeromorphicAt (hadamardDenom m f) z1 := hden_mero z1 (by simp)
      have hcont : ContinuousAt (hadamardDenom m f) z1 := (hden_entire.differentiableAt).continuousAt
      have hne_nhds : ∀ᶠ w in 𝓝 z1, hadamardDenom m f w ≠ 0 :=
        (hcont.ne_iff_eventually_ne continuousAt_const).1 hden1
      have hne_nhdsNE : ∀ᶠ w in 𝓝[≠] z1, hadamardDenom m f w ≠ 0 :=
        eventually_nhdsWithin_of_eventually_nhds hne_nhds
      exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf := hdenAt)).2 hne_nhdsNE
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected (hf := hden_mero)
      (x := z1) (hU := isPreconnected_univ) (h₁x := by simp) (hy := by simp) hz1_ne_top
  have hinv_order_ne_top :
      ∀ z ∈ (Set.univ : Set ℂ), meromorphicOrderAt (fun z : ℂ => (hadamardDenom m f z)⁻¹) z ≠ ⊤ := by
    intro z hzU
    have hinv_mero : MeromorphicOn (fun z : ℂ => (hadamardDenom m f z)⁻¹) (Set.univ : Set ℂ) :=
      hden_mero.inv
    have hz1_ne_top : meromorphicOrderAt (fun z : ℂ => (hadamardDenom m f z)⁻¹) z1 ≠ ⊤ := by
      have hinvAt : MeromorphicAt (fun z : ℂ => (hadamardDenom m f z)⁻¹) z1 :=
        hinv_mero z1 (by simp)
      have hcont_denom : ContinuousAt (hadamardDenom m f) z1 :=
        (hden_entire.differentiableAt).continuousAt
      have hcont : ContinuousAt (fun z : ℂ => (hadamardDenom m f z)⁻¹) z1 :=
        hcont_denom.inv₀ hden1
      have hinv1 : (fun z : ℂ => (hadamardDenom m f z)⁻¹) z1 ≠ 0 := by
        simpa using inv_ne_zero hden1
      have hne_nhds : ∀ᶠ w in 𝓝 z1, (fun z : ℂ => (hadamardDenom m f z)⁻¹) w ≠ 0 :=
        (hcont.ne_iff_eventually_ne continuousAt_const).1 hinv1
      have hne_nhdsNE : ∀ᶠ w in 𝓝[≠] z1, (fun z : ℂ => (hadamardDenom m f z)⁻¹) w ≠ 0 :=
        eventually_nhdsWithin_of_eventually_nhds hne_nhds
      exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf := hinvAt)).2 hne_nhdsNE
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected (hf := hinv_mero)
      (x := z1) (hU := isPreconnected_univ) (h₁x := by simp) (hy := by simp) hz1_ne_top
  have hdiv_denom : MeromorphicOn.divisor (hadamardDenom m f) (Set.univ : Set ℂ) =
      MeromorphicOn.divisor f (Set.univ : Set ℂ) :=
    divisor_hadamardDenom_eq (m := m) (hf := hf) (h_sum := h_sum)
  calc
    MeromorphicOn.divisor (fun z : ℂ => f z / hadamardDenom m f z) (Set.univ : Set ℂ)
        = MeromorphicOn.divisor (fun z : ℂ => f z * (hadamardDenom m f z)⁻¹) (Set.univ : Set ℂ) := by
            simp [div_eq_mul_inv]
    _ = MeromorphicOn.divisor f (Set.univ : Set ℂ) +
          MeromorphicOn.divisor (fun z : ℂ => (hadamardDenom m f z)⁻¹) (Set.univ : Set ℂ) := by
          simpa using (MeromorphicOn.divisor_fun_mul (U := (Set.univ : Set ℂ))
            (f₁ := f) (f₂ := fun z => (hadamardDenom m f z)⁻¹) hf_mero (hden_mero.inv)
            hf_order_ne_top hinv_order_ne_top)
    _ = MeromorphicOn.divisor f (Set.univ : Set ℂ) - MeromorphicOn.divisor (hadamardDenom m f) (Set.univ : Set ℂ) := by
          simp [sub_eq_add_neg]
    _ = 0 := by
          simp [hdiv_denom]

theorem exists_entire_nonzero_hadamardQuotient
    (m : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1))) :
    ∃ H : ℂ → ℂ,
      Differentiable ℂ H ∧
      (∀ z, H z ≠ 0) ∧
      ∀ z : ℂ,
        f z =
          H z * z ^ (analyticOrderNatAt f 0) *
            divisorCanonicalProduct m f (Set.univ : Set ℂ) z := by
  classical
  let denom : ℂ → ℂ := hadamardDenom m f
  let q : ℂ → ℂ := fun z => f z / denom z
  have hden_entire : Differentiable ℂ denom :=
    differentiable_hadamardDenom (m := m) f h_sum
  have hq_mero : MeromorphicOn q (Set.univ : Set ℂ) := by
    intro z hzU
    have hf_m : MeromorphicAt f z := (hf.analyticAt z).meromorphicAt
    have hden_m : MeromorphicAt denom z := (hden_entire.analyticAt z).meromorphicAt
    simpa [q, denom, div_eq_mul_inv] using (hf_m.mul hden_m.inv)
  let H : ℂ → ℂ := toMeromorphicNFOn q (Set.univ : Set ℂ)
  have hNF : MeromorphicNFOn H (Set.univ : Set ℂ) :=
    meromorphicNFOn_toMeromorphicNFOn q (Set.univ : Set ℂ)
  have hdivH : MeromorphicOn.divisor H (Set.univ : Set ℂ) = 0 := by
    have hdivq : MeromorphicOn.divisor q (Set.univ : Set ℂ) = 0 :=
      divisor_hadamardQuotient_eq_zero (m := m) (f := f) (hf := hf) (hnot := hnot) (h_sum := h_sum)
    simpa [H, hdivq] using (MeromorphicOn.divisor_of_toMeromorphicNFOn (f := q) (U := (Set.univ : Set ℂ)) hq_mero)
  have hA : AnalyticOnNhd ℂ H (Set.univ : Set ℂ) := by
    have : (0 : Function.locallyFinsuppWithin (Set.univ : Set ℂ) ℤ) ≤ MeromorphicOn.divisor H (Set.univ : Set ℂ) := by
      simp [hdivH]
    exact (MeromorphicNFOn.divisor_nonneg_iff_analyticOnNhd (h₁f := hNF)).1 (by simp [hdivH])
  have hH_entire : Differentiable ℂ H := by
    intro z
    exact (hA z (by simp)).differentiableAt
  rcases hnot with ⟨z1, hz1⟩
  have hden1 : denom z1 ≠ 0 :=
    hadamardDenom_ne_zero_at (m := m) (f := f) hf ⟨z1, hz1⟩ h_sum hz1
  have hqA1 : AnalyticAt ℂ q z1 := by
    have hdenA1 : AnalyticAt ℂ denom z1 := hden_entire.analyticAt z1
    exact (hf.analyticAt z1).div hdenA1 hden1
  have hqNF1 : MeromorphicNFAt q z1 := hqA1.meromorphicNFAt
  have htoEq : toMeromorphicNFAt q z1 = q := (toMeromorphicNFAt_eq_self (f := q) (x := z1)).2 hqNF1
  have hH1 : H z1 = q z1 := by
    have hx : z1 ∈ (Set.univ : Set ℂ) := by simp
    have : toMeromorphicNFOn q (Set.univ : Set ℂ) z1 = toMeromorphicNFAt q z1 z1 :=
      (toMeromorphicNFOn_eq_toMeromorphicNFAt (f := q) (U := (Set.univ : Set ℂ)) hq_mero hx)
    simpa [H, htoEq] using this
  have hH1_ne : H z1 ≠ 0 := by
    have : q z1 ≠ 0 := div_ne_zero hz1 hden1
    simpa [hH1] using this
  have hH_not_top : ∀ z : ℂ, analyticOrderAt H z ≠ ⊤ := by
    exact analyticOrderAt_ne_top_of_exists_ne_zero (hf := hH_entire) ⟨z1, hH1_ne⟩
  have hH_orderNat_zero : ∀ z : ℂ, analyticOrderNatAt H z = 0 := by
    intro z
    have hzdiv :
        (MeromorphicOn.divisor H (Set.univ : Set ℂ)) z = (analyticOrderNatAt H z : ℤ) := by
      simpa using (divisor_univ_eq_analyticOrderNatAt_int (f := H) hH_entire z)
    have : (MeromorphicOn.divisor H (Set.univ : Set ℂ)) z = 0 := by
      simp [hdivH]
    have : (analyticOrderNatAt H z : ℤ) = 0 := by simpa [hzdiv] using this
    exact_mod_cast this
  have hH_ne : ∀ z : ℂ, H z ≠ 0 := by
    intro z
    have hcast : (analyticOrderNatAt H z : ℕ∞) = analyticOrderAt H z :=
      Nat.cast_analyticOrderNatAt (f := H) (z₀ := z) (hH_not_top z)
    have : analyticOrderAt H z = 0 := by
      have : (analyticOrderNatAt H z : ℕ∞) = 0 := by exact_mod_cast (hH_orderNat_zero z)
      simpa [hcast] using this
    exact ((hA z (by simp)).analyticOrderAt_eq_zero).1 this
  have hfA : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) := fun z hzU => hf.analyticAt z
  have hdenA : AnalyticOnNhd ℂ denom (Set.univ : Set ℂ) := fun z hzU => hden_entire.analyticAt z
  have hprodA : AnalyticOnNhd ℂ (fun z => H z * denom z) (Set.univ : Set ℂ) :=
    (hA.mul hdenA)
  have hlocal : f =ᶠ[𝓝 z1] fun z => H z * denom z := by
    have hden_ne : ∀ᶠ z in 𝓝 z1, denom z ≠ 0 :=
      (hden_entire.differentiableAt.continuousAt.ne_iff_eventually_ne continuousAt_const).1 hden1
    have hH_eq_q : H =ᶠ[𝓝 z1] q := by
      have hx : z1 ∈ (Set.univ : Set ℂ) := by simp
      have hloc :
          toMeromorphicNFOn q (Set.univ : Set ℂ) =ᶠ[𝓝 z1] toMeromorphicNFAt q z1 := by
        simpa [H] using (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds (f := q)
          (U := (Set.univ : Set ℂ)) hq_mero hx)
      simpa [H, htoEq] using hloc
    filter_upwards [hden_ne, hH_eq_q] with z hzden hHz
    have hcancel : q z * denom z = f z := by
      dsimp [q]
      field_simp [hzden]
    calc
      f z = q z * denom z := hcancel.symm
      _ = H z * denom z := by simp [hHz]
  have hglob : f = fun z => H z * denom z :=
    AnalyticOnNhd.eq_of_eventuallyEq (hf := hfA) (hg := hprodA) hlocal
  refine ⟨H, hH_entire, hH_ne, ?_⟩
  intro z
  have hglobz : f z = H z * denom z := congrArg (fun g => g z) hglob
  simpa [denom, hadamardDenom, mul_assoc, mul_left_comm, mul_comm] using hglobz


/-!
## Intrinsic Lindelöf summability: growth ⇒ summability of divisor-indexed exponents

This section is the first global ingredient needed to remove the final `sorry` in
`hadamard_factorization_of_growth`.

We derive the summability hypothesis required to form the intrinsic canonical product from the
growth bound on `log (1 + ‖f z‖)` by bounding the logarithmic counting function of the divisor.
-/

open scoped Real

lemma logCounting_divisor_univ_eq_circleAverage_sub_log_trailingCoeff {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {R : ℝ} (hR : R ≠ 0) :
    (Function.locallyFinsuppWithin.logCounting (MeromorphicOn.divisor f (Set.univ : Set ℂ)) R)
      = Real.circleAverage (fun z : ℂ => Real.log ‖f z‖) 0 R
        - Real.log ‖meromorphicTrailingCoeffAt f 0‖ := by
  have hmero : Meromorphic f := by
    intro z
    exact (hf.analyticAt z).meromorphicAt
  simpa [top_eq_univ] using
    (Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const (f := f)
      (h := hmero) (hR := hR))

lemma logCounting_divisor_univ_le_of_growth {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f)
    (hgrowth : ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ)
    {R : ℝ} (hR0 : 0 < R) :
    Function.locallyFinsuppWithin.logCounting (MeromorphicOn.divisor f (Set.univ : Set ℂ)) R
      ≤ (Classical.choose hgrowth) * (1 + |R|) ^ ρ
        + |Real.log ‖meromorphicTrailingCoeffAt f 0‖| := by
  classical
  set C : ℝ := Classical.choose hgrowth
  have hCpos : 0 < C := (Classical.choose_spec hgrowth).1
  have hC : ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ :=
    (Classical.choose_spec hgrowth).2
  have hR : R ≠ 0 := ne_of_gt hR0
  have hEq := logCounting_divisor_univ_eq_circleAverage_sub_log_trailingCoeff (f := f) hf (R := R) hR
  have hf_sphere : MeromorphicOn f (Metric.sphere (0 : ℂ) |R|) := by
    intro z hz
    exact (hf.analyticAt z).meromorphicAt
  have hInt : CircleIntegrable (fun z : ℂ => Real.log ‖f z‖) 0 R :=
    circleIntegrable_log_norm_meromorphicOn hf_sphere
  have hbound_circle : ∀ z ∈ Metric.sphere (0 : ℂ) |R|,
      Real.log ‖f z‖ ≤ C * (1 + |R|) ^ ρ := by
    intro z hz
    have hz_norm : ‖z‖ = |R| := by
      simpa [Metric.mem_sphere, dist_zero_right] using hz
    have hlog1 : Real.log ‖f z‖ ≤ Real.log (1 + ‖f z‖) := by
      by_cases h0 : f z = 0
      · simp [h0]
      · have hpos : 0 < ‖f z‖ := norm_pos_iff.2 h0
        have hle : ‖f z‖ ≤ 1 + ‖f z‖ := by linarith [norm_nonneg (f z)]
        exact Real.log_le_log hpos hle
    have hlog1' : Real.log ‖f z‖ ≤ C * (1 + ‖z‖) ^ ρ := le_trans hlog1 (hC z)
    simpa [hz_norm] using hlog1'
  have hCircleAvg_le :
      Real.circleAverage (fun z : ℂ => Real.log ‖f z‖) 0 R ≤ C * (1 + |R|) ^ ρ :=
    Real.circleAverage_mono_on_of_le_circle (c := (0 : ℂ)) (R := R) (f := fun z => Real.log ‖f z‖)
      hInt hbound_circle
  calc
    Function.locallyFinsuppWithin.logCounting (MeromorphicOn.divisor f (Set.univ : Set ℂ)) R
        = Real.circleAverage (fun z : ℂ => Real.log ‖f z‖) 0 R
            - Real.log ‖meromorphicTrailingCoeffAt f 0‖ := hEq
    _ ≤ Real.circleAverage (fun z : ℂ => Real.log ‖f z‖) 0 R
          + |Real.log ‖meromorphicTrailingCoeffAt f 0‖| := by
          have : -Real.log ‖meromorphicTrailingCoeffAt f 0‖ ≤ |Real.log ‖meromorphicTrailingCoeffAt f 0‖| :=
            neg_le_abs (Real.log ‖meromorphicTrailingCoeffAt f 0‖)
          linarith
    _ ≤ C * (1 + |R|) ^ ρ + |Real.log ‖meromorphicTrailingCoeffAt f 0‖| := by
          nlinarith [hCircleAvg_le]

lemma countable_divisor_support_univ {f : ℂ → ℂ} :
    (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support.Countable := by
  classical
  set D : Function.locallyFinsuppWithin (Set.univ : Set ℂ) ℤ :=
    MeromorphicOn.divisor f (Set.univ : Set ℂ)
  have hclosed : IsClosed D.support := by
    simpa [D] using (D.closedSupport (hU := isClosed_univ))
  have hdisc : IsDiscrete D.support := by
    simpa [D] using (D.discreteSupport)
  have hL : IsLindelof (Set.univ : Set ℂ) := isLindelof_univ
  have hL' : IsLindelof D.support :=
    IsLindelof.of_isClosed_subset hL hclosed (by simp)
  simpa [D] using hL'.countable_of_isDiscrete hdisc

lemma logCounting_two_mul_lower_bound_sum_divisor_closedBall {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {R : ℝ} (hR : 1 ≤ R) :
    (Real.log 2) *
        ((((Function.locallyFinsuppWithin.finiteSupport
                (Function.locallyFinsuppWithin.toClosedBall R
                  (MeromorphicOn.divisor f (Set.univ : Set ℂ)))
                (isCompact_closedBall (0 : ℂ) |R|)).toFinset).filter fun z : ℂ => z ≠ 0).sum
          fun z : ℂ => (MeromorphicOn.divisor f (Set.univ : Set ℂ) z : ℝ))
      ≤ Function.locallyFinsuppWithin.logCounting
          (MeromorphicOn.divisor f (Set.univ : Set ℂ)) (2 * R) := by
  classical
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR
  set D : Function.locallyFinsuppWithin (Set.univ : Set ℂ) ℤ :=
    MeromorphicOn.divisor f (Set.univ : Set ℂ)
  set r : ℝ := 2 * R
  have hrpos : 0 < r := by dsimp [r]; nlinarith
  have hr : r ≠ 0 := ne_of_gt hrpos
  have hDnonneg : 0 ≤ D := by
    have hAnal : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) := by
      intro z hz
      simpa using (hf.analyticAt z)
    simpa [D] using
      (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (𝕜 := ℂ) (f := f) (U := (Set.univ : Set ℂ)) hAnal)
  let Dr : Function.locallyFinsuppWithin (Metric.closedBall (0 : ℂ) |r|) ℤ :=
    Function.locallyFinsuppWithin.toClosedBall r D
  have hDr_fin : Set.Finite Dr.support := Dr.finiteSupport (isCompact_closedBall (0 : ℂ) |r|)
  let F : Finset ℂ := hDr_fin.toFinset
  let SR : Finset ℂ :=
    (Function.locallyFinsuppWithin.finiteSupport (Function.locallyFinsuppWithin.toClosedBall R D)
          (isCompact_closedBall (0 : ℂ) |R|)).toFinset
  let S : Finset ℂ := SR.filter fun z : ℂ => z ≠ 0
  have hS_sub : S ⊆ F := by
    intro z hzS
    have hz0 : z ≠ 0 := (Finset.mem_filter.1 hzS).2
    have hz_mem_SR : z ∈ SR := (Finset.mem_filter.1 hzS).1
    have hzR : z ∈ (Function.locallyFinsuppWithin.toClosedBall R D).support := by
      exact (Set.Finite.mem_toFinset
        (Function.locallyFinsuppWithin.finiteSupport (Function.locallyFinsuppWithin.toClosedBall R D)
          (isCompact_closedBall (0 : ℂ) |R|))).1 hz_mem_SR
    have hz_in_ballR : z ∈ Metric.closedBall (0 : ℂ) |R| := by
      exact (Function.locallyFinsuppWithin.toClosedBall R D).supportWithinDomain hzR
    have hz_norm_le_R : ‖z‖ ≤ R := by
      have : ‖z‖ ≤ |R| := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hz_in_ballR
      simpa [abs_of_pos hR0] using this
    have hz_norm_le_r : ‖z‖ ≤ |r| := by
      have : ‖z‖ ≤ r := le_trans hz_norm_le_R (by dsimp [r]; nlinarith)
      simpa [abs_of_pos hrpos] using this
    have hz_in_ballr : z ∈ Metric.closedBall (0 : ℂ) |r| := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hz_norm_le_r
    have hDrz : Dr z = D z := by
      simpa [Dr] using (Function.locallyFinsuppWithin.toClosedBall_eval_within (r := r) (f := D)
        (z := z) hz_in_ballr)
    have hDz_ne : D z ≠ 0 := by
      have hDz' : (Function.locallyFinsuppWithin.toClosedBall R D) z ≠ 0 := by
        simpa [Function.mem_support] using hzR
      have hz_in_ballR' : z ∈ Metric.closedBall (0 : ℂ) |R| := hz_in_ballR
      have hDz_eq : (Function.locallyFinsuppWithin.toClosedBall R D) z = D z := by
        simpa using (Function.locallyFinsuppWithin.toClosedBall_eval_within (r := R) (f := D)
          (z := z) hz_in_ballR')
      simpa [hDz_eq] using hDz'
    have : z ∈ Dr.support := by
      simp [Function.mem_support, hDrz, hDz_ne]
    exact (Set.Finite.mem_toFinset hDr_fin).2 this
  have hlogCounting :
      Function.locallyFinsuppWithin.logCounting D r
        = (F.sum fun z : ℂ => (Dr z : ℝ) * Real.log (r * ‖z‖⁻¹)) + (D 0 : ℝ) * Real.log r := by
    have hsupp :
        Function.support (fun z : ℂ => (Dr z : ℝ) * Real.log (r * ‖z‖⁻¹)) ⊆ F := by
      intro z hz
      have : Dr z ≠ 0 := by
        by_contra h0
        simp [Function.mem_support, h0] at hz
      have : z ∈ Dr.support := by simpa [Function.mem_support] using this
      exact (Set.Finite.mem_toFinset hDr_fin).2 this
    simp [Function.locallyFinsuppWithin.logCounting, D, Dr, r,
      finsum_eq_sum_of_support_subset (f := fun z : ℂ =>
        (Dr z : ℝ) * Real.log (r * ‖z‖⁻¹)) (s := F) hsupp]
  have hsum_le :
      (Real.log 2) * (S.sum fun z : ℂ => (D z : ℝ))
        ≤ F.sum (fun z : ℂ => (Dr z : ℝ) * Real.log (r * ‖z‖⁻¹)) := by
    have hterm_nonneg : ∀ z ∈ F, 0 ≤ (Dr z : ℝ) * Real.log (r * ‖z‖⁻¹) := by
      intro z hzF
      have hz_sup : z ∈ Dr.support := (Set.Finite.mem_toFinset hDr_fin).1 hzF
      have hz_in : z ∈ Metric.closedBall (0 : ℂ) |r| := Dr.supportWithinDomain hz_sup
      have hDz : 0 ≤ Dr z := by
        have hDz' : 0 ≤ D z := hDnonneg z
        have hDrz : Dr z = D z := by
          simpa [Dr] using (Function.locallyFinsuppWithin.toClosedBall_eval_within (r := r) (f := D)
            (z := z) hz_in)
        simpa [hDrz] using hDz'
      have hlog : 0 ≤ Real.log (r * ‖z‖⁻¹) := by
        by_cases hz0 : z = 0
        · subst hz0
          simp
        · have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
          have hzle : ‖z‖ ≤ r := by
            have : ‖z‖ ≤ |r| := by simpa [Metric.mem_closedBall, dist_zero_right] using hz_in
            simpa [abs_of_pos hrpos] using this
          have : 1 ≤ r * ‖z‖⁻¹ := by
            have : 1 ≤ r / ‖z‖ := (one_le_div hzpos).2 hzle
            simpa [div_eq_mul_inv] using this
          exact Real.log_nonneg this
      exact mul_nonneg (by exact_mod_cast hDz) hlog
    have hsumSF :
        S.sum (fun z : ℂ => (Dr z : ℝ) * Real.log (r * ‖z‖⁻¹))
          ≤ F.sum (fun z : ℂ => (Dr z : ℝ) * Real.log (r * ‖z‖⁻¹)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hS_sub (by
        intro z hzF hznot; exact hterm_nonneg z hzF)
    have hterm_ge : ∀ z ∈ S,
        (Real.log 2) * (D z : ℝ) ≤ (Dr z : ℝ) * Real.log (r * ‖z‖⁻¹) := by
      intro z hzS
      have hz0 : z ≠ 0 := (Finset.mem_filter.1 hzS).2
      have hz_norm_le_R : ‖z‖ ≤ R := by
        have hz_mem_SR : z ∈ SR := (Finset.mem_filter.1 hzS).1
        have hzRsup : z ∈ (Function.locallyFinsuppWithin.toClosedBall R D).support := by
          exact (Set.Finite.mem_toFinset
            (Function.locallyFinsuppWithin.finiteSupport (Function.locallyFinsuppWithin.toClosedBall R D)
              (isCompact_closedBall (0 : ℂ) |R|))).1 hz_mem_SR
        have hz_in : z ∈ Metric.closedBall (0 : ℂ) |R| :=
          (Function.locallyFinsuppWithin.toClosedBall R D).supportWithinDomain hzRsup
        have : ‖z‖ ≤ |R| := by simpa [Metric.mem_closedBall, dist_zero_right] using hz_in
        simpa [abs_of_pos hR0] using this
      have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
      have hle2 : (2 : ℝ) ≤ r * ‖z‖⁻¹ := by
        have hRdiv : 1 ≤ R / ‖z‖ := (one_le_div hzpos).2 hz_norm_le_R
        have : (2 : ℝ) ≤ 2 * (R / ‖z‖) := by nlinarith
        simpa [r, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
      have hlog_le : Real.log 2 ≤ Real.log (r * ‖z‖⁻¹) :=
        Real.log_le_log (by positivity : (0 : ℝ) < 2) hle2
      have hDz_nonneg : 0 ≤ D z := hDnonneg z
      have hz_in_ballr : z ∈ Metric.closedBall (0 : ℂ) |r| := by
        have : ‖z‖ ≤ r := le_trans hz_norm_le_R (by dsimp [r]; nlinarith)
        simpa [Metric.mem_closedBall, dist_zero_right, abs_of_pos hrpos] using this
      have hDrz : Dr z = D z := by
        simpa [Dr] using (Function.locallyFinsuppWithin.toClosedBall_eval_within (r := r) (f := D)
          (z := z) hz_in_ballr)
      have : (Real.log 2) * (D z : ℝ) ≤ (Real.log (r * ‖z‖⁻¹)) * (D z : ℝ) :=
        mul_le_mul_of_nonneg_right hlog_le (by exact_mod_cast hDz_nonneg)
      simpa [hDrz, mul_assoc, mul_left_comm, mul_comm] using this
    calc
      (Real.log 2) * (S.sum fun z : ℂ => (D z : ℝ))
          = S.sum (fun z : ℂ => (Real.log 2) * (D z : ℝ)) := by
              simp [Finset.mul_sum]
      _ ≤ S.sum (fun z : ℂ => (Dr z : ℝ) * Real.log (r * ‖z‖⁻¹)) := by
            exact Finset.sum_le_sum fun z hz => hterm_ge z hz
      _ ≤ F.sum (fun z : ℂ => (Dr z : ℝ) * Real.log (r * ‖z‖⁻¹)) := hsumSF
  have hcenter_nonneg : 0 ≤ (D 0 : ℝ) * Real.log r := by
    have hD0 : 0 ≤ D 0 := hDnonneg 0
    have hlogr : 0 ≤ Real.log r := Real.log_nonneg (by nlinarith [hR])
    exact mul_nonneg (by exact_mod_cast hD0) hlogr
  have : (Real.log 2) * (S.sum fun z : ℂ => (D z : ℝ))
      ≤ Function.locallyFinsuppWithin.logCounting D r := by
    rw [hlogCounting]
    nlinarith [hsum_le, hcenter_nonneg]
  simpa [D, r, S, SR] using this

lemma sum_divisor_closedBall_le_of_growth {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f)
    (hgrowth : ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ)
    {R : ℝ} (hR : 1 ≤ R) :
    ((((Function.locallyFinsuppWithin.finiteSupport
            (Function.locallyFinsuppWithin.toClosedBall R
              (MeromorphicOn.divisor f (Set.univ : Set ℂ)))
            (isCompact_closedBall (0 : ℂ) |R|)).toFinset).filter fun z : ℂ => z ≠ 0).sum
        fun z : ℂ => (MeromorphicOn.divisor f (Set.univ : Set ℂ) z : ℝ))
      ≤ ((Classical.choose hgrowth) * (1 + |2 * R|) ^ ρ
          + |Real.log ‖meromorphicTrailingCoeffAt f 0‖|) / (Real.log 2) := by
  classical
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hR
  have hlog2pos : 0 < Real.log 2 := by
    have : (1 : ℝ) < 2 := by norm_num
    exact Real.log_pos this
  have hlow :
      (Real.log 2) *
          ((((Function.locallyFinsuppWithin.finiteSupport
                  (Function.locallyFinsuppWithin.toClosedBall R
                    (MeromorphicOn.divisor f (Set.univ : Set ℂ)))
                  (isCompact_closedBall (0 : ℂ) |R|)).toFinset).filter fun z : ℂ => z ≠ 0).sum
            fun z : ℂ => (MeromorphicOn.divisor f (Set.univ : Set ℂ) z : ℝ))
        ≤ Function.locallyFinsuppWithin.logCounting
            (MeromorphicOn.divisor f (Set.univ : Set ℂ)) (2 * R) :=
    logCounting_two_mul_lower_bound_sum_divisor_closedBall (f := f) hf (R := R) hR
  have hupp :
      Function.locallyFinsuppWithin.logCounting (MeromorphicOn.divisor f (Set.univ : Set ℂ)) (2 * R)
        ≤ (Classical.choose hgrowth) * (1 + |2 * R|) ^ ρ
          + |Real.log ‖meromorphicTrailingCoeffAt f 0‖| := by
    have h2R0 : 0 < (2 * R) := by nlinarith [hR0]
    simpa using (logCounting_divisor_univ_le_of_growth (f := f) (ρ := ρ) hf hgrowth (R := 2 * R) h2R0)
  have : (Real.log 2) *
        ((((Function.locallyFinsuppWithin.finiteSupport
                (Function.locallyFinsuppWithin.toClosedBall R
                  (MeromorphicOn.divisor f (Set.univ : Set ℂ)))
                (isCompact_closedBall (0 : ℂ) |R|)).toFinset).filter fun z : ℂ => z ≠ 0).sum
          fun z : ℂ => (MeromorphicOn.divisor f (Set.univ : Set ℂ) z : ℝ))
      ≤ (Classical.choose hgrowth) * (1 + |2 * R|) ^ ρ + |Real.log ‖meromorphicTrailingCoeffAt f 0‖| :=
    le_trans hlow hupp
  have : ((((Function.locallyFinsuppWithin.finiteSupport
              (Function.locallyFinsuppWithin.toClosedBall R
                (MeromorphicOn.divisor f (Set.univ : Set ℂ)))
              (isCompact_closedBall (0 : ℂ) |R|)).toFinset).filter fun z : ℂ => z ≠ 0).sum
          fun z : ℂ => (MeromorphicOn.divisor f (Set.univ : Set ℂ) z : ℝ))
      ≤ ((Classical.choose hgrowth) * (1 + |2 * R|) ^ ρ + |Real.log ‖meromorphicTrailingCoeffAt f 0‖|)
          / (Real.log 2) := by
    have hx :
        ((((Function.locallyFinsuppWithin.finiteSupport
                (Function.locallyFinsuppWithin.toClosedBall R
                  (MeromorphicOn.divisor f (Set.univ : Set ℂ)))
                (isCompact_closedBall (0 : ℂ) |R|)).toFinset).filter fun z : ℂ => z ≠ 0).sum
            fun z : ℂ => (MeromorphicOn.divisor f (Set.univ : Set ℂ) z : ℝ)) * (Real.log 2)
          ≤ (Classical.choose hgrowth) * (1 + |2 * R|) ^ ρ + |Real.log ‖meromorphicTrailingCoeffAt f 0‖| := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    exact (le_div_iff₀ hlog2pos).2 hx
  simpa using this

lemma sum_divisor_closedBall_mono {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {R₁ R₂ : ℝ} (hR₁ : 0 ≤ R₁) (hR₁₂ : R₁ ≤ R₂) :
    ((((Function.locallyFinsuppWithin.finiteSupport
            (Function.locallyFinsuppWithin.toClosedBall R₁
              (MeromorphicOn.divisor f (Set.univ : Set ℂ)))
            (isCompact_closedBall (0 : ℂ) |R₁|)).toFinset).filter fun z : ℂ => z ≠ 0).sum
        fun z : ℂ => (MeromorphicOn.divisor f (Set.univ : Set ℂ) z : ℝ))
      ≤
      ((((Function.locallyFinsuppWithin.finiteSupport
              (Function.locallyFinsuppWithin.toClosedBall R₂
                (MeromorphicOn.divisor f (Set.univ : Set ℂ)))
              (isCompact_closedBall (0 : ℂ) |R₂|)).toFinset).filter fun z : ℂ => z ≠ 0).sum
          fun z : ℂ => (MeromorphicOn.divisor f (Set.univ : Set ℂ) z : ℝ)) := by
  classical
  have hR₂ : 0 ≤ R₂ := le_trans hR₁ hR₁₂
  have habs₁ : |R₁| = R₁ := abs_of_nonneg hR₁
  have habs₂ : |R₂| = R₂ := abs_of_nonneg hR₂
  set U : Set ℂ := (Set.univ : Set ℂ)
  set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  have hAnal : AnalyticOnNhd ℂ f U := by
    intro z hz; simpa using (hf.analyticAt z)
  have hDnonneg : 0 ≤ D := by
    simpa [D] using
      (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (𝕜 := ℂ) (f := f) (U := U) hAnal)
  let SR (R : ℝ) : Finset ℂ :=
    (Function.locallyFinsuppWithin.finiteSupport (Function.locallyFinsuppWithin.toClosedBall R D)
          (isCompact_closedBall (0 : ℂ) |R|)).toFinset
  let S (R : ℝ) : Finset ℂ := (SR R).filter fun z : ℂ => z ≠ 0
  have hsub : S R₁ ⊆ S R₂ := by
    intro z hz
    have hzSR₁ : z ∈ SR R₁ := (Finset.mem_filter.1 hz).1
    have hz0 : z ≠ 0 := (Finset.mem_filter.1 hz).2
    have hz_sup₁ :
        z ∈ (Function.locallyFinsuppWithin.toClosedBall R₁ D).support := by
      exact (Set.Finite.mem_toFinset
        (Function.locallyFinsuppWithin.finiteSupport (Function.locallyFinsuppWithin.toClosedBall R₁ D)
          (isCompact_closedBall (0 : ℂ) |R₁|))).1 hzSR₁
    have hz_ball₁ : z ∈ Metric.closedBall (0 : ℂ) |R₁| :=
      (Function.locallyFinsuppWithin.toClosedBall R₁ D).supportWithinDomain hz_sup₁
    have hz_norm₁ : ‖z‖ ≤ R₁ := by
      have : ‖z‖ ≤ |R₁| := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hz_ball₁
      simpa [habs₁] using this
    have hz_norm₂ : ‖z‖ ≤ R₂ := le_trans hz_norm₁ hR₁₂
    have hz_ball₂ : z ∈ Metric.closedBall (0 : ℂ) |R₂| := by
      have : ‖z‖ ≤ |R₂| := by simpa [habs₂] using hz_norm₂
      simpa [Metric.mem_closedBall, dist_zero_right] using this
    have hEq₁ : (Function.locallyFinsuppWithin.toClosedBall R₁ D) z = D z := by
      simpa using
        (Function.locallyFinsuppWithin.toClosedBall_eval_within (r := R₁) (f := D)
          (z := z) hz_ball₁)
    have hEq₂ : (Function.locallyFinsuppWithin.toClosedBall R₂ D) z = D z := by
      simpa using
        (Function.locallyFinsuppWithin.toClosedBall_eval_within (r := R₂) (f := D)
          (z := z) hz_ball₂)
    have hDz_ne : D z ≠ 0 := by
      have : (Function.locallyFinsuppWithin.toClosedBall R₁ D) z ≠ 0 := by
        simpa [Function.mem_support] using hz_sup₁
      simpa [hEq₁] using this
    have hz_sup₂ : z ∈ (Function.locallyFinsuppWithin.toClosedBall R₂ D).support := by
      have : (Function.locallyFinsuppWithin.toClosedBall R₂ D) z ≠ 0 := by
        simpa [hEq₂] using hDz_ne
      simpa [Function.mem_support] using this
    have hzSR₂ : z ∈ SR R₂ := by
      exact (Set.Finite.mem_toFinset
        (Function.locallyFinsuppWithin.finiteSupport (Function.locallyFinsuppWithin.toClosedBall R₂ D)
          (isCompact_closedBall (0 : ℂ) |R₂|))).2 hz_sup₂
    exact Finset.mem_filter.2 ⟨hzSR₂, hz0⟩
  have hterm_nonneg : ∀ z ∈ S R₂, 0 ≤ (MeromorphicOn.divisor f U z : ℝ) := by
    intro z hz
    have : 0 ≤ D z := hDnonneg z
    exact_mod_cast this
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z hz₂ _hznot => hterm_nonneg z hz₂)

lemma exists_r0_le_norm_divisorZeroIndex₀_val {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0) :
    ∃ r0 : ℝ, 0 < r0 ∧ ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), r0 ≤ ‖divisorZeroIndex₀_val p‖ := by
  classical
  set U : Set ℂ := (Set.univ : Set ℂ)
  set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  have hAnal : AnalyticOnNhd ℂ f U := by
    intro z hz
    simpa using (hf.analyticAt z)
  have hDnonneg : 0 ≤ D := by
    simpa [D] using
      (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (𝕜 := ℂ) (f := f) (U := U) hAnal)
  have hzero : ∀ p : divisorZeroIndex₀ f U, f (divisorZeroIndex₀_val p) = 0 := by
    intro p
    set z : ℂ := divisorZeroIndex₀_val p
    have hneTop : meromorphicOrderAt f z ≠ ⊤ := by
      have hzAnal : AnalyticAt ℂ f z := hf.analyticAt z
      have hzA : analyticOrderAt f z ≠ ⊤ :=
        analyticOrderAt_ne_top_of_exists_ne_zero (f := f) (hf := hf) hnot (z := z)
      intro htop
      have hm : meromorphicOrderAt f z = (analyticOrderAt f z).map (↑) :=
        hzAnal.meromorphicOrderAt_eq (𝕜 := ℂ)
      cases h : analyticOrderAt f z with
      | top =>
          exact hzA (by simp [h])
      | coe n =>
          have : (analyticOrderAt f z).map (↑) ≠ (⊤ : WithTop ℤ) := by
            simp [h]
          exact this (by simpa [hm] using htop)
    have hmon : MeromorphicOn f U := by
      intro w hw; exact (hf.analyticAt w).meromorphicAt
    have hdiv : MeromorphicOn.divisor f U z = (meromorphicOrderAt f z).untop₀ := by
      simpa [U] using (MeromorphicOn.divisor_apply (f := f) (U := U) (z := z) hmon (by aesop))
    have hDz : MeromorphicOn.divisor f U z ≠ 0 := by
      have hzsup : z ∈ (MeromorphicOn.divisor f U).support := by
        simp [z]
      simpa [Function.mem_support] using hzsup
    have hposZ : (0 : ℤ) < (meromorphicOrderAt f z).untop₀ := by
      have hge0 : 0 ≤ (meromorphicOrderAt f z).untop₀ := by
        have : 0 ≤ MeromorphicOn.divisor f U z := by
          simpa [D, U, z] using hDnonneg z
        simpa [hdiv] using this
      have hne0 : (meromorphicOrderAt f z).untop₀ ≠ 0 := by
        simpa [hdiv] using hDz
      exact lt_of_le_of_ne hge0 (by simpa [eq_comm] using hne0)
    have hpos : (0 : WithTop ℤ) < meromorphicOrderAt f z := by
      have : (0 : WithTop ℤ) < ((meromorphicOrderAt f z).untop₀ : WithTop ℤ) :=
        WithTop.coe_lt_coe.2 hposZ
      simpa [WithTop.coe_untop₀_of_ne_top hneTop] using this
    have htend0 : Tendsto f (𝓝[≠] z) (𝓝 (0 : ℂ)) :=
      tendsto_zero_of_meromorphicOrderAt_pos (f := f) (x := z) hpos
    have hcontz : ContinuousAt f z := (hf z).continuousAt
    have htendz : Tendsto f (𝓝[≠] z) (𝓝 (f z)) :=
      (hcontz.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] z ≤ 𝓝 z))
    exact tendsto_nhds_unique htendz htend0
  by_cases h0 : f 0 = 0
  · have hD0 : D 0 ≠ 0 := by
      have hmero0 : MeromorphicAt f (0 : ℂ) := (hf.analyticAt 0).meromorphicAt
      have hneTop0 : meromorphicOrderAt f (0 : ℂ) ≠ ⊤ := by
        have hA0 : analyticOrderAt f (0 : ℂ) ≠ ⊤ :=
          analyticOrderAt_ne_top_of_exists_ne_zero (f := f) (hf := hf) hnot (z := 0)
        intro htop
        have hm : meromorphicOrderAt f (0 : ℂ) = (analyticOrderAt f (0 : ℂ)).map (↑) :=
          (hf.analyticAt 0).meromorphicOrderAt_eq (𝕜 := ℂ)
        cases h : analyticOrderAt f (0 : ℂ) with
        | top => exact Ne.elim hA0 h
        | coe n =>
            have : (analyticOrderAt f (0 : ℂ)).map (↑) ≠ (⊤ : WithTop ℤ) := by
              simp [h]
            exact this (by simpa [hm] using htop)
      have htend0 : Tendsto f (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := by
        have hcont0 : ContinuousAt f (0 : ℂ) := (hf 0).continuousAt
        have : Tendsto f (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by simpa [h0] using hcont0.tendsto
        exact this.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 (0 : ℂ))
      have hpos0 : (0 : WithTop ℤ) < meromorphicOrderAt f (0 : ℂ) :=
        (tendsto_zero_iff_meromorphicOrderAt_pos hmero0).1 htend0
      have hpos0' : (0 : ℤ) < (meromorphicOrderAt f (0 : ℂ)).untop₀ := by
        have : (0 : WithTop ℤ) < ((meromorphicOrderAt f (0 : ℂ)).untop₀ : WithTop ℤ) := by
          simpa [WithTop.coe_untop₀_of_ne_top hneTop0] using hpos0
        simpa using (WithTop.coe_lt_coe.1 this)
      have hdiv0 : D 0 = (meromorphicOrderAt f (0 : ℂ)).untop₀ := by
        have hmon : MeromorphicOn f U := by
          intro w hw; exact (hf.analyticAt w).meromorphicAt
        simpa [D, U] using (MeromorphicOn.divisor_apply (f := f) (U := U) (z := (0 : ℂ)) hmon (by aesop))
      exact by
        have : (meromorphicOrderAt f (0 : ℂ)).untop₀ ≠ 0 := ne_of_gt hpos0'
        simpa [hdiv0] using this
    have hmem0 : (0 : ℂ) ∈ D.support := by
      simp [Function.mem_support, hD0]
    have hdisc : IsDiscrete D.support := by
      simpa [D] using (D.discreteSupport)
    rcases Metric.exists_ball_inter_eq_singleton_of_mem_discrete hdisc hmem0 with ⟨r0, hr0pos, hr0⟩
    refine ⟨r0, hr0pos, ?_⟩
    intro p
    have hp : divisorZeroIndex₀_val p ∈ D.support := by
      simpa [D] using (divisorZeroIndex₀_val_mem_divisor_support (f := f) (U := U) p)
    have hnotBall : divisorZeroIndex₀_val p ∉ Metric.ball (0 : ℂ) r0 := by
      intro hball
      have : divisorZeroIndex₀_val p ∈ Metric.ball (0 : ℂ) r0 ∩ D.support := ⟨hball, hp⟩
      have : divisorZeroIndex₀_val p ∈ ({(0 : ℂ)} : Set ℂ) := by simp [hr0] at this
      have : divisorZeroIndex₀_val p = 0 := by simp [Set.mem_singleton_iff] at this
      exact (divisorZeroIndex₀_val_ne_zero p) this
    have : r0 ≤ ‖divisorZeroIndex₀_val p‖ := by
      have : ¬ ‖divisorZeroIndex₀_val p‖ < r0 := by
        intro hlt
        exact hnotBall (by simpa [Metric.mem_ball, dist_zero_right] using hlt)
      exact le_of_not_gt this
    exact this
  · have hcont0 : ContinuousAt f (0 : ℂ) := (hf 0).continuousAt
    have hne : ∀ᶠ z in 𝓝 (0 : ℂ), f z ≠ 0 := hcont0.eventually_ne h0
    rcases Metric.mem_nhds_iff.1 hne with ⟨r0, hr0pos, hr0⟩
    refine ⟨r0, hr0pos, ?_⟩
    intro p
    have : ¬ ‖divisorZeroIndex₀_val p‖ < r0 := by
      intro hlt
      have hzball : divisorZeroIndex₀_val p ∈ Metric.ball (0 : ℂ) r0 := by
        simpa [Metric.mem_ball, dist_zero_right] using hlt
      have : f (divisorZeroIndex₀_val p) ≠ 0 := hr0 hzball
      exact this (hzero p)
    exact le_of_not_gt this


/-!
### Dyadic-shell summability for divisor-indexed zeros
-/

open scoped BigOperators

private lemma two_pow_floor_logb_le {x : ℝ} (hx : 1 ≤ x) :
    (2 : ℝ) ^ (⌊Real.logb 2 x⌋₊ : ℝ) ≤ x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx
  have hlog_nonneg : 0 ≤ Real.logb 2 x :=
    Real.logb_nonneg (b := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2) hx
  have hfloor_le : (⌊Real.logb 2 x⌋₊ : ℝ) ≤ Real.logb 2 x := by
    simpa using (Nat.floor_le hlog_nonneg)
  exact (Real.le_logb_iff_rpow_le (b := (2 : ℝ)) (x := (⌊Real.logb 2 x⌋₊ : ℝ)) (y := x)
    (by norm_num : (1 : ℝ) < 2) hx0).1 hfloor_le

private lemma lt_two_pow_floor_logb_add_one {x : ℝ} (hx : 1 ≤ x) :
    x < (2 : ℝ) ^ ((⌊Real.logb 2 x⌋₊ : ℝ) + 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx
  have hlt : Real.logb 2 x < (⌊Real.logb 2 x⌋₊ : ℝ) + 1 := by
    simpa using (Nat.lt_floor_add_one (Real.logb 2 x))
  exact (Real.logb_lt_iff_lt_rpow (b := (2 : ℝ)) (x := x)
    (y := (⌊Real.logb 2 x⌋₊ : ℝ) + 1) (by norm_num : (1 : ℝ) < 2) hx0).1 hlt

private lemma card_shell_le_sum_divisor_closedBall
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

--set_option maxHeartbeats 0 in
theorem summable_norm_inv_pow_divisorZeroIndex₀_of_growth {f : ℂ → ℂ} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    (hgrowth : ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) :
    Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (Nat.floor ρ + 1)) := by
  classical
  set m : ℕ := Nat.floor ρ
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
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1) := by
    intro p
    exact pow_nonneg (inv_nonneg.2 (norm_nonneg _)) _
  have hSk_summable : ∀ k : ℕ, Summable fun p : S k => ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ (m + 1) := by
    intro k
    haveI : Finite (S k) := by
      have hsub :
          S k ⊆ {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1)} := by
        intro p hp
        have hk : kfun p = k := hp
        have hx1 : (1 : ℝ) ≤ ‖divisorZeroIndex₀_val p‖ / r0 := by
          have : r0 ≤ ‖divisorZeroIndex₀_val p‖ := hr0 p
          have : r0 / r0 ≤ ‖divisorZeroIndex₀_val p‖ / r0 :=
            div_le_div_of_nonneg_right this (le_of_lt hr0pos)
          simpa [hr0ne] using this
        have hlt :
            ‖divisorZeroIndex₀_val p‖ / r0 < (2 : ℝ) ^ ((k : ℝ) + 1) := by
          have := lt_two_pow_floor_logb_add_one (x := ‖divisorZeroIndex₀_val p‖ / r0) hx1
          simpa [kfun, hk] using this
        have := mul_lt_mul_of_pos_left hlt hr0pos
        have hxEq : r0 * (‖divisorZeroIndex₀_val p‖ / r0) = ‖divisorZeroIndex₀_val p‖ := by
          field_simp [hr0ne]
        have : ‖divisorZeroIndex₀_val p‖ < r0 * (2 : ℝ) ^ ((k : ℝ) + 1) := by
          simpa [mul_assoc, hxEq] using this
        exact le_of_lt this
      have hfin :
          ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1)} : Set _).Finite := by
        have : Metric.closedBall (0 : ℂ) (r0 * (2 : ℝ) ^ ((k : ℝ) + 1)) ⊆ (Set.univ : Set ℂ) := by simp
        simpa using (divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ))
          (B := r0 * (2 : ℝ) ^ ((k : ℝ) + 1)) this)
      exact (hfin.subset hsub).to_subtype
    exact Summable.of_finite
  have hshell_summable :
      Summable fun k : ℕ => ∑' p : S k, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ (m + 1) := by
    have hρ_lt : (ρ : ℝ) < (m + 1 : ℝ) := by
      have : ρ < (m : ℝ) + 1 := by
        simpa [m] using (Nat.lt_floor_add_one (a := ρ))
      simpa [add_comm, add_left_comm, add_assoc] using this
    let q : ℝ := (2 : ℝ) ^ (ρ - (m + 1 : ℝ))
    let qσ : ℝ := (2 : ℝ) ^ (-(m + 1 : ℝ))
    have hq_nonneg : 0 ≤ q := le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
    have hq_lt_one : q < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (x := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
        (sub_neg.2 hρ_lt)
    have hqσ_nonneg : 0 ≤ qσ := le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
    have hqσ_lt_one : qσ < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (x := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
        (by
          have : (0 : ℝ) < (m + 1 : ℝ) := by positivity
          linarith)
    have hgeom_q : Summable (fun k : ℕ => q ^ k) :=
      summable_geometric_of_lt_one hq_nonneg hq_lt_one
    have hgeom_qσ : Summable (fun k : ℕ => qσ ^ k) :=
      summable_geometric_of_lt_one hqσ_nonneg hqσ_lt_one
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hlog2ne : (Real.log 2) ≠ 0 := ne_of_gt hlog2pos
    let Cgrow : ℝ := Classical.choose hgrowth
    let Ctrail : ℝ := |Real.log ‖meromorphicTrailingCoeffAt f 0‖|
    let A : ℝ := ((Cgrow / Real.log 2) * (1 + 4 * r0) ^ ρ) * (r0⁻¹) ^ (m + 1)
    let B : ℝ := ((Ctrail / Real.log 2) + 1) * (r0⁻¹) ^ (m + 1)
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
        Summable fun k : ℕ => ∑' p : S (k + k0), ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ (m + 1) := by
      refine (Summable.of_nonneg_of_le
        (f := fun k : ℕ => A0 * q ^ k + B0 * qσ ^ k)
        (g := fun k : ℕ => ∑' p : S (k + k0), ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ (m + 1))
        (fun k => by
          have : ∀ p : S (k + k0), 0 ≤ ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ (m + 1) := by
            intro p; exact pow_nonneg (inv_nonneg.2 (norm_nonneg _)) _
          exact tsum_nonneg this)
        (fun k => by
          let kk : ℕ := k + k0
          let rk : ℝ := r0 * (2 : ℝ) ^ (kk : ℝ)
          let Rk : ℝ := r0 * (2 : ℝ) ^ ((kk : ℝ) + 1)
          have hrk_pos : 0 < rk := mul_pos hr0pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
          have hRk_pos : 0 < Rk := mul_pos hr0pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
          have hk_lower : ∀ p : S kk, rk ≤ ‖divisorZeroIndex₀_val p.1‖ := by
            intro p
            have hp' : kfun p.1 = kk := p.2
            have hx1 : (1 : ℝ) ≤ ‖divisorZeroIndex₀_val p.1‖ / r0 := by
              have : r0 ≤ ‖divisorZeroIndex₀_val p.1‖ := hr0 p.1
              have : r0 / r0 ≤ ‖divisorZeroIndex₀_val p.1‖ / r0 :=
                div_le_div_of_nonneg_right this (le_of_lt hr0pos)
              simpa [hr0ne] using this
            have hle : (2 : ℝ) ^ (kk : ℝ) ≤ ‖divisorZeroIndex₀_val p.1‖ / r0 := by
              have := two_pow_floor_logb_le (x := ‖divisorZeroIndex₀_val p.1‖ / r0) hx1
              simpa [kfun, hp'] using this
            have := mul_le_mul_of_nonneg_left hle (le_of_lt hr0pos)
            have hxEq : r0 * (‖divisorZeroIndex₀_val p.1‖ / r0) = ‖divisorZeroIndex₀_val p.1‖ := by
              field_simp [hr0ne]
            simpa [rk, mul_assoc, hxEq] using this
          have hk_upper : ∀ p : S kk, ‖divisorZeroIndex₀_val p.1‖ ≤ Rk := by
            intro p
            have hp' : kfun p.1 = kk := p.2
            have hx1 : (1 : ℝ) ≤ ‖divisorZeroIndex₀_val p.1‖ / r0 := by
              have : r0 ≤ ‖divisorZeroIndex₀_val p.1‖ := hr0 p.1
              have : r0 / r0 ≤ ‖divisorZeroIndex₀_val p.1‖ / r0 :=
                div_le_div_of_nonneg_right this (le_of_lt hr0pos)
              simpa [hr0ne] using this
            have hlt : ‖divisorZeroIndex₀_val p.1‖ / r0 < (2 : ℝ) ^ ((kk : ℝ) + 1) := by
              have := lt_two_pow_floor_logb_add_one (x := ‖divisorZeroIndex₀_val p.1‖ / r0) hx1
              simpa [kfun, hp'] using this
            have := mul_lt_mul_of_pos_left hlt hr0pos
            have hxEq : r0 * (‖divisorZeroIndex₀_val p.1‖ / r0) = ‖divisorZeroIndex₀_val p.1‖ := by
              field_simp [hr0ne]
            have : ‖divisorZeroIndex₀_val p.1‖ < Rk := by
              simpa [Rk, mul_assoc, hxEq] using this
            exact le_of_lt this
          haveI : Finite (S kk) := by
            have hfin :
                ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ Rk} : Set _).Finite := by
              have : Metric.closedBall (0 : ℂ) Rk ⊆ (Set.univ : Set ℂ) := by simp
              simpa [Rk] using
                (divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ)) (B := Rk) this)
            have hsub : S kk ⊆ {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ Rk} := by
              intro p hp; exact hk_upper ⟨p, hp⟩
            exact (hfin.subset hsub).to_subtype
          haveI : Fintype (S kk) := Fintype.ofFinite _
          have hterm_le : ∀ p : S kk, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ (m + 1) ≤ rk⁻¹ ^ (m + 1) := by
            intro p
            have hrk_le : rk ≤ ‖divisorZeroIndex₀_val p.1‖ := hk_lower p
            have hinv' : ‖divisorZeroIndex₀_val p.1‖⁻¹ ≤ rk⁻¹ := by
              have : (1 / ‖divisorZeroIndex₀_val p.1‖ : ℝ) ≤ 1 / rk :=
                one_div_le_one_div_of_le hrk_pos hrk_le
              simpa [one_div] using this
            exact pow_le_pow_left₀ (inv_nonneg.2 (norm_nonneg _)) hinv' _
          have htsum_le :
              (∑' p : S kk, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ (m + 1))
                ≤ (Fintype.card (S kk) : ℝ) * (rk⁻¹ ^ (m + 1)) := by
            classical
            have hsum_le :
                (∑ p : S kk, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ (m + 1))
                  ≤ ∑ _p : S kk, (rk⁻¹ ^ (m + 1)) := by
              refine Finset.sum_le_sum ?_
              intro p _hp
              exact hterm_le p
            simpa [tsum_fintype, Finset.sum_const, nsmul_eq_mul] using
              (hsum_le.trans_eq (by
                simp [Finset.sum_const, nsmul_eq_mul, mul_comm]))
          have hcard_le_mass :
              (Fintype.card (S kk) : ℝ) ≤
                ((((Function.locallyFinsuppWithin.finiteSupport
                        (Function.locallyFinsuppWithin.toClosedBall Rk
                          (MeromorphicOn.divisor f (Set.univ : Set ℂ)))
                        (isCompact_closedBall (0 : ℂ) |Rk|)).toFinset).filter fun z : ℂ => z ≠ 0).sum
                    fun z : ℂ => (MeromorphicOn.divisor f (Set.univ : Set ℂ) z : ℝ)) := by
            classical
            let Aball : Type :=
              {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) // ‖divisorZeroIndex₀_val p‖ ≤ Rk}
            haveI : Fintype Aball := by
              classical
              have : Finite Aball := by
                have : Metric.closedBall (0 : ℂ) Rk ⊆ (Set.univ : Set ℂ) := by simp
                simpa using
                  (finite_divisorZeroIndex₀_subtype_norm_le (f := f) (U := (Set.univ : Set ℂ)) (B := Rk) this)
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
                          (isCompact_closedBall (0 : ℂ) |Rk|)).toFinset).filter fun z : ℂ => z ≠ 0).sum
                      fun z : ℂ => (MeromorphicOn.divisor f (Set.univ : Set ℂ) z : ℝ)) :=
              card_shell_le_sum_divisor_closedBall (f := f) hf hnot (r0 := r0) (R := Rk) hr0pos hRk_lower
            calc
              (Fintype.card (S kk) : ℝ) ≤ (Fintype.card Aball : ℝ) := by exact_mod_cast hcard_le
              _ = (Nat.card Aball : ℝ) := by simp [Nat.card_eq_fintype_card]
              _ ≤ _ := hAball
          have hRk_ge_one : (1 : ℝ) ≤ Rk := by
            have hpow_nat : (1 / r0) ≤ (2 : ℝ) ^ (kk + 1) := by
              have hkk : k0 ≤ kk + 1 := by
                simp [kk, Nat.add_assoc, Nat.add_comm]
              exact hk0 (kk + 1) hkk
            have hpow_rpow : (1 / r0) ≤ (2 : ℝ) ^ ((kk : ℝ) + 1) := by
              have hEq : (2 : ℝ) ^ ((kk : ℝ) + 1) = (2 : ℝ) ^ (kk + 1) := by
                calc
                  (2 : ℝ) ^ ((kk : ℝ) + 1) = (2 : ℝ) ^ ((kk + 1 : ℕ) : ℝ) := by simp
                  _ = (2 : ℝ) ^ (kk + 1) := by simpa using (Real.rpow_natCast (2 : ℝ) (kk + 1))
              simpa [hEq] using hpow_nat
            have : (r0 * (1 / r0) : ℝ) ≤ r0 * (2 : ℝ) ^ ((kk : ℝ) + 1) :=
              mul_le_mul_of_nonneg_left hpow_rpow hr0pos.le
            simpa [Rk, one_div, hr0ne, mul_assoc] using this
          have hmass_le_growth :
            ((((Function.locallyFinsuppWithin.finiteSupport
                      (Function.locallyFinsuppWithin.toClosedBall Rk
                        (MeromorphicOn.divisor f (Set.univ : Set ℂ)))
                      (isCompact_closedBall (0 : ℂ) |Rk|)).toFinset).filter fun z : ℂ => z ≠ 0).sum
                  fun z : ℂ => (MeromorphicOn.divisor f (Set.univ : Set ℂ) z : ℝ))
              ≤ (Cgrow * (1 + |2 * Rk|) ^ ρ + Ctrail) / (Real.log 2) := by
            simpa [Cgrow, Ctrail] using
              (sum_divisor_closedBall_le_of_growth (f := f) (ρ := ρ) hf hgrowth (R := Rk) hRk_ge_one)
          have hrk_inv : rk⁻¹ ^ (m + 1) = (r0⁻¹ ^ (m + 1)) * qσ ^ kk := by
            have h2 : ((2 : ℝ) ^ (-1 - (m : ℝ))) = (2⁻¹ : ℝ) ^ (m + 1) := by
              have hneg0 :
                  (2 : ℝ) ^ (-(m + 1 : ℝ)) = ((2 : ℝ) ^ (m + 1 : ℝ))⁻¹ :=
                Real.rpow_neg (by positivity : (0 : ℝ) ≤ (2 : ℝ)) (m + 1 : ℝ)
              have hneg :
                  (2 : ℝ) ^ (-1 - (m : ℝ)) = ((2 : ℝ) ^ (m + 1 : ℝ))⁻¹ := by
                simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hneg0
              calc
                (2 : ℝ) ^ (-1 - (m : ℝ)) = ((2 : ℝ) ^ (m + 1 : ℝ))⁻¹ := hneg
                _ = ((2 : ℝ) ^ (m + 1))⁻¹ := by
                      simpa [Nat.cast_add_one] using (Real.rpow_natCast (2 : ℝ) (m + 1))
                _ = (2⁻¹ : ℝ) ^ (m + 1) := by simp
            have hcombine : (2⁻¹ : ℝ) ^ kk * (2⁻¹ : ℝ) ^ (kk * m) = (2⁻¹ : ℝ) ^ (kk * (m + 1)) := by
              calc
                (2⁻¹ : ℝ) ^ kk * (2⁻¹ : ℝ) ^ (kk * m) = (2⁻¹ : ℝ) ^ (kk + kk * m) := by
                  simp [pow_add]
                _ = (2⁻¹ : ℝ) ^ (kk * (m + 1)) := by
                  congr 1
                  nlinarith [Nat.mul_add kk m 1]
            have : rk⁻¹ ^ (m + 1) =
                (r0⁻¹ ^ (m + 1)) * ((2⁻¹ : ℝ) ^ kk * (2⁻¹ : ℝ) ^ (kk * m)) := by
              have h2ne : ((2 : ℝ) ^ kk) ≠ 0 := by
                exact pow_ne_zero kk (by norm_num : (2 : ℝ) ≠ 0)
              simp [rk, pow_add, pow_mul, mul_pow, inv_pow,
                mul_assoc, mul_left_comm, mul_comm]
            calc
              rk⁻¹ ^ (m + 1)
                  = (r0⁻¹ ^ (m + 1)) * ((2⁻¹ : ℝ) ^ kk * (2⁻¹ : ℝ) ^ (kk * m)) := this
              _ = (r0⁻¹ ^ (m + 1)) * (2⁻¹ : ℝ) ^ (kk * (m + 1)) := by
                    simpa [mul_assoc] using congrArg (fun x => (r0⁻¹ ^ (m + 1)) * x) hcombine
              _ = (r0⁻¹ ^ (m + 1)) * ((2 : ℝ) ^ (-1 - (m : ℝ))) ^ kk := by
                    have hb : (2⁻¹ : ℝ) ^ (kk * (m + 1)) = ((2 : ℝ) ^ (-1 - (m : ℝ))) ^ kk := by
                      calc
                        (2⁻¹ : ℝ) ^ (kk * (m + 1)) = ((2⁻¹ : ℝ) ^ (m + 1)) ^ kk := by
                          simpa [Nat.mul_comm] using (pow_mul (2⁻¹ : ℝ) (m + 1) kk)
                        _ = ((2 : ℝ) ^ (-1 - (m : ℝ))) ^ kk := by
                          simp [h2]
                    simp [hb]
              _ = (r0⁻¹ ^ (m + 1)) * qσ ^ kk := by
                    simp [qσ, sub_eq_add_neg, add_comm,]
          have hpow_bound :
              (1 + |2 * Rk|) ^ ρ ≤ (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ kk := by
            have hk1 : (1 : ℝ) ≤ (2 : ℝ) ^ (kk : ℝ) :=
              Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) (by linarith)
            have habs : |2 * Rk| = (4 * r0) * ((2 : ℝ) ^ (kk : ℝ)) := by
              have hnonneg : 0 ≤ 2 * Rk := by nlinarith [hRk_pos.le]
              have : 2 * Rk = (4 * r0) * ((2 : ℝ) ^ (kk : ℝ)) := by
                have h2pos : (0 : ℝ) < 2 := by norm_num
                calc
                  2 * Rk
                      = 2 * (r0 * (2 : ℝ) ^ ((kk : ℝ) + 1)) := by simp [Rk]
                  _ = (2 * r0) * ((2 : ℝ) ^ (kk : ℝ) * (2 : ℝ) ^ (1 : ℝ)) := by
                        simp [mul_assoc, Real.rpow_add h2pos]
                  _ = (4 * r0) * ((2 : ℝ) ^ (kk : ℝ)) := by
                        simp [Real.rpow_one]
                        ring
              have habs1 : |2 * Rk| = 2 * Rk := abs_of_nonneg hnonneg
              calc
                |2 * Rk| = 2 * Rk := habs1
                _ = (4 * r0) * ((2 : ℝ) ^ (kk : ℝ)) := this
            have hRk_le : 1 + |2 * Rk| ≤ (1 + 4 * r0) * ((2 : ℝ) ^ (kk : ℝ)) := by
              have : 1 + (4 * r0) * ((2 : ℝ) ^ (kk : ℝ)) ≤ (1 + 4 * r0) * ((2 : ℝ) ^ (kk : ℝ)) := by
                nlinarith [hk1]
              simpa [habs] using this
            have hpow :
                (1 + |2 * Rk|) ^ ρ ≤ ((1 + 4 * r0) * ((2 : ℝ) ^ (kk : ℝ))) ^ ρ :=
              Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 1 + |2 * Rk|) hRk_le hρ
            have hrhs :
                ((1 + 4 * r0) * ((2 : ℝ) ^ (kk : ℝ))) ^ ρ
                  = (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ kk := by
              have hkk : ((2 : ℝ) ^ ρ) ^ kk = ((2 : ℝ) ^ ρ) ^ ((kk : ℕ) : ℝ) := by
                simp
              calc
                ((1 + 4 * r0) * ((2 : ℝ) ^ (kk : ℝ))) ^ ρ
                    = (1 + 4 * r0) ^ ρ * (((2 : ℝ) ^ (kk : ℝ)) ^ ρ) := by
                        have hr0nonneg : 0 ≤ r0 := le_of_lt hr0pos
                        have h14nonneg : 0 ≤ (1 + 4 * r0) := by nlinarith
                        have h2nonneg : 0 ≤ (2 : ℝ) ^ (kk : ℝ) :=
                          le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
                        simp [Real.mul_rpow, h14nonneg]
                _ = (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ((kk : ℝ) * ρ)) := by
                        simp [Real.rpow_mul, (by positivity : (0 : ℝ) ≤ (2 : ℝ))]
                _ = (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ kk := by
                        have h2mul :
                            (2 : ℝ) ^ ((kk : ℝ) * ρ) = ((2 : ℝ) ^ ρ) ^ (kk : ℝ) := by
                          calc
                            (2 : ℝ) ^ ((kk : ℝ) * ρ) = (2 : ℝ) ^ (ρ * (kk : ℝ)) := by
                              simp [mul_comm]
                            _ = ((2 : ℝ) ^ ρ) ^ (kk : ℝ) := by
                              simpa using (Real.rpow_mul (x := (2 : ℝ)) (by positivity) ρ (kk : ℝ))
                        simp [h2mul, hkk.symm]
            exact hpow.trans_eq hrhs
          have : (∑' p : S (k + k0), ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ (m + 1)) ≤
            A0 * q ^ k + B0 * qσ ^ k := by
            have hmain :
                (∑' p : S kk, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ (m + 1)) ≤ A * q ^ kk + B * qσ ^ kk := by
              have hcard_le_growth :
                  (Fintype.card (S kk) : ℝ) ≤ (Cgrow * (1 + |2 * Rk|) ^ ρ + Ctrail) / (Real.log 2) := by
                exact le_trans hcard_le_mass (le_trans hmass_le_growth (by
                  simp [Ctrail, add_comm]))
              have htsum' :
                  (∑' p : S kk, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ (m + 1))
                    ≤ ((Cgrow * (1 + |2 * Rk|) ^ ρ + Ctrail) / (Real.log 2)) * (rk⁻¹ ^ (m + 1)) := by
                have :
                    (Fintype.card (S kk) : ℝ) * (rk⁻¹ ^ (m + 1))
                      ≤ ((Cgrow * (1 + |2 * Rk|) ^ ρ + Ctrail) / (Real.log 2)) * (rk⁻¹ ^ (m + 1)) := by
                  exact mul_le_mul_of_nonneg_right hcard_le_growth (by
                    exact pow_nonneg (inv_nonneg.2 hrk_pos.le) _)
                exact le_trans htsum_le this
              have hq_split : q ^ kk = ((2 : ℝ) ^ ρ) ^ kk * qσ ^ kk := by
                have h2pos : (0 : ℝ) < 2 := by norm_num
                have hq_fac : q = ((2 : ℝ) ^ ρ) * qσ := by
                  simp [q, qσ, sub_eq_add_neg, Real.rpow_add h2pos]
                simp [hq_fac, mul_pow]
              calc
                (∑' p : S kk, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ (m + 1))
                    ≤ ((Cgrow * (1 + |2 * Rk|) ^ ρ + Ctrail) / (Real.log 2)) * (rk⁻¹ ^ (m + 1)) := htsum'
                _ = ((Cgrow / Real.log 2) * (1 + |2 * Rk|) ^ ρ) * (rk⁻¹ ^ (m + 1))
                      + ((Ctrail / Real.log 2) * (rk⁻¹ ^ (m + 1))) := by
                        field_simp [hlog2ne]
                _ ≤ ((Cgrow / Real.log 2) * ((1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ kk)) * (rk⁻¹ ^ (m + 1))
                      + ((Ctrail / Real.log 2) * (rk⁻¹ ^ (m + 1))) := by
                        have hCgrow_pos : 0 < Cgrow := (Classical.choose_spec hgrowth).1
                        have hCgrow_nonneg : 0 ≤ Cgrow / Real.log 2 :=
                          div_nonneg hCgrow_pos.le hlog2pos.le
                        have hrk_nonneg : 0 ≤ (rk⁻¹ ^ (m + 1)) :=
                          pow_nonneg (inv_nonneg.2 hrk_pos.le) _
                        have hmul :
                            ((Cgrow / Real.log 2) * (1 + |2 * Rk|) ^ ρ) * (rk⁻¹ ^ (m + 1))
                              ≤ ((Cgrow / Real.log 2) * ((1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ kk))
                                  * (rk⁻¹ ^ (m + 1)) := by
                          exact mul_le_mul_of_nonneg_right
                            (mul_le_mul_of_nonneg_left hpow_bound hCgrow_nonneg) hrk_nonneg
                        simpa [mul_assoc, mul_left_comm, mul_comm] using
                          add_le_add_right hmul ((Ctrail / Real.log 2) * (rk⁻¹ ^ (m + 1)))
                _ ≤ A * q ^ kk + B * qσ ^ kk := by
                      have hr0Inv_nonneg : 0 ≤ (r0⁻¹ : ℝ) ^ (m + 1) := by
                        have : 0 ≤ (r0⁻¹ : ℝ) := inv_nonneg.2 (le_of_lt hr0pos)
                        exact pow_nonneg this _
                      have hqσ_nonneg' : 0 ≤ qσ ^ kk := by
                        exact pow_nonneg hqσ_nonneg _
                      have hAterm :
                          ((Cgrow / Real.log 2) * ((1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ kk))
                              * (rk⁻¹ ^ (m + 1))
                            = A * q ^ kk := by
                        rw [hrk_inv]
                        dsimp [A]
                        rw [hq_split]
                        ac_rfl
                      have hBterm :
                          ((Ctrail / Real.log 2) * (rk⁻¹ ^ (m + 1))) ≤ B * qσ ^ kk := by
                        rw [hrk_inv]
                        have hcoeff :
                            (Ctrail / Real.log 2) * ((r0⁻¹ : ℝ) ^ (m + 1))
                              ≤ ((Ctrail / Real.log 2) + 1) * ((r0⁻¹ : ℝ) ^ (m + 1)) := by
                          have : (Ctrail / Real.log 2) ≤ (Ctrail / Real.log 2) + 1 := by linarith
                          exact mul_le_mul_of_nonneg_right this hr0Inv_nonneg
                        have hmul' :
                            ((Ctrail / Real.log 2) * ((r0⁻¹ : ℝ) ^ (m + 1))) * (qσ ^ kk)
                              ≤ (((Ctrail / Real.log 2) + 1) * ((r0⁻¹ : ℝ) ^ (m + 1))) * (qσ ^ kk) :=
                          mul_le_mul_of_nonneg_right hcoeff hqσ_nonneg'
                        dsimp [B]
                        simpa [mul_assoc, mul_left_comm, mul_comm] using hmul'
                      have := add_le_add (le_of_eq hAterm) hBterm
                      simpa [mul_assoc, mul_left_comm, mul_comm, add_assoc] using this
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
          simpa [kk] using this))
        hmajor
    exact (summable_nat_add_iff k0).1 hshell_summable_shift
  have hpart :=
    (summable_partition (f := fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
        ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)) hnonneg (s := S) hS)
  have : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
        ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)) :=
    (hpart.2 ⟨hSk_summable, hshell_summable⟩)
  simpa [m] using this


set_option maxHeartbeats 0 in
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
        have hx1 : (1 : ℝ) ≤ ‖divisorZeroIndex₀_val p‖ / r0 := by
          have : r0 ≤ ‖divisorZeroIndex₀_val p‖ := hr0 p
          have : r0 / r0 ≤ ‖divisorZeroIndex₀_val p‖ / r0 :=
            div_le_div_of_nonneg_right this (le_of_lt hr0pos)
          simpa [hr0ne] using this
        have hlt :
            ‖divisorZeroIndex₀_val p‖ / r0 < (2 : ℝ) ^ ((k : ℝ) + 1) := by
          have := lt_two_pow_floor_logb_add_one (x := ‖divisorZeroIndex₀_val p‖ / r0) hx1
          simpa [kfun, hk] using this
        have := mul_lt_mul_of_pos_left hlt hr0pos
        have hxEq : r0 * (‖divisorZeroIndex₀_val p‖ / r0) = ‖divisorZeroIndex₀_val p‖ := by
          field_simp [hr0ne]
        have : ‖divisorZeroIndex₀_val p‖ < r0 * (2 : ℝ) ^ ((k : ℝ) + 1) := by
          simpa [mul_assoc, hxEq] using this
        exact le_of_lt this
      have hfin :
          ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) |
            ‖divisorZeroIndex₀_val p‖ ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1)} : Set _).Finite := by
        have : Metric.closedBall (0 : ℂ) (r0 * (2 : ℝ) ^ ((k : ℝ) + 1)) ⊆ (Set.univ : Set ℂ) := by simp
        simpa using (divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ))
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
                S kk ⊆ {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ Rk} := by
              intro p hp
              have hk' : kfun p = kk := hp
              have hx1 : (1 : ℝ) ≤ ‖divisorZeroIndex₀_val p‖ / r0 := by
                have : r0 ≤ ‖divisorZeroIndex₀_val p‖ := hr0 p
                have : r0 / r0 ≤ ‖divisorZeroIndex₀_val p‖ / r0 :=
                  div_le_div_of_nonneg_right this (le_of_lt hr0pos)
                simpa [hr0ne] using this
              have hlt :
                  ‖divisorZeroIndex₀_val p‖ / r0 < (2 : ℝ) ^ ((kk : ℝ) + 1) := by
                have := lt_two_pow_floor_logb_add_one (x := ‖divisorZeroIndex₀_val p‖ / r0) hx1
                simpa [kfun, hk'] using this
              have := mul_lt_mul_of_pos_left hlt hr0pos
              have hxEq : r0 * (‖divisorZeroIndex₀_val p‖ / r0) = ‖divisorZeroIndex₀_val p‖ := by
                field_simp [hr0ne]
              have : ‖divisorZeroIndex₀_val p‖ < Rk := by
                simpa [Rk, mul_assoc, hxEq] using this
              exact le_of_lt this
            have hfin :
                ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ Rk} : Set _).Finite := by
              have : Metric.closedBall (0 : ℂ) Rk ⊆ (Set.univ : Set ℂ) := by simp
              simpa using
                (divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ)) (B := Rk) this)
            exact (hfin.subset hsub).to_subtype
          haveI : Fintype (S kk) := Fintype.ofFinite (S kk)
          have hk_upper : ∀ p : S kk, ‖divisorZeroIndex₀_val p.1‖ ≤ Rk := by
            intro p
            have hk' : kfun p.1 = kk := p.2
            have hx1 : (1 : ℝ) ≤ ‖divisorZeroIndex₀_val p.1‖ / r0 := by
              have : r0 ≤ ‖divisorZeroIndex₀_val p.1‖ := hr0 p.1
              have : r0 / r0 ≤ ‖divisorZeroIndex₀_val p.1‖ / r0 :=
                div_le_div_of_nonneg_right this (le_of_lt hr0pos)
              simpa [hr0ne] using this
            have hlt :
                ‖divisorZeroIndex₀_val p.1‖ / r0 < (2 : ℝ) ^ ((kk : ℝ) + 1) := by
              have := lt_two_pow_floor_logb_add_one (x := ‖divisorZeroIndex₀_val p.1‖ / r0) hx1
              simpa [kfun, hk'] using this
            have := mul_lt_mul_of_pos_left hlt hr0pos
            have hxEq : r0 * (‖divisorZeroIndex₀_val p.1‖ / r0) = ‖divisorZeroIndex₀_val p.1‖ := by
              field_simp [hr0ne]
            have : ‖divisorZeroIndex₀_val p.1‖ < Rk := by
              simpa [Rk, mul_assoc, hxEq] using this
            exact le_of_lt this
          have hk_lower : ∀ p : S kk, rk ≤ ‖divisorZeroIndex₀_val p.1‖ := by
            intro p
            have hk' : kfun p.1 = kk := p.2
            have hx1 : (1 : ℝ) ≤ ‖divisorZeroIndex₀_val p.1‖ / r0 := by
              have : r0 ≤ ‖divisorZeroIndex₀_val p.1‖ := hr0 p.1
              have : r0 / r0 ≤ ‖divisorZeroIndex₀_val p.1‖ / r0 :=
                div_le_div_of_nonneg_right this (le_of_lt hr0pos)
              simpa [hr0ne] using this
            have hle :
                (2 : ℝ) ^ (kk : ℝ) ≤ ‖divisorZeroIndex₀_val p.1‖ / r0 := by
              have := two_pow_floor_logb_le (x := ‖divisorZeroIndex₀_val p.1‖ / r0) hx1
              simpa [kfun, hk'] using this
            have := mul_le_mul_of_nonneg_left hle (le_of_lt hr0pos)
            have hxEq : r0 * (‖divisorZeroIndex₀_val p.1‖ / r0) = ‖divisorZeroIndex₀_val p.1‖ := by
              field_simp [hr0ne]
            have : rk ≤ ‖divisorZeroIndex₀_val p.1‖ := by
              simpa [rk, mul_assoc, hxEq] using this
            exact this
          have htsum_le :
              (∑' p : S kk, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ)
                ≤ (Fintype.card (S kk) : ℝ) * (rk⁻¹ ^ τ) := by
            classical
            have hterm_le : ∀ p : S kk, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ ≤ rk⁻¹ ^ τ := by
              intro p
              have hinv : ‖divisorZeroIndex₀_val p.1‖⁻¹ ≤ rk⁻¹ := by
                simpa using (inv_anti₀ hrk_pos (hk_lower p))
              exact Real.rpow_le_rpow (inv_nonneg.2 (norm_nonneg _)) hinv (le_of_lt hτpos)
            have hsum_le :
                (∑ p : S kk, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ)
                  ≤ ∑ _p : S kk, rk⁻¹ ^ τ := by
              refine Finset.sum_le_sum ?_
              intro p _hp
              exact hterm_le p
            have hconst :
                (∑ _p : S kk, rk⁻¹ ^ τ) = (Fintype.card (S kk) : ℝ) * (rk⁻¹ ^ τ) := by
              classical
              simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
            have : (∑' p : S kk, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ)
                ≤ (∑ p : S kk, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ) := by
              simp [tsum_fintype]
            simpa [tsum_fintype, hconst] using (hsum_le.trans_eq hconst)
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
                        (isCompact_closedBall (0 : ℂ) |Rk|)).toFinset).filter fun z : ℂ => z ≠ 0).sum
                  fun z : ℂ => (MeromorphicOn.divisor f (Set.univ : Set ℂ) z : ℝ))
                ≤ (Cgrow * (1 + |2 * Rk|) ^ ρ + Ctrail) / (Real.log 2) := by
            simpa [Cgrow, Ctrail] using
              (sum_divisor_closedBall_le_of_growth (f := f) (ρ := ρ) hf hgrowth (R := Rk) hRk_ge_one)
          have hcard_le_mass :
              (Fintype.card (S kk) : ℝ) ≤
                ((((Function.locallyFinsuppWithin.finiteSupport
                        (Function.locallyFinsuppWithin.toClosedBall Rk
                          (MeromorphicOn.divisor f (Set.univ : Set ℂ)))
                        (isCompact_closedBall (0 : ℂ) |Rk|)).toFinset).filter fun z : ℂ => z ≠ 0).sum
                    fun z : ℂ => (MeromorphicOn.divisor f (Set.univ : Set ℂ) z : ℝ)) := by
            classical
            let Aball : Type :=
              {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) // ‖divisorZeroIndex₀_val p‖ ≤ Rk}
            haveI : Fintype Aball := by
              classical
              have : Finite Aball := by
                have : Metric.closedBall (0 : ℂ) Rk ⊆ (Set.univ : Set ℂ) := by simp
                simpa using
                  (finite_divisorZeroIndex₀_subtype_norm_le (f := f) (U := (Set.univ : Set ℂ)) (B := Rk) this)
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
                          (isCompact_closedBall (0 : ℂ) |Rk|)).toFinset).filter fun z : ℂ => z ≠ 0).sum
                      fun z : ℂ => (MeromorphicOn.divisor f (Set.univ : Set ℂ) z : ℝ)) :=
              card_shell_le_sum_divisor_closedBall (f := f) hf hnot (r0 := r0) (R := Rk) hr0pos hRk_lower
            calc
              (Fintype.card (S kk) : ℝ) ≤ (Fintype.card Aball : ℝ) := by exact_mod_cast hcard_le
              _ = (Nat.card Aball : ℝ) := by simp [Nat.card_eq_fintype_card]
              _ ≤ _ := hAball
          have htsum' :
              (∑' p : S kk, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ)
                ≤ ((Cgrow * (1 + |2 * Rk|) ^ ρ + Ctrail) / (Real.log 2)) * (rk⁻¹ ^ τ) := by
            have hcard_le_growth :
                (Fintype.card (S kk) : ℝ) ≤ (Cgrow * (1 + |2 * Rk|) ^ ρ + Ctrail) / (Real.log 2) :=
              le_trans hcard_le_mass hmass_le_growth
            have := mul_le_mul_of_nonneg_right hcard_le_growth (Real.rpow_nonneg (inv_nonneg.2 hrk0) τ)
            exact le_trans htsum_le this
          have hpow_bound :
              (1 + |2 * Rk|) ^ ρ ≤ (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ kk := by
            have hRk' : |2 * Rk| = 4 * r0 * (2 : ℝ) ^ (kk : ℝ) := by
              have hnonneg : 0 ≤ (2 : ℝ) * Rk := by
                have : 0 ≤ Rk := by
                  dsimp [Rk]
                  exact mul_nonneg hr0pos.le (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
                nlinarith
              have hmul : (2 : ℝ) * Rk = 4 * r0 * (2 : ℝ) ^ (kk : ℝ) := by
                dsimp [Rk]
                calc
                  (2 : ℝ) * (r0 * (2 : ℝ) ^ ((kk : ℝ) + 1))
                      = (2 * r0) * (2 : ℝ) ^ ((kk : ℝ) + 1) := by ring
                  _ = (2 * r0) * ((2 : ℝ) ^ (kk : ℝ) * (2 : ℝ) ^ (1 : ℝ)) := by
                        simp [Real.rpow_add, mul_assoc]
                  _ = (2 * r0) * ((2 : ℝ) ^ (kk : ℝ) * 2) := by simp [Real.rpow_one]
                  _ = 4 * r0 * (2 : ℝ) ^ (kk : ℝ) := by ring
              calc
                |2 * Rk| = 2 * Rk := abs_of_nonneg hnonneg
                _ = 4 * r0 * (2 : ℝ) ^ (kk : ℝ) := hmul
            have hbase :
                (1 + |2 * Rk|) ≤ (1 + 4 * r0) * (2 : ℝ) ^ (kk : ℝ) := by
              have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (kk : ℝ) := by
                have : (1 : ℝ) ≤ (2 : ℝ) ^ (kk : ℕ) := by
                  simpa using (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ (2 : ℝ)))
                simpa [Real.rpow_natCast] using this
              have habs : 1 + |2 * Rk| ≤ (2 : ℝ) ^ (kk : ℝ) + (4 * r0) * (2 : ℝ) ^ (kk : ℝ) := by
                rw [hRk']
                simpa [add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using
                  (add_le_add_right h1 ((4 * r0) * (2 : ℝ) ^ (kk : ℝ)))
              have hfac :
                  (2 : ℝ) ^ (kk : ℝ) + (4 * r0) * (2 : ℝ) ^ (kk : ℝ)
                    = (1 + 4 * r0) * (2 : ℝ) ^ (kk : ℝ) := by
                ring
              exact habs.trans (le_of_eq hfac)
            have hRnonneg : 0 ≤ (1 + |2 * Rk|) := by linarith [abs_nonneg (2 * Rk)]
            have hbase_nonneg : 0 ≤ (1 + 4 * r0) * (2 : ℝ) ^ (kk : ℝ) := by
              have : 0 ≤ (1 + 4 * r0) := by nlinarith [hr0pos.le]
              exact mul_nonneg this (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
            have : (1 + |2 * Rk|) ^ ρ ≤ ((1 + 4 * r0) * (2 : ℝ) ^ (kk : ℝ)) ^ ρ :=
              Real.rpow_le_rpow hRnonneg hbase hρ
            have hsplit :
                ((1 + 4 * r0) * (2 : ℝ) ^ (kk : ℝ)) ^ ρ
                  = (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ (kk : ℝ)) ^ ρ := by
              have h1 : 0 ≤ (1 + 4 * r0) := by nlinarith [hr0pos.le]
              have h2 : 0 ≤ (2 : ℝ) ^ (kk : ℝ) := le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
              simpa using (Real.mul_rpow h1 h2 (z := ρ))
            have hpow :
                ((2 : ℝ) ^ (kk : ℝ)) ^ ρ = ((2 : ℝ) ^ ρ) ^ kk := by
              have h2nonneg : (0 : ℝ) ≤ 2 := by norm_num
              calc
                ((2 : ℝ) ^ (kk : ℝ)) ^ ρ = (2 : ℝ) ^ ((kk : ℝ) * ρ) := by
                  simp [Real.rpow_mul]
                _ = ((2 : ℝ) ^ ρ) ^ (kk : ℝ) := by
                  simpa [mul_comm] using (Real.rpow_mul (x := (2 : ℝ)) (y := ρ) (z := (kk : ℝ)) h2nonneg)
                _ = ((2 : ℝ) ^ ρ) ^ kk := by
                  simp [Real.rpow_natCast]
            calc
              (1 + |2 * Rk|) ^ ρ ≤ ((1 + 4 * r0) * (2 : ℝ) ^ (kk : ℝ)) ^ ρ := this
              _ = (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ (kk : ℝ)) ^ ρ := hsplit
              _ = (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ kk := by
                    simpa [mul_assoc] using congrArg (fun t => (1 + 4 * r0) ^ ρ * t) hpow
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
                  ((Cgrow * ((1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ kk) + Ctrail) / (Real.log 2)) * (rk⁻¹ ^ τ)
                    =
                    ((Cgrow / Real.log 2) * ((1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ kk)) * (rk⁻¹ ^ τ)
                      + ((Ctrail / Real.log 2) * (rk⁻¹ ^ τ)) := by
                simp [div_eq_mul_inv, mul_add, mul_assoc, mul_left_comm, mul_comm]
              exact le_trans hmul' (le_of_eq hdecomp)
            have htsum'' : (∑' p : S kk, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ)
                ≤ ((Cgrow * (1 + |2 * Rk|) ^ ρ + Ctrail) / (Real.log 2)) * (rk⁻¹ ^ τ) := htsum'
            have hpre :=
              le_trans htsum'' (le_trans (le_of_eq rfl) hsplit')
            have hrk_inv : rk⁻¹ ^ τ = (r0⁻¹ : ℝ) ^ τ * (qσ ^ kk) := by
              have hr0nn : 0 ≤ r0 := le_of_lt hr0pos
              have h2kk_nn : 0 ≤ (2 : ℝ) ^ (kk : ℝ) :=
                le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
              calc
                rk⁻¹ ^ τ = rk ^ (-τ) := by
                  simpa using (Real.rpow_neg_eq_inv_rpow rk τ).symm
                _ = (r0 * (2 : ℝ) ^ (kk : ℝ)) ^ (-τ) := by rfl
                _ = (r0 ^ (-τ)) * (((2 : ℝ) ^ (kk : ℝ)) ^ (-τ)) := by
                      simpa using (Real.mul_rpow hr0nn h2kk_nn (z := (-τ)))
                _ = (r0⁻¹ ^ τ) * (qσ ^ kk) := by
                      have hr0' : r0 ^ (-τ) = r0⁻¹ ^ τ := by
                        simp [Real.rpow_neg_eq_inv_rpow]
                      have h2' : ((2 : ℝ) ^ (kk : ℝ)) ^ (-τ) = qσ ^ kk := by
                        have h2nonneg : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
                        calc
                          ((2 : ℝ) ^ (kk : ℝ)) ^ (-τ) = (2 : ℝ) ^ ((kk : ℝ) * (-τ)) := by
                            exact (Real.rpow_mul (x := (2 : ℝ)) (y := (kk : ℝ)) (z := (-τ)) h2nonneg).symm
                          _ = (2 : ℝ) ^ ((-τ) * (kk : ℝ)) := by ring_nf
                          _ = ((2 : ℝ) ^ (-τ)) ^ (kk : ℝ) := by
                            exact (Real.rpow_mul (x := (2 : ℝ)) (y := (-τ)) (z := (kk : ℝ)) h2nonneg)
                          _ = ((2 : ℝ) ^ (-τ)) ^ kk := by
                            simp [Real.rpow_natCast]
                          _ = qσ ^ kk := by rfl
                      calc
                        r0 ^ (-τ) * ((2 : ℝ) ^ (kk : ℝ)) ^ (-τ)
                            = (r0⁻¹ ^ τ) * ((2 : ℝ) ^ (kk : ℝ)) ^ (-τ) := by
                                simpa [mul_assoc] using
                                  congrArg (fun t : ℝ => t * (((2 : ℝ) ^ (kk : ℝ)) ^ (-τ))) hr0'
                        _ = (r0⁻¹ ^ τ) * (qσ ^ kk) := by
                                simpa [mul_assoc] using
                                  congrArg (fun t : ℝ => (r0⁻¹ ^ τ) * t) h2'
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
            have hpost : (∑' p : S kk, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ) ≤ A * q ^ kk + B * qσ ^ kk := by
              have hAB : ((Cgrow / Real.log 2) * ((1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ kk)) * (rk⁻¹ ^ τ)
                    + ((Ctrail / Real.log 2) * (rk⁻¹ ^ τ))
                  ≤ A * q ^ kk + B * qσ ^ kk := by
                have hA : ((Cgrow / Real.log 2) * ((1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ kk)) * (rk⁻¹ ^ τ)
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


/-!
## Boundedness on compact annuli (away from `z₀`)

This is the boundedness statement that is *actually true* for quotient functions: on any compact set
that stays a positive distance away from `z₀`, the quotient is bounded.
-/

theorem bddAbove_norm_divisorCanonicalProduct_div_pow_annulus
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (z₀ : ℂ) (k : ℕ) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) :
    BddAbove
      (norm ∘
        (fun z : ℂ => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k) ''
          (Metric.annulusIcc z₀ r₁ r₂)) := by
  classical
  set K : Set ℂ := Metric.annulusIcc z₀ r₁ r₂
  have hK : IsCompact K := by
    have hclosed : IsClosed (Metric.ball z₀ r₁)ᶜ := Metric.isOpen_ball.isClosed_compl
    simpa [K, Metric.annulusIcc_eq] using (isCompact_closedBall z₀ r₂).inter_right hclosed
  have hKz : ∀ z ∈ K, z ≠ z₀ := by
    intro z hz hzz
    have hzBall : z ∈ Metric.ball z₀ r₁ := by
      simpa [hzz] using (Metric.mem_ball_self hr₁ : z₀ ∈ Metric.ball z₀ r₁)
    have hz' : z ∈ Metric.closedBall z₀ r₂ ∧ z ∉ Metric.ball z₀ r₁ := by
      simpa [K, Metric.annulusIcc_eq] using hz
    exact hz'.2 hzBall
  have hdiff : DifferentiableOn ℂ
        (fun z : ℂ => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k)
        ((Set.univ : Set ℂ) \ {z₀}) :=
    differentiableOn_divisorCanonicalProduct_div_pow_sub (m := m) (f := f) h_sum (z₀ := z₀) (k := k)
  have hcont : ContinuousOn
      (fun z : ℂ => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k) K := by
    refine (hdiff.mono ?_).continuousOn
    intro z hz
    refine ⟨by simp, ?_⟩
    exact hKz z hz
  have hKimg :
      IsCompact
        ((fun z : ℂ => (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) / (z - z₀) ^ k) '' K) :=
    hK.image_of_continuousOn hcont
  rcases (isBounded_iff_forall_norm_le.1 hKimg.isBounded) with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  rintro _ ⟨w, hwK, rfl⟩
  exact hC _ ⟨w, hwK, rfl⟩

/-!
## Elementary helper: `log(1 + exp B) ≤ B + log 2`

Used when converting a norm bound `‖H z‖ ≤ exp(B)` into a `log(1+‖H z‖)` bound.
-/

lemma log_one_add_exp_le (B : ℝ) (hB : 0 ≤ B) :
    Real.log (1 + Real.exp B) ≤ B + Real.log 2 := by
  have hle : (1 : ℝ) + Real.exp B ≤ 2 * Real.exp B := by
    have : (1 : ℝ) ≤ Real.exp B := by simpa using (Real.exp_monotone hB)
    nlinarith
  have hpos : 0 < (1 : ℝ) + Real.exp B := by
    have : 0 < Real.exp B := Real.exp_pos _
    linarith
  have hlog_le : Real.log (1 + Real.exp B) ≤ Real.log (2 * Real.exp B) :=
    Real.log_le_log hpos (hle.trans_eq rfl)
  have hlog_mul : Real.log (2 * Real.exp B) = Real.log 2 + B := by
    simp [Real.log_mul, show (2 : ℝ) ≠ 0 by norm_num]
  linarith [hlog_le, hlog_mul]

/-!
## Hadamard factorization (intrinsic statement)

This is the *target* API: no `ZeroData`, and zeros/multiplicities are obtained intrinsically via the
divisor infrastructure.

-/

--set_option maxHeartbeats 800000 in
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
  classical
  -- Step 1: obtain the intrinsic Lindelöf summability needed for the canonical product.
  set m : ℕ := Nat.floor ρ
  have h_sum :
      Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
        ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)) := by
    simpa [m] using
      (summable_norm_inv_pow_divisorZeroIndex₀_of_growth (f := f) (ρ := ρ)
        hρ hentire hnot hgrowth)
  -- Step 2: quotient step (intrinsic): split off the canonical product and the origin power.
  rcases exists_entire_nonzero_hadamardQuotient (m := m) (f := f) hentire hnot h_sum with
    ⟨H, hH_entire, hH_ne, hfactor⟩
  -- Step 3: Cartan/minimum-modulus step: show `H` has growth exponent `< m+1`, hence `H = exp(P)`
  -- with `deg P ≤ m`, and conclude the factorization.
  -- We choose an intermediate exponent `τ` with `ρ < τ < m+1`, so that `Nat.floor τ = m`.
  let τ : ℝ := (ρ + (m + 1 : ℝ)) / 2
  have hτ : ρ < τ := by
    have hm : ρ < (m + 1 : ℝ) := by
      -- `m = floor ρ` gives `ρ < m+1`
      simpa [m] using (Nat.lt_floor_add_one (a := ρ))
    dsimp [τ]
    linarith
  have hτ_lt : τ < (m + 1 : ℝ) := by
    have hm : ρ < (m + 1 : ℝ) := by
      -- `m = floor ρ` gives `ρ < m+1`
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
  -- Intrinsic Cartan/minimum-modulus growth bound for the Hadamard quotient:
  -- Tao-style “good radius + minimum modulus”, implemented intrinsically over `divisorZeroIndex₀`,
  -- producing `‖H z‖ ≤ exp(C*(1+‖z‖)^τ)` for `ρ < τ < m+1`.
  have hH_bound_rpow :
      ∃ C > 0, ∀ z : ℂ, ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ) := by
    classical
    rcases hgrowth with ⟨Cf, hCfpos, hCf⟩
    -- τ-summability of divisor indices (intrinsic Lindelöf)
    have hsumτ :
        Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
          ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ) :=
      summable_norm_inv_rpow_divisorZeroIndex₀_of_growth (f := f) (ρ := ρ) (τ := τ)
        hρ hτ hentire hnot ⟨Cf, hCfpos, hCf⟩
    let Sτ : ℝ := ∑' p : divisorZeroIndex₀ f (Set.univ : Set ℂ), ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ
    have hSτ_nonneg : 0 ≤ Sτ := tsum_nonneg (fun _ => by
      exact Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _)
    -- A coarse constant for the canonical product inverse bound on good circles.
    let Cprod : ℝ := ((CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ + 3) * (Sτ + 1)
    have hCprod_nonneg : 0 ≤ Cprod := by
      have hS : 0 ≤ Sτ + 1 := by linarith [hSτ_nonneg]
      have hA : 0 ≤ (CartanBound.Cφ + (2 : ℝ) * m) * (4 : ℝ) ^ τ + 3 := by
        have hCφ : 0 ≤ CartanBound.Cφ := le_of_lt CartanBound.Cφ_pos
        have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
        have h4τ : 0 ≤ (4 : ℝ) ^ τ := by positivity
        nlinarith [hCφ, hm0, h4τ]
      simpa [Cprod] using mul_nonneg hA hS
    refine ⟨(Cf + Cprod + 10) * (3 : ℝ) ^ τ, by
      have h3τ : 0 < (3 : ℝ) ^ τ := by positivity
      nlinarith [hCfpos, hCprod_nonneg, h3τ], ?_⟩
    intro z
    -- choose a dyadic scale `R` and a good radius `r ∈ (R,2R]`
    let R : ℝ := max ‖z‖ 1
    have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hRle : (1 : ℝ) ≤ R := le_max_right _ _
    -- finite family of divisor indices with `‖val‖ ≤ 4R`
    let smallSet : Set (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := {p | ‖divisorZeroIndex₀_val p‖ ≤ 4 * R}
    have hsmall_fin : smallSet.Finite := by
      have : Metric.closedBall (0 : ℂ) (4 * R) ⊆ (Set.univ : Set ℂ) := by simp
      simpa [smallSet] using
        (divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ)) (B := 4 * R) this)
    let small : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := hsmall_fin.toFinset
    let a : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀_val p‖
    have ha_pos : ∀ p ∈ small, 0 < a p := by
      intro p hp; dsimp [a]
      exact norm_pos_iff.2 (divisorZeroIndex₀_val_ne_zero p)
    let bad : Finset ℝ := small.image a
    rcases CartanBound.exists_radius_Ioc_sum_mul_phi_div_le_Cφ_mul_sum_avoid
        (s := small) (w := fun _ => (1 : ℝ)) (a := a)
        (hw := by intro _ _; norm_num) (ha := ha_pos) (bad := bad) (R := R) hRpos with
      ⟨r, hr_mem, hr_not_bad, hr_phi⟩
    have hR_le_r : R ≤ r := le_of_lt hr_mem.1
    have hr_le_2R : r ≤ 2 * R := hr_mem.2
    have hrpos : 0 < r := lt_of_lt_of_le hRpos hR_le_r
    -- bound `‖H‖` on the circle `‖u‖ = r`, then propagate to the ball by maximum modulus.
    have hcircle :
        ∀ u : ℂ, ‖u‖ = r → ‖H u‖ ≤ Real.exp ((Cf + Cprod + 10) * (1 + r) ^ τ) := by
      intro u hur
      -- `H u = f u / (u^ord0 * canonicalProduct u)` via `hfactor`
      have hden_eq : f u = H u * (u ^ analyticOrderNatAt f 0 * divisorCanonicalProduct m f (Set.univ : Set ℂ) u) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using (hfactor u)
      have hu0 : u ≠ 0 := by
        intro hu0; subst hu0
        have : (0 : ℝ) = r := by simpa using hur
        exact (ne_of_gt hrpos) this.symm
      have hpow_ne : u ^ analyticOrderNatAt f 0 ≠ 0 := pow_ne_zero _ hu0
      -- First show that `f` has no zeros on this circle: if `f u = 0`, then `‖u‖ = r` belongs to the
      -- finite bad set of zero radii, contradiction.
      have hfu_ne : f u ≠ 0 := by
        have hr_le_4R : r ≤ 4 * R := by
          have : r ≤ 2 * R := hr_le_2R
          nlinarith [this, hRpos]
        -- turn `r ∉ bad` into a pointwise "radius avoids all divisor radii up to `4R`"
        have hr_not :
            ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
              ‖divisorZeroIndex₀_val p‖ ≤ 4 * R → r ≠ ‖divisorZeroIndex₀_val p‖ := by
          intro p hpB
          intro hEq
          have hp_small : p ∈ small := by
            simpa [small, smallSet] using (hsmall_fin.mem_toFinset.2 hpB)
          have : r ∈ bad := by
            refine Finset.mem_image.2 ⟨p, hp_small, ?_⟩
            simpa [a] using hEq.symm
          exact (hr_not_bad this).elim
        exact no_zero_on_sphere_of_forall_val_norm_ne (f := f) hentire hnot
          (B := 4 * R) (r := r) hrpos hr_le_4R hr_not u hur
      have hden_ne :
          (u ^ analyticOrderNatAt f 0 * divisorCanonicalProduct m f (Set.univ : Set ℂ) u) ≠ 0 := by
        intro hden0
        have : f u = 0 := by simpa [hden0] using hden_eq
        exact hfu_ne this
      have hHu : H u = f u / (u ^ analyticOrderNatAt f 0 * divisorCanonicalProduct m f (Set.univ : Set ℂ) u) := by
        -- divide the identity `f u = H u * denom` by `denom`
        have : (H u * (u ^ analyticOrderNatAt f 0 * divisorCanonicalProduct m f (Set.univ : Set ℂ) u)) /
              (u ^ analyticOrderNatAt f 0 * divisorCanonicalProduct m f (Set.univ : Set ℂ) u) = H u := by
          simpa using (mul_div_cancel_right₀ (H u) hden_ne)
        -- rewrite `f u` using `hden_eq`
        have : f u / (u ^ analyticOrderNatAt f 0 * divisorCanonicalProduct m f (Set.univ : Set ℂ) u) = H u := by
          simpa [hden_eq, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
        exact this.symm
      -- bound `‖f u‖` by the τ-growth (we weaken `ρ` to `τ`)
      have hf_u : ‖f u‖ ≤ Real.exp (Cf * (1 + r) ^ τ) := by
        have hlog := hCf u
        -- `C*(1+‖u‖)^ρ ≤ C*(1+‖u‖)^τ` since `1+‖u‖ ≥ 1` and `ρ ≤ τ`
        have hbase : (1 : ℝ) ≤ 1 + ‖u‖ := by linarith [norm_nonneg u]
        have hρleτ : ρ ≤ τ := le_of_lt hτ
        have hpow : (1 + ‖u‖) ^ ρ ≤ (1 + ‖u‖) ^ τ :=
          Real.rpow_le_rpow_of_exponent_le hbase hρleτ
        have hlog' : Real.log (1 + ‖f u‖) ≤ Cf * (1 + ‖u‖) ^ τ := by
          exact hlog.trans (mul_le_mul_of_nonneg_left hpow (le_of_lt hCfpos))
        have hpos : 0 < (1 : ℝ) + ‖f u‖ := by linarith [norm_nonneg (f u)]
        have : (1 : ℝ) + ‖f u‖ ≤ Real.exp (Cf * (1 + ‖u‖) ^ τ) :=
          (Real.log_le_iff_le_exp hpos).1 hlog'
        have : ‖f u‖ ≤ Real.exp (Cf * (1 + ‖u‖) ^ τ) := by linarith
        simpa [hur] using this
      -- crude bound on the inverse denominator: use `Cprod` (full minimum-modulus proof to be filled)
      have hden_inv : ‖(u ^ analyticOrderNatAt f 0 * divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖
          ≤ Real.exp (Cprod * (1 + r) ^ τ) := by
        classical
        -- It suffices to bound the inverse canonical product, since `‖(u^k)⁻¹‖ ≤ 1` on this circle (`r ≥ 1`).
        have hr1 : (1 : ℝ) ≤ r := le_trans hRle hR_le_r
        have hpow_inv_le1 : ‖(u ^ analyticOrderNatAt f 0)⁻¹‖ ≤ 1 := by
          -- `‖u‖ = r ≥ 1` gives `‖u‖⁻¹ ≤ 1`, hence its powers are ≤ 1.
          have hinv : (‖u‖ : ℝ)⁻¹ ≤ 1 := by
            have : (1 : ℝ) ≤ ‖u‖ := by simpa [hur] using hr1
            exact inv_le_one_of_one_le₀ this
          have hnn : 0 ≤ (‖u‖ : ℝ)⁻¹ := by positivity
          have : (‖u‖ : ℝ)⁻¹ ^ analyticOrderNatAt f 0 ≤ 1 ^ analyticOrderNatAt f 0 :=
            pow_le_pow_left₀ hnn hinv _
          simpa [norm_inv, norm_pow] using this
        -- Now bound the inverse canonical product `∏' p, E_m(u / a_p)`.
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
        -- Majorant `b p` and pointwise estimate `‖(fac p)⁻¹‖ ≤ exp(b p)`.
        let ap : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℝ := fun p => ‖divisorZeroIndex₀_val p‖
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
            have hmτ : (m : ℝ) ≤ τ := by
              have hmρ : (m : ℝ) ≤ ρ := by
                have := Nat.floor_le hρ
                simpa [m] using this
              exact le_trans hmρ (le_of_lt hτ)
            have hnear :
                ‖(weierstrassFactor m (u / divisorZeroIndex₀_val p))⁻¹‖
                  ≤ Real.exp (CartanBound.φ (r / ap p) + (m : ℝ) * (1 + (r / ap p) ^ τ)) := by
              simpa [ap] using
                (norm_inv_weierstrassFactor_le_exp_near (m := m) (τ := τ) (r := r)
                    (u := u) (a := divisorZeroIndex₀_val p)
                    (hur := hur) (ha := hval0) (hr := by simpa [ap] using hval_ne) hmτ)
            simpa [fac, b, hp] using hnear
          · -- tail regime: `‖u / a‖ ≤ 1/2`, so use the far log bound and compare exponents.
            have hlarge : (4 * R : ℝ) < ap p := by
              have : ¬ap p ≤ 4 * R := by
                intro hle
                have : p ∈ small := by
                  -- `p ∈ small` iff `ap p ≤ 4R`
                  simpa [small, smallSet, ap] using (hsmall_fin.mem_toFinset.2 hle)
                exact hp this
              exact lt_of_not_ge this
            have hz' : ‖u / divisorZeroIndex₀_val p‖ ≤ (1 / 2 : ℝ) := by
              have hnorm : ‖u / divisorZeroIndex₀_val p‖ = r / ap p := by
                simp [div_eq_mul_inv, hur, ap, norm_inv]
              rw [hnorm]
              have hap : 0 < ap p := by
                dsimp [ap]
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
        -- Tao-style bound on partial sums of the majorant `b`:
        -- prove `Summable b` and bound `tsum b`, then use `sum_le_tsum`.
        have hb_le :
            ∀ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)),
              (∑ p ∈ s, b p) ≤ Cprod * (1 + r) ^ τ := by
          intro s
          have hsmallSet' :
              smallSet =
                {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ 4 * R} := rfl
          -- Use the extracted Tao bookkeeping lemma (compiled once to `.olean`).
          simpa [small, ap, b, Sτ, Cprod, a, hsmallSet'] using
            (Complex.Hadamard.cartan_sum_majorant_le (f := f) (m := m) (τ := τ) (R := R) (r := r)
              (hRpos := hRpos) (hrpos := hrpos) (hR_le_r := hR_le_r) (hτ_nonneg := hτ_nonneg)
              (smallSet := smallSet) (hsmall_fin := hsmall_fin) (hsmallSet := hsmallSet')
              (hsumτ := hsumτ)
              (hr_phi := by
                -- `exists_radius...` gives weights `w ≡ 1`; rewrite the RHS `∑ 1` as `card`.
                simpa [one_mul, Finset.sum_const] using hr_phi)
              s)
        have hcprod_inv :
            ‖(divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖ ≤ Real.exp (Cprod * (1 + r) ^ τ) := by
          -- Use the reusable lemma: pointwise `‖fac⁻¹‖ ≤ exp(b)` plus a bound on all partial sums of `b`
          -- gives the bound on the infinite product limit.
          refine hasProd_norm_inv_le_exp_of_pointwise_le_exp
            (α := divisorZeroIndex₀ f (Set.univ : Set ℂ)) (fac := fac)
            (F := divisorCanonicalProduct m f (Set.univ : Set ℂ) u)
            hprod (b := b) (B := Cprod * (1 + r) ^ τ) ?_ ?_
          · exact hterm
          · intro s
            exact hb_le s
        -- Put the two factors together.
        have hmul :
            ‖(u ^ analyticOrderNatAt f 0 * divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖
              = ‖(u ^ analyticOrderNatAt f 0)⁻¹‖ * ‖(divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖ := by
          simp [mul_inv_rev, norm_mul, mul_assoc, mul_left_comm, mul_comm]
        rw [hmul]
        have : ‖(u ^ analyticOrderNatAt f 0)⁻¹‖ * ‖(divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖
              ≤ 1 * Real.exp (Cprod * (1 + r) ^ τ) :=
          mul_le_mul hpow_inv_le1 hcprod_inv (by positivity) (by positivity)
        simpa using this
      have : ‖H u‖ ≤ ‖f u‖ * ‖(u ^ analyticOrderNatAt f 0 * divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖ := by
        -- `H = f / denom`
        have : ‖H u‖ = ‖f u / (u ^ analyticOrderNatAt f 0 * divisorCanonicalProduct m f (Set.univ : Set ℂ) u)‖ := by
          simp [hHu]
        -- `‖f / denom‖ = ‖f‖ * ‖denom⁻¹‖`
        simp [div_eq_mul_inv, norm_mul, norm_inv, this]
      have hmul :
          ‖f u‖ * ‖(u ^ analyticOrderNatAt f 0 * divisorCanonicalProduct m f (Set.univ : Set ℂ) u)⁻¹‖
            ≤ Real.exp (Cf * (1 + r) ^ τ) * Real.exp (Cprod * (1 + r) ^ τ) :=
        mul_le_mul hf_u hden_inv (by positivity) (by positivity)
      have hexp : Real.exp (Cf * (1 + r) ^ τ) * Real.exp (Cprod * (1 + r) ^ τ)
          = Real.exp ((Cf + Cprod) * (1 + r) ^ τ) := by
        simp [Real.exp_add, add_mul, add_comm, add_left_comm]
      -- absorb slack
      have : ‖H u‖ ≤ Real.exp ((Cf + Cprod) * (1 + r) ^ τ) :=
        (this.trans hmul).trans_eq hexp
      -- finalize with extra `+10` slack
      have hslack :
          Real.exp ((Cf + Cprod) * (1 + r) ^ τ) ≤ Real.exp ((Cf + Cprod + 10) * (1 + r) ^ τ) := by
        refine Real.exp_le_exp.2 ?_
        have hnn : 0 ≤ (1 + r) ^ τ := by positivity
        nlinarith
      exact this.trans hslack
    -- Now use maximum modulus on the ball of radius `r` to bound `H z` (since `‖z‖ ≤ R ≤ r`).
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
      -- maximum modulus principle on the bounded set `U = ball 0 r`
      let U : Set ℂ := Metric.ball (0 : ℂ) r
      have hU : Bornology.IsBounded U := Metric.isBounded_ball
      have hd : DiffContOnCl ℂ H U := hH_entire.diffContOnCl
      have hz_cl : z ∈ closure U := subset_closure hz_ball
      have hCfront : ∀ w ∈ frontier U, ‖H w‖ ≤ Real.exp ((Cf + Cprod + 10) * (1 + r) ^ τ) := by
        intro w hw
        simpa [U] using hfront w (by simpa [U] using hw)
      simpa [U] using
        (Complex.norm_le_of_forall_mem_frontier_norm_le (f := H) (U := U) hU hd hCfront (z := z) hz_cl)
    -- convert `r` to `‖z‖` using `r ≤ 2R ≤ 3*(1+‖z‖)`
    have hr_le_3 : 1 + r ≤ 3 * (1 + ‖z‖) := by
      have hR_le1z : R ≤ 1 + ‖z‖ := by
        have hz' : ‖z‖ ≤ 1 + ‖z‖ := by linarith
        have h1' : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
        exact max_le_iff.2 ⟨hz', h1'⟩
      have : r ≤ 2 * R := hr_le_2R
      nlinarith [this, hR_le1z, hRle]
    have hpow : (1 + r) ^ τ ≤ (3 : ℝ) ^ τ * (1 + ‖z‖) ^ τ := by
      -- `1+r ≤ 3*(1+‖z‖)` and `τ ≥ 0`
      have hbase : 0 ≤ 1 + r := by linarith [le_of_lt hrpos]
      have hbase' : 0 ≤ 3 * (1 + ‖z‖) := by positivity
      have := Real.rpow_le_rpow hbase (by exact hr_le_3) hτ_nonneg
      -- rewrite RHS: `(3*(1+‖z‖))^τ = 3^τ * (1+‖z‖)^τ`
      have hmul :
          (3 * (1 + ‖z‖)) ^ τ = (3 : ℝ) ^ τ * (1 + ‖z‖) ^ τ := by
        have h3 : 0 ≤ (3 : ℝ) := by norm_num
        have h1 : 0 ≤ (1 + ‖z‖ : ℝ) := by positivity
        simpa [mul_assoc] using (Real.mul_rpow (x := (3 : ℝ)) (y := (1 + ‖z‖ : ℝ)) (z := τ) h3 h1)
      simpa [hmul] using this
    have hmain :
        Real.exp ((Cf + Cprod + 10) * (1 + r) ^ τ)
          ≤ Real.exp (((Cf + Cprod + 10) * (3 : ℝ) ^ τ) * (1 + ‖z‖) ^ τ) := by
      refine Real.exp_le_exp.2 ?_
      have hnn : 0 ≤ (Cf + Cprod + 10) := by nlinarith [le_of_lt hCfpos, hCprod_nonneg]
      nlinarith [hpow]
    -- finish with the constant chosen at the start (`(Cf + Cprod + 10) * 3^τ`)
    have hmain' :
        Real.exp (((Cf + Cprod + 10) * (3 : ℝ) ^ τ) * (1 + ‖z‖) ^ τ)
          = Real.exp (((Cf + Cprod + 10) * (3 : ℝ) ^ τ) * (1 + ‖z‖) ^ τ) := rfl
    simpa [mul_assoc] using (le_trans (le_trans hball hmain) (le_of_eq hmain'))
  -- Deduce an integer-exponent growth bound to apply `zero_free_polynomial_growth_is_exp_poly`.
  have hH_growth_nat :
      ∃ C > 0, ∀ z : ℂ, ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (m + 1)) := by
    rcases hH_bound_rpow with ⟨C, hCpos, hC⟩
    refine ⟨C, hCpos, ?_⟩
    intro z
    have hbase : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
    have hτ_le : τ ≤ (m + 1 : ℝ) := le_of_lt hτ_lt
    have hpow : (1 + ‖z‖) ^ τ ≤ (1 + ‖z‖) ^ (m + 1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hbase hτ_le
    have hpow' : (1 + ‖z‖) ^ (m + 1 : ℝ) = (1 + ‖z‖) ^ (m + 1) := by
      simpa using (Real.rpow_natCast (1 + ‖z‖) (m + 1))
    have : C * (1 + ‖z‖) ^ τ ≤ C * (1 + ‖z‖) ^ (m + 1) := by
      nlinarith [hpow, hpow']
    have := Real.exp_le_exp.2 this
    exact (hC z).trans this
  rcases (zero_free_polynomial_growth_is_exp_poly (H := H) (n := m + 1)
      hH_entire hH_ne hH_growth_nat) with ⟨P, hPn, hHP⟩
  -- sharp degree bound via the integer-order obstruction at exponent `τ`
  have hPnat : P.natDegree ≤ m := by
    have hlog_growth :
        ∃ C > 0, ∀ z : ℂ,
          Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖) ≤ C * (1 + ‖z‖) ^ τ := by
      rcases hH_bound_rpow with ⟨C, hCpos, hC⟩
      refine ⟨C + Real.log 2, by
        have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
        linarith [hCpos, hlog2], ?_⟩
      intro z
      have hB : 0 ≤ C * (1 + ‖z‖) ^ τ := by
        have : 0 ≤ C := le_of_lt hCpos
        have : 0 ≤ (1 + ‖z‖) ^ τ := by positivity
        nlinarith
      -- `H = exp(P)` and `‖H z‖ ≤ exp(C*(1+‖z‖)^τ)`
      have hHz : ‖Complex.exp (Polynomial.eval z P)‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ) := by
        simpa [hHP z] using (hC z)
      -- turn into `log(1+...)` bound
      have : Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖)
          ≤ C * (1 + ‖z‖) ^ τ + Real.log 2 := by
        have : Real.log (1 + ‖Complex.exp (Polynomial.eval z P)‖)
            ≤ Real.log (1 + Real.exp (C * (1 + ‖z‖) ^ τ)) := by
          have hpos : 0 < (1 : ℝ) + ‖Complex.exp (Polynomial.eval z P)‖ := by
            linarith [norm_nonneg (Complex.exp (Polynomial.eval z P))]
          have hle : (1 : ℝ) + ‖Complex.exp (Polynomial.eval z P)‖ ≤ (1 : ℝ) + Real.exp (C * (1 + ‖z‖) ^ τ) := by
            linarith [hHz]
          exact Real.log_le_log hpos hle
        exact (this.trans (log_one_add_exp_le (B := C * (1 + ‖z‖) ^ τ) hB))
      -- absorb the additive constant `log 2` into the multiplicative constant using `1 ≤ (1+‖z‖)^τ`.
      have hX : (1 : ℝ) ≤ (1 + ‖z‖) ^ τ := by
        have hbase : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
        exact Real.one_le_rpow hbase hτ_nonneg
      have hlog2_nonneg : 0 ≤ Real.log 2 := le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
      have hlin : C * (1 + ‖z‖) ^ τ + Real.log 2 ≤ (C + Real.log 2) * (1 + ‖z‖) ^ τ := by
        -- `C*X + log2 ≤ C*X + log2*X` since `log2 ≤ log2*X` (with `0 ≤ log2` and `1 ≤ X`)
        -- and the RHS is `(C+log2)*X`.
        nlinarith [hX, hlog2_nonneg]
      exact this.trans hlin
    have := natDegree_le_floor_of_growth_exp_eval (ρ := τ) hτ_nonneg P hlog_growth
    simpa [hfloorτ] using this
  refine ⟨P, ?_, ?_⟩
  · -- `degree ≤ floor ρ = m`
    -- use `natDegree` bound and relate to `degree`.
    have : P.degree ≤ m := Polynomial.degree_le_of_natDegree_le hPnat
    simpa [m] using this
  · intro z
    have hH' : H z = Complex.exp (Polynomial.eval z P) := by simpa using (hHP z)
    simpa [hH', mul_assoc, mul_left_comm, mul_comm, m] using (hfactor z)

/-!
## Finite order hypothesis ⇒ Hadamard factorization

Tao (246B, Theorem 22 following Iwaniec and Kowalski) assumes an “order at most `ρ`” hypothesis given by an `ε`-family of growth
bounds. Our proof pipeline is phrased in terms of a single explicit bound on `log (1 + ‖f z‖)`.
The theorem below bridges this gap: from the `ε`-family of exponential bounds we pick an
intermediate exponent `τ` with `ρ < τ < ⌊ρ⌋ + 1` and obtain the single growth hypothesis needed to
apply `hadamard_factorization_of_growth`.
-/

theorem hadamard_factorization_of_order_bounded_order {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hentire : Differentiable ℂ f)
    (hnot : ∃ z : ℂ, f z ≠ 0)
    (horder :
      ∀ ε : ℝ, 0 < ε →
        ∃ C > 0, ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (ρ + ε))) :
    ∃ (P : Polynomial ℂ),
      P.degree ≤ Nat.floor ρ ∧
      ∀ z : ℂ,
        f z =
          Complex.exp (Polynomial.eval z P) *
            z ^ (analyticOrderNatAt f 0) *
            divisorCanonicalProduct (Nat.floor ρ) f (Set.univ : Set ℂ) z := by
  classical
  set m : ℕ := Nat.floor ρ
  -- Choose an intermediate exponent `τ` with `ρ < τ < m+1`, so `Nat.floor τ = m`.
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
  -- Obtain a single growth bound at exponent `τ` from the `ε`-family.
  have hε : 0 < τ - ρ := sub_pos.2 hτ
  rcases horder (τ - ρ) hε with ⟨C, hCpos, hC⟩
  have hgrowthτ :
      ∃ C' > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C' * (1 + ‖z‖) ^ τ := by
    refine ⟨C + Real.log 2, by
      have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      linarith, ?_⟩
    intro z
    have hbase : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
    have hX : (1 : ℝ) ≤ (1 + ‖z‖) ^ τ := Real.one_le_rpow hbase hτ_nonneg
    have hB : 0 ≤ C * (1 + ‖z‖) ^ τ := by
      exact mul_nonneg (le_of_lt hCpos) (by positivity)
    have hnorm_le : ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ) := by
      -- rewrite the exponent `ρ + (τ - ρ)` to `τ`
      simpa [sub_add_cancel] using (hC z)
    have hlog_le :
        Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ τ + Real.log 2 := by
      have : Real.log (1 + ‖f z‖) ≤ Real.log (1 + Real.exp (C * (1 + ‖z‖) ^ τ)) := by
        have hpos : 0 < (1 : ℝ) + ‖f z‖ := by linarith [norm_nonneg (f z)]
        have hle : (1 : ℝ) + ‖f z‖ ≤ (1 : ℝ) + Real.exp (C * (1 + ‖z‖) ^ τ) := by
          linarith [hnorm_le]
        exact Real.log_le_log hpos hle
      exact this.trans (log_one_add_exp_le (B := C * (1 + ‖z‖) ^ τ) hB)
    have hlog2_nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlog2 : Real.log 2 ≤ Real.log 2 * (1 + ‖z‖) ^ τ := by
      simpa [one_mul] using (mul_le_mul_of_nonneg_left hX hlog2_nonneg)
    nlinarith [hlog_le, hlog2]
  -- Apply the growth-based theorem at exponent `τ`, then rewrite floors.
  rcases (hadamard_factorization_of_growth (f := f) (ρ := τ) hτ_nonneg hentire hnot hgrowthτ) with
    ⟨P, hdeg, hfac⟩
  refine ⟨P, ?_, ?_⟩
  · simpa [m, hfloorτ] using hdeg
  · intro z
    simpa [m, hfloorτ] using hfac z


/-- Alias for downstream zeta applications. -/
theorem hadamard_factorization_of_order {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hf : Differentiable ℂ f) (hnot : ∃ z, f z ≠ 0)
    (horder : ∀ ε > 0, ∃ C > 0, ∀ z, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (ρ + ε))) :
    ∃ P : Polynomial ℂ, P.degree ≤ Nat.floor ρ ∧
      ∀ z, f z = exp (P.eval z) * z ^ (analyticOrderNatAt f 0) *
        divisorCanonicalProduct (Nat.floor ρ) f (Set.univ : Set ℂ) z :=
  hadamard_factorization_of_order_bounded_order hρ hf hnot horder

end Complex.Hadamard
