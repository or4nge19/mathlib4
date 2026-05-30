/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.WeierstrassFactor

/-!
# Canonical products

This file defines canonical products attached to a sequence `a : ℕ → ℂ`:

`canonicalProduct m a z := ∏' n, weierstrassFactor m (z / a n)`.

The main convergence results are thin wrappers around the locally uniform product API for scaled
Weierstrass factors developed in `Mathlib.Analysis.Complex.WeierstrassFactor`.
-/

public section

noncomputable section

open Filter Topology

namespace Complex

/-- The canonical product `∏' n, E_m(z / a_n)` for a sequence `a`. -/
def canonicalProduct (m : ℕ) (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∏' n : ℕ, weierstrassFactor m (z / a n)

private theorem analyticOnNhd_updated_canonicalProduct {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) (n : ℕ) :
    AnalyticOnNhd ℂ
      (fun z ↦ ∏' k, Function.update (fun k ↦ weierstrassFactor m (z / a k)) n (fun _ ↦ 1) k)
      Set.univ := by
  have hprod :
      HasProdLocallyUniformlyOn
        (Function.update (fun k ↦ fun z : ℂ ↦ weierstrassFactor m (z / a k)) n (fun _ ↦ 1))
        (fun z ↦ ∏' k, Function.update (fun k ↦ weierstrassFactor m (z / a k)) n (fun _ ↦ 1) k)
        Set.univ := by
    apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
    intro K hKu hK
    let f : ℕ → ℂ → ℂ := fun k z ↦ weierstrassFactor m (z / a k)
    let u : ℕ → ℂ → ℂ := Function.update f n (fun _ ↦ (1 : ℂ))
    have hmulK : MultipliableUniformlyOn f K :=
      (hasProdUniformlyOn_canonicalProduct_compact h_sum h_nonzero hK).multipliableUniformlyOn
    have hmulKu : MultipliableUniformlyOn u K := by
      change Multipliable (UniformOnFun.ofFun {K} ∘ u)
      simpa [f, u, Function.comp] using
        (show Multipliable (UniformOnFun.ofFun {K} ∘ f) from hmulK).update n
          (UniformOnFun.ofFun {K} (fun _ ↦ (1 : ℂ)))
    exact hmulKu.hasProdUniformlyOn
  have hloc :=
    hprod.tendstoLocallyUniformlyOn_finsetRange
  have hfactor :
      ∀ i : ℕ,
        Differentiable ℂ (Function.update (fun k ↦ fun z : ℂ ↦ weierstrassFactor m (z / a k)) n
          (fun _ : ℂ ↦ (1 : ℂ)) i) := by
    intro i
    by_cases hi : i = n
    · subst hi
      simpa using (differentiable_const : Differentiable ℂ (fun _ : ℂ ↦ (1 : ℂ)))
    · simpa [Function.update, hi] using
        (differentiable_weierstrassFactor m).comp (differentiable_id.div_const (a i))
  have hpartial :
      ∀ᶠ N in Filter.atTop,
        DifferentiableOn ℂ
          (fun z ↦
            ∏ k ∈ Finset.range N,
              Function.update (fun k ↦ fun z : ℂ ↦ weierstrassFactor m (z / a k)) n
                (fun _ : ℂ ↦ (1 : ℂ)) k z)
          Set.univ := by
    filter_upwards with N
    simpa [differentiableOn_univ] using
      (Differentiable.fun_finset_prod (u := Finset.range N) fun i hi ↦ hfactor i)
  exact DifferentiableOn.analyticOnNhd
    (differentiableOn_univ.mpr <| hloc.differentiableOn hpartial isOpen_univ) isOpen_univ

private theorem canonicalProduct_eq_mul_updated_canonicalProduct {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0)
    (n : ℕ) (z : ℂ) :
    canonicalProduct m a z =
      weierstrassFactor m (z / a n) *
        ∏' k, Function.update (fun k ↦ weierstrassFactor m (z / a k)) n 1 k := by
  let f : ℕ → ℂ := fun k ↦ weierstrassFactor m (z / a k)
  have hmult : Multipliable f :=
    (multipliableLocallyUniformlyOn_canonicalProduct h_sum h_nonzero).multipliable (by simp)
  have hupdate : Multipliable (Function.update f n 1) := hmult.update n 1
  calc
    canonicalProduct m a z = ∏' k, f k := by simp [canonicalProduct, f]
    _ = f n * ∏' k, Function.update f n 1 k := by
      simpa [Function.update] using hmult.tprod_eq_mul_tprod_ite' n hupdate
    _ = weierstrassFactor m (z / a n) *
          ∏' k, Function.update (fun k ↦ weierstrassFactor m (z / a k)) n 1 k := by
      simp [f]

private theorem tprod_updatedWeierstrassFactor_ne_zero {m : ℕ} {a : ℕ → ℂ}
    (ha : Function.Injective a)
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) (n : ℕ) :
    ∏' k, Function.update (fun k ↦ weierstrassFactor m (a n / a k)) n 1 k ≠ 0 := by
  let h : ℕ → ℂ := Function.update (fun k ↦ weierstrassFactor m (a n / a k) - 1) n 0
  have hfn : ∀ k, 1 + h k ≠ 0 := by
    intro k
    by_cases hk : k = n
    · simp [h, hk]
    · have hneq : a n ≠ a k := by
        intro hEq
        exact hk (ha hEq.symm)
      simpa [h, hk] using
        (weierstrassFactor_div_ne_zero_iff (m := m) (a := a k) (z := a n) (h_nonzero k)).2 hneq
  have hnormsumm : Summable (fun k : ℕ ↦ ‖h k‖) := by
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) ?_
      (summable_norm_weierstrassFactor_div_sub_one_of_summable_inv_pow
        (m := m) (a := a) h_sum h_nonzero (a n))
    intro k
    by_cases hk : k = n
    · simp [h, hk]
    · simp [h, hk]
  have hEq : (fun k ↦ 1 + h k) = Function.update (fun k ↦ weierstrassFactor m (a n / a k)) n 1 := by
    funext k
    by_cases hk : k = n
    · subst hk
      simp [h]
    · simp [h, hk]
  simpa [hEq] using
    tprod_one_add_ne_zero_of_summable (f := h) hfn hnormsumm

/-- The canonical product converges locally uniformly on `ℂ` under the standard summability
hypothesis. -/
theorem hasProdLocallyUniformlyOn_canonicalProduct {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    HasProdLocallyUniformlyOn (fun n z ↦ weierstrassFactor m (z / a n))
      (canonicalProduct m a) Set.univ := by
  simpa [canonicalProduct] using
    hasProdLocallyUniformlyOn_weierstrassFactor_div_of_summable_inv_pow
      (m := m) (a := a) h_sum h_nonzero

/-- The canonical product is locally uniformly multipliable on `ℂ` under the standard
summability hypothesis. -/
theorem multipliableLocallyUniformlyOn_canonicalProduct {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    MultipliableLocallyUniformlyOn (fun n z ↦ weierstrassFactor m (z / a n))
      (Set.univ : Set ℂ) := by
  simpa using
    (hasProdLocallyUniformlyOn_canonicalProduct h_sum h_nonzero).multipliableLocallyUniformlyOn

/-- The canonical product converges uniformly on compact sets under the standard summability
hypothesis. -/
theorem hasProdUniformlyOn_canonicalProduct_compact {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0)
    {K : Set ℂ} (hK : IsCompact K) :
    HasProdUniformlyOn (fun n z ↦ weierstrassFactor m (z / a n)) (canonicalProduct m a) K := by
  have hloc :
      HasProdLocallyUniformlyOn (fun n z ↦ weierstrassFactor m (z / a n))
        (canonicalProduct m a) K :=
    (hasProdLocallyUniformlyOn_canonicalProduct h_sum h_nonzero).mono (by simp : K ⊆ Set.univ)
  exact hloc.hasProdUniformlyOn_of_isCompact hK

/-- Uniform convergence on compact sets for the canonical product. -/
theorem canonicalProduct_converges_uniformOn_compact {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    ∀ K : Set ℂ, IsCompact K →
      TendstoUniformlyOn (fun s z => ∏ n ∈ s, weierstrassFactor m (z / a n))
        (canonicalProduct m a) Filter.atTop K := by
  intro K hK
  exact (hasProdUniformlyOn_iff_tendstoUniformlyOn.1
    (hasProdUniformlyOn_canonicalProduct_compact h_sum h_nonzero hK))

/-- The canonical product is holomorphic on `ℂ` under the standard summability hypothesis. -/
theorem differentiable_canonicalProduct {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    Differentiable ℂ (canonicalProduct m a) := by
  have hloc :=
    HasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange
      (hasProdLocallyUniformlyOn_canonicalProduct h_sum h_nonzero)
  have hfactor : ∀ i : ℕ, Differentiable ℂ (fun z ↦ weierstrassFactor m (z / a i)) := by
    intro i
    simpa using (differentiable_weierstrassFactor m).comp (differentiable_id.div_const (a i))
  have hpartial :
      ∀ᶠ N in Filter.atTop,
        DifferentiableOn ℂ (fun z ↦ ∏ n ∈ Finset.range N, weierstrassFactor m (z / a n))
          Set.univ := by
    filter_upwards with N
    simpa [differentiableOn_univ] using
      (Differentiable.fun_finset_prod (u := Finset.range N) fun i hi ↦ hfactor i)
  exact differentiableOn_univ.mp <| hloc.differentiableOn hpartial isOpen_univ

/-- The canonical product is analytic on `ℂ` under the standard summability hypothesis. -/
theorem analyticOnNhd_canonicalProduct {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    AnalyticOnNhd ℂ (canonicalProduct m a) Set.univ := by
  exact DifferentiableOn.analyticOnNhd
    (differentiableOn_univ.mpr (differentiable_canonicalProduct h_sum h_nonzero)) isOpen_univ

/-- The canonical product vanishes at each prescribed zero `a n`. -/
@[simp]
theorem canonicalProduct_apply_eq_zero {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) (n : ℕ) :
    canonicalProduct m a (a n) = 0 := by
  let f : ℕ → ℂ := fun k ↦ weierstrassFactor m (a n / a k)
  have hmult : Multipliable f :=
    (multipliableLocallyUniformlyOn_canonicalProduct h_sum h_nonzero).multipliable (by simp)
  have htend :
      Tendsto (fun N : ℕ ↦ ∏ k ∈ Finset.range N, f k) Filter.atTop
        (𝓝 (canonicalProduct m a (a n))) := by
    simpa [f, canonicalProduct] using hmult.hasProd.tendsto_prod_nat
  have hzero :
      (fun N : ℕ ↦ ∏ k ∈ Finset.range N, f k) =ᶠ[Filter.atTop] fun _ ↦ (0 : ℂ) := by
    refine Filter.eventually_atTop.2 ⟨n + 1, fun N hN ↦ ?_⟩
    have hnN : n ∈ Finset.range N := Finset.mem_range.mpr <| lt_of_lt_of_le (Nat.lt_succ_self n) hN
    apply Finset.prod_eq_zero hnN
    simp [f, h_nonzero n, weierstrassFactor_at_one]
  exact tendsto_nhds_unique_of_eventuallyEq htend tendsto_const_nhds hzero

/-- The canonical product vanishes at every point in `Set.range a`. -/
theorem canonicalProduct_eq_zero_of_mem_range {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0)
    {z : ℂ} (hz : z ∈ Set.range a) :
    canonicalProduct m a z = 0 := by
  rcases hz with ⟨n, rfl⟩
  exact canonicalProduct_apply_eq_zero h_sum h_nonzero n

/-- Away from the prescribed zero set `Set.range a`, the canonical product is nonzero. -/
theorem canonicalProduct_ne_zero {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0)
    {z : ℂ} (hz : z ∉ Set.range a) :
    canonicalProduct m a z ≠ 0 := by
  let f : ℕ → ℂ := fun n ↦ weierstrassFactor m (z / a n) - 1
  have hfn : ∀ n, 1 + f n ≠ 0 := by
    intro n
    have hza : z ≠ a n := by
      intro hza
      exact hz ⟨n, hza.symm⟩
    simpa [f] using (weierstrassFactor_div_ne_zero_iff (m := m) (a := a n) (z := z)
      (h_nonzero n)).2 hza
  have hnormsumm :
      Summable (fun n : ℕ ↦ ‖weierstrassFactor m (z / a n) - 1‖) :=
    summable_norm_weierstrassFactor_div_sub_one_of_summable_inv_pow
      (m := m) (a := a) h_sum h_nonzero z
  simpa [canonicalProduct, f] using
    (tprod_one_add_ne_zero_of_summable (f := f) hfn hnormsumm)

private theorem tendsto_deriv_canonicalPartialProduct {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) (n : ℕ) :
    Tendsto (fun N ↦ deriv (fun z ↦ ∏ k ∈ Finset.range N, weierstrassFactor m (z / a k)) (a n))
      Filter.atTop
      (𝓝 (deriv (canonicalProduct m a) (a n))) := by
  have hloc :=
    HasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange
      (hasProdLocallyUniformlyOn_weierstrassFactor_div_of_summable_inv_pow
        (m := m) (a := a) h_sum h_nonzero)
  have hpartial :
      ∀ᶠ N in Filter.atTop,
        DifferentiableOn ℂ (fun z ↦ ∏ k ∈ Finset.range N, weierstrassFactor m (z / a k)) Set.univ := by
    filter_upwards with N
    exact differentiableOn_canonicalPartialProduct m a N
  simpa [canonicalProduct] using
    (hloc.deriv hpartial isOpen_univ).tendsto_at (by simp)

/-- Under injectivity, the canonical product admits a local linear factor at each prescribed zero. -/
theorem exists_analyticAt_canonicalProduct_factor {m : ℕ} {a : ℕ → ℂ} (ha : Function.Injective a)
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) (n : ℕ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (a n) ∧ g (a n) ≠ 0 ∧
      canonicalProduct m a =ᶠ[𝓝 (a n)] fun z ↦ (z - a n) * g z := by
  let F : ℂ → ℂ := fun z ↦ weierstrassFactor m (z / a n)
  let G : ℂ → ℂ := fun z ↦
    ∏' k, Function.update (fun k ↦ weierstrassFactor m (z / a k)) n (fun _ ↦ (1 : ℂ)) k
  have hF_an : AnalyticAt ℂ F (a n) := by
    have hF_anNhd : AnalyticOnNhd ℂ F Set.univ := by
      exact DifferentiableOn.analyticOnNhd
        (differentiableOn_univ.mpr <| by
          simpa [F] using
            (differentiable_weierstrassFactor m).comp (differentiable_id.div_const (a n)))
        isOpen_univ
    exact hF_anNhd (a n) (by simp)
  have hF_order : analyticOrderAt F (a n) = 1 :=
    hF_an.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
      (by simp [F, h_nonzero n, weierstrassFactor_at_one])
      (by simpa [F] using deriv_weierstrassFactor_div_at_self_ne_zero m (h_nonzero n))
  obtain ⟨h, hh_an, hh0, hh_eq⟩ := (hF_an.analyticOrderAt_eq_natCast (n := 1)).mp hF_order
  have hG_an : AnalyticAt ℂ G (a n) :=
    (analyticOnNhd_updated_canonicalProduct h_sum h_nonzero n) (a n) (by simp)
  have hG0 : G (a n) ≠ 0 := by
    simpa [G] using tprod_updatedWeierstrassFactor_ne_zero ha h_sum h_nonzero n
  refine ⟨fun z ↦ h z * G z, hh_an.mul hG_an, mul_ne_zero hh0 hG0, ?_⟩
  have hsplit : canonicalProduct m a =ᶠ[𝓝 (a n)] fun z ↦ F z * G z :=
    Filter.Eventually.of_forall (canonicalProduct_eq_mul_updated_canonicalProduct h_sum h_nonzero n)
  filter_upwards [hh_eq, hsplit] with z hz1 hz2
  calc
    canonicalProduct m a z = F z * G z := hz2
    _ = ((z - a n) * h z) * G z := by rw [hz1]
    _ = (z - a n) * (h z * G z) := by ring

/-- Under injectivity, each prescribed zero of the canonical product is simple. -/
theorem analyticOrderAt_canonicalProduct_eq_one {m : ℕ} {a : ℕ → ℂ} (ha : Function.Injective a)
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) (n : ℕ) :
    analyticOrderAt (canonicalProduct m a) (a n) = 1 := by
  have han : AnalyticAt ℂ (canonicalProduct m a) (a n) :=
    (analyticOnNhd_canonicalProduct h_sum h_nonzero) (a n) (by simp)
  obtain ⟨g, hg, hg0, hEq⟩ := exists_analyticAt_canonicalProduct_factor ha h_sum h_nonzero n
  exact (han.analyticOrderAt_eq_natCast (n := 1)).2 ⟨g, hg, hg0, hEq⟩

/-- The zero set of the canonical product is exactly `Set.range a`. -/
theorem canonicalProduct_eq_zero_iff {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0)
    {z : ℂ} :
    canonicalProduct m a z = 0 ↔ z ∈ Set.range a := by
  constructor
  · intro hz0
    by_contra hzrange
    exact (canonicalProduct_ne_zero h_sum h_nonzero hzrange) hz0
  · exact canonicalProduct_eq_zero_of_mem_range h_sum h_nonzero

/-- Away from `Set.range a`, the canonical product is nonzero, expressed as an iff. -/
theorem canonicalProduct_ne_zero_iff {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0)
    {z : ℂ} :
    canonicalProduct m a z ≠ 0 ↔ z ∉ Set.range a := by
  rw [not_iff_not]
  exact canonicalProduct_eq_zero_iff h_sum h_nonzero

end Complex
