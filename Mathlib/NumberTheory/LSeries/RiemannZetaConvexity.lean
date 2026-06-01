/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.RiemannZetaAbelContinuation
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.MetricSpace.Basic

/-!
# Bounds for the Riemann zeta function

Euler product estimates and strip bounds for `riemannZeta`, used in `ZetaFiniteOrder`.
Abel-summation continuation is in `RiemannZetaAbelContinuation`.

## Main results

* `norm_riemannZeta_le`, `norm_riemannZeta_shift_le` : strip bounds for the Λ₀ pipeline
* `norm_riemannZeta_ratio_le_on_vertical_line` : convexity input on vertical lines
* `riemannZeta_eq_zetaContinuationAux` : Abel formula for `1/10 < re s`, `s ≠ 1` (in `RiemannZetaAbelContinuation`)
-/

@[expose] public section

open scoped BigOperators Topology

/-- The subtype of prime natural numbers, used as the Euler product index type. -/
abbrev ℙ := Nat.Primes

-- Euler product bounds

private lemma abs_zeta_prod_prime (s : ℂ) (hs : 1 < s.re) :
  norm (riemannZeta s) = ∏' p : ℙ, (norm (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ)))⁻¹ := by
  calc
    norm (riemannZeta s) = norm (∏' p : ℙ, (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹) := by
      rw [riemannZeta_eulerProduct_tprod hs]
    _ = ∏' p : ℙ, norm ((1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹) := by
      exact Multipliable.norm_tprod (riemannZeta_eulerProduct_hasProd hs).multipliable
    _ = ∏' p : ℙ, (norm (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ)))⁻¹ := by
      congr 1; ext p
      simp [norm_inv, (isUnit_one_sub_of_norm_lt_one (Nat.Primes.norm_cpow_neg_lt_one p s hs)).ne_zero]

section EulerProductTools

local notation "ι" => fun (z : ℂˣ) ↦ (z : ℂ)

private theorem tprod_commutes_with_inclusion_infinite {α : Type*} (f : α → ℂˣ) (h : Multipliable f) :
    ι (tprod f) = tprod (fun i ↦ ι (f i)) := by
  change ((tprod f : ℂˣ) : ℂ) = tprod (fun i ↦ ((f i : ℂˣ) : ℂ))
  have hcont : Continuous (Units.coeHom ℂ) := by
    simpa using (Units.continuous_val : Continuous (fun u : ℂˣ => ((u : ℂˣ) : ℂ)))
  simpa [Units.coeHom] using
    (Multipliable.map_tprod (f := f) (γ := ℂ) h (g := Units.coeHom ℂ) hcont)

private theorem inclusion_commutes_with_division (a b : ℂˣ) :
    ι (a / b) = ι a / ι b := Units.val_div_eq_div_val a b

private lemma lift_multipliable_of_nonzero {P : Type*} (a : P → ℂ) (ha : Multipliable a)
    (h_a_nonzero : ∀ p, a p ≠ 0) (hA_nonzero' : ∀ A, HasProd a A → A ≠ 0) :
    Multipliable (fun p ↦ Units.mk0 (a p) (h_a_nonzero p)) := by
  obtain ⟨A, hA⟩ := ha
  have hA_nonzero := hA_nonzero' A hA
  refine ⟨Units.mk0 A hA_nonzero, ?_⟩
  simp [HasProd, tendsto_nhds] at hA ⊢
  intro sU h_sU_open hA_mem
  have hA_im_mem : ι (Units.mk0 A hA_nonzero) ∈ ι '' sU := Set.mem_image_of_mem ι hA_mem
  have sU_im_open : IsOpen (ι '' sU) := by
    apply (Topology.IsOpenEmbedding.isOpen_iff_image_isOpen ?_).mp
    assumption
    exact Units.isOpenEmbedding_val
  have := hA (ι '' sU) sU_im_open hA_im_mem
  obtain ⟨a1, ha⟩ := this
  use a1
  intro b ha1
  obtain ⟨x', x'_spec_mem, x'_spec_eq⟩ := ha b ha1
  suffices x' = ∏ b ∈ b, Units.mk0 (a b) (by simp [*]) by
    rwa [← this]
  have : Units.mk0 (ι x') (Units.ne_zero x') = x' :=
    Units.mk0_val x' (Units.ne_zero x')
  have this2 : (Units.mk0 (∏ b ∈ b, a b)
    (Finset.prod_ne_zero_iff.mpr fun a a_1 => h_a_nonzero a)) = x' :=
      Units.val_inj.mp (id (Eq.symm x'_spec_eq))
  rw [Units.mk0_prod] at this2
  rw [←this2]
  conv =>
    rhs
    rw [← Finset.prod_attach]

private lemma prod_of_ratios_simplified {P : Type*} (a b : P → ℂ)
    (ha : Multipliable a) (hb : Multipliable b)
    (h_a_nonzero : ∀ p, a p ≠ 0) (h_b_nonzero : ∀ p, b p ≠ 0)
    (hA_nonzero' : ∀ A, HasProd a A → A ≠ 0) (hB_nonzero' : ∀ A, HasProd b A → A ≠ 0) :
    (∏' p : P, a p) / (∏' p : P, b p) = ∏' p : P, (a p / b p) := by
  let a' : P → ℂˣ := fun p ↦ Units.mk0 (a p) (h_a_nonzero p)
  let b' : P → ℂˣ := fun p ↦ Units.mk0 (b p) (h_b_nonzero p)
  have h_multipliable_a' : Multipliable a' :=
    lift_multipliable_of_nonzero a ha h_a_nonzero hA_nonzero'
  have h_multipliable_b' : Multipliable b' :=
    lift_multipliable_of_nonzero b hb h_b_nonzero hB_nonzero'
  have h_multipliable_a'_div_b' : Multipliable (fun p ↦ a' p / b' p) :=
    Multipliable.div h_multipliable_a' h_multipliable_b'
  calc
    (∏' p, a p) / (∏' p, b p)
        = (∏' p, ι (a' p)) / (∏' p, ι (b' p)) := by simp [a', b']
    _ = ι (∏' p, a' p) / ι (∏' p, b' p) := by
          simp [tprod_commutes_with_inclusion_infinite, tprod_commutes_with_inclusion_infinite, *]
    _ = ι ((∏' p, a' p) / (∏' p, b' p)) := by rw [← inclusion_commutes_with_division]
    _ = ι (∏' p, a' p / b' p) := by simp [Multipliable.tprod_div, *]
    _ = ∏' p, ι (a' p / b' p) := by simp [tprod_commutes_with_inclusion_infinite, *]
    _ = ∏' p, (ι (a' p) / ι (b' p)) := by simp [inclusion_commutes_with_division]
    _ = ∏' p, a p / b p := by simp [a', b']

private lemma prod_of_ratios {P : Type*} (a b : P → ℂ) (ha : Multipliable a) (hb : Multipliable b)
    (h_b_nonzero : ∀ p, b p ≠ 0) (hA_nonzero' : ∀ A, HasProd a A → A ≠ 0)
    (hB_nonzero' : ∀ B, HasProd b B → B ≠ 0) :
    (∏' p : P, a p) / (∏' p : P, b p) = ∏' p : P, (a p / b p) := by
  by_cases h_a_zero : ∃ p, a p = 0
  · have lhs_zero : ∏' p : P, a p = 0 := tprod_of_exists_eq_zero h_a_zero
    have rhs_zero : ∏' p : P, (a p / b p) = 0 := by
      obtain ⟨p₀, hp₀⟩ := h_a_zero
      exact tprod_of_exists_eq_zero ⟨p₀, by simp [hp₀]⟩
    simp [lhs_zero, rhs_zero]
  · push_neg at h_a_zero
    exact prod_of_ratios_simplified a b ha hb h_a_zero h_b_nonzero hA_nonzero' hB_nonzero'

private lemma eulerFactor_tprod_div (s : ℂ) (hs : 1 < s.re) :
    (∏' p : ℙ, (1 - ((p : ℕ) : ℂ) ^ (-(2 * s) : ℂ))⁻¹) / (∏' p : ℙ, (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹) =
      ∏' p : ℙ, ((1 - ((p : ℕ) : ℂ) ^ (-(2 * s) : ℂ))⁻¹ / (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹) := by
  let a := fun p : ℙ => (1 - ((p : ℕ) : ℂ) ^ (-(2 * s) : ℂ))⁻¹
  let b := fun p : ℙ => (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹
  have ha : Multipliable a :=
    (riemannZeta_eulerProduct_hasProd (by simp; linarith)).multipliable
  have hb : Multipliable b := (riemannZeta_eulerProduct_hasProd hs).multipliable
  have h_b_nonzero : ∀ p, b p ≠ 0 := fun p =>
    inv_ne_zero (isUnit_one_sub_of_norm_lt_one (Nat.Primes.norm_cpow_neg_lt_one p s hs)).ne_zero
  refine prod_of_ratios a b ha hb h_b_nonzero (by
    intro A hA
    have h_eq : A = riemannZeta (2 * s) := by
      have h : HasProd a (riemannZeta (2 * s)) := by
        simpa [a] using riemannZeta_eulerProduct_hasProd (s := 2 * s) (by simp; linarith)
      exact HasProd.unique hA h
    rw [h_eq]
    exact riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)) (by
    intro B hB
    have h_eq : B = riemannZeta s := by
      have h : HasProd b (riemannZeta s) := by
        simpa [b] using riemannZeta_eulerProduct_hasProd (s := s) hs
      exact HasProd.unique hB h
    rw [h_eq]
    exact riemannZeta_ne_zero_of_one_lt_re hs)

private lemma ratio_invs (z : ℂ) (hz : norm z < 1) :
    (1 - z ^ 2)⁻¹ / (1 - z)⁻¹ = (1 + z)⁻¹ := by
  have hz1 : 1 - z ≠ 0 := (isUnit_one_sub_of_norm_lt_one hz).ne_zero
  have h1 : 1 - z ^ 2 = (1 - z) * (1 + z) := by ring
  simp [div_eq_mul_inv, h1, mul_inv_rev, hz1, mul_comm, mul_left_comm, mul_assoc]

/-- `ζ(2s)/ζ(s)` equals the Euler product of `(1 + p^{-s})^{-1}`. -/
theorem zeta_ratio_identity (s : ℂ) (hs : 1 < s.re) :
    riemannZeta (2 * s) / riemannZeta s = ∏' p : ℙ, (1 + ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹ := by
  rw [← riemannZeta_eulerProduct_tprod (by simp; linarith)]
  rw [← riemannZeta_eulerProduct_tprod hs]
  rw [eulerFactor_tprod_div s hs]
  congr 1; ext p
  have hp : ((p : ℕ) : ℂ) ≠ 0 := by
    rw [ne_eq, Nat.cast_eq_zero]; exact Nat.Prime.ne_zero p.2
  have hpow : ((p : ℕ) : ℂ) ^ (-(2 * s)) = (((p : ℕ) : ℂ) ^ (-s))^2 := by
    rw [show -(2 * s) = 2 * (-s) from by ring,
      show (2 : ℂ) * (-s) = ((2 : ℕ) : ℂ) * (-s) from by norm_cast, Complex.cpow_nat_mul]
  have hz : norm (((p : ℕ) : ℂ) ^ (-s)) < 1 := Nat.Primes.norm_cpow_neg_lt_one p s hs
  rw [hpow, ratio_invs (((p : ℕ) : ℂ) ^ (-s)) hz]

private lemma zeta_ratio_at_real (r : ℝ) (hr : 1 < (((r : ℝ) / 2 : ℂ)).re) :
    riemannZeta (r : ℂ) / riemannZeta ((r / 2 : ℝ) : ℂ) =
      ∏' p : ℙ, (1 + ((p : ℕ) : ℂ) ^ (-(((r : ℝ) / 2) : ℂ)))⁻¹ := by
  have h2s : (2 : ℂ) * ((r : ℝ) / 2 : ℂ) = (r : ℂ) := by
    have hreal : (2 : ℝ) * (r / 2) = r := by ring
    calc
      (2 : ℂ) * ((r : ℝ) / 2 : ℂ) = ((2 * (r / 2) : ℝ) : ℂ) := by simp
      _ = (r : ℂ) := by simp [hreal]
  simpa [h2s] using zeta_ratio_identity (((r : ℝ) / 2 : ℂ)) hr

end EulerProductTools

private lemma abs_term_bound (p : ℙ) (t : ℝ) :
  norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))) ≤ 1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)) := by
  have h1 : norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))) ≤
      1 + norm (((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))) := by
    simpa [sub_eq_add_neg, norm_one, norm_neg] using
      norm_add_le (1 : ℂ) (-((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I)))
  have h2 := Nat.Primes.norm_cpow_neg_eq_rpow_neg_re p (((3 : ℝ) / 2) + t * Complex.I)
  have h3 : (((3 : ℝ) / 2) + t * Complex.I).re = ((3 : ℝ) / 2) := by simp [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re]
  have h4 : -(((3 : ℝ) / 2) + t * Complex.I).re = -((3 : ℝ) / 2) := by simp [h3]
  have h5 : norm (((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))) = ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)) := by
    rw [h2, h4]
  rw [h5] at h1
  exact h1

private lemma condp32 (p : ℙ) (t : ℝ) : 1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I)) ≠ 0 := by
  intro h
  have hp_eq_one : ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I)) = 1 := by
    rw [sub_eq_zero] at h; exact h.symm
  let s := ((3 : ℝ) / 2) + t * Complex.I
  have hs : 1 < s.re := by
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, add_zero]
    norm_num
  have h_abs_lt : norm (((p : ℕ) : ℂ) ^ (-s)) < 1 := Nat.Primes.norm_cpow_neg_lt_one p s hs
  have h_s_eq : ((p : ℕ) : ℂ) ^ (-s) = ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I)) := by simp only [s]
  rw [h_s_eq, hp_eq_one] at h_abs_lt
  have : norm (1 : ℂ) = 1 := by simp [norm, norm_one]
  rw [this] at h_abs_lt
  exact lt_irrefl 1 h_abs_lt

private lemma abs_term_inv_bound (p : ℙ) (t : ℝ) : (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ ≤ (norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))))⁻¹ := by
  have h1 := abs_term_bound p t
  have h2 := condp32 p t
  have hpos : 0 < norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))) :=
    norm_pos_iff.mpr h2
  simpa [one_div] using one_div_le_one_div_of_le hpos h1

private lemma multipliable_complex_abs_inv {i : Type*} (g : i → ℂ)
    (h_mult : Multipliable (fun i => (1 - g i)⁻¹)) :
    Multipliable (fun i => (norm (1 - g i))⁻¹) := by
  have h_norm_mult : Multipliable (fun i => ‖(1 - g i)⁻¹‖) := Multipliable.norm h_mult
  simpa [norm_inv] using h_norm_mult

private lemma multipliable_positive_inv_powers (r : ℝ) (hr : 1 < r) :
    Multipliable (fun p : ℙ => (1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹) := by
  have h_sum : Summable (fun p : ℙ => ((p : ℕ) : ℝ) ^ (-r)) := by
    rw [Nat.Primes.summable_rpow]
    linarith
  have h_log_sum : Summable (fun p : ℙ => Real.log (1 + ((p : ℕ) : ℝ) ^ (-r))) :=
    Real.summable_log_one_add_of_summable h_sum
  have h_log_inv_sum : Summable (fun p : ℙ => Real.log ((1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹)) := by
    simpa [Real.log_inv, neg_mul] using h_log_sum.neg
  have h_pos : ∀ p : ℙ, 0 < (1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹ := by
    intro p
    apply inv_pos.mpr
    have h_ge : 0 ≤ ((p : ℕ) : ℝ) ^ (-r) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    linarith
  exact Real.multipliable_of_summable_log h_pos h_log_inv_sum

section PositiveTprod

private lemma hasProd_nonneg_of_pos {i : Type*} (f : i → ℝ) (hpos : ∀ i, 0 < f i) (a : ℝ)
    (ha : HasProd f a) : 0 ≤ a :=
  ge_of_tendsto ha <| Filter.Eventually.of_forall fun s =>
    le_of_lt <| Finset.prod_pos fun i _ => hpos i

private lemma hasProd_nnreal_of_coe {i : Type*} (g : i → NNReal) (b : NNReal)
    (h : HasProd (fun i => (g i : ℝ)) (b : ℝ)) : HasProd g b := by
  have h_eq : (fun s => ∏ i ∈ s, (g i : ℝ)) = fun s => ↑(∏ i ∈ s, g i) := by
    ext s; exact (NNReal.coe_prod s g).symm
  have h_comp : Filter.Tendsto ((fun x : NNReal => (x : ℝ)) ∘ fun s => ∏ i ∈ s, g i) Filter.atTop
      (𝓝 (b : ℝ)) := by
    show Filter.Tendsto (fun s => ↑(∏ i ∈ s, g i)) Filter.atTop (𝓝 (b : ℝ))
    rw [← h_eq]
    exact h
  exact NNReal.isEmbedding_coe.tendsto_nhds_iff.mpr h_comp

private lemma multipliable_real_to_nnreal {i : Type*} (f : i → ℝ) (hpos : ∀ i, 0 < f i)
    (h_mult : Multipliable f) : Multipliable (fun i => ⟨f i, le_of_lt (hpos i)⟩ : i → NNReal) := by
  obtain ⟨a, ha⟩ := h_mult
  let a_nnreal : NNReal := ⟨a, hasProd_nonneg_of_pos f hpos a ha⟩
  exact ⟨a_nnreal, hasProd_nnreal_of_coe _ _ (by simp [NNReal.coe_mk]; exact ha)⟩

private lemma nnreal_coe_tprod_eq_tprod_coe {i : Type*} (f : i → NNReal) (hf : Multipliable f) :
    ∏' i, (↑(f i) : ℝ) = ↑(∏' i, f i) :=
  (HasProd.map (Multipliable.hasProd hf) NNReal.toRealHom NNReal.continuous_coe).tprod_eq

private lemma nnreal_tprod_le_coe {i : Type*} (f g : i → NNReal) (hf : Multipliable f)
    (hg : Multipliable g) (h : ∏' i, f i ≤ ∏' i, g i) :
    ∏' i, (f i : ℝ) ≤ ∏' i, (g i : ℝ) := by
  rw [nnreal_coe_tprod_eq_tprod_coe f hf, nnreal_coe_tprod_eq_tprod_coe g hg]
  exact NNReal.coe_le_coe.mpr h

end PositiveTprod

private lemma abs_zeta_inequality (t : ℝ) :
  ∏' p : ℙ, (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ ≤
  ∏' p : ℙ, (norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))))⁻¹ := by
  let s := ((3 : ℝ) / 2) + t * Complex.I
  have hs : 1 < s.re := by
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero, add_zero]
    norm_num
  have h_pos_left : ∀ p : ℙ, 0 < (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ := fun p => by
    exact inv_pos.mpr (add_pos zero_lt_one <| Real.rpow_pos_of_pos (Nat.cast_pos.mpr p.property.pos) _)
  have h_pos_right : ∀ p : ℙ, 0 < (norm (1 - ((p : ℕ) : ℂ) ^ (-s)))⁻¹ := fun p => by
    exact inv_pos.mpr (norm_pos_iff.mpr (condp32 p t))
  let f : ℙ → NNReal := fun p => ⟨(1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹, le_of_lt (h_pos_left p)⟩
  let g : ℙ → NNReal := fun p => ⟨(norm (1 - ((p : ℕ) : ℂ) ^ (-s)))⁻¹, le_of_lt (h_pos_right p)⟩
  have hf := multipliable_real_to_nnreal _ h_pos_left <|
    multipliable_positive_inv_powers ((3 : ℝ) / 2) (by norm_num : 1 < (3 : ℝ) / 2)
  have hg := multipliable_real_to_nnreal _ h_pos_right <|
    multipliable_complex_abs_inv (fun p : ℙ => ((p : ℕ) : ℂ) ^ (-s))
      (riemannZeta_eulerProduct_hasProd hs).multipliable
  have h_nnreal : ∏' p, f p ≤ ∏' p, g p :=
    Multipliable.tprod_le_tprod (fun p => by
      simp only [f, g, ← NNReal.coe_le_coe, NNReal.coe_mk]
      exact abs_term_inv_bound p t) hf hg
  have h_convert : ∏' p, (f p : ℝ) ≤ ∏' p, (g p : ℝ) := nnreal_tprod_le_coe f g hf hg h_nnreal
  have h_eq_f : ∏' p, (f p : ℝ) = ∏' p : ℙ, (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ := by
    simp only [f, NNReal.coe_mk]
  have h_eq_g : ∏' p, (g p : ℝ) = ∏' p : ℙ, (norm (1 - ((p : ℕ) : ℂ) ^ (-s)))⁻¹ := by
    simp only [g, NNReal.coe_mk]
  rw [h_eq_f, h_eq_g] at h_convert
  exact h_convert

private lemma abs_zeta_ratio_eval : norm (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2)) = ∏' p : ℙ, (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ := by
  -- Start from the Euler product identity at 3/2
  have hratio := zeta_ratio_at_real 3 (by norm_num : 1 < (((3 : ℝ) / 2 : ℂ)).re)
  -- Define complex and real Euler factors
  let w : ℙ → ℂ := fun p => (1 + ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) : ℂ)))⁻¹
  let u : ℙ → ℝ := fun p => (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹
  -- Multipliability of the real factors
  have hu_mult : Multipliable u :=
    multipliable_positive_inv_powers ((3 : ℝ) / 2) (by norm_num : 1 < (3 : ℝ) / 2)
  -- Show w is the complexification of u
  have hw_eq : w = fun p : ℙ => (u p : ℂ) := by
    funext p
    -- rewrite the complex cpow as a real rpow, using nonnegativity of the base
    have hx : 0 ≤ ((p : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le (p : ℕ))
    have hcpow : (((((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2))) : ℝ) : ℂ)
        = ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) : ℂ)) := by
      simpa using (Complex.ofReal_cpow (x := ((p : ℕ) : ℝ)) (hx := hx) (y := -((3 : ℝ) / 2)))
    calc
      w p = (1 + ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) : ℂ)))⁻¹ := rfl
      _ = (1 + (((((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2))) : ℝ) : ℂ))⁻¹ := by
        simp [hcpow]
      _ = (((1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ : ℝ) : ℂ) := by
        simp [Complex.ofReal_add, Complex.ofReal_inv, Complex.ofReal_one]
  -- Multipliability of the complex factors via mapping by ofReal
  have hw_mult : Multipliable w := by
    have hmap : Multipliable ((fun x : ℝ => (x : ℂ)) ∘ u) :=
      Multipliable.map (hf := hu_mult) Complex.ofRealHom Complex.continuous_ofReal
    simpa [hw_eq] using hmap
  -- Take absolute values inside the product
  have h_abs_tprod : norm (∏' p : ℙ, w p) = ∏' p : ℙ, norm (w p) :=
    Multipliable.norm_tprod hw_mult
  -- For each factor, the absolute value equals the real factor
  have h_abs_eq_fun : (fun p : ℙ => norm (w p)) = u := by
    funext p
    -- u p ≥ 0
    have hge : 0 ≤ ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)) :=
      Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le (p : ℕ))) _
    have hpos : 0 < 1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)) := by linarith
    have hnonneg : 0 ≤ u p := by
      have : 0 < (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ := inv_pos.mpr hpos
      exact this.le
    -- conclude
    simp [hw_eq, Complex.norm_real, abs_of_nonneg hnonneg]
  -- Rewrite the ratio using the identity, then conclude
  have h_abs_ratio : norm (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2))
      = norm (∏' p : ℙ, w p) := by
    simpa [w] using congrArg norm hratio
  calc
    norm (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2))
        = norm (∏' p : ℙ, w p) := h_abs_ratio
    _ = ∏' p : ℙ, norm (w p) := h_abs_tprod
    _ = ∏' p : ℙ, u p := by simp [h_abs_eq_fun]
    _ = ∏' p : ℙ, (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ := rfl

/-- For `t : ℝ`, the Euler product at `re s = 3` controls `‖ζ 3 / ζ (3/2 + it)‖`. -/
theorem norm_riemannZeta_ratio_le_on_vertical_line (t : ℝ) :
    ‖riemannZeta 3 / riemannZeta ((3 : ℝ) / 2)‖ ≤
      ‖riemannZeta (((3 : ℝ) / 2) + t * Complex.I)‖ := by
  have hs : 1 < (((3 : ℝ) / 2 : ℂ) + t * Complex.I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, mul_zero, add_zero]
    norm_num
  calc
    norm (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2))
        = ∏' p : ℙ, (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ := abs_zeta_ratio_eval
    _ ≤ ∏' p : ℙ, (norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))))⁻¹ :=
          abs_zeta_inequality t
    _ = norm (riemannZeta (((3 : ℝ) / 2 : ℂ) + t * Complex.I)) := by
          simpa using (abs_zeta_prod_prime (((3 : ℝ) / 2 : ℂ) + t * Complex.I) hs).symm

open Real Set Filter Topology MeasureTheory

/-- If `1/10 < re s` and `s ≠ 1`, then `‖ζ s‖ ≤ 1 + ‖(s - 1)⁻¹‖ + ‖s‖ / re s`. -/
theorem norm_riemannZeta_le (s : ℂ) (hs_re : 1/10 < s.re) (hs_ne : s ≠ 1) :
    ‖riemannZeta s‖ ≤ 1 + ‖1 / (s - 1)‖ + ‖s‖ / s.re := by
  set f : ℝ → ℂ := fun u => (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1) with hfdef
  set g : ℝ → ℝ := fun u => u ^ (-s.re - 1) with hgdef
  have hζ : ‖riemannZeta s‖ ≤ 1 + ‖1 / (s - 1)‖ + ‖s‖ * ‖∫ u in Ioi (1 : ℝ), f u‖ := by
    classical
    set S : Set ℂ := {z : ℂ | z ≠ 1}
    set T : Set ℂ := {z : ℂ | z ∈ S ∧ 1/10 < z.re}
    set Iint : ℂ := ∫ u in Ioi (1 : ℝ), f u
    have hT : s ∈ T := by
      have hsS : s ∈ S := by simpa [S, Set.mem_setOf_eq] using hs_ne
      simpa [T, Set.mem_setOf_eq] using And.intro hsS hs_re
    have hAC : ∀ z ∈ T,
        riemannZeta z = 1 + 1 / (z - 1) - z * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-z - 1) := by
      simpa [S, T] using riemannZeta_eq_zetaContinuationAux
    have hzeta : riemannZeta s = 1 + 1 / (s - 1) - s * Iint := by
      simpa [Iint, hfdef] using hAC s hT
    have h1 : ‖riemannZeta s‖ ≤ ‖1 + 1 / (s - 1)‖ + ‖-s * Iint‖ := by
      simpa [hzeta, sub_eq_add_neg] using norm_add_le (1 + 1 / (s - 1)) (-s * Iint)
    have hA : ‖1 + 1 / (s - 1)‖ ≤ 1 + ‖1 / (s - 1)‖ := by
      simpa using norm_add_le (1 : ℂ) (1 / (s - 1))
    have hB : ‖-s * Iint‖ = ‖s‖ * ‖Iint‖ := by simp
    have h2 : ‖riemannZeta s‖ ≤ (1 + ‖1 / (s - 1)‖) + (‖s‖ * ‖Iint‖) :=
      le_trans h1 (add_le_add hA hB.le)
    simpa [add_assoc, add_left_comm, add_comm] using h2
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Ioi (1 : ℝ))
  have h_ae_bound : ∀ᵐ u ∂μ, ‖f u‖ ≤ g u := by
    have hforall : ∀ u ∈ Ioi (1 : ℝ), ‖f u‖ ≤ g u := by
      intro u hu
      have := fract_kernel_norm_bound u (le_of_lt hu) s
      simpa [hfdef, hgdef] using this
    have hmeas : MeasurableSet (Ioi (1 : ℝ)) := measurableSet_Ioi
    simpa [μ] using
      (MeasureTheory.ae_restrict_of_forall_mem (μ := volume) (s := Ioi (1 : ℝ)) hmeas hforall)
  have hg_intOn : IntegrableOn g (Ioi (1 : ℝ)) := by
    classical
    by_contra hnot
    have hnot' : ¬ Integrable g μ := by simpa [μ, IntegrableOn] using hnot
    have hint0 : (∫ u, g u ∂μ) = 0 := by
      simpa using (integral_undef (μ := μ) (f := g) hnot')
    have hval : ∫ u in Ioi (1 : ℝ), g u = 1 / s.re := by
      simpa [hgdef] using integral_Ioi_rpow_neg_re_sub_one (hs := by linarith [hs_re])
    have hne : (1 / s.re) ≠ 0 := by exact one_div_ne_zero (ne_of_gt (by linarith [hs_re]))
    have : (∫ u in Ioi (1 : ℝ), g u) = 0 := by simpa [μ] using hint0
    exact hne (by simpa [hval] using this)
  have hg_int : Integrable g μ := by simpa [μ, IntegrableOn] using hg_intOn
  have h_int_bound : ‖∫ u in Ioi (1 : ℝ), f u‖ ≤ ∫ u in Ioi (1 : ℝ), g u := by
    have :=
      (MeasureTheory.norm_integral_le_of_norm_le (μ := μ) (f := f) (g := g) hg_int h_ae_bound)
    simpa [μ] using this
  have h_g_val : ∫ u in Ioi (1 : ℝ), g u = 1 / s.re := by
    simpa [hgdef] using integral_Ioi_rpow_neg_re_sub_one (hs := by linarith [hs_re])
  have h_int_bound_conc : ‖∫ u in Ioi (1 : ℝ), f u‖ ≤ 1 / s.re := by
    simpa [h_g_val] using h_int_bound
  have hmul : ‖s‖ * ‖∫ u in Ioi (1 : ℝ), f u‖ ≤ ‖s‖ * (1 / s.re) := by
    exact mul_le_mul_of_nonneg_left h_int_bound_conc (by exact norm_nonneg s)
  have hsum0 : (1 + ‖1 / (s - 1)‖) + ‖s‖ * ‖∫ u in Ioi (1 : ℝ), f u‖
      ≤ (1 + ‖1 / (s - 1)‖) + ‖s‖ * (1 / s.re) := by
    exact (add_le_add_iff_left (1 + ‖1 / (s - 1)‖)).mpr hmul
  have hsum : 1 + ‖1 / (s - 1)‖ + ‖s‖ * ‖∫ u in Ioi (1 : ℝ), f u‖
      ≤ 1 + ‖1 / (s - 1)‖ + ‖s‖ * (1 / s.re) := by
    simpa [add_assoc] using hsum0
  have hfinal1 : ‖riemannZeta s‖ ≤ 1 + ‖1 / (s - 1)‖ + ‖s‖ * (1 / s.re) :=
    le_trans hζ hsum
  simpa [div_eq_mul_inv] using hfinal1

private lemma helper_three_abs_sq (t : ℝ) : (3 : ℝ) ^ 2 + t ^ 2 ≤ (3 + |t|) ^ 2 := by
  have hnonneg : 0 ≤ (6 : ℝ) * |t| := by
    have h6 : (0 : ℝ) ≤ 6 := by norm_num
    exact mul_nonneg h6 (abs_nonneg t)
  have hmul : |t| * |t| = t * t := by
    simp
  calc
    (3 : ℝ) ^ 2 + t ^ 2 = (3 : ℝ) ^ 2 + t * t := by simp [pow_two]
    _ = (3 : ℝ) ^ 2 + |t| * |t| := by simp [hmul]
    _ ≤ (3 : ℝ) ^ 2 + |t| * |t| + (6 : ℝ) * |t| := by exact le_add_of_nonneg_right hnonneg
    _ = (3 + |t|) ^ 2 := by ring

/-- Lemma: Bound on `‖s‖` when `1/2 ≤ Re(s) < 3`. -/
private lemma lem_sBound (s : ℂ) (hs : (1/2 : ℝ) ≤ s.re ∧ s.re < (3 : ℝ)) : ‖s‖ < (3 : ℝ) + |s.im| := by
  have hnegthree_lt_re : (- (3 : ℝ)) < s.re := by
    have hlt : (- (3 : ℝ)) < (1 / 2 : ℝ) := by norm_num
    exact lt_of_lt_of_le hlt hs.1
  have hlt3 : s.re < (3 : ℝ) := hs.2
  have h_re_sq_lt : s.re ^ 2 < (3 : ℝ) ^ 2 := by
    simpa using (sq_lt_sq' hnegthree_lt_re hlt3)
  have hsumlt : s.re ^ 2 + s.im ^ 2 < (3 : ℝ) ^ 2 + s.im ^ 2 := by
    exact (add_lt_add_iff_right (s.im ^ 2)).mpr h_re_sq_lt
  have hsq : ‖s‖ ^ 2 < (3 + |s.im|) ^ 2 := by
    have hnormSq : Complex.normSq s < (3 + |s.im|) ^ 2 := by
      have h := lt_of_lt_of_le hsumlt (helper_three_abs_sq s.im)
      simpa [Complex.normSq_apply, pow_two] using h
    rw [Complex.sq_norm]
    exact hnormSq
  have hnormnn : 0 ≤ ‖s‖ := norm_nonneg _
  have hpos : 0 ≤ (3 : ℝ) + |s.im| := add_nonneg (by norm_num) (abs_nonneg _)
  exact (sq_lt_sq₀ hnormnn hpos).1 hsq

/-- Lemma: Bound on `1 / Re(s)` under `1/2 ≤ Re(s) < 3`. -/
private lemma lem_invReSbound (s : ℂ) (hs : (1/2 : ℝ) ≤ s.re ∧ s.re < (3 : ℝ)) :
    1 / s.re ≤ (2 : ℝ) := by
  have h_pos : (0 : ℝ) < s.re := by
    linarith [hs.1]
  have h_half_pos : (0 : ℝ) < (1/2 : ℝ) := by norm_num
  have h_recip : 1 / s.re ≤ 1 / (1/2 : ℝ) := one_div_le_one_div_of_le h_half_pos hs.1
  have h_simplify : 1 / (1/2 : ℝ) = (2 : ℝ) := by norm_num
  rw [h_simplify] at h_recip
  exact h_recip

/-- Lemma: Lower bound on `‖s - 1‖` when `1/2 ≤ Re(s) < 3` and `|Im(s)| ≥ 1`. -/
private lemma lem_invSminus1bound (s : ℂ) (hs_re : (1/2 : ℝ) ≤ s.re ∧ s.re < (3 : ℝ)) (hs_im : (1 : ℝ) ≤ |s.im|) : (1 : ℝ) ≤ ‖s - 1‖ := by
  have h2 : |s.im| ≤ ‖s - 1‖ := by
    have : (s - (1 : ℂ)).im = s.im := by
      simp [Complex.sub_im, Complex.one_im]
    simpa [this] using Complex.abs_im_le_norm (s - 1)
  exact le_trans hs_im h2

/-- Final bound combination for the strip `1/2 ≤ re s < 3`, `1 ≤ |im s|`. -/
private lemma lem_finalBoundCombination (s : ℂ) (hs_re : (1/2 : ℝ) ≤ s.re ∧ s.re < (3 : ℝ)) (hs_im : (1 : ℝ) ≤ |s.im|) : ‖riemannZeta s‖ < 1 + 1 + ((3 : ℝ) + |s.im|) * 2 := by
  have hs_ne : s ≠ 1 := by
    intro h
    rw [h] at hs_im
    simp at hs_im
    linarith
  have hs_re_pos : 0 < s.re := by linarith [hs_re.1]
  have h1 : ‖riemannZeta s‖ ≤ 1 + 1 / ‖s - 1‖ + ‖s‖ / s.re := by
    simpa [one_div] using norm_riemannZeta_le s (by linarith [hs_re_pos]) hs_ne
  have h2 : (1 : ℝ) ≤ ‖s - 1‖ := lem_invSminus1bound s hs_re hs_im
  have h3 : 1 / ‖s - 1‖ ≤ 1 := by
    simpa [one_div, norm_inv] using inv_le_one_of_one_le₀ (a := ‖s - 1‖) h2
  have h4 : ‖s‖ < (3 : ℝ) + |s.im| := lem_sBound s hs_re
  have h5 : 1 / s.re ≤ (2 : ℝ) := lem_invReSbound s hs_re
  calc ‖riemannZeta s‖
    ≤ 1 + 1 / ‖s - 1‖ + ‖s‖ / s.re := h1
    _ ≤ 1 + 1 + ‖s‖ / s.re := by linarith [h3]
    _ ≤ 1 + 1 + ‖s‖ * 2 := by
      have s_nonneg : 0 ≤ ‖s‖ := norm_nonneg _
      have h6 : ‖s‖ / s.re ≤ ‖s‖ * 2 := by
        rw [div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_left h5 s_nonneg
      linarith
    _ < 1 + 1 + ((3 : ℝ) + |s.im|) * 2 := by linarith [h4]

/-- In the strip `1/2 ≤ re z < 3` with `1 ≤ |im z|`, `‖ζ z‖ < 8 + 2|im z|`. -/
theorem norm_riemannZeta_lt_linear_im_on_strip (z : ℂ)
    (hz_re : z.re ∈ Ico (1/2 : ℝ) (3 : ℝ)) (hz_im : (1 : ℝ) ≤ |z.im|) :
    ‖riemannZeta z‖ < (8 : ℝ) + 2 * |z.im| := by
  have hz_re' : (1/2 : ℝ) ≤ z.re ∧ z.re < (3 : ℝ) := by
    simpa [Ico] using hz_re
  calc ‖riemannZeta z‖
      < 1 + 1 + ((3 : ℝ) + |z.im|) * 2 := lem_finalBoundCombination z hz_re' hz_im
    _ = (8 : ℝ) + 2 * |z.im| := by ring

/-- For `z = s + 3/2 + it`, `z.re = s.re + 3/2` and `z.im = s.im + t`. -/
private theorem riemannZeta_shift_three_halves_re_im (s : ℂ) (t : ℝ) :
    (let z := s + (3/2 : ℝ) + Complex.I * t
     z.re = s.re + (3/2 : ℝ) ∧ z.im = s.im + t) := by
  constructor
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    have h1 : Complex.I.re = 0 := Complex.I_re
    have h2 : Complex.I.im * 0 = 0 := mul_zero _
    rw [h1, h2]
    simp
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    have h1 : Complex.I.re * 0 = 0 := mul_zero _
    have h2 : Complex.I.im = 1 := Complex.I_im
    rw [h1, h2]
    simp

/-- If `‖s‖ ≤ 1` and `2 < |t|`, then `s + 3/2 + it` lies in the strip used for
`norm_riemannZeta_lt_linear_im_on_strip`. -/
private theorem riemannZeta_shift_three_halves_mem_strip (s : ℂ) (t : ℝ)
    (hs : ‖s‖ ≤ (1 : ℝ)) (ht : (2 : ℝ) < |t|) :
    (let z := s + (3/2 : ℝ) + Complex.I * t
     z.re ∈ Ico (1/2 : ℝ) (3 : ℝ) ∧ (1 : ℝ) ≤ |z.im|) := by
  have h_calc := riemannZeta_shift_three_halves_re_im s t
  simp only [h_calc.1, h_calc.2]
  constructor
  · have hs_re_bound : |s.re| ≤ 1 :=
      (Complex.abs_re_le_norm s).trans hs
    rw [abs_le] at hs_re_bound
    rw [Set.mem_Ico]
    constructor
    · linarith [hs_re_bound.1]
    · linarith [hs_re_bound.2]
  · have hs_im_bound : |s.im| ≤ 1 :=
      (Complex.abs_im_le_norm s).trans hs
    rw [abs_le] at hs_im_bound
    by_cases h : 0 ≤ t
    · have ht_pos : t > 2 := by
        rwa [abs_of_nonneg h] at ht
      have lower_bound : s.im + t ≥ 1 := by
        linarith [hs_im_bound.1, ht_pos]
      have nonneg : 0 ≤ s.im + t := by linarith
      rw [abs_of_nonneg nonneg]
      linarith [lower_bound]
    · push_neg at h
      have ht_neg : t < -2 := by
        rw [abs_of_neg h] at ht
        linarith [ht]
      have upper_bound : s.im + t ≤ -1 := by
        linarith [hs_im_bound.2, ht_neg]
      have neg : s.im + t < 0 := by linarith
      rw [abs_of_neg neg]
      linarith [upper_bound]

/-- If `‖s‖ ≤ 1`, then `|im s + t| ≤ 1 + |t|`. -/
private theorem abs_im_add_shift_le (s : ℂ) (t : ℝ) (hs : ‖s‖ ≤ 1) : |s.im + t| ≤ 1 + |t| := by
  have h1 : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have h2 : |s.im| ≤ 1 := le_trans h1 hs
  have h3 : |s.im + t| ≤ |s.im| + |t| := abs_add_le s.im t
  linarith

/-- If `‖s‖ ≤ 1` and `2 < |t|`, then `‖ζ (s + 3/2 + it)‖ < 10 + 2|t|`. -/
theorem norm_riemannZeta_shift_le (t : ℝ) (s : ℂ) (hs : ‖s‖ ≤ 1) (ht : 2 < |t|) :
    ‖riemannZeta (s + (3 / 2 : ℝ) + Complex.I * t)‖ < 10 + 2 * |t| := by
  set z := s + (3/2 : ℝ) + Complex.I * t with hz_def
  have hz_cond : z.re ∈ Ico (1/2 : ℝ) (3 : ℝ) ∧ (1 : ℝ) ≤ |z.im| :=
    riemannZeta_shift_three_halves_mem_strip s t hs ht
  have h_bound : ‖riemannZeta z‖ < (8 : ℝ) + 2 * |z.im| :=
    norm_riemannZeta_lt_linear_im_on_strip z hz_cond.1 hz_cond.2
  have hz_im_calc : z.im = s.im + t := (riemannZeta_shift_three_halves_re_im s t).2
  have h_im_bound : |z.im| ≤ 1 + |t| := by
    rw [hz_im_calc]
    exact abs_im_add_shift_le s t hs
  have h_intermediate : ‖riemannZeta z‖ < (8 : ℝ) + 2 * (1 + |t|) := by
    calc ‖riemannZeta z‖
      < (8 : ℝ) + 2 * |z.im| := h_bound
      _ ≤ (8 : ℝ) + 2 * (1 + |t|) := by linarith [h_im_bound]
  have h_algebra : (8 : ℝ) + 2 * (1 + |t|) = (10 : ℝ) + 2 * |t| := by ring
  have h_final : ‖riemannZeta z‖ < (10 : ℝ) + 2 * |t| := by
    linarith [h_intermediate, h_algebra]
  rwa [hz_def] at h_final

open Metric Set Filter Asymptotics BigOperators
