/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.ZetaFunctionalEquation
public import Mathlib.Analysis.Complex.Domain
public import Mathlib.Topology.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Local API for Mathlib's completed Riemann zeta function

This file records basic local facts about Mathlib's `completedRiemannZeta`

`Λ(s) = Γ_ℝ(s) * ζ(s)`.

This is not the classical entire Riemann xi function
`ξ(s) = s * (s - 1) * Λ(s) / 2`; the statements below deliberately avoid introducing a
definitionally-equal alias for `completedRiemannZeta`.
-/

@[expose] public section

noncomputable section

open Complex

namespace Complex

/-- Open right half-plane Ω = { s | Re s > 1/2 }. -/
private lemma isOpen_Ω : IsOpen Ω := by
  change IsOpen {s : ℂ | (1 / 2 : ℝ) < s.re}
  exact isOpen_lt continuous_const Complex.continuous_re

/-- Differentiability of `completedRiemannZeta` away from its two poles `0` and `1`. -/
lemma differentiableAt_completedRiemannZeta_of_ne {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ completedRiemannZeta s := by
  exact differentiableAt_completedZeta (s := s) hs0 hs1

/-- Differentiability of `completedRiemannZeta` on the right half-plane `Ω`, away from `1`. -/
theorem differentiableOn_completedRiemannZeta_on_Ω_sdiff_one :
    DifferentiableOn ℂ completedRiemannZeta (Ω \ ({1} : Set ℂ)) := by
  intro z hz
  have hzΩ : (1 / 2 : ℝ) < z.re := by
    simpa [Ω, Set.mem_setOf_eq] using hz.1
  have hz0 : z ≠ 0 := by
    intro h0
    have : (0 : ℝ) < z.re := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hzΩ
    simp [h0, Complex.zero_re] at this
  have hz1 : z ≠ 1 := by simpa using hz.2
  exact (differentiableAt_completedRiemannZeta_of_ne (s := z) hz0 hz1).differentiableWithinAt

/-- Analyticity of `completedRiemannZeta` on the right half-plane `Ω`, away from `1`. -/
lemma analyticOn_completedRiemannZeta_on_Ω_sdiff_one :
    AnalyticOn ℂ completedRiemannZeta (Ω \ ({1} : Set ℂ)) := by
  have hOpen : IsOpen (Ω \ ({1} : Set ℂ)) :=
    (isOpen_Ω).sdiff isClosed_singleton
  have h :=
    (analyticOn_iff_differentiableOn (f := completedRiemannZeta)
      (s := Ω \ ({1} : Set ℂ)) hOpen)
  exact h.mpr differentiableOn_completedRiemannZeta_on_Ω_sdiff_one

/-- On `Ω`, zeros of the completed zeta factor `Λ` coincide with zeros of `riemannZeta`. -/
lemma completedRiemannZeta_eq_zero_iff_riemannZeta_eq_zero_on_Ω :
    ∀ z ∈ Ω, completedRiemannZeta z = 0 ↔ riemannZeta z = 0 := by
  intro z hzΩ
  have hhalf : (1 / 2 : ℝ) < z.re := by
    simpa [Ω, Set.mem_setOf_eq] using hzΩ
  have hpos : (0 : ℝ) < z.re := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hhalf
  have hΓnz : Gammaℝ z ≠ 0 := Gammaℝ_ne_zero_of_re_pos hpos
  have hζ : riemannZeta z = completedRiemannZeta z / Gammaℝ z :=
    riemannZeta_def_of_ne_zero (s := z) (by
      intro h0
      have hnot : ¬ ((1 / 2 : ℝ) < 0) := by norm_num
      exact hnot (by simpa [h0, Complex.zero_re] using hhalf))
  constructor
  · intro hΛ
    calc
      riemannZeta z = completedRiemannZeta z / Gammaℝ z := hζ
      _ = completedRiemannZeta z * (Gammaℝ z)⁻¹ := by rw [div_eq_mul_inv]
      _ = 0 * (Gammaℝ z)⁻¹ := by rw [hΛ]
      _ = 0 := by simp
  · intro hζ0
    have hdiv0 : completedRiemannZeta z / Gammaℝ z = 0 := by
      simpa [hζ] using hζ0
    by_contra hΛ
    exact (div_ne_zero hΛ hΓnz) hdiv0

/-- Nonvanishing of the archimedean factor `Γ_ℝ` on `Ω`. -/
lemma Gammaℝ_ne_zero_on_Ω : ∀ z ∈ Ω, Gammaℝ z ≠ 0 := by
  intro z hzΩ
  have hhalf : (1 / 2 : ℝ) < z.re := by
    simpa [Ω, Set.mem_setOf_eq] using hzΩ
  have hpos : (0 : ℝ) < z.re := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hhalf
  exact Gammaℝ_ne_zero_of_re_pos hpos

/-- Factorization of the completed zeta factor on `Ω`: `Λ = Γ_ℝ · ζ`. -/
lemma completedRiemannZeta_eq_Gammaℝ_mul_riemannZeta_on_Ω :
    ∀ z ∈ Ω, completedRiemannZeta z = Gammaℝ z * riemannZeta z := by
  intro z hzΩ
  have hhalf : (1 / 2 : ℝ) < z.re := by
    simpa [Ω, Set.mem_setOf_eq] using hzΩ
  have hpos : (0 : ℝ) < z.re := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hhalf
  have hΓnz : Gammaℝ z ≠ 0 := Gammaℝ_ne_zero_of_re_pos hpos
  have hζ : riemannZeta z = completedRiemannZeta z / Gammaℝ z := by
    refine riemannZeta_def_of_ne_zero (s := z) ?_
    intro h0
    have : (0 : ℝ) < z.re := hpos
    simp [h0, Complex.zero_re] at this
  have : riemannZeta z * Gammaℝ z = completedRiemannZeta z := by
    calc
      riemannZeta z * Gammaℝ z
          = (completedRiemannZeta z / Gammaℝ z) * Gammaℝ z := by
            simp [hζ]
      _ = completedRiemannZeta z := div_mul_cancel₀ _ hΓnz
  simpa [mul_comm] using this.symm

/-- Measurability of `completedRiemannZeta` on all of `ℂ`. -/
lemma measurable_completedRiemannZeta : Measurable completedRiemannZeta := by
  classical
  let S : Set ℂ := ({0, 1} : Set ℂ)
  let Scompl : Set ℂ := {z : ℂ | z ∉ S}
  have hFinite : S.Finite := by
    simp [S]
  have hRestr : Measurable (Scompl.restrict completedRiemannZeta) := by
    have hCont : Continuous fun z : Scompl => completedRiemannZeta z := by
      refine continuous_iff_continuousAt.mpr ?_
      intro z
      have hzNot : (z : ℂ) ∉ S := by
        have := z.property
        dsimp [Scompl] at this
        exact this
      have hzMem :
          (z : ℂ) ≠ 0 ∧ (z : ℂ) ≠ 1 := by
        simpa [S, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hzNot
      have hDiff : DifferentiableAt ℂ completedRiemannZeta (z : ℂ) :=
        differentiableAt_completedRiemannZeta_of_ne (s := (z : ℂ)) hzMem.1 hzMem.2
      exact hDiff.continuousAt.comp continuous_subtype_val.continuousAt
    simpa using hCont.measurable
  have hCompl : Scompl = Sᶜ := by
    ext z; simp [Scompl, S]
  simpa [hCompl] using measurable_of_measurable_on_compl_finite S hFinite hRestr

/-- Continuity of `completedRiemannZeta` away from its two poles `0` and `1`. -/
lemma continuousOn_completedRiemannZeta_compl_zero_one :
    ContinuousOn completedRiemannZeta (({0} : Set ℂ)ᶜ ∩ ({1} : Set ℂ)ᶜ) := by
  intro z hz
  have hz0 : z ≠ 0 := by
    have : z ∉ ({0} : Set ℂ) := hz.1
    simpa [Set.mem_singleton_iff] using this
  have hz1 : z ≠ 1 := by
    have : z ∉ ({1} : Set ℂ) := hz.2
    simpa [Set.mem_singleton_iff] using this
  exact ContinuousAt.continuousWithinAt
    (differentiableAt_completedRiemannZeta_of_ne (s := z) hz0 hz1).continuousAt

end Complex
