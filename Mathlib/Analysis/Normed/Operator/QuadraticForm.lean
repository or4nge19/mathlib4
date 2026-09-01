/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Signature of a continuous bilinear form, and its stability

The quadratic form `v ↦ b v v` of a continuous bilinear map `b` has a well-defined signature.
This file records that construction, and shows that if the radical is trivial then the signature
cannot jump: nearby forms have the same `sigPos` and `sigNeg`. No symmetry of `b` is used, since
`sigPos`, `sigNeg` and `radical` see only the quadratic part.

This is the analytic input to local constancy of the index of a pseudo-Riemannian metric.

## Main definitions

* `ContinuousLinearMap.toQuadraticForm`

## Main results

* `ContinuousLinearMap.eventually_restrict_posDef`, `eventually_restrict_negDef`: definiteness on a
  fixed subspace is an open condition on the form
* `ContinuousLinearMap.eventually_radical_eq_bot`, `eventually_sigPos_eq`, `eventually_sigNeg_eq`:
  nondegeneracy and both inertia indices are locally constant
* `ContinuousLinearMap.sigNeg_toQuadraticForm_of_congr`: transport along a linear equivalence

## Tags

signature, index, inertia, Sylvester, nondegenerate, locally constant
-/

@[expose] public section

open Filter Module Metric Set QuadraticMap
open scoped Topology

namespace ContinuousLinearMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- The quadratic form `v ↦ b v v` of a continuous bilinear map. No symmetry is required: the
companion is `(v, w) ↦ b v w + b w v`. -/
noncomputable def toQuadraticForm (b : E →L[ℝ] E →L[ℝ] ℝ) : QuadraticForm ℝ E :=
  b.toBilinForm.toQuadraticMap

@[simp]
lemma toQuadraticForm_apply (b : E →L[ℝ] E →L[ℝ] ℝ) (v : E) : b.toQuadraticForm v = b v v := rfl

@[simp]
lemma toQuadraticForm_neg (b : E →L[ℝ] E →L[ℝ] ℝ) :
    (-b).toQuadraticForm = -b.toQuadraticForm := by
  ext v; simp

section Perturbation

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Positive definiteness on a subspace is quantitative: `ε ‖v‖ ^ 2 ≤ b v v` for some `ε > 0`,
by compactness of the unit sphere and homogeneity. -/
lemma exists_pos_forall_le_of_posDef (b : F →L[ℝ] F →L[ℝ] ℝ) {V : Submodule ℝ F}
    (hV₀ : (b.toQuadraticForm.restrict V).PosDef) :
    ∃ ε > 0, ∀ v : V, ε * ‖(v : F)‖ ^ 2 ≤ b v v := by
  have hV : ∀ v : V, v ≠ 0 → 0 < b (v : F) (v : F) := fun v hv ↦ by simpa using hV₀ v hv
  have hcont : Continuous fun v : V ↦ b (v : F) (v : F) :=
    (b.continuous.comp continuous_subtype_val).clm_apply continuous_subtype_val
  rcases subsingleton_or_nontrivial V with _ | _
  · -- The subspace is trivial: every vector is `0` and both sides vanish.
    refine ⟨1, one_pos, fun v ↦ ?_⟩
    have hv : v = 0 := Subsingleton.elim _ _
    simp [hv]
  · obtain ⟨v₀, hv₀, hmin⟩ :=
      (isCompact_sphere (0 : V) 1).exists_isMinOn
        (NormedSpace.sphere_nonempty.mpr zero_le_one) hcont.continuousOn
    have hv₀norm : ‖v₀‖ = 1 := by simpa using hv₀
    have hv₀ne : v₀ ≠ 0 := by
      intro h; rw [h] at hv₀norm; simp at hv₀norm
    refine ⟨b (v₀ : F) (v₀ : F), hV v₀ hv₀ne, fun v ↦ ?_⟩
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    -- Normalise `v` to the unit sphere and use homogeneity of `v ↦ b v v`.
    have hvn : (0 : ℝ) < ‖(v : F)‖ := by
      simpa using norm_pos_iff.mpr hv
    set u : V := ‖(v : F)‖⁻¹ • v with hu_def
    have hu : u ∈ sphere (0 : V) 1 := by
      simp only [mem_sphere_iff_norm, sub_zero, hu_def, norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ (by simpa using hvn.ne')
    have hbu : b (v₀ : F) (v₀ : F) ≤ b (u : F) (u : F) := hmin hu
    have hcoe : (u : F) = ‖(v : F)‖⁻¹ • (v : F) := rfl
    have hscale : b (u : F) (u : F) = (‖(v : F)‖ ^ 2)⁻¹ * b (v : F) (v : F) := by
      simp only [hcoe, map_smul, smul_apply, smul_eq_mul]
      ring
    rw [hscale] at hbu
    have hpos : (0 : ℝ) < ‖(v : F)‖ ^ 2 := pow_pos hvn 2
    calc b (v₀ : F) (v₀ : F) * ‖(v : F)‖ ^ 2
        ≤ ((‖(v : F)‖ ^ 2)⁻¹ * b (v : F) (v : F)) * ‖(v : F)‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hbu hpos.le
      _ = b (v : F) (v : F) := by field_simp

omit [FiniteDimensional ℝ F] in
/-- If `b ≥ ε ‖·‖ ^ 2` on a subspace and `‖c - b‖ < ε`, then `c` is positive there. -/
private lemma pos_of_norm_sub_lt {b c : F →L[ℝ] F →L[ℝ] ℝ} {V : Submodule ℝ F} {ε : ℝ}
    (hle : ∀ v : V, ε * ‖(v : F)‖ ^ 2 ≤ b v v) (hc : ‖c - b‖ < ε) :
    ∀ v : V, v ≠ 0 → 0 < c (v : F) (v : F) := by
  intro v hv
  have hvn : (0 : ℝ) < ‖(v : F)‖ := by simpa using norm_pos_iff.mpr hv
  have hbound : |c (v : F) (v : F) - b (v : F) (v : F)| ≤ ‖c - b‖ * ‖(v : F)‖ ^ 2 := by
    have h := (c - b).le_opNorm₂ (v : F) (v : F)
    simp only [sub_apply, Real.norm_eq_abs] at h
    calc |c (v : F) (v : F) - b (v : F) (v : F)| ≤ ‖c - b‖ * ‖(v : F)‖ * ‖(v : F)‖ := h
      _ = ‖c - b‖ * ‖(v : F)‖ ^ 2 := by ring
  have hsq : (0 : ℝ) < ‖(v : F)‖ ^ 2 := by positivity
  nlinarith [hle v, (abs_le.mp hbound).1, (abs_le.mp hbound).2]

/-- Positive definiteness on a fixed subspace is an open condition on the bilinear form. -/
lemma eventually_restrict_posDef {b : F →L[ℝ] F →L[ℝ] ℝ} {V : Submodule ℝ F}
    (hV : (b.toQuadraticForm.restrict V).PosDef) :
    ∀ᶠ c in 𝓝 b, (c.toQuadraticForm.restrict V).PosDef := by
  obtain ⟨ε, hε, hle⟩ := exists_pos_forall_le_of_posDef b hV
  filter_upwards [ball_mem_nhds b hε] with c hc v hv
  have h1 : dist c b < ε := Metric.mem_ball.mp hc
  rw [dist_eq_norm c b] at h1
  simpa using pos_of_norm_sub_lt hle h1 v hv

/-- Negative definiteness on a fixed subspace is an open condition on the bilinear form. As in
`QuadraticForm.le_sigNeg_of_negDef`, negative definiteness is spelled as positive definiteness
of `-Q`. -/
lemma eventually_restrict_negDef {b : F →L[ℝ] F →L[ℝ] ℝ} {V : Submodule ℝ F}
    (hV : ((-b.toQuadraticForm).restrict V).PosDef) :
    ∀ᶠ c in 𝓝 b, ((-c.toQuadraticForm).restrict V).PosDef := by
  -- Negation is a homeomorphism, so this is the positive case at `-b`.
  have h := eventually_restrict_posDef (b := -b) (V := V) (by simpa using hV)
  filter_upwards [(continuous_neg.tendsto b).eventually h] with c hc
  simpa using hc

/-! ### Local constancy of the signature -/

variable {b : F →L[ℝ] F →L[ℝ] ℝ}

private lemma sigPos_add_sigNeg_of_radical_eq_bot (hb : b.toQuadraticForm.radical = ⊥) :
    sigPos b.toQuadraticForm + sigNeg b.toQuadraticForm = finrank ℝ F := by
  have h := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := b.toQuadraticForm)
  rwa [hb, finrank_bot, Nat.add_zero] at h

/-- Near a nondegenerate form the radical stays trivial and neither inertia index moves. The three
consequences are exposed separately below. -/
private lemma eventually_radical_and_sig_eq (hb : b.toQuadraticForm.radical = ⊥) :
    ∀ᶠ c in 𝓝 b, c.toQuadraticForm.radical = ⊥ ∧
      sigPos c.toQuadraticForm = sigPos b.toQuadraticForm ∧
      sigNeg c.toQuadraticForm = sigNeg b.toQuadraticForm := by
  classical
  obtain ⟨Vp, hVpdim, hVppos⟩ := exists_finrank_eq_sigPos_and_posDef b.toQuadraticForm
  obtain ⟨Vn, hVndim, hVnneg⟩ := exists_finrank_eq_sigNeg_and_negDef b.toQuadraticForm
  have hsum := sigPos_add_sigNeg_of_radical_eq_bot hb
  filter_upwards [eventually_restrict_posDef hVppos, eventually_restrict_negDef hVnneg]
    with c hcp hcn
  -- Both maximal definite subspaces stay definite, so the two parts of the signature can only grow.
  have hle_pos : sigPos b.toQuadraticForm ≤ sigPos c.toQuadraticForm := by
    rw [← hVpdim]; exact le_sigPos_of_posDef _ hcp
  have hle_neg : sigNeg b.toQuadraticForm ≤ sigNeg c.toQuadraticForm := by
    rw [← hVndim]; exact le_sigNeg_of_negDef _ hcn
  -- Sylvester's law caps the total, so both inequalities are equalities.
  have hc := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := c.toQuadraticForm)
  have hrad : finrank ℝ c.toQuadraticForm.radical = 0 := by lia
  exact ⟨Submodule.finrank_eq_zero.mp hrad, by lia, by lia⟩

/-- **Nondegeneracy is an open condition** on a continuous bilinear form. -/
theorem eventually_radical_eq_bot (hb : b.toQuadraticForm.radical = ⊥) :
    ∀ᶠ c in 𝓝 b, c.toQuadraticForm.radical = ⊥ :=
  (eventually_radical_and_sig_eq hb).mono fun _ h ↦ h.1

/-- **The positive inertia index is locally constant** at a nondegenerate form.

No symmetry is assumed: `sigPos`, `sigNeg` and `radical` see only `v ↦ b v v`, which is unchanged
by symmetrising `b`. -/
theorem eventually_sigPos_eq (hb : b.toQuadraticForm.radical = ⊥) :
    ∀ᶠ c in 𝓝 b, sigPos c.toQuadraticForm = sigPos b.toQuadraticForm :=
  (eventually_radical_and_sig_eq hb).mono fun _ h ↦ h.2.1

/-- **The negative inertia index is locally constant** at a nondegenerate form. -/
theorem eventually_sigNeg_eq (hb : b.toQuadraticForm.radical = ⊥) :
    ∀ᶠ c in 𝓝 b, sigNeg c.toQuadraticForm = sigNeg b.toQuadraticForm :=
  (eventually_radical_and_sig_eq hb).mono fun _ h ↦ h.2.2

/-! ### Transport along a linear equivalence -/

section Congr

variable {X Y : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]

/-- A linear equivalence intertwining two continuous bilinear forms preserves `sigNeg`. Used to
transport a fibrewise computation to the model fibre of a vector bundle. -/
lemma sigNeg_toQuadraticForm_of_congr (b : X →L[ℝ] X →L[ℝ] ℝ) (b' : Y →L[ℝ] Y →L[ℝ] ℝ)
    (φ : X ≃ₗ[ℝ] Y) (h : ∀ u w : X, b' (φ u) (φ w) = b u w) :
    sigNeg b.toQuadraticForm = sigNeg b'.toQuadraticForm :=
  QuadraticMap.Equivalent.sigNeg_eq ⟨{ toLinearEquiv := φ, map_app' := fun m ↦ h m m }⟩

/-- Nondegeneracy is likewise transported along a linear equivalence. -/
lemma radical_toQuadraticForm_eq_bot_of_congr (b : X →L[ℝ] X →L[ℝ] ℝ) (b' : Y →L[ℝ] Y →L[ℝ] ℝ)
    (φ : X ≃ₗ[ℝ] Y) (h : ∀ u w : X, b' (φ u) (φ w) = b u w)
    (hb : b.toQuadraticForm.radical = ⊥) : b'.toQuadraticForm.radical = ⊥ := by
  have hiso : QuadraticMap.IsometryEquiv b.toQuadraticForm b'.toQuadraticForm :=
    { toLinearEquiv := φ, map_app' := fun m ↦ h m m }
  rw [← QuadraticMap.IsometryEquiv.map_radical hiso, hb, Submodule.map_bot]

end Congr

end Perturbation

end ContinuousLinearMap
