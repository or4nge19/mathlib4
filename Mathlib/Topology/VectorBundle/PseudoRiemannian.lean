/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.InnerProductSpace.Pseudo
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.VectorBundle.Constructions
public import Mathlib.Topology.VectorBundle.Hom

/-!
# The index of a pseudo-Riemannian vector bundle

For a vector bundle whose fibres carry a `PseudoInnerProductSpace`, the fibrewise index — the
`sigNeg` of the associated quadratic form — is locally constant as soon as the form depends
continuously on the base point. This is Sylvester's law of inertia fibrewise: the form is
everywhere nondegenerate, so its signature has no room to jump.

No manifold structure and no smoothness are used, only continuity, which is why this lives at the
topological level, next to `Mathlib/Topology/VectorBundle/Riemannian.lean`. The smooth corollary
`Bundle.isLocallyConstant_index` is in
`Mathlib/Geometry/Manifold/VectorBundle/PseudoRiemannian.lean`.

## Main results

* `Bundle.isLocallyConstant_index_of_continuous`

## Tags

vector bundle, pseudo-Riemannian, signature, index, Sylvester
-/

@[expose] public section

open ContinuousLinearMap Filter Module QuadraticMap Set
open scoped Topology

namespace Bundle

/-! ## The index of a pseudo-Riemannian bundle

Local constancy of the index needs no manifold structure and no smoothness: continuity of the
fibrewise form is enough. It is therefore proved here for an arbitrary topological vector bundle,
and specialized to the smooth setting afterwards. -/

section Index

variable
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, PseudoInnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]

omit [∀ x, PseudoInnerProductSpace ℝ (E x)] in
/-- Undoing a trivialization recovers the original vector. -/
private lemma symm_continuousLinearEquivAt_apply {x₀ x : B}
    (hx : x ∈ (trivializationAt F E x₀).baseSet) (u : E x) :
    (trivializationAt F E x₀).symm x
      (((trivializationAt F E x₀).continuousLinearEquivAt ℝ x hx).toLinearEquiv u) = u :=
  ((trivializationAt F E x₀).continuousLinearEquivAt ℝ x hx).symm_apply_apply u

/-- Reading the fibrewise form in a local trivialization does not change its index. -/
private lemma index_eq_sigNeg_trivialization {x₀ x : B}
    (hx : x ∈ (trivializationAt F E x₀).baseSet)
    (g : ∀ y : B, E y →L[ℝ] E y →L[ℝ] ℝ)
    (hg : ∀ (y : B) (v w : E y), inner ℝ v w = g y v w)
    (G : F →L[ℝ] F →L[ℝ] ℝ)
    (hG : ∀ u u' : F, G u u' =
      g x ((trivializationAt F E x₀).symm x u) ((trivializationAt F E x₀).symm x u')) :
    PseudoInnerProductSpace.index (E x) = sigNeg G.toQuadraticForm := by
  have hform : PseudoInnerProductSpace.toQuadraticForm (E x) = (g x).toQuadraticForm := by
    ext v
    simpa using hg x v v
  rw [PseudoInnerProductSpace.index, hform]
  refine ContinuousLinearMap.sigNeg_toQuadraticForm_of_congr (g x) G
    ((trivializationAt F E x₀).continuousLinearEquivAt ℝ x hx).toLinearEquiv (fun u w ↦ ?_)
  rw [hG, symm_continuousLinearEquivAt_apply hx u, symm_continuousLinearEquivAt_apply hx w]

omit [∀ x, PseudoInnerProductSpace ℝ (E x)] in
/-- Reading the trivial line bundle in its (global) trivialization is the identity. -/
private lemma trivial_linearMapAt_apply (x₀ x : B) (r : ℝ) :
    (trivializationAt ℝ (Bundle.Trivial B ℝ) x₀).linearMapAt ℝ x r = r := by
  rw [Trivialization.coe_linearMapAt_of_mem _ (by simp)]
  simp

omit [∀ x, PseudoInnerProductSpace ℝ (E x)] in
/-- The coordinate expression of the fibrewise form in the trivialization of the bundle of
bilinear forms at `x₀` is the transport of the form along the trivialization of `E`. -/
private lemma hom_trivialization_apply {x₀ x : B}
    (hx : x ∈ (trivializationAt F E x₀).baseSet)
    (b : E x →L[ℝ] E x →L[ℝ] ℝ) (u u' : F) :
    ((trivializationAt (F →L[ℝ] F →L[ℝ] ℝ) (fun y : B ↦ E y →L[ℝ] E y →L[ℝ] ℝ) x₀)
        ⟨x, b⟩).2 u u' =
      b ((trivializationAt F E x₀).symm x u) ((trivializationAt F E x₀).symm x u') := by
  have hrfl : ((trivializationAt (F →L[ℝ] F →L[ℝ] ℝ) (fun y : B ↦ E y →L[ℝ] E y →L[ℝ] ℝ) x₀)
      ⟨x, b⟩).2 = inCoordinates F E (F →L[ℝ] ℝ) (fun y : B ↦ E y →L[ℝ] ℝ) x₀ x x₀ x b := rfl
  rw [hrfl, _root_.inCoordinates_apply_eq₂ (F₁ := F) (E₁ := E) (F₂ := F) (E₂ := E) (F₃ := ℝ)
    (E₃ := Bundle.Trivial B ℝ) hx hx (by simp)]
  exact trivial_linearMapAt_apply x₀ x _

variable [FiniteDimensional ℝ F]

/-- **The index is locally constant**, for a merely continuous fibrewise form.

Sylvester's law of inertia fibrewise, transported to the model fibre by a local trivialization:
the form varies continuously and is everywhere nondegenerate, so its signature cannot jump. -/
theorem isLocallyConstant_index_of_continuous (g : ∀ x : B, E x →L[ℝ] E x →L[ℝ] ℝ)
    (hcont : Continuous fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
      (E := fun y : B ↦ E y →L[ℝ] E y →L[ℝ] ℝ) x (g x))
    (hg : ∀ (x : B) (v w : E x), inner ℝ v w = g x v w) :
    IsLocallyConstant (fun x ↦ PseudoInnerProductSpace.index (E x)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x₀
  set eh := trivializationAt (F →L[ℝ] F →L[ℝ] ℝ) (fun y : B ↦ E y →L[ℝ] E y →L[ℝ] ℝ) x₀ with heh
  set Φ : B → (F →L[ℝ] F →L[ℝ] ℝ) := fun x ↦ (eh ⟨x, g x⟩).2 with hΦ
  -- `Φ` is the form read in a local trivialization; it is continuous at `x₀`.
  have hx₀ : x₀ ∈ eh.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  have hcontΦ : ContinuousAt Φ x₀ := by
    have hmaps : MapsTo (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun y : B ↦ E y →L[ℝ] E y →L[ℝ] ℝ) x (g x)) eh.baseSet eh.source :=
      fun x hx ↦ eh.mem_source.mpr hx
    have hcomp : ContinuousOn (fun x ↦ eh ⟨x, g x⟩) eh.baseSet :=
      eh.continuousOn.comp hcont.continuousOn hmaps
    exact (continuous_snd.comp_continuousOn hcomp).continuousAt
      (eh.open_baseSet.mem_nhds hx₀)
  -- On the base set of the trivialization, the index is that of the coordinate form.
  have hbase : ∀ x ∈ eh.baseSet,
      PseudoInnerProductSpace.index (E x) = sigNeg (Φ x).toQuadraticForm := by
    intro x hx
    rw [hom_trivializationAt_baseSet] at hx
    exact index_eq_sigNeg_trivialization hx.1 g hg (Φ x)
      (fun u u' ↦ hom_trivialization_apply hx.1 (g x) u u')
  -- The coordinate form at `x₀` is nondegenerate, so the signature is locally constant there.
  have hrad : (Φ x₀).toQuadraticForm.radical = ⊥ := by
    have hmem := hx₀
    rw [hom_trivializationAt_baseSet] at hmem
    have hform : PseudoInnerProductSpace.toQuadraticForm (E x₀) = (g x₀).toQuadraticForm := by
      ext v; simpa using hg x₀ v v
    refine ContinuousLinearMap.radical_toQuadraticForm_eq_bot_of_congr (g x₀) (Φ x₀)
      ((trivializationAt F E x₀).continuousLinearEquivAt ℝ x₀ hmem.1).toLinearEquiv
      (fun u w ↦ ?_) ?_
    · rw [hom_trivialization_apply hmem.1 (g x₀),
        symm_continuousLinearEquivAt_apply hmem.1 u, symm_continuousLinearEquivAt_apply hmem.1 w]
    · rw [← hform]
      exact PseudoInnerProductSpace.radical_toQuadraticForm_eq_bot (E x₀)
  filter_upwards [eh.open_baseSet.mem_nhds hx₀,
    hcontΦ (ContinuousLinearMap.eventually_sigNeg_eq hrad)] with x hx hsig
  rw [hbase x hx, hbase x₀ hx₀, hsig]

end Index

end Bundle
