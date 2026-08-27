/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smooth inversion of fibrewise-invertible bundle morphisms

If a `C^n` family of continuous linear maps between the fibres of two vector bundles is
invertible at a point, the family of pointwise inverses is `C^n` at that point; if it is
invertible everywhere, the inverse family is globally `C^n`.

This is the bundle-level packaging of `ContMDiffAt.clm_inverse`: in the trivialization
coordinates provided by `contMDiffAt_hom_bundle`, the family reads as a smooth map into
`F₁ →L[𝕜] F₂` that is invertible at the base point, so its pointwise `Ring.inverse` is
smooth there. The coordinate representative of the inverse family agrees with that
pointwise inverse near the base point because `ContinuousLinearMap.inverse` intertwines
composition with the (invertible) trivialization legs unconditionally.

The pointwise versions only assume invertibility **at the base point**: smoothness is local,
and invertibility of the coordinate representative propagates to a neighbourhood through
`Ring.inverse` without being assumed.

As a corollary, a `C^n` (resp. differentiable) section of `Hom(E₁, E₂)` that is fibrewise a
continuous linear equivalence has a `C^n` (resp. differentiable) inverse section.

## Main declarations

* `ContinuousLinearMap.inCoordinates_inverse`
* `ContMDiffWithinAt.clm_bundle_inverse` (with `ContMDiffAt`, `ContMDiffOn`, `ContMDiff` versions)
* `ContMDiffAt.clm_bundle_symm`, `MDifferentiableAt.clm_bundle_symm`

## Tags

vector bundle, continuous linear equivalence, inverse, smoothness
-/

@[expose] public section

noncomputable section

open Bundle Set ContinuousLinearMap
open scoped Manifold Topology

variable {𝕜 B F₁ F₂ M : Type*} {n : WithTop ℕ∞}
  {E₁ : B → Type*} {E₂ : B → Type*} [NontriviallyNormedField 𝕜]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)] [∀ x, AddCommGroup (E₂ x)]
  [∀ x, Module 𝕜 (E₂ x)] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  [TopologicalSpace B] [ChartedSpace HB B]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM}
  [TopologicalSpace M] [ChartedSpace HM M]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]

omit [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)] in
/-- `ContinuousLinearMap.inverse` intertwines `ContinuousLinearMap.inCoordinates` in the
two directions, unconditionally: on the base sets of the reference trivializations the
coordinate legs are invertible, and `inverse` reverses compositions with invertible
maps whether or not the middle map is invertible. -/
theorem ContinuousLinearMap.inCoordinates_inverse {b₀ x : B} (φ : E₁ x →L[𝕜] E₂ x)
    (h₁ : x ∈ (trivializationAt F₁ E₁ b₀).baseSet)
    (h₂ : x ∈ (trivializationAt F₂ E₂ b₀).baseSet) :
    inCoordinates F₂ E₂ F₁ E₁ b₀ x b₀ x (inverse φ) =
      inverse (inCoordinates F₁ E₁ F₂ E₂ b₀ x b₀ x φ) := by
  rw [ContinuousLinearMap.inCoordinates_eq h₂ h₁, ContinuousLinearMap.inCoordinates_eq h₁ h₂,
    inverse_equiv_comp, inverse_comp_equiv, ContinuousLinearEquiv.symm_symm,
    ContinuousLinearMap.comp_assoc]

/-- Pointwise inversion of a smooth fibrewise family of continuous linear maps is
smooth at a point of invertibility. Only invertibility at the base point is assumed;
the trivialized family is then invertible near it, and its pointwise
`ContinuousLinearMap.inverse` is the coordinate representative of the inverse family. -/
theorem ContMDiffWithinAt.clm_bundle_inverse [CompleteSpace F₁]
    {b : M → B} {φ : ∀ x, E₁ (b x) →L[𝕜] E₂ (b x)} {s : Set M} {x₀ : M}
    (hφ : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (E := fun y ↦ E₁ y →L[𝕜] E₂ y) (F₁ →L[𝕜] F₂) (b x) (φ x))
      s x₀)
    (hinv : (φ x₀).IsInvertible) :
    ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₁)) n
      (fun x ↦ TotalSpace.mk' (E := fun y ↦ E₂ y →L[𝕜] E₁ y) (F₂ →L[𝕜] F₁) (b x)
        (inverse (φ x))) s x₀ := by
  obtain ⟨hb, hrep⟩ := (contMDiffWithinAt_hom_bundle _).mp hφ
  have hb₁ : b x₀ ∈ (trivializationAt F₁ E₁ (b x₀)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' (b x₀)
  have hb₂ : b x₀ ∈ (trivializationAt F₂ E₂ (b x₀)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' (b x₀)
  have hρ₀ :
      (inCoordinates F₁ E₁ F₂ E₂ (b x₀) (b x₀) (b x₀) (b x₀) (φ x₀)).IsInvertible := by
    rw [ContinuousLinearMap.inCoordinates_eq hb₁ hb₂]
    simpa using hinv
  refine (contMDiffWithinAt_hom_bundle _).mpr ⟨hb, ?_⟩
  have hev : ∀ᶠ x in 𝓝[s] x₀,
      b x ∈ (trivializationAt F₁ E₁ (b x₀)).baseSet ∩
        (trivializationAt F₂ E₂ (b x₀)).baseSet :=
    hb.continuousWithinAt.eventually
      (((trivializationAt F₁ E₁ (b x₀)).open_baseSet.inter
        (trivializationAt F₂ E₂ (b x₀)).open_baseSet).eventually_mem ⟨hb₁, hb₂⟩)
  refine (hrep.clm_inverse hρ₀).congr_of_eventuallyEq ?_
    (inCoordinates_inverse (φ x₀) hb₁ hb₂)
  filter_upwards [hev] with x hx
  exact inCoordinates_inverse (φ x) hx.1 hx.2

/-- Pointwise inversion of a `C^n` fibrewise family of continuous linear maps,
invertible at the base point, is `C^n` at that point. -/
theorem ContMDiffAt.clm_bundle_inverse [CompleteSpace F₁]
    {b : M → B} {φ : ∀ x, E₁ (b x) →L[𝕜] E₂ (b x)} {x₀ : M}
    (hφ : ContMDiffAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (E := fun y ↦ E₁ y →L[𝕜] E₂ y) (F₁ →L[𝕜] F₂) (b x) (φ x))
      x₀)
    (hinv : (φ x₀).IsInvertible) :
    ContMDiffAt IM (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₁)) n
      (fun x ↦ TotalSpace.mk' (E := fun y ↦ E₂ y →L[𝕜] E₁ y) (F₂ →L[𝕜] F₁) (b x)
        (inverse (φ x))) x₀ := by
  rw [← contMDiffWithinAt_univ] at hφ ⊢
  exact hφ.clm_bundle_inverse hinv

/-- Pointwise inversion of a `C^n` fibrewise family of continuous linear maps,
invertible on a set, is `C^n` on that set. -/
theorem ContMDiffOn.clm_bundle_inverse [CompleteSpace F₁]
    {b : M → B} {φ : ∀ x, E₁ (b x) →L[𝕜] E₂ (b x)} {s : Set M}
    (hφ : ContMDiffOn IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (E := fun y ↦ E₁ y →L[𝕜] E₂ y) (F₁ →L[𝕜] F₂) (b x) (φ x)) s)
    (hinv : ∀ x ∈ s, (φ x).IsInvertible) :
    ContMDiffOn IM (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₁)) n
      (fun x ↦ TotalSpace.mk' (E := fun y ↦ E₂ y →L[𝕜] E₁ y) (F₂ →L[𝕜] F₁) (b x)
        (inverse (φ x))) s :=
  fun x hx ↦ (hφ x hx).clm_bundle_inverse (hinv x hx)

/-- Pointwise inversion of a smooth everywhere-invertible fibrewise family of
continuous linear maps is smooth. -/
theorem ContMDiff.clm_bundle_inverse [CompleteSpace F₁]
    {b : M → B} {φ : ∀ x, E₁ (b x) →L[𝕜] E₂ (b x)}
    (hφ : ContMDiff IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (E := fun y ↦ E₁ y →L[𝕜] E₂ y) (F₁ →L[𝕜] F₂) (b x) (φ x)))
    (hinv : ∀ x, (φ x).IsInvertible) :
    ContMDiff IM (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₁)) n
      (fun x ↦ TotalSpace.mk' (E := fun y ↦ E₂ y →L[𝕜] E₁ y) (F₂ →L[𝕜] F₁) (b x)
        (inverse (φ x))) :=
  fun x ↦ (hφ x).clm_bundle_inverse (hinv x)

/-- A `C^n` bundle map that is fibrewise a continuous linear equivalence has a `C^n` inverse. -/
theorem ContMDiffAt.clm_bundle_symm [CompleteSpace F₁] (φ : ∀ x : B, E₁ x ≃L[𝕜] E₂ x) {x₀ : B}
    (hφ : ContMDiffAt IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun y ↦ E₁ y →L[𝕜] E₂ y) x (φ x)) x₀) :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₁)) n
      (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁) (E := fun y ↦ E₂ y →L[𝕜] E₁ y) x (φ x).symm) x₀ := by
  simpa [inverse_equiv] using
    hφ.clm_bundle_inverse (b := id) (isInvertible_equiv (f := φ x₀))

/-- A `C^n` bundle map that is fibrewise a continuous linear equivalence has a `C^n` inverse. -/
theorem ContMDiff.clm_bundle_symm [CompleteSpace F₁] (φ : ∀ x : B, E₁ x ≃L[𝕜] E₂ x)
    (hφ : ContMDiff IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun y ↦ E₁ y →L[𝕜] E₂ y) x (φ x))) :
    ContMDiff IB (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₁)) n
      (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁) (E := fun y ↦ E₂ y →L[𝕜] E₁ y) x (φ x).symm) :=
  fun x ↦ ContMDiffAt.clm_bundle_symm φ (hφ x)

/-- Differentiable version of `ContMDiffWithinAt.clm_inverse`, for use in bundle inversion. -/
theorem MDifferentiableWithinAt.clm_inverse [CompleteSpace F₁] {A : M → F₁ →L[𝕜] F₂}
    {s : Set M} {x₀ : M}
    (hA : MDifferentiableWithinAt IM 𝓘(𝕜, F₁ →L[𝕜] F₂) A s x₀) (hinv : (A x₀).IsInvertible) :
    MDifferentiableWithinAt IM 𝓘(𝕜, F₂ →L[𝕜] F₁) (fun x ↦ inverse (A x)) s x₀ :=
  ((hinv.contDiffAt_map_inverse (n := 1)).differentiableAt one_ne_zero).comp_mdifferentiableWithinAt
    hA

/-- Pointwise inversion of a differentiable fibrewise family of continuous linear maps is
differentiable at a point of invertibility. -/
theorem MDifferentiableWithinAt.clm_bundle_inverse [CompleteSpace F₁]
    {b : M → B} {φ : ∀ x, E₁ (b x) →L[𝕜] E₂ (b x)} {s : Set M} {x₀ : M}
    (hφ : MDifferentiableWithinAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun x ↦ TotalSpace.mk' (E := fun y ↦ E₁ y →L[𝕜] E₂ y) (F₁ →L[𝕜] F₂) (b x) (φ x))
      s x₀)
    (hinv : (φ x₀).IsInvertible) :
    MDifferentiableWithinAt IM (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₁))
      (fun x ↦ TotalSpace.mk' (E := fun y ↦ E₂ y →L[𝕜] E₁ y) (F₂ →L[𝕜] F₁) (b x)
        (inverse (φ x))) s x₀ := by
  obtain ⟨hb, hrep⟩ := (mdifferentiableWithinAt_hom_bundle _).mp hφ
  have hb₁ : b x₀ ∈ (trivializationAt F₁ E₁ (b x₀)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' (b x₀)
  have hb₂ : b x₀ ∈ (trivializationAt F₂ E₂ (b x₀)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' (b x₀)
  have hρ₀ :
      (inCoordinates F₁ E₁ F₂ E₂ (b x₀) (b x₀) (b x₀) (b x₀) (φ x₀)).IsInvertible := by
    rw [ContinuousLinearMap.inCoordinates_eq hb₁ hb₂]
    simpa using hinv
  refine (mdifferentiableWithinAt_hom_bundle _).mpr ⟨hb, ?_⟩
  have hev : ∀ᶠ x in 𝓝[s] x₀,
      b x ∈ (trivializationAt F₁ E₁ (b x₀)).baseSet ∩
        (trivializationAt F₂ E₂ (b x₀)).baseSet :=
    hb.continuousWithinAt.eventually
      (((trivializationAt F₁ E₁ (b x₀)).open_baseSet.inter
        (trivializationAt F₂ E₂ (b x₀)).open_baseSet).eventually_mem ⟨hb₁, hb₂⟩)
  refine (hrep.clm_inverse hρ₀).congr_of_eventuallyEq ?_
    (inCoordinates_inverse (φ x₀) hb₁ hb₂)
  filter_upwards [hev] with x hx
  exact inCoordinates_inverse (φ x) hx.1 hx.2

/-- A differentiable bundle map that is fibrewise a continuous linear equivalence has a
differentiable inverse. -/
theorem MDifferentiableAt.clm_bundle_symm [CompleteSpace F₁] (φ : ∀ x : B, E₁ x ≃L[𝕜] E₂ x)
    {x₀ : B}
    (hφ : MDifferentiableAt IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun y ↦ E₁ y →L[𝕜] E₂ y) x (φ x)) x₀) :
    MDifferentiableAt IB (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₁))
      (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁) (E := fun y ↦ E₂ y →L[𝕜] E₁ y) x (φ x).symm) x₀ := by
  rw [← mdifferentiableWithinAt_univ] at hφ ⊢
  simpa [inverse_equiv] using
    hφ.clm_bundle_inverse (b := id) (isInvertible_equiv (f := φ x₀))

/-- A differentiable bundle map that is fibrewise a continuous linear equivalence has a
differentiable inverse. -/
theorem MDifferentiable.clm_bundle_symm [CompleteSpace F₁] (φ : ∀ x : B, E₁ x ≃L[𝕜] E₂ x)
    (hφ : MDifferentiable IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun y ↦ E₁ y →L[𝕜] E₂ y) x (φ x))) :
    MDifferentiable IB (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₁))
      (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁) (E := fun y ↦ E₂ y →L[𝕜] E₁ y) x (φ x).symm) :=
  fun x ↦ MDifferentiableAt.clm_bundle_symm φ (hφ x)
