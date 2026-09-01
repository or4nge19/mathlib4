/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Smooth inversion of fibrewise-invertible bundle morphisms

If a `C^n` family of continuous linear maps between the fibres of two vector bundles is invertible
at a point, the family of pointwise inverses is `C^n` at that point; if it is invertible
everywhere, the inverse family is globally `C^n`. The same holds for differentiability.

This is the bundle-level packaging of `ContMDiffWithinAt.clm_inverse`: in the trivialization
coordinates provided by `contMDiffWithinAt_hom_bundle`, the family reads as a smooth map into
`F₁ →L[𝕜] F₂` that is invertible at the base point, so its pointwise inverse is smooth there. The
coordinate representative of the inverse family agrees with that pointwise inverse near the base
point by `ContinuousLinearMap.inCoordinates_inverse`.

The pointwise versions only assume invertibility **at the base point**: smoothness is local, and
invertibility of the coordinate representative propagates to a neighbourhood on its own.

## Main results

* `ContMDiffWithinAt.clm_bundle_inverse`, with `ContMDiffAt`, `ContMDiffOn`, `ContMDiff` and
  `MDifferentiable*` versions
* `ContMDiffWithinAt.clm_bundle_symm`: a bundle map that is fibrewise a continuous linear
  equivalence has an inverse of the same regularity

## Tags

vector bundle, continuous linear equivalence, inverse, smoothness
-/

public section

open Bundle Set ContinuousLinearMap Filter
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
  {b : M → B} {φ : ∀ x, E₁ (b x) →L[𝕜] E₂ (b x)} {s : Set M} {x₀ : M}

section Coordinates

omit [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]

/-- The coordinate representative of a fibrewise map at the reference point is invertible when the
map is. -/
private lemma isInvertible_inCoordinates {b₀ : B} {ψ : E₁ b₀ →L[𝕜] E₂ b₀} (hinv : ψ.IsInvertible) :
    (inCoordinates F₁ E₁ F₂ E₂ b₀ b₀ b₀ b₀ ψ).IsInvertible := by
  rw [ContinuousLinearMap.inCoordinates_eq (FiberBundle.mem_baseSet_trivializationAt' b₀)
    (FiberBundle.mem_baseSet_trivializationAt' b₀)]
  simpa using hinv

/-- Near the base point, inverting the coordinate representative computes the coordinate
representative of the pointwise inverse. This is the single geometric input shared by the `C^n`
and the differentiable statements below. -/
private lemma inverse_inCoordinates_eventuallyEq (φ : ∀ x, E₁ (b x) →L[𝕜] E₂ (b x))
    (hb : ContinuousWithinAt b s x₀) :
    (fun x ↦ inCoordinates F₂ E₂ F₁ E₁ (b x₀) (b x) (b x₀) (b x) (inverse (φ x))) =ᶠ[𝓝[s] x₀]
      fun x ↦ inverse (inCoordinates F₁ E₁ F₂ E₂ (b x₀) (b x) (b x₀) (b x) (φ x)) := by
  filter_upwards [hb.eventually
    (((trivializationAt F₁ E₁ (b x₀)).open_baseSet.inter
      (trivializationAt F₂ E₂ (b x₀)).open_baseSet).eventually_mem
        ⟨FiberBundle.mem_baseSet_trivializationAt' _,
          FiberBundle.mem_baseSet_trivializationAt' _⟩)] with x hx
  exact inCoordinates_inverse (φ x) hx.1 hx.2

end Coordinates

/-! ### `C^n` inversion -/

/-- Pointwise inversion of a `C^n` fibrewise family of continuous linear maps is `C^n` within a
set, at a point where the family is invertible. -/
theorem ContMDiffWithinAt.clm_bundle_inverse [CompleteSpace F₁]
    (hφ : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (E := fun y ↦ E₁ y →L[𝕜] E₂ y) (F₁ →L[𝕜] F₂) (b x) (φ x)) s x₀)
    (hinv : (φ x₀).IsInvertible) :
    ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₁)) n
      (fun x ↦ TotalSpace.mk' (E := fun y ↦ E₂ y →L[𝕜] E₁ y) (F₂ →L[𝕜] F₁) (b x)
        (inverse (φ x))) s x₀ := by
  obtain ⟨hb, hrep⟩ := (contMDiffWithinAt_hom_bundle _).mp hφ
  refine (contMDiffWithinAt_hom_bundle _).mpr ⟨hb, ?_⟩
  exact (hrep.clm_inverse (isInvertible_inCoordinates hinv)).congr_of_eventuallyEq
    (inverse_inCoordinates_eventuallyEq φ hb.continuousWithinAt)
    (inCoordinates_inverse (φ x₀) (FiberBundle.mem_baseSet_trivializationAt' _)
      (FiberBundle.mem_baseSet_trivializationAt' _))

/-- Pointwise inversion of a `C^n` fibrewise family of continuous linear maps, invertible at the
base point, is `C^n` at that point. -/
theorem ContMDiffAt.clm_bundle_inverse [CompleteSpace F₁]
    (hφ : ContMDiffAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (E := fun y ↦ E₁ y →L[𝕜] E₂ y) (F₁ →L[𝕜] F₂) (b x) (φ x)) x₀)
    (hinv : (φ x₀).IsInvertible) :
    ContMDiffAt IM (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₁)) n
      (fun x ↦ TotalSpace.mk' (E := fun y ↦ E₂ y →L[𝕜] E₁ y) (F₂ →L[𝕜] F₁) (b x)
        (inverse (φ x))) x₀ := by
  rw [← contMDiffWithinAt_univ] at hφ ⊢
  exact hφ.clm_bundle_inverse hinv

/-- Pointwise inversion of a `C^n` fibrewise family of continuous linear maps, invertible on a set,
is `C^n` on that set. -/
theorem ContMDiffOn.clm_bundle_inverse [CompleteSpace F₁]
    (hφ : ContMDiffOn IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (E := fun y ↦ E₁ y →L[𝕜] E₂ y) (F₁ →L[𝕜] F₂) (b x) (φ x)) s)
    (hinv : ∀ x ∈ s, (φ x).IsInvertible) :
    ContMDiffOn IM (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₁)) n
      (fun x ↦ TotalSpace.mk' (E := fun y ↦ E₂ y →L[𝕜] E₁ y) (F₂ →L[𝕜] F₁) (b x)
        (inverse (φ x))) s :=
  fun x hx ↦ (hφ x hx).clm_bundle_inverse (hinv x hx)

/-- Pointwise inversion of a `C^n` everywhere-invertible fibrewise family of continuous linear maps
is `C^n`. -/
theorem ContMDiff.clm_bundle_inverse [CompleteSpace F₁]
    (hφ : ContMDiff IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (E := fun y ↦ E₁ y →L[𝕜] E₂ y) (F₁ →L[𝕜] F₂) (b x) (φ x)))
    (hinv : ∀ x, (φ x).IsInvertible) :
    ContMDiff IM (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₁)) n
      (fun x ↦ TotalSpace.mk' (E := fun y ↦ E₂ y →L[𝕜] E₁ y) (F₂ →L[𝕜] F₁) (b x)
        (inverse (φ x))) :=
  fun x ↦ (hφ x).clm_bundle_inverse (hinv x)

/-! ### Differentiable inversion -/

/-- Pointwise inversion of a differentiable fibrewise family of continuous linear maps is
differentiable within a set, at a point where the family is invertible. -/
theorem MDifferentiableWithinAt.clm_bundle_inverse [CompleteSpace F₁]
    (hφ : MDifferentiableWithinAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun x ↦ TotalSpace.mk' (E := fun y ↦ E₁ y →L[𝕜] E₂ y) (F₁ →L[𝕜] F₂) (b x) (φ x)) s x₀)
    (hinv : (φ x₀).IsInvertible) :
    MDifferentiableWithinAt IM (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₁))
      (fun x ↦ TotalSpace.mk' (E := fun y ↦ E₂ y →L[𝕜] E₁ y) (F₂ →L[𝕜] F₁) (b x)
        (inverse (φ x))) s x₀ := by
  obtain ⟨hb, hrep⟩ := (mdifferentiableWithinAt_hom_bundle _).mp hφ
  refine (mdifferentiableWithinAt_hom_bundle _).mpr ⟨hb, ?_⟩
  exact (hrep.clm_inverse (isInvertible_inCoordinates hinv)).congr_of_eventuallyEq
    (inverse_inCoordinates_eventuallyEq φ hb.continuousWithinAt)
    (inCoordinates_inverse (φ x₀) (FiberBundle.mem_baseSet_trivializationAt' _)
      (FiberBundle.mem_baseSet_trivializationAt' _))

/-- Pointwise inversion of a differentiable fibrewise family of continuous linear maps, invertible
at the base point, is differentiable at that point. -/
theorem MDifferentiableAt.clm_bundle_inverse [CompleteSpace F₁]
    (hφ : MDifferentiableAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun x ↦ TotalSpace.mk' (E := fun y ↦ E₁ y →L[𝕜] E₂ y) (F₁ →L[𝕜] F₂) (b x) (φ x)) x₀)
    (hinv : (φ x₀).IsInvertible) :
    MDifferentiableAt IM (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₁))
      (fun x ↦ TotalSpace.mk' (E := fun y ↦ E₂ y →L[𝕜] E₁ y) (F₂ →L[𝕜] F₁) (b x)
        (inverse (φ x))) x₀ := by
  rw [← mdifferentiableWithinAt_univ] at hφ ⊢
  exact hφ.clm_bundle_inverse hinv

/-- Pointwise inversion of a differentiable fibrewise family of continuous linear maps, invertible
on a set, is differentiable on that set. -/
theorem MDifferentiableOn.clm_bundle_inverse [CompleteSpace F₁]
    (hφ : MDifferentiableOn IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun x ↦ TotalSpace.mk' (E := fun y ↦ E₁ y →L[𝕜] E₂ y) (F₁ →L[𝕜] F₂) (b x) (φ x)) s)
    (hinv : ∀ x ∈ s, (φ x).IsInvertible) :
    MDifferentiableOn IM (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₁))
      (fun x ↦ TotalSpace.mk' (E := fun y ↦ E₂ y →L[𝕜] E₁ y) (F₂ →L[𝕜] F₁) (b x)
        (inverse (φ x))) s :=
  fun x hx ↦ (hφ x hx).clm_bundle_inverse (hinv x hx)

/-- Pointwise inversion of a differentiable everywhere-invertible fibrewise family of continuous
linear maps is differentiable. -/
theorem MDifferentiable.clm_bundle_inverse [CompleteSpace F₁]
    (hφ : MDifferentiable IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun x ↦ TotalSpace.mk' (E := fun y ↦ E₁ y →L[𝕜] E₂ y) (F₁ →L[𝕜] F₂) (b x) (φ x)))
    (hinv : ∀ x, (φ x).IsInvertible) :
    MDifferentiable IM (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₁))
      (fun x ↦ TotalSpace.mk' (E := fun y ↦ E₂ y →L[𝕜] E₁ y) (F₂ →L[𝕜] F₁) (b x)
        (inverse (φ x))) :=
  fun x ↦ (hφ x).clm_bundle_inverse (hinv x)

/-! ### Inversion of a fibrewise linear equivalence -/

variable (ψ : ∀ x : B, E₁ x ≃L[𝕜] E₂ x) {t : Set B} {y₀ : B}

/-- A `C^n` bundle map that is fibrewise a continuous linear equivalence has a `C^n` inverse. -/
theorem ContMDiffWithinAt.clm_bundle_symm [CompleteSpace F₁]
    (hψ : ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun y ↦ E₁ y →L[𝕜] E₂ y) x (ψ x)) t y₀) :
    ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₁)) n
      (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁) (E := fun y ↦ E₂ y →L[𝕜] E₁ y) x (ψ x).symm) t y₀ := by
  simpa [inverse_equiv] using hψ.clm_bundle_inverse (b := id) (isInvertible_equiv (f := ψ y₀))

/-- A `C^n` bundle map that is fibrewise a continuous linear equivalence has a `C^n` inverse. -/
theorem ContMDiffAt.clm_bundle_symm [CompleteSpace F₁]
    (hψ : ContMDiffAt IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun y ↦ E₁ y →L[𝕜] E₂ y) x (ψ x)) y₀) :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₁)) n
      (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁) (E := fun y ↦ E₂ y →L[𝕜] E₁ y) x (ψ x).symm) y₀ := by
  simpa [inverse_equiv] using hψ.clm_bundle_inverse (b := id) (isInvertible_equiv (f := ψ y₀))

/-- A `C^n` bundle map that is fibrewise a continuous linear equivalence has a `C^n` inverse. -/
theorem ContMDiffOn.clm_bundle_symm [CompleteSpace F₁]
    (hψ : ContMDiffOn IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun y ↦ E₁ y →L[𝕜] E₂ y) x (ψ x)) t) :
    ContMDiffOn IB (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₁)) n
      (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁) (E := fun y ↦ E₂ y →L[𝕜] E₁ y) x (ψ x).symm) t :=
  fun y hy ↦ ContMDiffWithinAt.clm_bundle_symm ψ (hψ y hy)

/-- A `C^n` bundle map that is fibrewise a continuous linear equivalence has a `C^n` inverse. -/
theorem ContMDiff.clm_bundle_symm [CompleteSpace F₁]
    (hψ : ContMDiff IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun y ↦ E₁ y →L[𝕜] E₂ y) x (ψ x))) :
    ContMDiff IB (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₁)) n
      (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁) (E := fun y ↦ E₂ y →L[𝕜] E₁ y) x (ψ x).symm) :=
  fun y ↦ ContMDiffAt.clm_bundle_symm ψ (hψ y)

/-- A differentiable bundle map that is fibrewise a continuous linear equivalence has a
differentiable inverse. -/
theorem MDifferentiableAt.clm_bundle_symm [CompleteSpace F₁]
    (hψ : MDifferentiableAt IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun y ↦ E₁ y →L[𝕜] E₂ y) x (ψ x)) y₀) :
    MDifferentiableAt IB (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₁))
      (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁) (E := fun y ↦ E₂ y →L[𝕜] E₁ y) x (ψ x).symm) y₀ := by
  simpa [inverse_equiv] using hψ.clm_bundle_inverse (b := id) (isInvertible_equiv (f := ψ y₀))

/-- A differentiable bundle map that is fibrewise a continuous linear equivalence has a
differentiable inverse. -/
theorem MDifferentiable.clm_bundle_symm [CompleteSpace F₁]
    (hψ : MDifferentiable IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun y ↦ E₁ y →L[𝕜] E₂ y) x (ψ x))) :
    MDifferentiable IB (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₁))
      (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₁) (E := fun y ↦ E₂ y →L[𝕜] E₁ y) x (ψ x).symm) :=
  fun y ↦ MDifferentiableAt.clm_bundle_symm ψ (hψ y)
