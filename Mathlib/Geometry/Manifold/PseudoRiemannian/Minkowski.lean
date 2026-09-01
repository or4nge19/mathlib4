/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Geometry.Manifold.PseudoRiemannian.Lorentzian

/-!
# Vector spaces as pseudo-Riemannian manifolds, and Minkowski spacetime

A vector space carrying a pseudo-inner product is a pseudo-Riemannian manifold over itself, with
the constant metric `Bundle.pseudoRiemannianMetricVectorSpace`. Its index at every point is the
index of the form, so it is Lorentzian exactly when that index is `1`.

Applied to `PseudoInnerProductSpace.prodDiff F ℝ` — the form `⟪x, x'⟫ - t t'` on `F × ℝ` — this
produces **Minkowski spacetime** over an arbitrary Euclidean space part `F`, in the
`(-, +, …, +)` convention. Taking `F := EuclideanSpace ℝ (Fin 3)` gives the physical case.

These are the witnesses that make `PseudoRiemannian.IsLorentzian` non-vacuous.

## Main results

* `PseudoRiemannian.index_vectorSpace`: the index of the constant metric is the index of the form
* `PseudoRiemannian.isLorentzian_vectorSpace`: index `1` makes the vector space Lorentzian
* `PseudoRiemannian.isLorentzian_prodDiff`: Minkowski spacetime `F × ℝ` is Lorentzian

## Tags

Minkowski, Lorentzian, pseudo-Riemannian, spacetime, signature
-/

@[expose] public section

open Bundle PseudoInnerProductSpace
open scoped Manifold Bundle ContDiff

namespace PseudoRiemannian

section VectorSpace

variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [PseudoInnerProductSpace ℝ V]

/-- The fibrewise structure induced on the tangent spaces of `V` by the constant metric. -/
noncomputable abbrev tangentPseudoInnerProductSpace :
    ∀ x : V, PseudoInnerProductSpace ℝ (TangentSpace 𝓘(ℝ, V) x) :=
  (pseudoRiemannianMetricVectorSpace V).toPseudoInnerProductSpace

attribute [local instance] tangentPseudoInnerProductSpace

/-- The tangent spaces of `V` carry exactly the form of `V`, so the index of the constant metric is
the index of the form. -/
lemma index_vectorSpace (x : V) : index 𝓘(ℝ, V) x = PseudoInnerProductSpace.index V := rfl

/-- **A vector space whose pseudo-inner product has index one is a Lorentzian manifold.** -/
lemma isLorentzian_vectorSpace (h : PseudoInnerProductSpace.index V = 1) :
    IsLorentzian 𝓘(ℝ, V) V :=
  ⟨fun x ↦ (index_vectorSpace V x).trans h⟩

end VectorSpace

section Minkowski

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

attribute [local instance] PseudoInnerProductSpace.prodDiff tangentPseudoInnerProductSpace

/-- **Minkowski spacetime is a Lorentzian manifold.**

The underlying vector space is `F × ℝ` with the form `⟪x, x'⟫ - t t'`, whose index is
`Module.finrank ℝ ℝ = 1` by `PseudoInnerProductSpace.index_prodDiff`. Taking
`F := EuclideanSpace ℝ (Fin 3)` gives four-dimensional spacetime. -/
lemma isLorentzian_prodDiff : IsLorentzian 𝓘(ℝ, F × ℝ) (F × ℝ) :=
  isLorentzian_vectorSpace (F × ℝ) (by rw [index_prodDiff]; simp)

end Minkowski

end PseudoRiemannian
