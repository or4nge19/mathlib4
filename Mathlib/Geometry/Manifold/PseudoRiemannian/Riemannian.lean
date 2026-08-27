/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Geometry.Manifold.PseudoRiemannian.Basic

/-!
# Riemannian manifolds as the index-zero pseudo-Riemannian manifolds

Mathlib's Riemannian hypotheses already discharge the pseudo-Riemannian ones. This file records
the invariant separating the two cases: a Riemannian metric has index `0`.

We do not introduce a class `IsRiemannian`, which would clash with Mathlib's
`IsRiemannianManifold`.
-/

@[expose] public section

open Bundle
open scoped Manifold Bundle ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

namespace PseudoRiemannian

variable [IsManifold I 1 M] [RiemannianBundle (TangentSpace I : M → Type _)]

/-- Transparency check: a Riemannian manifold satisfies the pseudo-Riemannian hypotheses with no
adapter. -/
example [IsContMDiffRiemannianBundle I n E (TangentSpace I : M → Type _)] :
    IsContMDiffPseudoRiemannianBundle I n E (TangentSpace I : M → Type _) := inferInstance

omit [IsManifold I 1 M] in
/-- A Riemannian metric has index `0` at every point. -/
@[simp]
lemma index_eq_zero_of_riemannianBundle [FiniteDimensional ℝ E] (x : M) : index I x = 0 :=
  PseudoInnerProductSpace.index_eq_zero_of_innerProductSpace (TangentSpace I x)

end PseudoRiemannian
