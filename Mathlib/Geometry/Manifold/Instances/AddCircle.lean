/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Manifold structure on the additive circle

This file endows `UnitAddCircle = ℝ ⧸ ℤ` with the analytic manifold structure transported from
the complex unit circle along `AddCircle.homeomorphCircle`.
-/

public noncomputable section

open scoped ContDiff Manifold

namespace UnitAddCircle

/-- The standard homeomorphism from `ℝ ⧸ ℤ` to the complex unit circle. -/
@[expose]
def homeomorphCircle : UnitAddCircle ≃ₜ Circle :=
  AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero

/-- The additive circle `ℝ ⧸ ℤ` is charted through its homeomorphism with the complex unit
circle. -/
instance : ChartedSpace (EuclideanSpace ℝ (Fin 1)) UnitAddCircle :=
  homeomorphCircle.chartedSpace

/-- The additive circle `ℝ ⧸ ℤ` is an analytic manifold. -/
instance : IsManifold (𝓡 1) ω UnitAddCircle :=
  { homeomorphCircle.hasGroupoid_chartedSpace with }

end UnitAddCircle
