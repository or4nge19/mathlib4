/-
Copyright (c) 2025 Michael Rothgang, Pepa Montero, Archibald Browne, Enrique Díaz,
Juan José Madrigal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Pepa Montero, Archibald Browne, Enrique Díaz, Juan José Madrigal
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Topology.Covering.Quotient

/-!
# Quotients of manifolds

This file contains results about quotients of manifolds by group actions.

## Main results

* `MulAction.instChartedSpaceQuotient`: a choice of charted space structure on the quotient of a
  charted space by a free, properly-discontinuous group action.
* `MulAction.isManifoldQuotient_of_chartedSpace_compatible`: a criterion reducing the smooth
  quotient-manifold structure to compatibility of the chart transitions selected by the quotient
  covering map.

## TODO

* prove the chart-transition compatibility criterion from smoothness of the `G`-action.
* if `G` acts smoothly, the projection map is smooth

## tags
smooth manifold, smooth action, quotient manifold
-/

public noncomputable section

open scoped ContDiff Manifold
open OpenPartialHomeomorph

namespace MulAction

variable {M : Type*} [TopologicalSpace M]
  {G : Type*} [Group G] [MulAction G M]
  [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] [IsCancelSMul G M]
  [T2Space M] [LocallyCompactSpace M]
  {H : Type*} [TopologicalSpace H] [ChartedSpace H M]

/-!
## Charted space structure on quotient by a group
-/

/-- The induced charted space structure on the quotient of a charted space by a free, properly
discontinuous group action. -/
@[expose, to_additive]
instance instChartedSpaceQuotient : ChartedSpace H (orbitRel.Quotient G M) :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap
    |>.isLocalHomeomorph.chartedSpace Quotient.mk_surjective

/-- The chart on an action quotient selected by the quotient covering map and the chosen
representative of a quotient point. -/
@[to_additive
/-- The chart on an additive action quotient selected by the quotient covering map and the chosen
representative of a quotient point. -/]
noncomputable def quotientChartAt (q : orbitRel.Quotient G M) :
    OpenPartialHomeomorph (orbitRel.Quotient G M) H :=
  ((isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul (G := G) (E := M))
    |>.isCoveringMap.isLocalHomeomorph.localInverseAt
      (Quotient.mk_surjective.hasRightInverse.choose q)).trans
    (chartAt H (Quotient.mk_surjective.hasRightInverse.choose q))

section IsManifold

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}

/-- A quotient by a free, properly discontinuous action is a manifold once the chart transitions
selected by the quotient covering map lie in the target smooth structure groupoid.

This is the local-homeomorphism part of the quotient-manifold construction. The remaining
geometric step is to prove the compatibility hypothesis from smoothness of the action. -/
@[to_additive
/-- A quotient by a free, properly discontinuous additive action is a manifold once the chart
transitions selected by the quotient covering map lie in the target smooth structure groupoid.

This is the local-homeomorphism part of the quotient-manifold construction. The remaining
geometric step is to prove the compatibility hypothesis from smoothness of the action. -/]
theorem isManifoldQuotient_of_local_chartedSpace_compatible
    (hcompat : ∀ q q' : orbitRel.Quotient G M, ∀ x,
      x ∈ ((quotientChartAt (G := G) (M := M) (H := H) q).symm ≫ₕ
        quotientChartAt (G := G) (M := M) (H := H) q').source →
      ∃ s : Set H, IsOpen s ∧ x ∈ s ∧ ∃ e : OpenPartialHomeomorph H H,
        e ∈ contDiffGroupoid n I ∧
          (((quotientChartAt (G := G) (M := M) (H := H) q).symm ≫ₕ
            quotientChartAt (G := G) (M := M) (H := H) q').restr s) ≈ e) :
    IsManifold I n (orbitRel.Quotient G M) := by
  let qcov : IsQuotientCoveringMap (Quotient.mk (MulAction.orbitRel G M)) G :=
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
  letI : ChartedSpace H (orbitRel.Quotient G M) :=
    qcov.isCoveringMap.isLocalHomeomorph.chartedSpace Quotient.mk_surjective
  have hG : HasGroupoid (orbitRel.Quotient G M) (contDiffGroupoid n I) :=
    qcov.isCoveringMap.isLocalHomeomorph.hasGroupoid_chartedSpace_of_local
      Quotient.mk_surjective <| by
        intro q q' x hx
        simpa [quotientChartAt, qcov] using hcompat q q' x hx
  exact IsManifold.mk' I n (orbitRel.Quotient G M)

/-- A quotient by a free, properly discontinuous action is a manifold once the chart transitions
selected by the quotient covering map lie in the target smooth structure groupoid.

This is a non-local convenience wrapper around
`MulAction.isManifoldQuotient_of_local_chartedSpace_compatible`. -/
@[to_additive
/-- A quotient by a free, properly discontinuous additive action is a manifold once the chart
transitions selected by the quotient covering map lie in the target smooth structure groupoid.

This is a non-local convenience wrapper around
`AddAction.isManifoldQuotient_of_local_chartedSpace_compatible`. -/]
theorem isManifoldQuotient_of_chartedSpace_compatible
    (hcompat : ∀ q q' : orbitRel.Quotient G M,
      (quotientChartAt (G := G) (M := M) (H := H) q).symm.trans
        (quotientChartAt (G := G) (M := M) (H := H) q') ∈ contDiffGroupoid n I) :
    IsManifold I n (orbitRel.Quotient G M) := by
  let qcov : IsQuotientCoveringMap (Quotient.mk (MulAction.orbitRel G M)) G :=
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
  letI : ChartedSpace H (orbitRel.Quotient G M) :=
    qcov.isCoveringMap.isLocalHomeomorph.chartedSpace Quotient.mk_surjective
  have hG : HasGroupoid (orbitRel.Quotient G M) (contDiffGroupoid n I) :=
    qcov.isCoveringMap.isLocalHomeomorph.hasGroupoid_chartedSpace Quotient.mk_surjective
      hcompat
  exact IsManifold.mk' I n (orbitRel.Quotient G M)

end IsManifold

end MulAction
