/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.PseudoRiemannian

/-!
# Pseudo-Riemannian manifolds

A pseudo-Riemannian metric on `M` is a pseudo-Riemannian structure on its tangent bundle, so this
file only specializes `Mathlib.Geometry.Manifold.VectorBundle.PseudoRiemannian`. To say "let
`M` be a pseudo-Riemannian manifold", write
```
variable [∀ x : M, PseudoInnerProductSpace (TangentSpace I x)]
  [IsContMDiffPseudoRiemannianBundle I n E (TangentSpace I : M → Type _)]
```
Mathlib's `[RiemannianBundle (TangentSpace I : M → Type _)]` with
`[IsContMDiffRiemannianBundle I n E (TangentSpace I : M → Type _)]` implies this. No
`ofCoreOfTopology` detour is needed, since an indefinite form determines no norm.

The musical isomorphisms are inherited: at `x` they are
`PseudoInnerProductSpace.flatEquiv (TangentSpace I x)` and `sharpEquiv (TangentSpace I x)`, with
inverse metric `dualPseudoInnerSL (TangentSpace I x)`.

## Main definitions

* `PseudoRiemannianMetric I n M`: metric data on `M`; theorems are stated with the typeclasses.
* `PseudoRiemannian.index I x`: the index of the metric at `x`.

## Main results

* `PseudoRiemannian.isLocallyConstant_index` and `index_eq_of_preconnectedSpace`: signature
  constancy is a theorem, so no metric carries it as data.

## Acknowledgements

The design follows Sébastien Gouëzel's proposal on Zulip, see [Zulip](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/The.20future.20of.20pseudo-Riemannian.20manifolds/with/619509253).

## Tags

pseudo-Riemannian, Lorentzian, metric tensor, index, musical isomorphisms

## References

* Barrett O'Neill, *Semi-Riemannian Geometry with Applications to Relativity*, Academic
  Press (1983).
-/

@[expose] public section

open Bundle Module
open scoped Manifold Bundle Topology ContDiff

/-- A `C^n` pseudo-Riemannian metric on `M`: the tangent-bundle case of
`Bundle.ContMDiffPseudoRiemannianMetric`. Use it to produce the instances that theorems are
stated with. -/
abbrev PseudoRiemannianMetric {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (n : ℕ∞ω)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :=
  Bundle.ContMDiffPseudoRiemannianMetric (IB := I) (n := n) (F := E)
    (E := fun x : M ↦ TangentSpace I x)

namespace PseudoRiemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}
  [∀ x : M, PseudoInnerProductSpace (TangentSpace I x)]

variable (I) in
/-- The index of the metric at `x`. Index `0` is Riemannian, index `1` Lorentzian in the "mostly
plus" convention. -/
noncomputable def index (x : M) : ℕ := PseudoInnerProductSpace.index (TangentSpace I x)

variable [IsManifold I 1 M] [FiniteDimensional ℝ E]

/-- **The index is locally constant.** Smoothness and pointwise nondegeneracy already force
signature constancy, so it is nowhere assumed. -/
theorem isLocallyConstant_index
    [IsContMDiffPseudoRiemannianBundle I n E (TangentSpace I : M → Type _)] :
    IsLocallyConstant (index I : M → ℕ) :=
  Bundle.isLocallyConstant_index (IB := I) (n := n) (F := E)
    (E := fun x : M ↦ TangentSpace I x)

/-- The index is constant on preconnected subsets of the manifold. -/
lemma index_eq_of_isPreconnected
    [IsContMDiffPseudoRiemannianBundle I n E (TangentSpace I : M → Type _)] {s : Set M}
    (hs : IsPreconnected s) {x y : M} (hx : x ∈ s) (hy : y ∈ s) : index I x = index I y :=
  (isLocallyConstant_index (I := I) (n := n)).apply_eq_of_isPreconnected hs hx hy

/-- On a connected manifold the index is a global invariant. -/
lemma index_eq_of_preconnectedSpace [PreconnectedSpace M]
    [IsContMDiffPseudoRiemannianBundle I n E (TangentSpace I : M → Type _)] (x y : M) :
    index I x = index I y :=
  (isLocallyConstant_index (I := I) (n := n)).apply_eq_of_preconnectedSpace x y

/-- The index is constant along connected components. -/
lemma index_eq_of_mem_connectedComponent
    [IsContMDiffPseudoRiemannianBundle I n E (TangentSpace I : M → Type _)] {x y : M}
    (hy : y ∈ connectedComponent x) : index I y = index I x :=
  index_eq_of_isPreconnected (n := n) isConnected_connectedComponent.isPreconnected hy
    mem_connectedComponent

end PseudoRiemannian
