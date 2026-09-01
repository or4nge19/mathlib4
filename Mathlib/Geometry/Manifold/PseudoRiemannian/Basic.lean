/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-!
# Pseudo-Riemannian manifolds

A pseudo-Riemannian metric on `M` is a pseudo-Riemannian structure on its tangent bundle, so this
file only specializes `Mathlib.Geometry.Manifold.VectorBundle.PseudoRiemannian`. To say "let
`M` be a pseudo-Riemannian manifold", write
```
variable [∀ x : M, PseudoInnerProductSpace ℝ (TangentSpace I x)]
  [IsContMDiffPseudoRiemannianBundle I n E (TangentSpace I : M → Type _)]
```
Mathlib's `[RiemannianBundle (TangentSpace I : M → Type _)]` with
`[IsContMDiffPseudoRiemannianBundle I n E (TangentSpace I : M → Type _)]`, which a Riemannian
bundle supplies through `InnerProductSpace.toPseudoInnerProductSpace`. No
`ofCoreOfTopology` detour is needed, since an indefinite form determines no norm.

The musical isomorphisms are inherited: at `x` they are
`PseudoInnerProductSpace.flatEquiv (TangentSpace I x)` and `sharpEquiv (TangentSpace I x)`, with
inverse metric `dualPseudoInnerSL (TangentSpace I x)`.

## Main definitions

* `PseudoRiemannianMetric I n M`: metric data on `M`; theorems are stated with the typeclasses.
* `PseudoRiemannian.index I x`, `PseudoRiemannian.coindex I x`: the numbers of negative and of
  positive directions at `x`, related by `coindex_add_index_eq_finrank`;
  `index_eq_zero_of_riemannianBundle` identifies Riemannian geometry as the index-zero case.

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
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [∀ x : M, PseudoInnerProductSpace ℝ (TangentSpace I x)]

variable (I) in
/-- The index of the metric at `x`: the number of negative directions. Index `0` is Riemannian,
index `1` Lorentzian in the "mostly plus" convention. -/
noncomputable def index (x : M) : ℕ := PseudoInnerProductSpace.index (TangentSpace I x)

variable (I) in
/-- The coindex of the metric at `x`: the number of positive directions. A metric is Lorentzian in
the "mostly minus" convention `(+, -, …, -)` exactly when its coindex is `1`; `coindex` is provided
so that such a statement needs no adapter. -/
noncomputable def coindex (x : M) : ℕ := PseudoInnerProductSpace.coindex (TangentSpace I x)

variable [IsManifold I 1 M] [FiniteDimensional ℝ E]

/-- **The index is locally constant.** Smoothness and pointwise nondegeneracy already force
signature constancy, so it is nowhere assumed.

The smoothness exponent `n` is explicit throughout this section: it occurs only in the instance
argument, so it cannot be inferred from the conclusion. -/
theorem isLocallyConstant_index (n : ℕ∞ω)
    [IsContMDiffPseudoRiemannianBundle I n E (TangentSpace I : M → Type _)] :
    IsLocallyConstant (index I : M → ℕ) :=
  Bundle.isLocallyConstant_index (IB := I) n (F := E) (E := fun x : M ↦ TangentSpace I x)

/-- The index is constant on preconnected subsets of the manifold. -/
lemma index_eq_of_isPreconnected (n : ℕ∞ω)
    [IsContMDiffPseudoRiemannianBundle I n E (TangentSpace I : M → Type _)] {s : Set M}
    (hs : IsPreconnected s) {x y : M} (hx : x ∈ s) (hy : y ∈ s) : index I x = index I y :=
  (isLocallyConstant_index (I := I) n).apply_eq_of_isPreconnected hs hx hy

/-- On a connected manifold the index is a global invariant. -/
lemma index_eq_of_preconnectedSpace (n : ℕ∞ω) [PreconnectedSpace M]
    [IsContMDiffPseudoRiemannianBundle I n E (TangentSpace I : M → Type _)] (x y : M) :
    index I x = index I y :=
  (isLocallyConstant_index (I := I) n).apply_eq_of_preconnectedSpace x y

omit [IsManifold I 1 M] in
/-- **The two inertia indices add up to the dimension**, so either one determines the other and a
statement may be phrased in whichever signature convention the application uses. -/
lemma coindex_add_index_eq_finrank (x : M) : coindex I x + index I x = Module.finrank ℝ E :=
  PseudoInnerProductSpace.coindex_add_index_eq_finrank (TangentSpace I x)

/-- **The coindex is locally constant**, being the dimension minus the index. -/
theorem isLocallyConstant_coindex (n : ℕ∞ω)
    [IsContMDiffPseudoRiemannianBundle I n E (TangentSpace I : M → Type _)] :
    IsLocallyConstant (coindex I : M → ℕ) := by
  have key : (coindex I : M → ℕ) = (Module.finrank ℝ E - ·) ∘ (index I : M → ℕ) := by
    funext x; have := coindex_add_index_eq_finrank (I := I) x; simp only [Function.comp_apply]; lia
  rw [key]
  exact (isLocallyConstant_index n).comp _

/-- On a connected manifold the coindex is a global invariant. -/
lemma coindex_eq_of_preconnectedSpace (n : ℕ∞ω) [PreconnectedSpace M]
    [IsContMDiffPseudoRiemannianBundle I n E (TangentSpace I : M → Type _)] (x y : M) :
    coindex I x = coindex I y :=
  (isLocallyConstant_coindex (I := I) n).apply_eq_of_preconnectedSpace x y

/-- The index is constant along connected components. -/
lemma index_eq_of_mem_connectedComponent (n : ℕ∞ω)
    [IsContMDiffPseudoRiemannianBundle I n E (TangentSpace I : M → Type _)] {x y : M}
    (hy : y ∈ connectedComponent x) : index I y = index I x :=
  index_eq_of_isPreconnected n isConnected_connectedComponent.isPreconnected hy
    mem_connectedComponent

/-! ### A vector space with a pseudo-inner product is a pseudo-Riemannian manifold

This is the pseudo-Riemannian analogue of `riemannianMetricVectorSpace`, and the source of the
concrete examples: applied to `PseudoInnerProductSpace.prodDiff` it produces Minkowski spacetime.
-/

section VectorSpace

variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [PseudoInnerProductSpace ℝ V]

set_option backward.isDefEq.respectTransparency false in
/-- The constant pseudo-Riemannian metric on a vector space carrying a pseudo-inner product, given
by that form on each tangent space. -/
noncomputable def pseudoRiemannianMetricVectorSpace :
    Bundle.ContMDiffPseudoRiemannianMetric 𝓘(ℝ, V) ω V (fun (x : V) ↦ TangentSpace% x) where
  metric _ := PseudoInnerProductSpace.innerSL (𝕜 := ℝ) (E := V)
  symm _ v w := PseudoInnerProductSpace.innerSL_conj_symm (𝕜 := ℝ) (E := V) v w
  nondegenerate _ v hv := PseudoInnerProductSpace.innerSL_nondegenerate (𝕜 := ℝ) (E := V) v hv
  contMDiff := by
    intro x
    rw [contMDiffAt_section]
    convert! contMDiffAt_const (c := PseudoInnerProductSpace.innerSL (𝕜 := ℝ) (E := V))
    ext v w
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, TangentSpace]

end VectorSpace

end PseudoRiemannian

namespace PseudoRiemannian

/-! ### Riemannian manifolds are the index-zero case -/

section Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (TangentSpace I : M → Type _)]

omit [IsManifold I 1 M] in
/-- A Riemannian metric has index `0` at every point: Riemannian geometry is the index-zero case.
The fibrewise form is the one supplied by `RiemannianBundle`, through
`InnerProductSpace.toPseudoInnerProductSpace`, so no adapter is involved.

There is deliberately no `IsRiemannian` class: Mathlib's `IsRiemannianManifold` already covers
it. -/
@[simp]
lemma index_eq_zero_of_riemannianBundle (x : M) : index I x = 0 :=
  PseudoInnerProductSpace.index_eq_zero_of_innerProductSpace (TangentSpace I x)

end Riemannian

end PseudoRiemannian
