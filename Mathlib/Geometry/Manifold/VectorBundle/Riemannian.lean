/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.PseudoRiemannian
public import Mathlib.Topology.VectorBundle.Riemannian

/-! # Riemannian vector bundles

Given a vector bundle over a manifold whose fibers are all endowed with a scalar product, we
say that this bundle is Riemannian if the scalar product depends smoothly on the base point.

Smoothness of the fibrewise scalar product is registered by
`[IsContMDiffPseudoRiemannianBundle IB n F E]`, which does not assume positivity; for
inner-product fibres it is supplied by `InnerProductSpace.toPseudoInnerProductSpace`, which carries
Mathlib's *own* `Inner` instance. So a Riemannian bundle satisfies that class with no adapter, and
`inner ℝ` denotes the same function on the nose.

Consequently the smoothness results for the scalar product — `ContMDiffWithinAt.inner_bundle` and
friends — are not restated here: they *are* the general statements proved in
`Mathlib/Geometry/Manifold/VectorBundle/PseudoRiemannian.lean`, under exactly these names.

If the fibers of a bundle `E` have a preexisting topology (like the tangent bundle), one cannot
assume additionally `[∀ b, InnerProductSpace ℝ (E b)]` as this would create diamonds. Instead,
use `[RiemannianBundle E]`, which endows the fibers with a scalar product while ensuring that
there is no diamond (for this, the `Bundle` scope should be open). We provide a
constructor for `[RiemannianBundle E]` from a smooth family of metrics, which registers
automatically `[IsContMDiffPseudoRiemannianBundle IB n F E]`.

The following code block is the standard way to say "Let `E` be a smooth vector bundle equipped with
a `C^n` Riemannian structure over a `C^n` manifold `B`":
```
variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)] [FiberBundle F E] [VectorBundle ℝ F E]
  [IsManifold IB n B] [ContMDiffVectorBundle n F E IB]
  [IsContMDiffPseudoRiemannianBundle IB n F E]
```
-/

@[expose] public section

open Bundle ContinuousLinearMap ENat Bornology PseudoInnerProductSpace

open scoped Manifold ContDiff Topology

section

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n n' : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- `IsContMDiffRiemannianBundle` has been weakened to `IsContMDiffPseudoRiemannianBundle`, which
does not assume positivity; a bundle with inner-product fibres satisfies it through
`InnerProductSpace.toPseudoInnerProductSpace`, so uses of the old name need only be renamed. -/
@[deprecated IsContMDiffPseudoRiemannianBundle (since := "2026-08-31")]
abbrev IsContMDiffRiemannianBundle := @IsContMDiffPseudoRiemannianBundle


end

namespace Bundle

section Construction

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n n' : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

variable (IB n F E) in
/-- A family of inner product space structures on the fibers of a fiber bundle, defining the same
topology as the already existing one, and varying continuously with the base point. See also
`ContinuousRiemannianMetric` for a continuous version.

This structure is used through `RiemannianBundle` for typeclass inference, to register the inner
product space structure on the fibers without creating diamonds. -/
structure ContMDiffRiemannianMetric where
  /-- The scalar product along the fibers of the bundle. -/
  inner (b : B) : E b →L[ℝ] E b →L[ℝ] ℝ
  symm (b : B) (v w : E b) : inner b v w = inner b w v
  pos (b : B) (v : E b) (hv : v ≠ 0) : 0 < inner b v v
  isVonNBounded (b : B) : IsVonNBounded ℝ {v : E b | inner b v v < 1}
  contMDiff : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
    (fun b ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (inner b))

/-- A smooth Riemannian metric defines in particular a continuous Riemannian metric. -/
def ContMDiffRiemannianMetric.toContinuousRiemannianMetric
    (g : ContMDiffRiemannianMetric IB n F E) : ContinuousRiemannianMetric F E :=
  { g with continuous := g.contMDiff.continuous }

/-- A smooth Riemannian metric defines in particular a Riemannian metric. -/
def ContMDiffRiemannianMetric.toRiemannianMetric
    (g : ContMDiffRiemannianMetric IB n F E) : RiemannianMetric E :=
  g.toContinuousRiemannianMetric.toRiemannianMetric

instance (g : ContMDiffRiemannianMetric IB n F E) :
    letI : RiemannianBundle E := ⟨g.toRiemannianMetric⟩
    IsContMDiffPseudoRiemannianBundle IB n F E :=
  letI : RiemannianBundle E := ⟨g.toRiemannianMetric⟩
  ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩

end Construction

end Bundle

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

instance [CompleteSpace E] {x : M} : CompleteSpace (TangentSpace I x) :=
  VectorBundle.completeSpace ℝ E ..

end
