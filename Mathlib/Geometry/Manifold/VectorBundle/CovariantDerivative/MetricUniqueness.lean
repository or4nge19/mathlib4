/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

/-!
# Uniqueness of a torsion-free metric connection

A connection on the tangent bundle that is compatible with a fibrewise nondegenerate symmetric
form and torsion-free is unique on differentiable vector fields. Positivity plays no role, so this
covers Riemannian, Lorentzian and arbitrary pseudo-Riemannian signatures at once; the Riemannian
statement `CovariantDerivative.IsLeviCivitaConnection.uniqueness` is derived from it in
`Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean`.

The argument is classical. The difference of two connections is a tensor
(`IsCovariantDerivativeOn.difference`); equal torsions make it symmetric, metric compatibility
makes it antisymmetric against the form, and
`PseudoInnerProductSpace.eq_zero_of_symm_of_antisymm` forces it to vanish.

Existence is proved in
`Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean`, at the same
generality: the Koszul construction there recovers `∇_X Y` from `⟪∇_X Y, ·⟫` through the musical
isomorphism `PseudoInnerProductSpace.sharpL`, which is an isomorphism by nondegeneracy alone.

## Main results

* `CovariantDerivative.eq_of_isMetricCompatible_of_torsion_eq_zero`

## Tags

Levi-Civita, connection, torsion, metric connection, pseudo-Riemannian
-/

@[expose] public section

open Bundle NormedSpace PseudoInnerProductSpace Set FiberBundle
open scoped Manifold ContDiff

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [IsManifold I 2 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]

namespace CovariantDerivative

section General

variable [∀ x : M, PseudoInnerProductSpace ℝ (TangentSpace I x)]
  [IsContMDiffPseudoRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  {cov cov' : CovariantDerivative I E (TangentSpace I : M → Type _)}

/-- The difference tensor of two connections on the tangent bundle, at a point. -/
private def diffAt (cov cov' : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  IsCovariantDerivativeOn.difference (cov.isCovariantDerivativeOn (s := (univ : Set M)))
    (cov'.isCovariantDerivativeOn (s := (univ : Set M))) x

omit [IsManifold I 2 M] [∀ x : M, PseudoInnerProductSpace ℝ (TangentSpace I x)]
  [IsContMDiffPseudoRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
private lemma diffAt_apply {x : M} {σ : Π y : M, TangentSpace I y} (hσ : MDiffAt (T% σ) x) :
    diffAt cov cov' x (σ x) = cov σ x - cov' σ x :=
  IsCovariantDerivativeOn.difference_apply _ _ (mem_univ x) hσ

omit [IsManifold I 2 M] [∀ x : M, PseudoInnerProductSpace ℝ (TangentSpace I x)]
  [IsContMDiffPseudoRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
private lemma diffAt_extend {x : M} (v : TangentSpace I x) :
    diffAt cov cov' x v = cov (extend E v) x - cov' (extend E v) x := by
  have h := diffAt_apply (cov := cov) (cov' := cov') (σ := extend E v)
    (mdifferentiableAt_extend I E v)
  rwa [extend_apply_self] at h

omit [∀ x : M, PseudoInnerProductSpace ℝ (TangentSpace I x)]
  [IsContMDiffPseudoRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- Two torsion-free connections have a symmetric difference tensor. -/
private lemma diffAt_symm (ht : cov.torsion = 0) (ht' : cov'.torsion = 0) {x : M}
    (u v : TangentSpace I x) : diffAt cov cov' x v u = diffAt cov cov' x u v := by
  have hu := mdifferentiableAt_extend I E u
  have hv := mdifferentiableAt_extend I E v
  have h := cov.torsion_eq_zero_iff.mp ht hu hv
  have h' := cov'.torsion_eq_zero_iff.mp ht' hu hv
  rw [extend_apply_self, extend_apply_self] at h h'
  have hsub : (cov (extend E v) x u - cov' (extend E v) x u)
      - (cov (extend E u) x v - cov' (extend E u) x v) = 0 := by
    rw [sub_sub_sub_comm, h, h', sub_self]
  have hv' := diffAt_extend (cov := cov) (cov' := cov') v
  have hu' := diffAt_extend (cov := cov) (cov' := cov') u
  have := sub_eq_zero.mp hsub
  simpa [hv', hu'] using this

omit [IsManifold I 2 M] in
/-- Two metric connections have a difference tensor that is antisymmetric against the form. -/
private lemma diffAt_antisymm (hm : cov.IsMetricCompatible)
    (hm' : cov'.IsMetricCompatible) {x : M} (u v w : TangentSpace I x) :
    inner ℝ (diffAt cov cov' x u v) w = -inner ℝ (diffAt cov cov' x w v) u := by
  have hu := mdifferentiableAt_extend I E u
  have hw := mdifferentiableAt_extend I E w
  have h := hm.mvfderiv_inner_eq (extend E v) hu hw
  have h' := hm'.mvfderiv_inner_eq (extend E v) hu hw
  simp only [extend_apply_self] at h h'
  rw [h'] at h
  have hu' := diffAt_extend (cov := cov) (cov' := cov') u
  have hw' := diffAt_extend (cov := cov) (cov' := cov') w
  have key : inner ℝ (diffAt cov cov' x u v) w + inner ℝ u (diffAt cov cov' x w v) = 0 := by
    simp only [hu', hw', sub_apply, PseudoInnerProductSpace.inner_sub_left,
      PseudoInnerProductSpace.inner_sub_right]
    linarith
  rw [PseudoInnerProductSpace.inner_comm u (diffAt cov cov' x w v)] at key
  linarith

/-- **Uniqueness of the Levi-Civita connection.** Two connections on the tangent bundle that are
compatible with the pseudo-inner product and torsion-free agree on differentiable vector fields.

No positivity is used, so this covers Lorentzian and general pseudo-Riemannian signatures. -/
theorem eq_of_isMetricCompatible_of_torsion_eq_zero
    (hm : cov.IsMetricCompatible) (hm' : cov'.IsMetricCompatible)
    (ht : cov.torsion = 0) (ht' : cov'.torsion = 0)
    {x : M} {Y : Π y : M, TangentSpace I y} (hY : MDiffAt (T% Y) x) :
    cov Y x = cov' Y x := by
  have hzero : ∀ u v : TangentSpace I x, diffAt cov cov' x u v = 0 :=
    eq_zero_of_symm_of_antisymm (fun u v ↦ diffAt_symm ht ht' v u) (diffAt_antisymm hm hm')
  have hYzero : diffAt cov cov' x (Y x) = 0 := by ext v; exact hzero (Y x) v
  rw [diffAt_apply hY] at hYzero
  exact sub_eq_zero.mp hYzero

end General

end CovariantDerivative
