/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Geometry.Manifold.PseudoRiemannian.Basic

/-!
# Lorentzian manifolds

A Lorentzian metric is a pseudo-Riemannian metric of index `1`. The index is locally constant, so
on a connected manifold the condition need only be checked at one point; see
`PseudoRiemannian.isLorentzian_of_index_eq_one`.

We use the "mostly plus" convention, signature `(-, +, …, +)`, i.e. index `1`. The "mostly minus"
convention `(+, -, …, -)` used in particle physics is the coindex-`1` condition on the same metric;
`PseudoRiemannian.coindex_eq_of_isLorentzian` converts between the two, and downstream
libraries
working in that convention can state their own condition directly with
`PseudoRiemannian.coindex`, which is locally constant by
`PseudoRiemannian.isLocallyConstant_coindex`.

## Main definitions

* `PseudoRiemannian.IsLorentzian I M`: the index is `1` everywhere.

## Main results

* `PseudoRiemannian.coindex_eq_of_isLorentzian`: in dimension `n` a Lorentzian metric has coindex
  `n - 1`, which is the "mostly minus" reading of the same condition.
* `PseudoRiemannian.finiteDimensional_of_isLorentzian`: index `1` already forces the model to be
  finite-dimensional, so the class needs no such hypothesis.

Minkowski spacetime is the witness that this class is non-vacuous, in
`Mathlib/Geometry/Manifold/PseudoRiemannian/Minkowski.lean`.

## Tags

Lorentzian, pseudo-Riemannian, index, signature, spacetime
-/

@[expose] public section

open Bundle
open scoped Manifold Bundle ContDiff

namespace PseudoRiemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [∀ x : M, PseudoInnerProductSpace ℝ (TangentSpace I x)]

variable (I M) in
/-- The metric is Lorentzian: its index is `1` at every point, i.e. its signature is
`(-, +, …, +)`. -/
class IsLorentzian : Prop where
  /-- A Lorentzian metric has index `1` at every point. -/
  index_eq_one : ∀ x : M, index I x = 1

@[simp]
lemma index_eq_one [IsLorentzian I M] (x : M) : index I x = 1 :=
  IsLorentzian.index_eq_one x

/-- Index `1` is unattainable in infinite dimensions, where `QuadraticForm.sigNeg` vanishes, so a
Lorentzian metric already forces a finite-dimensional model: the class needs no such hypothesis. -/
lemma finiteDimensional_of_isLorentzian [IsLorentzian I M] (x : M) :
    FiniteDimensional ℝ (TangentSpace I x) := by
  refine PseudoInnerProductSpace.finiteDimensional_of_index_pos ?_
  rw [show PseudoInnerProductSpace.index (TangentSpace I x) = index I x from rfl, index_eq_one]
  norm_num

variable [IsManifold I 1 M] [FiniteDimensional ℝ E]

omit [IsManifold I 1 M] in
/-- A Lorentzian metric has `dim M - 1` positive directions: this is the same condition read in the
"mostly minus" convention `(+, -, …, -)`, which is how particle physics states it. -/
lemma coindex_eq_of_isLorentzian [IsLorentzian I M] (x : M) :
    coindex I x + 1 = Module.finrank ℝ E := by
  have h := coindex_add_index_eq_finrank (I := I) x
  rwa [index_eq_one] at h

/-- On a connected manifold, being Lorentzian can be checked at a single point. -/
lemma isLorentzian_of_index_eq_one (n : ℕ∞ω) [PreconnectedSpace M]
    [IsContMDiffPseudoRiemannianBundle I n E (TangentSpace I : M → Type _)] {x₀ : M}
    (h : index I x₀ = 1) : IsLorentzian I M :=
  ⟨fun x ↦ (index_eq_of_preconnectedSpace n x x₀).trans h⟩

end PseudoRiemannian
