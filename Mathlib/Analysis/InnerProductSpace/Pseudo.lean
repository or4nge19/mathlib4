/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Operator.QuadraticFormSignature
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Pseudo-inner product spaces

`PseudoInnerProductSpace E` equips a real topological vector space with a continuous symmetric
nondegenerate bilinear form. Positivity is dropped, so the form induces no norm and leaves the
topology of `E` free; the class can therefore be attached to a space that already carries one — a
tangent space, a bundle fibre — without a diamond. Inheritance runs
`InnerProductSpace ℝ E → PseudoInnerProductSpace E` and never the reverse.

Nothing here mentions manifolds: the musical isomorphisms are linear algebra, so the same results
serve tangent, normal and gauge bundles. `♭` is obtained from `LinearMap.BilinForm.toDual`, so it
is an isomorphism only under `[T2Space E]` and `[FiniteDimensional ℝ E]`. Demanding instead that
`♭` be an isomorphism outright — a perfect pairing, `LinearMap.IsPerfPair` — would restrict the
`InnerProductSpace` instance to Hilbert spaces, since Fréchet–Riesz needs completeness, and so
would defeat the subsumption.

## Main definitions

* `PseudoInnerProductSpace E`, `pseudoInner v w`, `PseudoInnerProductSpace.flatL`
* `PseudoInnerProductSpace.ofBilinForm`: build an instance from a symmetric nondegenerate
  bilinear form, with no continuity obligation
* `PseudoInnerProductSpace.flatEquiv`, `sharpEquiv`, `sharpL`: `♭ : E ≃L[ℝ] E⋆` and its inverse
* `PseudoInnerProductSpace.dualPseudoInnerSL`: the induced form on `E⋆`, i.e. the inverse metric
* `PseudoInnerProductSpace.index`: negative inertia `sigNeg` of the associated quadratic form
* `PseudoInnerProductSpace.eq_zero_of_symm_of_antisymm`: the algebraic identity behind
  uniqueness of the Levi-Civita connection, independent of signature

## Acknowledgements

The design follows Sébastien Gouëzel's proposal on Zulip: a fibrewise class for the bilinear
form, an instance from `InnerProductSpace`, and a weakening of `IsContMDiffRiemannianBundle` to
it, so that Riemannian geometry is subsumed rather than duplicated. See
https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/The.20future.20of.20pseudo-Riemannian.20manifolds/with/619509253

## Tags

pseudo-inner product, nondegenerate bilinear form, musical isomorphism, index raising, signature
-/

@[expose] public section

open Module QuadraticMap

/-! ## The class -/

/-- A real topological vector space with a continuous symmetric nondegenerate bilinear form.
Positivity is not assumed, so the topology of `E` is independent data.

Here `Pseudo` means *indefinite*, as in "pseudo-Riemannian", not the usual Mathlib sense of
dropping a separation axiom: nondegeneracy is retained. -/
class PseudoInnerProductSpace (E : Type*) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] where
  /-- The pseudo-inner product, as a continuous bilinear map. -/
  pseudoInnerSL : E →L[ℝ] E →L[ℝ] ℝ
  /-- The pseudo-inner product is symmetric. -/
  pseudoInner_symm : ∀ v w : E, pseudoInnerSL v w = pseudoInnerSL w v
  /-- The pseudo-inner product is nondegenerate: a vector pairing to zero with everything is
  itself zero. -/
  pseudoInner_nondegenerate : ∀ v : E, (∀ w : E, pseudoInnerSL v w = 0) → v = 0

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- The pseudo-inner product `⟪v, w⟫` of two vectors of a pseudo-inner product space. -/
noncomputable def pseudoInner [PseudoInnerProductSpace E] (v w : E) : ℝ :=
  PseudoInnerProductSpace.pseudoInnerSL v w

namespace PseudoInnerProductSpace

section Basic

variable [PseudoInnerProductSpace E]

lemma pseudoInner_comm (v w : E) : pseudoInner v w = pseudoInner w v :=
  pseudoInner_symm v w

lemma eq_zero_of_pseudoInner_eq_zero {v : E} (h : ∀ w : E, pseudoInner v w = 0) : v = 0 :=
  pseudoInner_nondegenerate v h

lemma eq_zero_of_pseudoInner_right_eq_zero {w : E} (h : ∀ v : E, pseudoInner v w = 0) : w = 0 :=
  pseudoInner_nondegenerate w fun v ↦ (pseudoInner_comm w v).trans (h v)

@[simp] lemma pseudoInner_zero_left (w : E) : pseudoInner (0 : E) w = 0 := by
  simp [pseudoInner]

@[simp] lemma pseudoInner_zero_right (v : E) : pseudoInner v (0 : E) = 0 := by
  simp [pseudoInner]

lemma pseudoInner_add_left (u v w : E) :
    pseudoInner (u + v) w = pseudoInner u w + pseudoInner v w := by
  simp [pseudoInner]

lemma pseudoInner_add_right (u v w : E) :
    pseudoInner u (v + w) = pseudoInner u v + pseudoInner u w := by
  simp [pseudoInner]

lemma pseudoInner_sub_left (u v w : E) :
    pseudoInner (u - v) w = pseudoInner u w - pseudoInner v w := by
  simp [pseudoInner]

lemma pseudoInner_sub_right (u v w : E) :
    pseudoInner u (v - w) = pseudoInner u v - pseudoInner u w := by
  simp [pseudoInner]

lemma pseudoInner_smul_left (c : ℝ) (v w : E) :
    pseudoInner (c • v) w = c * pseudoInner v w := by
  simp [pseudoInner]

lemma pseudoInner_smul_right (c : ℝ) (v w : E) :
    pseudoInner v (c • w) = c * pseudoInner v w := by
  simp [pseudoInner]

/-! ### The Levi-Civita rigidity identity -/

/-- A map that is symmetric in its two arguments and antisymmetric against the form in its
outer arguments vanishes.

This is the algebraic content of the uniqueness of the Levi-Civita connection: the difference
tensor `S` of two connections is symmetric when both are torsion-free, and satisfies
`⟪S u v, w⟫ = -⟪S w v, u⟫` when both are metric, and these two together force `S = 0`. Only
symmetry and nondegeneracy of the form are used, so the statement is insensitive to signature. -/
lemma eq_zero_of_symm_of_antisymm {S : E → E → E} (hsymm : ∀ u v, S u v = S v u)
    (hanti : ∀ u v w, pseudoInner (S u v) w = -pseudoInner (S w v) u) (u v : E) :
    S u v = 0 := by
  refine eq_zero_of_pseudoInner_eq_zero fun w ↦ ?_
  have h1 := hanti u v w
  have h2 : pseudoInner (S w v) u = pseudoInner (S v w) u := by rw [hsymm w v]
  have h3 := hanti v w u
  have h4 : pseudoInner (S u w) v = pseudoInner (S w u) v := by rw [hsymm u w]
  have h5 := hanti w u v
  have h6 : pseudoInner (S v u) w = pseudoInner (S u v) w := by rw [hsymm v u]
  linarith

end Basic

/-! ## Riemannian geometry as a special case -/

section InnerProduct

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Every real inner product space is a pseudo-inner product space: positive definiteness is in
particular nondegeneracy. This instance is what makes the subsumption automatic. -/
noncomputable instance (priority := 100) _root_.InnerProductSpace.toPseudoInnerProductSpace :
    PseudoInnerProductSpace F where
  pseudoInnerSL := innerSL ℝ
  pseudoInner_symm v w := real_inner_comm w v
  pseudoInner_nondegenerate v hv := (inner_self_eq_zero (𝕜 := ℝ)).mp (hv v)

@[simp]
lemma pseudoInner_eq_inner (v w : F) : pseudoInner v w = inner ℝ v w := rfl

end InnerProduct

/-! ## The associated bilinear and quadratic forms -/

section Forms

variable [PseudoInnerProductSpace E]

variable (E) in
/-- Index lowering `♭ : v ↦ pseudoInner v ·`. Definitionally the pseudo-inner product; this makes
`E` explicit and records the geometric role. -/
abbrev flatL : E →L[ℝ] (E →L[ℝ] ℝ) := PseudoInnerProductSpace.pseudoInnerSL

@[simp]
lemma flatL_apply (v w : E) : flatL E v w = pseudoInner v w := rfl

lemma toBilinForm_isSymm : (flatL E).toBilinForm.IsSymm :=
  ⟨fun v w ↦ by simpa using (pseudoInner_comm v w)⟩

lemma toBilinForm_nondegenerate : (flatL E).toBilinForm.Nondegenerate := by
  constructor
  · exact fun v hv ↦ eq_zero_of_pseudoInner_eq_zero fun w ↦ by simpa using hv w
  · exact fun w hw ↦ eq_zero_of_pseudoInner_right_eq_zero fun v ↦ by simpa using hw v

variable (E) in
/-- The quadratic form `v ↦ pseudoInner v v`. Its `sigNeg` is the index. -/
noncomputable def toQuadraticForm : QuadraticForm ℝ E := (flatL E).toQuadraticForm

@[simp]
lemma toQuadraticForm_apply (v : E) : toQuadraticForm E v = pseudoInner v v := rfl

end Forms

/-! ## Building an instance from a bilinear form -/

section OfBilinForm

variable (E) in
/-- Build a pseudo-inner product from a symmetric nondegenerate bilinear form on a
finite-dimensional Hausdorff space. Continuity is automatic there, so no analytic input is
needed; this is how a concrete metric (Minkowski, Schwarzschild, FLRW) is supplied. -/
@[reducible] noncomputable def ofBilinForm [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [T2Space E] [FiniteDimensional ℝ E] (B : LinearMap.BilinForm ℝ E) (hs : B.IsSymm)
    (hn : B.Nondegenerate) : PseudoInnerProductSpace E where
  pseudoInnerSL := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E) (F' := ℝ)).toLinearMap ∘ₗ B)
  pseudoInner_symm := LinearMap.BilinForm.isSymm_def.mp hs
  pseudoInner_nondegenerate := hn.1

end OfBilinForm

/-! ## Musical isomorphisms -/

section Musical

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
  [FiniteDimensional ℝ E] [PseudoInnerProductSpace E]

variable (E) in
/-- The musical isomorphism `♭ : E ≃L[ℝ] E⋆`, from `LinearMap.BilinForm.toDual` composed with the
identification of the algebraic and continuous duals in finite dimension. -/
noncomputable def flatEquiv : E ≃L[ℝ] (E →L[ℝ] ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    (((flatL E).toBilinForm.toDual toBilinForm_nondegenerate).trans
      (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E) (F' := ℝ)))

@[simp]
lemma flatEquiv_apply (v w : E) : flatEquiv E v w = pseudoInner v w := rfl

variable (E) in
/-- The musical isomorphism `♯ : E⋆ ≃L[ℝ] E`, inverse to `♭`. -/
noncomputable def sharpEquiv : (E →L[ℝ] ℝ) ≃L[ℝ] E := (flatEquiv E).symm

variable (E) in
/-- Index raising `♯ : E⋆ →L[ℝ] E`, as a continuous linear map. -/
noncomputable def sharpL : (E →L[ℝ] ℝ) →L[ℝ] E := (sharpEquiv E).toContinuousLinearMap

lemma sharpL_apply (ω : E →L[ℝ] ℝ) : sharpL E ω = sharpEquiv E ω := rfl

@[simp]
lemma sharpL_flatL (v : E) : sharpL E (flatL E v) = v :=
  (flatEquiv E).symm_apply_apply v

@[simp]
lemma flatL_sharpL (ω : E →L[ℝ] ℝ) : flatL E (sharpL E ω) = ω :=
  (flatEquiv E).apply_symm_apply ω

/-- Pairing with a raised covector is evaluation. -/
@[simp]
lemma pseudoInner_sharpL_right (v : E) (ω : E →L[ℝ] ℝ) :
    pseudoInner v (sharpL E ω) = ω v := by
  rw [pseudoInner_comm]
  exact congrFun (congrArg (fun f : E →L[ℝ] ℝ ↦ (f : E → ℝ)) (flatL_sharpL ω)) v

/-- Pairing with a raised covector is evaluation. -/
@[simp]
lemma pseudoInner_sharpL_left (v : E) (ω : E →L[ℝ] ℝ) :
    pseudoInner (sharpL E ω) v = ω v := by
  rw [pseudoInner_comm]; exact pseudoInner_sharpL_right v ω

/-! ### The induced form on the dual -/

variable (E) in
/-- The form induced on `E⋆` by raising both indices, `(ω₁, ω₂) ↦ ω₁ (ω₂♯)`; for a metric tensor,
the inverse metric `g^{ab}`. -/
noncomputable def dualPseudoInnerSL : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E →L[ℝ] ℝ) (F' := (E →L[ℝ] ℝ) →L[ℝ] ℝ)
    { toFun := fun ω : E →L[ℝ] ℝ ↦ ω.comp (sharpL E)
      map_add' := fun ω₁ ω₂ ↦ by ext ω; simp
      map_smul' := fun c ω ↦ by ext ω'; simp }

@[simp]
lemma dualPseudoInnerSL_apply (ω₁ ω₂ : E →L[ℝ] ℝ) :
    dualPseudoInnerSL E ω₁ ω₂ = ω₁ (sharpL E ω₂) := rfl

lemma dualPseudoInnerSL_eq_pseudoInner_sharpL (ω₁ ω₂ : E →L[ℝ] ℝ) :
    dualPseudoInnerSL E ω₁ ω₂ = pseudoInner (sharpL E ω₁) (sharpL E ω₂) := by
  rw [dualPseudoInnerSL_apply, pseudoInner_sharpL_left]

lemma dualPseudoInnerSL_symm (ω₁ ω₂ : E →L[ℝ] ℝ) :
    dualPseudoInnerSL E ω₁ ω₂ = dualPseudoInnerSL E ω₂ ω₁ := by
  simp only [dualPseudoInnerSL_eq_pseudoInner_sharpL]
  exact pseudoInner_comm _ _

lemma dualPseudoInnerSL_nondegenerate (ω : E →L[ℝ] ℝ)
    (h : ∀ η : E →L[ℝ] ℝ, dualPseudoInnerSL E ω η = 0) : ω = 0 := by
  ext v
  simpa only [dualPseudoInnerSL_apply, sharpL_flatL, zero_apply]
    using h (flatL E v)

variable (E) in
/-- `E⋆` with the inverse form. Deliberately a `def`: as an instance it would let typeclass
inference loop through iterated duals. -/
@[reducible] noncomputable def dual : PseudoInnerProductSpace (E →L[ℝ] ℝ) where
  pseudoInnerSL := dualPseudoInnerSL E
  pseudoInner_symm := dualPseudoInnerSL_symm
  pseudoInner_nondegenerate := dualPseudoInnerSL_nondegenerate

end Musical

/-! ## The index -/

variable (E : Type*) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [PseudoInnerProductSpace E]

/-- The index, or negative inertia: the largest dimension of a subspace on which the form is
negative definite. Index `0` is the Riemannian case, index `1` the Lorentzian one. -/
noncomputable def index : ℕ := sigNeg (toQuadraticForm E)

lemma index_def : index E = sigNeg (toQuadraticForm E) := rfl

/-- Nondegeneracy, restated: the quadratic form has trivial radical. -/
lemma radical_toQuadraticForm_eq_bot : (toQuadraticForm E).radical = ⊥ := by
  rw [QuadraticMap.radical_eq_ker_polarBilin, Submodule.eq_bot_iff]
  intro v hv
  refine eq_zero_of_pseudoInner_eq_zero fun w ↦ ?_
  have h0 : QuadraticMap.polar (toQuadraticForm E) v w = 0 := by
    simpa using DFunLike.congr_fun (LinearMap.mem_ker.mp hv) w
  have hpolar : QuadraticMap.polar (toQuadraticForm E) v w = 2 * pseudoInner v w := by
    simp only [QuadraticMap.polar, toQuadraticForm_apply, pseudoInner_add_left,
      pseudoInner_add_right]
    rw [pseudoInner_comm w v]
    ring
  linarith

variable [FiniteDimensional ℝ E]

variable {E} in
/-- One vector of negative square already forces positive index: the form is not Riemannian. -/
lemma one_le_index_of_neg {v : E} (hv : v ≠ 0) (h : pseudoInner v v < 0) : 1 ≤ index E := by
  have key : Module.finrank ℝ (ℝ ∙ v : Submodule ℝ E) ≤ sigNeg (toQuadraticForm E) := by
    refine le_sigNeg_of_negDef _ fun x hx ↦ ?_
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp x.2
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hx (Subtype.ext (by simpa using hc.symm))
    have hval : toQuadraticForm E (x : E) = c * c * pseudoInner v v := by
      rw [← hc, ← toQuadraticForm_apply v, QuadraticMap.map_smul]
      simp [smul_eq_mul]
    change (0 : ℝ) < -(toQuadraticForm E (x : E))
    rw [hval]
    nlinarith [mul_self_pos.mpr hc0]
  rwa [finrank_span_singleton hv] at key

variable {E} in
/-- A positive definite form has index `0`. -/
lemma index_eq_zero_of_posDef (h : (toQuadraticForm E).PosDef) : index E = 0 := by
  obtain ⟨W, hW, hWneg⟩ :=
    exists_finrank_eq_sigNeg_and_negDef (Q := toQuadraticForm E)
  have hWbot : W = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    by_contra hx0
    have hxW : (⟨x, hx⟩ : W) ≠ 0 := fun hcontra ↦ hx0 (congrArg Subtype.val hcontra)
    have hlt : toQuadraticForm E x < 0 := by
      have := hWneg _ hxW
      simp only [QuadraticMap.restrict_apply, neg_apply] at this
      linarith
    exact absurd (h x hx0) (by linarith)
  simp [index, ← hW, hWbot]

/-- Raising both indices is an isometry, so the inverse metric on `E⋆` has the same index. -/
lemma index_dual_eq [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] :
    letI := dual E
    index (E →L[ℝ] ℝ) = index E := by
  have key : ∀ u w : E, dualPseudoInnerSL E (flatL E u) (flatL E w) = pseudoInner u w := by
    intro u w
    rw [dualPseudoInnerSL_apply, sharpL_flatL, flatL_apply]
  exact (ContinuousLinearMap.sigNeg_toQuadraticForm_of_congr
    (PseudoInnerProductSpace.pseudoInnerSL (E := E)) (dualPseudoInnerSL E)
    (flatEquiv E).toLinearEquiv key).symm

/-- Riemannian geometry is the index-zero case. -/
@[simp]
lemma index_eq_zero_of_innerProductSpace (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] : index F = 0 :=
  index_eq_zero_of_posDef fun v hv ↦ by
    simpa using real_inner_self_pos.mpr hv

end PseudoInnerProductSpace
