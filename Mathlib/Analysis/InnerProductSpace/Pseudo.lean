/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Operator.QuadraticForm
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

* `PseudoInnerProductSpace E`, `inner ℝ v w`, `PseudoInnerProductSpace.flatL`
* `PseudoInnerProductSpace.ofBilinForm`: build an instance from a symmetric nondegenerate
  bilinear form, with no continuity obligation
* `PseudoInnerProductSpace.flatEquiv`, `sharpEquiv`, `sharpL`: `♭ : E ≃L[ℝ] E⋆` and its inverse
* `PseudoInnerProductSpace.dualInnerSL`: the induced form on `E⋆`, i.e. the inverse metric
* `PseudoInnerProductSpace.index`, `coindex`: the negative and positive inertia indices
  (`sigNeg`/`sigPos` of the associated quadratic form), related by `coindex_add_index_eq_finrank`
* `PseudoInnerProductSpace.prodDiff`: the standard indefinite model `⟪f, f'⟫ - ⟪g, g'⟫` on `F × G`,
  with `coindex_prodDiff` and `index_prodDiff` computing its signature; taking `G := ℝ` realises
  the Lorentzian signature, so the class is non-vacuous in every signature
* `PseudoInnerProductSpace.eq_zero_of_symm_of_antisymm`: the algebraic identity behind
  uniqueness of the Levi-Civita connection, independent of signature

## Acknowledgements

The design follows Sébastien Gouëzel's proposal on Zulip: a fibrewise class for the bilinear
form, an instance from `InnerProductSpace`, and a weakening of the smooth bundle-metric class to
it, so that Riemannian geometry is subsumed rather than duplicated. See
https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/The.20future.20of.20pseudo-Riemannian.20manifolds/with/619509253

## Tags

pseudo-inner product, nondegenerate bilinear form, musical isomorphism, index raising, signature
-/

@[expose] public section

open Module QuadraticMap RCLike ComplexConjugate

/-! ## The class -/

/-- A real topological vector space with a continuous symmetric nondegenerate bilinear form.
Positivity is not assumed, so the topology of `E` is independent data.

Here `Pseudo` means *indefinite*, as in "pseudo-Riemannian", not the usual Mathlib sense of
dropping a separation axiom: nondegeneracy is retained. -/
class PseudoInnerProductSpace (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] extends Inner 𝕜 E where
  /-- The pairing as a continuous sesquilinear map: conjugate-linear in the first slot and linear
  in the second, exactly like Mathlib's `innerSL`. Read as a map `E → E⋆` it is the musical
  isomorphism `♭`. -/
  innerSL : E →L⋆[𝕜] E →L[𝕜] 𝕜
  /-- The `Inner` structure is the one carried by `innerSL`.

  Both are stored, tied by this law, so that an `InnerProductSpace` supplies its *own* `Inner`
  instance: the two are then definitionally equal, and every `inner_*` lemma of Mathlib applies
  verbatim in the positive-definite case with no restatement and no bridging simp lemma. -/
  inner_eq_innerSL : ∀ v w : E, inner v w = innerSL v w
  /-- The pairing is conjugate-symmetric. Over `ℝ` this is plain symmetry. -/
  innerSL_conj_symm : ∀ v w : E, conj (innerSL v w) = innerSL w v
  /-- The pairing is nondegenerate: a vector pairing to zero with everything is itself zero. -/
  innerSL_nondegenerate : ∀ v : E, (∀ w : E, innerSL v w = 0) → v = 0

namespace PseudoInnerProductSpace

section Generic

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]

section Basic

variable [PseudoInnerProductSpace 𝕜 E]

/-- The pairing evaluated through its continuous sesquilinear map.

The class field `inner_eq_innerSL` is the reverse direction, and is the one to feed to `simp` when
bilinearity is wanted: unfolding to `innerSL` lets the `ContinuousLinearMap.map_*` lemmas do the
algebra. Neither direction is `@[simp]`, so Mathlib's `inner` stays the normal form in the
positive-definite case. -/
lemma innerSL_apply (v w : E) : innerSL v w = inner 𝕜 v w :=
  (PseudoInnerProductSpace.inner_eq_innerSL v w).symm

lemma inner_conj_symm (v w : E) : conj (inner 𝕜 v w) = inner 𝕜 w v := by
  simp only [← innerSL_apply]; exact innerSL_conj_symm v w

lemma eq_zero_of_inner_eq_zero {v : E} (h : ∀ w : E, inner 𝕜 v w = 0) : v = 0 :=
  innerSL_nondegenerate v fun w ↦ (innerSL_apply v w).trans (h w)

lemma eq_zero_of_inner_right_eq_zero {w : E} (h : ∀ v : E, inner 𝕜 v w = 0) : w = 0 := by
  refine eq_zero_of_inner_eq_zero (𝕜 := 𝕜) fun v ↦ ?_
  have hv := congrArg conj (h v)
  rwa [inner_conj_symm, map_zero] at hv

/-! ### Sesquilinearity

These generalise Mathlib's root-level `inner_add_left` and friends from `InnerProductSpace` to the
present weaker class, so they live in this namespace (as `CStarModule.inner_add_right` does for
`CStarModule`). Each is immediate from the continuous sesquilinear map underlying the pairing. -/

@[simp] lemma inner_zero_left (w : E) : inner 𝕜 (0 : E) w = 0 := by
  simp [← innerSL_apply]

@[simp] lemma inner_zero_right (v : E) : inner 𝕜 v (0 : E) = 0 := by
  simp [← innerSL_apply]

@[simp] lemma inner_add_left (u v w : E) :
    inner 𝕜 (u + v) w = inner 𝕜 u w + inner 𝕜 v w := by
  simp [← innerSL_apply]

@[simp] lemma inner_add_right (u v w : E) :
    inner 𝕜 u (v + w) = inner 𝕜 u v + inner 𝕜 u w := by
  simp [← innerSL_apply]

@[simp] lemma inner_neg_left (v w : E) : inner 𝕜 (-v) w = -inner 𝕜 v w := by
  simp [← innerSL_apply]

@[simp] lemma inner_neg_right (v w : E) : inner 𝕜 v (-w) = -inner 𝕜 v w := by
  simp [← innerSL_apply]

@[simp] lemma inner_sub_left (u v w : E) :
    inner 𝕜 (u - v) w = inner 𝕜 u w - inner 𝕜 v w := by
  simp [← innerSL_apply]

@[simp] lemma inner_sub_right (u v w : E) :
    inner 𝕜 u (v - w) = inner 𝕜 u v - inner 𝕜 u w := by
  simp [← innerSL_apply]

@[simp] lemma inner_smul_right (c : 𝕜) (v w : E) :
    inner 𝕜 v (c • w) = c * inner 𝕜 v w := by
  simp [← innerSL_apply]

/-- The first slot is *conjugate*-linear, as for `InnerProductSpace`. Over `ℝ` use
`real_inner_smul_left`. -/
@[simp] lemma inner_smul_left (c : 𝕜) (v w : E) :
    inner 𝕜 (c • v) w = conj c * inner 𝕜 v w := by
  simp [← innerSL_apply]

end Basic

/-! ## Riemannian geometry as a special case -/

section InnerProduct

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Every inner product space is a pseudo-inner product space: positive definiteness is in
particular nondegeneracy.

The `Inner` field is Mathlib's own instance, so `inner 𝕜` denotes the same function on the nose:
every `inner_*` lemma applies verbatim and no bridging lemma is needed. -/
noncomputable instance (priority := 100) _root_.InnerProductSpace.toPseudoInnerProductSpace :
    PseudoInnerProductSpace 𝕜 F where
  toInner := inferInstance
  innerSL := _root_.innerSL 𝕜
  inner_eq_innerSL _ _ := rfl
  innerSL_conj_symm v w := _root_.inner_conj_symm w v
  innerSL_nondegenerate v hv := (inner_self_eq_zero (𝕜 := 𝕜)).mp (hv v)

end InnerProduct

end Generic

section RealTheory

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-! ## The real case

Over `ℝ` conjugation is the identity, so the pairing is a genuine symmetric bilinear form. This is
the setting of pseudo-Riemannian geometry. -/

section Real

variable [PseudoInnerProductSpace ℝ E]

lemma inner_comm (v w : E) : inner ℝ v w = inner ℝ w v := by
  simpa using inner_conj_symm (𝕜 := ℝ) v w

@[simp] lemma real_inner_smul_left (c : ℝ) (v w : E) :
    inner ℝ (c • v) w = c * inner ℝ v w := by
  simp

/-! ### The Levi-Civita rigidity identity -/

/-- A map that is symmetric in its two arguments and antisymmetric against the form in its
outer arguments vanishes.

This is the algebraic content of the uniqueness of the Levi-Civita connection: the difference
tensor `S` of two connections is symmetric when both are torsion-free, and satisfies
`⟪S u v, w⟫ = -⟪S w v, u⟫` when both are metric, and these two together force `S = 0`. Only
symmetry and nondegeneracy of the form are used, so the statement is insensitive to signature. -/
lemma eq_zero_of_symm_of_antisymm {S : E → E → E} (hsymm : ∀ u v, S u v = S v u)
    (hanti : ∀ u v w, inner ℝ (S u v) w = -inner ℝ (S w v) u) (u v : E) :
    S u v = 0 := by
  refine eq_zero_of_inner_eq_zero (𝕜 := ℝ) fun w ↦ ?_
  have h1 := hanti u v w
  have h2 : inner ℝ (S w v) u = inner ℝ (S v w) u := by rw [hsymm w v]
  have h3 := hanti v w u
  have h4 : inner ℝ (S u w) v = inner ℝ (S w u) v := by rw [hsymm u w]
  have h5 := hanti w u v
  have h6 : inner ℝ (S v u) w = inner ℝ (S u v) w := by rw [hsymm v u]
  linarith


end Real

/-! ## The associated bilinear and quadratic forms -/

section Forms

variable [PseudoInnerProductSpace ℝ E]

lemma toBilinForm_isSymm : (innerSL (𝕜 := ℝ) (E := E)).toBilinForm.IsSymm :=
  ⟨fun v w ↦ by simpa [innerSL_apply (𝕜 := ℝ)] using (inner_comm v w)⟩

lemma toBilinForm_nondegenerate : (innerSL (𝕜 := ℝ) (E := E)).toBilinForm.Nondegenerate := by
  constructor
  · exact fun v hv ↦ eq_zero_of_inner_eq_zero fun w ↦ by simpa [innerSL_apply (𝕜 := ℝ)] using hv w
  · exact fun w hw ↦ eq_zero_of_inner_right_eq_zero fun v ↦ by
      simpa [innerSL_apply (𝕜 := ℝ)] using hw v

variable (E) in
/-- The quadratic form `v ↦ inner ℝ v v`. Its `sigNeg` is the index. -/
noncomputable def toQuadraticForm : QuadraticForm ℝ E := (innerSL (𝕜 := ℝ) (E := E)).toQuadraticForm

@[simp]
lemma toQuadraticForm_apply (v : E) : toQuadraticForm E v = inner ℝ v v := innerSL_apply v v

end Forms

/-! ## Building an instance from a bilinear form -/

section OfBilinForm

variable (E) in
/-- Build a pseudo-inner product from a symmetric nondegenerate bilinear form on a
finite-dimensional Hausdorff space. Continuity is automatic there, so no analytic input is
needed; this is how a concrete metric (Minkowski, Schwarzschild, FLRW) is supplied. -/
@[reducible] noncomputable def ofBilinForm [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [T2Space E] [FiniteDimensional ℝ E] (B : LinearMap.BilinForm ℝ E) (hs : B.IsSymm)
    (hn : B.Nondegenerate) : PseudoInnerProductSpace ℝ E where
  toInner := ⟨fun v w ↦ B v w⟩
  innerSL := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E) (F' := ℝ)).toLinearMap ∘ₗ B)
  inner_eq_innerSL _ _ := rfl
  innerSL_conj_symm v w := LinearMap.BilinForm.isSymm_def.mp hs v w
  innerSL_nondegenerate := hn.1

end OfBilinForm

/-! ## Musical isomorphisms -/

section Musical

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
  [FiniteDimensional ℝ E] [PseudoInnerProductSpace ℝ E]

variable (E) in
/-- The musical isomorphism `♭ : E ≃L[ℝ] E⋆`, from `LinearMap.BilinForm.toDual` composed with the
identification of the algebraic and continuous duals in finite dimension. -/
noncomputable def flatEquiv : E ≃L[ℝ] (E →L[ℝ] ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    (((innerSL (𝕜 := ℝ) (E := E)).toBilinForm.toDual toBilinForm_nondegenerate).trans
      (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E) (F' := ℝ)))

@[simp]
lemma flatEquiv_apply (v w : E) : flatEquiv E v w = inner ℝ v w := innerSL_apply v w

variable (E) in
/-- The musical isomorphism `♯ : E⋆ ≃L[ℝ] E`, inverse to `♭`. -/
noncomputable def sharpEquiv : (E →L[ℝ] ℝ) ≃L[ℝ] E := (flatEquiv E).symm

variable (E) in
/-- Index raising `♯ : E⋆ →L[ℝ] E`, as a continuous linear map. -/
noncomputable def sharpL : (E →L[ℝ] ℝ) →L[ℝ] E := (sharpEquiv E).toContinuousLinearMap

lemma sharpL_apply (ω : E →L[ℝ] ℝ) : sharpL E ω = sharpEquiv E ω := rfl

@[simp]
lemma sharpL_innerSL (v : E) : sharpL E (innerSL (𝕜 := ℝ) (E := E) v) = v :=
  (flatEquiv E).symm_apply_apply v

@[simp]
lemma innerSL_sharpL (ω : E →L[ℝ] ℝ) : innerSL (𝕜 := ℝ) (E := E) (sharpL E ω) = ω :=
  (flatEquiv E).apply_symm_apply ω

/-- Pairing with a raised covector is evaluation. -/
@[simp]
lemma inner_sharpL_right (v : E) (ω : E →L[ℝ] ℝ) :
    inner ℝ v (sharpL E ω) = ω v := by
  rw [inner_comm, ← innerSL_apply]
  exact congrFun (congrArg (fun f : E →L[ℝ] ℝ ↦ (f : E → ℝ)) (innerSL_sharpL ω)) v

/-- Pairing with a raised covector is evaluation. -/
@[simp]
lemma inner_sharpL_left (v : E) (ω : E →L[ℝ] ℝ) :
    inner ℝ (sharpL E ω) v = ω v := by
  rw [inner_comm]; exact inner_sharpL_right v ω

/-! ### The induced form on the dual -/

variable (E) in
/-- The form induced on `E⋆` by raising both indices, `(ω₁, ω₂) ↦ ω₁ (ω₂♯)`; for a metric tensor,
the inverse metric `g^{ab}`. -/
noncomputable def dualInnerSL : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E →L[ℝ] ℝ) (F' := (E →L[ℝ] ℝ) →L[ℝ] ℝ)
    { toFun := fun ω : E →L[ℝ] ℝ ↦ ω.comp (sharpL E)
      map_add' := fun ω₁ ω₂ ↦ by ext ω; simp
      map_smul' := fun c ω ↦ by ext ω'; simp }

@[simp]
lemma dualInnerSL_apply (ω₁ ω₂ : E →L[ℝ] ℝ) :
    dualInnerSL E ω₁ ω₂ = ω₁ (sharpL E ω₂) := rfl

lemma dualInnerSL_eq_inner_sharpL (ω₁ ω₂ : E →L[ℝ] ℝ) :
    dualInnerSL E ω₁ ω₂ = inner ℝ (sharpL E ω₁) (sharpL E ω₂) := by
  rw [dualInnerSL_apply, inner_sharpL_left]

lemma dualInnerSL_symm (ω₁ ω₂ : E →L[ℝ] ℝ) :
    dualInnerSL E ω₁ ω₂ = dualInnerSL E ω₂ ω₁ := by
  simp only [dualInnerSL_eq_inner_sharpL]
  exact inner_comm _ _

lemma dualInnerSL_nondegenerate (ω : E →L[ℝ] ℝ)
    (h : ∀ η : E →L[ℝ] ℝ, dualInnerSL E ω η = 0) : ω = 0 := by
  ext v
  simpa only [dualInnerSL_apply, sharpL_innerSL, zero_apply]
    using h (innerSL (𝕜 := ℝ) (E := E) v)

variable (E) in
/-- `E⋆` with the inverse form. Deliberately a `def`: as an instance it would let typeclass
inference loop through iterated duals. -/
@[reducible] noncomputable def dual : PseudoInnerProductSpace ℝ (E →L[ℝ] ℝ) where
  toInner := ⟨fun ω η ↦ dualInnerSL E ω η⟩
  innerSL := dualInnerSL E
  inner_eq_innerSL _ _ := rfl
  innerSL_conj_symm ω η := dualInnerSL_symm ω η
  innerSL_nondegenerate := dualInnerSL_nondegenerate

end Musical

/-! ## The index -/

variable (E : Type*) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [PseudoInnerProductSpace ℝ E]

/-- The index, or negative inertia: the largest dimension of a subspace on which the form is
negative definite. Index `0` is the Riemannian case.

Both inertia indices are provided, and `coindex_add_index_eq_finrank` relates them, so that a
statement can be phrased in either signature convention without an adapter: a Lorentzian form has
index `1` in the `(-, +, …, +)` convention and coindex `1` in the `(+, -, …, -)` one. -/
noncomputable def index : ℕ := sigNeg (toQuadraticForm E)

lemma index_def : index E = sigNeg (toQuadraticForm E) := rfl

/-- The coindex, or positive inertia: the largest dimension of a subspace on which the form is
positive definite. See `index` for the relation between the two conventions. -/
noncomputable def coindex : ℕ := sigPos (toQuadraticForm E)

lemma coindex_def : coindex E = sigPos (toQuadraticForm E) := rfl

/-- Nondegeneracy, restated: the quadratic form has trivial radical. -/
lemma radical_toQuadraticForm_eq_bot : (toQuadraticForm E).radical = ⊥ := by
  rw [QuadraticMap.radical_eq_ker_polarBilin, Submodule.eq_bot_iff]
  intro v hv
  refine eq_zero_of_inner_eq_zero (𝕜 := ℝ) fun w ↦ ?_
  have h0 : QuadraticMap.polar (toQuadraticForm E) v w = 0 := by
    simpa using DFunLike.congr_fun (LinearMap.mem_ker.mp hv) w
  have hpolar : QuadraticMap.polar (toQuadraticForm E) v w = 2 * inner ℝ v w := by
    simp only [QuadraticMap.polar, toQuadraticForm_apply, inner_add_left, inner_add_right,
      inner_comm w v]
    ring
  linarith

variable {E} in
/-- A form of positive coindex lives on a finite-dimensional space: in infinite dimension
`Module.finrank` vanishes, and `QuadraticForm.sigPos` is bounded by it. -/
lemma finiteDimensional_of_coindex_pos (h : 0 < coindex E) : FiniteDimensional ℝ E :=
  Module.finite_of_finrank_pos (lt_of_lt_of_le h (sigPos_le_finrank (toQuadraticForm E)))

variable {E} in
/-- A form of positive index lives on a finite-dimensional space. -/
lemma finiteDimensional_of_index_pos (h : 0 < index E) : FiniteDimensional ℝ E :=
  Module.finite_of_finrank_pos (lt_of_lt_of_le h (sigNeg_le_finrank (toQuadraticForm E)))

variable [FiniteDimensional ℝ E]

/-- **The two inertia indices add up to the dimension.** The form is nondegenerate, so its radical
is trivial and Sylvester's law of inertia leaves nothing else. This is what lets a statement be
translated between the `(+, -, …, -)` and `(-, +, …, +)` conventions. -/
lemma coindex_add_index_eq_finrank : coindex E + index E = Module.finrank ℝ E := by
  have h := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := toQuadraticForm E)
  rwa [radical_toQuadraticForm_eq_bot, finrank_bot, Nat.add_zero] at h

variable {E} in
/-- One vector of negative square already forces positive index: the form is not Riemannian. -/
lemma one_le_index_of_neg {v : E} (hv : v ≠ 0) (h : inner ℝ v v < 0) : 1 ≤ index E := by
  have key : Module.finrank ℝ (ℝ ∙ v : Submodule ℝ E) ≤ sigNeg (toQuadraticForm E) := by
    refine le_sigNeg_of_negDef _ fun x hx ↦ ?_
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp x.2
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hx (Subtype.ext (by simpa using hc.symm))
    have hval : toQuadraticForm E (x : E) = c * c * inner ℝ v v := by
      rw [← hc, ← toQuadraticForm_apply v, QuadraticMap.map_smul]
      simp [smul_eq_mul]
    simp only [QuadraticMap.restrict_apply, neg_apply, hval]
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
  have hfe : ∀ u : E, ((flatEquiv E u : E →L[ℝ] ℝ)) = innerSL u := fun u ↦ by
    ext w; simp [innerSL_apply]
  have key : ∀ u w : E, dualInnerSL E (flatEquiv E u) (flatEquiv E w) = innerSL u w := by
    intro u w
    rw [hfe u, hfe w, dualInnerSL_apply, sharpL_innerSL]
  exact (ContinuousLinearMap.sigNeg_toQuadraticForm_of_congr
    (PseudoInnerProductSpace.innerSL (𝕜 := ℝ) (E := E)) (dualInnerSL E)
    (flatEquiv E).toLinearEquiv key).symm

/-- Riemannian geometry is the index-zero case. -/
@[simp]
lemma index_eq_zero_of_innerProductSpace (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] : index F = 0 :=
  index_eq_zero_of_posDef fun v hv ↦ by
    simpa using real_inner_self_pos.mpr hv

end RealTheory

/-! ## The standard indefinite model -/

section Model

variable (F G : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- The continuous bilinear form `(v, w) ↦ ⟪v.1, w.1⟫ - ⟪v.2, w.2⟫` on `F × G`. -/
noncomputable def prodDiffSL : (F × G) →L[ℝ] (F × G) →L[ℝ] ℝ :=
  ((ContinuousLinearMap.fst ℝ F G).precomp ℝ).comp
      ((_root_.innerSL ℝ).comp (ContinuousLinearMap.fst ℝ F G)) -
    ((ContinuousLinearMap.snd ℝ F G).precomp ℝ).comp
      ((_root_.innerSL ℝ).comp (ContinuousLinearMap.snd ℝ F G))

@[simp]
lemma prodDiffSL_apply (v w : F × G) :
    prodDiffSL F G v w = inner ℝ v.1 w.1 - inner ℝ v.2 w.2 := rfl

lemma prodDiffSL_symm (v w : F × G) : prodDiffSL F G v w = prodDiffSL F G w v := by
  rw [prodDiffSL_apply, prodDiffSL_apply, real_inner_comm w.1 v.1, real_inner_comm w.2 v.2]

lemma prodDiffSL_nondegenerate (v : F × G) (hv : ∀ w, prodDiffSL F G v w = 0) : v = 0 := by
  have h := hv (v.1, -v.2)
  simp only [prodDiffSL_apply, _root_.inner_neg_right, sub_neg_eq_add] at h
  have h1 : (0 : ℝ) ≤ inner ℝ v.1 v.1 := real_inner_self_nonneg
  have h2 : (0 : ℝ) ≤ inner ℝ v.2 v.2 := real_inner_self_nonneg
  have e1 : v.1 = 0 := inner_self_eq_zero (𝕜 := ℝ) |>.mp (by linarith)
  have e2 : v.2 = 0 := inner_self_eq_zero (𝕜 := ℝ) |>.mp (by linarith)
  exact Prod.ext e1 e2

/-- The pseudo-inner product on `F × G` given by `⟪(f, g), (f', g')⟫ = ⟪f, f'⟫ - ⟪g, g'⟫`.

This is the standard model of an indefinite form: by Sylvester's law of inertia every
finite-dimensional pseudo-inner product space is isometric to one of these, with `F` of dimension
the coindex and `G` of dimension the index (`coindex_prodDiff`, `index_prodDiff`). Taking
`G := ℝ` produces the Lorentzian signature; `F := EuclideanSpace ℝ (Fin 3)` with `G := ℝ` is
Minkowski spacetime in the `(-, +, +, +)` convention.

Deliberately a `def` and not an instance: `F × G` already carries the *positive* inner product, so
registering this globally would create a diamond. Use it through `letI`. -/
@[reducible] noncomputable def prodDiff : PseudoInnerProductSpace ℝ (F × G) where
  toInner := ⟨fun v w ↦ prodDiffSL F G v w⟩
  innerSL := prodDiffSL F G
  inner_eq_innerSL _ _ := rfl
  -- over `ℝ` the conjugation is the identity, so this is plain symmetry of the form
  innerSL_conj_symm := prodDiffSL_symm F G
  innerSL_nondegenerate := prodDiffSL_nondegenerate F G

@[simp]
lemma prodDiff_inner (v w : F × G) :
    letI := prodDiff F G
    inner ℝ v w = inner ℝ v.1 w.1 - inner ℝ v.2 w.2 := rfl

section Signature

private lemma posDef_restrict_fst :
    letI := prodDiff F G
    ((toQuadraticForm (F × G)).restrict (Submodule.fst ℝ F G)).PosDef := by
  let _ := prodDiff F G
  rintro ⟨v, hv⟩ hne
  have hv2 : v.2 = 0 := by simpa [Submodule.fst] using hv
  have hv1 : v.1 ≠ 0 := fun h ↦ hne (Subtype.ext (Prod.ext h hv2))
  simpa [QuadraticMap.restrict_apply, hv2] using real_inner_self_pos.mpr hv1

private lemma posDef_restrict_snd :
    letI := prodDiff F G
    ((-toQuadraticForm (F × G)).restrict (Submodule.snd ℝ F G)).PosDef := by
  let _ := prodDiff F G
  rintro ⟨v, hv⟩ hne
  have hv1 : v.1 = 0 := by simpa [Submodule.snd] using hv
  have hv2 : v.2 ≠ 0 := fun h ↦ hne (Subtype.ext (Prod.ext hv1 h))
  simpa [QuadraticMap.restrict_apply, hv1] using real_inner_self_pos.mpr hv2

variable [FiniteDimensional ℝ F] [FiniteDimensional ℝ G]

/-- **The model realises every signature.** The positive part of `F × G` has dimension
`finrank ℝ F`. -/
lemma coindex_prodDiff :
    letI := prodDiff F G
    coindex (F × G) = Module.finrank ℝ F := by
  let _ := prodDiff F G
  have hF : Module.finrank ℝ F ≤ coindex (F × G) := by
    have h := le_sigPos_of_posDef (toQuadraticForm (F × G)) (posDef_restrict_fst F G)
    rwa [(Submodule.fstEquiv ℝ F G).finrank_eq] at h
  have hG : Module.finrank ℝ G ≤ index (F × G) := by
    have h := le_sigNeg_of_negDef (toQuadraticForm (F × G)) (posDef_restrict_snd F G)
    rwa [(Submodule.sndEquiv ℝ F G).finrank_eq] at h
  have hsum := coindex_add_index_eq_finrank (F × G)
  rw [Module.finrank_prod] at hsum
  lia

/-- The negative part of `F × G` has dimension `finrank ℝ G`; in particular every index is
attained, so `PseudoInnerProductSpace` is non-vacuous in every signature. -/
lemma index_prodDiff :
    letI := prodDiff F G
    index (F × G) = Module.finrank ℝ G := by
  let _ := prodDiff F G
  have hsum := coindex_add_index_eq_finrank (F × G)
  rw [Module.finrank_prod, coindex_prodDiff] at hsum
  lia

end Signature

end Model

end PseudoInnerProductSpace
