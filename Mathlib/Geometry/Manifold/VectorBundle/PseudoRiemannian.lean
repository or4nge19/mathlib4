/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.InnerProductSpace.Pseudo
public import Mathlib.Geometry.Manifold.VectorBundle.HomInverse
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Topology.VectorBundle.PseudoRiemannian

/-!
# Pseudo-Riemannian vector bundles

A vector bundle whose fibres carry a `PseudoInnerProductSpace` is *pseudo-Riemannian* when that
form varies smoothly with the base point.

This is the smoothness class for bundle metrics; it does **not** assume positivity, so fibres need
only be topological vector spaces and the API also serves normal, gauge and spinor bundles.
Riemannian bundles are the special case: `InnerProductSpace.toPseudoInnerProductSpace` supplies the
fibrewise structure, so a bundle with inner-product fibres satisfies this class with no adapter and
`Mathlib/Geometry/Manifold/VectorBundle/Riemannian.lean` restates the consequences in terms of
`inner`.

The standard variable block is
```
variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, PseudoInnerProductSpace ℝ (E x)] [FiberBundle F E] [VectorBundle ℝ F E]
  [IsManifold IB n B] [ContMDiffVectorBundle n F E IB]
  [IsContMDiffPseudoRiemannianBundle IB n F E]
```

## Main definitions

* `IsContMDiffPseudoRiemannianBundle IB n F E`: the fibrewise form is `C^n`.
* `Bundle.ContMDiffPseudoRiemannianMetric IB n F E`: metric data, used to build instances.

## Main results

* `ContMDiffWithinAt.inner_bundle`, `ContMDiffWithinAt.innerSL_bundle`: pairing two smooth
  sections and lowering an index preserve smoothness — the inputs to the Koszul formula.
* `injective_inner_mdifferentiableAt_section`: nondegeneracy in the form the Levi-Civita
  construction uses — a fibre vector is determined by its pairings with differentiable sections.
* `Bundle.isLocallyConstant_index`: the fibrewise index is locally constant. This is the smooth
  corollary of `Bundle.isLocallyConstant_index_of_continuous`, which is proved with no manifold
  structure and no smoothness in `Mathlib/Topology/VectorBundle/PseudoRiemannian.lean`.

## Acknowledgements

The design follows Sébastien Gouëzel's proposal on Zulip, see [Zulip](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/The.20future.20of.20pseudo-Riemannian.20manifolds/with/619509253).

## Tags

pseudo-Riemannian, vector bundle, signature, index, Levi-Civita
-/

@[expose] public section

open Bundle ContinuousLinearMap ENat Filter Module Set
open scoped Manifold Bundle Topology ContDiff

/-! ## The smoothness class -/

section Class

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n n' : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, PseudoInnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]

variable (IB n F E) in
/-- The fibrewise pseudo-inner product depends `C^n`-smoothly on the base point.

As for the Riemannian metrics it generalizes, this is phrased as the existence of a smooth family
agreeing
with the fibrewise structure, keeping the class `Prop`-valued. -/
class IsContMDiffPseudoRiemannianBundle : Prop where
  exists_contMDiff : ∃ g : ∀ x : B, E x →L[ℝ] E x →L[ℝ] ℝ,
    ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun b ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (g b))
    ∧ ∀ (x : B) (v w : E x), inner ℝ v w = g x v w

lemma IsContMDiffPseudoRiemannianBundle.of_le
    [h : IsContMDiffPseudoRiemannianBundle IB n F E] (h' : n' ≤ n) :
    IsContMDiffPseudoRiemannianBundle IB n' F E := by
  rcases h.exists_contMDiff with ⟨g, g_smooth, hg⟩
  exact ⟨g, g_smooth.of_le h', hg⟩

instance {a : ℕ∞ω} [IsContMDiffPseudoRiemannianBundle IB ∞ F E] [h : LEInfty a] :
    IsContMDiffPseudoRiemannianBundle IB a F E :=
  IsContMDiffPseudoRiemannianBundle.of_le h.out

instance {a : ℕ∞ω} [IsContMDiffPseudoRiemannianBundle IB ω F E] :
    IsContMDiffPseudoRiemannianBundle IB a F E :=
  IsContMDiffPseudoRiemannianBundle.of_le le_top

instance [IsContMDiffPseudoRiemannianBundle IB 1 F E] :
    IsContMDiffPseudoRiemannianBundle IB 0 F E :=
  IsContMDiffPseudoRiemannianBundle.of_le zero_le_one

instance [IsContMDiffPseudoRiemannianBundle IB 2 F E] :
    IsContMDiffPseudoRiemannianBundle IB 1 F E :=
  IsContMDiffPseudoRiemannianBundle.of_le one_le_two

instance [IsContMDiffPseudoRiemannianBundle IB 3 F E] :
    IsContMDiffPseudoRiemannianBundle IB 2 F E :=
  IsContMDiffPseudoRiemannianBundle.of_le (n := 3) (by norm_cast)

section Trivial

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [PseudoInnerProductSpace ℝ F₁]

set_option backward.isDefEq.respectTransparency false in
/-- A trivial bundle whose model fibre is a pseudo-inner product space is pseudo-Riemannian. -/
instance : IsContMDiffPseudoRiemannianBundle IB n F₁ (Bundle.Trivial B F₁) := by
  refine ⟨fun _ ↦ PseudoInnerProductSpace.innerSL (𝕜 := ℝ) (E := F₁), fun x ↦ ?_,
    fun _ v w ↦ PseudoInnerProductSpace.inner_eq_innerSL v w⟩
  simp only [contMDiffAt_section]
  convert! contMDiffAt_const (c := PseudoInnerProductSpace.innerSL (𝕜 := ℝ) (E := F₁))
  ext v w
  simp [hom_trivializationAt_apply, inCoordinates]

end Trivial

end Class

namespace Bundle

/-! ## Nondegeneracy: a fibre vector is determined by its pairings -/

section Injective

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, PseudoInnerProductSpace ℝ (E x)] [FiberBundle F E]

variable (IB F E) in
/-- A vector in `E x` is determined by its pairings with the sections that are differentiable
at `x`.

This is nondegeneracy of the fibrewise form, transported along `FiberBundle.extend`: no positivity
and no finiteness of rank is involved, so this is the form in which the Levi-Civita construction
actually needs it. -/
lemma injective_inner_mdifferentiableAt_section (x : B) :
    Function.Injective (fun X₀ : E x ↦
      fun (Z : Π x, E x) (_ : MDiffAt (T% Z) x) ↦ inner ℝ X₀ (Z x)) := by
  intro X₀ Y₀ h
  refine sub_eq_zero.mp (PseudoInnerProductSpace.eq_zero_of_inner_eq_zero (𝕜 := ℝ) fun w ↦ ?_)
  have hw := congr($h _ (FiberBundle.mdifferentiableAt_extend (V := E) _ _ w))
  simp only [FiberBundle.extend_apply_self] at hw
  rw [PseudoInnerProductSpace.inner_eq_innerSL, map_sub, sub_apply,
    PseudoInnerProductSpace.innerSL_apply, PseudoInnerProductSpace.innerSL_apply, hw, sub_self]

variable (IB F E) in
/-- A vector in `E x` is determined by its pairings with the sections that are `C^n` at `x`. -/
lemma injective_inner_contMDiffAt_section (n : ℕ∞ω) (x : B) :
    Function.Injective (fun X₀ : E x ↦
      fun (Z : Π x, E x) (_ : CMDiffAt n (T% Z) x) ↦ inner ℝ X₀ (Z x)) := by
  intro X₀ Y₀ h
  refine sub_eq_zero.mp (PseudoInnerProductSpace.eq_zero_of_inner_eq_zero (𝕜 := ℝ) fun w ↦ ?_)
  have hw := congr($h _ (FiberBundle.contMDiffAt_extend (V := E) _ _ w))
  simp only [FiberBundle.extend_apply_self] at hw
  rw [PseudoInnerProductSpace.inner_eq_innerSL, map_sub, sub_apply,
    PseudoInnerProductSpace.innerSL_apply, PseudoInnerProductSpace.innerSL_apply, hw, sub_self]

end Injective

/-! ## Smoothness of the pairing -/

section ContMDiff

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, PseudoInnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [h : IsContMDiffPseudoRiemannianBundle IB n F E]
  {b : M → B} {v w : ∀ x, E (b x)} {s : Set M} {x : M}

/-- The pairing of two smooth maps into the fibres is smooth. -/
lemma _root_.ContMDiffWithinAt.inner_bundle
    (hv : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) s x)
    (hw : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E)) s x) :
    ContMDiffWithinAt IM 𝓘(ℝ) n (fun m ↦ inner ℝ (v m) (w m)) s x := by
  rcases h.exists_contMDiff with ⟨g, g_smooth, hg⟩
  have hb : ContMDiffWithinAt IM IB n b s x := by
    simp only [contMDiffWithinAt_totalSpace] at hv
    exact hv.1
  simp only [hg]
  have key : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ)) n
      (fun m ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial B ℝ) (b m) (g (b m) (v m) (w m))) s x := by
    apply ContMDiffWithinAt.clm_bundle_apply₂ (F₁ := F) (F₂ := F)
    · exact ContMDiffAt.comp_contMDiffWithinAt x g_smooth.contMDiffAt hb
    · exact hv
    · exact hw
  simp only [contMDiffWithinAt_totalSpace] at key
  exact key.2

/-- The pairing of two smooth maps into the fibres is smooth. -/
lemma _root_.ContMDiffAt.inner_bundle
    (hv : ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) x)
    (hw : ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E)) x) :
    ContMDiffAt IM 𝓘(ℝ) n (fun m ↦ inner ℝ (v m) (w m)) x :=
  ContMDiffWithinAt.inner_bundle hv hw

/-- The pairing of two smooth maps into the fibres is smooth. -/
lemma _root_.ContMDiffOn.inner_bundle
    (hv : ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) s)
    (hw : ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E)) s) :
    ContMDiffOn IM 𝓘(ℝ) n (fun m ↦ inner ℝ (v m) (w m)) s :=
  fun x hx ↦ (hv x hx).inner_bundle (hw x hx)

/-- The pairing of two smooth maps into the fibres is smooth. -/
lemma _root_.ContMDiff.inner_bundle
    (hv : ContMDiff IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)))
    (hw : ContMDiff IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E))) :
    ContMDiff IM 𝓘(ℝ) n (fun m ↦ inner ℝ (v m) (w m)) :=
  fun x ↦ (hv x).inner_bundle (hw x)

end ContMDiff

section MDifferentiable

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, PseudoInnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [h : IsContMDiffPseudoRiemannianBundle IB 1 F E]
  {b : M → B} {v w : ∀ x, E (b x)} {s : Set M} {x : M}

/-- The pairing of two differentiable maps into the fibres is differentiable. -/
lemma _root_.MDifferentiableWithinAt.inner_bundle
    (hv : MDifferentiableWithinAt IM (IB.prod 𝓘(ℝ, F)) (fun m ↦ (v m : TotalSpace F E)) s x)
    (hw : MDifferentiableWithinAt IM (IB.prod 𝓘(ℝ, F)) (fun m ↦ (w m : TotalSpace F E)) s x) :
    MDifferentiableWithinAt IM 𝓘(ℝ) (fun m ↦ inner ℝ (v m) (w m)) s x := by
  rcases h.exists_contMDiff with ⟨g, g_smooth, hg⟩
  have hb : MDifferentiableWithinAt IM IB b s x := by
    simp only [mdifferentiableWithinAt_totalSpace] at hv
    exact hv.1
  simp only [hg]
  have key : MDifferentiableWithinAt IM (IB.prod 𝓘(ℝ))
      (fun m ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial B ℝ) (b m) (g (b m) (v m) (w m))) s x := by
    apply MDifferentiableWithinAt.clm_bundle_apply₂ (F₁ := F) (F₂ := F)
    · exact MDifferentiableAt.comp_mdifferentiableWithinAt x
        (g_smooth.mdifferentiableAt one_ne_zero) hb
    · exact hv
    · exact hw
  simp only [mdifferentiableWithinAt_totalSpace] at key
  exact key.2

/-- The pairing of two differentiable maps into the fibres is differentiable. -/
lemma _root_.MDifferentiableAt.inner_bundle
    (hv : MDifferentiableAt IM (IB.prod 𝓘(ℝ, F)) (fun m ↦ (v m : TotalSpace F E)) x)
    (hw : MDifferentiableAt IM (IB.prod 𝓘(ℝ, F)) (fun m ↦ (w m : TotalSpace F E)) x) :
    MDifferentiableAt IM 𝓘(ℝ) (fun m ↦ inner ℝ (v m) (w m)) x :=
  MDifferentiableWithinAt.inner_bundle hv hw

/-- The pairing of two differentiable maps into the fibres is differentiable. -/
lemma _root_.MDifferentiableOn.inner_bundle
    (hv : MDifferentiableOn IM (IB.prod 𝓘(ℝ, F)) (fun m ↦ (v m : TotalSpace F E)) s)
    (hw : MDifferentiableOn IM (IB.prod 𝓘(ℝ, F)) (fun m ↦ (w m : TotalSpace F E)) s) :
    MDifferentiableOn IM 𝓘(ℝ) (fun m ↦ inner ℝ (v m) (w m)) s :=
  fun x hx ↦ (hv x hx).inner_bundle (hw x hx)

/-- The pairing of two differentiable maps into the fibres is differentiable. -/
lemma _root_.MDifferentiable.inner_bundle
    (hv : MDifferentiable IM (IB.prod 𝓘(ℝ, F)) (fun m ↦ (v m : TotalSpace F E)))
    (hw : MDifferentiable IM (IB.prod 𝓘(ℝ, F)) (fun m ↦ (w m : TotalSpace F E))) :
    MDifferentiable IM 𝓘(ℝ) (fun m ↦ inner ℝ (v m) (w m)) :=
  fun x ↦ (hv x).inner_bundle (hw x)

end MDifferentiable

/-! ## Smoothness of index lowering -/

section Flat

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, PseudoInnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [h : IsContMDiffPseudoRiemannianBundle IB n F E]
  {b : M → B} {v : ∀ x, E (b x)} {s : Set M} {x : M}

variable (IB n F E) in
/-- Index lowering is a smooth section of `Hom(E, E⋆)`. -/
lemma contMDiff_innerSL :
    ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun z : B ↦ E z →L[ℝ] E z →L[ℝ] ℝ) y
        (PseudoInnerProductSpace.innerSL (𝕜 := ℝ) (E := E y))) := by
  obtain ⟨g, g_smooth, hg⟩ := h.exists_contMDiff
  have hEq : ∀ y : B, PseudoInnerProductSpace.innerSL (𝕜 := ℝ) (E := (E y)) = g y := fun y ↦ by
    ext w w'; rw [PseudoInnerProductSpace.innerSL_apply]; exact hg y w w'
  simpa only [hEq] using g_smooth

/-- Index lowering sends smooth sections to smooth covector fields. -/
lemma _root_.ContMDiffWithinAt.innerSL_bundle
    (hv : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) s x) :
    ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun y : B ↦ E y →L[ℝ] ℝ) (b m)
        (PseudoInnerProductSpace.innerSL (𝕜 := ℝ) (E := (E (b m))) (v m))) s x := by
  have hb : ContMDiffWithinAt IM IB n b s x := by
    simp only [contMDiffWithinAt_totalSpace] at hv
    exact hv.1
  exact ContMDiffWithinAt.clm_bundle_apply (F₁ := F) (F₂ := F →L[ℝ] ℝ)
    (ContMDiffAt.comp_contMDiffWithinAt x (contMDiff_innerSL IB n F E).contMDiffAt hb) hv

/-- Index lowering sends smooth sections to smooth covector fields. -/
lemma _root_.ContMDiffAt.innerSL_bundle
    (hv : ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) x) :
    ContMDiffAt IM (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun y : B ↦ E y →L[ℝ] ℝ) (b m)
        (PseudoInnerProductSpace.innerSL (𝕜 := ℝ) (E := (E (b m))) (v m))) x :=
  ContMDiffWithinAt.innerSL_bundle hv

/-- Index lowering sends smooth sections to smooth covector fields. -/
lemma _root_.ContMDiffOn.innerSL_bundle
    (hv : ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) s) :
    ContMDiffOn IM (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun y : B ↦ E y →L[ℝ] ℝ) (b m)
        (PseudoInnerProductSpace.innerSL (𝕜 := ℝ) (E := (E (b m))) (v m))) s :=
  fun x hx ↦ (hv x hx).innerSL_bundle

/-- Index lowering sends smooth sections to smooth covector fields. -/
lemma _root_.ContMDiff.innerSL_bundle
    (hv : ContMDiff IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E))) :
    ContMDiff IM (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun y : B ↦ E y →L[ℝ] ℝ) (b m)
        (PseudoInnerProductSpace.innerSL (𝕜 := ℝ) (E := (E (b m))) (v m))) :=
  fun x ↦ (hv x).innerSL_bundle

end Flat

/-! ## Smoothness of index raising -/

section Sharp

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℝ (E x)]
  [∀ x, T2Space (E x)] [∀ x, FiniteDimensional ℝ (E x)]
  [∀ x, PseudoInnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]

variable (IB n F E) in
/-- Index raising is a smooth section of `Hom(E⋆, E)`.

This is `ContMDiff.clm_bundle_symm` applied to `♭`: no metric-specific argument is involved, only
that inverting a smooth fibrewise isomorphism is smooth. -/
lemma contMDiff_sharpL [h : IsContMDiffPseudoRiemannianBundle IB n F E] :
    ContMDiff IB (IB.prod 𝓘(ℝ, (F →L[ℝ] ℝ) →L[ℝ] F)) n
      (fun y ↦ TotalSpace.mk' ((F →L[ℝ] ℝ) →L[ℝ] F)
        (E := fun z : B ↦ (E z →L[ℝ] ℝ) →L[ℝ] E z) y
        (PseudoInnerProductSpace.sharpL (E y))) := by
  refine ContMDiff.clm_bundle_symm (fun y ↦ PseudoInnerProductSpace.flatEquiv (E y)) ?_
  have hEq : ∀ y : B,
      ((PseudoInnerProductSpace.flatEquiv (E y) : E y ≃L[ℝ] (E y →L[ℝ] ℝ)) :
        E y →L[ℝ] (E y →L[ℝ] ℝ)) = PseudoInnerProductSpace.innerSL (𝕜 := ℝ) (E := (E y)) := by
    intro y; ext v w; rfl
  simpa only [hEq] using contMDiff_innerSL IB n F E

variable
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {b : M → B} {η : ∀ x, E (b x) →L[ℝ] ℝ} {s : Set M} {x : M}

/-- Index raising sends smooth covector fields to smooth vector fields. -/
lemma _root_.ContMDiffWithinAt.sharpL_bundle [IsContMDiffPseudoRiemannianBundle IB n F E]
    (hη : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun y : B ↦ E y →L[ℝ] ℝ) (b m) (η m)) s x) :
    ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n
      (fun m ↦ TotalSpace.mk' F (b m) (PseudoInnerProductSpace.sharpL (E (b m)) (η m))) s x := by
  have hb : ContMDiffWithinAt IM IB n b s x := by
    simp only [contMDiffWithinAt_totalSpace] at hη
    exact hη.1
  exact ContMDiffWithinAt.clm_bundle_apply (F₁ := F →L[ℝ] ℝ) (F₂ := F)
    (E₁ := fun y : B ↦ E y →L[ℝ] ℝ) (E₂ := E)
    (ContMDiffAt.comp_contMDiffWithinAt x (contMDiff_sharpL IB n F E).contMDiffAt hb) hη

/-- Index raising sends smooth covector fields to smooth vector fields. -/
lemma _root_.ContMDiffAt.sharpL_bundle [IsContMDiffPseudoRiemannianBundle IB n F E]
    (hη : ContMDiffAt IM (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun y : B ↦ E y →L[ℝ] ℝ) (b m) (η m)) x) :
    ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n
      (fun m ↦ TotalSpace.mk' F (b m) (PseudoInnerProductSpace.sharpL (E (b m)) (η m))) x :=
  ContMDiffWithinAt.sharpL_bundle hη

/-- Index raising sends smooth covector fields to smooth vector fields. -/
lemma _root_.ContMDiffOn.sharpL_bundle [IsContMDiffPseudoRiemannianBundle IB n F E]
    (hη : ContMDiffOn IM (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun y : B ↦ E y →L[ℝ] ℝ) (b m) (η m)) s) :
    ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n
      (fun m ↦ TotalSpace.mk' F (b m) (PseudoInnerProductSpace.sharpL (E (b m)) (η m))) s :=
  fun x hx ↦ (hη x hx).sharpL_bundle

/-- Index raising sends smooth covector fields to smooth vector fields. -/
lemma _root_.ContMDiff.sharpL_bundle [IsContMDiffPseudoRiemannianBundle IB n F E]
    (hη : ContMDiff IM (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun y : B ↦ E y →L[ℝ] ℝ) (b m) (η m))) :
    ContMDiff IM (IB.prod 𝓘(ℝ, F)) n
      (fun m ↦ TotalSpace.mk' F (b m) (PseudoInnerProductSpace.sharpL (E (b m)) (η m))) :=
  fun x ↦ (hη x).sharpL_bundle

/-- Index raising sends differentiable covector fields to differentiable vector fields. -/
lemma _root_.MDifferentiableWithinAt.sharpL_bundle
    [IsContMDiffPseudoRiemannianBundle IB 1 F E]
    (hη : MDifferentiableWithinAt IM (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ))
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun y : B ↦ E y →L[ℝ] ℝ) (b m) (η m)) s x) :
    MDifferentiableWithinAt IM (IB.prod 𝓘(ℝ, F))
      (fun m ↦ TotalSpace.mk' F (b m) (PseudoInnerProductSpace.sharpL (E (b m)) (η m))) s x := by
  have hb : MDifferentiableWithinAt IM IB b s x := by
    simp only [mdifferentiableWithinAt_totalSpace] at hη
    exact hη.1
  exact MDifferentiableWithinAt.clm_bundle_apply (F₁ := F →L[ℝ] ℝ) (F₂ := F)
    (E₁ := fun y : B ↦ E y →L[ℝ] ℝ) (E₂ := E)
    (MDifferentiableAt.comp_mdifferentiableWithinAt x
      ((contMDiff_sharpL IB 1 F E).mdifferentiableAt one_ne_zero) hb) hη

/-- Index raising sends differentiable covector fields to differentiable vector fields. -/
lemma _root_.MDifferentiableAt.sharpL_bundle [IsContMDiffPseudoRiemannianBundle IB 1 F E]
    (hη : MDifferentiableAt IM (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ))
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun y : B ↦ E y →L[ℝ] ℝ) (b m) (η m)) x) :
    MDifferentiableAt IM (IB.prod 𝓘(ℝ, F))
      (fun m ↦ TotalSpace.mk' F (b m) (PseudoInnerProductSpace.sharpL (E (b m)) (η m))) x :=
  MDifferentiableWithinAt.sharpL_bundle hη

/-- Index raising sends differentiable covector fields to differentiable vector fields. -/
lemma _root_.MDifferentiableOn.sharpL_bundle [IsContMDiffPseudoRiemannianBundle IB 1 F E]
    (hη : MDifferentiableOn IM (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ))
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun y : B ↦ E y →L[ℝ] ℝ) (b m) (η m)) s) :
    MDifferentiableOn IM (IB.prod 𝓘(ℝ, F))
      (fun m ↦ TotalSpace.mk' F (b m) (PseudoInnerProductSpace.sharpL (E (b m)) (η m))) s :=
  fun x hx ↦ (hη x hx).sharpL_bundle

/-- Index raising sends differentiable covector fields to differentiable vector fields. -/
lemma _root_.MDifferentiable.sharpL_bundle [IsContMDiffPseudoRiemannianBundle IB 1 F E]
    (hη : MDifferentiable IM (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ))
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun y : B ↦ E y →L[ℝ] ℝ) (b m) (η m))) :
    MDifferentiable IM (IB.prod 𝓘(ℝ, F))
      (fun m ↦ TotalSpace.mk' F (b m) (PseudoInnerProductSpace.sharpL (E (b m)) (η m))) :=
  fun x ↦ (hη x).sharpL_bundle

end Sharp

section MDifferentiableFlat

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, PseudoInnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [IsContMDiffPseudoRiemannianBundle IB 1 F E]
  {b : M → B} {v : ∀ x, E (b x)} {s : Set M} {x : M}

/-- Index lowering sends differentiable sections to differentiable covector fields. -/
lemma _root_.MDifferentiableWithinAt.innerSL_bundle
    (hv : MDifferentiableWithinAt IM (IB.prod 𝓘(ℝ, F)) (fun m ↦ (v m : TotalSpace F E)) s x) :
    MDifferentiableWithinAt IM (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ))
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun y : B ↦ E y →L[ℝ] ℝ) (b m)
        (PseudoInnerProductSpace.innerSL (𝕜 := ℝ) (E := (E (b m))) (v m))) s x := by
  have hb : MDifferentiableWithinAt IM IB b s x := by
    simp only [mdifferentiableWithinAt_totalSpace] at hv
    exact hv.1
  exact MDifferentiableWithinAt.clm_bundle_apply (F₁ := F) (F₂ := F →L[ℝ] ℝ)
    (MDifferentiableAt.comp_mdifferentiableWithinAt x
      ((contMDiff_innerSL IB 1 F E).mdifferentiableAt one_ne_zero) hb) hv

/-- Index lowering sends differentiable sections to differentiable covector fields. -/
lemma _root_.MDifferentiableAt.innerSL_bundle
    (hv : MDifferentiableAt IM (IB.prod 𝓘(ℝ, F)) (fun m ↦ (v m : TotalSpace F E)) x) :
    MDifferentiableAt IM (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ))
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun y : B ↦ E y →L[ℝ] ℝ) (b m)
        (PseudoInnerProductSpace.innerSL (𝕜 := ℝ) (E := (E (b m))) (v m))) x :=
  MDifferentiableWithinAt.innerSL_bundle hv

/-- Index lowering sends differentiable sections to differentiable covector fields. -/
lemma _root_.MDifferentiableOn.innerSL_bundle
    (hv : MDifferentiableOn IM (IB.prod 𝓘(ℝ, F)) (fun m ↦ (v m : TotalSpace F E)) s) :
    MDifferentiableOn IM (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ))
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun y : B ↦ E y →L[ℝ] ℝ) (b m)
        (PseudoInnerProductSpace.innerSL (𝕜 := ℝ) (E := (E (b m))) (v m))) s :=
  fun x hx ↦ (hv x hx).innerSL_bundle

/-- Index lowering sends differentiable sections to differentiable covector fields. -/
lemma _root_.MDifferentiable.innerSL_bundle
    (hv : MDifferentiable IM (IB.prod 𝓘(ℝ, F)) (fun m ↦ (v m : TotalSpace F E))) :
    MDifferentiable IM (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ))
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun y : B ↦ E y →L[ℝ] ℝ) (b m)
        (PseudoInnerProductSpace.innerSL (𝕜 := ℝ) (E := (E (b m))) (v m))) :=
  fun x ↦ (hv x).innerSL_bundle

end MDifferentiableFlat

/-! ## Bundled smooth pseudo-Riemannian metrics -/

section Construction

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]

variable (IB n F E) in
/-- A `C^n` pseudo-Riemannian metric along a vector bundle, used to build instances via
`toPseudoInnerProductSpace`.

Unlike `Bundle.ContMDiffRiemannianMetric` there is no von Neumann boundedness field: it is needed
there only to build a norm, and an indefinite form induces none. -/
structure ContMDiffPseudoRiemannianMetric where
  /-- The fibrewise bilinear form. -/
  metric (b : B) : E b →L[ℝ] E b →L[ℝ] ℝ
  /-- Symmetry of the form. -/
  symm (b : B) (v w : E b) : metric b v w = metric b w v
  /-- Nondegeneracy of the form. -/
  nondegenerate (b : B) (v : E b) (hv : ∀ w : E b, metric b v w = 0) : v = 0
  /-- Smoothness of the form as a section of the bundle of bilinear forms. -/
  contMDiff : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
    (fun b ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (metric b))

namespace ContMDiffPseudoRiemannianMetric

/-- The fibrewise pseudo-inner product structure carried by a smooth pseudo-Riemannian metric. -/
@[reducible] noncomputable def toPseudoInnerProductSpace
    (g : ContMDiffPseudoRiemannianMetric IB n F E) (b : B) :
    PseudoInnerProductSpace ℝ (E b) where
  toInner := ⟨fun v w ↦ g.metric b v w⟩
  innerSL := g.metric b
  inner_eq_innerSL _ _ := rfl
  innerSL_conj_symm := g.symm b
  innerSL_nondegenerate := g.nondegenerate b

/-- A smooth metric makes the bundle a smooth pseudo-Riemannian bundle. -/
instance (g : ContMDiffPseudoRiemannianMetric IB n F E) :
    letI : ∀ b : B, PseudoInnerProductSpace ℝ (E b) := g.toPseudoInnerProductSpace
    IsContMDiffPseudoRiemannianBundle IB n F E :=
  letI : ∀ b : B, PseudoInnerProductSpace ℝ (E b) := g.toPseudoInnerProductSpace
  ⟨g.metric, g.contMDiff, fun _ _ _ ↦ rfl⟩

end ContMDiffPseudoRiemannianMetric

end Construction

section IndexSmooth

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, PseudoInnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]

/-- The index of a smooth pseudo-Riemannian bundle metric is locally constant.

The smoothness exponent `n` is explicit: it is pinned down only by the instance argument, so
leaving it implicit would force every call site to supply it by name. -/
theorem isLocallyConstant_index (n : ℕ∞ω) [h : IsContMDiffPseudoRiemannianBundle IB n F E] :
    IsLocallyConstant (fun x ↦ PseudoInnerProductSpace.index (E x)) := by
  obtain ⟨g, g_smooth, hg⟩ := h.exists_contMDiff
  exact isLocallyConstant_index_of_continuous g g_smooth.continuous hg

end IndexSmooth

end Bundle
