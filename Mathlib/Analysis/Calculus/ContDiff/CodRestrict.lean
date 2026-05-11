/-
Copyright (c) 2026 Axiomatic-AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.TangentCone.Basic
import Mathlib.Analysis.Calculus.TangentCone.Defs
import Mathlib.Analysis.Calculus.TangentCone.Seq
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.UniqueDifferential
import Mathlib.Topology.Maps.Basic

/-!
# Smooth and analytic codomain restriction to closed submodules

This file isolates the ambient Banach-space calculus needed to descend smoothness and
analyticity through closed submodules.

## Mathematical Framework

Descending differential and analytic properties to a closed submodule $p \subseteq Y$ relies
on two fundamental principles from infinite-dimensional functional analysis:

1. **The Quotient Map Trick (Smoothness)**: Following Lang's *Fundamentals of Differential
   Geometry*, mapping into a closed submodule $p$ is topologically equivalent to stating that
   the composition with the continuous linear quotient map $\pi : Y \to Y/p$ is identically zero.
   Since Fréchet derivatives are canonical and respect continuous linear maps, the chain rule
   yields $\pi \circ D^n f = D^n(\pi \circ f) = 0$. This guarantees that all iterated derivatives
   inherently map into $p$.

2. **Taylor-Coefficient Induction (Analyticity)**: For analytic functions and polynomials, the
   relevant data are packaged by `HasFTaylorSeriesUpToOn`: the zeroth coefficient is the function
   itself, and successor coefficients are linked to Fréchet derivatives via `curryLeft`. Starting
   from the assumption that the function maps into a closed submodule `p`, one proves inductively
   that every Taylor coefficient takes values in `p`, using the codomain-restriction theorem for
   derivatives at each successor step. The resulting Taylor family can then be corestricted
   coefficientwise to `p`.

## Main statements

* Derivatives (`iteratedFDeriv`, `fderiv`) of maps valued in a closed submodule inherently
  land in that submodule.
* Codomain restriction preserves differentiability (`HasFDerivAt`, `DifferentiableOn`).
* Codomain restriction preserves smoothness (`ContDiff`, `ContMDiff`).
* Codomain restriction preserves analyticity (`AnalyticOn`) and bounded polynomials
  (`CPolynomial`) by extracting and corestricting the symmetric multilinear series.

-/

noncomputable section

open Set Topology
open scoped Manifold

universe u uX uY uZ uK

variable {𝕜 : Type uK} [NontriviallyNormedField 𝕜]
variable {n : ℕ∞}

lemma hasFDerivAt_comp_clm_iff
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {Z : Type uZ} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    {f : X → Y} {f' : X →L[𝕜] Y} {x : X}
    (e : Y →L[𝕜] Z) (he : IsInducing e) :
    HasFDerivAt (e ∘ f) (e ∘L f') x ↔ HasFDerivAt f f' x := by
  constructor <;> intro h
  · have h' :
        (fun x' : X => (e ∘ f) x' - (e ∘ f) x - (e ∘L f') (x' - x))
          =o[𝕜; 𝓝 x] fun x' : X => x' - x :=
      hasFDerivAt_iff_isLittleOTVS.1 h
    rw [hasFDerivAt_iff_isLittleOTVS]
    let r : X → Y := fun x' ↦ f x' - f x - f' (x' - x)
    have hsmall : (e ∘ r) =o[𝕜; 𝓝 x] fun x' ↦ x' - x := by
      simpa [r, Function.comp_def, ContinuousLinearMap.comp_apply, map_sub] using h'
    have htheta : (e ∘ r) =Θ[𝕜; 𝓝 x] r := e.isThetaTVS_comp (f := r) he
    exact htheta.symm.trans_isLittleOTVS hsmall
  · exact e.hasFDerivAt.comp x h

lemma hasFDerivWithinAt_comp_clm_iff
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {Z : Type uZ} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    {s : Set X} {f : X → Y} {f' : X →L[𝕜] Y} {x : X}
    (e : Y →L[𝕜] Z) (he : IsInducing e) :
    HasFDerivWithinAt (e ∘ f) (e ∘L f') s x ↔ HasFDerivWithinAt f f' s x := by
  constructor <;> intro h
  · have h' :
        (fun x' : X => (e ∘ f) x' - (e ∘ f) x - (e ∘L f') (x' - x))
          =o[𝕜; 𝓝[s] x] fun x' : X => x' - x :=
      hasFDerivWithinAt_iff_isLittleOTVS.1 h
    rw [hasFDerivWithinAt_iff_isLittleOTVS]
    let r : X → Y := fun x' ↦ f x' - f x - f' (x' - x)
    have hsmall : (e ∘ r) =o[𝕜; 𝓝[s] x] fun x' ↦ x' - x := by
      simpa [r, Function.comp_def, ContinuousLinearMap.comp_apply, map_sub] using h'
    have htheta : (e ∘ r) =Θ[𝕜; 𝓝[s] x] r := e.isThetaTVS_comp (f := r) he
    exact htheta.symm.trans_isLittleOTVS hsmall
  · exact e.hasFDerivAt.comp_hasFDerivWithinAt x h

lemma isInducing_compContinuousMultilinearMapL
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {Z : Type uZ} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    {m : ℕ} (e : Y →L[𝕜] Z) (he : IsInducing e) :
    IsInducing
      (ContinuousLinearMap.compContinuousMultilinearMapL 𝕜 (fun _ : Fin m ↦ X) Y Z e) := by
  change IsInducing
    (e.compContinuousMultilinearMap :
      ContinuousMultilinearMap 𝕜 (fun _ : Fin m ↦ X) Y →
        ContinuousMultilinearMap 𝕜 (fun _ : Fin m ↦ X) Z)
  exact
    (ContinuousMultilinearMap.isUniformInducing_postcomp e
      (AddMonoidHom.isUniformInducing_of_isInducing he)).isInducing

theorem HasFTaylorSeriesUpToOn.continuousLinearMap_comp_iff
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {Z : Type uZ} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    {N : WithTop ℕ∞} {s : Set X} {f : X → Y}
    {pSeries : X → FormalMultilinearSeries 𝕜 X Y}
    (e : Y →L[𝕜] Z) (he : IsInducing e) :
    HasFTaylorSeriesUpToOn N (e ∘ f)
      (fun x m ↦ e.compContinuousMultilinearMap (pSeries x m)) s ↔
      HasFTaylorSeriesUpToOn N f pSeries s := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      apply he.injective
      simpa [Function.comp, ContinuousMultilinearMap.curry0_apply,
        ContinuousLinearMap.compContinuousMultilinearMap_coe] using h.zero_eq x hx
    · intro m hm x hx
      let e' :=
        ContinuousLinearMap.compContinuousMultilinearMapL 𝕜 (fun _ : Fin m ↦ X) Y Z e
      have he' : IsInducing e' :=
        isInducing_compContinuousMultilinearMapL
          (𝕜 := 𝕜) (X := X) (Y := Y) (Z := Z) (m := m) e he
      have hcomp :
          HasFDerivWithinAt (e' ∘ (pSeries · m)) (e' ∘L (pSeries x m.succ).curryLeft) s x := by
        simpa [e', Function.comp, ContinuousLinearMap.compContinuousMultilinearMap_coe,
          ContinuousMultilinearMap.curryLeft_apply] using h.fderivWithin m hm x hx
      exact (hasFDerivWithinAt_comp_clm_iff (e := e') (he := he')).1 hcomp
    · intro m hm
      let e' :=
        ContinuousLinearMap.compContinuousMultilinearMapL 𝕜 (fun _ : Fin m ↦ X) Y Z e
      have he' : IsInducing e' :=
        isInducing_compContinuousMultilinearMapL
          (𝕜 := 𝕜) (X := X) (Y := Y) (Z := Z) (m := m) e he
      have hcont : ContinuousOn (e' ∘ (pSeries · m)) s := by
        simpa [e', Function.comp, ContinuousLinearMap.compContinuousMultilinearMap_coe] using
          h.cont m hm
      exact (he'.continuousOn_iff).2 hcont
  · intro h
    exact h.continuousLinearMap_comp e

theorem HasFTaylorSeriesUpToOn.subtypeL_comp_iff
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {p : Submodule 𝕜 Y}
    {N : WithTop ℕ∞} {s : Set X} {f : X → p}
    {pSeries : X → FormalMultilinearSeries 𝕜 X p} :
    HasFTaylorSeriesUpToOn N (fun x ↦ (f x : Y))
      (fun x m ↦ p.subtypeL.compContinuousMultilinearMap (pSeries x m)) s ↔
      HasFTaylorSeriesUpToOn N f pSeries s := by
  simpa [Function.comp] using
    (HasFTaylorSeriesUpToOn.continuousLinearMap_comp_iff
      (𝕜 := 𝕜) (X := X) (Y := p) (Z := Y) (N := N) (s := s)
      (f := f) (pSeries := pSeries) p.subtypeL
      (p.subtypeₗᵢ.isometry.isEmbedding.isInducing : IsInducing (p.subtype : p → Y)))

lemma tangentConeAt_submodule_subset
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (p : Submodule 𝕜 X) (hp : IsClosed (p : Set X)) (x : X) (hx : x ∈ p) :
    tangentConeAt 𝕜 (p : Set X) x ⊆ p := by
  rw [← hp.closure_eq, tangentConeAt_closure]
  intro y hy
  rcases exists_fun_of_mem_tangentConeAt hy with ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩
  have hd_mem : ∀ᶠ n in l, c n • d n ∈ p := by
    filter_upwards [hds] with n hn
    have hdn : d n ∈ p := by
      simpa using p.sub_mem hn hx
    exact p.smul_mem (c n) hdn
  simpa [hp.closure_eq] using hp.mem_of_tendsto hcd hd_mem

lemma hasFDerivAt_mapsTo_submodule
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {f : X → Y} {f' : X →L[𝕜] Y} {x : X}
    (h : HasFDerivAt f f' x) (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y))
    (hf : MapsTo f univ p) :
    MapsTo f' univ p := by
  intro y hy
  have hwithin : HasFDerivWithinAt f f' univ x := by
    simpa [HasFDerivAt, HasFDerivWithinAt] using h
  have hy0 : y ∈ tangentConeAt 𝕜 (univ : Set X) x := by
    simp [tangentConeAt_univ]
  have hcone : f' y ∈ tangentConeAt 𝕜 (Set.range f) (f x) := by
    simpa [Set.range_comp] using hwithin.mapsTo_tangent_cone hy0
  have hcone' : f' y ∈ tangentConeAt 𝕜 (p : Set Y) (f x) :=
    tangentConeAt_mono
      (by
        intro z hz
        rcases hz with ⟨w, rfl⟩
        exact hf (show w ∈ univ from trivial))
      hcone
  exact tangentConeAt_submodule_subset p hp (f x) (hf (show x ∈ univ from trivial)) hcone'

theorem HasFDerivWithinAt.mapsTo_submodule
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {s : Set X} {f : X → Y} {f' : X →L[𝕜] Y} {x : X}
    (h : HasFDerivWithinAt f f' s x) (hs : UniqueDiffWithinAt 𝕜 s x)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) (hf : MapsTo f s p) :
    MapsTo f' univ p := by
  have hfx : f x ∈ p := by
    have hclosure : f x ∈ closure (p : Set Y) :=
      h.continuousWithinAt.mem_closure hs.mem_closure hf
    simpa [hp.closure_eq] using hclosure
  let q : Submodule 𝕜 X := p.comap f'.toLinearMap
  have hcone : tangentConeAt 𝕜 s x ⊆ q := by
    intro y hy
    have hycone : f' y ∈ tangentConeAt 𝕜 (f '' s) (f x) := h.mapsTo_tangent_cone hy
    have hycone' : f' y ∈ tangentConeAt 𝕜 (p : Set Y) (f x) :=
      tangentConeAt_mono
        (by
          intro z hz
          rcases hz with ⟨w, hw, rfl⟩
          exact hf hw)
        hycone
    exact tangentConeAt_submodule_subset p hp (f x) hfx hycone'
  have hspan : (Submodule.span 𝕜 (tangentConeAt 𝕜 s x)) ≤ q :=
    Submodule.span_le.2 hcone
  have hq_closed : IsClosed (q : Set X) :=
    hp.preimage f'.continuous
  have hclosure :
      closure (Submodule.span 𝕜 (tangentConeAt 𝕜 s x) : Set X) ⊆ q := by
    exact closure_minimal (by simpa using hspan) hq_closed
  have hall : (Set.univ : Set X) ⊆ q := by
    simpa [hs.dense_tangentConeAt.closure_eq] using hclosure
  intro y hy
  exact hall (show y ∈ univ from trivial)

/-- Continuous linear maps whose image lands in the submodule `p`. -/
def clmMapsToSubmodule
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (p : Submodule 𝕜 Y) :
    Submodule 𝕜 (X →L[𝕜] Y) where
  carrier := {L | MapsTo L univ p}
  zero_mem' := by
    intro v hv
    simp
  add_mem' := by
    intro L M hL hM v hv
    exact p.add_mem (hL (show v ∈ univ from hv)) (hM (show v ∈ univ from hv))
  smul_mem' := by
    intro c L hL v hv
    exact p.smul_mem c (hL (show v ∈ univ from hv))

def clmMapsToSubmoduleToCLM
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (p : Submodule 𝕜 Y) :
    clmMapsToSubmodule (𝕜 := 𝕜) (X := X) (Y := Y) p →L[𝕜] X →L[𝕜] p :=
  LinearMap.mkContinuous
    { toFun := fun (L : clmMapsToSubmodule (𝕜 := 𝕜) (X := X) (Y := Y) p) ↦
        L.1.codRestrict p fun x ↦ L.2 (show x ∈ univ from trivial)
      map_add' := by
        intro L M
        ext x
        rfl
      map_smul' := by
        intro c L
        ext x
        rfl }
    1
    (by
      intro L
      have hnorm :
          ‖L.1.codRestrict p fun x ↦ L.2 (show x ∈ univ from trivial)‖ ≤ ‖L.1‖ := by
        refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_
        intro x
        simpa using L.1.le_opNorm x
      show ‖L.1.codRestrict p fun x ↦ L.2 (show x ∈ univ from trivial)‖ ≤ 1 * ‖L‖
      simpa using hnorm)

def clmMapsToSubmoduleFromCLM
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (p : Submodule 𝕜 Y) :
    (X →L[𝕜] p) →L[𝕜] clmMapsToSubmodule (𝕜 := 𝕜) (X := X) (Y := Y) p :=
  LinearMap.mkContinuous
    { toFun := fun (L : X →L[𝕜] p) ↦ ⟨p.subtypeL.comp L, fun x _ ↦ (L x).2⟩
      map_add' := by
        intro L M
        ext x
        rfl
      map_smul' := by
        intro c L
        ext x
        rfl }
    ‖p.subtypeL‖
    (by
      intro L
      simpa using (ContinuousLinearMap.opNorm_comp_le p.subtypeL L))

noncomputable def clmMapsToSubmoduleEquiv
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (p : Submodule 𝕜 Y) :
    clmMapsToSubmodule (𝕜 := 𝕜) (X := X) (Y := Y) p ≃L[𝕜] X →L[𝕜] p :=
  ContinuousLinearEquiv.equivOfInverse
    (clmMapsToSubmoduleToCLM (𝕜 := 𝕜) p)
    (clmMapsToSubmoduleFromCLM (𝕜 := 𝕜) p)
    (by
      intro L
      ext x
      rfl)
    (by
      intro L
      ext x
      rfl)

@[simp] theorem clmMapsToSubmoduleEquiv_apply
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (p : Submodule 𝕜 Y) (L : clmMapsToSubmodule (𝕜 := 𝕜) (X := X) (Y := Y) p) :
    clmMapsToSubmoduleEquiv (𝕜 := 𝕜) (X := X) (Y := Y) p L =
      L.1.codRestrict p fun x ↦ L.2 (show x ∈ univ from trivial) := by
  rfl

@[simp] theorem clmMapsToSubmoduleEquiv_symm_apply
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (p : Submodule 𝕜 Y) (L : X →L[𝕜] p) :
    (clmMapsToSubmoduleEquiv (𝕜 := 𝕜) (X := X) (Y := Y) p).symm L =
      ⟨p.subtypeL.comp L, fun x _ ↦ (L x).2⟩ := by
  rfl

/-- Continuous multilinear maps whose image lands in the submodule `p`. -/
def cmlmMapsToSubmodule
    {ι : Type*} [Fintype ι]
    {X : ι → Type*} [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace 𝕜 (X i)]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (p : Submodule 𝕜 Y) :
    Submodule 𝕜 (ContinuousMultilinearMap 𝕜 X Y) where
  carrier := {L | MapsTo L univ p}
  zero_mem' := by
    intro v hv
    simp
  add_mem' := by
    intro L M hL hM v hv
    exact p.add_mem (hL (show v ∈ univ from hv)) (hM (show v ∈ univ from hv))
  smul_mem' := by
    intro c L hL v hv
    exact p.smul_mem c (hL (show v ∈ univ from hv))

def cmlmMapsToSubmoduleToCMLM
    {ι : Type*} [Fintype ι]
    {X : ι → Type*} [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace 𝕜 (X i)]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (p : Submodule 𝕜 Y) :
    cmlmMapsToSubmodule (𝕜 := 𝕜) (X := X) (Y := Y) p →L[𝕜]
      ContinuousMultilinearMap 𝕜 X p :=
  LinearMap.mkContinuous
    { toFun := fun (L : cmlmMapsToSubmodule (𝕜 := 𝕜) (X := X) (Y := Y) p) ↦
        L.1.codRestrict p fun x ↦ L.2 (show x ∈ univ from trivial)
      map_add' := by
        intro L M
        ext x
        rfl
      map_smul' := by
        intro c L
        ext x
        rfl }
    1
    (by
      intro L
      have hnorm :
          ‖L.1.codRestrict p fun x ↦ L.2 (show x ∈ univ from trivial)‖ ≤ ‖L.1‖ := by
        refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) ?_
        intro x
        simpa using L.1.le_opNorm x
      show ‖L.1.codRestrict p fun x ↦ L.2 (show x ∈ univ from trivial)‖ ≤ 1 * ‖L‖
      simpa using hnorm)

def cmlmMapsToSubmoduleFromCMLM
    {ι : Type*} [Fintype ι]
    {X : ι → Type*} [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace 𝕜 (X i)]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (p : Submodule 𝕜 Y) :
    ContinuousMultilinearMap 𝕜 X p →L[𝕜]
      cmlmMapsToSubmodule (𝕜 := 𝕜) (X := X) (Y := Y) p :=
  LinearMap.mkContinuous
    { toFun := fun (L : ContinuousMultilinearMap 𝕜 X p) ↦
        ⟨p.subtypeL.compContinuousMultilinearMap L, fun x _ ↦ (L x).2⟩
      map_add' := by
        intro L M
        ext x
        rfl
      map_smul' := by
        intro c L
        ext x
        rfl }
    ‖p.subtypeL‖
    (by
      intro L
      simpa using (ContinuousLinearMap.norm_compContinuousMultilinearMap_le p.subtypeL L))

noncomputable def cmlmMapsToSubmoduleEquiv
    {ι : Type*} [Fintype ι]
    {X : ι → Type*} [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace 𝕜 (X i)]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (p : Submodule 𝕜 Y) :
    cmlmMapsToSubmodule (𝕜 := 𝕜) (X := X) (Y := Y) p ≃L[𝕜]
      ContinuousMultilinearMap 𝕜 X p :=
  ContinuousLinearEquiv.equivOfInverse
    (cmlmMapsToSubmoduleToCMLM (𝕜 := 𝕜) p)
    (cmlmMapsToSubmoduleFromCMLM (𝕜 := 𝕜) p)
    (by
      intro L
      ext x
      rfl)
    (by
      intro L
      ext x
      rfl)

@[simp] theorem cmlmMapsToSubmoduleEquiv_apply
    {ι : Type*} [Fintype ι]
    {X : ι → Type*} [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace 𝕜 (X i)]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (p : Submodule 𝕜 Y)
    (L : cmlmMapsToSubmodule (𝕜 := 𝕜) (X := X) (Y := Y) p) :
    cmlmMapsToSubmoduleEquiv (𝕜 := 𝕜) (X := X) (Y := Y) p L =
      L.1.codRestrict p fun x ↦ L.2 (show x ∈ univ from trivial) := by
  rfl

@[simp] theorem cmlmMapsToSubmoduleEquiv_symm_apply
    {ι : Type*} [Fintype ι]
    {X : ι → Type*} [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace 𝕜 (X i)]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (p : Submodule 𝕜 Y) (L : ContinuousMultilinearMap 𝕜 X p) :
    (cmlmMapsToSubmoduleEquiv (𝕜 := 𝕜) (X := X) (Y := Y) p).symm L =
      ⟨p.subtypeL.compContinuousMultilinearMap L, fun x _ ↦ (L x).2⟩ := by
  rfl

lemma isClosed_clmMapsToSubmodule
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) :
    IsClosed ((clmMapsToSubmodule (𝕜 := 𝕜) (X := X) (Y := Y) p : Submodule 𝕜 (X →L[𝕜] Y)) :
      Set (X →L[𝕜] Y)) := by
  simpa [clmMapsToSubmodule, Set.setOf_forall] using
    isClosed_iInter fun x : X ↦ hp.preimage (ContinuousLinearMap.apply 𝕜 Y x).continuous

lemma isClosed_cmlmMapsToSubmodule
    {ι : Type*} [Fintype ι]
    {X : ι → Type*} [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace 𝕜 (X i)]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) :
    IsClosed ((cmlmMapsToSubmodule (𝕜 := 𝕜) (X := X) (Y := Y) p :
      Submodule 𝕜 (ContinuousMultilinearMap 𝕜 X Y)) :
      Set (ContinuousMultilinearMap 𝕜 X Y)) := by
  simpa [cmlmMapsToSubmodule, Set.setOf_forall] using
    isClosed_iInter fun x : ∀ i, X i ↦ hp.preimage (continuous_eval_const x)

/-- The quotient map to `Y ⧸ p` as a continuous linear map. -/
def mkQContinuousLinearMap
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (p : Submodule 𝕜 Y) :
    Y →L[𝕜] Y ⧸ p :=
  LinearMap.mkContinuous p.mkQ 1 fun y ↦ by
    simpa using Submodule.Quotient.norm_mk_le (S := p) y

theorem HasFTaylorSeriesUpToOn.mapsTo_cmlmMapsToSubmodule
    {E : Type uX} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {s : Set E} {f : E → Y} {pSeries : E → FormalMultilinearSeries 𝕜 E Y}
    {N : WithTop ℕ∞} (h : HasFTaylorSeriesUpToOn N f pSeries s) (hs : UniqueDiffOn 𝕜 s)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) (hf : MapsTo f s p) :
    ∀ m : ℕ, m ≤ N →
      MapsTo (fun x ↦ pSeries x m) s
        (cmlmMapsToSubmodule (𝕜 := 𝕜) (X := fun _ : Fin m ↦ E) (Y := Y) p) := by
  intro m
  induction m with
  | zero =>
      intro hm x hx v hv
      simpa [h.zero_eq' hx, ContinuousMultilinearMap.uncurry0_apply] using hf hx
  | succ m ih =>
      intro hm x hx v hv
      let q : Submodule 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin m ↦ E) Y) :=
        cmlmMapsToSubmodule (𝕜 := 𝕜) (X := fun _ : Fin m ↦ E) (Y := Y) p
      have hq : IsClosed (q : Set (ContinuousMultilinearMap 𝕜 (fun _ : Fin m ↦ E) Y)) :=
        isClosed_cmlmMapsToSubmodule (𝕜 := 𝕜) (X := fun _ : Fin m ↦ E) (Y := Y) p hp
      have hm_lt : (m : WithTop ℕ∞) < N := by
        exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self m) hm
      have hm_le : (m : WithTop ℕ∞) ≤ N := by
        exact le_trans (by exact_mod_cast Nat.le_succ m) hm
      have hmaps :
          MapsTo (fun y ↦ pSeries y m) s q :=
        ih hm_le
      have hcurry :
          MapsTo ((pSeries x m.succ).curryLeft) univ q := by
        exact HasFDerivWithinAt.mapsTo_submodule
          (h := h.fderivWithin m hm_lt x hx) (hs := hs x hx) q hq hmaps
      have hmem : (pSeries x m.succ).curryLeft (v 0) ∈ q :=
        hcurry (show v 0 ∈ univ from trivial)
      simpa [ContinuousMultilinearMap.curryLeft_apply, Fin.cons_self_tail] using
        hmem (show Fin.tail v ∈ univ from trivial)

theorem HasFTaylorSeriesUpToOn.comp_mkQContinuousLinearMap_eq_zero
    {E : Type uX} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {s : Set E} {f : E → Y} {pSeries : E → FormalMultilinearSeries 𝕜 E Y}
    {N : WithTop ℕ∞} (h : HasFTaylorSeriesUpToOn N f pSeries s) (hs : UniqueDiffOn 𝕜 s)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) (hf : MapsTo f s p) :
    ∀ m : ℕ, m ≤ N →
      EqOn
        (fun x ↦
          mkQContinuousLinearMap (𝕜 := 𝕜) p |>.compContinuousMultilinearMap (pSeries x m))
        0 s := by
  intro m hm x hx
  let q : Y →L[𝕜] Y ⧸ p := mkQContinuousLinearMap (𝕜 := 𝕜) p
  have hq :
      HasFTaylorSeriesUpToOn N (q ∘ f)
        (fun y k ↦ q.compContinuousMultilinearMap (pSeries y k)) s :=
    h.continuousLinearMap_comp q
  have hq0 :
      HasFTaylorSeriesUpToOn N (fun _ : E ↦ (0 : Y ⧸ p))
        (fun y k ↦ q.compContinuousMultilinearMap (pSeries y k)) s := by
    refine hq.congr ?_
    intro y hy
    symm
    change q (f y) = 0
    simpa [q, mkQContinuousLinearMap] using (Submodule.Quotient.mk_eq_zero p).2 (hf hy)
  have hm_eq :
      q.compContinuousMultilinearMap (pSeries x m) =
        iteratedFDerivWithin 𝕜 m (fun _ : E ↦ (0 : Y ⧸ p)) s x :=
    hq0.eq_iteratedFDerivWithin_of_uniqueDiffOn hm hs hx
  simpa [q] using hm_eq.trans (by simp)

-- The target universe bump comes from `continuousMultilinearCurryRightEquiv'` in the
-- successor step.
theorem HasFTaylorSeriesUpToOn.analyticOn_coeff
    {E : Type uX} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {Y : Type (max uX uY)} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {s : Set E} {f : E → Y} {pSeries : E → FormalMultilinearSeries 𝕜 E Y}
    (h : HasFTaylorSeriesUpToOn (⊤ : WithTop ℕ∞) f pSeries s) (hs : UniqueDiffOn 𝕜 s)
    (hf : AnalyticOn 𝕜 f s) :
    ∀ m : ℕ, AnalyticOn 𝕜 (fun x ↦ pSeries x m) s := by
  suffices hcoeff :
      ∀ {Z : Type (max uX uY)} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
        {g : E → Z} {qSeries : E → FormalMultilinearSeries 𝕜 E Z},
          HasFTaylorSeriesUpToOn (⊤ : WithTop ℕ∞) g qSeries s →
            AnalyticOn 𝕜 g s →
              ∀ m : ℕ, AnalyticOn 𝕜 (fun x ↦ qSeries x m) s by
    exact hcoeff (g := f) (qSeries := pSeries) h hf
  intro Z _ _ g qSeries hg hanalytic m
  induction m generalizing Z g qSeries with
  | zero =>
      refine (((continuousMultilinearCurryFin0 𝕜 E Z).symm :
        Z →L[𝕜] E [×0]→L[𝕜] Z).comp_analyticOn hanalytic).congr ?_
      intro x hx
      simp [hg.zero_eq' hx]
  | succ m ih =>
      have hg' :
          HasFTaylorSeriesUpToOn (⊤ : WithTop ℕ∞)
            (fun x ↦ continuousMultilinearCurryFin1 𝕜 E Z (qSeries x 1))
            (fun x ↦ (qSeries x).shift) s := by
        have h_top_le_omega : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞) := le_top
        exact
          ((hasFTaylorSeriesUpToOn_top_iff_right
            (𝕜 := 𝕜) (N := (⊤ : WithTop ℕ∞)) (f := g) (p := qSeries) (s := s)
            h_top_le_omega).1 hg).2.2
      have hanalytic' :
          AnalyticOn 𝕜 (fun x ↦ continuousMultilinearCurryFin1 𝕜 E Z (qSeries x 1)) s := by
        refine (hanalytic.fderivWithin hs).congr ?_
        intro x hx
        simpa using
          ((hg.hasFDerivWithinAt (hn := by decide) hx).fderivWithin (hs x hx)).symm
      have hshift :
          AnalyticOn 𝕜 (fun x ↦ (qSeries x).shift m) s :=
        ih hg' hanalytic'
      refine ((((continuousMultilinearCurryRightEquiv' 𝕜 m E Z).symm :
        (E [×m]→L[𝕜] E →L[𝕜] Z) →L[𝕜] E [×(m + 1)]→L[𝕜] Z)
        ).comp_analyticOn hshift).congr ?_
      intro x hx
      change qSeries x (m + 1) =
        (continuousMultilinearCurryRightEquiv' 𝕜 m E Z).symm
          ((continuousMultilinearCurryRightEquiv' 𝕜 m E Z) (qSeries x (m + 1)))
      exact (LinearIsometryEquiv.symm_apply_apply
        (continuousMultilinearCurryRightEquiv' 𝕜 m E Z) (qSeries x (m + 1))).symm

theorem HasFTaylorSeriesUpToOn.analyticOn_coeff_of_zero
    {E : Type uX} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {Y : Type (max uX uY)} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {s : Set E} {f : E → Y} {pSeries : E → FormalMultilinearSeries 𝕜 E Y}
    (h : HasFTaylorSeriesUpToOn (⊤ : WithTop ℕ∞) f pSeries s) (hs : UniqueDiffOn 𝕜 s)
    (h0 : AnalyticOn 𝕜 (fun x ↦ pSeries x 0) s) :
    ∀ m : ℕ, AnalyticOn 𝕜 (fun x ↦ pSeries x m) s := by
  exact HasFTaylorSeriesUpToOn.analyticOn_coeff (h := h) hs (h.analyticOn h0)

theorem AnalyticOn.iteratedFDerivWithin_mapsTo_cmlmMapsToSubmodule
    {E : Type uX} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {s : Set E} {f : E → Y} (h : AnalyticOn 𝕜 f s) (hs : UniqueDiffOn 𝕜 s)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) (hf : MapsTo f s p) (m : ℕ) :
    MapsTo (iteratedFDerivWithin 𝕜 m f s) s
      (cmlmMapsToSubmodule (𝕜 := 𝕜) (X := fun _ : Fin m ↦ E) (Y := Y) p) := by
  simpa [ftaylorSeriesWithin] using
    (HasFTaylorSeriesUpToOn.mapsTo_cmlmMapsToSubmodule
      (h := h.hasFTaylorSeriesUpToOn hs) (hs := hs) p hp hf m le_top)

theorem HasFDerivAt.codRestrict_submodule
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {f : X → Y} {f' : X →L[𝕜] Y} {x : X}
    (h : HasFDerivAt f f' x) (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y))
    (hf : MapsTo f univ p) :
    HasFDerivAt (Set.codRestrict f p fun x ↦ hf (show x ∈ univ from trivial))
      (f'.codRestrict p fun x ↦ hasFDerivAt_mapsTo_submodule h p hp hf (show x ∈ univ from trivial))
      x := by
  apply (hasFDerivAt_comp_clm_iff (e := p.subtypeL) ?_).mp
  · simpa [Set.codRestrict, Function.comp_def] using h
  · simpa [Submodule.subtypeL] using
      (p.subtypeₗᵢ.isometry.isEmbedding.isInducing : IsInducing (p.subtype : p → Y))

theorem HasFDerivWithinAt.codRestrict_submodule
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {s : Set X} {f : X → Y} {f' : X →L[𝕜] Y} {x : X}
    (h : HasFDerivWithinAt f f' s x) (hs : UniqueDiffWithinAt 𝕜 s x)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) (hf : MapsTo f univ p) :
    HasFDerivWithinAt (Set.codRestrict f p fun y ↦ hf (show y ∈ univ from trivial))
      (f'.codRestrict p fun y ↦
        (HasFDerivWithinAt.mapsTo_submodule h hs p hp (hf.mono_left (subset_univ s)))
          (show y ∈ univ from trivial))
      s x := by
  apply (hasFDerivWithinAt_comp_clm_iff (e := p.subtypeL) ?_).mp
  · simpa [Set.codRestrict, Function.comp_def] using h
  · simpa [Submodule.subtypeL] using
      (p.subtypeₗᵢ.isometry.isEmbedding.isInducing : IsInducing (p.subtype : p → Y))

theorem DifferentiableWithinAt.codRestrict_submodule
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {s : Set X} {f : X → Y} {x : X}
    (h : DifferentiableWithinAt 𝕜 f s x) (hs : UniqueDiffWithinAt 𝕜 s x)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) (hf : MapsTo f univ p) :
    DifferentiableWithinAt 𝕜
      (Set.codRestrict f p fun y ↦ hf (show y ∈ univ from trivial)) s x := by
  exact
    (HasFDerivWithinAt.codRestrict_submodule h.hasFDerivWithinAt hs p hp hf).differentiableWithinAt

theorem DifferentiableOn.codRestrict_submodule
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {s : Set X} {f : X → Y}
    (h : DifferentiableOn 𝕜 f s) (hs : UniqueDiffOn 𝕜 s)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) (hf : MapsTo f univ p) :
    DifferentiableOn 𝕜 (Set.codRestrict f p fun y ↦ hf (show y ∈ univ from trivial)) s := by
  intro x hx
  rcases h x hx with ⟨f', hf'⟩
  exact (HasFDerivWithinAt.codRestrict_submodule hf' (hs x hx) p hp hf).differentiableWithinAt

theorem fderivWithin_codRestrict_submodule
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {s : Set X} {f : X → Y} {x : X}
    (h : DifferentiableWithinAt 𝕜 f s x) (hs : UniqueDiffWithinAt 𝕜 s x)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) (hf : MapsTo f univ p) :
    fderivWithin 𝕜 (Set.codRestrict f p fun y ↦ hf (show y ∈ univ from trivial)) s x =
      (fderivWithin 𝕜 f s x).codRestrict p fun y ↦
        HasFDerivWithinAt.mapsTo_submodule h.hasFDerivWithinAt hs p hp
          (hf.mono_left (subset_univ s)) (show y ∈ univ from trivial) := by
  simpa using
    (HasFDerivWithinAt.codRestrict_submodule h.hasFDerivWithinAt hs p hp hf).fderivWithin hs

theorem HasFTaylorSeriesUpToOn.codRestrict_submodule
    {E : Type uX} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {s : Set E} {f : E → Y} {pSeries : E → FormalMultilinearSeries 𝕜 E Y}
    {N : WithTop ℕ∞} (h : HasFTaylorSeriesUpToOn N f pSeries s) (hs : UniqueDiffOn 𝕜 s)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) (hf : MapsTo f univ p) :
    ∃ qSeries : E → FormalMultilinearSeries 𝕜 E p,
      HasFTaylorSeriesUpToOn N
        (Set.codRestrict f p fun x ↦ hf (show x ∈ univ from trivial))
        qSeries s := by
  classical
  have hmaps :
      ∀ m : ℕ, (m : WithTop ℕ∞) ≤ N →
        MapsTo (fun x ↦ pSeries x m) s
          (cmlmMapsToSubmodule (𝕜 := 𝕜) (X := fun _ : Fin m ↦ E) (Y := Y) p) := by
    intro m hm
    exact HasFTaylorSeriesUpToOn.mapsTo_cmlmMapsToSubmodule
      (h := h) (hs := hs) p hp (hf.mono_left (subset_univ s)) m hm
  let qSeries : E → FormalMultilinearSeries 𝕜 E p := fun x m ↦
    if hm : (m : WithTop ℕ∞) ≤ N then
      if hx : x ∈ s then
        (cmlmMapsToSubmoduleToCMLM (𝕜 := 𝕜) (X := fun _ : Fin m ↦ E) (Y := Y) p)
          ⟨pSeries x m, hmaps m hm hx⟩
      else 0
    else 0
  let g : E → p := Set.codRestrict f p fun x ↦ hf (show x ∈ univ from trivial)
  have hsub :
      HasFTaylorSeriesUpToOn N f
        (fun x m ↦ p.subtypeL.compContinuousMultilinearMap (qSeries x m)) s := by
    refine h.congr_series ?_
    intro m hm x hx
    ext v
    simp [qSeries, hm, hx, cmlmMapsToSubmoduleToCMLM]
  refine ⟨qSeries, ?_⟩
  have hambient :
      HasFTaylorSeriesUpToOn N (fun x ↦ (g x : Y))
        (fun x m ↦ p.subtypeL.compContinuousMultilinearMap (qSeries x m)) s := by
    simpa [g, Set.codRestrict] using hsub
  exact
    (HasFTaylorSeriesUpToOn.subtypeL_comp_iff
      (𝕜 := 𝕜) (X := E) (Y := Y) (p := p) (N := N) (s := s)
      (f := g) (pSeries := qSeries)).1 hambient

theorem HasFTaylorSeriesUpToOn.codRestrict_submodule_subtypeL
    {E : Type uX} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {s : Set E} {f : E → Y} {pSeries : E → FormalMultilinearSeries 𝕜 E Y}
    {N : WithTop ℕ∞} (h : HasFTaylorSeriesUpToOn N f pSeries s) (hs : UniqueDiffOn 𝕜 s)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) (hf : MapsTo f univ p) :
    ∃ qSeries : E → FormalMultilinearSeries 𝕜 E p,
      HasFTaylorSeriesUpToOn N
        (Set.codRestrict f p fun x ↦ hf (show x ∈ univ from trivial))
        qSeries s ∧
      HasFTaylorSeriesUpToOn N f
        (fun x m ↦ p.subtypeL.compContinuousMultilinearMap (qSeries x m)) s := by
  obtain ⟨qSeries, hq⟩ :=
    HasFTaylorSeriesUpToOn.codRestrict_submodule (h := h) (hs := hs) p hp hf
  refine ⟨qSeries, hq, ?_⟩
  refine
    ((HasFTaylorSeriesUpToOn.subtypeL_comp_iff
      (𝕜 := 𝕜) (X := E) (Y := Y) (p := p) (N := N) (s := s)
      (f := Set.codRestrict f p fun x ↦ hf (show x ∈ univ from trivial))
      (pSeries := qSeries)).2 hq).congr ?_
  intro x hx
  simp [Set.codRestrict]

section

attribute [local instance] Classical.propDecidable

theorem HasFTaylorSeriesUpToOn.codRestrict_submodule_piecewise
    {E : Type uX} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {s : Set E} {f : E → Y} {pSeries : E → FormalMultilinearSeries 𝕜 E Y}
    {N : WithTop ℕ∞} (h : HasFTaylorSeriesUpToOn N f pSeries s) (hs : UniqueDiffOn 𝕜 s)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) (hf : MapsTo f s p) :
    ∃ qSeries : E → FormalMultilinearSeries 𝕜 E p,
      HasFTaylorSeriesUpToOn N
        (fun y ↦ if hy : y ∈ s then (⟨f y, hf hy⟩ : p) else 0)
        qSeries s := by
  classical
  let fExt : E → Y := fun y ↦ if hy : y ∈ s then f y else 0
  have hExt : HasFTaylorSeriesUpToOn N fExt pSeries s := by
    refine h.congr ?_
    intro y hy
    simp [fExt, hy]
  have hfExt : MapsTo fExt univ p := by
    intro y hy
    by_cases hy' : y ∈ s
    · simpa [fExt, hy'] using hf hy'
    · simp [fExt, hy']
  obtain ⟨qSeries, hq⟩ :=
    HasFTaylorSeriesUpToOn.codRestrict_submodule (h := hExt) (hs := hs) p hp hfExt
  refine ⟨qSeries, hq.congr ?_⟩
  intro y hy
  apply Subtype.ext
  simp [Set.codRestrict, fExt, hy]

theorem HasFTaylorSeriesUpToOn.contDiffOn_of_analyticOn_coeff
    {E : Type uX} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {s : Set E} {f : E → Y} {pSeries : E → FormalMultilinearSeries 𝕜 E Y}
    {N : WithTop ℕ∞} (h : HasFTaylorSeriesUpToOn N f pSeries s)
    (hcoeff : ∀ m : ℕ, AnalyticOn 𝕜 (fun x ↦ pSeries x m) s) :
    ContDiffOn 𝕜 N f s := by
  by_cases hN : N = ⊤
  · subst hN
    intro x hx
    refine ⟨s, ?_, pSeries, h, hcoeff⟩
    simpa [insert_eq_of_mem hx] using (self_mem_nhdsWithin : s ∈ 𝓝[s] x)
  · rcases WithTop.ne_top_iff_exists.mp hN with ⟨n, rfl⟩
    simpa using h.contDiffOn

end

theorem HasFiniteFPowerSeriesOnBall.iteratedFDerivWithin_eq_zero_of_le
    {E : Type uX} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {f : E → Y} {pSeries : FormalMultilinearSeries 𝕜 E Y}
    {x : E} {n m : ℕ} {r : ENNReal}
    (h : HasFiniteFPowerSeriesOnBall f pSeries x n r)
    {y : E} (hy : y ∈ Metric.eball x r) (hm : n ≤ m) :
    iteratedFDerivWithin 𝕜 m f (Metric.eball x r) y = 0 := by
  let t : Set E := Metric.eball y (r - ‖y - x‖₊)
  have hy' : (‖y - x‖₊ : ENNReal) < r := by
    simpa [Metric.mem_eball, edist_eq_enorm_sub] using hy
  have hyt : y ∈ t := by
    simp [t, hy']
  have hsubset : t ⊆ Metric.eball x r := by
    intro z hz
    rw [Metric.mem_eball] at hz hy ⊢
    have hz' : edist z y < r - edist y x := by
      simpa [t, edist_eq_enorm_sub] using hz
    have hzr : edist z y + edist y x < r := by
      rw [lt_tsub_iff_right, add_comm] at hz'
      simpa [add_comm] using hz'
    exact lt_of_le_of_lt (edist_triangle z y x) hzr
  have hchange : HasFiniteFPowerSeriesOnBall f (pSeries.changeOrigin (y - x)) y n
      (r - ‖y - x‖₊) :=
    by simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h.changeOrigin hy'
  have hpow :
      HasFPowerSeriesWithinOnBall f (pSeries.changeOrigin (y - x)) t y (r - ‖y - x‖₊) :=
    hchange.1.hasFPowerSeriesWithinOnBall (s := t)
  have hanalytic : AnalyticOn 𝕜 f t :=
    hchange.cpolynomialOn.analyticOn
  have hzero_t :
      iteratedFDerivWithin 𝕜 m f t y = 0 := by
    refine HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_zero
      (h := hpow) hanalytic Metric.isOpen_eball.uniqueDiffOn hyt ?_
    exact pSeries.changeOrigin_finite_of_finite h.finite hm
  have hsame :
      iteratedFDerivWithin 𝕜 m f t y =
        iteratedFDerivWithin 𝕜 m f (Metric.eball x r) y := by
    simpa [t, Set.inter_eq_right.2 hsubset] using
      (iteratedFDerivWithin_inter_open
        (𝕜 := 𝕜) (f := f) (s := Metric.eball x r) (u := t)
        (n := m) Metric.isOpen_eball hyt)
  simpa [hsame] using hzero_t

theorem HasFiniteFPowerSeriesOnBall.ftaylorSeriesWithin_eq_zero_of_le
    {E : Type uX} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {f : E → Y} {pSeries : FormalMultilinearSeries 𝕜 E Y}
    {x : E} {n m : ℕ} {r : ENNReal}
    (h : HasFiniteFPowerSeriesOnBall f pSeries x n r)
    {y : E} (hy : y ∈ Metric.eball x r) (hm : n ≤ m) :
    ftaylorSeriesWithin 𝕜 f (Metric.eball x r) y m = 0 := by
  let s : Set E := Metric.eball x r
  have hs : UniqueDiffOn 𝕜 s := Metric.isOpen_eball.uniqueDiffOn
  have hanalytic : AnalyticOn 𝕜 f s := h.cpolynomialOn.analyticOn
  have htaylor :
      HasFTaylorSeriesUpToOn (⊤ : WithTop ℕ∞) f (ftaylorSeriesWithin 𝕜 f s) s :=
    hanalytic.hasFTaylorSeriesUpToOn hs
  rw [htaylor.eq_iteratedFDerivWithin_of_uniqueDiffOn le_top hs hy]
  exact HasFiniteFPowerSeriesOnBall.iteratedFDerivWithin_eq_zero_of_le (h := h) hy hm

theorem HasFiniteFPowerSeriesOnBall.hasFTaylorSeriesUpToOn_ftaylorSeriesWithin
    {E : Type uX} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {f : E → Y} {pSeries : FormalMultilinearSeries 𝕜 E Y}
    {x : E} {n : ℕ} {r : ENNReal}
    (h : HasFiniteFPowerSeriesOnBall f pSeries x n r) :
    HasFTaylorSeriesUpToOn (⊤ : WithTop ℕ∞) f
      (ftaylorSeriesWithin 𝕜 f (Metric.eball x r)) (Metric.eball x r) := by
  let s := Metric.eball x r
  have hs : UniqueDiffOn 𝕜 s := Metric.isOpen_eball.uniqueDiffOn
  exact h.cpolynomialOn.analyticOn.hasFTaylorSeriesUpToOn hs

theorem HasFiniteFPowerSeriesAt.exists_eball_hasFTaylorSeriesUpToOn_ftaylorSeriesWithin
    {E : Type uX} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {f : E → Y} {pSeries : FormalMultilinearSeries 𝕜 E Y}
    {x : E} {n : ℕ}
    (h : HasFiniteFPowerSeriesAt f pSeries x n) :
    ∃ r : ENNReal, 0 < r ∧
      HasFTaylorSeriesUpToOn (⊤ : WithTop ℕ∞) f
        (ftaylorSeriesWithin 𝕜 f (Metric.eball x r)) (Metric.eball x r) := by
  rcases h with ⟨r, hr⟩
  exact ⟨r, hr.r_pos, HasFiniteFPowerSeriesOnBall.hasFTaylorSeriesUpToOn_ftaylorSeriesWithin hr⟩

section

theorem HasFiniteFPowerSeriesOnBall.unshift
    {E : Type uX} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type uY} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → E →L[𝕜] F} {p : FormalMultilinearSeries 𝕜 E (E →L[𝕜] F)}
    {x : E} {n : ℕ} {r : ENNReal} {z : F}
    (h : HasFiniteFPowerSeriesOnBall f p x n r) :
    HasFiniteFPowerSeriesOnBall (fun y ↦ z + f y (y - x)) (p.unshift z) x (n + 1) r := by
  refine ⟨h.toHasFPowerSeriesOnBall.unshift (z := z), ?_⟩
  intro m hm
  cases m with
  | zero =>
      exact (Nat.not_succ_le_zero n hm).elim
  | succ m =>
      have hp : p m = 0 := h.finite m (Nat.succ_le_succ_iff.mp hm)
      rw [FormalMultilinearSeries.unshift, hp]
      exact (continuousMultilinearCurryRightEquiv' 𝕜 m E F).symm.map_zero

theorem HasFiniteFPowerSeriesAt.unshift
    {E : Type uX} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type uY} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → E →L[𝕜] F} {p : FormalMultilinearSeries 𝕜 E (E →L[𝕜] F)}
    {x : E} {n : ℕ} {z : F}
    (h : HasFiniteFPowerSeriesAt f p x n) :
    HasFiniteFPowerSeriesAt (fun y ↦ z + f y (y - x)) (p.unshift z) x (n + 1) := by
  rcases h with ⟨r, hr⟩
  exact ⟨r, HasFiniteFPowerSeriesOnBall.unshift (z := z) hr⟩

theorem CPolynomialAt.unshift
    {E : Type uX} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type uY} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → E →L[𝕜] F} {x : E} {z : F}
    (h : CPolynomialAt 𝕜 f x) :
    CPolynomialAt 𝕜 (fun y ↦ z + f y (y - x)) x := by
  rcases h with ⟨p, n, hp⟩
  exact ⟨p.unshift z, n + 1, HasFiniteFPowerSeriesAt.unshift (z := z) hp⟩

attribute [local instance] Classical.propDecidable

theorem HasFiniteFPowerSeriesOnBall.exists_ftaylorSeriesWithin_codRestrict_submodule
    {E : Type uX} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {f : E → Y} {pSeries : FormalMultilinearSeries 𝕜 E Y}
    {x : E} {n : ℕ} {r : ENNReal}
    (h : HasFiniteFPowerSeriesOnBall f pSeries x n r)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y))
    (hf : MapsTo f (Metric.eball x r) p) :
    ∃ qSeries : E → FormalMultilinearSeries 𝕜 E p,
      HasFTaylorSeriesUpToOn (⊤ : WithTop ℕ∞)
        (fun y ↦ if hy : y ∈ Metric.eball x r then (⟨f y, hf hy⟩ : p) else 0)
        qSeries (Metric.eball x r) ∧
      ∀ y ∈ Metric.eball x r, ∀ m : ℕ, n ≤ m → qSeries y m = 0 := by
  classical
  let s : Set E := Metric.eball x r
  let fExt : E → Y := fun y ↦ if hy : y ∈ s then f y else 0
  have hs : UniqueDiffOn 𝕜 s := Metric.isOpen_eball.uniqueDiffOn
  have hExt_eq : ∀ y ∈ s, fExt y = f y := by
    intro y hy
    simp [fExt, hy]
  have hanalytic : AnalyticOn 𝕜 f s :=
    h.cpolynomialOn.analyticOn
  have ht :
      HasFTaylorSeriesUpToOn (⊤ : WithTop ℕ∞) fExt (ftaylorSeriesWithin 𝕜 f s) s := by
    exact (hanalytic.hasFTaylorSeriesUpToOn hs).congr hExt_eq
  have hfExt : MapsTo fExt univ p := by
    intro y hy
    by_cases hy' : y ∈ s
    · simpa [fExt, hy'] using hf hy'
    · simp [fExt, hy']
  obtain ⟨qSeries, hq_raw, hq_sub⟩ :=
    HasFTaylorSeriesUpToOn.codRestrict_submodule_subtypeL
      (h := ht) (hs := hs) p hp hfExt
  have hq :
      HasFTaylorSeriesUpToOn (⊤ : WithTop ℕ∞)
        (fun y ↦ if hy : y ∈ s then (⟨f y, hf hy⟩ : p) else 0)
        qSeries s := by
    refine hq_raw.congr ?_
    intro y hy
    apply Subtype.ext
    simp [fExt, hy]
  have hcoeff :
      ∀ y ∈ s, ∀ m : ℕ,
        p.subtypeL.compContinuousMultilinearMap (qSeries y m) =
          ftaylorSeriesWithin 𝕜 f s y m := by
    intro y hy m
    rw [hq_sub.eq_iteratedFDerivWithin_of_uniqueDiffOn le_top hs hy,
      ht.eq_iteratedFDerivWithin_of_uniqueDiffOn le_top hs hy]
  have hfinite :
      ∀ y ∈ s, ∀ m : ℕ, n ≤ m → qSeries y m = 0 := by
    intro y hy m hm
    have hzero :
        p.subtypeL.compContinuousMultilinearMap (qSeries y m) = 0 := by
      rw [hcoeff y hy m]
      exact HasFiniteFPowerSeriesOnBall.ftaylorSeriesWithin_eq_zero_of_le (h := h) hy hm
    ext v
    simpa using congrArg (fun L ↦ L v) hzero
  exact ⟨qSeries, hq, hfinite⟩

theorem HasFiniteFPowerSeriesAt.exists_eball_hasFTaylorSeriesUpToOn_codRestrict_submodule
    {E : Type uX} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {f : E → Y} {pSeries : FormalMultilinearSeries 𝕜 E Y}
    {x : E} {n : ℕ}
    (h : HasFiniteFPowerSeriesAt f pSeries x n)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) (hf : MapsTo f univ p) :
    ∃ r : ENNReal, 0 < r ∧ ∃ qSeries : E → FormalMultilinearSeries 𝕜 E p,
      HasFTaylorSeriesUpToOn (⊤ : WithTop ℕ∞)
        (Set.codRestrict f p fun y ↦ hf (show y ∈ univ from trivial))
        qSeries (Metric.eball x r) ∧
      ∀ y ∈ Metric.eball x r, ∀ m : ℕ, n ≤ m → qSeries y m = 0 := by
  rcases h with ⟨r, hr⟩
  refine ⟨r, hr.r_pos, ?_⟩
  have hfball : MapsTo f (Metric.eball x r) p := by
    intro y hy
    exact hf (show y ∈ univ from trivial)
  obtain ⟨qSeries, hq, hfinite⟩ :=
    HasFiniteFPowerSeriesOnBall.exists_ftaylorSeriesWithin_codRestrict_submodule
      (h := hr) p hp hfball
  refine ⟨qSeries, ?_, hfinite⟩
  refine hq.congr ?_
  intro y hy
  apply Subtype.ext
  simp [Set.codRestrict, hy]

theorem CPolynomialAt.exists_eball_hasFTaylorSeriesUpToOn_codRestrict_submodule
    {E : Type uX} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {f : E → Y} {x : E}
    (h : CPolynomialAt 𝕜 f x)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) (hf : MapsTo f univ p) :
    ∃ n : ℕ, ∃ r : ENNReal, 0 < r ∧ ∃ qSeries : E → FormalMultilinearSeries 𝕜 E p,
      HasFTaylorSeriesUpToOn (⊤ : WithTop ℕ∞)
        (Set.codRestrict f p fun y ↦ hf (show y ∈ univ from trivial))
        qSeries (Metric.eball x r) ∧
      ∀ y ∈ Metric.eball x r, ∀ m : ℕ, n ≤ m → qSeries y m = 0 := by
  rcases h with ⟨pSeries, n, hpow⟩
  rcases HasFiniteFPowerSeriesAt.exists_eball_hasFTaylorSeriesUpToOn_codRestrict_submodule
      (h := hpow) p hp hf with
    ⟨r, hr, qSeries, hq, hfinite⟩
  exact ⟨n, r, hr, qSeries, hq, hfinite⟩

end

theorem ContDiffOn.iteratedFDerivWithin_codRestrict_submodule
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {n : WithTop ℕ∞} {s : Set X} {f : X → Y}
    (h : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) (hf : MapsTo f univ p)
    {m : ℕ} (hm : (m : WithTop ℕ∞) ≤ n) {x : X} (hx : x ∈ s) :
    iteratedFDerivWithin 𝕜 m (Set.codRestrict f p fun y ↦ hf (show y ∈ univ from trivial)) s x =
      (iteratedFDerivWithin 𝕜 m f s x).codRestrict p fun v ↦
        (HasFTaylorSeriesUpToOn.mapsTo_cmlmMapsToSubmodule
          (h := h.ftaylorSeriesWithin hs) (hs := hs) p hp
          (hf.mono_left (subset_univ s)) m hm hx) (show v ∈ univ from trivial) := by
  let g : X → p := Set.codRestrict f p fun y ↦ hf (show y ∈ univ from trivial)
  have ht : HasFTaylorSeriesUpToOn n f (ftaylorSeriesWithin 𝕜 f s) s :=
    h.ftaylorSeriesWithin hs
  obtain ⟨qSeries, hq, hq_sub⟩ :=
    HasFTaylorSeriesUpToOn.codRestrict_submodule_subtypeL
      (h := ht) (hs := hs) p hp hf
  have hq_eq :
      qSeries x m = iteratedFDerivWithin 𝕜 m g s x :=
    hq.eq_iteratedFDerivWithin_of_uniqueDiffOn hm hs hx
  have hq_sub_eq :
      p.subtypeL.compContinuousMultilinearMap (qSeries x m) =
        iteratedFDerivWithin 𝕜 m f s x :=
    hq_sub.eq_iteratedFDerivWithin_of_uniqueDiffOn hm hs hx
  ext v
  simpa [g, hq_eq] using congrArg (fun L ↦ L v) hq_sub_eq

open Classical in
theorem ContDiffOn.iteratedFDerivWithin_codRestrict_submodule_piecewise
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {n : WithTop ℕ∞} {s : Set X} {f : X → Y}
    (h : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) (hf : MapsTo f s p)
    {m : ℕ} (hm : (m : WithTop ℕ∞) ≤ n) {x : X} (hx : x ∈ s) :
    iteratedFDerivWithin 𝕜 m
      (fun y ↦ if hy : y ∈ s then (⟨f y, hf hy⟩ : p) else 0) s x =
      (iteratedFDerivWithin 𝕜 m f s x).codRestrict p fun v ↦
        (HasFTaylorSeriesUpToOn.mapsTo_cmlmMapsToSubmodule
          (h := h.ftaylorSeriesWithin hs) (hs := hs) p hp hf m hm hx)
          (show v ∈ univ from trivial) := by
  classical
  let fExt : X → Y := fun y ↦ if hy : y ∈ s then f y else 0
  let g : X → p := fun y ↦ if hy : y ∈ s then (⟨f y, hf hy⟩ : p) else 0
  have hExt : ContDiffOn 𝕜 n fExt s := by
    refine h.congr ?_
    intro y hy
    simp [fExt, hy]
  have hfExt : MapsTo fExt univ p := by
    intro y hy
    by_cases hy' : y ∈ s
    · simpa [fExt, hy'] using hf hy'
    · simp [fExt, hy']
  have hEqIter :
      iteratedFDerivWithin 𝕜 m fExt s x = iteratedFDerivWithin 𝕜 m f s x := by
    exact iteratedFDerivWithin_congr (𝕜 := 𝕜) (s := s) (f₁ := fExt) (f := f)
      (fun y hy ↦ by simp [fExt, hy]) hx m
  have hEqg :
      EqOn
        (Set.codRestrict fExt p fun y ↦ hfExt (show y ∈ univ from trivial))
        g s := by
    intro y hy
    apply Subtype.ext
    simp [fExt, g, hy]
  calc
    iteratedFDerivWithin 𝕜 m g s x
      = iteratedFDerivWithin 𝕜 m
          (Set.codRestrict fExt p fun y ↦ hfExt (show y ∈ univ from trivial)) s x := by
            symm
            exact iteratedFDerivWithin_congr (𝕜 := 𝕜) (s := s)
              (f₁ := Set.codRestrict fExt p fun y ↦ hfExt (show y ∈ univ from trivial))
              (f := g) hEqg hx m
    _ = (iteratedFDerivWithin 𝕜 m fExt s x).codRestrict p fun v ↦
          (HasFTaylorSeriesUpToOn.mapsTo_cmlmMapsToSubmodule
            (h := hExt.ftaylorSeriesWithin hs) (hs := hs) p hp
            (hfExt.mono_left (subset_univ s)) m hm hx) (show v ∈ univ from trivial) := by
          exact ContDiffOn.iteratedFDerivWithin_codRestrict_submodule
            (h := hExt) (hs := hs) (p := p) (hp := hp) (hf := hfExt) (m := m) hm hx
    _ = (iteratedFDerivWithin 𝕜 m f s x).codRestrict p fun v ↦
          (HasFTaylorSeriesUpToOn.mapsTo_cmlmMapsToSubmodule
            (h := h.ftaylorSeriesWithin hs) (hs := hs) p hp hf m hm hx)
            (show v ∈ univ from trivial) := by
          ext v
          simp [hEqIter]

theorem ContDiff.iteratedFDeriv_codRestrict_submodule
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {n : WithTop ℕ∞} {f : X → Y}
    (h : ContDiff 𝕜 n f)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) (hf : MapsTo f univ p)
    {m : ℕ} (hm : (m : WithTop ℕ∞) ≤ n) (x : X) :
    iteratedFDeriv 𝕜 m (Set.codRestrict f p fun y ↦ hf (show y ∈ univ from trivial)) x =
      (iteratedFDeriv 𝕜 m f x).codRestrict p fun v ↦
        by
          simpa [ftaylorSeriesWithin, iteratedFDerivWithin_univ] using
            (HasFTaylorSeriesUpToOn.mapsTo_cmlmMapsToSubmodule
              (h := (contDiffOn_univ.2 h).ftaylorSeriesWithin uniqueDiffOn_univ)
              (hs := uniqueDiffOn_univ) p hp hf m hm (show x ∈ univ from trivial))
              (show v ∈ univ from trivial) := by
  simpa [iteratedFDerivWithin_univ] using
    (ContDiffOn.iteratedFDerivWithin_codRestrict_submodule
      (h := contDiffOn_univ.2 h) uniqueDiffOn_univ p hp hf hm (x := x) (hx := by simp))

theorem AnalyticOn.iteratedFDerivWithin_codRestrict_submodule
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {s : Set X} {f : X → Y} (h : AnalyticOn 𝕜 f s) (hs : UniqueDiffOn 𝕜 s)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) (hf : MapsTo f univ p)
    {m : ℕ} {x : X} (hx : x ∈ s) :
    iteratedFDerivWithin 𝕜 m (Set.codRestrict f p fun y ↦ hf (show y ∈ univ from trivial)) s x =
      (iteratedFDerivWithin 𝕜 m f s x).codRestrict p fun v ↦
        (AnalyticOn.iteratedFDerivWithin_mapsTo_cmlmMapsToSubmodule
          (h := h) (hs := hs) p hp (hf.mono_left (subset_univ s)) m hx)
          (show v ∈ univ from trivial) := by
  simpa using
    (ContDiffOn.iteratedFDerivWithin_codRestrict_submodule
      (h := h.contDiffOn (n := (⊤ : WithTop ℕ∞)) hs) hs p hp hf le_top hx)

open Classical in
theorem AnalyticOn.iteratedFDerivWithin_codRestrict_submodule_piecewise
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {s : Set X} {f : X → Y} (h : AnalyticOn 𝕜 f s) (hs : UniqueDiffOn 𝕜 s)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) (hf : MapsTo f s p)
    {m : ℕ} {x : X} (hx : x ∈ s) :
    iteratedFDerivWithin 𝕜 m
      (fun y ↦ if hy : y ∈ s then (⟨f y, hf hy⟩ : p) else 0) s x =
      (iteratedFDerivWithin 𝕜 m f s x).codRestrict p fun v ↦
        (AnalyticOn.iteratedFDerivWithin_mapsTo_cmlmMapsToSubmodule
          (h := h) (hs := hs) p hp hf m hx)
          (show v ∈ univ from trivial) := by
  simpa using
    (ContDiffOn.iteratedFDerivWithin_codRestrict_submodule_piecewise
      (h := h.contDiffOn (n := (⊤ : WithTop ℕ∞)) hs) (hs := hs)
      (p := p) (hp := hp) (hf := hf) (m := m) (hm := le_top) (x := x) hx)

theorem AnalyticOn.iteratedFDeriv_mapsTo_cmlmMapsToSubmodule
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {f : X → Y} (h : AnalyticOn 𝕜 f univ)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) (hf : MapsTo f univ p) (m : ℕ) :
    MapsTo (iteratedFDeriv 𝕜 m f) univ
      (cmlmMapsToSubmodule (𝕜 := 𝕜) (X := fun _ : Fin m ↦ X) (Y := Y) p) := by
  simpa [iteratedFDerivWithin_univ] using
    (AnalyticOn.iteratedFDerivWithin_mapsTo_cmlmMapsToSubmodule
      (h := h) (hs := uniqueDiffOn_univ) p hp hf m)

theorem AnalyticOn.iteratedFDeriv_codRestrict_submodule
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {f : X → Y} (h : AnalyticOn 𝕜 f univ)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) (hf : MapsTo f univ p)
    {m : ℕ} (x : X) :
    iteratedFDeriv 𝕜 m (Set.codRestrict f p fun y ↦ hf (show y ∈ univ from trivial)) x =
      (iteratedFDeriv 𝕜 m f x).codRestrict p fun v ↦
        (AnalyticOn.iteratedFDeriv_mapsTo_cmlmMapsToSubmodule
          (h := h) p hp hf m (show x ∈ univ from trivial))
          (show v ∈ univ from trivial) := by
  simpa [iteratedFDerivWithin_univ] using
    (AnalyticOn.iteratedFDerivWithin_codRestrict_submodule
      (h := h) (hs := uniqueDiffOn_univ) p hp hf (m := m) (x := x) (hx := by simp))

lemma contDiffOn_codRestrict_submodule
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {s : Set X} (hs : UniqueDiffOn 𝕜 s) {f : X → Y}
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y))
    (hf : MapsTo f univ p) (h : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (Set.codRestrict f p fun x ↦ hf (show x ∈ univ from trivial)) s := by
  have ht : HasFTaylorSeriesUpToOn n f (ftaylorSeriesWithin 𝕜 f s) s :=
    h.ftaylorSeriesWithin hs
  obtain ⟨qSeries, hq⟩ :=
    HasFTaylorSeriesUpToOn.codRestrict_submodule (h := ht) (hs := hs) p hp hf
  exact hq.contDiffOn

lemma contDiffOn_codRestrict_submodule_of_isOpen
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {s : Set X} (hs : IsOpen s) {f : X → Y}
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y))
    (hf : MapsTo f univ p) (h : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (Set.codRestrict f p fun x ↦ hf (show x ∈ univ from trivial)) s :=
  contDiffOn_codRestrict_submodule (𝕜 := 𝕜) (s := s) hs.uniqueDiffOn p hp hf h

theorem ContDiffOn.codRestrict_submodule_of_isOpen
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {s : Set X} {f : X → Y} (h : ContDiffOn 𝕜 n f s) (hs : IsOpen s)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) (hf : MapsTo f univ p) :
    ContDiffOn 𝕜 n (Set.codRestrict f p fun x ↦ hf (show x ∈ univ from trivial)) s :=
  contDiffOn_codRestrict_submodule_of_isOpen (𝕜 := 𝕜) (s := s) hs p hp hf h

theorem ContDiffOn.codRestrict_submodule
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {s : Set X} {f : X → Y} (h : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) (hf : MapsTo f univ p) :
    ContDiffOn 𝕜 n (Set.codRestrict f p fun x ↦ hf (show x ∈ univ from trivial)) s :=
  contDiffOn_codRestrict_submodule (𝕜 := 𝕜) (s := s) hs p hp hf h

open Classical in
theorem ContDiffOn.codRestrict_submodule_piecewise
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {s : Set X} {f : X → Y} (h : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) (hf : MapsTo f s p) :
    ContDiffOn 𝕜 n (fun y ↦ if hy : y ∈ s then (⟨f y, hf hy⟩ : p) else 0) s := by
  let fExt : X → Y := fun y ↦ if hy : y ∈ s then f y else 0
  have hExt : ContDiffOn 𝕜 n fExt s := by
    refine h.congr ?_
    intro y hy
    simp [fExt, hy]
  have hfExt : MapsTo fExt univ p := by
    intro y hy
    by_cases hy' : y ∈ s
    · simpa [fExt, hy'] using hf hy'
    · simp [fExt, hy']
  refine
    (ContDiffOn.codRestrict_submodule (h := hExt) (hs := hs) (p := p) (hp := hp)
      (hf := hfExt)).congr ?_
  intro y hy
  apply Subtype.ext
  simp [fExt, hy]

open Classical in
theorem ContDiffOn.codRestrict_submodule_piecewise_of_ne_top
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {n : WithTop ℕ∞} {s : Set X} {f : X → Y} (h : ContDiffOn 𝕜 n f s) (hn : n ≠ ⊤)
    (hs : UniqueDiffOn 𝕜 s) (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) (hf : MapsTo f s p) :
    ContDiffOn 𝕜 n (fun y ↦ if hy : y ∈ s then (⟨f y, hf hy⟩ : p) else 0) s := by
  rcases WithTop.ne_top_iff_exists.mp hn with ⟨m, rfl⟩
  simpa using
    (ContDiffOn.codRestrict_submodule_piecewise (𝕜 := 𝕜) (n := m) (h := h) (hs := hs)
      (p := p) (hp := hp) (hf := hf))

lemma contDiff_codRestrict_submodule
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {f : X → Y} (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y))
    (hf : MapsTo f univ p) (h : ContDiff 𝕜 n f) :
    ContDiff 𝕜 n (Set.codRestrict f p fun x ↦ hf (show x ∈ univ from trivial)) := by
  simpa [contDiffOn_univ] using
    contDiffOn_codRestrict_submodule (𝕜 := 𝕜) (s := univ) uniqueDiffOn_univ p hp hf
      (contDiffOn_univ.2 h)

theorem ContDiff.codRestrict_submodule
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {f : X → Y} (h : ContDiff 𝕜 n f)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) (hf : MapsTo f univ p) :
    ContDiff 𝕜 n (Set.codRestrict f p fun x ↦ hf (show x ∈ univ from trivial)) :=
  contDiff_codRestrict_submodule (𝕜 := 𝕜) p hp hf h

lemma contDiffOn_codRestrict_submodule_of_ne_top
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {n : WithTop ℕ∞} {s : Set X} (hn : n ≠ ⊤) (hs : UniqueDiffOn 𝕜 s) {f : X → Y}
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y))
    (hf : MapsTo f univ p) (h : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (Set.codRestrict f p fun x ↦ hf (show x ∈ univ from trivial)) s := by
  rcases WithTop.ne_top_iff_exists.mp hn with ⟨m, rfl⟩
  simpa using
    contDiffOn_codRestrict_submodule (𝕜 := 𝕜) (n := m) (X := X) (Y := Y) (s := s) hs p hp hf h

lemma contDiff_codRestrict_submodule_of_ne_top
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {n : WithTop ℕ∞} {f : X → Y} (hn : n ≠ ⊤)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y))
    (hf : MapsTo f univ p) (h : ContDiff 𝕜 n f) :
    ContDiff 𝕜 n (Set.codRestrict f p fun x ↦ hf (show x ∈ univ from trivial)) := by
  simpa [contDiffOn_univ] using
    contDiffOn_codRestrict_submodule_of_ne_top (𝕜 := 𝕜) (n := n) hn uniqueDiffOn_univ p hp hf
      (contDiffOn_univ.2 h)

theorem ContDiffOn.codRestrict_submodule_of_ne_top
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {n : WithTop ℕ∞} {s : Set X} {f : X → Y} (h : ContDiffOn 𝕜 n f s) (hn : n ≠ ⊤)
    (hs : UniqueDiffOn 𝕜 s) (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y))
    (hf : MapsTo f univ p) :
    ContDiffOn 𝕜 n (Set.codRestrict f p fun x ↦ hf (show x ∈ univ from trivial)) s :=
  contDiffOn_codRestrict_submodule_of_ne_top (𝕜 := 𝕜) (n := n) hn hs p hp hf h

theorem ContDiff.codRestrict_submodule_of_ne_top
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {n : WithTop ℕ∞} {f : X → Y} (h : ContDiff 𝕜 n f) (hn : n ≠ ⊤)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) (hf : MapsTo f univ p) :
    ContDiff 𝕜 n (Set.codRestrict f p fun x ↦ hf (show x ∈ univ from trivial)) :=
  contDiff_codRestrict_submodule_of_ne_top (𝕜 := 𝕜) (n := n) hn p hp hf h

theorem ContDiffAt.codRestrict_submodule
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {f : X → Y} {x : X} (h : ContDiffAt 𝕜 n f x)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) (hf : MapsTo f univ p) :
    ContDiffAt 𝕜 n (Set.codRestrict f p fun y ↦ hf (show y ∈ univ from trivial)) x := by
  by_cases hn : n = ⊤
  · have htop : ContDiffAt 𝕜 ((⊤ : ℕ∞) : WithTop ℕ∞) f x := by
      simpa [hn] using h
    have htop_sub :
        ContDiffAt 𝕜 ((⊤ : ℕ∞) : WithTop ℕ∞)
          (Set.codRestrict f p fun y ↦ hf (show y ∈ univ from trivial)) x := by
      rw [contDiffAt_infty] at htop ⊢
      intro m
      have hm : ContDiffAt 𝕜 m f x := htop m
      have hwithin : ContDiffWithinAt 𝕜 m f univ x := by simpa using hm
      rcases (contDiffWithinAt_iff_contDiffOn_nhds (𝕜 := 𝕜) (n := (m : WithTop ℕ∞)) (f := f)
          (s := univ) (x := x) (by simp)).1 hwithin with ⟨u, hu, hcu⟩
      have hu' : u ∈ 𝓝 x := by simpa using hu
      rcases mem_nhds_iff.mp hu' with ⟨v, hvu, hvopen, hxv⟩
      have hcv : ContDiffOn 𝕜 m f v := hcu.mono hvu
      have hsub :
          ContDiffOn 𝕜 m (Set.codRestrict f p fun y ↦ hf (show y ∈ univ from trivial)) v :=
        contDiffOn_codRestrict_submodule_of_isOpen (𝕜 := 𝕜) (s := v) hvopen p hp hf hcv
      exact hsub.contDiffAt (hvopen.mem_nhds hxv)
    simpa [hn] using htop_sub
  · have hwithin : ContDiffWithinAt 𝕜 n f univ x := by simpa using h
    have hn' : ((n : WithTop ℕ∞)) ≠ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
      intro htop
      exact hn (WithTop.coe_eq_coe.mp htop)
    rcases (contDiffWithinAt_iff_contDiffOn_nhds (𝕜 := 𝕜) (n := (n : WithTop ℕ∞)) (f := f)
        (s := univ) (x := x) hn').1 hwithin with ⟨u, hu, hcu⟩
    have hu' : u ∈ 𝓝 x := by simpa using hu
    rcases mem_nhds_iff.mp hu' with ⟨v, hvu, hvopen, hxv⟩
    have hcv : ContDiffOn 𝕜 n f v := hcu.mono hvu
    have hsub :
        ContDiffOn 𝕜 n (Set.codRestrict f p fun y ↦ hf (show y ∈ univ from trivial)) v :=
      contDiffOn_codRestrict_submodule_of_isOpen (𝕜 := 𝕜) (s := v) hvopen p hp hf hcv
    exact hsub.contDiffAt (hvopen.mem_nhds hxv)

theorem ContDiffAt.codRestrict_submodule_of_ne_top
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {n : WithTop ℕ∞} {f : X → Y} {x : X} (h : ContDiffAt 𝕜 n f x) (hn : n ≠ ⊤)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) (hf : MapsTo f univ p) :
    ContDiffAt 𝕜 n (Set.codRestrict f p fun y ↦ hf (show y ∈ univ from trivial)) x := by
  rcases WithTop.ne_top_iff_exists.mp hn with ⟨m, rfl⟩
  simpa using (ContDiffAt.codRestrict_submodule (𝕜 := 𝕜) (n := m) h p hp hf)

theorem ContMDiffOn.codRestrict_submodule
    {E : Type uX} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [IsManifold I n M]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {s : Set M} {f : M → Y}
    (h : ContMDiffOn I (modelWithCornersSelf 𝕜 Y) n f s) (hs : UniqueMDiffOn I s)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) (hf : MapsTo f univ p) :
    ContMDiffOn I (modelWithCornersSelf 𝕜 p) n
      (Set.codRestrict f p fun x ↦ hf (show x ∈ univ from trivial)) s := by
  rw [contMDiffOn_iff] at h ⊢
  refine ⟨?_, ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    simpa [Set.restrict, Function.comp_def, Set.codRestrict] using
      (h.1.mapsToRestrict fun x _ ↦ hf (show x ∈ univ from trivial))
  · intro x y
    let t : Set E := (extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s
    have ht : UniqueDiffOn 𝕜 t := by
      simpa [t] using hs.uniqueDiffOn_target_inter x
    have hf_chart : MapsTo (fun z : E ↦ f ((extChartAt I x).symm z)) univ p := by
      intro z hz
      exact hf (show (extChartAt I x).symm z ∈ univ from trivial)
    have hchart : ContDiffOn 𝕜 n (fun z : E ↦ f ((extChartAt I x).symm z)) t := by
      simpa only [t, mfld_simps] using h.2 x (0 : Y)
    have hchart_sub :
        ContDiffOn 𝕜 n
          (Set.codRestrict (fun z : E ↦ f ((extChartAt I x).symm z)) p
            fun z ↦ hf_chart (show z ∈ univ from trivial)) t :=
      contDiffOn_codRestrict_submodule (𝕜 := 𝕜) (X := E) (Y := Y) (s := t) ht p hp hf_chart
        hchart
    simpa only [t, Set.codRestrict, mfld_simps] using hchart_sub

open Classical in
theorem ContMDiffOn.codRestrict_submodule_piecewise
    {E : Type uX} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [IsManifold I n M]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {s : Set M} {f : M → Y}
    (h : ContMDiffOn I (modelWithCornersSelf 𝕜 Y) n f s) (hs : UniqueMDiffOn I s)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) (hf : MapsTo f s p) :
    ContMDiffOn I (modelWithCornersSelf 𝕜 p) n
      (fun x ↦ if hx : x ∈ s then (⟨f x, hf hx⟩ : p) else 0) s := by
  rw [contMDiffOn_iff] at h ⊢
  refine ⟨?_, ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    simpa [Set.restrict] using
      (Continuous.subtype_mk (show Continuous (Set.restrict s f) from h.1.restrict)
        fun x ↦ hf x.2)
  · intro x y
    let t : Set E := (extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s
    have ht : UniqueDiffOn 𝕜 t := by
      simpa [t] using hs.uniqueDiffOn_target_inter x
    have hf_chart : MapsTo (fun z : E ↦ f ((extChartAt I x).symm z)) t p := by
      intro z hz
      exact hf hz.2
    have hchart : ContDiffOn 𝕜 n (fun z : E ↦ f ((extChartAt I x).symm z)) t := by
      simpa only [t, mfld_simps] using h.2 x (0 : Y)
    have hchart_sub := ContDiffOn.codRestrict_submodule_piecewise
      (h := hchart) (hs := ht) (p := p) (hp := hp) (hf := hf_chart)
    have hchart_piece :
        ContDiffOn 𝕜 n
          (fun z ↦
            if hz : (extChartAt I x).symm z ∈ s then
              (⟨f ((extChartAt I x).symm z), hf hz⟩ : p)
            else 0) t := by
      refine hchart_sub.congr ?_
      intro z hz
      simp only [t, mfld_simps] at hz ⊢
      simp [hz]
    simpa only [t, mfld_simps] using hchart_piece

open Classical in
theorem ContMDiffOn.codRestrict_submodule_piecewise_of_ne_top
    {E : Type uX} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {n : WithTop ℕ∞} [IsManifold I 1 M] [IsManifold I n M]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {s : Set M} {f : M → Y}
    (h : ContMDiffOn I (modelWithCornersSelf 𝕜 Y) n f s) (hn : n ≠ ⊤) (hs : UniqueMDiffOn I s)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) (hf : MapsTo f s p) :
    ContMDiffOn I (modelWithCornersSelf 𝕜 p) n
      (fun x ↦ if hx : x ∈ s then (⟨f x, hf hx⟩ : p) else 0) s := by
  rcases WithTop.ne_top_iff_exists.mp hn with ⟨m, rfl⟩
  simpa using
    (ContMDiffOn.codRestrict_submodule_piecewise
      (𝕜 := 𝕜) (I := I) (n := m) (h := h) (hs := hs) (p := p) (hp := hp) (hf := hf))

theorem ContMDiff.codRestrict_submodule
    {E : Type uX} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [IsManifold I n M]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {f : M → Y}
    (h : ContMDiff I (modelWithCornersSelf 𝕜 Y) n f)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) (hf : MapsTo f univ p) :
    ContMDiff I (modelWithCornersSelf 𝕜 p) n
      (Set.codRestrict f p fun x ↦ hf (show x ∈ univ from trivial)) := by
  simpa [contMDiffOn_univ] using
    (ContMDiffOn.codRestrict_submodule (h := contMDiffOn_univ.2 h) uniqueMDiffOn_univ p hp hf)

theorem ContMDiffOn.codRestrict_submodule_of_ne_top
    {E : Type uX} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {n : WithTop ℕ∞} [IsManifold I 1 M] [IsManifold I n M]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {s : Set M} {f : M → Y}
    (h : ContMDiffOn I (modelWithCornersSelf 𝕜 Y) n f s) (hn : n ≠ ⊤) (hs : UniqueMDiffOn I s)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) (hf : MapsTo f univ p) :
    ContMDiffOn I (modelWithCornersSelf 𝕜 p) n
      (Set.codRestrict f p fun x ↦ hf (show x ∈ univ from trivial)) s := by
  rcases WithTop.ne_top_iff_exists.mp hn with ⟨m, rfl⟩
  simpa using
    (ContMDiffOn.codRestrict_submodule (𝕜 := 𝕜) (n := m) (I := I) (h := h) hs p hp hf)

theorem ContMDiff.codRestrict_submodule_of_ne_top
    {E : Type uX} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {n : WithTop ℕ∞} [IsManifold I 1 M] [IsManifold I n M]
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {f : M → Y}
    (h : ContMDiff I (modelWithCornersSelf 𝕜 Y) n f) (hn : n ≠ ⊤)
    (p : Submodule 𝕜 Y) (hp : IsClosed (p : Set Y)) (hf : MapsTo f univ p) :
    ContMDiff I (modelWithCornersSelf 𝕜 p) n
      (Set.codRestrict f p fun x ↦ hf (show x ∈ univ from trivial)) := by
  rcases WithTop.ne_top_iff_exists.mp hn with ⟨m, rfl⟩
  simpa using (ContMDiff.codRestrict_submodule (𝕜 := 𝕜) (n := m) (I := I) h p hp hf)
