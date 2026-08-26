/-
Copyright (c) 2026 Axiomatic AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Krystian Nowakowski
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Function.SimpleFunc
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.Topology.Bornology.BoundedOperation
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Bounded measurable functions

This file defines bounded measurable functions valued in a normed measurable additive group, and
develops the algebraic API, including the C⋆-algebra structure of `α →ᵇᵐ A` under the supremum
norm. It is the measurable analogue of `BoundedContinuousFunction`.

Blackadar's *Operator Algebras*, III.5.2.13, calls this algebra `B(X)`.

## Main definitions

- `BoundedMeasurableFunction`
- `BoundedMeasurableFunction.ofSimpleFunc`
- `BoundedMeasurableFunction.const`
- `BoundedMeasurableFunction.indicator`

## Notation

- `α →ᵇᵐ E` for bounded measurable functions from `α` to `E`, scoped in `MeasureTheory`.

## Main results

* `MeasureTheory.BoundedMeasurableFunction.instNormedAddCommGroup`, `instNormedRing`,
  `instStarRing`, `instCStarRing`: the C⋆-identity
* `MeasureTheory.BoundedMeasurableFunction.instCompleteSpace`: completeness in the supremum norm
* `MeasureTheory.BoundedMeasurableFunction.instCStarAlgebra`: `α →ᵇᵐ A` is a C⋆-algebra when `A`
  is one
* `ContinuousMap.toBoundedMeasurableFunction : C(α, A) →⋆ₐ[𝕜] (α →ᵇᵐ A)`: the unital `⋆`-hom
  forgetting continuity, injective and isometric
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped Pointwise

namespace MeasureTheory

/-- A bounded measurable function on a measurable space `α` taking values in a normed measurable
space `E`. -/
structure BoundedMeasurableFunction (α : Type*) (E : Type*)
    [MeasurableSpace α] [NormedAddCommGroup E] [MeasurableSpace E] where
  /-- The underlying function. -/
  toFun : α → E
  /-- The underlying function is measurable. -/
  measurable' : Measurable toFun
  /-- The range of the underlying function is bounded. -/
  bounded' : Bornology.IsBounded (range toFun)

@[inherit_doc] scoped[MeasureTheory] infixr:25 " →ᵇᵐ " => MeasureTheory.BoundedMeasurableFunction

namespace BoundedMeasurableFunction

section Basics

variable {α E 𝕜 : Type*}
variable [MeasurableSpace α]
variable [NormedAddCommGroup E] [MeasurableSpace E]

instance instFunLike : FunLike (BoundedMeasurableFunction α E) α E where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr

theorem coe_injective :
    Function.Injective ((↑) : BoundedMeasurableFunction α E → α → E) :=
  DFunLike.coe_injective

@[ext]
theorem ext {f g : BoundedMeasurableFunction α E} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

theorem measurable (f : BoundedMeasurableFunction α E) : Measurable f :=
  f.measurable'

theorem isBounded_range (f : BoundedMeasurableFunction α E) :
    Bornology.IsBounded (range f) :=
  f.bounded'

/-- A continuous function on a compact space, viewed as a bounded measurable function. -/
noncomputable def ofContinuous {α E : Type*}
    [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α] [BorelSpace α]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (f : C(α, E)) : BoundedMeasurableFunction α E where
  toFun := f
  measurable' := f.continuous.measurable
  bounded' := by
    simpa using (isCompact_range f.continuous).isBounded

@[simp]
lemma ofContinuous_apply {α E : Type*}
    [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α] [BorelSpace α]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (f : C(α, E)) (x : α) :
    ofContinuous f x = f x :=
  rfl

instance instZero : Zero (BoundedMeasurableFunction α E) where
  zero :=
    { toFun := 0
      measurable' := measurable_const
      bounded' := Bornology.IsBounded.subset Bornology.isBounded_singleton Set.range_const_subset }

instance instOne [One E] : One (BoundedMeasurableFunction α E) where
  one :=
    { toFun := 1
      measurable' := measurable_const
      bounded' := Bornology.IsBounded.subset Bornology.isBounded_singleton Set.range_const_subset }

instance instAdd [MeasurableAdd₂ E] : Add (BoundedMeasurableFunction α E) where
  add f g :=
    { toFun := f + g
      measurable' := f.measurable.add g.measurable
      bounded' := by
        rcases f.isBounded_range.exists_norm_le with ⟨Cf, hCf⟩
        rcases g.isBounded_range.exists_norm_le with ⟨Cg, hCg⟩
        refine (isBounded_iff_forall_norm_le).2 ?_
        refine ⟨Cf + Cg, ?_⟩
        rintro _ ⟨x, rfl⟩
        exact (norm_add_le _ _).trans
          (add_le_add (hCf _ (mem_range_self x)) (hCg _ (mem_range_self x))) }

instance instNeg [MeasurableNeg E] : Neg (BoundedMeasurableFunction α E) where
  neg f :=
    { toFun := -f
      measurable' := f.measurable.neg
      bounded' := by
        rcases f.isBounded_range.exists_norm_le with ⟨Cf, hCf⟩
        refine (isBounded_iff_forall_norm_le).2 ?_
        refine ⟨Cf, ?_⟩
        rintro _ ⟨x, rfl⟩
        simpa using hCf _ (mem_range_self x) }

instance instSub [MeasurableSub₂ E] : Sub (BoundedMeasurableFunction α E) where
  sub f g :=
    { toFun := f - g
      measurable' := f.measurable.sub g.measurable
      bounded' := by
        rcases f.isBounded_range.exists_norm_le with ⟨Cf, hCf⟩
        rcases g.isBounded_range.exists_norm_le with ⟨Cg, hCg⟩
        refine (isBounded_iff_forall_norm_le).2 ?_
        refine ⟨Cf + Cg, ?_⟩
        rintro _ ⟨x, rfl⟩
        exact (norm_sub_le _ _).trans
          (add_le_add (hCf _ (mem_range_self x)) (hCg _ (mem_range_self x))) }

instance instSMulNat [MeasurableAdd₂ E] : SMul ℕ (BoundedMeasurableFunction α E) where
  smul n f :=
    { toFun := fun x ↦ n • f x
      measurable' := by
        induction n with
        | zero =>
            simp
        | succ n ihn =>
            have : (fun x ↦ (n + 1) • f x) = (fun x ↦ n • f x) + (f : α → E) := by
              ext x; exact succ_nsmul (f x) n
            rw [this]
            exact ihn.add f.measurable
      bounded' := by
        rcases f.isBounded_range.exists_norm_le with ⟨Cf, hCf⟩
        refine (isBounded_iff_forall_norm_le).2 ?_
        refine ⟨n * Cf, ?_⟩
        rintro _ ⟨x, rfl⟩
        exact (norm_nsmul_le (a := f x) (n := n)).trans <| by
          gcongr
          exact hCf _ (mem_range_self x) }

instance instSMulInt [MeasurableAdd₂ E] [MeasurableNeg E] :
    SMul ℤ (BoundedMeasurableFunction α E) where
  smul n f :=
    match n with
    | .ofNat m => m • f
    | .negSucc m => -((m.succ : ℕ) • f)

@[simp]
lemma zero_apply (x : α) : (0 : BoundedMeasurableFunction α E) x = 0 :=
  rfl

@[simp]
lemma one_apply [One E] (x : α) : (1 : BoundedMeasurableFunction α E) x = 1 :=
  rfl

@[simp]
lemma add_apply [MeasurableAdd₂ E] (f g : BoundedMeasurableFunction α E) (x : α) :
    (f + g) x = f x + g x :=
  rfl

@[simp]
lemma neg_apply [MeasurableNeg E] (f : BoundedMeasurableFunction α E) (x : α) :
    (-f) x = -f x :=
  rfl

@[simp]
lemma sub_apply [MeasurableSub₂ E] (f g : BoundedMeasurableFunction α E) (x : α) :
    (f - g) x = f x - g x :=
  rfl

@[simp]
lemma nsmul_apply [MeasurableAdd₂ E] (n : ℕ) (f : BoundedMeasurableFunction α E) (x : α) :
    (n • f) x = n • f x :=
  rfl

@[simp]
theorem zsmul_apply [MeasurableAdd₂ E] [MeasurableNeg E]
    (n : ℤ) (f : BoundedMeasurableFunction α E) (x : α) :
    (n • f) x = n • f x := by
  cases n with
  | ofNat m =>
      change ((m : ℕ) • f) x = (m : ℤ) • f x
      rw [nsmul_apply]
      simp
  | negSucc m =>
      change (-((m.succ : ℕ) • f)) x = (Int.negSucc m) • f x
      rw [neg_apply, nsmul_apply]
      simp

@[simp]
lemma coe_zero : ((0 : BoundedMeasurableFunction α E) : α → E) = 0 :=
  rfl

@[simp]
lemma coe_one [One E] : ((1 : BoundedMeasurableFunction α E) : α → E) = 1 :=
  rfl

@[simp]
lemma coe_add [MeasurableAdd₂ E] (f g : BoundedMeasurableFunction α E) :
    ((f + g : BoundedMeasurableFunction α E) : α → E) = f + g :=
  rfl

@[simp]
lemma coe_neg [MeasurableNeg E] (f : BoundedMeasurableFunction α E) :
    ((-f : BoundedMeasurableFunction α E) : α → E) = -f :=
  rfl

@[simp]
lemma coe_sub [MeasurableSub₂ E] (f g : BoundedMeasurableFunction α E) :
    ((f - g : BoundedMeasurableFunction α E) : α → E) = f - g :=
  rfl

@[simp]
lemma coe_nsmul [MeasurableAdd₂ E] (f : BoundedMeasurableFunction α E) (n : ℕ) :
    ((n • f : BoundedMeasurableFunction α E) : α → E) = n • f :=
  rfl

@[simp]
theorem coe_zsmul [MeasurableAdd₂ E] [MeasurableNeg E]
    (f : BoundedMeasurableFunction α E) (n : ℤ) :
    ((n • f : BoundedMeasurableFunction α E) : α → E) = n • f := by
  ext x
  exact zsmul_apply n f x

instance instAddCommGroup [MeasurableAdd₂ E] [MeasurableNeg E] [MeasurableSub₂ E] :
    AddCommGroup (BoundedMeasurableFunction α E) :=
  Function.Injective.addCommGroup (M₁ := BoundedMeasurableFunction α E) (M₂ := α → E)
    _ coe_injective coe_zero coe_add coe_neg coe_sub coe_nsmul coe_zsmul

instance instSMul [NormedField 𝕜] [MeasurableSpace 𝕜] [NormedSpace 𝕜 E]
    [MeasurableSMul₂ 𝕜 E] : SMul 𝕜 (BoundedMeasurableFunction α E) where
  smul c f :=
    { toFun := c • f
      measurable' := measurable_const.smul f.measurable
      bounded' := by
        rcases f.isBounded_range.exists_norm_le with ⟨Cf, hCf⟩
        refine (isBounded_iff_forall_norm_le).2 ?_
        refine ⟨‖c‖ * Cf, ?_⟩
        rintro _ ⟨x, rfl⟩
        calc
          ‖c • f x‖ = ‖c‖ * ‖f x‖ := norm_smul c (f x)
          _ ≤ ‖c‖ * Cf := by
            gcongr
            exact hCf _ (mem_range_self x) }

@[simp]
lemma smul_apply [NormedField 𝕜] [MeasurableSpace 𝕜] [NormedSpace 𝕜 E]
    [MeasurableSMul₂ 𝕜 E] (c : 𝕜) (f : BoundedMeasurableFunction α E) (x : α) :
    (c • f) x = c • f x :=
  rfl

@[simp]
lemma coe_smul [NormedField 𝕜] [MeasurableSpace 𝕜] [NormedSpace 𝕜 E]
    [MeasurableSMul₂ 𝕜 E] (c : 𝕜) (f : BoundedMeasurableFunction α E) :
    ((c • f : BoundedMeasurableFunction α E) : α → E) = c • f :=
  rfl

instance instModule [NormedField 𝕜] [MeasurableSpace 𝕜] [NormedSpace 𝕜 E]
    [MeasurableAdd₂ E] [MeasurableNeg E] [MeasurableSub₂ E] [MeasurableSMul₂ 𝕜 E] :
    Module 𝕜 (BoundedMeasurableFunction α E) :=
  Function.Injective.module 𝕜
    ⟨⟨fun f ↦ show α → E from f, coe_zero⟩, coe_add⟩
    coe_injective coe_smul

instance instMul [Mul E] [BoundedMul E] [MeasurableMul₂ E] :
    Mul (BoundedMeasurableFunction α E) where
  mul f g :=
    { toFun := f * g
      measurable' := f.measurable.mul g.measurable
      bounded' := by
        refine Bornology.IsBounded.subset (isBounded_mul f.isBounded_range g.isBounded_range) ?_
        rintro z ⟨x, rfl⟩
        exact Set.mul_mem_mul (Set.mem_range_self (f := f) x) (Set.mem_range_self (f := g) x) }

instance instPow [Monoid E] [BoundedMul E] [MeasurableMul₂ E] :
    Pow (BoundedMeasurableFunction α E) ℕ where
  pow f n :=
    { toFun := f ^ n
      measurable' := f.measurable.pow_const n
      bounded' := by
        refine Bornology.IsBounded.subset (isBounded_pow f.isBounded_range n) ?_
        rintro z ⟨x, rfl⟩
        exact ⟨f x, Set.mem_range_self (f := f) x, rfl⟩ }

@[simp]
lemma mul_apply [Mul E] [BoundedMul E] [MeasurableMul₂ E]
    (f g : BoundedMeasurableFunction α E) (x : α) :
    (f * g) x = f x * g x :=
  rfl

@[simp]
lemma pow_apply [Monoid E] [BoundedMul E] [MeasurableMul₂ E]
    (f : BoundedMeasurableFunction α E) (n : ℕ) (x : α) :
    (f ^ n) x = f x ^ n :=
  rfl

@[simp]
lemma coe_mul [Mul E] [BoundedMul E] [MeasurableMul₂ E]
    (f g : BoundedMeasurableFunction α E) :
    ((f * g : BoundedMeasurableFunction α E) : α → E) = f * g :=
  rfl

@[simp]
lemma coe_pow [Monoid E] [BoundedMul E] [MeasurableMul₂ E]
    (f : BoundedMeasurableFunction α E) (n : ℕ) :
    ((f ^ n : BoundedMeasurableFunction α E) : α → E) = f ^ n :=
  rfl

instance instMulOneClass [MulOneClass E] [BoundedMul E] [MeasurableMul₂ E] :
    MulOneClass (BoundedMeasurableFunction α E) :=
  DFunLike.coe_injective.mulOneClass _ coe_one coe_mul

instance instMonoid [Monoid E] [BoundedMul E] [MeasurableMul₂ E] :
    Monoid (BoundedMeasurableFunction α E) :=
  Function.Injective.monoid
    (fun f : BoundedMeasurableFunction α E => show α → E from f)
    coe_injective coe_one coe_mul coe_pow

instance instCommMonoid [CommMonoid E] [BoundedMul E] [MeasurableMul₂ E] :
    CommMonoid (BoundedMeasurableFunction α E) :=
  Function.Injective.commMonoid
    (fun f : BoundedMeasurableFunction α E => show α → E from f)
    coe_injective coe_one coe_mul coe_pow

instance instStar [TopologicalSpace E] [BorelSpace E] [StarAddMonoid E] [NormedStarGroup E]
    [ContinuousStar E] : Star (BoundedMeasurableFunction α E) where
  star f :=
    { toFun := star f
      measurable' := continuous_star.measurable.comp f.measurable
      bounded' := by
        rcases f.isBounded_range.exists_norm_le with ⟨C, hC⟩
        refine (isBounded_iff_forall_norm_le).2 ?_
        refine ⟨C, ?_⟩
        rintro z ⟨x, rfl⟩
        simpa [norm_star] using hC _ (Set.mem_range_self (f := f) x) }

@[simp]
lemma star_apply [TopologicalSpace E] [BorelSpace E] [StarAddMonoid E] [NormedStarGroup E]
    [ContinuousStar E] (f : BoundedMeasurableFunction α E) (x : α) :
    (star f) x = star (f x) :=
  rfl

@[simp]
lemma coe_star [TopologicalSpace E] [BorelSpace E] [StarAddMonoid E] [NormedStarGroup E]
    [ContinuousStar E] (f : BoundedMeasurableFunction α E) :
    ⇑(star f) = star (⇑f : α → E) :=
  rfl

theorem star_add_eq [TopologicalSpace E] [BorelSpace E] [MeasurableAdd₂ E]
    [MeasurableNeg E] [MeasurableSub₂ E] [StarAddMonoid E] [NormedStarGroup E]
    [ContinuousStar E] (f g : BoundedMeasurableFunction α E) :
    star (f + g) = star f + star g := by
  apply DFunLike.coe_injective
  funext x
  simp [star_add]

/-- Precompose a bounded measurable function with a measurable map. -/
noncomputable def compMeasurable {β : Type*} [MeasurableSpace β]
    (f : BoundedMeasurableFunction β E) (g : α → β) (hg : Measurable g) :
    BoundedMeasurableFunction α E where
  toFun := fun x ↦ f (g x)
  measurable' := f.measurable.comp hg
  bounded' := by
    refine Bornology.IsBounded.subset f.isBounded_range ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨g x, rfl⟩

@[simp]
lemma compMeasurable_apply {β : Type*} [MeasurableSpace β]
    (f : BoundedMeasurableFunction β E) (g : α → β) (hg : Measurable g) (x : α) :
    f.compMeasurable g hg x = f (g x) :=
  rfl

@[simp]
lemma coe_compMeasurable {β : Type*} [MeasurableSpace β]
    (f : BoundedMeasurableFunction β E) (g : α → β) (hg : Measurable g) :
    ((f.compMeasurable g hg : BoundedMeasurableFunction α E) : α → E) = f ∘ g :=
  rfl

/-- Any measurable simple function defines a bounded measurable function. -/
noncomputable def ofSimpleFunc (f : SimpleFunc α E) : BoundedMeasurableFunction α E where
  toFun := f
  measurable' := f.measurable
  bounded' := by
    refine Bornology.IsBounded.subset (Set.Finite.isBounded f.finite_range) ?_
    rintro y ⟨x, rfl⟩
    exact mem_range_self x

/-- The coercion of `ofSimpleFunc f` to a function is `f` itself.

The pointwise `ofSimpleFunc_apply` cannot rewrite underneath a coercion `⇑(ofSimpleFunc f)`,
which is the form in which the function appears in `Integrable.toL1` and friends; this is the
`funext`ed companion that mathlib's naming convention pairs with it. -/
@[simp]
lemma coe_ofSimpleFunc (f : SimpleFunc α E) : ⇑(ofSimpleFunc f) = ⇑f := rfl

@[simp]
lemma ofSimpleFunc_apply (f : SimpleFunc α E) (x : α) :
    ofSimpleFunc f x = f x :=
  rfl

@[simp]
theorem star_ofSimpleFunc [TopologicalSpace E] [BorelSpace E] [StarAddMonoid E]
    [NormedStarGroup E] [ContinuousStar E] (f : SimpleFunc α E) :
    star (ofSimpleFunc f) = ofSimpleFunc (star f) := by
  ext x
  rfl

/-- Constant bounded measurable functions. -/
noncomputable def const (α : Type*) [MeasurableSpace α] (c : E) :
    BoundedMeasurableFunction α E :=
  ofSimpleFunc (SimpleFunc.const α c)

@[simp]
lemma const_apply (c : E) (x : α) : const α c x = c :=
  rfl

/-- Indicator functions of measurable sets, viewed as bounded measurable functions. -/
noncomputable def indicator (α : Type*) [MeasurableSpace α] (u : Set α) (hu : MeasurableSet u)
    [One E] : BoundedMeasurableFunction α E :=
  ofSimpleFunc (SimpleFunc.piecewise u hu (SimpleFunc.const α 1) (SimpleFunc.const α 0))

open scoped Classical in
@[simp]
lemma indicator_apply [One E] (u : Set α) (hu : MeasurableSet u) (x : α) :
    indicator α u hu x = if x ∈ u then (1 : E) else (0 : E) :=
  rfl

end Basics

section SupNorm

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [MeasurableSpace E]

/-! ### The supremum norm

`BoundedMeasurableFunction` is the measurable analogue of `BoundedContinuousFunction`, and carries
the same supremum norm; into a C⋆-algebra it is again a C⋆-algebra, the C⋆-identity holding
pointwise. -/

theorem exists_norm_le (f : α →ᵇᵐ E) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isBounded_iff_forall_norm_le.1 f.isBounded_range)
  exact ⟨max C 0, le_max_right _ _, fun x => (hC _ ⟨x, rfl⟩).trans (le_max_left _ _)⟩

/-- The supremum norm of a bounded measurable function, as the least bound. -/
noncomputable instance instNorm : Norm (α →ᵇᵐ E) where
  norm f := sInf {C | 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C}

theorem norm_def (f : α →ᵇᵐ E) : ‖f‖ = sInf {C | 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C} := rfl

private theorem bounds_nonempty (f : α →ᵇᵐ E) :
    ∃ C, C ∈ {C | 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C} := exists_norm_le f

private theorem bounds_bddBelow (f : α →ᵇᵐ E) :
    BddBelow {C | 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C} := ⟨0, fun _ hC => hC.1⟩

theorem norm_nonneg' (f : α →ᵇᵐ E) : 0 ≤ ‖f‖ :=
  le_csInf (bounds_nonempty f) fun _ hC => hC.1

theorem norm_coe_le_norm (f : α →ᵇᵐ E) (x : α) : ‖f x‖ ≤ ‖f‖ :=
  le_csInf (bounds_nonempty f) fun _ hC => hC.2 x

theorem norm_le_of_forall {f : α →ᵇᵐ E} {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, ‖f x‖ ≤ C) : ‖f‖ ≤ C :=
  csInf_le (bounds_bddBelow f) ⟨hC, h⟩

theorem norm_le {f : α →ᵇᵐ E} {C : ℝ} (hC : 0 ≤ C) : ‖f‖ ≤ C ↔ ∀ x, ‖f x‖ ≤ C :=
  ⟨fun h x => (norm_coe_le_norm f x).trans h, norm_le_of_forall hC⟩

theorem norm_eq_zero_iff [MeasurableAdd₂ E] [MeasurableNeg E] [MeasurableSub₂ E]
    {f : α →ᵇᵐ E} : ‖f‖ = 0 ↔ f = 0 := by
  refine ⟨fun h => ext fun x => ?_, fun h => ?_⟩
  · have := norm_coe_le_norm f x
    rw [h] at this
    exact norm_le_zero_iff.1 this
  · subst h
    exact le_antisymm (norm_le_of_forall le_rfl fun x => by simp) (norm_nonneg' _)

/-- **Bounded measurable functions form a normed additive group** under the supremum norm. -/
noncomputable instance instNormedAddCommGroup [MeasurableAdd₂ E] [MeasurableNeg E]
    [MeasurableSub₂ E] : NormedAddCommGroup (α →ᵇᵐ E) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := fun f => ‖f‖
      map_zero' := le_antisymm (norm_le_of_forall le_rfl fun x => by simp) (norm_nonneg' _)
      add_le' := fun f g =>
        norm_le_of_forall (add_nonneg (norm_nonneg' f) (norm_nonneg' g)) fun x => by
          calc ‖(f + g) x‖ = ‖f x + g x‖ := by rw [add_apply]
            _ ≤ ‖f x‖ + ‖g x‖ := norm_add_le _ _
            _ ≤ ‖f‖ + ‖g‖ := add_le_add (norm_coe_le_norm f x) (norm_coe_le_norm g x)
      neg' := fun f => le_antisymm
        (norm_le_of_forall (norm_nonneg' f) fun x => by
          rw [neg_apply, norm_neg]; exact norm_coe_le_norm f x)
        (norm_le_of_forall (norm_nonneg' _) fun x => by
          rw [show f x = -((-f) x) by rw [neg_apply, neg_neg], norm_neg]
          exact norm_coe_le_norm (-f) x)
      eq_zero_of_map_eq_zero' := fun f h => norm_eq_zero_iff.1 h }

section CStar

variable {A : Type*} [NormedRing A] [MeasurableSpace A] [BorelSpace A] [MeasurableAdd₂ A]
  [MeasurableNeg A] [MeasurableSub₂ A] [MeasurableMul₂ A] [BoundedMul A]

/-- **Bounded measurable functions into a ring form a ring**, pointwise. -/
instance instRing : Ring (α →ᵇᵐ A) where
  __ := instAddCommGroup
  __ := instMonoid
  left_distrib _ _ _ := ext fun _ => mul_add _ _ _
  right_distrib _ _ _ := ext fun _ => add_mul _ _ _
  zero_mul _ := ext fun _ => zero_mul _
  mul_zero _ := ext fun _ => mul_zero _

omit [BorelSpace A] [MeasurableAdd₂ A] [MeasurableNeg A] [MeasurableSub₂ A] in
theorem norm_mul_le' (f g : α →ᵇᵐ A) : ‖f * g‖ ≤ ‖f‖ * ‖g‖ :=
  norm_le_of_forall (mul_nonneg (norm_nonneg' f) (norm_nonneg' g)) fun x => by
    calc ‖(f * g) x‖ = ‖f x * g x‖ := by rw [mul_apply]
      _ ≤ ‖f x‖ * ‖g x‖ := norm_mul_le _ _
      _ ≤ ‖f‖ * ‖g‖ :=
          mul_le_mul (norm_coe_le_norm f x) (norm_coe_le_norm g x) (norm_nonneg _)
            (norm_nonneg' f)

/-- **Bounded measurable functions into a normed ring form a normed ring.** -/
noncomputable instance instNormedRing : NormedRing (α →ᵇᵐ A) where
  __ := instNormedAddCommGroup
  __ := instRing
  norm_mul_le := norm_mul_le'

variable {B : Type*} [NormedAddCommGroup B] [MeasurableSpace B] [BorelSpace B]
  [StarAddMonoid B] [NormedStarGroup B] [MeasurableAdd₂ B] [MeasurableNeg B] [MeasurableSub₂ B]

omit [MeasurableAdd₂ B] [MeasurableNeg B] [MeasurableSub₂ B] in
@[simp] theorem norm_star (f : α →ᵇᵐ B) : ‖star f‖ = ‖f‖ := by
  refine le_antisymm (norm_le_of_forall (norm_nonneg' f) fun x => ?_)
    (norm_le_of_forall (norm_nonneg' _) fun x => ?_)
  · rw [star_apply, _root_.norm_star]
    exact norm_coe_le_norm f x
  · rw [show f x = star (star f x) by rw [star_apply, star_star], _root_.norm_star]
    exact norm_coe_le_norm (star f) x

section CStarRing

variable {A : Type*} [NormedRing A] [StarRing A] [CStarRing A] [MeasurableSpace A] [BorelSpace A]
  [MeasurableAdd₂ A] [MeasurableNeg A] [MeasurableSub₂ A] [MeasurableMul₂ A] [BoundedMul A]
  [NormedStarGroup A]

/-- **Bounded measurable functions into a star ring form a star ring**, pointwise. -/
instance instStarRing : StarRing (α →ᵇᵐ A) where
  star_involutive _ := ext fun _ => star_star _
  star_mul _ _ := ext fun _ => star_mul _ _
  star_add _ _ := ext fun _ => star_add _ _

/-- **The C⋆-identity holds pointwise, hence in the supremum norm**: bounded measurable functions
into a C⋆-algebra form a C⋆-ring. -/
instance instCStarRing : CStarRing (α →ᵇᵐ A) where
  norm_mul_self_le f := by
    have hM : (0:ℝ) ≤ ‖star f * f‖ := norm_nonneg _
    have hle : ‖f‖ ≤ Real.sqrt ‖star f * f‖ := by
      refine norm_le_of_forall (Real.sqrt_nonneg _) fun x => ?_
      rw [← Real.sqrt_sq (norm_nonneg (f x))]
      refine Real.sqrt_le_sqrt ?_
      calc ‖f x‖ ^ 2 = ‖star (f x) * f x‖ := by
            rw [CStarRing.norm_star_mul_self, sq]
        _ = ‖(star f * f) x‖ := by rw [mul_apply, star_apply]
        _ ≤ ‖star f * f‖ := norm_coe_le_norm _ x
    calc ‖f‖ * ‖f‖ = ‖f‖ ^ 2 := (sq ‖f‖).symm
      _ ≤ (Real.sqrt ‖star f * f‖) ^ 2 := by
          refine pow_le_pow_left₀ (norm_nonneg' f) hle 2
      _ = ‖star f * f‖ := Real.sq_sqrt hM

end CStarRing

end CStar

end SupNorm


section Completeness

open scoped Topology

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [MeasurableSpace E]
  [BorelSpace E] [MeasurableAdd₂ E] [MeasurableNeg E] [MeasurableSub₂ E] [CompleteSpace E]

/-- **The bounded measurable functions are complete in the supremum norm.**

Each orbit of a Cauchy sequence is Cauchy, so the sequence converges pointwise; the limit is
measurable as a pointwise limit of measurable functions and bounded because a Cauchy sequence is
bounded, and the convergence is uniform by passing the Cauchy estimate to the limit in each
orbit. -/
instance instCompleteSpace : CompleteSpace (α →ᵇᵐ E) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  have hdist : ∀ (m n : ℕ) (x : α), ‖u m x - u n x‖ ≤ dist (u m) (u n) := fun m n x => by
    rw [dist_eq_norm, ← sub_apply]
    exact norm_coe_le_norm _ x
  have hptCauchy : ∀ x, CauchySeq fun n => u n x := fun x => by
    refine Metric.cauchySeq_iff.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu ε hε
    exact ⟨N, fun m hm n hn => lt_of_le_of_lt (by rw [dist_eq_norm]; exact hdist m n x)
      (hN m hm n hn)⟩
  choose g hg using fun x => cauchySeq_tendsto_of_complete (hptCauchy x)
  obtain ⟨R, -, hR⟩ := cauchySeq_bdd hu
  set C : ℝ := R + ‖u 0‖ with hCdef
  have hC : ∀ n, ‖u n‖ ≤ C := fun n => by
    have h0 : ‖u n - u 0‖ ≤ R := by
      rw [← dist_eq_norm]; exact (hR n 0).le
    calc ‖u n‖ = ‖u n - u 0 + u 0‖ := by rw [sub_add_cancel]
      _ ≤ ‖u n - u 0‖ + ‖u 0‖ := norm_add_le _ _
      _ ≤ C := by rw [hCdef]; linarith
  have hgle : ∀ x, ‖g x‖ ≤ C := fun x =>
    le_of_tendsto (hg x).norm
      (Filter.Eventually.of_forall fun n => (norm_coe_le_norm (u n) x).trans (hC n))
  have hmeas : Measurable g :=
    measurable_of_tendsto_metrizable (fun n => (u n).measurable) (tendsto_pi_nhds.2 hg)
  have hbdd : Bornology.IsBounded (Set.range g) :=
    isBounded_iff_forall_norm_le.2 ⟨C, by rintro _ ⟨x, rfl⟩; exact hgle x⟩
  refine ⟨⟨g, hmeas, hbdd⟩, Metric.tendsto_atTop.2 fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu (ε / 2) (by positivity)
  refine ⟨N + 1, fun n hn => ?_⟩
  rw [dist_eq_norm]
  refine lt_of_le_of_lt (norm_le_of_forall (by positivity : (0:ℝ) ≤ ε / 2) fun x => ?_)
    (by linarith)
  have hlim : Filter.Tendsto (fun m => ‖u n x - u m x‖) Filter.atTop (𝓝 ‖u n x - g x‖) :=
    (tendsto_const_nhds.sub (hg x)).norm
  have : ‖u n x - g x‖ ≤ ε / 2 := by
    refine le_of_tendsto hlim ?_
    filter_upwards [Filter.eventually_ge_atTop (N + 1)] with m hm
    exact (hdist n m x).trans (hN n (by omega) m (by omega)).le
  rw [sub_apply]
  exact this

end Completeness


section AlgebraStructure

variable {α : Type*} [MeasurableSpace α] {𝕜 A : Type*} [NormedField 𝕜] [MeasurableSpace 𝕜]
  [NormedRing A] [NormedAlgebra 𝕜 A] [MeasurableSpace A] [BorelSpace A]
  [MeasurableAdd₂ A] [MeasurableNeg A] [MeasurableSub₂ A] [MeasurableMul₂ A] [BoundedMul A]
  [MeasurableSMul₂ 𝕜 A]

/-- **Bounded measurable functions into a normed algebra form an algebra**, pointwise. -/
noncomputable instance instAlgebra : Algebra 𝕜 (α →ᵇᵐ A) :=
  Algebra.ofModule (fun r f g => ext fun x => smul_mul_assoc r (f x) (g x))
    (fun r f g => ext fun x => mul_smul_comm r (f x) (g x))

/-- **The supremum norm is an algebra norm.** -/
noncomputable instance instNormedAlgebra : NormedAlgebra 𝕜 (α →ᵇᵐ A) where
  norm_smul_le r f := by
    refine norm_le_of_forall (by positivity) fun x => ?_
    rw [smul_apply]
    exact (norm_smul_le r (f x)).trans (by gcongr; exact norm_coe_le_norm f x)

end AlgebraStructure

section StarAlgebraStructure

variable {α : Type*} [MeasurableSpace α] {𝕜 A : Type*} [NormedField 𝕜] [MeasurableSpace 𝕜]
  [StarRing 𝕜] [NormedRing A] [StarRing A] [CStarRing A] [NormedAlgebra 𝕜 A] [StarModule 𝕜 A]
  [MeasurableSpace A] [BorelSpace A] [MeasurableAdd₂ A] [MeasurableNeg A] [MeasurableSub₂ A]
  [MeasurableMul₂ A] [BoundedMul A] [MeasurableSMul₂ 𝕜 A] [NormedStarGroup A]

/-- **The star operation is conjugate-linear**, pointwise. -/
instance instStarModule : StarModule 𝕜 (α →ᵇᵐ A) where
  star_smul r f := ext fun x => star_smul r (f x)

end StarAlgebraStructure

section CStarAlgebraInstance

variable {α : Type*} [MeasurableSpace α] {A : Type*} [NormedRing A] [StarRing A] [CStarRing A]
  [NormedAlgebra ℂ A] [StarModule ℂ A] [CompleteSpace A] [MeasurableSpace A] [BorelSpace A]
  [MeasurableAdd₂ A] [MeasurableNeg A] [MeasurableSub₂ A] [MeasurableMul₂ A] [BoundedMul A]
  [MeasurableSMul₂ ℂ A] [NormedStarGroup A]

/-- **The bounded measurable functions into a C⋆-algebra form a C⋆-algebra**, under the supremum
norm. -/
noncomputable instance instCStarAlgebra : CStarAlgebra (α →ᵇᵐ A) where
  __ := instNormedRing
  __ := instStarRing
  __ := instCompleteSpace
  __ := instCStarRing
  __ := instNormedAlgebra
  __ := instStarModule

end CStarAlgebraInstance


section ContinuousMapHom

variable {α : Type*} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α] [BorelSpace α]
  {𝕜 A : Type*} [NormedField 𝕜] [MeasurableSpace 𝕜] [StarRing 𝕜]
  [NormedRing A] [StarRing A] [NormedAlgebra 𝕜 A] [StarModule 𝕜 A] [MeasurableSpace A]
  [BorelSpace A] [MeasurableAdd₂ A] [MeasurableNeg A] [MeasurableSub₂ A] [MeasurableMul₂ A]
  [BoundedMul A] [MeasurableSMul₂ 𝕜 A] [NormedStarGroup A] [ContinuousStar A]

/-- **A continuous function on a compact space is a bounded measurable function**, as a unital
`⋆`-algebra homomorphism `C(α, A) →⋆ₐ[𝕜] (α →ᵇᵐ A)`.  It is injective and isometric: it forgets
continuity and nothing else. -/
noncomputable def _root_.ContinuousMap.toBoundedMeasurableFunction :
    C(α, A) →⋆ₐ[𝕜] (α →ᵇᵐ A) where
  toFun := ofContinuous
  map_one' := ext fun _ => rfl
  map_mul' _ _ := ext fun _ => rfl
  map_zero' := ext fun _ => rfl
  map_add' _ _ := ext fun _ => rfl
  commutes' r := ext fun x => by
    change (algebraMap 𝕜 C(α, A) r) x = (algebraMap 𝕜 (α →ᵇᵐ A) r) x
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    rfl
  map_star' _ := ext fun _ => rfl

omit [StarRing 𝕜] [StarModule 𝕜 A] in
@[simp] theorem _root_.ContinuousMap.toBoundedMeasurableFunction_apply (f : C(α, A)) (x : α) :
    ContinuousMap.toBoundedMeasurableFunction (𝕜 := 𝕜) f x = f x := rfl

omit [StarRing 𝕜] [StarModule 𝕜 A] in
/-- The `⋆`-hom is injective: it only forgets continuity. -/
theorem _root_.ContinuousMap.toBoundedMeasurableFunction_injective :
    Function.Injective (ContinuousMap.toBoundedMeasurableFunction (α := α) (A := A) (𝕜 := 𝕜)) :=
  fun f g h => ContinuousMap.ext fun x => by
    simpa using congrArg (fun F : α →ᵇᵐ A => F x) h

omit [StarRing 𝕜] [StarModule 𝕜 A] in
/-- The `⋆`-hom is isometric for the supremum norms. -/
theorem _root_.ContinuousMap.norm_toBoundedMeasurableFunction (f : C(α, A)) :
    ‖ContinuousMap.toBoundedMeasurableFunction (𝕜 := 𝕜) f‖ = ‖f‖ := by
  refine le_antisymm (norm_le_of_forall (norm_nonneg f) fun x => ?_) ?_
  · simpa using f.norm_coe_le_norm x
  · refine (ContinuousMap.norm_le _ (norm_nonneg' _)).2 fun x => ?_
    simpa using norm_coe_le_norm (ContinuousMap.toBoundedMeasurableFunction (𝕜 := 𝕜) f) x

end ContinuousMapHom

end BoundedMeasurableFunction


end MeasureTheory
