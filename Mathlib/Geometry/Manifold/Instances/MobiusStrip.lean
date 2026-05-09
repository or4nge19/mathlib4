/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Geometry.Manifold.Instances.Quotient
public import Mathlib.Geometry.Manifold.ContMDiff.Constructions
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.Instances.AddCircle

/-!
# The Möbius strip

This file defines the Möbius strip as the quotient of the plane by the usual `ℤ`-action
`n • (x, y) = (x + n, (-1)^n y)`.

This is the flat line bundle associated to the covering `ℝ → ℝ ⧸ ℤ` and the monodromy
representation `n ↦ (-1)^n` on `ℝ`.

## TODO

* Upgrade the quotient charted-space construction to a smooth manifold structure, once the quotient
  manifold API proves `IsManifold` for quotients by smooth properly discontinuous actions. Then
  state smoothness of `proj`.
* Express the flat line bundle structure. Mathlib's `FiberBundle` and `VectorBundle` classes are
  currently formulated for sigma-type total spaces `Bundle.TotalSpace F E`, not arbitrary maps such
  as `proj : MobiusStrip → UnitAddCircle`, so this likely needs a sigma-type presentation and a
  comparison with the quotient model below.
* Relate this quotient model to the tautological line bundle over `ℝP^1`.
-/

public noncomputable section

open scoped ContDiff

/-- The monodromy scalar in the flat line-bundle description of the Möbius strip. -/
@[expose]
def mobiusMonodromyUnit (n : ℤ) : ℝˣ :=
  Units.mk0 ((-1 : ℝ) ^ n) (zpow_ne_zero n (by norm_num : (-1 : ℝ) ≠ 0))

/-- The monodromy representation `ℤ → GL(ℝ)` of the Möbius strip. -/
@[expose]
def mobiusMonodromy (n : ℤ) : ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.unitsEquivAut ℝ (mobiusMonodromyUnit n)

/-- The scalar formula for the Möbius monodromy. -/
@[simp]
lemma mobiusMonodromy_apply (n : ℤ) (y : ℝ) :
    mobiusMonodromy n y = (-1 : ℝ) ^ n * y := by
  simp [mobiusMonodromy, mobiusMonodromyUnit, mul_comm]

/-- The monodromy is compatible with addition in the deck group. -/
lemma mobiusMonodromy_add_apply (n m : ℤ) (y : ℝ) :
    mobiusMonodromy (n + m) y = mobiusMonodromy n (mobiusMonodromy m y) := by
  simp only [mobiusMonodromy_apply]
  rw [zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
  ring

/-- The monodromy representation, as a homomorphism from the additive group `ℤ`. -/
@[expose]
def mobiusMonodromyHom : Multiplicative ℤ →* ℝ ≃L[ℝ] ℝ where
  toFun n := mobiusMonodromy n.toAdd
  map_one' := by
    ext y
    change mobiusMonodromy 0 y = y
    simp
  map_mul' n m := by
    ext y
    exact mobiusMonodromy_add_apply n.toAdd m.toAdd y

/-- The same monodromy as a bare function, convenient in coordinate formulas. -/
@[expose]
def mobiusRep (n : ℤ) (y : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * y

@[simp]
lemma mobiusRep_apply (n : ℤ) (y : ℝ) : mobiusRep n y = (-1 : ℝ) ^ n * y :=
  rfl

@[simp]
lemma mobiusRep_zero (y : ℝ) : mobiusRep 0 y = y := by
  simp [mobiusRep]

lemma mobiusRep_add (n m : ℤ) (y : ℝ) :
    mobiusRep (n + m) y = mobiusRep n (mobiusRep m y) := by
  unfold mobiusRep
  rw [zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
  ring

lemma mobiusRep_eq_mobiusMonodromy (n : ℤ) (y : ℝ) : mobiusRep n y = mobiusMonodromy n y := by
  simp [mobiusRep]

/-- A type synonym for the plane carrying the Möbius action. -/
@[expose]
def MobiusPlane :=
  ℝ × ℝ
  deriving TopologicalSpace, T2Space, LocallyCompactSpace, SecondCountableTopology

namespace MobiusPlane

@[expose]
instance : AddAction ℤ MobiusPlane where
  vadd n p := (p.1 + n, mobiusRep n p.2)
  zero_vadd := by
    rintro ⟨x, y⟩
    change ((x + ((0 : ℤ) : ℝ), mobiusRep 0 y) : ℝ × ℝ) = (x, y)
    ext <;> simp
  add_vadd n m := by
    rintro ⟨x, y⟩
    change
      ((x + ((n + m : ℤ) : ℝ), mobiusRep (n + m) y) : ℝ × ℝ) =
        (x + (m : ℝ) + (n : ℝ), mobiusRep n (mobiusRep m y))
    ext
    · norm_num
      ring
    · exact mobiusRep_add n m y

@[simp]
lemma vadd_fst (n : ℤ) (p : MobiusPlane) : (n +ᵥ p).1 = p.1 + n :=
  rfl

@[simp]
lemma vadd_snd (n : ℤ) (p : MobiusPlane) : (n +ᵥ p).2 = (-1 : ℝ) ^ n * p.2 :=
  rfl

instance : ContinuousConstVAdd ℤ MobiusPlane where
  continuous_const_vadd n := by
    change Continuous fun p : MobiusPlane ↦
      ((p.1 + (n : ℝ), mobiusRep n p.2) : ℝ × ℝ)
    exact (continuous_fst.add continuous_const).prodMk (continuous_const.mul continuous_snd)

instance : IsCancelVAdd ℤ MobiusPlane where
  left_cancel' n p q h := by
    change (p.1, p.2) = (q.1, q.2)
    ext
    · have hx := congrArg Prod.fst h
      simp only [vadd_fst] at hx
      linarith
    · have hy := congrArg Prod.snd h
      simp only [vadd_snd] at hy
      exact mul_left_cancel₀ (zpow_ne_zero n (by norm_num : (-1 : ℝ) ≠ 0)) hy
  right_cancel' n m p h := by
    have hx := congrArg Prod.fst h
    simp only [vadd_fst] at hx
    have hcast : (n : ℝ) = m := by linarith
    exact_mod_cast hcast

instance : ProperlyDiscontinuousVAdd ℤ MobiusPlane where
  finite_disjoint_inter_image {K L} hK hL := by
    let C : Set ℝ :=
      (fun p : ℝ × ℝ ↦ p.2 - p.1) '' ((Prod.fst '' K) ×ˢ (Prod.fst '' L))
    have hKx : IsCompact (Prod.fst '' K) := hK.image continuous_fst
    have hLx : IsCompact (Prod.fst '' L) := hL.image continuous_fst
    have hC : IsCompact C := (hKx.prod hLx).image (continuous_snd.sub continuous_fst)
    refine (tendsto_cofinite_cocompact_iff.mp Int.tendsto_coe_cofinite C hC).subset ?_
    intro n hn
    rcases hn with ⟨q, ⟨p, hpK, hpq⟩, hqL⟩
    change (n : ℝ) ∈ C
    refine ⟨(p.1, q.1), ⟨⟨⟨p, hpK, rfl⟩, ⟨q, hqL, rfl⟩⟩, ?_⟩⟩
    have hx := congrArg Prod.fst hpq
    simp only [vadd_fst] at hx
    linarith

instance : ChartedSpace (ℝ × ℝ) MobiusPlane :=
  inferInstanceAs (ChartedSpace (ℝ × ℝ) (ℝ × ℝ))

instance (n : ℕ∞ω) : IsManifold (modelWithCornersSelf ℝ (ℝ × ℝ)) n MobiusPlane :=
  inferInstanceAs (IsManifold (modelWithCornersSelf ℝ (ℝ × ℝ)) n (ℝ × ℝ))

lemma contMDiff_vadd (n : ℤ) (k : ℕ∞ω) :
    ContMDiff (modelWithCornersSelf ℝ (ℝ × ℝ)) (modelWithCornersSelf ℝ (ℝ × ℝ)) k
      (fun p : MobiusPlane ↦ n +ᵥ p) := by
  change ContMDiff (modelWithCornersSelf ℝ (ℝ × ℝ)) (modelWithCornersSelf ℝ (ℝ × ℝ)) k
    (fun p : ℝ × ℝ ↦ (p.1 + (n : ℝ), mobiusRep n p.2))
  exact ((contDiff_fst.add contDiff_const).prodMk (contDiff_const.mul contDiff_snd)).contMDiff

end MobiusPlane

/-- The Möbius strip as the quotient of the plane by the standard `ℤ`-action. -/
abbrev MobiusStrip :=
  AddAction.orbitRel.Quotient ℤ MobiusPlane

namespace MobiusStrip

instance : ChartedSpace (ℝ × ℝ) MobiusStrip :=
  inferInstanceAs (ChartedSpace (ℝ × ℝ) (AddAction.orbitRel.Quotient ℤ MobiusPlane))

instance : T2Space MobiusStrip :=
  inferInstanceAs (T2Space (AddAction.orbitRel.Quotient ℤ MobiusPlane))

instance : SecondCountableTopology MobiusStrip :=
  ContinuousConstVAdd.secondCountableTopology (Γ := ℤ) (T := MobiusPlane)

/-- The quotient map from the plane to the Möbius strip. -/
@[expose]
def mk (p : MobiusPlane) : MobiusStrip :=
  ⟦p⟧

lemma mk_surjective : Function.Surjective mk :=
  Quotient.mk_surjective

@[continuity]
lemma continuous_mk : Continuous mk :=
  continuous_quotient_mk'

@[simp]
lemma mk_vadd (n : ℤ) (p : MobiusPlane) : mk (n +ᵥ p) = mk p := by
  exact Quotient.sound (AddAction.mem_orbit p n)

lemma isAddQuotientCoveringMap_mk : IsAddQuotientCoveringMap mk ℤ := by
  exact isAddQuotientCoveringMap_quotientMk_of_properlyDiscontinuousVAdd

lemma isCoveringMap_mk : IsCoveringMap mk :=
  isAddQuotientCoveringMap_mk.isCoveringMap

lemma isOpenQuotientMap_mk : IsOpenQuotientMap mk :=
  isAddQuotientCoveringMap_mk.isOpenQuotientMap

instance : LocallyCompactSpace MobiusStrip :=
  isOpenQuotientMap_mk.locallyCompactSpace

/-- Two points in the plane define the same point of the Möbius strip iff they are in the same
`ℤ`-orbit. This is the quotient-oriented replacement for a hand-written `mobius_equiv`. -/
lemma mk_eq_mk_iff_exists_vadd_eq_left {p q : MobiusPlane} :
    mk p = mk q ↔ ∃ n : ℤ, n +ᵥ q = p := by
  change (⟦p⟧ : AddAction.orbitRel.Quotient ℤ MobiusPlane) = ⟦q⟧ ↔
    ∃ n : ℤ, n +ᵥ q = p
  rw [Quotient.eq, AddAction.orbitRel_apply]
  rfl

/-- The more common orientation of `mk_eq_mk_iff_exists_vadd_eq_left`: representatives define the
same point of the Möbius strip iff one is obtained from the other by the Möbius action. -/
lemma mk_eq_mk_iff_exists_vadd_eq {p q : MobiusPlane} :
    mk p = mk q ↔ ∃ n : ℤ, n +ᵥ p = q := by
  rw [eq_comm, mk_eq_mk_iff_exists_vadd_eq_left]

/-- The projection from the Möbius strip to the base circle. -/
@[expose]
def proj : MobiusStrip → UnitAddCircle :=
  Quotient.lift (fun p : MobiusPlane ↦ (p.1 : UnitAddCircle)) <| by
    intro p q h
    rcases h with ⟨n, rfl⟩
    have hshift : ((n : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨n, by simp⟩
    calc
      ((q.1 + (n : ℝ) : ℝ) : UnitAddCircle) =
          (q.1 : UnitAddCircle) + ((n : ℝ) : UnitAddCircle) :=
        AddCircle.coe_add (1 : ℝ) q.1 (n : ℝ)
      _ = (q.1 : UnitAddCircle) := by simp [hshift]

@[simp]
lemma proj_mk (p : MobiusPlane) : proj (mk p) = (p.1 : UnitAddCircle) :=
  rfl

lemma proj_surjective : Function.Surjective proj := by
  intro z
  refine QuotientAddGroup.induction_on z ?_
  intro x
  exact ⟨mk ⟨x, 0⟩, rfl⟩

@[continuity]
lemma continuous_proj : Continuous proj := by
  rw [isQuotientMap_quotient_mk'.continuous_iff]
  change Continuous (fun p : MobiusPlane ↦ (p.1 : UnitAddCircle))
  exact (AddCircle.continuous_mk' (1 : ℝ)).comp continuous_fst

end MobiusStrip
