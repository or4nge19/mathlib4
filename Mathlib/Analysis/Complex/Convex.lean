/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies
-/
module

public import Mathlib.Analysis.Complex.ReImTopology
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.PathConnected

/-!
# Theorems about convexity on the complex plane

We show that the open and closed half-spaces in ℂ given by an inequality on either the real or
imaginary part are all convex over ℝ. We also prove some results on star-convexity for the
slit plane.
-/

@[expose] public section

open Set
open scoped ComplexOrder

namespace Complex

/-- A version of `convexHull_prod` for `Set.reProdIm`. -/
lemma convexHull_reProdIm (s t : Set ℝ) :
    convexHull ℝ (s ×ℂ t) = convexHull ℝ s ×ℂ convexHull ℝ t :=
  calc
    convexHull ℝ (equivRealProdLm ⁻¹' (s ×ˢ t)) = equivRealProdLm ⁻¹' convexHull ℝ (s ×ˢ t) := by
      simpa only [← LinearEquiv.image_symm_eq_preimage]
        using ((equivRealProdLm.symm.toLinearMap).image_convexHull (s ×ˢ t)).symm
    _ = convexHull ℝ s ×ℂ convexHull ℝ t := by rw [convexHull_prod]; rfl

/-- The slit plane is star-convex at a positive number. -/
lemma starConvex_slitPlane {z : ℂ} (hz : 0 < z) : StarConvex ℝ z slitPlane :=
  Complex.compl_Iic_zero ▸ starConvex_compl_Iic hz

/-- The slit plane is star-shaped at a positive real number. -/
lemma starConvex_ofReal_slitPlane {x : ℝ} (hx : 0 < x) : StarConvex ℝ ↑x slitPlane :=
  starConvex_slitPlane <| zero_lt_real.2 hx

/-- The slit plane is star-shaped at `1`. -/
lemma starConvex_one_slitPlane : StarConvex ℝ 1 slitPlane := starConvex_slitPlane one_pos

end Complex

open Complex

variable (r : ℝ)

theorem convex_halfSpace_re_lt : Convex ℝ { c : ℂ | c.re < r } :=
  convex_halfSpace_lt (.mk add_re smul_re) _
theorem convex_halfSpace_re_le : Convex ℝ { c : ℂ | c.re ≤ r } :=
  convex_halfSpace_le (.mk add_re smul_re) _
theorem convex_halfSpace_re_gt : Convex ℝ { c : ℂ | r < c.re } :=
  convex_halfSpace_gt (.mk add_re smul_re) _
theorem convex_halfSpace_re_ge : Convex ℝ { c : ℂ | r ≤ c.re } :=
  convex_halfSpace_ge (.mk add_re smul_re) _
theorem convex_halfSpace_im_lt : Convex ℝ { c : ℂ | c.im < r } :=
  convex_halfSpace_lt (.mk add_im smul_im) _
theorem convex_halfSpace_im_le : Convex ℝ { c : ℂ | c.im ≤ r } :=
  convex_halfSpace_le (.mk add_im smul_im) _
theorem convex_halfSpace_im_gt : Convex ℝ { c : ℂ | r < c.im } :=
  convex_halfSpace_gt (.mk add_im smul_im) _
theorem convex_halfSpace_im_ge : Convex ℝ { c : ℂ | r ≤ c.im } :=
  convex_halfSpace_ge (.mk add_im smul_im) _

namespace Complex

lemma isConnected_of_upperHalfPlane {r} {s : Set ℂ} (hs₁ : {z | r < z.im} ⊆ s)
    (hs₂ : s ⊆ {z | r ≤ z.im}) : IsConnected s := by
  refine .subset_closure ?_ hs₁ (by simpa only [closure_setOf_lt_im] using hs₂)
  exact (convex_halfSpace_im_gt r).isConnected ⟨(r + 1) * I, by simp⟩

lemma isConnected_of_lowerHalfPlane {r} {s : Set ℂ} (hs₁ : {z | z.im < r} ⊆ s)
    (hs₂ : s ⊆ {z | z.im ≤ r}) : IsConnected s := by
  refine .subset_closure ?_ hs₁ (by simpa only [closure_setOf_im_lt] using hs₂)
  exact (convex_halfSpace_im_lt r).isConnected ⟨(r - 1) * I, by simp⟩

lemma rectangle_eq_convexHull (z w : ℂ) :
    Rectangle z w = convexHull ℝ {z, z.re + w.im * I, w.re + z.im * I, w} := by
  simp_rw [Rectangle, ← segment_eq_uIcc, ← convexHull_pair, ← convexHull_reProdIm,
    ← preimage_equivRealProd_prod, insert_prod, singleton_prod, image_pair, insert_union,
    ← insert_eq, ← Equiv.image_symm_eq_preimage, image_insert_eq, image_singleton,
    equivRealProd_symm_apply, re_add_im]

/-- If opposite corners of a rectangle are contained in a convex set, the whole rectangle is. -/
lemma Convex.rectangle_subset {U : Set ℂ} (U_convex : Convex ℝ U) {z w : ℂ} (hz : z ∈ U)
    (hw : w ∈ U) (hzw : (z.re + w.im * I) ∈ U) (hwz : (w.re + z.im * I) ∈ U) :
    Rectangle z w ⊆ U := by
  simpa only [rectangle_eq_convexHull] using convexHull_min (by grind) U_convex

/-- The open right half-plane `{z | a < re z}` with one point removed is path-connected. -/
theorem isPathConnected_halfSpace_re_gt_diff_singleton (a : ℝ) (p : ℂ) (hp : a < p.re) :
    IsPathConnected ({z : ℂ | a < z.re} \ ({p} : Set ℂ)) := by
  classical
  let S1 : Set ℂ := {z : ℂ | a < z.re ∧ z.im < p.im}
  let S2 : Set ℂ := {z : ℂ | a < z.re ∧ z.re < p.re}
  let S3 : Set ℂ := {z : ℂ | a < z.re ∧ p.im < z.im}
  let S4 : Set ℂ := {z : ℂ | p.re < z.re}
  have hS1conv : Convex ℝ S1 := by
    have h1 : Convex ℝ {z : ℂ | a < z.re} := convex_halfSpace_re_gt (r := a)
    have h2 : Convex ℝ {z : ℂ | z.im < p.im} := convex_halfSpace_im_lt (r := p.im)
    simpa [S1, Set.setOf_and] using h1.inter h2
  have hS2conv : Convex ℝ S2 := by
    have h1 : Convex ℝ {z : ℂ | a < z.re} := convex_halfSpace_re_gt (r := a)
    have h2 : Convex ℝ {z : ℂ | z.re < p.re} := convex_halfSpace_re_lt (r := p.re)
    simpa [S2, Set.setOf_and] using h1.inter h2
  have hS3conv : Convex ℝ S3 := by
    have h1 : Convex ℝ {z : ℂ | a < z.re} := convex_halfSpace_re_gt (r := a)
    have h2 : Convex ℝ {z : ℂ | p.im < z.im} := convex_halfSpace_im_gt (r := p.im)
    simpa [S3, Set.setOf_and] using h1.inter h2
  have hS4conv : Convex ℝ S4 := by
    simpa [S4] using (convex_halfSpace_re_gt (r := p.re))
  have hS1ne : S1.Nonempty := by
    refine ⟨((max a p.re) + 1 : ℝ) + (p.im - 1) * Complex.I, ?_⟩
    have h1 : a < (max a p.re) + 1 := by
      have : a ≤ max a p.re := le_max_left _ _
      exact lt_of_le_of_lt this (by linarith)
    have h2 : (p.im - 1) < p.im := by linarith
    simpa [S1, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
      using And.intro h1 h2
  have hS2ne : S2.Nonempty := by
    refine ⟨((a + p.re) / 2 : ℝ) + (p.im : ℝ) * Complex.I, ?_⟩
    have h1 : a < (a + p.re) / 2 := by linarith
    have h2 : (a + p.re) / 2 < p.re := by linarith
    simpa [S2, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
      using And.intro h1 h2
  have hS3ne : S3.Nonempty := by
    refine ⟨((max a p.re) + 1 : ℝ) + (p.im + 1) * Complex.I, ?_⟩
    have h1 : a < (max a p.re) + 1 := by
      have : a ≤ max a p.re := le_max_left _ _
      exact lt_of_le_of_lt this (by linarith)
    have h2 : p.im < (p.im + 1) := by linarith
    simpa [S3, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
      using And.intro h1 h2
  have hS4ne : S4.Nonempty := by
    refine ⟨(p.re + 1 : ℝ) + (0 : ℝ) * Complex.I, ?_⟩
    have : p.re < p.re + 1 := by linarith
    simp [S4, Complex.add_re, Complex.mul_re]
  have hS1pc : IsPathConnected S1 := (hS1conv.isPathConnected hS1ne)
  have hS2pc : IsPathConnected S2 := (hS2conv.isPathConnected hS2ne)
  have hS3pc : IsPathConnected S3 := (hS3conv.isPathConnected hS3ne)
  have hS4pc : IsPathConnected S4 := (hS4conv.isPathConnected hS4ne)
  let A : Set ℂ := S1 ∪ S2
  let B : Set ℂ := S3 ∪ S4
  have hS1S2_int : (S1 ∩ S2).Nonempty := by
    refine ⟨((a + p.re) / 2 : ℝ) + (p.im - (1/2)) * Complex.I, ?_⟩
    have h1a : a < (a + p.re) / 2 := by linarith
    have h1b : (p.im - (1/2)) < p.im := by linarith
    have h2a : a < (a + p.re) / 2 := by linarith
    have h2b : (a + p.re) / 2 < p.re := by linarith
    constructor
    · simpa [S1, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h1a h1b
    · simpa [S2, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h2a h2b
  have hApc : IsPathConnected A :=
    IsPathConnected.union (U := S1) (V := S2) hS1pc hS2pc (by
      rcases hS1S2_int with ⟨z, hz⟩; exact ⟨z, hz⟩)
  have hS3S4_int : (S3 ∩ S4).Nonempty := by
    refine ⟨(p.re + 1 : ℝ) + (p.im + 1) * Complex.I, ?_⟩
    have h3a : a < p.re + 1 := lt_trans hp (by linarith)
    have h3b : p.im < p.im + 1 := by linarith
    have h4 : p.re < p.re + 1 := by linarith
    constructor
    · simpa [S3, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h3a h3b
    · simp [S4, Complex.add_re, Complex.mul_re]
  have hBpc : IsPathConnected B :=
    IsPathConnected.union (U := S3) (V := S4) hS3pc hS4pc (by
      rcases hS3S4_int with ⟨z, hz⟩; exact ⟨z, hz⟩)
  have hABint : (A ∩ B).Nonempty := by
    refine ⟨(p.re + 1 : ℝ) + (p.im - 1) * Complex.I, ?_⟩
    constructor
    · refine Or.inl ?_
      have h1 : a < p.re + 1 := lt_trans hp (by linarith)
      have h2 : (p.im - 1) < p.im := by linarith
      simpa [S1, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h1 h2
    · refine Or.inr ?_
      have h4 : p.re < p.re + 1 := by linarith
      simp [S4, Complex.add_re, Complex.mul_re]
  have hUnionPC : IsPathConnected (A ∪ B) :=
    IsPathConnected.union (U := A) (V := B) hApc hBpc (by
      rcases hABint with ⟨z, hz⟩; exact ⟨z, hz⟩)
  have hcover : ({z : ℂ | a < z.re} \ ({p} : Set ℂ)) = A ∪ B := by
    ext z; constructor
    · intro hz
      rcases hz with ⟨hzH, hznot⟩
      rcases lt_trichotomy z.re p.re with hlt | heq | hgt
      · exact Or.inl (Or.inr ⟨hzH, hlt⟩)
      · rcases lt_trichotomy z.im p.im with himlt | himeq | himgt
        · exact Or.inl (Or.inl ⟨hzH, himlt⟩)
        · have hz_eq : z = p := by
            have hzdecomp : (z.re : ℂ) + (z.im : ℝ) * Complex.I = z := by simp
            have hpdecomp : (p.re : ℂ) + (p.im : ℝ) * Complex.I = p := by simp
            have : (z.re : ℂ) + (z.im : ℝ) * Complex.I = (p.re : ℂ) + (p.im : ℝ) * Complex.I := by
              simp [heq, himeq]
            simpa [hzdecomp, hpdecomp] using this
          have : z ∈ ({p} : Set ℂ) := by simp [Set.mem_singleton_iff, hz_eq]
          exact (hznot this).elim
        · exact Or.inr (Or.inl ⟨hzH, himgt⟩)
      · exact Or.inr (Or.inr hgt)
    · intro hz
      have hzH : a < z.re := by
        rcases hz with hA | hB
        · rcases hA with hS1 | hS2
          · exact hS1.1
          · exact hS2.1
        · rcases hB with hS3 | hS4
          · exact hS3.1
          · exact lt_trans hp hS4
      have hzneq : z ≠ p := by
        rcases hz with hA | hB
        · rcases hA with hS1 | hS2
          · intro h
            have : z.im = p.im := by simp [h]
            have : z.im < z.im := by simpa [this] using hS1.2
            exact lt_irrefl _ this
          · intro h
            have : z.re = p.re := by simp [h]
            exact (ne_of_lt hS2.2) this
        · rcases hB with hS3 | hS4
          · intro h
            have : p.im = z.im := by simp [h]
            have : z.im < z.im := by simpa [this] using hS3.2
            exact lt_irrefl _ this
          · intro h
            have : p.re = z.re := by simp [h]
            exact (ne_of_gt hS4) this.symm
      exact And.intro hzH (by intro hzmem; exact hzneq (by simpa [Set.mem_singleton_iff] using hzmem))
  simpa [hcover] using hUnionPC

-- This also follows easily from `isPathConnected_compl_singleton_of_one_lt_rank`,
-- or that `Complex.range_exp` and `Complex.continuous_exp`,
-- but both of them requires a lot more import.
instance : PathConnectedSpace ℂˣ :=
  have : PathConnectedSpace { z : ℂ // z ≠ 0 } :=
    (isPathConnected_iff_pathConnectedSpace (F := {0}ᶜ)).mp (by
      convert (((convex_halfSpace_im_gt 0).isPathConnected ⟨.I, by simp⟩).union
        ((convex_halfSpace_re_gt 0).isPathConnected ⟨1, by simp⟩) ⟨1 + .I, by simp⟩).union
        (((convex_halfSpace_im_lt 0).isPathConnected ⟨-.I, by simp⟩).union
        ((convex_halfSpace_re_lt 0).isPathConnected ⟨-1, by simp⟩) ⟨-1 - .I, by simp⟩)
        ⟨1 - .I, by simp⟩ using 1
      ext x
      refine ⟨?_, by aesop⟩
      simp +contextual [Complex.ext_iff, -not_and, not_and_or, or_imp, ← ne_eq, ← lt_or_lt_iff_ne])
  let e := unitsHomeomorphNeZero (G₀ := ℂ)
  e.symm.surjective.pathConnectedSpace e.symm.continuous

end Complex
