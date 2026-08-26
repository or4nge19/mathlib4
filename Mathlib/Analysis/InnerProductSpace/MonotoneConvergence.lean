/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Algebra.Order.Group.Pointwise.Bounds
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Monotone convergence for operators

A family of operators on a Hilbert space that is monotone for the Loewner order and bounded above
converges in the strong operator topology to its least upper bound. This is
[Blackadar, I.3.2.5][blackadar2006operator], slightly generalised: he states it for a bounded
increasing net of *positive* operators, whereas monotone and bounded above suffices, positivity
being needed only for the norm identity `‖S‖ = ⨆ ‖Tᵢ‖`.

The proof is Blackadar's. Cauchy–Schwarz for the positive operator `T j - T i` bounds
`‖T j x - T i x‖²` by `‖T j - T i‖` times the increment of `re ⟪T i x, x⟫`; the norms are
uniformly bounded because the norm is monotone on positive operators; and the real quantities
increase and are bounded, hence converge. So each orbit is Cauchy.

## Main results

* `ContinuousLinearMap.isPositive_of_tendsto`: a strong limit of positive operators is positive
* `ContinuousLinearMap.exists_isLUB_tendsto_of_monotone`: the theorem, for a monotone family
* `ContinuousLinearMap.exists_isLUB_tendsto_of_directedOn`: the same for a directed set
* `ContinuousLinearMap.exists_isGLB_tendsto_of_antitone`: the decreasing case
* `ContinuousLinearMap.tendsto_of_monotone_of_tendsto_inner`: weak convergence of a monotone
  family upgrades to strong ([Blackadar, I.3.2.6][blackadar2006operator])
* `ContinuousLinearMap.norm_eq_ciSup_of_isLUB`: `‖S‖ = ⨆ ‖Tᵢ‖`, for positive `Tᵢ`

The proof rests on `ContinuousLinearMap.IsPositive.norm_apply_sq_le` and
`ContinuousLinearMap.IsPositive.norm_le_norm_of_le`.
-/

public section
open RCLike ContinuousLinearMap Filter Topology Set
open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type*} [Nonempty ι] [Preorder ι] [IsDirected ι (· ≤ ·)]

omit [Nonempty ι] [IsDirected ι (· ≤ ·)] in
/-- Differences along a monotone family bounded above are uniformly norm-bounded. -/
theorem norm_sub_le_of_monotone {T : ι → E →L[𝕜] E} (hmono : Monotone T) {U : E →L[𝕜] E}
    (hU : ∀ i, T i ≤ U) (i₀ : ι) {i j : ι} (hi : i₀ ≤ i) (hij : i ≤ j) :
    ‖T j - T i‖ ≤ ‖U - T i₀‖ := by
  have hpos : (T j - T i).IsPositive := by
    rw [← le_def]
    exact hmono hij
  refine IsPositive.norm_le_norm_of_le hpos ?_
  -- `U - T i₀ - (T j - T i) = (U - T j) + (T i - T i₀) ≥ 0`
  rw [le_def]
  have h1 : (U - T j).IsPositive := by
    rw [← le_def]; exact hU j
  have h2 : (T i - T i₀).IsPositive := by
    rw [← le_def]; exact hmono hi
  have heq : U - T i₀ - (T j - T i) = (U - T j) + (T i - T i₀) := by abel
  rw [heq]
  exact h1.add h2

omit [Nonempty ι] [IsDirected ι (· ≤ ·)] in
/-- Along a monotone family bounded above, the real quantities `re ⟪T i x, x⟫` increase and are
bounded, hence converge. -/
theorem tendsto_reApplyInnerSelf_of_monotone {T : ι → E →L[𝕜] E} (hmono : Monotone T)
    {U : E →L[𝕜] E} (hU : ∀ i, T i ≤ U) (x : E) :
    Tendsto (fun i => re ⟪T i x, x⟫_𝕜) atTop (𝓝 (⨆ i, re ⟪T i x, x⟫_𝕜)) := by
  refine tendsto_atTop_ciSup (fun i j hij => ?_) ⟨‖U‖ * ‖x‖ ^ 2, ?_⟩
  · have h : (T j - T i).IsPositive := by
      rw [← le_def]; exact hmono hij
    have := h.2 x
    rw [reApplyInnerSelf_apply] at this
    simp only [_root_.sub_apply, inner_sub_left, map_sub] at this
    linarith
  · rintro _ ⟨i, rfl⟩
    calc re ⟪T i x, x⟫_𝕜 ≤ ‖U‖ * ‖x‖ ^ 2 := by
          have hU' := reApplyInnerSelf_le_norm_mul_norm_sq (A := U) x
          rw [reApplyInnerSelf_apply] at hU'
          refine le_trans ?_ hU'
          have h : (U - T i).IsPositive := by
            rw [← le_def]; exact hU i
          have := h.2 x
          rw [reApplyInnerSelf_apply] at this
          simp only [_root_.sub_apply, inner_sub_left, map_sub] at this
          linarith

omit [Nonempty ι] [IsDirected ι (· ≤ ·)] in
/-- **The key estimate**: along a monotone family bounded above, the increments of the orbit of a
vector are controlled by the increments of the real quantities `re ⟪T i x, x⟫`. -/
theorem norm_sub_apply_sq_le_of_monotone {T : ι → E →L[𝕜] E} (hmono : Monotone T)
    {U : E →L[𝕜] E} (hU : ∀ i, T i ≤ U) (i₀ : ι) (x : E) {i j : ι} (hi : i₀ ≤ i) (hij : i ≤ j) :
    ‖T j x - T i x‖ ^ 2 ≤ ‖U - T i₀‖ * (re ⟪T j x, x⟫_𝕜 - re ⟪T i x, x⟫_𝕜) := by
  have hpos : (T j - T i).IsPositive := by
    rw [← le_def]; exact hmono hij
  have hcs := IsPositive.norm_apply_sq_le hpos x
  have hre : re ⟪T j x - T i x, x⟫_𝕜 = re ⟪T j x, x⟫_𝕜 - re ⟪T i x, x⟫_𝕜 := by
    rw [inner_sub_left, map_sub]
  simp only [_root_.sub_apply] at hcs
  rw [hre] at hcs
  refine hcs.trans (mul_le_mul_of_nonneg_right
    (norm_sub_le_of_monotone hmono hU i₀ hi hij) ?_)
  rw [← hre]
  have := hpos.2 x
  rw [reApplyInnerSelf_apply] at this
  simpa using this

variable [CompleteSpace E]

/-- Along a monotone family bounded above, every orbit converges. -/
theorem exists_tendsto_apply_of_monotone {T : ι → E →L[𝕜] E} (hmono : Monotone T)
    {U : E →L[𝕜] E} (hU : ∀ i, T i ≤ U) (x : E) :
    ∃ y : E, Tendsto (fun i => T i x) atTop (𝓝 y) := by
  suffices h : Cauchy (map (fun i => T i x) atTop) by
    obtain ⟨y, hy⟩ := CompleteSpace.complete h
    exact ⟨y, hy⟩
  rw [Metric.cauchy_iff]
  refine ⟨map_neBot, fun ε hε => ?_⟩
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  set K : ℝ := ‖U - T i₀‖ with hK
  have hK0 : 0 ≤ K := norm_nonneg _
  set δ : ℝ := (ε / 2) ^ 2 / (K + 1) with hδdef
  have hδ : 0 < δ := by positivity
  have hreal := tendsto_reApplyInnerSelf_of_monotone hmono hU x
  have hev : ∀ᶠ i in atTop, dist (re ⟪T i x, x⟫_𝕜) (⨆ n, re ⟪T n x, x⟫_𝕜) < δ / 2 :=
    hreal (Metric.ball_mem_nhds _ (half_pos hδ))
  rw [atTop_basis.eventually_iff] at hev
  obtain ⟨N, -, hN⟩ := hev
  obtain ⟨i₁, hi₁a, hi₁b⟩ := directed_of (· ≤ ·) i₀ N
  refine ⟨(fun i => T i x) '' (Ici i₁), image_mem_map (Ici_mem_atTop i₁), ?_⟩
  have hsmall : ∀ i ≥ i₁, ∀ k ≥ i, ‖T k x - T i x‖ < ε / 2 := by
    intro i hi k hk
    have hgi : dist (re ⟪T i x, x⟫_𝕜) (⨆ n, re ⟪T n x, x⟫_𝕜) < δ / 2 :=
      hN (le_trans hi₁b hi)
    have hgk : dist (re ⟪T k x, x⟫_𝕜) (⨆ n, re ⟪T n x, x⟫_𝕜) < δ / 2 :=
      hN (le_trans hi₁b (le_trans hi hk))
    have hdiff : re ⟪T k x, x⟫_𝕜 - re ⟪T i x, x⟫_𝕜 < δ := by
      rw [Real.dist_eq] at hgi hgk
      have h1 := abs_lt.1 hgi
      have h2 := abs_lt.1 hgk
      linarith [h1.1, h1.2, h2.1, h2.2]
    have hbound := norm_sub_apply_sq_le_of_monotone hmono hU i₀ x (le_trans hi₁a hi) hk
    have hsq : ‖T k x - T i x‖ ^ 2 < (ε / 2) ^ 2 := by
      calc ‖T k x - T i x‖ ^ 2 ≤ K * (re ⟪T k x, x⟫_𝕜 - re ⟪T i x, x⟫_𝕜) := hbound
        _ ≤ K * δ := by
            refine mul_le_mul_of_nonneg_left hdiff.le hK0
        _ < (ε / 2) ^ 2 := by
            rw [hδdef]
            rw [mul_div_assoc'] at *
            rw [div_lt_iff₀ (by positivity)]
            nlinarith [sq_nonneg (ε / 2), hK0]
    nlinarith [norm_nonneg (T k x - T i x), hsq, hε]
  rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  calc dist (T i x) (T j x) ≤ dist (T i x) (T k x) + dist (T k x) (T j x) :=
        dist_triangle _ _ _
    _ = ‖T k x - T i x‖ + ‖T k x - T j x‖ := by
        rw [dist_eq_norm, dist_eq_norm, norm_sub_rev (T i x), norm_sub_rev (T k x)]
    _ < ε / 2 + ε / 2 := by
        exact add_lt_add (hsmall i hi k hik) (hsmall j hj k hjk)
    _ = ε := by ring

omit [CompleteSpace E] in
/-- A weak limit of positive operators is positive.

That is, if `P i` is eventually positive and `⟪P i x, y⟫ → ⟪Q x, y⟫` for all `x, y`, then `Q`
is positive. Closedness in the strong operator topology is the special case
`isPositive_of_tendsto`. -/
theorem isPositive_of_tendsto_inner {P : ι → E →L[𝕜] E} {Q : E →L[𝕜] E}
    (hpos : ∀ᶠ i in atTop, (P i).IsPositive)
    (hweak : ∀ x y, Tendsto (fun i => ⟪P i x, y⟫_𝕜) atTop (𝓝 ⟪Q x, y⟫_𝕜)) : Q.IsPositive := by
  constructor
  · intro x y
    have h2 : Tendsto (fun i => ⟪x, P i y⟫_𝕜) atTop (𝓝 ⟪x, Q y⟫_𝕜) := by
      have := (hweak y x).star
      simpa only [RCLike.star_def, inner_conj_symm] using this
    refine tendsto_nhds_unique (hweak x y) (h2.congr' ?_)
    filter_upwards [hpos] with i hi
    exact (hi.1 x y).symm
  · intro x
    rw [reApplyInnerSelf_apply]
    refine ge_of_tendsto ((RCLike.continuous_re.tendsto _).comp (hweak x x)) ?_
    filter_upwards [hpos] with i hi
    have := hi.2 x
    rwa [reApplyInnerSelf_apply] at this

omit [CompleteSpace E] in
/-- A strong limit of positive operators is positive.

The special case of `isPositive_of_tendsto_inner`, since strong convergence implies weak. -/
theorem isPositive_of_tendsto {P : ι → E →L[𝕜] E} {Q : E →L[𝕜] E}
    (hpos : ∀ᶠ i in atTop, (P i).IsPositive)
    (hlim : ∀ x, Tendsto (fun i => P i x) atTop (𝓝 (Q x))) : Q.IsPositive :=
  isPositive_of_tendsto_inner hpos fun x _ => (hlim x).inner tendsto_const_nhds

/-- **Monotone convergence for operators** ([Blackadar, I.3.2.5][blackadar2006operator]): a
monotone family of operators that is bounded above converges in the strong operator topology to
its least upper bound. -/
theorem exists_isLUB_tendsto_of_monotone {T : ι → E →L[𝕜] E} (hmono : Monotone T)
    (hbd : BddAbove (Set.range T)) :
    ∃ S : E →L[𝕜] E, IsLUB (Set.range T) S ∧ ∀ x, Tendsto (fun i => T i x) atTop (𝓝 (S x)) := by
  obtain ⟨U, hU'⟩ := hbd
  have hU : ∀ i, T i ≤ U := fun i => hU' ⟨i, rfl⟩
  choose f hf using fun x => exists_tendsto_apply_of_monotone hmono hU x
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hadd : ∀ x y, f (x + y) = f x + f y := fun x y => by
    refine tendsto_nhds_unique (hf (x + y)) ?_
    simpa only [map_add] using (hf x).add (hf y)
  have hsmul : ∀ (c : 𝕜) x, f (c • x) = c • f x := fun c x => by
    refine tendsto_nhds_unique (hf (c • x)) ?_
    simpa only [_root_.map_smul] using (hf x).const_smul c
  set K : ℝ := ‖T i₀‖ + ‖U - T i₀‖ with hKdef
  have hnormle : ∀ i, i₀ ≤ i → ‖T i‖ ≤ K := by
    intro i hi
    calc ‖T i‖ = ‖T i₀ + (T i - T i₀)‖ := by rw [add_sub_cancel]
      _ ≤ ‖T i₀‖ + ‖T i - T i₀‖ := norm_add_le _ _
      _ ≤ K := by
          have := norm_sub_le_of_monotone hmono hU i₀ (le_refl i₀) hi
          linarith
  have hfbound : ∀ x, ‖f x‖ ≤ K * ‖x‖ := by
    intro x
    refine le_of_tendsto (hf x).norm ?_
    rw [atTop_basis.eventually_iff]
    refine ⟨i₀, trivial, fun i hi => ?_⟩
    calc ‖T i x‖ ≤ ‖T i‖ * ‖x‖ := (T i).le_opNorm x
      _ ≤ K * ‖x‖ := by
          exact mul_le_mul_of_nonneg_right (hnormle i hi) (norm_nonneg x)
  set S : E →L[𝕜] E :=
    LinearMap.mkContinuous
      { toFun := f, map_add' := hadd, map_smul' := fun c x => by simpa using hsmul c x } K hfbound
    with hS
  have hSapply : ∀ x, S x = f x := fun _ => rfl
  have hSf : ∀ x, Tendsto (fun i => T i x) atTop (𝓝 (S x)) := fun x => by
    rw [hSapply]; exact hf x
  refine ⟨S, ⟨?_, ?_⟩, hSf⟩
  · rintro _ ⟨i, rfl⟩
    rw [le_def]
    refine isPositive_of_tendsto (P := fun j => T j - T i) ?_ (fun x => ?_)
    · rw [atTop_basis.eventually_iff]
      exact ⟨i, trivial, fun j hj => by rw [← le_def]; exact hmono hj⟩
    · simpa [_root_.sub_apply] using (hSf x).sub_const (T i x)
  · intro V hV2
    rw [le_def]
    refine isPositive_of_tendsto (P := fun j => V - T j) ?_ (fun x => ?_)
    · filter_upwards with j
      rw [← le_def]
      exact hV2 ⟨j, rfl⟩
    · simpa [_root_.sub_apply] using tendsto_const_nhds.sub (hSf x)

/-- **Monotone convergence, for a directed set** ([Blackadar, I.3.2.5][blackadar2006operator]):
a directed set of operators that is bounded above has a least upper bound, and the net it defines
converges to it strongly. -/
theorem exists_isLUB_tendsto_of_directedOn {s : Set (E →L[𝕜] E)} (hs : DirectedOn (· ≤ ·) s)
    (hnon : s.Nonempty) (hbd : BddAbove s) :
    ∃ S : E →L[𝕜] E, IsLUB s S ∧
      ∀ x, Tendsto (fun T : s => (T : E →L[𝕜] E) x) atTop (𝓝 (S x)) := by
  have : Nonempty s := hnon.to_subtype
  have : IsDirected s (· ≤ ·) := ⟨fun a b => by
    obtain ⟨c, hc, hac, hbc⟩ := hs a a.2 b b.2
    exact ⟨⟨c, hc⟩, hac, hbc⟩⟩
  obtain ⟨S, hlub, htend⟩ :=
    exists_isLUB_tendsto_of_monotone (T := (Subtype.val : s → E →L[𝕜] E))
      (fun a b hab => hab) (by
        obtain ⟨U, hU⟩ := hbd
        exact ⟨U, by rintro _ ⟨a, rfl⟩; exact hU a.2⟩)
  refine ⟨S, ?_, htend⟩
  rwa [show Set.range (Subtype.val : s → E →L[𝕜] E) = s from Subtype.range_val] at hlub

/-- **The decreasing case** ([Blackadar, I.3.2.5][blackadar2006operator]): an antitone family
bounded below converges strongly to its greatest lower bound. -/
theorem exists_isGLB_tendsto_of_antitone {T : ι → E →L[𝕜] E} (hanti : Antitone T)
    (hbd : BddBelow (Set.range T)) :
    ∃ S : E →L[𝕜] E, IsGLB (Set.range T) S ∧ ∀ x, Tendsto (fun i => T i x) atTop (𝓝 (S x)) := by
  obtain ⟨S, hlub, htend⟩ :=
    exists_isLUB_tendsto_of_monotone (T := fun i => -T i) (fun i j hij => neg_le_neg (hanti hij))
      (by
        obtain ⟨L, hL⟩ := hbd
        refine ⟨-L, ?_⟩
        rintro _ ⟨i, rfl⟩
        exact neg_le_neg (hL ⟨i, rfl⟩))
  refine ⟨-S, ?_, fun x => ?_⟩
  · rw [show Set.range T = -Set.range (fun i => -T i) by
      ext y; simp [Set.mem_neg, eq_comm, neg_eq_iff_eq_neg]]
    exact hlub.neg
  · simpa using (htend x).neg

/-- **Weak convergence upgrades to strong for monotone families**
([Blackadar, I.3.2.6][blackadar2006operator]): if a monotone family converges weakly — that is,
`⟪T i x, y⟫ → ⟪V x, y⟫` for all `x, y` — then it converges strongly, and `V` is its least upper
bound.

The point is that a weak limit of a monotone family is automatically an upper bound, so the family
is bounded above and the strong limit exists; the two limits then agree because strong convergence
implies weak. -/
theorem tendsto_of_monotone_of_tendsto_inner {T : ι → E →L[𝕜] E} (hmono : Monotone T)
    {V : E →L[𝕜] E} (hweak : ∀ x y, Tendsto (fun i => ⟪T i x, y⟫_𝕜) atTop (𝓝 ⟪V x, y⟫_𝕜)) :
    IsLUB (Set.range T) V ∧ ∀ x, Tendsto (fun i => T i x) atTop (𝓝 (V x)) := by
  have hub : ∀ i, T i ≤ V := by
    intro i
    rw [le_def]
    refine isPositive_of_tendsto_inner (P := fun j => T j - T i) ?_ (fun x y => ?_)
    · rw [atTop_basis.eventually_iff]
      exact ⟨i, trivial, fun j hj => by rw [← le_def]; exact hmono hj⟩
    · have h := (hweak x y).sub (tendsto_const_nhds (x := ⟪T i x, y⟫_𝕜))
      simpa only [_root_.sub_apply, inner_sub_left] using h
  obtain ⟨S, hlub, hstrong⟩ := exists_isLUB_tendsto_of_monotone hmono ⟨V, by
    rintro _ ⟨i, rfl⟩; exact hub i⟩
  have hSV : S = V := by
    refine ext fun x => ?_
    refine ext_inner_right 𝕜 fun y => ?_
    exact tendsto_nhds_unique ((hstrong x).inner tendsto_const_nhds) (hweak x y)
  subst hSV
  exact ⟨hlub, hstrong⟩

omit [CompleteSpace E] in
/-- **The norm of the limit is the supremum of the norms**, completing
[Blackadar, I.3.2.5][blackadar2006operator] for a family of *positive* operators.

Monotonicity of the family is not needed: `hlub` and positivity give `‖T i‖ ≤ ‖S‖`, and the
convergence of the orbits gives the reverse bound. -/
theorem norm_eq_ciSup_of_isLUB {T : ι → E →L[𝕜] E}
    (hpos : ∀ i, (T i).IsPositive) {S : E →L[𝕜] E} (hlub : IsLUB (Set.range T) S)
    (htend : ∀ x, Tendsto (fun i => T i x) atTop (𝓝 (S x))) :
    ‖S‖ = ⨆ i, ‖T i‖ := by
  have hle : ∀ i, ‖T i‖ ≤ ‖S‖ := fun i =>
    IsPositive.norm_le_norm_of_le (hpos i) (hlub.1 ⟨i, rfl⟩)
  have hbdd : BddAbove (Set.range fun i => ‖T i‖) := ⟨‖S‖, by rintro _ ⟨i, rfl⟩; exact hle i⟩
  refine le_antisymm ?_ (ciSup_le hle)
  refine S.opNorm_le_bound (le_ciSup_of_le hbdd (Classical.arbitrary ι) (norm_nonneg _)) fun x => ?_
  refine le_of_tendsto (htend x).norm ?_
  filter_upwards with i
  calc ‖T i x‖ ≤ ‖T i‖ * ‖x‖ := (T i).le_opNorm x
    _ ≤ (⨆ j, ‖T j‖) * ‖x‖ := by
        exact mul_le_mul_of_nonneg_right (le_ciSup hbdd i) (norm_nonneg x)

end ContinuousLinearMap
