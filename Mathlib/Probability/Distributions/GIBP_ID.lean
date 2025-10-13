import Mathlib.Probability.Distributions.GIBP_HilbertFin

/-
Looking at your formalization and the Mathlib PR, I can identify several pathways to extend GIBP to infinite dimensions. Let me analyze the mathematical connections and suggest the most promising approaches.

## Key Observation: Different but Complementary Approaches

Your Hilbert space formalization and the Mathlib Banach space work are mathematically complementary rather than competing approaches:

1. **Your approach**: Finite-dimensional Hilbert spaces with explicit ONB decomposition
2. **Mathlib PR**: Infinite-dimensional Banach spaces with Cameron-Martin theory

## Most Promising Extension Strategy

### 1. Cameron-Martin Bridge Approach (Recommended)

The Cameron-Martin space from the PR provides the natural infinite-dimensional analog of your covariance operator. Here's the connection:

**Finite-dimensional (your work):**
```lean
covOp (hg : IsGaussianHilbert g) : H →L[ℝ] H :=
  ∑ i, (hg.τ i : ℝ) • rank_one_projection (hg.w i)
```

**Infinite-dimensional analog:**
```lean
-- The Cameron-Martin embedding gives the "square root" of covariance
cmCoe : cameronMartin μ →L[ℝ] E
-- Your IBP becomes: E[⟪g,h⟫ F(g)] = E[dF(g)(Σh)] where Σ is the covariance
```

### 2. Concrete Implementation Path

#### Phase 1: Separable Hilbert Space Extension
Extend your current framework to infinite-dimensional separable Hilbert spaces:

```lean
structure IsGaussianHilbertInf (g : Ω → H) where
  -- Countable ONB instead of finite
  w : OrthonormalBasis ℕ ℝ H
  τ : ℕ → ℝ≥0
  -- Summability condition
  τ_summable : Summable τ
  -- Independent Gaussian coordinates
  c : ℕ → Ω → ℝ
  c_indep : iIndepFun c ℙ
  c_gauss : ∀ n, IsCenteredGaussianRV (c n) (τ n)
  -- Convergence in L²
  repr_convergent : ∀ᵐ ω, Summable (fun n ⇒ (c n ω) • w n)
```

#### Phase 2: Connect to Cameron-Martin
```lean
-- The Cameron-Martin space embeds as the completion of finite linear combinations
def cameronMartinOfGaussianHilbert (hg : IsGaussianHilbertInf g) :
    cameronMartin (Measure.map g ℙ) ≃L[ℝ]
    completion {h : H // Summable (fun n ⇒ (⟪h, hg.w n⟫)^2 / (hg.τ n))} :=
sorry
```

#### Phase 3: Infinite-dimensional IBP
```lean
theorem gaussian_IBP_hilbert_inf
    {g : Ω → H} (hg : IsGaussianHilbertInf g) (h : H)
    {F : H → ℝ} (hF : ContDiff ℝ 1 F) (hF_growth : ModerateGrowth F)
    (h_in_cm : h ∈ range (cmCoe (cameronMartinOfGaussianHilbert hg))) :
    𝔼[⟪g,h⟫ * F(g)] = 𝔼[fderiv F (g) (Σ h)] :=
sorry
```

### 3. Integration with Existing Mathlib PR

Your work can complement the PR by providing:

1. **Concrete realizations**: Your coordinate-based approach gives explicit constructions
2. **Computational tools**: Your orthonormal basis methods enable calculations
3. **Finite-dimensional bridge**: Natural approximation theory

The integration would work as:
- **General theory**: Use Cameron-Martin framework from the PR
- **Concrete cases**: Your coordinate-based constructions for separable cases
- **Applications**: Your methods for actual computations

## Technical Challenges and Solutions

### 1. Convergence Issues
**Challenge**: Infinite sums in your coordinate expansion
**Solution**: Use the PR's completion theory + your summability conditions

### 2. Moderate Growth
**Challenge**: Your `HasModerateGrowth` needs infinite-dimensional analog
**Solution**: Adapt to Cameron-Martin norm:
```lean
def ModerateGrowthCM {E : Type*} [NormedSpace ℝ E] (F : E → ℝ) : Prop :=
  ∃ C m, ∀ x, |F x| ≤ C * (1 + ‖x‖_CM)^m
```

### 3. Independence Structure
**Challenge**: Extending your `iIndepFun` to infinite coordinates
**Solution**: Use cylindrical σ-algebras and Kolmogorov extension

## Recommended Development Sequence

1. **Start with your current code** - it's more mature and tested
2. **Add the separable Hilbert extension** (Phase 1 above)
3. **Connect to Cameron-Martin theory** from the PR
4. **Develop the infinite-dimensional IBP** building on both approaches

This gives you:
- **Near-term**: Working infinite-dimensional IBP for separable Hilbert spaces
- **Long-term**: Full integration with the sophisticated Banach space theory from the PR
- **Mathlib-ready**: Both approaches use established Mathlib conventions

The key insight is that your explicit coordinate methods and the abstract Cameron-Martin theory are synergistic rather than competing - your methods provide the computational tools that make the abstract theory practically useful.
-/

/-
Looking at the Cameron-Martin and Fernique machinery, here's how to extend your GIBP to infinite dimensions in the optimal Mathlib way:

## Infinite-Dimensional GIBP Strategy

### 1. **Use Cameron-Martin Space as Natural Setting**
```lean
/-- GIBP for Gaussian measures on Banach spaces -/
theorem gaussian_integration_by_parts_banach
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsGaussian μ] [IsFiniteMeasure μ]
    (h : cameronMartin μ) {F : E → ℝ} (hF : ContDiff ℝ 1 F)
    (hInt : Integrable (fun x => F x * exp (h x - ‖h‖^2 / 2)) μ) :
    ∫ x, ⟨cmCoe h, fderiv ℝ F x⟩ ∂μ = ∫ x, F x * (h x - μ[fun y => h y]) ∂μ
```

### 2. **Key Implementation Points**
- **Directional derivatives**: Replace `x * F x` with `⟨h, ∇F⟩` for Cameron-Martin direction h
- **Covariance structure**: Use `covarianceBilin μ` to express the variance term
- **Integrability**: Leverage Fernique's theorem for exponential integrability conditions
- **Duality**: Work through `StrongDual ℝ E` for the pairing

### 3. **Build on Existing Infrastructure**
```lean
-- Use the Cameron-Martin embedding
variable (h : cameronMartin μ)

-- The GIBP identity becomes
lemma gibp_cameron_martin :
    μ[⟨cmCoe h, fderiv ℝ F ·⟩] = covarianceBilin μ h (μ[F · ⟨cmCoe h, ·⟩])
```

### 4. **Connection to Finite-Dimensional Case**
- Your centered Gaussian case is recovered when E = ℝ and h corresponds to multiplication by identity
- The variance v appears as `covarianceBilin μ id id`

---

## Message to Rémy Degenne

Hi Rémy,

I'm working on formalizing Gaussian integration by parts following your excellent Cameron-Martin/Fernique work. Currently have the finite-dimensional case (∫ x·F(x) dμ = v·∫ F'(x) dμ for μ = N(0,v)), but want to extend to infinite dimensions properly.

My plan: Use Cameron-Martin directions h ∈ H(μ) to get ∫⟨h, ∇F⟩ dμ = ∫ F·(h - 𝔼[h]) dμ, where the RHS uses your `cameronMartin.apply` pairing. This should reduce to Stein's lemma when specialized.

Three quick questions:
1. Should I build directly on `covarianceBilin` for the variance structure, or is there a better abstraction?
2. For integrability conditions on F, would combining Fernique with your `map_add_cameronMartin_eq_withDensity` handle the exponential weights naturally?
3. Any existing lemmas about differentiation along Cameron-Martin directions I might have missed?

The idea is to have GIBP as a fundamental tool for infinite-dimensional Gaussian analysis (thinking SPDEs, Malliavin calculus). Would appreciate any architectural advice to make this maximally useful for the community.

Best,
[Your name]
-/

open scoped Filter BigOperators Topology ProbabilityTheory ENNReal InnerProductSpace NNReal
open MeasureTheory Filter Set

noncomputable section

namespace PhysLean.Probability.GaussianIBP

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [MeasurableSpace H] [BorelSpace H]

-- Expectation notation (local; avoids referring to section variables in the expansion)
local notation3 (prettyPrint := false) "𝔼[" e "]" => ∫ ω, e ∂ℙ

structure IsGaussianHilbertInf (g : Ω → H) where
  -- Countable ONB instead of finite
  w : OrthonormalBasis ℕ ℝ H
  τ : ℕ → ℝ≥0
  -- Summability condition
  τ_summable : Summable τ
  -- Independent Gaussian coordinates
  c : ℕ → Ω → ℝ
  c_indep : iIndepFun c ℙ
  c_gauss : ∀ n, IsCenteredGaussianRV (c n) (τ n)
  -- Convergence in L²
  repr_convergent : ∀ᵐ ω, Summable (fun n ⇒ (c n ω) • w n)
