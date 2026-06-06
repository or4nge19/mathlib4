/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.BinetGammaBound
public import Mathlib.Analysis.SpecialFunctions.Gamma.BinetLogGamma
public import Mathlib.Analysis.SpecialFunctions.Gamma.BinetRealBounds

/-!
# Binet's formula for log Γ

This module aggregates the Binet development split across:

* `Mathlib.Analysis.SpecialFunctions.Gamma.BinetKernel` — the kernel `K̃`
* `Mathlib.Analysis.SpecialFunctions.Gamma.BinetIntegral` — the integral `J` and `‖J z‖` bounds
* `Mathlib.Analysis.SpecialFunctions.Gamma.BinetRealIntegral` — real specialization of `J`
* `BinetLogGammaPre`, `BinetLogGammaRecurrence`, `BinetLogGamma` — Binet's formula for `Real.log Γ`
* `Mathlib.Analysis.SpecialFunctions.Gamma.BinetRealBounds` — real bounds on `(J x).re`
* `Mathlib.Analysis.SpecialFunctions.Gamma.BinetGammaBound` — strip bounds for `Γ`

## Main results

* `Binet.log_Gamma_real_eq` : Binet's formula for `Real.log (Real.Gamma x)`
* `Binet.re_J_robbins_bounds`, `Binet.re_J_robbins_bounds_strict_upper` : Robbins two-sided
  bounds on `(J x).re`
* `Binet.J_norm_le_re` : `‖J z‖ ≤ 1 / (12 * re z)` for `0 < re z` (in `BinetIntegral`)
* Robbins bounds for `n!` live in `Mathlib.Analysis.SpecialFunctions.Gamma.StirlingRobbins`.

This is independent of the Weierstrass-product construction of `Γ` discussed in Tao 246B Notes 1:
the proofs here use Binet's integral formula and explicit kernel bounds, though the closed-form
real Binet formula currently uses Mathlib's existing Stirling limit to identify the integration
constant.

The current closed-form theorem is real-axis Binet formula.  A statement with the principal
complex logarithm `Complex.log (Complex.Gamma z)` is not valid on the full right half-plane; a
complex formulation needs a chosen holomorphic branch of `log Γ`.  Also note that the proof of
`Binet.log_Gamma_real_eq` currently uses the existing Stirling limit from
`Mathlib.Analysis.SpecialFunctions.Stirling` to identify the integration constant.

## References

* [DLMF], §5.9.10_2 for Binet's first integral formula
* [DLMF], §5.11 for Stirling asymptotic background and error bounds
* [whittakerWatson1927], Chapter XII for the classical Gamma-function background
* [robbins1955] for the sharp bounds used downstream in `StirlingRobbins`
-/
