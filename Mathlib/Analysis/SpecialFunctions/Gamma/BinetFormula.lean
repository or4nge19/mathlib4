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
* `Mathlib.Analysis.SpecialFunctions.Gamma.BinetRealBounds` — sharp bounds on `(J x).re`
* `Mathlib.Analysis.SpecialFunctions.Gamma.BinetGammaBound` — strip bounds for `Γ`

## Main results

* `Binet.log_Gamma_real_eq` : Binet's formula for `Real.log (Real.Gamma x)`
* `Binet.re_J_lt_one_div_twelve`, `Binet.re_J_ge_one_div_twelve_add_one` : Robbins two-sided
  bounds on `(J x).re`
* `Binet.J_norm_le_re` : `‖J z‖ ≤ 1 / (12 * re z)` for `0 < re z` (in `BinetIntegral`)
* Robbins bounds for `n!` live in `Mathlib.Analysis.SpecialFunctions.Gamma.StirlingRobbins`.

This is independent of the Weierstrass-product construction of `Γ` discussed in Tao 246B Notes 1:
the proofs here use Binet's integral formula and explicit kernel bounds.
-/
