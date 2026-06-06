/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.BinetKernel.Core
public import Mathlib.Analysis.SpecialFunctions.Gamma.BinetKernel.Bounds
public import Mathlib.Analysis.SpecialFunctions.Gamma.BinetKernel.Limit

/-!
# The Binet kernel

Aggregates `BinetKernel.Core`, `BinetKernel.Bounds`, and `BinetKernel.Limit`.

## Main results

* `BinetKernel.tendsto_Ktilde_zero` : `Ktilde t → 1/12` as `t → 0⁺`
* `BinetKernel.Ktilde_ge_one_div_twelve_mul_exp_neg_div_twelve` : Robbins-style lower bound
* `BinetKernel.integrable_Ktilde_exp`, `integrable_Ktilde_exp_complex`
-/
