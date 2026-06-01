/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZetaConvexity

/-!
# Strip bounds for the Riemann zeta function

Entry point for bounds on `riemannZeta` used in `ZetaFiniteOrder` (finite order of
`completedRiemannZeta₀`). Proofs are in `RiemannZetaConvexity`.

## Main results

* `norm_riemannZeta_le` : bound on `‖ζ s‖` for `1/10 < re s`, `s ≠ 1`
* `norm_riemannZeta_shift_le` : linear bound for `ζ (s + 3/2 + it)` with `‖s‖ ≤ 1`
* `norm_riemannZeta_ratio_le_on_vertical_line` : vertical-line lower bound via Euler products
-/
