/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Jonathan Washburn
-/

module

public import Mathlib.CategoryTheory.Filtration.InducedOnGr

/-!
## Iterated graded pieces

For decreasing `ℤ`-filtrations `F` and `G` on an object `X` in an abelian category, Deligne
considers the *iterated graded* objects `Gr_F^p(Gr_G^q(X))` (Deligne, *Théorie de Hodge II*, §1.2.1).

This file defines:
- `grIter F G p q := Gr_F^p(Gr_G^q(X))`,
- the corresponding opposedness predicate stated via iterated graded pieces.
-/

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory

universe v u
variable {C : Type u} [Category.{v} C]

namespace Filtration
namespace DecFiltration

variable {X : C}

section
variable [Abelian C]

/-- The iterated graded piece `Gr_F^p(Gr_G^q(X))` (Deligne §1.2.1).

By definition this is the graded piece of the induced filtration of `F` on `Gr_G^q(X)`. -/
noncomputable def grIter (F G : Filtration.DecFiltration (C := C) X) (p q : ℤ) : C :=
  (inducedOnGr (C := C) (X := X) F G q).gr p

@[simp]
lemma grIter_def (F G : Filtration.DecFiltration (C := C) X) (p q : ℤ) :
    grIter (C := C) (X := X) F G p q = (inducedOnGr (C := C) (X := X) F G q).gr p := rfl

/-- Deligne's `n`-opposedness predicate phrased using iterated graded pieces.

Deligne (1.2.3) states opposedness in terms of `Gr_F^p Gr_G^q(X)` vanishing off the diagonal. -/
def IsNOpposedIter (F G : Filtration.DecFiltration (C := C) X) (n : ℤ) : Prop :=
  ∀ p q : ℤ, p + q ≠ n → IsZero (grIter (C := C) (X := X) F G p q)

lemma isZero_grIter_of_IsNOpposedIter {F G : Filtration.DecFiltration (C := C) X} {n p q : ℤ}
    (h : IsNOpposedIter (C := C) (X := X) F G n) (hpq : p + q ≠ n) :
    IsZero (grIter (C := C) (X := X) F G p q) :=
  h p q hpq

end

end DecFiltration
end Filtration

end CategoryTheory

