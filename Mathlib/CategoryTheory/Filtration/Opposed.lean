/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Jonathan Washburn
-/

module


public import Mathlib.CategoryTheory.Filtration.Subobject
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-!
## Opposed filtrations (Deligne, *Théorie de Hodge II*, §1.2.1–§1.2.3)

For decreasing `ℤ`-filtrations `F` and `G` on `X` in an abelian category, we define the
Zassenhaus bigraded piece `gr₂`.

For the opposedness predicate, the definition is the "direct sum" formulation
(Deligne Proposition (1.2.5)(i)), as suggested by the reviewer. We keep the `gr₂`-vanishing
formulation as a separate predicate (`IsNOpposedGr₂`) for downstream lemmas.
-/

@[expose] public section

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

/-- The Zassenhaus (symmetric) bigraded piece (Deligne 1.2), defined as a cokernel. -/
noncomputable def gr₂ (F G : Filtration.DecFiltration (C := C) X) (p q : ℤ) : C := by
  classical
  let Xpq : Subobject X := F.step p ⊓ G.step q
  let Ypq : Subobject X := (F.step (p + 1) ⊓ G.step q) ⊔ (F.step p ⊓ G.step (q + 1))
  have hY : Ypq ≤ Xpq := by
    refine sup_le ?_ ?_
    · have hp : (Opposite.op (p + 1) : ℤᵒᵖ) ⟶ (Opposite.op p : ℤᵒᵖ) := by
        exact (homOfLE (show p ≤ p + 1 from
          le_add_of_nonneg_right (show (0 : ℤ) ≤ 1 by decide))).op
      have hF : F.step (p + 1) ≤ F.step p := by
        simpa [Filtration.DecFiltration.step] using (F.subobject_le_of_hom hp)
      exact inf_le_inf hF le_rfl
    · have hq : (Opposite.op (q + 1) : ℤᵒᵖ) ⟶ (Opposite.op q : ℤᵒᵖ) := by
        exact (homOfLE (show q ≤ q + 1 from
          le_add_of_nonneg_right (show (0 : ℤ) ≤ 1 by decide))).op
      have hG : G.step (q + 1) ≤ G.step q := by
        simpa [Filtration.DecFiltration.step] using (G.subobject_le_of_hom hq)
      exact inf_le_inf le_rfl hG
  exact cokernel ((Ypq).ofLE Xpq hY)

/-- The `gr₂`-vanishing opposedness predicate (Deligne 1.2.3). -/
def IsNOpposedGr₂ (F G : Filtration.DecFiltration (C := C) X) (n : ℤ) : Prop :=
  ∀ p q : ℤ, p + q ≠ n → IsZero (gr₂ (C := C) (X := X) F G p q)

/-- Opposedness via direct sum decompositions (Deligne Proposition (1.2.5)(i)).

For all `p q` with `p+q = n+1`, the maps `F^p ⟶ X` and `G^q ⟶ X` exhibit `X` as their coproduct.
In an abelian category this is equivalent to a biproduct decomposition.
-/
def IsNOpposed (F G : Filtration.DecFiltration (C := C) X) (n : ℤ) : Prop :=
  ∀ p q : ℤ, p + q = n + 1 →
    Nonempty (IsColimit (BinaryCofan.mk (F.inj (Opposite.op p)) (G.inj (Opposite.op q))))

/-- Deligne's `n`-opposed condition for **finite** filtrations.

This bundles Deligne's finiteness hypotheses (Deligne 1.2.3).
-/
def IsNOpposedFinite (F G : Filtration.DecFiltration (C := C) X) (n : ℤ) : Prop :=
  Filtration.DecFiltration.IsFinite (C := C) (X := X) F ∧
    Filtration.DecFiltration.IsFinite (C := C) (X := X) G ∧
      IsNOpposed (C := C) (X := X) F G n

lemma isFinite_left_of_isNOpposedFinite {F G : Filtration.DecFiltration (C := C) X} {n : ℤ}
    (h : IsNOpposedFinite (C := C) (X := X) F G n) :
    Filtration.DecFiltration.IsFinite (C := C) (X := X) F :=
  h.1

lemma isFinite_right_of_isNOpposedFinite {F G : Filtration.DecFiltration (C := C) X} {n : ℤ}
    (h : IsNOpposedFinite (C := C) (X := X) F G n) :
    Filtration.DecFiltration.IsFinite (C := C) (X := X) G :=
  h.2.1

lemma isNOpposed_of_isNOpposedFinite {F G : Filtration.DecFiltration (C := C) X} {n : ℤ}
    (h : IsNOpposedFinite (C := C) (X := X) F G n) :
    IsNOpposed (C := C) (X := X) F G n :=
  h.2.2

/-- Convenience lemma for the `gr₂`-vanishing formulation. -/
lemma isZero_gr₂_of_IsNOpposedGr₂ {F G : Filtration.DecFiltration (C := C) X} {n p q : ℤ}
    (h : IsNOpposedGr₂ (C := C) (X := X) F G n) (hpq : p + q ≠ n) :
    IsZero (gr₂ (C := C) (X := X) F G p q) :=
  h p q hpq

end

end DecFiltration

end Filtration

end CategoryTheory
