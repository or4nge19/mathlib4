/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Jonathan Washburn
-/

module

public import Mathlib.CategoryTheory.Filtration.Basic
public import Mathlib.CategoryTheory.Subobject.Lattice

/-!
## Filtrations and `Subobject`

This file contains the `Subobject`-based API for filtrations:

- interpreting a filtration step as a subobject,
- for decreasing `ℤ`-filtrations: `step`, finiteness, `ofAntitone`, shifting,
- induced filtrations along morphisms using pullbacks and images,
- Deligne-style "preserves filtration" predicates phrased via images.

The core definition of a filtration as a functor `ι ⥤ MonoOver X` lives in
`Mathlib.CategoryTheory.Filtration.Basic`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

namespace Filtration

variable {X : C} {ι : Type*} [Category ι]

/-- The `i`-th filtration step as a subobject of `X`. -/
noncomputable def subobject (F : Filtration X ι) (i : ι) : Subobject X :=
  Subobject.mk (F.inj i)

@[simp, reassoc]
lemma subobject_arrow_eq (F : Filtration X ι) (i : ι) :
    (Subobject.mk (F.inj i)).arrow = (F.subobject i).arrow := rfl

/-- A morphism in the index category induces an inclusion of steps. -/
lemma subobject_le_of_hom (F : Filtration X ι) {i j : ι} (f : i ⟶ j) :
    F.subobject i ≤ F.subobject j := by
  classical
  refine Subobject.mk_le_mk_of_comm ((F.toMonoOver.map f).hom.left) ?_
  simp [Filtration.inj_eq]

end Filtration

namespace FilteredObject

section Images

variable [HasImages C]

/-- The image of a subobject under a morphism. -/
noncomputable def imageSubobject {A B : C} (f : A ⟶ B) (S : Subobject A) : Subobject B :=
  Subobject.mk (image.ι (S.arrow ≫ f))

lemma imageSubobject_mono {A B : C} (f : A ⟶ B) :
    Monotone (imageSubobject (C := C) f) := by
  intro S T hle
  classical
  dsimp [imageSubobject]
  refine Subobject.mk_le_mk_of_comm (image.lift
    { I := image (T.arrow ≫ f)
      m := image.ι (T.arrow ≫ f)
      e := S.ofLE T hle ≫ factorThruImage (T.arrow ≫ f)
      fac := by
        rw [Category.assoc, image.fac, ← Category.assoc, Subobject.ofLE_arrow] }) ?_
  exact image.lift_fac _

end Images

section DeligneCompatibility

variable [HasImages C]
variable {ι : Type*} [Category ι]
variable {F G : FilteredObject C ι}

/-- Deligne-style filtration preservation for a morphism `f : F.X ⟶ G.X`. -/
def PreservesFiltration (f : F.X ⟶ G.X) : Prop :=
  ∀ i : ι,
    imageSubobject (C := C) f (Filtration.subobject (F := F.filtration) i) ≤
      Filtration.subobject (F := G.filtration) i

/-- A morphism of filtered objects induces Deligne-style filtration preservation. -/
lemma Hom.preservesFiltration (f : F ⟶ G) :
    PreservesFiltration (C := C) (F := F) (G := G) f.hom := by
  intro i
  classical
  -- Let `S` be the `i`-th filtration subobject of `F.X`.
  set S : Subobject F.X := Filtration.subobject (F := F.filtration) i
  dsimp [PreservesFiltration, imageSubobject]
  have hS : S.arrow =
      (Subobject.underlyingIso (F.filtration.inj i)).hom ≫ F.filtration.inj i := by
    simp [S, Filtration.subobject]
  let MF : MonoFactorisation (S.arrow ≫ f.hom) :=
    { I := G.filtration.obj i
      m := G.filtration.inj i
      e := (Subobject.underlyingIso (F.filtration.inj i)).hom ≫ f.natTrans.app i
      fac := by
        simp [hS, Category.assoc, f.comm i] }
  refine Subobject.mk_le_mk_of_comm (image.lift MF) ?_
  exact image.lift_fac MF

end DeligneCompatibility

end FilteredObject

namespace Filtration

section Induced

variable {X Y : C} {ι : Type*} [Category ι]

/-!
### Induced filtrations along morphisms

These are the two general constructions suggested by the reviewer:

- given `f : X ⟶ Y`, push a filtration on `X` forward to `Y` using images;
- given `f : Y ⟶ X`, pull a filtration on `X` back to `Y` using pullbacks.
-/

section Pushforward

variable [HasImages C]

/-- Push a filtration forward along `f : X ⟶ Y`, using images. -/
noncomputable def pushforward (F : Filtration X ι) (f : X ⟶ Y) : Filtration Y ι where
  toMonoOver :=
    { obj := fun i =>
        MonoOver.mk (X := Y) (FilteredObject.imageSubobject (C := C) f (F.subobject i)).arrow
      map := fun {i j} g => by
        have hle :
            FilteredObject.imageSubobject (C := C) f (F.subobject i) ≤
              FilteredObject.imageSubobject (C := C) f (F.subobject j) :=
          (FilteredObject.imageSubobject_mono (C := C) f) (subobject_le_of_hom (F := F) g)
        refine MonoOver.homMk
          ((FilteredObject.imageSubobject (C := C) f (F.subobject i)).ofLE
            (FilteredObject.imageSubobject (C := C) f (F.subobject j)) hle) ?_
        simp [MonoOver.mk, MonoOver.arrow, Subobject.ofLE_arrow]
      map_id := by intro i; apply Subsingleton.elim
      map_comp := by intro i j k g h; apply Subsingleton.elim }

end Pushforward

section Pullback

variable [HasPullbacks C]

/-- Pull back a filtration along `f : Y ⟶ X`, using pullbacks of subobjects. -/
noncomputable def pullback (F : Filtration X ι) (f : Y ⟶ X) : Filtration Y ι where
  toMonoOver :=
    { obj := fun i =>
        MonoOver.mk (X := Y) ((Subobject.pullback f).obj (F.subobject i)).arrow
      map := fun {i j} g => by
        have hle :
            (Subobject.pullback f).obj (F.subobject i) ≤
              (Subobject.pullback f).obj (F.subobject j) :=
          (Subobject.pullback f).monotone (subobject_le_of_hom (F := F) g)
        refine MonoOver.homMk
          (((Subobject.pullback f).obj (F.subobject i)).ofLE
            ((Subobject.pullback f).obj (F.subobject j)) hle) ?_
        simp [MonoOver.mk, MonoOver.arrow, Subobject.ofLE_arrow]
      map_id := by intro i; apply Subsingleton.elim
      map_comp := by intro i j k g h; apply Subsingleton.elim }

end Pullback

end Induced

end Filtration

/-!
## `ℤ`-indexed specializations using `Subobject`
-/

namespace Filtration

open Opposite

namespace DecFiltration

variable {X : C}

/-- The `n`-th step as a subobject of `X`. -/
noncomputable abbrev step (F : DecFiltration (C := C) X) (n : ℤ) : Subobject X :=
  Filtration.subobject (F := F) (Opposite.op n)

lemma step_le_step_of_le (F : DecFiltration (C := C) X) {n m : ℤ} (h : n ≤ m) :
    F.step m ≤ F.step n := by
  -- A morphism `op m ⟶ op n` in `ℤᵒᵖ` is the opposite of a morphism `n ⟶ m` in `ℤ`.
  simpa using (Filtration.subobject_le_of_hom (F := F) ((homOfLE h).op))

/-- The steps of a decreasing `ℤ`-filtration form an antitone function. -/
lemma step_antitone (F : DecFiltration (C := C) X) : Antitone F.step := by
  intro n m h
  exact step_le_step_of_le (C := C) (X := X) F h

section Finite

variable [HasZeroObject C] [HasZeroMorphisms C]

/-- Finiteness/boundedness of a decreasing `ℤ`-filtration (Deligne 1.1.4). -/
def IsFinite (F : DecFiltration (C := C) X) : Prop :=
  ∃ a b : ℤ,
    (∀ n : ℤ, n ≤ a → F.step n = ⊤) ∧ (∀ n : ℤ, b ≤ n → F.step n = ⊥)

end Finite

section OfSubobject

/-- Build a decreasing `ℤ`-filtration from an antitone function `ℤ → Subobject X`. -/
noncomputable def ofAntitone (F : ℤ → Subobject X) (hF : Antitone F) :
    DecFiltration (C := C) X := by
  classical
  refine { toMonoOver := ?_ }
  refine
    { obj := fun n => MonoOver.mk (X := X) (F (Opposite.unop n)).arrow
      map := fun {i j} f => by
        have hij : Opposite.unop j ≤ Opposite.unop i := by
          simpa using (show Opposite.unop j ≤ Opposite.unop i from leOfHom f.unop)
        have hle : F (Opposite.unop i) ≤ F (Opposite.unop j) := hF hij
        refine MonoOver.homMk ((F (Opposite.unop i)).ofLE (F (Opposite.unop j)) hle) ?_
        simp [MonoOver.mk, MonoOver.arrow, Subobject.ofLE_arrow]
      map_id := by intro i; apply Subsingleton.elim
      map_comp := by intro i j k f g; apply Subsingleton.elim }

@[simp]
lemma ofAntitone_step (F : ℤ → Subobject X) (hF : Antitone F) (n : ℤ) :
    (ofAntitone (C := C) (X := X) F hF).step n = F n := by
  classical
  simp [ofAntitone, DecFiltration.step, Filtration.subobject, Filtration.inj, Subobject.mk_arrow]

end OfSubobject

end DecFiltration

end Filtration

end CategoryTheory
