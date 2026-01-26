/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Jonathan Washburn
-/

module

public import Mathlib.CategoryTheory.Filtration.Subobject
public import Mathlib.CategoryTheory.Abelian.Opposite
public import Mathlib.Tactic.Linarith

/-!
## Dual Deligne filtration

In an abelian category, Deligne defines a dual filtration on the opposite object (Deligne (1.1.6)).

This file formalizes:
- the quotient object `X ⧸ S` of a subobject `S : Subobject X`,
- the corresponding quotient subobject of `Xᵒᵖ`,
- the dual Deligne filtration `dualDeligne` on `Xᵒᵖ`,
- preservation of finiteness/boundedness under dualization.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory

universe v u
variable {C : Type u} [Category.{v} C]

namespace Filtration
namespace DecFiltration

open Opposite

variable {X : C}

section Abelian

variable [Abelian C]

/-- The quotient object `X ⧸ S`, defined as the cokernel of `S.arrow`. -/
noncomputable def quotientObj (S : Subobject X) : C :=
  cokernel S.arrow

/-- The canonical projection `X ⟶ X ⧸ S`. -/
noncomputable def quotientπ (S : Subobject X) : X ⟶ quotientObj (C := C) (X := X) S :=
  cokernel.π S.arrow

/-- If `S₁ ≤ S₂`, there is a canonical map `X ⧸ S₁ ⟶ X ⧸ S₂` commuting with projections. -/
noncomputable def quotientMap {S₁ S₂ : Subobject X} (h : S₁ ≤ S₂) :
    quotientObj (C := C) (X := X) S₁ ⟶ quotientObj (C := C) (X := X) S₂ :=
  cokernel.desc S₁.arrow (quotientπ (C := C) (X := X) S₂) (by
    have : S₁.arrow = (Subobject.ofLE S₁ S₂ h) ≫ S₂.arrow := by
      simp [Subobject.ofLE_arrow]
    calc
      S₁.arrow ≫ quotientπ (C := C) (X := X) S₂
          = (Subobject.ofLE S₁ S₂ h) ≫ S₂.arrow ≫ quotientπ (C := C) (X := X) S₂ := by
              rw [this]
              simp
      _ = 0 := by
            simp [quotientπ])

@[simp, reassoc]
lemma quotientπ_quotientMap {S₁ S₂ : Subobject X} (h : S₁ ≤ S₂) :
    quotientπ (C := C) (X := X) S₁ ≫ quotientMap (C := C) (X := X) h =
      quotientπ (C := C) (X := X) S₂ := by
  simp [quotientMap, quotientπ]

/-!
### Exactness around quotient maps

For `S₁ ≤ S₂` we record the standard exact sequence
\[
S₂ \to X/S₁ \to X/S₂ \to 0,
\]
by showing that `quotientMap h : X ⧸ S₁ ⟶ X ⧸ S₂` is the cokernel of the induced map
`(S₂ : C) ⟶ X ⧸ S₁`.
-/

/-- The canonical map `(S₂ : C) ⟶ X ⧸ S₁` induced by the inclusion `S₂ ↪ X` and the projection
`X ⟶ X ⧸ S₁`. -/
noncomputable def quotientMapKernelLeft (S₁ S₂ : Subobject X) :
    (S₂ : C) ⟶ quotientObj (C := C) (X := X) S₁ :=
  S₂.arrow ≫ quotientπ (C := C) (X := X) S₁

@[simp, reassoc]
lemma quotientMapKernelLeft_comp {S₁ S₂ : Subobject X} (h : S₁ ≤ S₂) :
    quotientMapKernelLeft (C := C) (X := X) S₁ S₂ ≫ quotientMap (C := C) (X := X) h = 0 := by
  dsimp [quotientMapKernelLeft]
  -- Reduce to the defining relation of the cokernel map `quotientπ S₂`.
  have hπ :
      quotientπ (C := C) (X := X) S₁ ≫ quotientMap (C := C) (X := X) h =
        quotientπ (C := C) (X := X) S₂ :=
    quotientπ_quotientMap (C := C) (X := X) (S₁ := S₁) (S₂ := S₂) h
  calc
    (S₂.arrow ≫ quotientπ (C := C) (X := X) S₁) ≫ quotientMap (C := C) (X := X) h
        = S₂.arrow ≫ quotientπ (C := C) (X := X) S₂ := by
            simp [Category.assoc, hπ]
    _ = 0 := by
          simp [quotientπ, quotientObj]

/-- `quotientMap h : X ⧸ S₁ ⟶ X ⧸ S₂` is the cokernel of the map
`quotientMapKernelLeft h : S₂ ⟶ X ⧸ S₁`. -/
noncomputable def quotientMapIsCokernel {S₁ S₂ : Subobject X} (h : S₁ ≤ S₂) :
    IsColimit (CokernelCofork.ofπ (quotientMap (C := C) (X := X) h)
      (quotientMapKernelLeft_comp (C := C) (X := X) h)) := by
  -- We'll use the convenience lemma `CokernelCofork.IsColimit.ofπ'`, cancelling epis.
  haveI : Epi (quotientMap (C := C) (X := X) h) := by
    haveI : Epi (cokernel.π S₁.arrow) := by infer_instance
    haveI : Epi (cokernel.π S₂.arrow) := by infer_instance
    have hπ :
        (cokernel.π S₁.arrow) ≫ quotientMap (C := C) (X := X) h = cokernel.π S₂.arrow := by
      simpa [quotientπ] using (quotientπ_quotientMap (C := C) (X := X) (S₁ := S₁) (S₂ := S₂) h)
    haveI : Epi ((cokernel.π S₁.arrow) ≫ quotientMap (C := C) (X := X) h) := by
      simpa [hπ] using (inferInstance : Epi (cokernel.π S₂.arrow))
    exact epi_of_epi (cokernel.π S₁.arrow) (quotientMap (C := C) (X := X) h)
  refine CokernelCofork.IsColimit.ofπ' (p := quotientMap (C := C) (X := X) h)
    (w := quotientMapKernelLeft_comp (C := C) (X := X) h) ?_
  intro A k hk
  refine ⟨cokernel.desc S₂.arrow (quotientπ (C := C) (X := X) S₁ ≫ k) ?_, ?_⟩
  · simpa [quotientMapKernelLeft, Category.assoc] using hk
  · -- cancel the epi `quotientπ S₁`
    apply (cancel_epi (cokernel.π S₁.arrow)).1
    have hπ :
        (cokernel.π S₁.arrow) ≫ quotientMap (C := C) (X := X) h = cokernel.π S₂.arrow := by
      simpa [quotientπ] using
        (quotientπ_quotientMap (C := C) (X := X) (S₁ := S₁) (S₂ := S₂) h)
    -- now use the cokernel universal property of `S₂.arrow`
    let d :
        quotientObj (C := C) (X := X) S₂ ⟶ A :=
      cokernel.desc S₂.arrow (quotientπ (C := C) (X := X) S₁ ≫ k)
        (by
          simpa [quotientMapKernelLeft, Category.assoc] using hk)
    have hπ' : ((cokernel.π S₁.arrow) ≫ quotientMap (C := C) (X := X) h) ≫ d =
        (cokernel.π S₂.arrow) ≫ d :=
      congrArg (fun t => t ≫ d) hπ
    -- reassociate, rewrite using `hπ`, then use `cokernel.π_desc`.
    simpa [Category.assoc, d] using
      (by
        -- `hπ'` gives the key rewrite
        simpa [Category.assoc] using hπ'.trans (by simp [d, quotientπ, quotientObj]))

/-- The quotient subobject of `Xᵒᵖ` associated to `S ≤ X`. -/
noncomputable def quotientSubobject (S : Subobject X) : Subobject (Opposite.op X) := by
  -- `quotientπ S` is a cokernel map, hence epi; thus its opposite is mono.
  haveI : Epi (quotientπ (C := C) (X := X) S) := by
    dsimp [quotientπ, quotientObj]
    infer_instance
  exact Subobject.mk ((quotientπ (C := C) (X := X) S).op)

lemma quotientSubobject_antitone :
    Antitone (quotientSubobject (C := C) (X := X) : Subobject X → Subobject (Opposite.op X)) := by
  intro S₁ S₂ h12
  -- Help typeclass search: `quotientπ` is epi, hence its opposite is mono.
  haveI : Mono (quotientπ (C := C) (X := X) S₁).op := by
    haveI : Epi (quotientπ (C := C) (X := X) S₁) := by
      dsimp [quotientπ, quotientObj]
      infer_instance
    infer_instance
  haveI : Mono (quotientπ (C := C) (X := X) S₂).op := by
    haveI : Epi (quotientπ (C := C) (X := X) S₂) := by
      dsimp [quotientπ, quotientObj]
      infer_instance
    infer_instance
  dsimp [quotientSubobject]
  refine Subobject.mk_le_mk_of_comm ((quotientMap (C := C) (X := X) h12).op) ?_
  apply Quiver.Hom.unop_inj
  simp [quotientπ_quotientMap]

/-- `quotientSubobject ⊥ = ⊤`. -/
lemma quotientSubobject_bot :
    quotientSubobject (C := C) (X := X) (⊥ : Subobject X) = ⊤ := by
  classical
  -- `⊥.arrow = 0`, hence its cokernel map is an isomorphism.
  let f : ((⊥ : Subobject X) : C) ⟶ X := (⊥ : Subobject X).arrow
  have hf : f = 0 := by
    dsimp [f]
    simp
  let i : cokernel f ≅ cokernel (0 : ((⊥ : Subobject X) : C) ⟶ X) := cokernelIsoOfEq hf
  haveI : IsIso (cokernel.π f ≫ i.hom) := by
    simpa [i] using
      (show IsIso (cokernel.π (0 : ((⊥ : Subobject X) : C) ⟶ X)) from inferInstance)
  haveI : IsIso (cokernel.π f) := by
    exact IsIso.of_isIso_comp_right (cokernel.π f) i.hom
  haveI : IsIso (quotientπ (C := C) (X := X) (⊥ : Subobject X)) := by
    dsimp [quotientπ]
    simpa [f] using (inferInstance : IsIso (cokernel.π f))
  haveI : IsIso ((quotientπ (C := C) (X := X) (⊥ : Subobject X)).op) := by
    infer_instance
  simpa [quotientSubobject] using
    (Subobject.isIso_iff_mk_eq_top ((quotientπ (C := C) (X := X) (⊥ : Subobject X)).op)).1
      (inferInstance : IsIso ((quotientπ (C := C) (X := X) (⊥ : Subobject X)).op))

/-- `quotientSubobject ⊤ = ⊥`. -/
lemma quotientSubobject_top :
    quotientSubobject (C := C) (X := X) (⊤ : Subobject X) = ⊥ := by
  classical
  haveI : Epi (quotientπ (C := C) (X := X) (⊤ : Subobject X)) := by
    dsimp [quotientπ, quotientObj]
    infer_instance
  haveI : Mono ((quotientπ (C := C) (X := X) (⊤ : Subobject X)).op) := by
    infer_instance
  haveI : Epi ((⊤ : Subobject X).arrow) := by infer_instance
  have hπ : quotientπ (C := C) (X := X) (⊤ : Subobject X) = 0 := by
    dsimp [quotientπ, quotientObj]
    simpa using (cokernel.π_of_epi ((⊤ : Subobject X).arrow))
  have : Subobject.mk ((quotientπ (C := C)
      (X := X) (⊤ : Subobject X)).op) = (⊥ : Subobject (Opposite.op X)) := by
    apply (Subobject.mk_eq_bot_iff_zero).2
    simp [hπ]
  simpa [quotientSubobject] using this

/-- The chosen underlying object of `quotientSubobject S` is isomorphic to `(X ⧸ S)ᵒᵖ`. -/
noncomputable def quotientSubobjectObjIso (S : Subobject X) :
    (quotientSubobject (C := C) (X := X) S : Cᵒᵖ) ≅
      Opposite.op (quotientObj (C := C) (X := X) S) := by
  classical
  haveI : Epi (quotientπ (C := C) (X := X) S) := by
    dsimp [quotientπ, quotientObj]
    infer_instance
  haveI : Mono ((quotientπ (C := C) (X := X) S).op) := by
    infer_instance
  -- `quotientSubobject S` is defined as `Subobject.mk ((quotientπ S).op)`.
  simpa [quotientSubobject] using
    (Subobject.underlyingIso ((quotientπ (C := C) (X := X) S).op))

@[simp, reassoc]
lemma quotientSubobjectObjIso_hom_comp (S : Subobject X) :
    (quotientSubobjectObjIso (C := C) (X := X) S).hom ≫
        (quotientπ (C := C) (X := X) S).op =
      (quotientSubobject (C := C) (X := X) S).arrow := by
  classical
  haveI : Epi (quotientπ (C := C) (X := X) S) := by
    dsimp [quotientπ, quotientObj]
    infer_instance
  haveI : Mono ((quotientπ (C := C) (X := X) S).op) := by
    infer_instance
  -- This is `Subobject.underlyingIso_hom_comp_eq_mk`.
  simpa [quotientSubobjectObjIso, quotientSubobject] using
    (Subobject.underlyingIso_hom_comp_eq_mk ((quotientπ (C := C) (X := X) S).op))

@[simp, reassoc]
lemma quotientSubobjectObjIso_inv_comp (S : Subobject X) :
    (quotientSubobjectObjIso (C := C) (X := X) S).inv ≫
        (quotientSubobject (C := C) (X := X) S).arrow =
      (quotientπ (C := C) (X := X) S).op := by
  classical
  haveI : Epi (quotientπ (C := C) (X := X) S) := by
    dsimp [quotientπ, quotientObj]
    infer_instance
  haveI : Mono ((quotientπ (C := C) (X := X) S).op) := by
    infer_instance
  simpa [quotientSubobjectObjIso, quotientSubobject] using
    (Subobject.underlyingIso_arrow ((quotientπ (C := C) (X := X) S).op))

/-- Deligne dual filtration `Fᵛ` on `Xᵒᵖ` (Deligne (1.1.6)). -/
noncomputable def dualDeligne (F : Filtration.DecFiltration (C := C) X) :
    Filtration.DecFiltration (C := Cᵒᵖ) (Opposite.op X) := by
  refine Filtration.DecFiltration.ofAntitone (C := Cᵒᵖ) (X := Opposite.op X)
    (fun n : ℤ => quotientSubobject (C := C) (X := X) (F.step (1 - n))) ?_
  intro n m hnm
  have h1 : (1 - m) ≤ (1 - n) := by linarith
  have hF : F.step (1 - n) ≤ F.step (1 - m) :=
    step_le_step_of_le (C := C) (X := X) F h1
  exact quotientSubobject_antitone (C := C) (X := X) hF

@[simp]
lemma dualDeligne_step (F : Filtration.DecFiltration (C := C) X) (n : ℤ) :
    (dualDeligne (C := C) (X := X) F).step n =
      quotientSubobject (C := C) (X := X) (F.step (1 - n)) := by
  simp [dualDeligne]

lemma dualDeligne_succHom_conj (F : Filtration.DecFiltration (C := C) X) (n : ℤ) :
    let S₁ : Subobject X := F.step (1 - n)
    let S₂ : Subobject X := F.step (1 - (n + 1))
    let h : S₁ ≤ S₂ :=
      step_le_step_of_le (C := C) (X := X) F (show (1 - (n + 1)) ≤ (1 - n) by linarith)
    (quotientSubobjectObjIso (C := C) (X := X) S₂).inv ≫
        Filtration.DecFiltration.succHom (dualDeligne (C := C) (X := X) F) n ≫
        (quotientSubobjectObjIso (C := C) (X := X) S₁).hom =
      (quotientMap (C := C) (X := X) h).op := by
  classical
  intro S₁ S₂ h
  -- Cancel the mono `(quotientπ S₁).op`.
  haveI : Epi (quotientπ (C := C) (X := X) S₁) := by
    dsimp [quotientπ, quotientObj]
    infer_instance
  haveI : Mono ((quotientπ (C := C) (X := X) S₁).op) := by
    infer_instance
  apply (cancel_mono ((quotientπ (C := C) (X := X) S₁).op)).1
  -- Use the defining commutativity for `succHom` together with the compatibility of the `ObjIso`s.
  have hs :=
    Filtration.DecFiltration.succHom_comp_inj (dualDeligne (C := C) (X := X) F) n
  -- Rewrite `inj` as the arrow of the corresponding `quotientSubobject`.
  have hs' :
      Filtration.DecFiltration.succHom (dualDeligne (C := C) (X := X) F) n ≫
          (quotientSubobject (C := C) (X := X) S₁).arrow =
        (quotientSubobject (C := C) (X := X) S₂).arrow := by
    simpa [dualDeligne, Filtration.DecFiltration.ofAntitone, Filtration.inj, S₁, S₂] using hs
  -- Now compute both sides after postcomposing with `(quotientπ S₁).op`.
  calc
    ((quotientSubobjectObjIso (C := C) (X := X) S₂).inv ≫
          Filtration.DecFiltration.succHom (dualDeligne (C := C) (X := X) F) n ≫
          (quotientSubobjectObjIso (C := C) (X := X) S₁).hom) ≫
        (quotientπ (C := C) (X := X) S₁).op
        =
        (quotientSubobjectObjIso (C := C) (X := X) S₂).inv ≫
          Filtration.DecFiltration.succHom (dualDeligne (C := C) (X := X) F) n ≫
          (quotientSubobject (C := C) (X := X) S₁).arrow := by
          simp [Category.assoc, quotientSubobjectObjIso_hom_comp]
    _ =
        (quotientSubobjectObjIso (C := C) (X := X) S₂).inv ≫
          (quotientSubobject (C := C) (X := X) S₂).arrow := by
          simp [Category.assoc, hs']
    _ = (quotientπ (C := C) (X := X) S₂).op := by
          simpa using (quotientSubobjectObjIso_inv_comp (C := C) (X := X) S₂)
    _ =
        (quotientMap (C := C) (X := X) h).op ≫ (quotientπ (C := C) (X := X) S₁).op := by
          -- take opposites of `quotientπ_quotientMap`
          apply Quiver.Hom.unop_inj
          simpa using
            (quotientπ_quotientMap (C := C) (X := X) (S₁ := S₁) (S₂ := S₂) h).symm

noncomputable def dualDeligne_grIso_op_kernel_quotientMap
    (F : Filtration.DecFiltration (C := C) X) (n : ℤ) :
    (dualDeligne (C := C) (X := X) F).gr (C := Cᵒᵖ) (X := Opposite.op X) n ≅
      Opposite.op
        (kernel
          (quotientMap (C := C) (X := X)
            (step_le_step_of_le (C := C) (X := X) F (show (1 - (n + 1)) ≤ (1 - n) by linarith)))) := by
  classical
  -- Notation for the relevant subobjects and inequality.
  let S₁ : Subobject X := F.step (1 - n)
  let S₂ : Subobject X := F.step (1 - (n + 1))
  let h : S₁ ≤ S₂ :=
    step_le_step_of_le (C := C) (X := X) F (show (1 - (n + 1)) ≤ (1 - n) by linarith)
  -- First, transport `succHom` along the `ObjIso`s to compare with `(quotientMap h).op`.
  have w :
      Filtration.DecFiltration.succHom (dualDeligne (C := C) (X := X) F) n ≫
          (quotientSubobjectObjIso (C := C) (X := X) S₁).hom =
        (quotientSubobjectObjIso (C := C) (X := X) S₂).hom ≫ (quotientMap (C := C) (X := X) h).op := by
    -- This is equivalent to the conjugation statement.
    have hc := dualDeligne_succHom_conj (C := C) (X := X) F n
    -- specialize `hc` to our `S₁ S₂ h`
    have hc' :
        (quotientSubobjectObjIso (C := C) (X := X) S₂).inv ≫
            Filtration.DecFiltration.succHom (dualDeligne (C := C) (X := X) F) n ≫
            (quotientSubobjectObjIso (C := C) (X := X) S₁).hom =
          (quotientMap (C := C) (X := X) h).op := by
      simpa [S₁, S₂, h] using hc
    -- rearrange
    calc
      Filtration.DecFiltration.succHom (dualDeligne (C := C) (X := X) F) n ≫
            (quotientSubobjectObjIso (C := C) (X := X) S₁).hom
          = (quotientSubobjectObjIso (C := C) (X := X) S₂).hom ≫
              ((quotientSubobjectObjIso (C := C) (X := X) S₂).inv ≫
                Filtration.DecFiltration.succHom (dualDeligne (C := C) (X := X) F) n ≫
                (quotientSubobjectObjIso (C := C) (X := X) S₁).hom) := by
                simp [Category.assoc]
      _ = (quotientSubobjectObjIso (C := C) (X := X) S₂).hom ≫
            (quotientMap (C := C) (X := X) h).op := by
              simp [Category.assoc, hc']
  -- Now compute `Gr` as a cokernel and use `cokernel.mapIso` to replace the defining morphism.
  dsimp [Filtration.DecFiltration.gr]
  refine (cokernel.mapIso
      (Filtration.DecFiltration.succHom (dualDeligne (C := C) (X := X) F) n)
      ((quotientMap (C := C) (X := X) h).op)
      (quotientSubobjectObjIso (C := C) (X := X) S₂)
      (quotientSubobjectObjIso (C := C) (X := X) S₁) ?_).trans ?_
  · -- commutativity for `cokernel.mapIso`
    simpa [Category.assoc] using w
  · -- Finally, `cokernel (f.op) ≅ (kernel f).op`.
    simpa using (cokernelOpOp (f := quotientMap (C := C) (X := X) h))

/-- Finiteness is preserved by Deligne dualization (Deligne (1.1.6)). -/
lemma IsFinite.dualDeligne {F : Filtration.DecFiltration (C := C) X}
    (hF : IsFinite (C := C) (X := X) F) :
    IsFinite (C := Cᵒᵖ) (X := Opposite.op X) (dualDeligne (C := C) (X := X) F) := by
  rcases hF with ⟨a, b, ha, hb⟩
  refine ⟨(1 - b), (1 - a), ?_, ?_⟩
  · intro n hn
    have : b ≤ (1 - n) := by linarith
    have hbot : F.step (1 - n) = ⊥ := hb (1 - n) this
    simp [dualDeligne_step, hbot, quotientSubobject_bot]
  · intro n hn
    have : (1 - n) ≤ a := by linarith
    have htop : F.step (1 - n) = ⊤ := ha (1 - n) this
    simp [dualDeligne_step, htop, quotientSubobject_top]

end Abelian

end DecFiltration
end Filtration

end CategoryTheory
