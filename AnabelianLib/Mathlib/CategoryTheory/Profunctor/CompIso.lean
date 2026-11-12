/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Profunctor.Comp


/-!
# Isomorphisms for profunctor composition

This file contains small isomorphism-level helpers for the profunctor composition developed in
`Mathlib.CategoryTheory.Profunctor.Comp`.
-/

@[expose] public section

universe w u

open Opposite

namespace CategoryTheory

namespace Profunctor

section WhiskerIso

variable {C D E : Type u} [Category* C] [Category* D] [Category* E]

/-- Whisker an isomorphism of profunctors on the left. -/
noncomputable def whiskerLeftIso (P : Profunctor.{max u w} C D)
    {Q R : Profunctor.{max u w} D E} (e : Q ≅ R) : P.comp Q ≅ P.comp R where
  hom := P.whiskerLeft e.hom
  inv := P.whiskerLeft e.inv
  hom_inv_id := by simp [← Profunctor.whiskerLeft_comp]
  inv_hom_id := by simp [← Profunctor.whiskerLeft_comp]

/-- Whisker an isomorphism of profunctors on the right. -/
noncomputable def whiskerRightIso {P Q : Profunctor.{max u w} C D}
    (R : Profunctor.{max u w} D E) (e : P ≅ Q) : P.comp R ≅ Q.comp R where
  hom := Profunctor.whiskerRight R e.hom
  inv := Profunctor.whiskerRight R e.inv
  hom_inv_id := by simp [← Profunctor.comp_whiskerRight]
  inv_hom_id := by simp [← Profunctor.comp_whiskerRight]

end WhiskerIso

section RightUnitorUlift

variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The right unitor for composition with the universe-lifted identity profunctor. -/
noncomputable def rightUnitorUlift (P : Profunctor.{u + 1} C D) :
    P.comp.{u + 1} (Profunctor.id (C := D)).ulift1 ≅ P :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ {
    hom := ↾Quot.lift (fun ⟨d, x, f⟩ ↦ (P.obj X).map f.down.op x) fun _ _ h ↦ by
      cases h
      simp [Profunctor.compDiagram]
    inv := ↾fun x ↦ Quot.mk _ ⟨Y.unop, x, ULift.up (𝟙 Y.unop)⟩
    hom_inv_id := by
      ext z
      induction z using Quot.inductionOn with
      | h z =>
        rcases z with ⟨d, x, f⟩
        rcases f with ⟨f⟩
        change Y.unop ⟶ d at f
        apply Quot.sound
        rw [CategoryTheory.Limits.Types.coendRel_iff]
        refine ⟨f, ⟨x, ULift.up (𝟙 Y.unop)⟩, ?_, ?_⟩
        · rfl
        · apply Prod.ext
          · rfl
          · apply congrArg ULift.up
            simp
    inv_hom_id := by
      ext x
      simp [CategoryTheory.Limits.Types.chosenCoend_def] })
    (fun f ↦ by
      dsimp
      ext
      simp [Profunctor.compDiagram, CategoryTheory.Limits.chosenCoend.ι_apply _]))
    (fun f ↦ by
      ext _ ⟨_, _⟩
      simp [CategoryTheory.Limits.Types.chosenCoend_def,
        CategoryTheory.Limits.chosenCoend.map_apply])

end RightUnitorUlift

end Profunctor

end CategoryTheory
