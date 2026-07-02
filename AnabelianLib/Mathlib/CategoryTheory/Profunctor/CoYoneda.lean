/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

import AnabelianLib.Mathlib.CategoryTheory.Profunctor.Comp


/-!
# Co-Yoneda for profunctor composition

This file records the co-Yoneda isomorphism for the profunctors represented by a functor
`F : C ⥤ D`. The composite of `F.toProfunctor.ulift1` and `F.toProfunctorRev.ulift1` is the
profunctor of morphisms between the images of objects under `F`.
-/


universe w u

open Opposite

namespace CategoryTheory

/-- Evaluation of the explicit Type-valued chosen-coend map on a quotient representative. -/
private lemma chosenCoendMap_mk {J : Type (u + 1)} [Category.{u} J]
    {F G : Jᵒᵖ ⥤ J ⥤ Type (max w (u + 1))} (α : F ⟶ G) (j : J)
    (x : (F.obj (Opposite.op j)).obj j) :
    (ConcreteCategory.hom (Limits.chosenCoend.map α)) (Quot.mk _ ⟨j, x⟩) =
      Quot.mk _ ⟨j, (α.app (Opposite.op j)).app j x⟩ := by
  simp [Limits.Types.chosenCoend_def, Limits.chosenCoend.map_apply]

namespace Functor

variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]

/--
The profunctor of morphisms between the images of objects under a functor.

At `(X, Y)` it is the universe lift of `F.obj Y ⟶ F.obj X`.
-/
@[simps! +dsimpLhs obj_obj obj_map map_app]
def imageHomProfunctor (F : C ⥤ D) : Profunctor.{u + 1} C C :=
  .ofCore {
    obj X Y := ULift.{u + 1, u} (F.obj Y ⟶ F.obj X)
    map f g := ↾fun a ↦ ULift.up (F.map g ≫ a.down ≫ F.map f) }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
The co-Yoneda isomorphism for a functor represented as profunctors.

The composite has representatives `F.obj Y ⟶ d ⟶ F.obj X`, modulo the coend relation, and this
isomorphism sends a representative to its composite in `D`.
-/
noncomputable def profunctorCoYonedaIso (F : C ⥤ D) :
    F.toProfunctor.ulift1.comp.{u + 1} F.toProfunctorRev.ulift1 ≅ F.imageHomProfunctor :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ {
    hom := ↾ Quot.lift
      (fun z : (d : D) ×
          (((F.toProfunctor.ulift1).obj X).obj (Opposite.op d) ×
            (((F.toProfunctorRev.ulift1).obj d).obj Y)) ↦
        ULift.up (z.2.2.down ≫ z.2.1.down))
      (fun z z' h ↦ by
        cases h with
        | mk f x =>
          rcases x with ⟨a, b⟩
          change ULift.{u + 1, u} (_ ⟶ F.obj X) at a
          change ULift.{u + 1, u} (F.obj Y.unop ⟶ _) at b
          dsimp at a b
          dsimp [Profunctor.compDiagram]
          rw [Category.assoc])
    inv := ↾fun a ↦
      Quot.mk _ ⟨F.obj X, (ULift.up (𝟙 _), ULift.up a.down)⟩
    hom_inv_id := by
      ext z
      induction z using Quot.inductionOn with
      | h z =>
        rcases z with ⟨d, a, b⟩
        change ULift.{u + 1, u} (d ⟶ F.obj X) at a
        change ULift.{u + 1, u} (F.obj Y.unop ⟶ d) at b
        change Quot.mk
          (Limits.Types.coendRel
            ((F.toProfunctor.ulift1).compDiagram (F.toProfunctorRev.ulift1) X Y.unop))
          ⟨F.obj X, (ULift.up (𝟙 (F.obj X)), ULift.up (b.down ≫ a.down))⟩ =
            Quot.mk
              (Limits.Types.coendRel
                ((F.toProfunctor.ulift1).compDiagram (F.toProfunctorRev.ulift1) X Y.unop))
              ⟨d, (a, b)⟩
        symm
        apply Quot.sound
        rw [Limits.Types.coendRel_iff]
        refine ⟨a.down, (ULift.up (𝟙 _), b), ?_, ?_⟩
        · dsimp [Profunctor.compDiagram]
          apply Prod.ext
          · rcases a with ⟨a⟩
            exact congr_arg ULift.up (Category.comp_id a)
          · rfl
        · dsimp [Profunctor.compDiagram]
    inv_hom_id := by
      ext a
      rcases a with ⟨a⟩
      simp })
    (by
      intro Y Y' g
      ext z
      induction z using Quot.inductionOn with
      | h z =>
        rcases z with ⟨d, a, b⟩
        change ULift.{u + 1, u} (d ⟶ F.obj X) at a
        change ULift.{u + 1, u} (F.obj Y.unop ⟶ d) at b
        simp only [Profunctor.comp_obj_map, imageHomProfunctor_obj_map]
        dsimp
        rw [chosenCoendMap_mk]
        dsimp [Profunctor.compDiagramMap, Profunctor.compDiagram]
        simp))
    (by
      intro X X' f
      ext Y z
      induction z using Quot.inductionOn with
      | h z =>
        rcases z with ⟨d, a, b⟩
        change ULift.{u + 1, u} (d ⟶ F.obj X) at a
        change ULift.{u + 1, u} (F.obj Y.unop ⟶ d) at b
        simp only [CategoryTheory.NatTrans.comp_app, Profunctor.comp_map_app,
          imageHomProfunctor_map_app]
        dsimp
        rw [chosenCoendMap_mk]
        dsimp [Profunctor.compDiagramMap, Profunctor.compDiagram]
        simp)

end Functor

end CategoryTheory
