/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import AnabelianLib.Framework.Reconstruction
public import AnabelianLib.Mathlib.CategoryTheory.Profunctor.CompIso
public import AnabelianLib.Mathlib.CategoryTheory.Profunctor.CoYoneda


/-!
# Hom-form reconstruction packages

The primary Hom-form package is the data of a profunctor `invariant` and `algorithm`
in opposite directions, reconstruct the identity Hom profunctor.
Strict covariant invariant functors are a representable special case, packaged separately by
`RepresentableHomFormPackage`.
-/

@[expose] public section

universe w u

namespace Anabelian

open CategoryTheory Opposite

variable {geom data : Type (u + 1)} [Category.{u} geom] [Category.{u} data]

/-- Evaluation of the explicit Type-valued chosen-coend map on a quotient representative. -/
lemma chosenCoendMap_mk {J : Type (u + 1)} [Category.{u} J]
    {F G : Jᵒᵖ ⥤ J ⥤ Type (max w (u + 1))} (α : F ⟶ G) (j : J)
    (x : (F.obj (Opposite.op j)).obj j) :
    (ConcreteCategory.hom (CategoryTheory.Limits.chosenCoend.map α)) (Quot.mk _ ⟨j, x⟩) =
      Quot.mk _ ⟨j, (α.app (Opposite.op j)).app j x⟩ := by
  rfl

/-- Hom-form reconstruction data. -/
structure HomFormPackage
    (geom : Type (u + 1)) (data : Type (u + 1)) [Category.{u} geom] [Category.{u} data] where
  /-- The "invariant" profunctor. -/
  invariant : Profunctor.{u + 1} geom data
  /-- The reconstruction algorithm. -/
  algorithm : Profunctor.{u + 1} data geom
  /-- The Hom-form reconstruction isomorphism. -/
  homIso : invariant.comp.{u + 1} algorithm ≅ Profunctor.id.ulift1

namespace HomFormPackage

variable (P : HomFormPackage geom data)

/-- A Hom-form package as a general profunctor reconstruction theorem. -/
noncomputable def toReconstruction : ProfunctorReconstruction geom data where
  invariant := P.invariant
  target := Profunctor.id.ulift1
  algorithm := P.algorithm
  decodeIso := P.homIso

end HomFormPackage

/-- Hom-form reconstruction data for a strict covariant invariant functor. -/
structure RepresentableHomFormPackage
    (geom : Type (u + 1)) (data : Type (u + 1)) [Category.{u} geom] [Category.{u} data] where
  /-- The strict covariant invariant functor. -/
  I : geom ⥤ data
  /-- The objectwise Hom-form theorem. -/
  homEquiv : ∀ X Y : geom, (Y ⟶ X) ≃ (I.obj Y ⟶ I.obj X)
  /--
  The forward direction of the objectwise Hom-form theorem is the canonical map induced by the
  invariant functor.
  -/
  homEquiv_apply : ∀ {X Y : geom} (f : Y ⟶ X), homEquiv X Y f = I.map f

namespace RepresentableHomFormPackage

variable (P : RepresentableHomFormPackage geom data)

/-- Naturality in the reconstructed target variable, derived from `homEquiv_apply`. -/
theorem natural_left {X X' Y : geom} (f : Y ⟶ X) (g : X ⟶ X') :
    P.homEquiv X' Y (f ≫ g) = P.homEquiv X Y f ≫ P.I.map g := by
  simp [P.homEquiv_apply]

/-- Naturality in the reconstructed source variable, derived from `homEquiv_apply`. -/
theorem natural_right {X Y Y' : geom} (f : Y ⟶ X) (g : Y' ⟶ Y) :
    P.homEquiv X Y' (g ≫ f) = P.I.map g ≫ P.homEquiv X Y f := by
  simp [P.homEquiv_apply]

/-- The invariant profunctor represented by `P.I`. -/
abbrev invariant : Profunctor.{u + 1} geom data :=
  representedInvariant P.I

/-- The canonical Hom-form algorithm: data morphisms out of the invariant object. -/
abbrev algorithm : Profunctor.{u + 1} data geom :=
  representedAlgorithm P.I

/-- The image-Hom profunctor associated to `P.I`. -/
abbrev dataHom : Profunctor.{u + 1} geom geom :=
  P.I.imageHomProfunctor

/-- The objectwise Hom-form theorem as an isomorphism of profunctors. -/
noncomputable def dataHomToIdIso : P.dataHom ≅ Profunctor.id.ulift1 :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ {
    hom := ↾fun a ↦ ULift.up ((P.homEquiv X Y.unop).symm a.down)
    inv := ↾fun f ↦ ULift.up (P.homEquiv X Y.unop f.down)
    hom_inv_id := by
      ext a
      exact congrArg ULift.up ((P.homEquiv X Y.unop).apply_symm_apply a.down)
    inv_hom_id := by
      ext f
      exact congrArg ULift.up ((P.homEquiv X Y.unop).symm_apply_apply f.down) })
    (fun {Y Y'} g ↦ by
      ext a
      rcases a with ⟨a⟩
      simp only [Profunctor.ulift_obj_map, Functor.imageHomProfunctor_obj_map,
        Profunctor.id_obj_map]
      apply congr_arg ULift.up
      change (P.homEquiv X Y'.unop).symm (P.I.map g.unop ≫ a) =
        g.unop ≫ (P.homEquiv X Y.unop).symm a
      rw [Equiv.symm_apply_eq]
      simpa using (P.natural_right ((P.homEquiv X Y.unop).symm a) g.unop).symm))
    (fun {X X'} g ↦ by
      ext Y a
      rcases a with ⟨a⟩
      simp only [CategoryTheory.NatTrans.comp_app, Profunctor.ulift_map_app,
        Functor.imageHomProfunctor_map_app, Profunctor.id_map_app]
      apply congr_arg ULift.up
      change (P.homEquiv X' Y.unop).symm (a ≫ P.I.map g) =
        (P.homEquiv X Y.unop).symm a ≫ g
      rw [Equiv.symm_apply_eq]
      simpa using (P.natural_left ((P.homEquiv X Y.unop).symm a) g).symm)

/-- The strict-functor Hom-form package as a profunctor Hom-form package. -/
noncomputable def toHomFormPackage : HomFormPackage geom data where
  invariant := P.invariant
  algorithm := P.algorithm
  homIso := P.I.profunctorCoYonedaIso ≪≫ P.dataHomToIdIso

variable {geom' : Type (u + 1)} [Category.{u} geom']

/--
The invariant profunctor obtained by precomposing the geometric category with
`G : geom' ⥤ geom`.
-/
abbrev invariantThroughGeomFunctor (I : geom ⥤ data) (G : geom' ⥤ geom) :
    Profunctor.{u + 1} geom' data :=
  representedInvariant (G ⋙ I)

/--
The algorithm profunctor obtained by precomposing the geometric category with
`G : geom' ⥤ geom`.
-/
abbrev algorithmThroughGeomFunctor (I : geom ⥤ data) (G : geom' ⥤ geom) :
    Profunctor.{u + 1} data geom' :=
  representedAlgorithm (G ⋙ I)

/-- The invariant profunctor after replacing the geometric category along `G : geom' ⥤ geom`. -/
abbrev invariantThroughGeom (G : geom' ⥤ geom) :
    Profunctor.{u + 1} geom' data :=
  invariantThroughGeomFunctor P.I G

/-- The algorithm profunctor after replacing the geometric category along `G : geom' ⥤ geom`. -/
abbrev algorithmThroughGeom (G : geom' ⥤ geom) :
    Profunctor.{u + 1} data geom' :=
  algorithmThroughGeomFunctor P.I G

/--
The objectwise Hom-form theorem as an isomorphism from data-Homs of the composed invariant to
morphisms between the presented geometric objects.
-/
noncomputable def dataHomToGeomDataHomIso (G : geom' ⥤ geom) :
    (G ⋙ P.I).imageHomProfunctor ≅ G.imageHomProfunctor :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ {
    hom := ↾fun a ↦ ULift.up ((P.homEquiv (G.obj X) (G.obj Y.unop)).symm a.down)
    inv := ↾fun f ↦ ULift.up (P.homEquiv (G.obj X) (G.obj Y.unop) f.down)
    hom_inv_id := by
      ext a
      exact congrArg ULift.up ((P.homEquiv (G.obj X) (G.obj Y.unop)).apply_symm_apply a.down)
    inv_hom_id := by
      ext f
      exact congrArg ULift.up ((P.homEquiv (G.obj X) (G.obj Y.unop)).symm_apply_apply f.down) })
    (fun {Y Y'} g ↦ by
      ext a
      rcases a with ⟨a⟩
      simp only [Functor.imageHomProfunctor_obj_map]
      apply congr_arg ULift.up
      change (P.homEquiv (G.obj X) (G.obj Y'.unop)).symm (P.I.map (G.map g.unop) ≫ a) =
        G.map g.unop ≫ (P.homEquiv (G.obj X) (G.obj Y.unop)).symm a
      rw [Equiv.symm_apply_eq]
      simpa using (P.natural_right ((P.homEquiv (G.obj X) (G.obj Y.unop)).symm a)
        (G.map g.unop)).symm))
    (fun {X X'} g ↦ by
      ext Y a
      rcases a with ⟨a⟩
      simp only [CategoryTheory.NatTrans.comp_app, Functor.imageHomProfunctor_map_app]
      apply congr_arg ULift.up
      change (P.homEquiv (G.obj X') (G.obj Y.unop)).symm (a ≫ P.I.map (G.map g)) =
        (P.homEquiv (G.obj X) (G.obj Y.unop)).symm a ≫ G.map g
      rw [Equiv.symm_apply_eq]
      have h := (P.natural_left ((P.homEquiv (G.obj X) (G.obj Y.unop)).symm a)
        (G.map g)).symm
      rw [Equiv.apply_symm_apply] at h
      exact h)

/--
A reconstruction theorem for a presented geometric category.

For an arbitrary functor `G : geom' ⥤ geom`, this reconstructs morphisms between the images
`G.obj Y ⟶ G.obj X`.  If `G` is fully faithful, this target can be identified with the ordinary
Hom profunctor on `geom'`.
-/
noncomputable def toGeomPresentationReconstruction (G : geom' ⥤ geom) :
    ProfunctorReconstruction geom' data where
  invariant := P.invariantThroughGeom G
  target := G.imageHomProfunctor
  algorithm := P.algorithmThroughGeom G
  decodeIso := (G ⋙ P.I).profunctorCoYonedaIso ≪≫ P.dataHomToGeomDataHomIso G

/--
Pull a representable Hom-form package back along a full faithful functor on geometric categories.

The full-faithfulness condition identifies morphisms in `geom'` with morphisms between their images
in `geom`; the already-normalized objectwise Hom-form equivalence then gives the new package.
-/
noncomputable def representableThroughGeom (G : geom' ⥤ geom) [G.Full] [G.Faithful] :
    RepresentableHomFormPackage geom' data where
  I := G ⋙ P.I
  homEquiv X Y := (Functor.FullyFaithful.ofFullyFaithful G).homEquiv.trans
    (P.homEquiv (G.obj X) (G.obj Y))
  homEquiv_apply f := P.homEquiv_apply (G.map f)

/--
Turn a representable Hom-form package into a profunctor Hom-form package after replacing the
geometric category along a full faithful functor `G : geom' ⥤ geom`.
-/
noncomputable def toHomFormPackageThroughGeom (G : geom' ⥤ geom) [G.Full] [G.Faithful] :
    HomFormPackage geom' data :=
  (P.representableThroughGeom G).toHomFormPackage

variable {data' : Type (u + 1)} [Category.{u} data']

/--
The invariant profunctor obtained from a functorial invariant after replacing the data category by a
category mapping to it.

It is the composite of the represented invariant with the profunctor represented by
`F : data' ⥤ data` in the algorithm direction.  Informally, it encodes maps
`F.obj d' ⟶ I.obj X`.
-/
abbrev invariantThroughFunctor (I : geom ⥤ data) (F : data' ⥤ data) :
    Profunctor.{u + 1} geom data' :=
  (representedInvariant I).comp.{u + 1} (representedAlgorithm F)

/--
The algorithm profunctor obtained from a functorial invariant after replacing the data category by a
category mapping to it.

It is the composite of the profunctor represented by `F : data' ⥤ data` in the invariant direction
with the represented algorithm of `I`.  Informally, it encodes maps `I.obj Y ⟶ F.obj d'`.
-/
abbrev algorithmThroughFunctor (I : geom ⥤ data) (F : data' ⥤ data) :
    Profunctor.{u + 1} data' geom :=
  (representedInvariant F).comp.{u + 1} (representedAlgorithm I)

/--
The invariant profunctor obtained from a representable invariant after replacing the data category
by a category mapping to it.
-/
abbrev invariantThrough (F : data' ⥤ data) : Profunctor.{u + 1} geom data' :=
  invariantThroughFunctor P.I F

/--
The algorithm profunctor obtained from a representable invariant after replacing the data category
by a category mapping to it.
-/
abbrev algorithmThrough (F : data' ⥤ data) : Profunctor.{u + 1} data' geom :=
  algorithmThroughFunctor P.I F

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
The density/co-Yoneda isomorphism for a full essentially-surjective functor.

It identifies factorizations `Y ⟶ F d' ⟶ X`, modulo the coend relation over `data'`, with ordinary
morphisms `Y ⟶ X` in `data`.
-/
noncomputable def fullEssSurjDensityIso (F : data' ⥤ data) [F.Full] [F.EssSurj] :
    (representedAlgorithm F).comp.{u + 1} (representedInvariant F) ≅
      (Profunctor.id (C := data)).ulift1 := by
  refine NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ ?_) ?_) ?_
  · refine {
      hom := ?_,
      inv := ?_,
      hom_inv_id := ?_,
      inv_hom_id := ?_ }
    · refine ↾ Quot.lift ?_ ?_
      · intro z
        exact ULift.up (z.2.2.down ≫ z.2.1.down)
      · intro z z' h
        cases h with
        | mk f x =>
          rcases x with ⟨a, b⟩
          change ULift.{u + 1, u} (F.obj _ ⟶ X) at a
          change ULift.{u + 1, u} (Y.unop ⟶ F.obj _) at b
          dsimp at a b
          dsimp [Profunctor.compDiagram]
          rw [Category.assoc]
    · exact ↾fun h ↦
        let A := F.objPreimage Y.unop
        let e := F.objObjPreimageIso Y.unop
        Quot.mk _ ⟨A, (ULift.up (e.hom ≫ h.down), ULift.up e.inv)⟩
    · ext z
      induction z using Quot.inductionOn with
      | h z =>
        rcases z with ⟨A, a, b⟩
        change ULift.{u + 1, u} (F.obj A ⟶ X) at a
        change ULift.{u + 1, u} (Y.unop ⟶ F.obj A) at b
        change Quot.mk
          (CategoryTheory.Limits.Types.coendRel
            ((representedAlgorithm F).compDiagram (representedInvariant F) X Y.unop))
          ⟨F.objPreimage Y.unop,
            (ULift.up ((F.objObjPreimageIso Y.unop).hom ≫ b.down ≫ a.down),
              ULift.up (F.objObjPreimageIso Y.unop).inv)⟩ =
          Quot.mk
            (CategoryTheory.Limits.Types.coendRel
              ((representedAlgorithm F).compDiagram (representedInvariant F) X Y.unop))
            ⟨A, (a, b)⟩
        apply Quot.sound
        rw [CategoryTheory.Limits.Types.coendRel_iff]
        let e := F.objObjPreimageIso Y.unop
        let f : F.objPreimage Y.unop ⟶ A := F.preimage (e.hom ≫ b.down)
        refine ⟨f, (a, ULift.up e.inv), ?_, ?_⟩
        · dsimp [Profunctor.compDiagram]
          change (ULift.up (F.map f ≫ a.down), ULift.up e.inv) =
            (ULift.up (e.hom ≫ b.down ≫ a.down), ULift.up e.inv)
          apply Prod.ext
          · apply congrArg ULift.up
            rw [F.map_preimage]
            simp [e]
          · rfl
        · dsimp [Profunctor.compDiagram]
          apply Prod.ext
          · rfl
          · apply congrArg ULift.up
            rw [F.map_preimage]
            simp [e]
    · ext h
      rcases h with ⟨h⟩
      simp
  · intro Y Y' g
    ext z
    induction z using Quot.inductionOn with
    | h z =>
      rcases z with ⟨A, a, b⟩
      change ULift.{u + 1, u} (F.obj A ⟶ X) at a
      change ULift.{u + 1, u} (Y.unop ⟶ F.obj A) at b
      simp only [Profunctor.ulift_obj_map, Profunctor.id_obj_map,
        Profunctor.comp_obj_map]
      dsimp
      rw [chosenCoendMap_mk]
      dsimp [Profunctor.compDiagramMap, Profunctor.compDiagram]
      rcases a with ⟨a⟩
      rcases b with ⟨b⟩
      simp
  · intro X X' g
    ext Y z
    induction z using Quot.inductionOn with
    | h z =>
      rcases z with ⟨A, a, b⟩
      change ULift.{u + 1, u} (F.obj A ⟶ X) at a
      change ULift.{u + 1, u} (Y.unop ⟶ F.obj A) at b
      simp only [CategoryTheory.NatTrans.comp_app, Profunctor.ulift_map_app,
        Profunctor.id_map_app, Profunctor.comp_map_app]
      dsimp
      rw [chosenCoendMap_mk]
      dsimp [Profunctor.compDiagramMap, Profunctor.compDiagram]
      rcases a with ⟨a⟩
      rcases b with ⟨b⟩
      simp

/--
The co-Yoneda comparison for replacing the data category by a full essentially-surjective
presentation `F : data' ⥤ data`.
-/
noncomputable def coYonedaDataHomIsoThroughFunctor (I : geom ⥤ data) (F : data' ⥤ data)
    [F.Full] [F.EssSurj] :
    (invariantThroughFunctor I F).comp.{u + 1} (algorithmThroughFunctor I F) ≅
      I.imageHomProfunctor := by
  let A := representedInvariant I
  let B := representedAlgorithm F
  let C := representedInvariant F
  let D := representedAlgorithm I
  exact
    (A.associator B (C.comp D)) ≪≫
    Profunctor.whiskerLeftIso A (B.associator C D).symm ≪≫
    (A.associator (B.comp C) D).symm ≪≫
    Profunctor.whiskerRightIso D (Profunctor.whiskerLeftIso A (fullEssSurjDensityIso F)) ≪≫
    Profunctor.whiskerRightIso D (Profunctor.rightUnitorUlift A) ≪≫
    I.profunctorCoYonedaIso

/--
The invariant profunctor after replacing both the geometric category and the data category.
-/
abbrev invariantThroughGeomDataFunctor (I : geom ⥤ data) (G : geom' ⥤ geom)
    (F : data' ⥤ data) : Profunctor.{u + 1} geom' data' :=
  invariantThroughFunctor (G ⋙ I) F

/--
The algorithm profunctor after replacing both the geometric category and the data category.
-/
abbrev algorithmThroughGeomDataFunctor (I : geom ⥤ data) (G : geom' ⥤ geom)
    (F : data' ⥤ data) : Profunctor.{u + 1} data' geom' :=
  algorithmThroughFunctor (G ⋙ I) F

/-- The invariant profunctor after replacing both geometric and data categories. -/
abbrev invariantThroughGeomData (G : geom' ⥤ geom) (F : data' ⥤ data) :
    Profunctor.{u + 1} geom' data' :=
  invariantThroughGeomDataFunctor P.I G F

/-- The algorithm profunctor after replacing both geometric and data categories. -/
abbrev algorithmThroughGeomData (G : geom' ⥤ geom) (F : data' ⥤ data) :
    Profunctor.{u + 1} data' geom' :=
  algorithmThroughGeomDataFunctor P.I G F

/--
A reconstruction theorem for a presented geometric category and a full essentially-surjective
presentation of the data category.

The target remains the pulled-back geometric Hom profunctor `G.imageHomProfunctor`.
-/
noncomputable def toGeomPresentationReconstructionThrough (G : geom' ⥤ geom)
    (F : data' ⥤ data) [F.Full] [F.EssSurj] : ProfunctorReconstruction geom' data' where
  invariant := P.invariantThroughGeomData G F
  target := G.imageHomProfunctor
  algorithm := P.algorithmThroughGeomData G F
  decodeIso := coYonedaDataHomIsoThroughFunctor (G ⋙ P.I) F ≪≫ P.dataHomToGeomDataHomIso G

/--
Turn a representable Hom-form package with data category `data` into a profunctor Hom-form
package with data category `data'`, along a full essentially-surjective functor
`F : data' ⥤ data`.
-/
noncomputable def toHomFormPackageThrough (F : data' ⥤ data) [F.Full] [F.EssSurj] :
    HomFormPackage geom data' where
  invariant := P.invariantThrough F
  algorithm := P.algorithmThrough F
  homIso := coYonedaDataHomIsoThroughFunctor P.I F ≪≫ P.dataHomToIdIso

/-- The associated general profunctor reconstruction theorem. -/
noncomputable def toReconstruction : ProfunctorReconstruction geom data :=
  P.toHomFormPackage.toReconstruction

end RepresentableHomFormPackage

end Anabelian
