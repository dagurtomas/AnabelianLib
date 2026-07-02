/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import AnabelianLib.Framework.HomForm
public import Mathlib.CategoryTheory.Core


/-!
# Iso-form reconstruction packages

Iso-form anabelian statements reconstruct only isomorphisms.  The default package therefore works
on the groupoid cores of both the geometric category and the data category.  The invariant and
algorithm are profunctors; strict functorial invariants are handled by
`RepresentableIsoFormPackage`.
-/

@[expose] public section

universe u

namespace Anabelian

open CategoryTheory Opposite

variable {geom data : Type (u + 1)} [Category.{u} geom] [Category.{u} data]

/-- Iso-form reconstruction data in fully profunctorial form.

This is Hom-form reconstruction on the groupoid cores of the geometric and data categories. -/
abbrev IsoFormPackage
    (geom : Type (u + 1)) (data : Type (u + 1)) [Category.{u} geom] [Category.{u} data] :=
  HomFormPackage (Core geom) (Core data)

namespace IsoFormPackage

variable (P : IsoFormPackage geom data)

/-- The Iso-form reconstruction isomorphism, as an alias for `HomFormPackage.homIso`. -/
abbrev isoIso :
    P.invariant.comp.{u + 1} P.algorithm ≅ CategoryTheory.Profunctor.id.ulift1 :=
  P.homIso

/-- The associated profunctor reconstruction theorem on groupoid cores. -/
noncomputable abbrev toReconstruction : ProfunctorReconstruction (Core geom) (Core data) :=
  HomFormPackage.toReconstruction P

end IsoFormPackage

/-- Iso-form reconstruction data for a strict covariant invariant functor on groupoid cores.

This is representable Hom-form reconstruction on the groupoid cores of the geometric and data
categories. -/
abbrev RepresentableIsoFormPackage
    (geom : Type (u + 1)) (data : Type (u + 1)) [Category.{u} geom] [Category.{u} data] :=
  RepresentableHomFormPackage (Core geom) (Core data)

namespace RepresentableIsoFormPackage

variable (P : RepresentableIsoFormPackage geom data)

/-- The objectwise Iso-form theorem, as an alias for `RepresentableHomFormPackage.homEquiv`. -/
abbrev isoEquiv : ∀ X Y : Core geom, (Y ⟶ X) ≃ (P.I.obj Y ⟶ P.I.obj X) :=
  P.homEquiv

/-- The forward direction of the objectwise Iso-form theorem is induced by the invariant functor. -/
theorem isoEquiv_apply {X Y : Core geom} (f : Y ⟶ X) :
    P.isoEquiv X Y f = P.I.map f :=
  P.homEquiv_apply f

/-- View a representable Iso-form package as a representable Hom-form package on cores. -/
abbrev toRepresentableHomFormPackage : RepresentableHomFormPackage (Core geom) (Core data) :=
  P

/-- The strict-functor Iso-form package as a profunctor-first Iso-form package. -/
noncomputable abbrev toIsoFormPackage : IsoFormPackage geom data :=
  P.toHomFormPackage

variable {geom' : Type (u + 1)} [Category.{u} geom']

/--
The invariant profunctor obtained from a representable Iso-form package by replacing the geometric
category along a functor `G : geom' ⥤ geom`.
-/
abbrev invariantThroughGeom (G : geom' ⥤ geom) :
    CategoryTheory.Profunctor.{u + 1} (Core geom') (Core data) :=
  P.toRepresentableHomFormPackage.invariantThroughGeom G.core

/--
The algorithm profunctor obtained from a representable Iso-form package by replacing the geometric
category along a functor `G : geom' ⥤ geom`.
-/
abbrev algorithmThroughGeom (G : geom' ⥤ geom) :
    CategoryTheory.Profunctor.{u + 1} (Core data) (Core geom') :=
  P.toRepresentableHomFormPackage.algorithmThroughGeom G.core

/--
The objectwise Iso-form theorem as an isomorphism from data-Homs of the composed invariant to
isomorphisms between the presented geometric objects.
-/
noncomputable abbrev dataHomToGeomDataHomIso (G : geom' ⥤ geom) :
    (G.core ⋙ P.I).imageHomProfunctor ≅ G.core.imageHomProfunctor :=
  P.toRepresentableHomFormPackage.dataHomToGeomDataHomIso G.core

/--
A reconstruction theorem for a presented geometric category.

For an arbitrary functor `G : geom' ⥤ geom`, this reconstructs isomorphisms between the images
`G.obj Y ≅ G.obj X` rather than morphisms in `geom'`.
-/
noncomputable abbrev toGeomPresentationReconstruction (G : geom' ⥤ geom) :
    ProfunctorReconstruction (Core geom') (Core data) :=
  P.toRepresentableHomFormPackage.toGeomPresentationReconstruction G.core

/--
Pull a representable Iso-form package back along a functor whose induced functor on cores is full
and faithful.
-/
noncomputable abbrev representableThroughGeom (G : geom' ⥤ geom)
    [G.core.Full] [G.core.Faithful] : RepresentableIsoFormPackage geom' data :=
  P.toRepresentableHomFormPackage.representableThroughGeom G.core

/--
Turn a representable Iso-form package into a profunctor-first package after replacing the geometric
category along a functor whose induced functor on cores is full and faithful.
-/
noncomputable abbrev toIsoFormPackageThroughGeom (G : geom' ⥤ geom)
    [G.core.Full] [G.core.Faithful] : IsoFormPackage geom' data :=
  (P.representableThroughGeom G).toIsoFormPackage

variable {data' : Type (u + 1)} [Category.{u} data']

/--
The invariant profunctor obtained from a representable Iso-form package by replacing the data
category along a functor `F : data' ⥤ data`.
-/
abbrev invariantThrough (F : data' ⥤ data) :
    CategoryTheory.Profunctor.{u + 1} (Core geom) (Core data') :=
  P.toRepresentableHomFormPackage.invariantThrough F.core

/--
The algorithm profunctor obtained from a representable Iso-form package by replacing the data
category along a functor `F : data' ⥤ data`.
-/
abbrev algorithmThrough (F : data' ⥤ data) :
    CategoryTheory.Profunctor.{u + 1} (Core data') (Core geom) :=
  P.toRepresentableHomFormPackage.algorithmThrough F.core

/-- The invariant profunctor after replacing both geometric and data categories. -/
abbrev invariantThroughGeomData (G : geom' ⥤ geom) (F : data' ⥤ data) :
    CategoryTheory.Profunctor.{u + 1} (Core geom') (Core data') :=
  P.toRepresentableHomFormPackage.invariantThroughGeomData G.core F.core

/-- The algorithm profunctor after replacing both geometric and data categories. -/
abbrev algorithmThroughGeomData (G : geom' ⥤ geom) (F : data' ⥤ data) :
    CategoryTheory.Profunctor.{u + 1} (Core data') (Core geom') :=
  P.toRepresentableHomFormPackage.algorithmThroughGeomData G.core F.core

/--
A reconstruction theorem for a presented geometric category and a full essentially-surjective
presentation of the data category.
-/
noncomputable abbrev toGeomPresentationReconstructionThrough (G : geom' ⥤ geom)
    (F : data' ⥤ data) [F.core.Full] [F.core.EssSurj] :
    ProfunctorReconstruction (Core geom') (Core data') :=
  P.toRepresentableHomFormPackage.toGeomPresentationReconstructionThrough G.core F.core

/--
Turn a representable Iso-form package with data category `data` into a profunctor-first Iso-form
package with data category `data'`, along a functor whose induced functor on cores is full and
essentially surjective.
-/
noncomputable abbrev toIsoFormPackageThrough (F : data' ⥤ data)
    [F.core.Full] [F.core.EssSurj] : IsoFormPackage geom data' :=
  P.toRepresentableHomFormPackage.toHomFormPackageThrough F.core

/-- The associated profunctor reconstruction theorem on groupoid cores. -/
noncomputable abbrev toReconstruction : ProfunctorReconstruction (Core geom) (Core data) :=
  P.toIsoFormPackage.toReconstruction

end RepresentableIsoFormPackage

end Anabelian
