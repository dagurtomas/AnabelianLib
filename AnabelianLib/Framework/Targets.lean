/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

import AnabelianLib.Framework.Reconstruction
import Mathlib.CategoryTheory.PUnit


/-!
# Alternative target profunctors

This file contains lightweight target packages for reconstruction statements whose target is not the
identity Hom profunctor.  Sub-Hom targets require stability under all pre- and postcomposition maps
in the ambient category; for properties such as dominance, this usually means the ambient category
should already have the right morphisms.
-/


universe v u

namespace Anabelian

open CategoryTheory Opposite

variable {geom : Type (u + 1)} [Category.{u} geom]

/-- A composition-stable sub-Hom target profunctor. -/
structure HomSubtarget (geom : Type (u + 1)) [Category.{u} geom] where
  /-- The geometric morphisms included in the target. -/
  Good : ∀ {Y X : geom}, (Y ⟶ X) → Prop
  /-- Stability under the profunctorial left and right actions. -/
  map_good : ∀ {X X' Y Y' : geom} (f : X ⟶ X') (g : Y ⟶ Y') {h : Y' ⟶ X},
    Good h → Good (g ≫ h ≫ f)

namespace HomSubtarget

variable (T : HomSubtarget geom)

/-- The profunctor of morphisms satisfying a stable sub-Hom condition. -/
@[simps! +dsimpLhs obj_obj obj_map map_app]
def profunctor : CategoryTheory.Profunctor.{u + 1} geom geom :=
  .ofCore {
    obj X Y := ULift.{u + 1, u} { f : Y ⟶ X // T.Good f }
    map f g := ↾fun h ↦ ULift.up ⟨g ≫ h.down.1 ≫ f, T.map_good f g h.down.2⟩ }

end HomSubtarget

/-- Dominant/nonconstant morphism data, strong enough to define a target profunctor. -/
structure DominanceStructure (geom : Type (u + 1)) [Category.{u} geom] where
  /-- The morphisms treated as dominant. -/
  Dominant : ∀ {Y X : geom}, (Y ⟶ X) → Prop
  /-- Stability under all ambient pre- and postcomposition maps. -/
  map_dominant : ∀ {X X' Y Y' : geom} (f : X ⟶ X') (g : Y ⟶ Y') {h : Y' ⟶ X},
    Dominant h → Dominant (g ≫ h ≫ f)

namespace DominanceStructure

variable (Dom : DominanceStructure geom)

/-- The dominant-morphism target profunctor. -/
def target : HomSubtarget geom where
  Good := Dom.Dominant
  map_good := Dom.map_dominant

/-- The profunctor of dominant morphisms. -/
abbrev profunctor : CategoryTheory.Profunctor.{u + 1} geom geom :=
  Dom.target.profunctor

end DominanceStructure

/-- A reconstruction theorem whose target is a stable sub-Hom profunctor. -/
structure SubtargetReconstruction
    (geom : Type (u + 1)) (data : Type (u + 1)) [Category.{u} geom] [Category.{u} data] where
  /-- The invariant profunctor. -/
  invariant : CategoryTheory.Profunctor.{u + 1} geom data
  /-- The stable sub-Hom target. -/
  target : HomSubtarget geom
  /-- The data-internal reconstruction algorithm. -/
  algorithm : CategoryTheory.Profunctor.{u + 1} data geom
  /-- The reconstruction isomorphism. -/
  decodeIso : CategoryTheory.Profunctor.comp.{u + 1} invariant algorithm ≅ target.profunctor

namespace SubtargetReconstruction

variable {data : Type (u + 1)} [Category.{u} data] (P : SubtargetReconstruction geom data)

/-- Forget the subtarget name and view the package as a profunctor reconstruction. -/
def toReconstruction : ProfunctorReconstruction geom data where
  invariant := P.invariant
  target := P.target.profunctor
  algorithm := P.algorithm
  decodeIso := P.decodeIso

end SubtargetReconstruction

/-- A section/rational-point reconstruction package as an isomorphism of profunctors. -/
structure SectionFormPackage
    (geom data sectionIndex : Type (u + 1))
    [Category.{u} geom] [Category.{u} data] [Category.{v} sectionIndex] where
  /-- The invariant profunctor. -/
  invariant : CategoryTheory.Profunctor.{u + 1} geom data
  /-- The section-like data attached to invariant-side objects. -/
  sections : CategoryTheory.Profunctor.{u + 1} data sectionIndex
  /-- The geometric point-like target. -/
  points : CategoryTheory.Profunctor.{u + 1} geom sectionIndex
  /-- Sections reconstruct points after composing with the invariant. -/
  sectionIso : CategoryTheory.Profunctor.comp.{u + 1} invariant sections ≅ points

/-- Direct comparison form for section theorems that have already composed the invariant. -/
structure SectionComparisonPackage
    (geom sectionIndex : Type (u + 1)) [Category.{u} geom] [Category.{v} sectionIndex] where
  /-- The section-like profunctor. -/
  sections : CategoryTheory.Profunctor.{u + 1} geom sectionIndex
  /-- The point-like profunctor. -/
  points : CategoryTheory.Profunctor.{u + 1} geom sectionIndex
  /-- Sections reconstruct points. -/
  sectionIso : sections ≅ points

end Anabelian
