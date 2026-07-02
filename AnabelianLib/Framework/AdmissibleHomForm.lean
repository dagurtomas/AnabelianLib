/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

import AnabelianLib.Framework.HomForm


/-!
# Admissible Hom-form reconstruction packages

The cleanest way to handle admissibility is usually to encode it in the theorem's algorithm
profunctor.  This file provides a representable helper for the common case where a strict invariant
functor is available and the algorithm is a subprofunctor of the canonical represented algorithm.
-/


universe u

namespace Anabelian

open CategoryTheory Opposite

variable {geom data : Type (u + 1)} [Category.{u} geom] [Category.{u} data]

/--
Admissibility data for a subprofunctor of the canonical Hom-form algorithm.

`Good d Y φ` says that the data morphism `φ : I Y ⟶ d` is admissible as an algorithmic input.
The stability fields are exactly what is needed for functoriality in `d` and `Y`.
-/
structure AlgorithmAdmissibility (I : geom ⥤ data) where
  /-- The admissible algorithmic morphisms out of invariant objects. -/
  Good : ∀ (d : data) (Y : geom), (I.obj Y ⟶ d) → Prop
  /-- Admissibility is stable under postcomposition by data morphisms. -/
  postcomp : ∀ {d d' : data} {Y : geom} (h : d ⟶ d') {φ : I.obj Y ⟶ d},
    Good d Y φ → Good d' Y (φ ≫ h)
  /-- Admissibility is stable under precomposition with invariant maps. -/
  precomp : ∀ {d : data} {Y Y' : geom} (g : Y ⟶ Y')
    {φ : I.obj Y' ⟶ d}, Good d Y' φ → Good d Y (I.map g ≫ φ)

namespace AlgorithmAdmissibility

variable {I : geom ⥤ data} (A : AlgorithmAdmissibility I)

/-- The admissible subprofunctor of the canonical Hom-form algorithm. -/
@[simps! +dsimpLhs obj_obj obj_map map_app]
def algorithm : CategoryTheory.Profunctor.{u + 1} data geom :=
  .ofCore {
    obj d Y := ULift.{u + 1, u} { φ : I.obj Y ⟶ d // A.Good d Y φ }
    map f g := ↾fun φ ↦
      ULift.up ⟨(I.map g ≫ φ.down.1) ≫ f, A.postcomp f (A.precomp g φ.down.2)⟩
    map_id _ _ := by
      ext φ
      simp
    map_comp _ _ _ _ := by
      ext φ
      simp }

end AlgorithmAdmissibility

/-- Hom-form theorem package using an admissible algorithm subprofunctor. -/
structure AdmissibleHomFormPackage
    (geom : Type (u + 1)) (data : Type (u + 1)) [Category.{u} geom] [Category.{u} data] where
  /-- The strict covariant invariant functor. -/
  I : geom ⥤ data
  /-- The admissible algorithmic morphisms. -/
  admissible : AlgorithmAdmissibility I
  /-- The Hom-form theorem with admissibility in the codomain. -/
  homEquiv : ∀ X Y : geom, (Y ⟶ X) ≃
    { φ : I.obj Y ⟶ I.obj X // admissible.Good _ Y φ }
  /-- Naturality in the reconstructed target variable. -/
  natural_left : ∀ {X X' Y : geom} (f : Y ⟶ X) (g : X ⟶ X'),
    homEquiv X' Y (f ≫ g) =
      ⟨(homEquiv X Y f).1 ≫ I.map g, admissible.postcomp (I.map g) (homEquiv X Y f).2⟩
  /-- Naturality in the reconstructed source variable. -/
  natural_right : ∀ {X Y Y' : geom} (f : Y ⟶ X) (g : Y' ⟶ Y),
    homEquiv X Y' (g ≫ f) =
      ⟨I.map g ≫ (homEquiv X Y f).1, admissible.precomp g (homEquiv X Y f).2⟩
  /-- The final profunctor reconstruction isomorphism. -/
  decodeIso : CategoryTheory.Profunctor.comp.{u + 1} (representedInvariant I) admissible.algorithm ≅
    CategoryTheory.Profunctor.id.ulift1

namespace AdmissibleHomFormPackage

variable (P : AdmissibleHomFormPackage geom data)

/-- The represented invariant profunctor. -/
abbrev invariant : CategoryTheory.Profunctor.{u + 1} geom data :=
  representedInvariant P.I

/-- The admissible algorithm profunctor. -/
abbrev algorithm : CategoryTheory.Profunctor.{u + 1} data geom :=
  P.admissible.algorithm

/-- The admissible Hom-form package as a profunctor reconstruction theorem. -/
noncomputable def toReconstruction : ProfunctorReconstruction geom data where
  invariant := P.invariant
  target := CategoryTheory.Profunctor.id.ulift1
  algorithm := P.algorithm
  decodeIso := P.decodeIso

end AdmissibleHomFormPackage

end Anabelian
