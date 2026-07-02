/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

import AnabelianLib.Framework.HomForm


/-!
# Marked and choice-dependent invariants

This file packages invariants that are first defined on a marked or choice-enhanced category.  The
unmarked invariant is a profunctor obtained by composing the forgetful profunctor with the
represented marked invariant.  Descent to a strict unmarked functor is optional extra data.
-/


universe u

namespace Anabelian

open CategoryTheory Opposite

variable {geom data marked : Type (u + 1)} [Category.{u} geom] [Category.{u} data]
  [Category.{u} marked]

/-- Invariant data defined on a marked category above the geometric category. -/
structure MarkedInvariant
    (geom : Type (u + 1)) (data : Type (u + 1)) (marked : Type (u + 1))
    [Category.{u} geom] [Category.{u} data] [Category.{u} marked] where
  /-- Forget the marking or auxiliary choice. -/
  forget : marked ⥤ geom
  /-- The strict covariant invariant on marked objects. -/
  markedI : marked ⥤ data

namespace MarkedInvariant

variable (S : MarkedInvariant geom data marked)

/-- The represented profunctor attached to the marked invariant. -/
abbrev markedInvariantProfunctor : CategoryTheory.Profunctor.{u + 1} marked data :=
  representedInvariant S.markedI

/--
The induced unmarked invariant profunctor.

A representative at `(X, d)` consists of a marked object `m`, a morphism `forget m ⟶ X`, and a data
morphism `d ⟶ markedI m`.
-/
abbrev invariant : CategoryTheory.Profunctor.{u + 1} geom data :=
  S.forget.toProfunctorRev.ulift1.comp.{u + 1} S.markedInvariantProfunctor

/-- Optional descent of a marked invariant to a strict unmarked invariant functor. -/
structure Descent where
  /-- The strict covariant invariant functor on unmarked geometric objects. -/
  I : geom ⥤ data
  /-- Compatibility of the marked invariant with the strict functor after forgetting. -/
  markedIso : S.markedI ≅ S.forget ⋙ I
  /-- The induced invariant profunctor is represented by the strict functor. -/
  invariantIso : S.invariant ≅ representedInvariant I

namespace Descent

variable {S} (Dsc : S.Descent)

/-- A marked descent is a representation of the induced invariant profunctor. -/
def toRepresentedInvariant : RepresentedInvariant S.invariant where
  I := Dsc.I
  iso := Dsc.invariantIso

end Descent

/-- Build a profunctor reconstruction directly from marked invariant data. -/
noncomputable def toReconstruction (target : CategoryTheory.Profunctor.{u + 1} geom geom)
    (algorithm : CategoryTheory.Profunctor.{u + 1} data geom)
    (decodeIso : S.invariant.comp.{u + 1} algorithm ≅ target) :
    ProfunctorReconstruction geom data where
  invariant := S.invariant
  target := target
  algorithm := algorithm
  decodeIso := decodeIso

end MarkedInvariant

end Anabelian
