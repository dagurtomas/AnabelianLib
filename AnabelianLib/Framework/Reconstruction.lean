/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import AnabelianLib.Mathlib.CategoryTheory.Profunctor.Comp


/-!
# Core profunctor reconstruction framework

The central object is an invariant profunctor

```
invariant : Profunctor geom data
```

This supports invariants depending on "indeterminacies", like choices, such as separable closures
or basepoints.

All framework profunctors live in universe `u + 1`; representable profunctors therefore use
`ULift` on ordinary hom-types in categories with morphisms in universe `u`.
-/

@[expose] public section

universe u

namespace Anabelian

open CategoryTheory Opposite

variable {geom data : Type (u + 1)} [Category.{u} geom] [Category.{u} data]

/--
The invariant profunctor represented by a strict covariant functor.

For `I : geom ⥤ data`, the value at `(X, d)` is the universe lift of `d ⟶ I X`.  This is the
standard profunctor represented by the invariant object `I X`, placed in the uniform profunctor
universe `u + 1`.
-/
@[simps! +dsimpLhs obj_obj obj_map map_app]
def representedInvariant (I : geom ⥤ data) : Profunctor.{u + 1} geom data :=
  I.toProfunctor.ulift1

/--
The canonical Hom-form algorithm associated to a strict covariant invariant functor.

At `(d, Y)` it is the universe lift of the type of data morphisms `I Y ⟶ d`.
-/
@[simps! +dsimpLhs obj_obj obj_map map_app]
def representedAlgorithm (I : geom ⥤ data) : Profunctor.{u + 1} data geom :=
  I.toProfunctorRev.ulift1

/--
A reconstruction theorem as an isomorphism of profunctors.

`invariant` is the group-theoretic invariant of geometric objects, `algorithm` is a profunctor in
the other direction, and `target` is the geometric profunctor being reconstructed (most often the
identity).
-/
structure ProfunctorReconstruction
    (geom : Type (u + 1)) (data : Type (u + 1)) [Category.{u} geom] [Category.{u} data] where
  /-- The invariant of geometric objects, allowing indeterminacy. -/
  invariant : Profunctor.{u + 1} geom data
  /-- The geometric profunctor being reconstructed. -/
  target : Profunctor.{u + 1} geom geom
  /-- The reconstruction algorithm. -/
  algorithm : Profunctor.{u + 1} data geom
  /-- The isomorphism from the composition of the invariant and the algorithm to the target. -/
  decodeIso : invariant.comp.{u + 1} algorithm ≅ target

namespace ProfunctorReconstruction

variable (P : ProfunctorReconstruction geom data)

/-- The decoding map from algorithmic data to geometric output. -/
noncomputable def decode :
    P.invariant.comp.{u + 1} P.algorithm ⟶ P.target :=
  P.decodeIso.hom

/-- The encoding map from geometric output to algorithmic data. -/
noncomputable def encode :
    P.target ⟶ P.invariant.comp.{u + 1} P.algorithm :=
  P.decodeIso.inv

@[simp]
theorem decode_encode : P.decode ≫ P.encode = 𝟙 _ :=
  P.decodeIso.hom_inv_id

@[simp]
theorem encode_decode : P.encode ≫ P.decode = 𝟙 P.target :=
  P.decodeIso.inv_hom_id

end ProfunctorReconstruction

/--
A two-sided reconstruction theorem for Hom-like statements whose source and target geometric
categories differ.

At `(Y, X)`, the target usually represents morphisms `X ⟶ Y`. The invariant is attached to the
codomain variable `Y`, while the algorithm is attached to the domain variable `X`.
-/
structure TwoSidedProfunctorReconstruction
    (codomain domain data : Type (u + 1))
    [Category.{u} codomain] [Category.{u} domain] [Category.{u} data] where
  /-- The invariant of target/codomain objects. -/
  invariant : Profunctor.{u + 1} codomain data
  /-- The geometric profunctor being reconstructed. -/
  target : Profunctor.{u + 1} codomain domain
  /-- The data-internal reconstruction algorithm, attached to source/domain objects. -/
  algorithm : Profunctor.{u + 1} data domain
  /-- Soundness and completeness as a profunctor isomorphism. -/
  decodeIso : invariant.comp.{u + 1} algorithm ≅ target

namespace TwoSidedProfunctorReconstruction

variable {codomain domain data : Type (u + 1)}
variable [Category.{u} codomain] [Category.{u} domain] [Category.{u} data]
variable (P : TwoSidedProfunctorReconstruction codomain domain data)

/-- The decoding map from algorithmic data to geometric output. -/
noncomputable def decode :
    P.invariant.comp.{u + 1} P.algorithm ⟶ P.target :=
  P.decodeIso.hom

/-- The encoding map from geometric output to algorithmic data. -/
noncomputable def encode :
    P.target ⟶ P.invariant.comp.{u + 1} P.algorithm :=
  P.decodeIso.inv

@[simp]
theorem decode_encode : P.decode ≫ P.encode = 𝟙 _ :=
  P.decodeIso.hom_inv_id

@[simp]
theorem encode_decode : P.encode ≫ P.decode = 𝟙 P.target :=
  P.decodeIso.inv_hom_id

end TwoSidedProfunctorReconstruction

/-- Optional representation of an indeterminate invariant profunctor by a strict functor. -/
structure RepresentedInvariant (invariant : Profunctor.{u + 1} geom data) where
  /-- A strict covariant invariant functor. -/
  I : geom ⥤ data
  /-- The given invariant profunctor is represented by `I`. -/
  iso : invariant ≅ representedInvariant I

end Anabelian
