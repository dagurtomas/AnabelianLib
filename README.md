# AnabelianLib

Reusable Lean scaffolding for profunctor-based anabelian reconstruction packages.

This library contains:

- profunctor composition helpers extending mathlib's profunctor API;
- abstract reconstruction, Hom-form, Iso-form, marked, admissible, and target packages.

The library is intended to be imported by the `Anabelian` project and other Lean developments that
want the same reconstruction framework without depending on the example/theorem files in that
project.
