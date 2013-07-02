Require Import
  interfaces.rationals interfaces.integers
  abstract_algebra theory.rationals.
Require Export
  implementations.field_of_fractions.

Section intfrac_rationals.
  Context `{Integers (Z:=Z)} `{UnEq _} `{!DenialInequality Z}.

  Instance FracZ_to_field: RationalsToField (Frac Z) := from_intfracs_to_field.
  Instance FracZ_rationals: Rationals (Frac Z) := from_intfracs.
End intfrac_rationals.

Hint Extern 2 (RationalsToField (Frac _)) => eapply @FracZ_to_field : typeclass_instances.
Hint Extern 2 (Rationals (Frac _)) => eapply @FracZ_rationals : typeclass_instances.
