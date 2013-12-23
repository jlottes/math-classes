Require Import
  abstract_algebra interfaces.integers.

Class RationalsToField `(Q:set)
  := rationals_to_field: ∀ `(F:set) `{Mult F} `{Plus F} `{One F} `{Zero F} `{Negate F} `{Inv F}, Q ⇀ F.
Arguments rationals_to_field {_} Q {RationalsToField _} F {_ _ _ _ _ _} _.
Instance: Params (@rationals_to_field) 11.

Section definition.
  Context `(Q:set) `{Field _ (F:=Q)}.

  Section spec.
    Context `{Field (F:=F)}.

    Class RationalsToFieldSpec (f:Q ⇀ F) : Prop :=
    { rationals_to_field_mor    : SemiRing_Morphism Q F f
    ; rationals_to_field_unique (g:Q ⇀ F) `{!SemiRing_Morphism Q F g} : g = f
    }.
  End spec.

  Class Rationals {U:RationalsToField Q} : Prop :=
  { rationals_field :>> Field Q
  ; rationals_denial_inequality :>> DenialInequality Q
  ; rationals_embed_ints `{Integers (Z:=Z)} :>> Injective Z Q (integers_to_ring Z Q)
  ; rationals_spec `{Integers (Z:=Z)} `{UnEq _} `{!DenialInequality Z}
      `{Field (F:=F)} `{!StrongInjective Z F (integers_to_ring Z F)}
    :> RationalsToFieldSpec (rationals_to_field Q F)
  }.
End definition.

Hint Extern 2 (SemiRing_Morphism _ _ (rationals_to_field _ _)) => eapply @rationals_to_field_mor : typeclass_instances.

