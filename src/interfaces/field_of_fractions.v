Require Import abstract_algebra.

(** We define an interface for the field of fractions of an integral domain [D],
based on its universal property: given a field [F] and (strongly) injective
ring morphism [h : D ⇀ F], there is a unique injective ring morphism from
the field of fractions to [F] that extends [h].
In other words, the field of fractions is initial in the
category of fields containing an embedding of [D]. *)

(** We define an “operational typeclass” that introduces the canonical name
[to_field_of_fracs D Q] to refer to the injection of an integral domain [D]
to its field of fractions [Q]. *)

Class ToFieldOfFracs `(D:set) `(Q:set) `{Mult D} `{Plus D} `{One D} `{Zero D} `{Negate D}
  := to_field_of_fracs : D ⇀ Q.
Arguments to_field_of_fracs {_ D} {_} Q {_ _ _ _ _} {ToFieldOfFracs} _.
Instance: Params (@to_field_of_fracs) 10.

(** A strongly injective ring morphism [h] from an integral domain [D] into
a field [F] can be uniquely extended to an injective ring morphism from the
field of fractions.
We give this extension the canonical name [frac_to_field Q F h]. *)

Class FracToField `(D:set) `(Q:set) `{Mult D} `{Plus D} `{One D} `{Zero D} `{Negate D}
  := frac_to_field: ∀ `(F:set) `{Mult F} `{Plus F} `{One F} `{Zero F} `{Negate F} `{Inv F}
     (h:D ⇀ F), Q ⇀ F.
Arguments frac_to_field {_ D} {_} Q {_ _ _ _ _} {FracToField _} F {_ _ _ _ _ _} h _.
Instance: Params (@frac_to_field) 19.

Section definition.
  Context `(D:set) `{IntegralDomain _ (D:=D)}
          `(Q:set) `{Field _ (F:=Q)} `{!ToFieldOfFracs D Q}.

  Section spec.
    Context `(F:set) `{Field _ (F:=F)} (h:D ⇀ F).

    Class FracToFieldSpec (f:Q ⇀ F) : Prop :=
    { frac_to_field_strong : Strong_Morphism   Q F f
    ; frac_to_field_mor    : SemiRing_Morphism Q F f
    ; frac_to_field_extend : f ∘ (to_field_of_fracs Q) = h
    ; frac_to_field_unique (g:Q ⇀ F) `{!Strong_Morphism Q F g} `{!SemiRing_Morphism Q F g} :
        g ∘ (to_field_of_fracs Q) = h → g = f
    }.
  End spec.

  Class Field_of_Fractions {U:FracToField D Q} : Prop :=
  { field_of_frac_intdom : IntegralDomain D
  ; field_of_frac_field  :>> Field Q
  ; field_of_frac_inject : StrongInjective   D Q (to_field_of_fracs Q)
  ; field_of_frac_mor    : SemiRing_Morphism D Q (to_field_of_fracs Q)
  ; field_of_frac_to_field `{Field (F:=F)} {h:D ⇀ F} `{!StrongInjective D F h} `{!SemiRing_Morphism D F h}
    :> FracToFieldSpec F h (frac_to_field Q F h)
  }.
End definition.

Hint Extern 2 (StrongInjective   _ _ (to_field_of_fracs _)) => eapply @field_of_frac_inject : typeclass_instances.
Hint Extern 2 (SemiRing_Morphism _ _ (to_field_of_fracs _)) => eapply @field_of_frac_mor    : typeclass_instances.
Hint Extern 2 (Strong_Morphism   _ _ (frac_to_field _ _ _)) => eapply @frac_to_field_strong : typeclass_instances.
Hint Extern 2 (SemiRing_Morphism _ _ (frac_to_field _ _ _)) => eapply @frac_to_field_mor    : typeclass_instances.
Hint Extern 2 (Strong_Morphism   _ _ (to_field_of_fracs _)) => eapply @strong_injective_mor : typeclass_instances.
Hint Extern 2 (SemiRng_Morphism  _ _ (to_field_of_fracs _)) => eapply @sringmor_srng_mor : typeclass_instances.
Hint Extern 2 (SemiRng_Morphism  _ _ (frac_to_field _ _ _)) => eapply @sringmor_srng_mor : typeclass_instances.
