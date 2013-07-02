Require Import
  abstract_algebra interfaces.orders interfaces.archimedean_ordered_field.

Class FieldToReals `(R:Subset)
  := field_to_reals: ∀ `{F:Subset} `{Equiv F} `{Le F} `{Mult F} `{Plus F} `{One F} `{Zero F} `{Negate F} `{Inv F}, F ⇀ R.
Arguments field_to_reals {_} R {FieldToReals _} F {_ _ _ _ _ _ _ _} _.
Instance: Params (@field_to_reals) 13.

Section definition.
  Context `(R:Subset) `{ArchimedeanOrderedField _ (F:=R)}.

  Section spec.
    Context `{ArchimedeanOrderedField (F:=F)}.

    Class FieldToRealsSpec (f:F ⇀ R) : Prop :=
    { field_to_reals_mor : Ring_Morphism F R f
    ; field_to_reals_embedding : StrictOrderEmbedding F R f
    ; unique (g:F ⇀ R) `{!Ring_Morphism F R g} `{!StrictOrderEmbedding F R g} : g = f
    }.
  End spec.

  Class Reals {U:FieldToReals R} : Prop :=
  { reals_arch_ord_field :>> ArchimedeanOrderedField R
  ; reals_spec `{ArchimedeanOrderedField (F:=F)} :> FieldToRealsSpec (field_to_reals R F)
  }.
End definition.

Hint Extern 2 (Ring_Morphism _ _ (field_to_reals _ _)) => eapply @field_to_reals_mor : typeclass_instances.
Hint Extern 2 (StrictOrderEmbedding _ _ (field_to_reals _ _)) => eapply @field_to_reals_embedding : typeclass_instances.

