Require Import
  abstract_algebra interfaces.orders interfaces.naturals.

Section archimedean_ordered_field.
  Context `{Field A (F:=F)} {Alt: Lt A} {Ale: Le A}.

  Class ArchimedeanOrderedField : Prop :=
  { arch_ord_field_field :>> Field F
  ; arch_ord_field_order :>> FullPseudoSemiRingOrder F
  ; archimedean_def `{Naturals (N:=N)} x `{x ∊ F₊} y `{y ∊ F₊}
      : ∃ `{n ∊ N}, x < (naturals_to_semiring N F⁺ n) * y
  }.
End archimedean_ordered_field.

Arguments ArchimedeanOrderedField {A _ _ _ _ _ _ _ _} F {_ _}.

