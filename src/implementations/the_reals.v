Require Import
  abstract_algebra interfaces.metric_spaces interfaces.archimedean_ordered_field interfaces.reals
  metric.metric_spaces
  the_rationals theory.archimedean_ordered_field
  cauchy_completion arch_field_completion complete_arch_field_reals.

Module Type TheRealsSig.
  Parameter A : Type.
  Parameter R : @Subset A.
  Parameter plus : Plus A.
  Parameter mult : Mult A.
  Parameter zero : Zero A.
  Parameter one  : One A.
  Parameter negate : Negate A.
  Parameter inv  : Inv A.
  Parameter equiv: Equiv A.
  Parameter uneq : UnEq A.
  Parameter lt   : Lt A.
  Parameter le   : Le A.
  Parameter U    : FieldToReals R.
  Parameter reals : @Reals A R plus mult zero one negate inv equiv uneq lt le U.
  Parameter ball : Ball A.
  Parameter ball_spec : ArchimedeanOrderedField_Metric R.
End TheRealsSig.

Local Notation Q := the_rationals.
Local Notation X := (CauchyFamilies Q).

Module TheReals : TheRealsSig.
  Definition A : Type := elt_type X.
  Definition R : @Subset A := X.
  Instance plus   : Plus   X := Creals_plus   (F:=Q) (R:=X).
  Instance mult   : Mult   X := Creals_mult   (F:=Q) (R:=X).
  Instance zero   : Zero   X := Creals_zero   (F:=Q) (R:=X).
  Instance one    : One    X := Creals_one    (F:=Q) (R:=X).
  Instance negate : Negate X := Creals_negate (F:=Q) (R:=X).
  Instance inv    : Inv    X := Creals_inv    (F:=Q) (R:=X).
  Instance equiv  : Equiv  X := _ : Equiv X .
  Instance uneq   : UnEq   X := default_metric_uneq (H:=_ : Ball X).
  Instance le     : Le     X := Creals_le     (F:=Q) (R:=X).
  Instance lt     : Lt     X := Creals_lt     (F:=Q) (R:=X).
  Instance ball   : Ball   X := _ : Ball X.

  Instance: MetricInequality X.   Proof. unfold uneq. apply _. Qed.
  Instance: ArchimedeanOrderedField X := Creals_arch_ord_field (F:=Q) (R:=X).
  Instance ball_spec: ArchimedeanOrderedField_Metric X := Creals_arch_ord_field_metric (F:=Q) (R:=X).
  Definition U := field_to_complete_arch_ord_field : FieldToReals X.
  Definition reals := complete_arch_ord_field_reals : Reals X.
End TheReals.

Notation the_reals := TheReals.R.
