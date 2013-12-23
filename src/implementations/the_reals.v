Require Import
  abstract_algebra interfaces.metric_spaces interfaces.archimedean_fields interfaces.reals
  metric.metric_spaces
  the_rationals orders.archimedean_fields
  cauchy_completion arch_field_completion complete_arch_field_reals theory.reals
  stdlib_ring stdlib_field.

Module Type TheRealsSig.
  Parameter A : Type.
  Parameter R : @set A.
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
  Parameter U    : ToReals R.
  Parameter reals : @Reals A R plus mult zero one negate inv equiv uneq lt le U.
  Parameter ball : Ball A.
  Parameter ball_spec : ArchimedeanField_Metric R.
End TheRealsSig.

Local Notation Q := the_rationals.
Local Notation X := (CauchyFamilies Q).

Module TheReals : TheRealsSig.
  Definition A : Type := elt_type X.
  Definition R : @set A := X.
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
  Instance: ArchimedeanField X := Creals_arch_field (F:=Q) (R:=X).
  Instance ball_spec: ArchimedeanField_Metric X := Creals_arch_field_metric (F:=Q) (R:=X).
  Definition U := to_complete_arch_field : ToReals X.
  Definition reals := complete_arch_field_reals : Reals X.
End TheReals.

Notation the_reals := TheReals.R.

Add Ring the_reals : (stdlib_ring_theory the_reals).
Add Field the_reals' : (stdlib_field_theory the_reals).

Instance: FinitePoints the_reals := _.
Instance: LocatedPoints the_reals := _.
Instance: PrelengthSpace the_reals := _.
Instance: MetricInequality the_reals := _.

Hint Extern 2 (Limit the_reals) => eapply @reals_limit : typeclass_instances.
Hint Extern 2 (CompleteMetricSpace the_reals) => eapply @reals_complete : typeclass_instances.
Hint Extern 4 (ToCompletion _ the_reals) => eapply @to_completion_reals : typeclass_instances.
Hint Extern 4 (Completion _ the_reals) => eapply @completion_reals : typeclass_instances.

Hint Extern 2 (Limit the_reals⁺) => exact (subspace_limit (X:=the_reals) the_reals⁺) : typeclass_instances.
Instance: CompleteMetricSpace the_reals⁺ := complete_subspace _.

Instance: Dense (X:=the_reals) (rationals.rationals_to_field the_ae_rationals the_reals)⁺¹(the_ae_rationals).
Proof arch_field_dense _.
