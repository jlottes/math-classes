Require Import
  abstract_algebra interfaces.orders interfaces.metric_spaces
  interfaces.archimedean_ordered_field interfaces.reals
  theory.setoids
  orders.maps
  metric.metric_spaces metric.maps
  metric.archimedean_ordered_field
  cauchy_completion arch_field_completion complete_arch_field_reals
  the_reals.

Local Open Scope grp_scope.

Section field_to_reals.
  Context `{Reals (R:=R)}.
  Context `{ArchimedeanOrderedField (F:=F)}.

  Section metric.
    Context `{!Ball R} `{!ArchimedeanOrderedField_Metric R}.
    Context `{!Ball F} `{!ArchimedeanOrderedField_Metric F}.
    Instance field_to_reals_iso : Isometry F R (field_to_reals R F) := arch_ord_field_isometry _.
  End metric.
  Existing Instance field_to_reals_iso.

  Instance field_to_reals_str_inj : StrongInjective F R (field_to_reals R F) := isometry_str_injective _.
  Instance field_to_reals_str_mor : Strong_Morphism F R (field_to_reals R F) := strong_injective_mor _.
End field_to_reals.

Hint Extern 2 (Isometry _ _ (field_to_reals _ _)) => eapply @field_to_reals_iso : typeclass_instances.
Hint Extern 2 (StrongInjective _ _ (field_to_reals _ _)) => eapply @field_to_reals_str_inj : typeclass_instances.
Hint Extern 2 (Strong_Morphism _ _ (field_to_reals _ _)) => eapply @field_to_reals_str_mor : typeclass_instances.

Section contents.
  Context `{Reals (R:=R)}.

  Lemma to_reals_self (f:R ⇀ R) `{!Ring_Morphism R R f} `{!StrictOrderEmbedding R R f}
    : f = id.
  Proof. transitivity (field_to_reals R R); [|symmetry]; exact (reals.unique R _). Qed.

  Lemma to_reals_self_applied (f:R ⇀ R) `{!Ring_Morphism R R f} `{!StrictOrderEmbedding R R f}
    x `{x ∊ R} : f x = x.
  Proof. now destruct (to_reals_self f _ _ (_ : Proper (R,=) x)). Qed.

  Context `{!Ball R} `{!ArchimedeanOrderedField_Metric R}.

  Notation C := (CauchyNets R).

  Instance: Plus C := Creals_plus.
  Instance: Mult C := Creals_mult.
  Instance: Negate C := Creals_negate.
  Instance: One C := Creals_one.
  Instance: Zero C := Creals_zero.
  Instance: Inv C := Creals_inv.
  Instance: Le C := Creals_le.
  Instance: Lt C := Creals_lt.
  Instance: UnEq C := default_metric_uneq.
  Instance: MetricInequality C := default_metric_inequality.
  Instance: ArchimedeanOrderedField C := Creals_arch_ord_field.
  Instance: ArchimedeanOrderedField_Metric C := Creals_arch_ord_field_metric.

  Instance: Ring_Morphism R C (') := Creals_inject_ring_mor.

  Instance: StrictOrderEmbedding R C (').
  Proof arch_ord_field_continuous_embedding (cast R C) _.

  Instance reals_limit : Limit R := field_to_reals R C.

  Instance reals_complete : CompleteMetricSpace R.
  Proof. split; unfold limit, reals_limit; try apply _.
    intros S ? p ? x ?.
    assert (x ∊ R) by now eapply (_: SubsetOf (S p) R).
    rewrite <-( R $ to_reals_self_applied (field_to_reals R C ∘ cast R C) x).
    unfold compose. rewrite <- (isometric (field_to_reals R C) _ _ _).
    subsymmetry. exact (net_const_dist _ _ _).
  Qed.

End contents.

Hint Extern 2 (Limit the_reals) => eapply @reals_limit : typeclass_instances.
Hint Extern 2 (CompleteMetricSpace the_reals) => eapply @reals_complete : typeclass_instances.

