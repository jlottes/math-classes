Require Import
  abstract_algebra interfaces.orders interfaces.metric_spaces
  interfaces.archimedean_fields interfaces.reals
  theory.setoids
  orders.maps
  metric.metric_spaces metric.maps
  cauchy_completion arch_field_completion complete_arch_field_reals.
Require Export
  metric.archimedean_fields.

Local Open Scope grp_scope.

Section field_to_reals.
  Context `{Reals (R:=R)}.
  Context `{ArchimedeanField (F:=F)}.

  Section metric.
    Context `{!Ball R} `{!ArchimedeanField_Metric R}.
    Context `{!Ball F} `{!ArchimedeanField_Metric F}.
    Instance to_reals_iso : Isometry F R (to_reals R F) := arch_field_isometry _.
    Instance to_reals_nonneg_iso : Isometry F⁺ R⁺ (to_reals R F) := arch_field_nonneg_isometry _.
  End metric.
  Existing Instance to_reals_iso.

  Instance to_reals_str_inj : StrongInjective F R (to_reals R F) := isometry_str_injective _.
  Instance to_reals_str_mor : Strong_Morphism F R (to_reals R F) := strong_injective_mor _.
End field_to_reals.

Hint Extern 3 (Isometry _ _ (to_reals _ _)) => eapply @to_reals_iso : typeclass_instances.
Hint Extern 2 (Isometry _⁺ _⁺ (to_reals _ _)) => eapply @to_reals_nonneg_iso : typeclass_instances.
Hint Extern 2 (StrongInjective _ _ (to_reals _ _)) => eapply @to_reals_str_inj : typeclass_instances.
Hint Extern 2 (Strong_Morphism _ _ (to_reals _ _)) => eapply @to_reals_str_mor : typeclass_instances.

Section metric.
  Context `{Reals (R:=R)}.

  Lemma to_reals_self (f:R ⇀ R) `{!SemiRing_Morphism R R f} `{!StrictOrderEmbedding R R f}
    : f = id.
  Proof. transitivity (to_reals R R); [|symmetry]; exact (to_reals_terminal R _). Qed.

  Lemma to_reals_self_applied (f:R ⇀ R) `{!SemiRing_Morphism R R f} `{!StrictOrderEmbedding R R f}
    x `{x ∊ R} : f x = x.
  Proof. now destruct (to_reals_self f _ _ (_ : Proper (R,=) x)). Qed.

  Context `{!Ball R} `{!ArchimedeanField_Metric R}.

  Notation C := (CauchyFamilies R).

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
  Instance: ArchimedeanField C := Creals_arch_field.
  Instance: ArchimedeanField_Metric C := Creals_arch_field_metric.

  Instance: SemiRing_Morphism R C (') := Creals_inject_ring_mor.

  Instance: StrictOrderEmbedding R C (').
  Proof arch_field_continuous_embedding (cast R C) _.

  Instance reals_limit : Limit R := to_reals R C.

  Instance reals_complete : CompleteMetricSpace R.
  Proof. split; unfold limit, reals_limit; try apply _.
    intros S ? p ? x ?.
    assert (x ∊ R) by now eapply (_: Subset (S p) R).
    rewrite <-( R $ to_reals_self_applied (to_reals R C ∘ cast R C) x).
    unfold compose. rewrite <- (isometric (to_reals R C) _ _ _).
    subsymmetry. exact (family_const_dist _ _ _).
  Qed.

  Section completion.
    Context `{ArchimedeanField (F:=F)} `{Ball F} `{!ArchimedeanField_Metric F}.

    Existing Instance arch_field_dense.

    Instance to_completion_reals : ToCompletion F R := to_reals R F.
    Instance completion_reals : Completion F R.
    Proof. unfold to_completion_reals. split; unfold to_completion; apply _. Qed.
  End completion.

End metric.

Hint Extern 10 (Ball (elt_type ?R)) => ensure_reals R; eapply arch_field_default_metric : typeclass_instances.
Hint Extern 20 (Ball ?A) => let R := reals_of_type A in eapply (arch_field_default_metric (F:=R)) : typeclass_instances.

Hint Extern 5 (Limit ?R) => ensure_reals R; eapply @reals_limit : typeclass_instances.
Hint Extern 5 (CompleteMetricSpace ?R) => ensure_reals R; eapply @reals_complete : typeclass_instances.
Hint Extern 7 (ToCompletion _ ?R) => ensure_reals R; eapply @to_completion_reals : typeclass_instances.
Hint Extern 7 (Completion _ ?R) => ensure_reals R; eapply @completion_reals : typeclass_instances.

Hint Extern 5 (Limit ?R⁺) => ensure_reals R; eexact (subspace_limit (X:=R) R⁺) : typeclass_instances.
Hint Extern 5 (CompleteMetricSpace ?R⁺) => ensure_reals R; eexact (complete_subspace R⁺) : typeclass_instances.

Hint Extern 5 (Dense (X:=?R) (rationals.rationals_to_field ?Q ?R)⁺¹(?Q)) => ensure_reals R; eapply @arch_field_dense : typeclass_instances.

(*
Section test.
  Context `{Reals (R:=R)}.
  Hint Extern 0 TheReals => eexact R : typeclass_instances.

  (*Instance: CompleteMetricSpace R := _.*)
  Instance: CompleteMetricSpace R⁺ := _.
End test.  
*)

Section image_is_reals.
  Context `{Reals (R:=R)}.
  Context `{ArchimedeanField (F:=F)}.
  Context (f:R ⇀ F) `{!SemiRing_Morphism R F f} `{!StrictOrderEmbedding R F f}.

  Instance image_to_reals : ToReals F := λ _ F' _ _ _ _ _ _ _ _, f ∘ to_reals R F' .

  Instance image_is_reals : Reals F.
  Proof. split; [ apply _ |..]; intros ????????? F' ???; unfold to_reals, image_to_reals.
    apply _. apply _.
    intros g ?? x y [[??]E]. red_sig.
    apply (injective (to_reals R F) _ _).
    cut (to_reals R F ∘ g = to_reals R F ∘ f ∘ to_reals R F').
      intro Ef. now destruct (Ef _ _ ( F' $ E)).
    subtransitivity (to_reals R F'); [| subsymmetry];
    apply (to_reals_terminal R); apply _.
  Qed.
End image_is_reals.

