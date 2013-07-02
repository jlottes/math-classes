Require Import
  abstract_algebra interfaces.orders interfaces.archimedean_ordered_field interfaces.metric_spaces
  interfaces.rationals the_ae_rationals
  interfaces.reals
  theory.setoids theory.products theory.rings
  metric.metric_spaces metric.maps metric.products
  metric.complete metric.continuity
  metric.archimedean_ordered_field.

Local Notation AQ := TheAERationals.A.
Local Notation Q := the_ae_rationals.
Local Notation "Q∞" := (aff_ext Q).
Local Notation Qfull := (aff_ext_full Q).

Local Open Scope grp_scope.

Local Existing Instance arch_ord_field_dense.

Section contents.
  Context `{ArchimedeanOrderedField (F:=R)} `{!Ball R} `{!ArchimedeanOrderedField_Metric R}
          `{!Limit R} `{!CompleteMetricSpace R}.
  Hint Extern 0 AmbientSpace => eexact R : typeclass_instances.
  Notation "#" := (rationals_to_field Q R).

  Section another_field.
    Context `{ArchimedeanOrderedField (F:=F)}.
    Hint Extern 0 AmbientSpace => eexact F : typeclass_instances.
    Notation "%" := (rationals_to_field Q F).

    Definition to_complete_arch_ord_field := ufm_cont_extension % # (M:=Q==>Q) id id .
    Notation φ := to_complete_arch_ord_field.

    Instance: StronglyUniformlyContinuous F R φ.
    Proof. unfold φ.
      apply (ufm_cont_ext_strong % # (M:=(Q==>Q)) id 0 id id).
      unfold id at 1. apply (subreflexivity (S:=Q==>Q) _).
    Qed.

    Let preserves q `{q ∊ Q} : φ (% q) = # q .
    Proof.
      now destruct (ufm_cont_ext_extends_2 % # (M:=Q==>Q) id id _ _ (_ : Proper (Q,=) q)).
    Qed.

    Let preserves_1 : φ 1 = 1.
    Proof. pose proof preserves 1 as E. now rewrite !(_ $ preserves_1) in E. Qed.

    Let preserves_plus x `{x ∊ F} y `{y ∊ F} : φ (x+y) = φ x + φ y.
    Proof.
      cut ( φ ∘ (uncurry (+) : F*F ⇀ F) = (uncurry (+) : R*R ⇀ R) ∘ prod_map φ φ ).
        intro E. now destruct (E _ _ (_:Proper (F*F,=) (x,y) )).
      apply (ufm_cont_equal_on_dense_image_applied (prod_map % %) _ _).
      intros [a b] [??]. change (φ (%a + %b) =  φ(%a) + φ(%b) ).
      rewrite <-(F $ preserves_plus a b).
      rewrite 3!(R $ preserves _).
      exact (preserves_plus _ _).
    Qed.

    Let preserves_mult x `{x ∊ F} y `{y ∊ F} : φ (x*y) = φ x * φ y.
    Proof.
      cut ( φ ∘ (uncurry (.*.) : F*F ⇀ F) = (uncurry (.*.) : R*R ⇀ R) ∘ prod_map φ φ ).
        intro E. now destruct (E _ _ (_:Proper (F*F,=) (x,y) )).
      pose proof arch_ord_field_mult_cont (F:=F).
      pose proof arch_ord_field_mult_cont (F:=R).
      apply (cont_equal_on_dense_image_applied _ _ (prod_map % %)).
      intros [a b] [??]. change (φ (%a * %b) =  φ(%a) * φ(%b) ).
      rewrite <-(F $ preserves_mult a b).
      rewrite 3!(R $ preserves _).
      exact (preserves_mult _ _).
    Qed.

    Instance to_complete_arch_ord_field_ring_mor : Ring_Morphism F R φ .
    Proof. apply ring_morphism_alt; try apply _.
      exact preserves_plus.
      exact preserves_mult.
      exact preserves_1.
    Qed.

    Instance to_complete_arch_ord_field_embedding : StrictOrderEmbedding F R φ.
    Proof. apply arch_ord_field_continuous_embedding; apply _. Qed.

    Context (f:F ⇀ R) `{!Ring_Morphism F R f} `{!StrictOrderEmbedding F R f}.

    Instance: Isometry F R f := arch_ord_field_isometry _.

    Lemma to_complete_arch_ord_field_unique : f = φ.
    Proof. apply (ufm_cont_ext_unique_2 % # (M:=Q==>Q) id id). apply _.
      mc_replace (# ∘ id) with # on (Q ⇀ R) by subreflexivity.
      apply (rationals_to_field_unique Q). apply _.
    Qed.

  End another_field.

  Instance field_to_complete_arch_ord_field : FieldToReals R
    := λ _ F _ _ _ _ _ _ _ _, to_complete_arch_ord_field (F:=F).

  Instance complete_arch_ord_field_reals : Reals R.
  Proof. split. apply _. intros. split.
    exact to_complete_arch_ord_field_ring_mor.
    exact to_complete_arch_ord_field_embedding.
    exact to_complete_arch_ord_field_unique.
  Qed.

End contents.
