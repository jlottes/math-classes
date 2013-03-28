Require Import
  abstract_algebra interfaces.metric_spaces
  theory.setoids theory.jections metric.metric_spaces
  orders.affinely_extended_field stdlib_field.

Local Notation B := TheAERationals.A.
Local Notation Q := the_ae_rationals.
Local Notation "Q∞" := (aff_ext Q).
Local Notation Qfull := (aff_ext_full Q).


Lemma prelength `{PrelengthMetricSpace (X:=X)}
  x `{x ∊ X} y `{y ∊ X} ε `{ε ∊ Q∞₊} δ₁ `{δ₁ ∊ Q∞₊} δ₂ `{δ₂ ∊ Q∞₊}
: ε < δ₁ + δ₂ → ball ε x y → ∃ `{z ∊ X}, ball δ₁ x z ∧ ball δ₂ z y.
Proof. intro E.
  destruct (ae_decompose_pos ε) as [E'|?]. rewrite (_ $ E') in E.
    pose proof (_ : δ₁ + δ₂ ∊ Q∞₊). destruct (lt_not_le_flip (P:=Q∞) _ _ E). exact (ae_inf_ub _).
  intro. destruct (ae_decompose_pos δ₁) as [E'|?].
    exists_sub y. split; [| easy]. rewrite (_ $ E'). exact (msp_ball_inf _ _).
  destruct (ae_decompose_pos δ₂) as [E'|?].
    exists_sub x. split; [easy |]. rewrite (_ $ E'). exact (msp_ball_inf _ _).
  now apply (prelength_msp _ _ ε).
Qed.

Local Open Scope mc_fun_scope.

Lemma isometric_image_prelength `{PrelengthMetricSpace (X:=X)} `{MetricSpace (X:=Y)}
  (f:X ⇀ Y) `{!Isometry X Y f} : PrelengthMetricSpace f⁺¹(X).
Proof. split. exact sub_metric_space.
  intros y₁ [?[x₁[? E1]]] y₂ [?[x₂[? E2]]]. intros.
  destruct (prelength x₁ x₂ ε δ₁ δ₂) as [x'[?[??]]]; trivial.
  now rewrite (isometric f _ _ _), (Y $ E1), (Y $ E2).
  exists_sub (f x'). rewrite <-(Y $ E1), <-(Y $ E2), <-2!(isometric f _ _ _). intuition.
Qed.

Lemma isometric_prelength `{PrelengthMetricSpace (X:=X)} `{MetricSpace (X:=Y)}
  (f:X ⇀ Y) `{!Isometry X Y f} `{!Inverse f} `{!Surjective X Y f} : PrelengthMetricSpace Y.
Proof. assert (∀ y, y ∊ Y -> y ∊ f⁺¹(X)). intros. split. apply _. exists_sub (f⁻¹ y). exact (surjective_applied f _).
  pose proof isometric_image_prelength f.
  split. apply _. intros.
  destruct (prelength (X:=f⁺¹(X)) x y ε δ₁ δ₂) as [z[?[??]]]; trivial.
  pose proof _ : f⁺¹(X) ⊆ Y. exists_sub z. intuition.
Qed.

Lemma dense_subset_prelength `{MetricSpace (X:=Y)} (X:Subset) `{!Dense Y X}
  `{!PrelengthMetricSpace X} : PrelengthMetricSpace Y.
Proof. pose proof _ : X ⊆ Y.
  split. apply _. intros y₁ ? y₂ ?. intros.
  pose proof _ : δ₁ + δ₂ ∊ Q₊ .
  set( f₁ := δ₁ / (δ₁ + δ₂) ). assert (f₁ ∊ Q₊) by (subst f₁; apply _).
  set( f₂ := δ₂ / (δ₁ + δ₂) ). assert (f₂ ∊ Q₊) by (subst f₂; apply _).
  set (p := (δ₁ + δ₂ - ε)/3). assert (p ∊ Q₊). subst p.
    cut (δ₁ + δ₂ - ε ∊ Q₊). intro. apply _. now rewrite (flip_pos_minus _ _).
  set( a := f₁ * p ). assert (a ∊ Q₊) by (subst a; apply _).
  set( b := f₂ * p ). assert (b ∊ Q₊) by (subst b; apply _).
  destruct (dense X y₁ a) as [x₁ [??]].
  destruct (dense X y₂ b) as [x₂ [??]].
  set( d₁ := δ₁ - a ). assert (d₁ ∊ Q₊). subst d₁ f₁ a p.
    match goal with |- ?q ∊ _ =>
      mc_replace q with (δ₁/(δ₁ + δ₂)*(2*δ₁ + 2*δ₂ + ε) / 3) on Q by subfield Q
    end. apply _.
  set( d₂ := δ₂ - b ). assert (d₂ ∊ Q₊). subst d₂ f₂ b p.
    match goal with |- ?q ∊ _ =>
      mc_replace q with (δ₂/(δ₁ + δ₂)*(2*δ₁ + 2*δ₂ + ε) / 3) on Q by subfield Q
    end. apply _.
  destruct (prelength x₁ x₂ (a+ε+b) d₁ d₂) as [z [?[??]]].
  + subst d₁ d₂. rewrite <-(flip_pos_minus _ _).
    match goal with |- ?q ∊ _ => cut (q = p) end.
    intro E. now rewrite (_ $ E).
    subtransitivity (3*p - 2*(a+b)). subst p. subfield Q.
    assert (a+b=p) as E. subst a b f₁ f₂. subfield Q. rewrite (_ $ E). subring Q.
  + apply (ball_triangle _ _ _ y₂ _); trivial.
    apply (ball_triangle _ _ _ y₁ _); trivial. subsymmetry.
  + exists_sub z. subst d₁ d₂. split.
    assert (a + (δ₁ - a) = δ₁) as Ea by subring Q.
    apply (ball_proper _ _ _ Y _ _ _ (_ $ Ea) _ _ (_ $ subreflexivity y₁) _ _ (_ $ subreflexivity z)).
    apply (ball_triangle _ _ _ x₁ _); trivial.
    assert (δ₂ - b + b = δ₂) as Eb by subring Q.
    apply (ball_proper _ _ _ Y _ _ _ (_ $ Eb) _ _ (_ $ subreflexivity z) _ _ (_ $ subreflexivity y₂)).
    apply (ball_triangle _ _ _ x₂ _); trivial. subsymmetry.
Qed.

Lemma prelength_completion `{Completion (X:=X) (X':=X')} `{!PrelengthMetricSpace X}
   : PrelengthMetricSpace X'.
Proof.
  pose proof isometric_image_prelength (to_completion X X').
  exact (dense_subset_prelength (to_completion X X')⁺¹(X)).
Qed.
