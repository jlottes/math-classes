Require Import
  abstract_algebra interfaces.metric_spaces interfaces.orders
  theory.setoids theory.products metric.metric_spaces
  orders.affinely_extended_field the_ae_rationals
  orders.lattices orders.minmax.

Local Notation B := TheAERationals.A.
Local Notation Q := the_ae_rationals.
Local Notation "Q∞" := (aff_ext Q).
Local Notation Qfull := (aff_ext_full Q).

Definition prod_sup_ball `{X:Subset} `{Y:Subset} `{Ball X} `{Ball Y} : Ball (X * Y)
  := λ ε x y, ball ε (fst x) (fst y) ∧ ball ε (snd x) (snd y).
Hint Extern 4 (Ball (elt_type (prod_subset ?X ?Y))) => eexact (prod_sup_ball (X:=X) (Y:=Y)) : typeclass_instances.
Hint Extern 4 (Ball (elt_type ?X * elt_type ?Y)) => eexact (prod_sup_ball (X:=X) (Y:=Y)) : typeclass_instances.
(*Hint Extern 8 (Ball (_ -> _)) => eapply @sup_ball : typeclass_instances.*)

Section contents.
  Context `{MetricSpace (X:=X)} `{MetricSpace (X:=Y)}.

  Instance prod_msp : MetricSpace (X * Y).
  Proof. split; unfold ball, prod_sup_ball. apply _.
  + intros a b E1 x1 x2 Ex y1 y2 Ey [??]. unfold_sigs.
    split; now rewrite <- (_ $ E1), <-(X*Y $ Ex), <-(X*Y $ Ey).
  + intros ?????? [E?]. exact (msp_nonneg _ _ _ E).
  + split; exact (msp_ball_inf _ _).
  + now split.
  + split; subsymmetry; firstorder.
  + intros. apply prod_equal_components; now apply (ball_separated _ _).
  + intros. split.
      now apply (ball_triangle _ _ _ (fst y) _).
      now apply (ball_triangle _ _ _ (snd y) _).
  + intros ?????? P. split; apply (ball_closed _ _ _); intros; now apply P.
  Qed.

  Lemma fst_ufm_cont : UniformlyContinuous (X*Y) X fst.
  Proof. split; try apply _. intros q ?. exists_sub q. now intros ???? [??]. Qed.

  Lemma snd_ufm_cont : UniformlyContinuous (X*Y) Y snd.
  Proof. split; try apply _. intros q ?. exists_sub q. now intros ???? [??]. Qed.

  Local Ltac set_min δ a b Ea Eb :=
    set (δ := @meet _ (min (X:=Q∞)) a b); assert (δ ∊ Q∞₊) by (subst δ; apply _);
    assert (δ ≤ a) as Ea by (subst δ; exact (meet_lb_l (Ameet:=(min (X:=Q∞))) (L:=Q∞) _ _));
    assert (δ ≤ b) as Eb by (subst δ; exact (meet_lb_r (Ameet:=(min (X:=Q∞))) (L:=Q∞) _ _)).

  Lemma prod_open U V : Open X U → Open Y V → Open (X*Y) (U*V).
  Proof. intros ??. split; try apply _.
    pose proof _ : U ⊆ X. pose proof _ : V ⊆ Y. pose proof _ : U*V ⊆ X*Y.
    intros [x y] [??].
    destruct (open U x) as [p[? OU]].
    destruct (open V y) as [q[? OV]].
    set_min r p q Ep Er. exists_sub r.
    intros [a b] [[??][Ba Bb]]. simpl in Ba,Bb. split.
      rewrite <-OU. split. apply _. red. apply (ball_weaken_le r _ _); trivial; apply _.
      rewrite <-OV. split. apply _. red. apply (ball_weaken_le r _ _); trivial; apply _.
  Qed.

End contents.
Hint Extern 2 (MetricSpace (prod_subset ?X ?Y)) => eapply @prod_msp : typeclass_instances.
Hint Extern 2 (UniformlyContinuous _ _ fst) => eapply @fst_ufm_cont : typeclass_instances.
Hint Extern 2 (UniformlyContinuous _ _ snd) => eapply @snd_ufm_cont : typeclass_instances.
Hint Extern 5 (Open (_ * _) (_ * _)) => eapply @prod_open : typeclass_instances.
