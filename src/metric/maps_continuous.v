Require Import
  abstract_algebra interfaces.orders interfaces.rationals interfaces.metric_spaces
  theory.setoids theory.jections theory.rings theory.rationals theory.powerset
  orders.rings orders.lattices orders.minmax
  orders.affinely_extended_field stdlib_field
  metric.metric_spaces metric.totally_bounded.
Require Export
  metric.maps.

Local Notation AQ := TheAERationals.A.
Local Notation Q := the_ae_rationals.
Local Notation "Q∞" := (aff_ext Q).
Local Notation Qfull := (aff_ext_full Q).

Section continuity_alt.
  Context `{MetricSpace (X:=X)} `{!LocallyTotallyBounded X} `{D ⊆ X} `{!Open (X:=X) D}.
  Context `{MetricSpace (X:=Y)} `{!LocallyTotallyBounded Y} `{R ⊆ Y} `{!Open (X:=Y) R}.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact Y : typeclass_instances.

  Lemma continuity_alt (f:D ⇀ R) `{!Morphism (D ⇒ R) f}
    : (∀ `{U ⊂⊂ D}, UniformlyContinuous U R f ∧ Bounded f⁺¹(U) ∧ SetContained f⁺¹(U) R)
     → Continuous D R f.
  Proof. intro P. split; try apply _; intros U ?. now destruct (P U _).
    split; try apply _; try apply (P U _).
  Qed.
End continuity_alt.

Lemma uniformly_continuous_continuous
  `{MetricSpace (X:=X)} `{!LocallyTotallyBounded X}
  `{MetricSpace (X:=Y)} `{!LocallyTotallyBounded Y} `{!FinitePoints Y}
  f `{!UniformlyContinuous X Y f} : Continuous (X:=X) (Y:=Y) X Y f.
Proof. apply (continuity_alt f). intros U ?.
  pose proof (restrict_uniformly_continuous f U). intuition.
  apply (ufm_cont_locally_totally_bounded_image _ _).
Qed.
Hint Extern 20 (Continuous _ _ _) => eapply @uniformly_continuous_continuous : typeclass_instances.

(* f = g → Continuous D R f ↔ Continuous D R g *)
Lemma continuous_proper: Find_Proper_Signature (@Continuous) 0
  (∀ A1 (Ae1:Equiv A1) (Aball1:Ball A1) (X:@set A1) D
     A2 (Ae2:Equiv A2) (Aball2:Ball A2) (Y:@set A2) R,
     Proper ((=)==> impl) (Continuous (X:=X) (Y:=Y) D R)).
Proof. red; intros. intros f g Ef ?.
  destruct (_ : Continuous (X:=X) (Y:=Y) D R f) as [?? ?? ?? _ _ _ ].
  assert (Morphism (D ⇒ R) g) by (rewrite <-Ef; apply _).
  split; try apply _; intros U ?.
  rewrite <-(ext_equiv_subrelation U D R R _ _ Ef). now apply (continuity_ufm (X:=X) (Y:=Y)).
  rewrite <-Ef. now apply (continuity_wc_range (X:=X) (Y:=Y)).
Qed.
Hint Extern 0 (Find_Proper_Signature (@Continuous) 0 _) => eexact continuous_proper : typeclass_instances.

Lemma continuous_dom_ran_proper `{MetricSpace (X:=X)} `{MetricSpace (X:=Y)}
  D R f `{!Continuous (X:=X) (Y:=Y) D R f} D' R'
  : D = D' → R = R' → Continuous (X:=X) (Y:=Y) D' R' f.
Proof. intros ED ER.
  destruct (_ : Continuous (X:=X) (Y:=Y) D R f) as [_ _ ?? _ _ _ _ _ ].
  assert (D' ⊆ X) by (rewrite <-ED; apply _).
  assert (R' ⊆ Y) by (rewrite <-ER; apply _).
  assert (Open (X:=X) D') by (rewrite <-ED; apply _).
  assert (Open (X:=Y) R') by (rewrite <-ER; apply _).
  assert (D' ⊆ D) by (rewrite <-ED; apply _).
  assert (R ⊆ R') by (rewrite <-ER; apply _).
  apply continuity_alt.
  rewrite <-(_ : Subset (D ⇒ R) (D' ⇒ R')). apply _.
  intros U ?. assert (WellContained (X:=X) U D) by (rewrite ED; apply _).
  pose proof (continuity_ufm (X:=X) (Y:=Y) U).
  pose proof (continuity_wc_range (X:=X) (Y:=Y) U).
  intuition.
  + apply (ufm_continuous_dom_ran_proper U R); trivial. reflexivity.
  + rewrite <-(image_dom_range_proper f D' R' U). apply _.
  + rewrite <-(image_dom_range_proper f D' R' U). rewrite <-ER. apply _.
Qed.

Section id_continuous.
  Context `{MetricSpace (X:=X)} `{!LocallyTotallyBounded X}.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.

  Lemma id_continuous `{R ⊆ X} `{D ⊆ R} `{!Open D} `{!Open R}
  : Continuous D R id.
  Proof. assert (D ⊆ X) by (transitivity R; apply _).
    split; try apply _; intros U ?;
    assert (U ⊆ R) by (transitivity D; apply _);
    pose proof sub_metric_space : MetricSpace R.
    apply _. rewrite (image_id _).
    now rewrite <-((⊆ X) $ (_ : D ⊆ R)).
  Qed.

  Context `{MetricSpace (X:=Y)} `{!LocallyTotallyBounded Y}.
  Hint Extern 0 AmbientSpace => eexact Y : typeclass_instances.

  Lemma const_continuous `{D ⊆ X} `{!Open D} `{R ⊆ Y} `{!Open R} c `{c ∊ R}
  : Continuous D R (λ _, c).
  Proof. apply continuity_alt. apply _. intros U ?.
    pose proof sub_metric_space : MetricSpace R.
    pose proof sub_metric_space : MetricSpace U.
    intuition.
    + split; try apply _. transitivity R; apply _. exists_sub 0.
      intros x [?[_[_ E1]]] y [?[_[_ E2]]].
      now rewrite <-(_ $ E1), <-(_ $ E2).
    + destruct (open R c) as [q [elq E]]. exists_sub q.
      intros y ? x [?[_[_ Ex]]] ?. apply E. split; trivial. red.
      rewrite (Y $ Ex). now apply (symmetry (S:=Y) _ _).
  Qed.
End id_continuous.
Hint Extern 2 (Continuous _ _ id) => eapply @id_continuous : typeclass_instances.
Hint Extern 2 (Continuous _ _ (λ _, ?c)) => eapply @const_continuous : typeclass_instances.

Section continuous_subsetoid.
  Context
    `{X:set} `{Equiv X} `{Ball X}
    `{Y:set} `{Equiv Y} `{Ball Y}.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact Y : typeclass_instances.

  Instance continuous_subsetoid (D:@set X) (R:@set Y) `{!Setoid D} `{!Setoid R} : D --> R ⊆ D ⇒ R.
  Proof. apply subsetoid_alt. apply _. intros f g E P. red in P.
    red. unfold_sigs. now rewrite <-E.
    now intros ? [??? _].
  Qed.
End continuous_subsetoid.
Hint Extern 2 (_ --> _ ⊆ _ ⇒ _) => eapply @continuous_subsetoid : typeclass_instances.
Hint Extern 2 (Setoid (?X --> ?Y)) => eapply (subsetoid_a (T:=(X ⇒ Y))) : typeclass_instances.

Section compose_continuous.
  Context
    `{X:set} `{Equiv X} `{Ball X}
    `{Y:set} `{Equiv Y} `{Ball Y}
    `{Z:set} `{Equiv Z} `{Ball Z}.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact Y : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact Z : typeclass_instances.

  Lemma compose_continuous
    D₁ R₁ D₂ R₂ (f:D₁ ⇀ R₁) (g:D₂ ⇀ R₂)
    `{!Continuous (X:=X) (Y:=Y) D₁ R₁ f}
    `{!Continuous (X:=Y) (Y:=Z) D₂ R₂ g}
    `{R₁ ⊆ D₂}
    : Continuous D₁ R₂ (g ∘ f).
  Proof.
    destruct (_ : Continuous (X:=X) (Y:=Y) D₁ R₁ f) as [?? ?? _ _ _ _ _ ].
    destruct (_ : Continuous (X:=Y) (Y:=Z) D₂ R₂ g) as [_ ? _ ? _ _ _ _ _ ].
    assert (Morphism (D₁ ⇒ D₂) f).
      rewrite <-(_:Subset (D₁ ⇒ R₁) (D₁ ⇒ D₂)). apply _.
    pose proof _ : Morphism (D₁ ⇒ R₂) (g ∘ (f:D₁ ⇀ D₂)).
    apply (continuity_alt _). intros U ?.
    pose proof (continuity_ufm U). pose proof (continuity_wc_range U).
    assert (f⁺¹(U) ⊂⊂ D₂) by (rewrite <-((⊆ Y) $ (_ : R₁ ⊆ D₂)); apply _).
    pose proof (continuity_ufm f⁺¹(U)). pose proof (continuity_wc_range f⁺¹(U)).
    split.
    + apply (compose_uniformly_cont (X:=U) (Y:=f⁺¹(U)) (Z:=R₂) (f:D₁ ⇀ D₂)); trivial.
      eapply (@restrict_ufm_cont_image _ U); apply _.
    + cut ((g ∘ f)⁺¹(U) ⊂⊂ R₂). intuition; apply _.
      rewrite (compose_image); trivial; try apply _.
      rewrite <-(image_dom_range_proper f U D₂ U). apply _.
      rewrite <-(_:Subset (D₁ ⇒ R₁) (U ⇒ D₂)). apply _.
  Qed.
End compose_continuous.
Hint Extern 2 (Continuous ?X ?Z (@compose _ ?X _ ?Y _ ?Z ?g ?f))
  => eapply (compose_continuous (X:=_:AmbientSpace) (Y:=_:AmbientSpace) (Z:=_:AmbientSpace)
               X Y Y Z f g) : typeclass_instances.

Section cont_strong_mor.
  Context `{Cf:Continuous (X:=X) (Y:=Y) (D:=D) (R:=R) (f:=f)}.
  Context `{UnEq X} `{!MetricInequality X}.
  Context `{UnEq Y} `{!MetricInequality Y}.
  Context `{!FinitePoints X}.

  Instance: MetricSpace X.  Proof. now destruct Cf. Qed.
  Instance: MetricSpace Y.  Proof. now destruct Cf. Qed.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact Y : typeclass_instances.

  Hint Extern 5 (_ ∊ X) => apply (_ : D ⊆ X) : typeclass_instances.
  Hint Extern 5 (_ ∊ Y) => apply (_ : R ⊆ Y) : typeclass_instances.

  Lemma cont_strong_mor : Strong_Morphism D R f.
  Proof. split. apply _. intros x ? y ? E.
    pose proof _ : B 0 x ⊔ B 0 y ⊂⊂ D .
    assert (∀ z, z ∊ B 0 x ⊔ B 0 y → z ∊ D). intros. now apply (_ : B 0 x ⊔ B 0 y ⊂⊂ D).
    assert (MetricInequality (B 0 x ⊔ B 0 y)). intros x' ? y' ?. exact (metric_inequality (X:=X) _ _).
    assert (MetricInequality R). intros x' ? y' ?. exact (metric_inequality (X:=Y) _ _).
    pose proof (continuity_ufm (B 0 x ⊔ B 0 y)).
    pose proof uniformly_cont_strong_mor (X:=B 0 x ⊔ B 0 y) (Y:=R) f as sm.
    apply (strong_morphism_proper (Strong_Morphism := sm)); trivial; apply _.
  Qed.

End cont_strong_mor.
Arguments cont_strong_mor {_ X _ _ _ Y _ _ D R} f {Cf _ _ _ _ _}.

Section continuous_misc.
  Context `{Cf:Continuous (X:=X) (Y:=Y) (D:=D) (R:=R) (f:=f)}.
  Instance: MetricSpace X.  Proof. now destruct Cf. Qed.
  Instance: MetricSpace Y.  Proof. now destruct Cf. Qed.
  Instance: LocallyTotallyBounded X.  Proof. now destruct Cf. Qed.
  Instance: LocallyTotallyBounded Y.  Proof. now destruct Cf. Qed.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact Y : typeclass_instances.

  Hint Extern 5 (_ ∊ X) => apply (_ : D ⊆ X) : typeclass_instances.
  Hint Extern 5 (_ ∊ Y) => apply (_ : R ⊆ Y) : typeclass_instances.

  Lemma pointwise_continuity x `{x ∊ D} ε `{ε ∊ Q∞₊} :  ∃ `{δ ∊ Q₊},
    ∀ `{y ∊ D}, ball δ x y → ball ε (f x) (f y).
  Proof. destruct (open_wc (X:=X) D x) as [q[??]].
    pose proof (continuity_ufm (B q x)).
    destruct (uniform_continuity (f:B q x ⇀ R) ε) as [δ[? C]].
    ae_rat_set_min r q δ E1 E2. pose proof (ae_pos_finite_bound r _ E1).
    exists_sub r. intros y ? By.
    assert (y ∊ B q x). split; [| apply _]. red.
      apply (ball_weaken_le) with r; trivial; try apply _.
    apply (C _ _ _ _).
      apply (ball_weaken_le) with r; trivial; try apply _.
  Qed.

  Context D' `{D' ⊆ D} `{!Open D'}.

  Instance: D' ⊆ X. Proof. transitivity D; apply _. Qed.

  Lemma restrict_continuous : Continuous D' R f.
  Proof. change (Continuous D' R (f ∘ (id:D' ⇀ D)) ). apply _. Qed.

End continuous_misc.
Arguments pointwise_continuity {_ X _ _ _ Y _ _ D R} f {_} x {_} ε {_}.

