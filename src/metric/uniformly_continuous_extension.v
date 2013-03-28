Require Import
  abstract_algebra interfaces.orders interfaces.rationals interfaces.metric_spaces
  theory.setoids theory.jections theory.fields theory.rationals
  orders.affinely_extended_field stdlib_field
  orders.minmax orders.lattices
  metric.metric_spaces prelength cauchy_completion
  theory.products metric.product.

Local Notation B := TheAERationals.A.
Local Notation Q := the_ae_rationals.
Local Notation "Q∞" := (aff_ext Q).
Local Notation Qfull := (aff_ext_full Q).
Add Field Q : (stdlib_field_theory Q).


(** A complete metric space is the completion of any of its
    dense subsets, including itself. *)

Hint Extern 10 (ToCompletion ?X ?Y) => eexact (id : X ⇀ Y) : typeclass_instances.

Section complete_dense_completion.
  Context `(X:Subset) (Y:Subset) `{CompleteMetricSpace _ (X:=Y)} `{!Dense Y X}.

  Let sub := _ : X ⊆ Y.
  Instance: MetricSpace X := sub_metric_space.
  Instance: Morphism (X ⇒ Y) (id:X ⇀ Y) := _.

  Instance complete_dense_subset_completion: Completion X Y.
  Proof. split; unfold to_completion; try apply _.
    split; try apply _. rewrite (image_id X). exact dense_def.
  Qed.
End complete_dense_completion.

Hint Extern 10 (Completion _ _) => eapply @complete_dense_subset_completion : typeclass_instances.


Local Existing Instance completion_msp_X.

Local Hint Extern 5 (?x ∊ ?X) => match goal with
  H : x ∊ ?S ?q |- _ => eapply (_: SubsetOf (S q) X)
end : typeclass_instances.

Local Hint Extern 5 (Cauchy ?S) => eexact (_ : S ∊ (CauchyNets _)) : typeclass_instances.

Local Hint Extern 2 (_ ∊ (⊆ _)) => red : typeclass_instances.

Lemma uniform_continuity_half `{X:Subset} `{Y:Subset} (f:X ⇀ Y)
  `{MetricSpace _ (X:=X)} `{MetricSpace _ (X:=Y)}
  q `{q ∊ Q∞₊} δ `{δ ∊ Q∞₊} :
  (∀ `{x₁ ∊ X} `{x₂ ∊ X}, ball δ x₁ x₂ → ball q (f x₁) (f x₂))
→ (∀ `{x₁ ∊ X} `{x₂ ∊ X}, ball (δ/2 + δ/2) x₁ x₂ → ball q (f x₁) (f x₂)).
Proof. intro P. intros ???? B. rewrite (_ $ ae_in_halves _) in B. now apply P. Qed.

Lemma uniform_continuity_alt `{X:Subset} `{Y:Subset} (f:X ⇀ Y)
  `{Equiv X} `{Ball X} `{Equiv Y} `{Ball Y} `{!UniformlyContinuous X Y f}
  q `{q ∊ Q∞₊} :  ∃ `{p ∊ Q∞₊} `{ε ∊ Q∞₊},
  (∀ `{x₁ ∊ X} `{x₂ ∊ X}, ball (p + ε) x₁ x₂ → ball q (f x₁) (f x₂)).
Proof. destruct (_ : UniformlyContinuous X Y f) as [?? _ _].
  destruct (uniform_continuity f q) as [p[el Pc]].
  exists_sub (p/2) (p/2). now apply (uniform_continuity_half f _ p).
Qed.

Local Ltac set_min δ a b Ea Eb :=
    set (δ := @meet _ (min (X:=Q∞)) a b); assert (δ ∊ Q∞₊) by (subst δ; apply _);
    assert (δ ≤ a) as Ea by (subst δ; exact (meet_lb_l (Ameet:=(min (X:=Q∞))) (L:=Q∞) _ _));
    assert (δ ≤ b) as Eb by (subst δ; exact (meet_lb_r (Ameet:=(min (X:=Q∞))) (L:=Q∞) _ _)).

Local Infix "==>" := UniformlyContinuous (at level 55, right associativity) : mc_scope.

Section ufm_continuous_extension.
  Context `{MetricSpace (X:=X₁)} `{MetricSpace (X:=X₂)}.
  Context (g:X₁ ⇀ X₂) `{!Isometry X₁ X₂ g} `{!Dense X₂ g⁺¹(X₁)}.
  Context `{MetricSpace (X:=Y₁)} `{CompleteMetricSpace (X:=Y₂)}.
  Context (h:Y₁ ⇀ Y₂) `{!Isometry Y₁ Y₂ h}.
  Context `{MetricSpace (X:=M)}.
  Context (m:(X₁==>Y₁) ⇀ M) `{!Isometry (X₁==>Y₁) M m} `{!Dense M m⁺¹(X₁==>Y₁)}.

  Section def.

    Context f `{f ∊ M}.

    Notation C := (CauchyNets Y₁).

    Let proj_ball q u : Subset := X₁ ⊓ (λ x, ball q u (g x)).

    Definition ufm_cont_ext_net : X₂ ⇀ C := λ u, net (λ q y,
      ∃ `{a ∊ Q∞⁺} `{b ∊ Q∞⁺}, a + b ≤ q 
        ∧ ∃ (f':X₁ ⇀ Y₁) `{f' ∊ (X₁==>Y₁)}, ball a (m f') f
          ∧ ∃ `{p ∊ Q∞₊} `{ε ∊ Q∞₊},
              (∀ `{x₁ ∊ X₁} `{x₂ ∊ X₁}, ball (p+ε) x₁ x₂ → ball b (f' x₁) (f' x₂))
              ∧ y ∊ f'⁺¹(proj_ball p u)
    ).

    Notation S := ufm_cont_ext_net.

    Instance: ∀ u `{u ∊ X₂} `{q ∊ Q∞⁺}, proj_ball q u ⊆ X₁.
    Proof. unfold proj_ball. intros. split. apply _.
    + intros ?? E [??]. unfold_sigs. split. apply _. red. now rewrite <- (_ $ E).
    + firstorder.
    Qed.

    Instance: ∀ u `{u ∊ X₂} `{q ∊ Q∞⁺}, S u q ⊆ Y₁.
    Proof with intuition. intros. split. apply _.
    + intros z1 z2 Ez [a[?[b[?[Eab [f'[Cf[Ef [p[?[ε[?[??]]]]] ]]] ]]]]].
      exists_sub a b... exists_sub f'... exists_sub p ε...
      red in Cf. now rewrite <-Ez.
    + now intros z [a[?[b[?[Eab [f'[Cf[Ef [p[?[ε[?[?[??]]]]]] ]]] ]]]]].
    Qed.

    Instance: ∀ u `{u ∊ X₂} `{q ∊ Q∞⁺}, Setoid (S u q).
    Proof. intros. exact subsetoid_a. Qed.

    Lemma ufm_cont_ext_net_proper_1 u `{u ∊ X₂} p `{p ∊ Q∞⁺} q `{q ∊ Q∞⁺} : p = q →
        ∀ `{z ∊ S u p}, z ∊ S u q.
    Proof. intros E z [a[?[b[?[Eab ?]]]]]. rewrite (_ $ E) in Eab.
      exists_sub a b. intuition.
    Qed.

    Lemma ufm_cont_ext_net_proper_2 y₁ `{y₁ ∊ X₂} y₂ `{y₂ ∊ X₂} : y₁ = y₂  →
      S y₁ = S y₂.
    Proof. intro E.
      intros q₁ ? q₂ ? z₁ [a₁[?[b₁[?[Eab₁ [f₁[Cf₁[Ef₁ [p₁[?[e₁[?[c₁[?[x₁[[??]Ez₁]]]]]]]] ]]] ]]]]].
      intros           z₂ [a₂[?[b₂[?[Eab₂ [f₂[Cf₂[Ef₂ [p₂[?[e₂[?[c₂[?[x₂[[??]Ez₂]]]]]]]] ]]] ]]]]].
      destruct (ae_nonneg_sum_finite_bound _ _ _ Eab₁).
      destruct (ae_nonneg_sum_finite_bound _ _ _ Eab₂).
      subsymmetry in Ef₂.
      pose proof (ball_triangle a₁ a₂ (m f₁) f (m f₂) Ef₁ Ef₂) as Ef. clear Ef₁ Ef₂.
      rewrite <-(isometric m _ _ _) in Ef. destruct Ef as [_ Ef].
      red in Cf₁,Cf₂.
      rewrite <-(_ $ Ez₁), <-(_ $ Ez₂).
      set_min ε e₁ e₂ Ee1 Ee2.
      destruct (dense g⁺¹(X₁) y₁ ε) as [y'[[?[x'[? Ex']]] B1]].
      assert (ball ε y₂ y') as B2 by now rewrite <-(_ $ E).
      assert (b₁ + (a₁ + a₂) + b₂ ≤ q₁ + q₂).
        subtransitivity ((a₁+b₁) + (a₂+b₂)). apply (eq_le _ _). subring Q.
        now apply (plus_le_compat _ _ _ _).
      apply (ball_weaken_le (b₁ + (a₁ + a₂) + b₂) _ _); trivial; try apply _.
      apply (ball_triangle _ _ _ (f₂ x') _).
      apply (ball_triangle _ _ _ (f₁ x') _).
      + apply (c₁ _ _ _ _). rewrite (isometric g _ _ _).
        apply (ball_triangle _ _ _ y₁ _). subsymmetry.
        rewrite (_ $ Ex'). now apply (ball_weaken_le ε _ _ B1 _).
      + now apply Ef.
      + apply (c₂ _ _ _ _). rewrite (isometric g _ _ _). subsymmetry.
        apply (ball_triangle _ _ _ y₂ _). subsymmetry.
        rewrite (_ $ Ex'). now apply (ball_weaken_le ε _ _ B2 _).
    Qed.

    Instance: ∀ y `{y ∊ X₂}, S y ∊ C.
    Proof. intros. split. apply _.
    + intros ?? E. unfold_sigs. red_sig.
      split; apply ufm_cont_ext_net_proper_1; trivial; try apply _. subsymmetry.
    + intros q ?. destruct (dense m⁺¹(X₁ ==> Y₁) f (q/2)) as [?[[? [f' [Cf Ef]]] Bf]].
      rewrite <-(_ $ Ef) in Bf. red in Cf.
      destruct (uniform_continuity_alt f' (q/2)) as [p[el[ε[el' Pc]]]].
      destruct (dense g⁺¹(X₁) y p) as [y'[[?[x'[? Ex']]] B1]].
      exists (f' x'). pose proof (_ : q/2 ∊ Q∞₊).
        exists_sub (q/2) (q/2). split.
        rewrite (_ $ ae_in_halves _). exact (subreflexivity (S:=Q∞) _).
      exists_sub f'. split. subsymmetry.
      exists_sub p ε. unfold proj_ball. rewrite <-(_ $ Ex') in B1.
      split. exact Pc. apply _.
    + now apply ufm_cont_ext_net_proper_2.
    Qed.

    Instance ufm_cont_ext_net_mor : Morphism (X₂ ⇒ C) S.
    Proof. intros y1 y2 Ey. unfold_sigs. red_sig. now apply ufm_cont_ext_net_proper_2. Qed.

  End def.

  Definition ufm_cont_extension : M ⇀ (X₂ ==> Y₂)
    := λ f, (map_limit h) ∘ (ufm_cont_ext_net f).

  Existing Instance ufm_cont_ext_net_mor.

  Instance ufm_cont_ext_mor f `{f ∊ M} : Morphism (X₂ ⇒ Y₂) (ufm_cont_extension f).
  Proof. unfold ufm_cont_extension. apply _. Qed.

  Section continuity.

  Context f `{f ∊ M}.
  Notation S := (ufm_cont_ext_net f).
  Notation cf := (ufm_cont_extension f).

  Lemma ufm_cont_ext_cont_nearly  a `{a ∊ Q₊} b `{b ∊ Q₊} p `{p ∊ Q∞₊} 
    f' `{Cf: f' ∊ (X₁ ==> Y₁)} : ball a (m f') f 
   → ( ∀ `{x₁ ∊ X₁} `{x₂ ∊ X₁}, ball p x₁ x₂ → ball b (f' x₁) (f' x₂) )
   → ∀ ε `{ε ∊ Q₊},
    ( ∀ `{y₁ ∊ X₂} `{y₂ ∊ X₂}, ball (p-ε) y₁ y₂ → ball (a+b+a) (cf y₁) (cf y₂) ).
  Proof. intros Bf Cb. intros. apply (ball_closed _ _ _). intros.
    mc_replace (a+b+a + δ) with ((a+δ/2) +b+ (a+δ/2)) on Q by subfield Q.
    unfold ufm_cont_extension, compose. red in Cf.
    destruct (uniform_continuity f' (δ/2)) as [c[? Cδ]].
    pose proof _ : c/2 ∊ Q∞₊ . pose proof _ : ε/2 ∊ Q₊ .
    set_min θ (c/2) (ε/2) Ec E; pose proof (ae_pos_finite_bound θ _ E).
    destruct (dense g⁺¹(X₁) y₁ θ) as [y₁'[[?[x₁[? Ex1]]] B1]].
    destruct (dense g⁺¹(X₁) y₂ θ) as [y₂'[[?[x₂[? Ex2]]] B2]].
    pose proof _ : δ/2 ∊ Q∞₊ .
    assert (f' x₁ ∊ S y₁ (a+δ/2)).
      exists_sub a (δ/2). split. subreflexivity.
      exists_sub f'. split. trivial.
      exists_sub (c/2) (c/2). split. now apply (uniform_continuity_half f' _ c).
      cut (g x₁ ∊ ball (c / 2) y₁). intro. apply _.
      red. rewrite (_ $ Ex1). apply (ball_weaken_le _ _ _ B1); trivial; apply _.
    assert (f' x₂ ∊ S y₂ (a+δ/2)).
      exists_sub a (δ/2). split. subreflexivity.
      exists_sub f'. split. trivial.
      exists_sub (c/2) (c/2). split. now apply (uniform_continuity_half f' _ c).
      cut (g x₂ ∊ ball (c / 2) y₂). intro. apply _.
      red. rewrite (_ $ Ex2). apply (ball_weaken_le _ _ _ B2); trivial; apply _.
    apply (ball_triangle _ _ _ (h (f' x₂)) _); [| now apply (map_limit_spec _ _ _ _)].
    apply (ball_triangle _ _ _ (h (f' x₁)) _). subsymmetry. now apply (map_limit_spec _ _ _ _).
    rewrite <-(isometric h _ _ _).
    apply (Cb _ _ _ _). apply (ball_weaken_le (θ + (p-ε) + θ) _ _); try apply _.
    rewrite (isometric g _ _ _), (_ $ Ex1), (_ $ Ex2).
    apply (ball_triangle _ _ _ y₂ _); trivial.
    apply (ball_triangle _ _ _ y₁ _); [ subsymmetry | trivial].
    destruct (ae_decompose_pos p) as [E'|?].
      rewrite (_ $ E'). rewrite (_ $ ae_plus_inf_l (-ε) (ae_minf_slb _)).
      pose proof _ : θ + ∞ + θ ∊ Q∞₊. exact (ae_inf_ub _).
    rewrite <-(mult_inv_le_cancel_r _ _ _) in E.
    mc_replace (θ + (p - ε) + θ) with (p + θ*2 - ε) on Q by subring Q.
    rewrite (flip_le_minus_l _ _ _). now apply (order_preserving (p+) _ _).
  Qed.

  Instance ufm_cont_ext_cont : UniformlyContinuous X₂ Y₂ cf.
  Proof. split; try apply _. intros q ?.
    destruct (dense m⁺¹(X₁ ==> Y₁) f (q/3)) as [?[[? [f' [Cf Ef]]] Bf]].
    rewrite <-(_ $ Ef) in Bf. subsymmetry in Bf. red in Cf.
    destruct (uniform_continuity f' (q/3)) as [p[el Pc]].
    assert (q = q/3+q/3+q/3) as Eq by subfield Q.
    destruct (ae_decompose_pos p) as [E|?].
      exists_sub ∞. intros y1 ? y2 ? ?. rewrite (_ $ Eq).
      apply (ufm_cont_ext_cont_nearly _ _ ∞ f' Bf) with 1; trivial; try apply _.
      intros. apply (Pc _ _ _ _). now rewrite (_ $ E).
      now rewrite (_ $ ae_plus_inf_l (-1) (ae_minf_slb _)).
    exists_sub (p/2). intros. rewrite (_ $ Eq).
    apply (ufm_cont_ext_cont_nearly _ _ p f' Bf) with (p/2); trivial; try apply _.
    now mc_replace (p-p/2) with (p/2) on Q by subfield Q.
  Qed.

  End continuity.

  Lemma ufm_cont_ext_extends q `{q ∊ Q⁺} f `{f ∊ M} f' `{!UniformlyContinuous X₁ Y₁ f'} :
    ball q (m f') f ↔ ball q (h ∘ f') (ufm_cont_extension f ∘ g).
  Proof.
    assert (∀ `{p ∊ Q⁺} `{r ∊ Q₊} f'' `{!(X₁ ==> Y₁) f''} `{x ∊ X₁},
       ball p (m f'') f → f'' x ∊ ufm_cont_ext_net f (g x) (p+r)) as Pel.
      intros. exists_sub p r. split. now apply (eq_le _ _).
      exists_sub f''. split; trivial.
      destruct (uniform_continuity_alt f'' r) as [p'[el'[ε[el'' Pc]]]].
      exists_sub p' ε. split. exact Pc.
      assert (ball p' (g x) (g x)) by subreflexivity. apply _.
    split.
  + intro. split. apply _. intros x ?. unfold compose.
    apply (ball_closed _ _ _). intros b ?.
    assert (f' x ∊ ufm_cont_ext_net f (g x) (q+b)) by now apply Pel.
    unfold ufm_cont_extension. apply (map_limit_spec _ _ _ _).
  + intros [_ P]. unfold compose in P. apply (ball_closed _ _ _). intros ε ?.
    destruct (dense m⁺¹(X₁ ==> Y₁) f (ε/3)) as [f'' [[? [f₂ [Cf Ef]]] Bf]]. red in Cf.
    mc_replace (q + ε) with (q + (ε/3+ε/3) + ε/3) on Q by subfield Q.
    apply (ball_triangle _ _ _ f'' _); try solve [ subsymmetry ].
    rewrite <-(_ $ Ef), <-(isometric m _ _ _).
    pose proof _ : ε/3 ∊ Q₊ . pose proof _ : q + (ε/3+ε/3) ∊ Q₊ .
    split. apply _. intros x ?. rewrite (isometric h _ _ _).
    apply (ball_triangle _ _ _ (ufm_cont_extension f (g x)) _).
    now apply P.
    assert (f₂ x ∊ ufm_cont_ext_net f (g x) (ε/3+ε/3)).
      apply Pel; trivial. apply _. rewrite (_ $ Ef). subsymmetry.
    unfold ufm_cont_extension. subsymmetry. apply (map_limit_spec _ _ _ _).
  Qed.

  Lemma ufm_cont_ext_extends_2 f `{!UniformlyContinuous X₁ Y₁ f}
    : ufm_cont_extension (m f) ∘ g = h ∘ f.
  Proof. rewrite <-(ball_separated (X:=X₁ ⇒ Y₂) _ _).
    subsymmetry. now rewrite <-(ufm_cont_ext_extends _ _ _).
  Qed.

End ufm_continuous_extension.

Hint Extern 2 (Morphism _ (ufm_cont_extension _ _ _ _)) => eapply @ufm_cont_ext_mor : typeclass_instances.
Hint Extern 2 (UniformlyContinuous _ _ (ufm_cont_extension _ _ _ _)) => eapply @ufm_cont_ext_cont : typeclass_instances.

Section ufm_continuous_equal_on_dense.
  Context `{Y:@Subset A} `{Z:Subset} (f:Y ⇀ Z) (g:Y ⇀ Z) (X:@Subset A).
  Context `{MetricSpace _ (X:=Y)}.
  Context `{MetricSpace _ (X:=Z)}.
  Context `{!Dense Y X}.
  Context `{!UniformlyContinuous Y Z f} `{!UniformlyContinuous Y Z g}.

  Let sub := _ : X ⊆ Y.
  Instance: MetricSpace X := sub_metric_space.
  Local Ltac apply_cont C δ :=
    apply (C _ _ _ _); apply (ball_weaken_le δ _ _); trivial; try apply _; subsymmetry.

  Lemma ufm_cont_ball_on_dense_fwd q `{q ∊ Qfull} : ball q (f:X ⇀ Z) (g:X ⇀ Z) → ball q f g.
  Proof.
    pose proof restrict_uniformly_continuous f X.
    pose proof restrict_uniformly_continuous g X.
    intro P. pose proof msp_nonneg (X:=X⇒Z) q _ _ P.
    destruct (ae_decompose_nonneg q) as [Eq|?].
      rewrite (_ $ Eq). exact (msp_ball_inf (X:=Y⇒Z) _ _).
    destruct P as [_ P]. split. apply _. intros y ?.
    apply (ball_closed _ _ _). intros ε ?.
    destruct (uniform_continuity f (ε/2)) as [a[el' Cf]].
    destruct (uniform_continuity g (ε/2)) as [b[el'' Cg]].
    set_min δ a b Ea Eb.
    destruct (dense X y δ) as [x[??]].
    mc_replace (q + ε) with (ε/2 + q + ε/2) on Q by subfield Q.
    apply (ball_triangle _ _ _ (g x) _).
    apply (ball_triangle _ _ _ (f x) _).
    apply_cont Cf δ. now apply P. apply_cont Cg δ.
  Qed.

  Lemma ufm_cont_ball_on_dense q `{q ∊ Qfull} : ball q (f:X ⇀ Z) (g:X ⇀ Z) ↔ ball q f g.
  Proof. split. exact (ufm_cont_ball_on_dense_fwd _).
    intros [? P]. split. apply _. intros x ?. exact (P _ _).
  Qed.

  Lemma ufm_cont_equal_on_dense : (f:X ⇀ Z) = (g:X ⇀ Z) ↔ f = g.
  Proof. rewrite <-(ball_separated (X:=Y⇒Z) _ _).
    pose proof restrict_uniformly_continuous f X.
    pose proof restrict_uniformly_continuous g X.
    rewrite <-(ball_separated (X:=X⇒Z) _ _).
    exact (ufm_cont_ball_on_dense _).
  Qed.

  Lemma extend_isometry : Isometry X Z f → Isometry Y Z f.
  Proof. intro. split; try apply _. intros q ? y₁ ? y₂ ?. split.
  + intro. apply (ball_closed _ _ _). intros a ?.
    set (ε := a/(2*2)). assert (ε ∊ Q₊) by (subst ε; apply _).
    destruct (uniform_continuity f ε) as [b [el Cf]].
    set_min δ ε b Ea Eb; pose proof (ae_pos_finite_bound δ _ Ea).
    apply (ball_weaken_le (ε + (δ + q + δ) + ε) _ _); [| apply _ |].
    * destruct (dense X y₁ δ) as [x₁[??]].
      destruct (dense X y₂ δ) as [x₂[??]].
      apply (ball_triangle _ _ _ (f x₂) _); [| apply_cont Cf δ ].
      apply (ball_triangle _ _ _ (f x₁) _); [apply_cont Cf δ |].
      rewrite <-(isometric (f:X ⇀ Z) (δ + q + δ) _ _).
      apply (ball_triangle _ _ _ y₂ _); trivial.
      apply (ball_triangle _ _ _ y₁ _); trivial. subsymmetry.
    * subtransitivity (q + 2*ε + 2*δ). apply (eq_le _ _). subring Q.
      subtransitivity (q + 2*ε + 2*ε); [| apply (eq_le _ _); subst ε; subfield Q].
      apply (order_preserving (_ +) _ _).
      now apply (order_preserving (2 *.) _ _).
  + intro. apply (ball_closed _ _ _). intros a ?.
    set (ε := a/(2*2)). assert (ε ∊ Q₊) by (subst ε; apply _).
    destruct (uniform_continuity f ε) as [b [el Cf]].
    set_min δ ε b Ea Eb; pose proof (ae_pos_finite_bound δ _ Ea).
    apply (ball_weaken_le (δ + (ε + q + ε) + δ) _ _); [| apply _ |].
    * destruct (dense X y₁ δ) as [x₁[??]].
      destruct (dense X y₂ δ) as [x₂[??]].
      apply (ball_triangle _ _ _ x₂ _); [| subsymmetry].
      apply (ball_triangle _ _ _ x₁ _); trivial.
      rewrite (isometric (f:X ⇀ Z) (ε + q + ε) _ _).
      apply (ball_triangle _ _ _ (f y₂) _); [| apply_cont Cf δ ].
      apply (ball_triangle _ _ _ (f y₁) _); trivial. apply_cont Cf δ.
    * subtransitivity (q + 2*ε + 2*δ). apply (eq_le _ _). subring Q.
      subtransitivity (q + 2*ε + 2*ε); [| apply (eq_le _ _); subst ε; subfield Q].
      apply (order_preserving (_ +) _ _).
      now apply (order_preserving (2 *.) _ _).
  Qed.

  Context `{!PrelengthMetricSpace X}.
  Lemma extend_modulus_of_uniform_continuity q `{q ∊ Q₊} p `{p ∊ Q∞₊} :
    ( ∀ `{x₁ ∊ X} `{x₂ ∊ X}, ball p x₁ x₂ → ball q (f x₁) (f x₂) )
  → ( ∀ `{y₁ ∊ Y} `{y₂ ∊ Y}, ball p y₁ y₂ → ball q (f y₁) (f y₂) ).
  Proof. intro Cf. intros. apply (ball_closed _ _ _). intros a ?.
    set (ε := a/3). assert (ε ∊ Q₊) by (subst ε; apply _).
    destruct (uniform_continuity f ε) as [b [el Cf']].
    pose proof (_ : b/3 ∊ Q∞₊). set_min δ 1 (b/3) Ea Eb. pose proof (ae_pos_finite_bound δ _ Ea).
    destruct (dense X y₁ δ) as [x₁[el' ?]].
    destruct (dense X y₂ δ) as [x₂[el'' ?]].
    assert (δ ≤ b). destruct (ae_decompose_pos b) as [E|?]. rewrite (_ $ E). exact (ae_inf_ub _).
      subtransitivity (b/3). rewrite <-(mult_inv_le_cancel_l _ _ _).
      apply (flip_nonneg_minus _ _). mc_replace (b*3-b) with (2*b) on Q by subring Q. apply _.
    apply (ball_weaken_le (ε+(q+ε)+ε) _ _); try apply _.
    apply (ball_triangle _ _ _ (f x₂) _); [| apply_cont Cf' δ ].
    apply (ball_triangle _ _ _ (f x₁) _). apply_cont Cf' δ.
    destruct (ae_decompose_pos p) as [Ep|?].
      apply (ball_weaken_plus _ _ _); try apply _. apply (Cf _ _ _ _). rewrite (_ $ Ep). exact (msp_ball_inf _ _).
    destruct (prelength x₁ x₂ (δ+p+δ) p b) as [x[?[??]]].
    + destruct (ae_decompose_pos b) as [E|?].
        rewrite (_ $ E), (_ $ ae_nonneg_plus_inf_r _). exact (ae_inf_sub _).
      rewrite (_ $ commutativity (+) _ p), <-(_ $ associativity (+) _ _ _).
      apply (strictly_order_preserving (p+) _ _).
      apply (lt_le_trans _ (δ+δ+δ) _). exact (pos_plus_lt_compat_r _ _).
      subtransitivity (δ*3). apply (eq_le _ _). subring Q.
      now rewrite (mult_inv_le_cancel_r _ _ _).
    + apply (ball_triangle _ _ _ y₂ _); trivial.
      apply (ball_triangle _ _ _ y₁ _); trivial. subsymmetry.
    + apply (ball_triangle _ _ _ (f x) _). now apply Cf. now apply (Cf' _ _ _ _).
    + apply (eq_le _ _). subst ε. subfield Q.
  Qed.

End ufm_continuous_equal_on_dense.

Section ufm_continuous_equal_on_dense_image.
  Context `{MetricSpace (X:=X)} `{MetricSpace (X:=Y)} `{MetricSpace (X:=Z)}.
  Context (k:X ⇀ Y) `{!Morphism (X ⇒ Y) k} `{!Dense Y k⁺¹(X)}.
  Context f g `{!(Y==>Z) f} `{!(Y==>Z) g}.

  Lemma ufm_cont_equal_on_dense_image : f ∘ k = g ∘ k ↔ f = g.
  Proof.
    rewrite <-(ufm_cont_equal_on_dense _ _ k⁺¹(X)). split.
  + intro E. intros ?? [[ [?[?[? Ex]]] [??] ] E2].
    red_sig. rewrite <-(_ $ E2), <-(_ $ Ex). apply E. now red_sig.
  + intro E. intros ?? E2. unfold_sigs. red_sig. unfold compose.
    rewrite <-(_ $ E2). apply E. now red_sig.
  Qed.

  Lemma ufm_cont_equal_on_dense_image_applied : (∀ `{x ∊ X}, f (k x) = g (k x)) → f = g.
  Proof. intro P.
    apply ufm_cont_equal_on_dense_image.
    intros ?? E. unfold_sigs. red_sig. unfold compose. rewrite <- (_ $ E). now apply P.
  Qed.

End ufm_continuous_equal_on_dense_image.

Section ufm_cont_ext_unique.
  Context `{MetricSpace (X:=X₁)} `{MetricSpace (X:=X₂)}.
  Context (g:X₁ ⇀ X₂) `{!Isometry X₁ X₂ g} `{!Dense X₂ g⁺¹(X₁)}.
  Context `{MetricSpace (X:=Y₁)} `{CompleteMetricSpace (X:=Y₂)}.
  Context (h:Y₁ ⇀ Y₂) `{!Isometry Y₁ Y₂ h}.
  Context `{MetricSpace (X:=M)}.
  Context (m:(X₁==>Y₁) ⇀ M) `{!Isometry (X₁==>Y₁) M m} `{!Dense M m⁺¹(X₁==>Y₁)}.

  Notation "#" := (ufm_cont_extension g h m).

  Lemma ufm_cont_ext_unique f `{f ∊ M} (cf:X₂ ⇀ Y₂) `{!UniformlyContinuous X₂ Y₂ cf}
  : (∀ `{q ∊ Q⁺} `{f' ∊ X₁ ==> Y₁}, ball q (m f') f ↔ ball q (h ∘ f') (cf ∘ g) )
    → cf = # f.
  Proof. intro P.
    apply (ufm_cont_equal_on_dense_image g _ _).
    apply (equal_by_ball_closed (X:=X₁ ⇒ Y₂)  _ _). intros q ?.
    destruct (dense m⁺¹(X₁ ==> Y₁) f (q/2)) as [fm [[? [f' [Cf Ef]]] Bf]]. red in Cf.
    rewrite <-(_ $ Ef) in Bf. subsymmetry in Bf.
    mc_replace q with (q/2+q/2) on Q by subfield Q.
    pose proof _ : q/2 ∊ Q₊ .
    apply (ball_triangle (X:=X₁ ⇒ Y₂) _ _ _ (h ∘ f') _).
    subsymmetry. now rewrite <-(P (q/2) _ f' _).
    now rewrite <-(ufm_cont_ext_extends g h m (q/2) f f').
  Qed.

  Lemma ufm_cont_ext_unique_2 f `{!UniformlyContinuous X₁ Y₁ f}
    (cf:X₂ ⇀ Y₂) `{!UniformlyContinuous X₂ Y₂ cf}
  : cf ∘ g = h ∘ f → cf = # (m f).
  Proof. intro E. apply (ufm_cont_equal_on_dense_image g _ _).
    transitivity (h ∘ f). exact E. symmetry. exact (ufm_cont_ext_extends_2 _ _ _ _).
  Qed.

  Lemma ufm_cont_ext_proper f₁ `{f₁ ∊ M} f₂ `{f₂ ∊ M} :
    f₁ = f₂ → # f₁ = # f₂ .
  Proof. intro E. apply (ufm_cont_ext_unique _ _). intros q ? f' Cf. red in Cf.
    rewrite <- (_ $ E). exact (ufm_cont_ext_extends g h m q f₁ f').
  Qed.

  Instance ufm_cont_ext_isometry: Isometry M (X₂ ==> Y₂) #.
  Proof. split; try apply _.
  + intros f1 f2 E. unfold_sigs. red_sig. now apply (ufm_cont_ext_proper _ _).
  + intros q ? f₁ ? f₂ ?.
    rewrite <-(ufm_cont_ball_on_dense _ _ g⁺¹(X₁) _).
    transitivity (ball q (# f₁ ∘ g) (# f₂ ∘ g)).
    * split.
      - intro. apply (ball_closed (X:=X₁ ⇒ Y₂) _ _ _). intros b ?.
        set (a:=b/(2*2)). assert (a ∊ Q₊). subst a. apply _.
        destruct (dense m⁺¹(X₁ ==> Y₁) f₁ a) as [fm [[? [f₁' [Cf1 Ef1]]] Bf1]].
        destruct (dense m⁺¹(X₁ ==> Y₁) f₂ a) as [fm'[[? [f₂' [Cf2 Ef2]]] Bf2]].
        red in Cf1,Cf2. rewrite <-(_ $ Ef1) in Bf1. rewrite <-(_ $ Ef2) in Bf2.
        clear dependent fm. clear dependent fm'. subsymmetry in Bf1. subsymmetry in Bf2.
        mc_replace (q+b) with (a+(a+q+a)+a) on Q by (subst a; subfield Q).
        apply (ball_triangle (X:=X₁ ⇒ Y₂) _ _ _ (h ∘ f₂') _).
        apply (ball_triangle (X:=X₁ ⇒ Y₂) _ _ _ (h ∘ f₁') _).
        subsymmetry. now rewrite <-(ufm_cont_ext_extends g h m a f₁ f₁').
        pose proof (isometric (X:=X₁ ==> Y₁) (h ∘) (a+q+a) f₁' f₂') as P.
          rewrite <-P. clear P.
        rewrite (isometric m _ _ _).
        apply (ball_triangle _ _ _ f₂ _); [|subsymmetry].
        now apply (ball_triangle _ _ _ f₁ _).
        now rewrite <-(ufm_cont_ext_extends g h m a f₂ f₂').
      - intro. apply (ball_closed _ _ _). intros b ?.
        set (a:=b/(2*2)). assert (a ∊ Q₊). subst a. apply _.
        destruct (dense m⁺¹(X₁ ==> Y₁) f₁ a) as [fm [[? [f₁' [Cf1 Ef1]]] Bf1]].
        destruct (dense m⁺¹(X₁ ==> Y₁) f₂ a) as [fm'[[? [f₂' [Cf2 Ef2]]] Bf2]].
        red in Cf1,Cf2. rewrite <-(_ $ Ef1) in Bf1. rewrite <-(_ $ Ef2) in Bf2.
        clear dependent fm. clear dependent fm'. subsymmetry in Bf1. subsymmetry in Bf2.
        mc_replace (q+b) with (a+(a+q+a)+a) on Q by (subst a; subfield Q).
        apply (ball_triangle _ _ _ (m f₂') _); trivial.
        apply (ball_triangle _ _ _ (m f₁') _). subsymmetry.
        rewrite <-(isometric m _ _ _).
        pose proof (isometric (X:=X₁ ==> Y₁) (h ∘) (a+q+a) f₁' f₂') as P.
          rewrite P. clear P.
        apply (ball_triangle (X:=X₁ ⇒ Y₂) _ _ _ (#f₂ ∘ g) _).
        apply (ball_triangle (X:=X₁ ⇒ Y₂) _ _ _ (#f₁ ∘ g) _); trivial.
        now rewrite <-(ufm_cont_ext_extends g h m a f₁ f₁').
        subsymmetry. now rewrite <-(ufm_cont_ext_extends g h m a f₂ f₂').
    * split; ( intros [? P]; split; [apply _ |] ).
        intros y [?[x[? E]]]. rewrite <-(_ $ E). exact (P _ _).
        intros x ?. exact (P _ _).
  Qed.

  (*
  Lemma cont_ext_preserves_isometry (f:X ⇀ Z) `{!Isometry X Z f}
  : Isometry Y Z (continuous_extension h f).
  Proof. apply (extend_isometry _ h⁺¹(X)). split; try apply _.
    exact sub_metric_space.
    rewrite <-(_:SubsetOf (Y ⇒ Z) (h⁺¹(X) ⇒ Z)). apply _.
    intros q ? y1 [?[x1[? E1]]] y2 [?[x2[? E2]]].
    rewrite <-(_ $ E1), <-(_ $ E2).
    rewrite 2!(_ $ cont_ext_extends_applied _ _ _).
    rewrite <-(isometric h _ _ _). exact (isometric f _ _ _).
  Qed.
  *)

End ufm_cont_ext_unique.

Hint Extern 2 (Isometry _ _ (ufm_cont_extension _ _ _)) => eapply @ufm_cont_ext_isometry : typeclass_instances.
Hint Extern 2 (Morphism _ (ufm_cont_extension _ _ _)) => eapply @isometry_mor : typeclass_instances.


(** The universal property of the completion of a metric space
    follows as a special case of the more general continuous extension above.  *)

Section ufm_lift_to_completion.
  Context `{Completion (X:=X) (X':=Y)} `{CompleteMetricSpace (X:=Z)}.

  Definition ufm_lift_to_completion : (X ==> Z) ⇀ (Y ==> Z)
    := ufm_cont_extension (to_completion X Y) (id:Z ⇀ Z) (id:(X ==> Z) ⇀ (X ==> Z)).

  Hint Unfold ufm_lift_to_completion : typeclass_instances.

  Instance ufm_lift_to_completion_isometry:
    Isometry (X ==> Z) (Y ==> Z) ufm_lift_to_completion
  := _.

  Context (f:X ⇀ Z) `{!UniformlyContinuous X Z f}.

  Instance ufm_lift_to_completion_mor : Morphism (Y ⇒ Z) (ufm_lift_to_completion f) := _.
  Instance ufm_lift_to_completion_cont : UniformlyContinuous Y Z (ufm_lift_to_completion f) := _.

  Lemma ufm_lift_to_completion_extends : (ufm_lift_to_completion f) ∘ (to_completion X Y) = f.
  Proof ufm_cont_ext_extends_2 _ id (id:(X ==> Z) ⇀ (X ==> Z)) _.

  Lemma ufm_lift_to_completion_unique (g:Y ⇀ Z) `{!UniformlyContinuous Y Z g}
  : g ∘ (to_completion X Y) = f → g = ufm_lift_to_completion f.
  Proof ufm_cont_ext_unique_2 (to_completion X Y) id (id:(X ==> Z) ⇀ (X ==> Z)) _ _.

End ufm_lift_to_completion.

Hint Extern 2 (Morphism _ (ufm_lift_to_completion _)) => eapply @ufm_lift_to_completion_mor : typeclass_instances.
Hint Extern 2 (UniformlyContinuous _ _ (ufm_lift_to_completion _)) => eapply @ufm_lift_to_completion_cont : typeclass_instances.
Hint Extern 2 (Isometry _ _ ufm_lift_to_completion) => eapply @ufm_lift_to_completion_isometry : typeclass_instances.

Section ufm_completion_map.
  Context `{Completion (X:=X) (X':=CX)}.
  Context `{Completion (X:=Y) (X':=CY)}.

  Notation g := (to_completion X CX).
  Notation h := (to_completion Y CY).

  Definition ufm_completion_map : (X ==> Y) ⇀ (CX ==> CY)
    := ufm_lift_to_completion ∘ (h ∘).

  Hint Unfold ufm_completion_map : typeclass_instances.

  Instance ufm_completion_map_isometry:
    Isometry (X ==> Y) (CX ==> CY) ufm_completion_map := _.

  Context (f:X ⇀ Y) `{!UniformlyContinuous X Y f}.

  Instance ufm_completion_map_mor : Morphism (CX ⇒ CY) (ufm_completion_map f).
  Proof. unfold ufm_completion_map, compose at 1. apply _. Qed.

  Instance ufm_completion_map_cont : UniformlyContinuous CX CY (ufm_completion_map f).
  Proof. unfold ufm_completion_map, compose at 1. apply _. Qed.

  Lemma ufm_completion_map_extends : (ufm_completion_map f) ∘ g = h ∘ f.
  Proof ufm_lift_to_completion_extends _.

  Lemma ufm_completion_map_unique (cf:CX ⇀ CY) `{!UniformlyContinuous CX CY cf}
  : cf ∘ g = h ∘ f → cf = (ufm_completion_map f).
  Proof ufm_lift_to_completion_unique _ _.

End ufm_completion_map.

Hint Extern 2 (Morphism _ (ufm_completion_map _)) => eapply @ufm_completion_map_mor : typeclass_instances.
Hint Extern 2 (UniformlyContinuous _ _ (ufm_completion_map _)) => eapply @ufm_completion_map_cont : typeclass_instances.
Hint Extern 2 (Isometry _ _ ufm_completion_map) => eapply @ufm_completion_map_isometry : typeclass_instances.

Section complete_ufm_fun_space.
  Context `{MetricSpace (X:=X)} `{CompleteMetricSpace (X:=Y)}.

  Notation C := (CauchyNets (X==>Y)).
  Notation m := (to_completion (X==>Y) C).

  Instance ufm_fun_space_limit : Limit (X==>Y)
    := ufm_cont_extension (id:X ⇀ X) (id:Y ⇀ Y) m.

  Instance ufm_fun_space_complete : CompleteMetricSpace (X==>Y).
  Proof. split; unfold limit, ufm_fun_space_limit; try apply _.
    intros S ? p ? f ?. pose proof _ : f ∊ X==>Y as Cf. red in Cf.
    setoid_rewrite <-(ufm_cont_ext_extends id id m p S f).
    subsymmetry. exact (net_const_dist _ _ _).
  Qed.
End complete_ufm_fun_space.
Hint Extern 2 (Limit (_ ==> _)) => eapply @ufm_fun_space_limit : typeclass_instances.
Hint Extern 2 (CompleteMetricSpace (_ ==> _)) => eapply @ufm_fun_space_complete : typeclass_instances.

Section complete_prod_space.
  Context `{CompleteMetricSpace (X:=X)} `{CompleteMetricSpace (X:=Y)}.

  Notation C := (CauchyNets (X * Y)).

  Notation fst' := (ufm_lift_to_completion (X:=X*Y) (Y:=C) fst).
  Notation snd' := (ufm_lift_to_completion (X:=X*Y) (Y:=C) snd).

  Instance prod_space_limit : Limit (X * Y) := λ S, (fst' S, snd' S).

  Notation g := (to_completion (X * Y) C).

  Instance prod_space_complete : CompleteMetricSpace (X*Y).
  Proof. split; unfold limit, prod_space_limit; try apply _.
  + intros ?? E. unfold_sigs. red_sig. now rewrite (_ $ E).
  + intros S ?. intros ?? x ?.
    apply (ball_closed (X:=X*Y) _ _ _). intros ε ?.
    destruct (uniform_continuity fst' (ε/2)) as [a[el C1]].
    destruct (uniform_continuity snd' (ε/2)) as [b[el' C2]].
    set_min c a b Ea Eb. set_min δ c (ε/2) Ec E.
    pose proof (ae_pos_finite_bound δ _ E).
    destruct (cauchy_net_inhabited (S:=S) δ) as [y ?].
    assert (p+ε/2+ε/2 ≤ p+ε) as Ep by (apply (eq_le _ _); subfield Q).
    apply (ball_weaken_le (X:=X*Y) (p+ε/2+ε/2) _ _); trivial; try apply _.
    apply (ball_triangle (X:=X*Y) _ _ _ (fst' (g y), snd' (g y)) _).
    * setoid_rewrite (ufm_lift_to_completion_extends (X:=X*Y) (Y:=C) fst y y (_:Proper (X*Y,=) y)).
      setoid_rewrite (ufm_lift_to_completion_extends (X:=X*Y) (Y:=C) snd y y (_:Proper (X*Y,=) y)).
      apply (ball_weaken_le (X:=X*Y) (p+δ) _ _); trivial; try apply _.
      apply (cauchy_net_def (X:=X*Y) _ _ _). now destruct y.
      now apply (order_preserving (p+) _ _).
    * split; simpl.
      - apply (C1 _ _ _ _). apply (ball_weaken_le δ _ _); try apply _.
        subsymmetry. apply (net_const_dist _ _ _).
        apply (subtransitivity (S:=Q∞)) with c; trivial; apply _.
      - apply (C2 _ _ _ _). apply (ball_weaken_le δ _ _); try apply _.
        subsymmetry. apply (net_const_dist _ _ _).
        apply (subtransitivity (S:=Q∞)) with c; trivial; apply _.
  Qed.
End complete_prod_space.
Hint Extern 2 (Limit (prod_subset _ _)) => eapply @prod_space_limit : typeclass_instances.
Hint Extern 2 (CompleteMetricSpace (prod_subset _ _)) => eapply @prod_space_complete : typeclass_instances.

Section prod_space_completion.
  Context `{Completion (X:=X) (X':=CX)}.
  Context `{Completion (X:=Y) (X':=CY)}.
  Notation g := (to_completion X CX).
  Notation h := (to_completion Y CY).

  Instance to_prod_space_completion : ToCompletion (X*Y) (CX*CY)
    := prod_map g h.

  Instance prod_space_completion : Completion (X*Y) (CX*CY).
  Proof. split; unfold to_completion, to_prod_space_completion; try apply _.
  + split; try apply _.
    intros ??????. split; intros [??].
      split; simpl. now rewrite <-(isometric g _ _ _). now rewrite <-(isometric h _ _ _).
      split. now rewrite (isometric g _ _ _). now rewrite (isometric h _ _ _).
  + split; try apply _. split. now intros [??]. intro. split. apply _. intros ε ?.
    destruct (dense g⁺¹(X) (fst x) ε) as [x' [[?[a [? Ea]]] Ba]]. rewrite <-(_ $ Ea) in Ba.
    destruct (dense h⁺¹(Y) (snd x) ε) as [y' [[?[b [? Eb]]] Bb]]. rewrite <-(_ $ Eb) in Bb.
    exists_sub (g a, h b). now split.
  Qed.

End prod_space_completion.
Hint Extern 2 (ToCompletion (_ * _) (_ * _)) => eapply @to_prod_space_completion : typeclass_instances.
Hint Extern 2 (Completion (_ * _) (_ * _)) => eapply @prod_space_completion : typeclass_instances.

Section ufm_completion_map_2.
  Context `{Completion (X:=X) (X':=CX)}.
  Context `{Completion (X:=Y) (X':=CY)}.
  Context `{Completion (X:=Z) (X':=CZ)}.

  Notation g := (to_completion X CX).
  Notation h := (to_completion Y CY).
  Notation k := (to_completion Z CZ).

  Definition ufm_completion_map_2 : (X==>Y==>Z) ⇀ (CX==>CY==>CZ)
    := ufm_cont_extension g ufm_completion_map id.

  Hint Unfold ufm_completion_map_2 : typeclass_instances.

  Instance ufm_completion_map_2_isometry:
    Isometry (X==>Y==>Z) (CX==>CY==>CZ) ufm_completion_map_2 := _.

  Context (f:X ⇀ Y ⇀ Z) `{!(X==>Y==>Z) f}.

  Instance: Morphism (X ⇒ Y ⇒ Z) f.
  Proof. rewrite <-(_ : SubsetOf (X ⇒ Y ==> Z) (X ⇒ Y ⇒ Z)). apply _. Qed.

  Instance ufm_completion_map_2_mor : Morphism (CX ⇒ CY ⇒ CZ) (ufm_completion_map_2 f).
  Proof. rewrite <-(_ : SubsetOf (CX ⇒ CY ==> CZ) (CX ⇒ CY ⇒ CZ)). apply _. Qed.

  Instance ufm_completion_map_2_cont : (CX==>CY==>CZ) (ufm_completion_map_2 f) := _.

  Lemma ufm_completion_map_2_extends x `{x ∊ X} y `{y ∊ Y}
    : (ufm_completion_map_2 f) (g x) (h y) = k (f x y).
  Proof. 
    pose proof _ : (f x) ∊ (Y ==> Z) as Cfx. red in Cfx.
    subtransitivity (ufm_completion_map (f x) (h y)).
    + pose proof (ufm_cont_ext_extends_2 g ufm_completion_map id f x x (_:Proper (X,=) x)) as E.
      unfold_sigs. apply (E (h y) (h y)). now red_sig.
    + change ((ufm_completion_map (f x) ∘ h) y = (k ∘ (f x)) y).
      apply (ufm_completion_map_extends _). now red_sig.
  Qed.

(*  Lemma completion_map_unique (cf:CX ⇀ CY) `{!UniformlyContinuous CX CY cf}
  : cf ∘ g = h ∘ f → cf = (completion_map f).
  Proof lift_to_completion_unique _ _. *)

End ufm_completion_map_2.
Hint Extern 2 (Morphism _ (ufm_completion_map_2 _)) => eapply @ufm_completion_map_2_mor : typeclass_instances.
Hint Extern 2 (UniformlyContinuous _ _ (ufm_completion_map_2 _)) => eapply @ufm_completion_map_2_cont : typeclass_instances.
Hint Extern 2 (Isometry _ _ ufm_completion_map_2) => eapply @ufm_completion_map_2_isometry : typeclass_instances.

