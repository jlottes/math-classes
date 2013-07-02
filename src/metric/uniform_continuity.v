Require Import
  abstract_algebra interfaces.orders interfaces.rationals interfaces.metric_spaces
  theory.setoids theory.jections theory.fields theory.rationals
  orders.affinely_extended_field stdlib_field
  orders.minmax orders.lattices
  metric.metric_spaces metric.maps prelength cauchy_completion
  theory.products metric.products.

Local Notation AQ := TheAERationals.A.
Local Notation Q := the_ae_rationals.
Local Notation "Q∞" := (aff_ext Q).
Local Notation Qfull := (aff_ext_full Q).




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

Section ufm_continuous_extension.
  Context `{MetricSpace (X:=X₁)} `{MetricSpace (X:=X₂)}.
  Context (g:X₁ ⇀ X₂) `{!Isometry X₁ X₂ g} `{!Dense (X:=X₂) g⁺¹(X₁)}.
  Context `{MetricSpace (X:=Y₁)} `{CompleteMetricSpace (X:=Y₂)}.
  Context (h:Y₁ ⇀ Y₂) `{!Isometry Y₁ Y₂ h}.
  Context `{MetricSpace (X:=M)}.
  Context (m:(X₁==>Y₁) ⇀ M) `{!Isometry (X₁==>Y₁) M m} `{!Dense (X:=M) m⁺¹(X₁==>Y₁)}.

  Hint Extern 0 AmbientSpace => eexact X₂ : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact M  : typeclass_instances.

  Section def.

    Context f `{f ∊ M}.

    Notation C := (CauchyNets Y₁).

    Let proj_ball q x : Subset := X₁ ⊓ (λ x', ball q x (g x')).

    Definition ufm_cont_ext_net : X₂ ⇀ C := λ x, net (λ q y,
      ∃ `{a ∊ Q∞⁺} `{b ∊ Q∞⁺}, a + b ≤ q 
        ∧ ∃ (f':X₁ ⇀ Y₁) `{f' ∊ (X₁==>Y₁)}, ball a (m f') f
          ∧ ∃ `{p ∊ Q∞₊} `{ε ∊ Q∞₊},
              (∀ `{x₁ ∊ X₁} `{x₂ ∊ X₁}, ball (p+ε) x₁ x₂ → ball b (f' x₁) (f' x₂))
              ∧ y ∊ f'⁺¹(proj_ball p x)
    ).

    Notation S := ufm_cont_ext_net.

    Instance: ∀ x `{x ∊ X₂} `{q ∊ Q∞⁺}, proj_ball q x ⊆ X₁.
    Proof. unfold proj_ball. intros. apply subsetoid_alt. apply _.
    + intros ?? E [??]. unfold_sigs. split. apply _. red. now rewrite <- (_ $ E).
    + firstorder.
    Qed.

    Instance: ∀ x `{x ∊ X₂} `{q ∊ Q∞⁺}, S x q ⊆ Y₁.
    Proof with intuition. intros. apply subsetoid_alt. apply _.
    + intros z1 z2 Ez [a[?[b[?[Eab [f'[Cf[Ef [p[?[ε[?[??]]]]] ]]] ]]]]].
      exists_sub a b... exists_sub f'... exists_sub p ε...
      red in Cf. now rewrite <-Ez.
    + now intros z [a[?[b[?[Eab [f'[Cf[Ef [p[?[ε[?[?[??]]]]]] ]]] ]]]]].
    Qed.

    Instance: ∀ x `{x ∊ X₂} `{q ∊ Q∞⁺}, Setoid (S x q).
    Proof. intros. exact subsetoid_a. Qed.

    Lemma ufm_cont_ext_net_proper_1 x `{x ∊ X₂} p `{p ∊ Q∞⁺} q `{q ∊ Q∞⁺} : p = q →
        ∀ `{z ∊ S x p}, z ∊ S x q.
    Proof. intros E z [a[?[b[?[Eab ?]]]]]. rewrite (_ $ E) in Eab.
      exists_sub a b. intuition.
    Qed.

    Lemma ufm_cont_ext_net_proper_2 x₁ `{x₁ ∊ X₂} x₂ `{x₂ ∊ X₂} : x₁ = x₂  →
      S x₁ = S x₂.
    Proof. intro E.
      intros q₁ ? q₂ ? y₁ [a₁[el [b₁[elb1[Eab₁ [f₁[Cf₁[Ef₁ [p₁[elp1[e₁[ele1[c₁[elc1[x₁'[[??]Ey₁]]]]]]]] ]]] ]]]]].
      intros           y₂ [a₂[el'[b₂[elb2[Eab₂ [f₂[Cf₂[Ef₂ [p₂[elp2[e₂[ele2[c₂[elc2[x₂'[[??]Ey₂]]]]]]]] ]]] ]]]]].
      destruct (ae_nonneg_sum_finite_bound _ _ _ Eab₁).
      destruct (ae_nonneg_sum_finite_bound _ _ _ Eab₂).
      subsymmetry in Ef₂.
      pose proof (ball_triangle a₁ a₂ (m f₁) f (m f₂) Ef₁ Ef₂) as Ef. clear Ef₁ Ef₂.
      rewrite <-(isometric m _ _ _) in Ef. destruct Ef as [_ Ef].
      red in Cf₁,Cf₂.
      rewrite <-(_ $ Ey₁), <-(_ $ Ey₂).
      ae_rat_set_min ε e₁ e₂ Ee1 Ee2.
      destruct (dense_image g X₁ x₁ ε) as [x [? B1]].
      assert (ball ε x₂ (g x)) as B2 by now rewrite <-(X₂ $ E).
      assert (b₁ + (a₁ + a₂) + b₂ ≤ q₁ + q₂) as Er.
        subtransitivity ((a₁+b₁) + (a₂+b₂)). apply (eq_le _ _). subring Q.
        now apply (plus_le_compat _ _ _ _).
      rewrite <-(Qfull $ Er).
      apply (ball_triangle _ _ _ (f₂ x) _).
      apply (ball_triangle _ _ _ (f₁ x) _).
      + apply (c₁ _ _ _ _). rewrite (isometric g _ _ _).
        apply (ball_triangle _ _ _ x₁ _). subsymmetry.
        now rewrite <-(Qfull $ Ee1).
      + now apply Ef.
      + apply (c₂ _ _ _ _). rewrite (isometric g _ _ _). subsymmetry.
        apply (ball_triangle _ _ _ x₂ _). subsymmetry.
        now rewrite <-(Qfull $ Ee2).
    Qed.

    Instance: ∀ x `{x ∊ X₂}, S x ∊ C.
    Proof. intros. split. apply _.
    + intros ?? E. unfold_sigs. red_sig.
      split; apply ufm_cont_ext_net_proper_1; trivial; try apply _. subsymmetry.
    + intros q ?. destruct (dense_image m (X₁ ==> Y₁) f (q/2)) as [f'[Cf Bf]]. red in Cf.
      destruct (uniform_continuity_alt f' (q/2)) as [p[el[ε[el' Pc]]]].
      destruct (dense_image g X₁ x p) as [x'[? B1]].
      exists (f' x'). pose proof (_ : q/2 ∊ Q∞₊).
      exists_sub (q/2) (q/2). split. now rewrite (_ $ ae_in_halves _).
      exists_sub f'. split. subsymmetry.
      exists_sub p ε. unfold proj_ball.
      split. exact Pc. apply _.
    + now apply ufm_cont_ext_net_proper_2.
    Qed.

    Instance ufm_cont_ext_net_mor : Morphism (X₂ ⇒ C) S.
    Proof. intros ???. unfold_sigs. red_sig. now apply ufm_cont_ext_net_proper_2. Qed.

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
    ae_rat_set_min θ (c/2) (ε/2) Ec E; pose proof (ae_pos_finite_bound θ _ E).
    destruct (dense_image g X₁ y₁ θ) as [x₁[? B1]].
    destruct (dense_image g X₁ y₂ θ) as [x₂[? B2]].
    pose proof _ : δ/2 ∊ Q∞₊ .
    assert (f' x₁ ∊ S y₁ (a+δ/2)).
      exists_sub a (δ/2). split. subreflexivity.
      exists_sub f'. split. trivial.
      exists_sub (c/2) (c/2). split. now apply (uniform_continuity_half f' _ c).
      cut (g x₁ ∊ ball (c / 2) y₁). intro. apply _.
      red. now rewrite <-(Qfull $ Ec).
    assert (f' x₂ ∊ S y₂ (a+δ/2)).
      exists_sub a (δ/2). split. subreflexivity.
      exists_sub f'. split. trivial.
      exists_sub (c/2) (c/2). split. now apply (uniform_continuity_half f' _ c).
      cut (g x₂ ∊ ball (c / 2) y₂). intro. apply _.
      red. now rewrite <-(Qfull $ Ec).
    apply (ball_triangle _ _ _ (h (f' x₂)) _); [| now apply (map_limit_spec _ _ _ _)].
    apply (ball_triangle _ _ _ (h (f' x₁)) _). subsymmetry. now apply (map_limit_spec _ _ _ _).
    rewrite <-(isometric h _ _ _). apply (Cb _ _ _ _).
    assert (θ + (p-ε) + θ ≤ p) as Er.
      destruct (ae_decompose_pos p) as [E'|?].
        rewrite (_ $ E'). rewrite (_ $ ae_inf_plus_fin _).
        pose proof _ : θ + ∞ + θ ∊ Q∞₊. exact (ae_inf_ub _).
      rewrite <-(mult_inv_le_cancel_r _ _ _) in E.
      mc_replace (θ + (p - ε) + θ) with (p + θ*2 - ε) on Q by subring Q.
      rewrite (flip_le_minus_l _ _ _). now apply (order_preserving (p+) _ _).
    apply (ball_weaken_le (θ + (p-ε) + θ) _ _); trivial; try apply _.
    rewrite (isometric g _ _ _).
    apply (ball_triangle _ _ _ y₂ _); trivial.
    apply (ball_triangle _ _ _ y₁ _); [ subsymmetry | trivial].
  Qed.

  Instance ufm_cont_ext_cont : UniformlyContinuous X₂ Y₂ cf.
  Proof. split; try apply _. intros q ?.
    destruct (dense_image m (X₁ ==> Y₁) f (q/3)) as [f'[Cf Bf]].
    subsymmetry in Bf. red in Cf.
    destruct (uniform_continuity f' (q/3)) as [p[el Pc]].
    assert (q = q/3+q/3+q/3) as Eq by subfield Q.
    destruct (ae_decompose_pos p) as [E|?].
      exists_sub ∞. intros y1 ? y2 ? ?. rewrite (_ $ Eq).
      apply (ufm_cont_ext_cont_nearly _ _ ∞ f' Bf) with 1; trivial; try apply _.
      intros. apply (Pc _ _ _ _). now rewrite (_ $ E).
      now rewrite (_ $ ae_inf_plus_fin _).
    exists_sub (p/2). intros. rewrite (_ $ Eq).
    apply (ufm_cont_ext_cont_nearly _ _ p f' Bf) with (p/2); trivial; try apply _.
    now mc_replace (p-p/2) with (p/2) on Q by subfield Q.
  Qed.

  End continuity.

  Lemma ufm_cont_ext_extends q `{q ∊ Q⁺} f `{f ∊ M} f' `{!UniformlyContinuous X₁ Y₁ f'} :
    ball q (m f') f ↔ ball q (h ∘ f') (ufm_cont_extension f ∘ g).
  Proof.
    assert (∀ `{p ∊ Q⁺} `{r ∊ Q₊} f'' `{!UniformlyContinuous X₁ Y₁ f''} `{x ∊ X₁},
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
    destruct (dense_image m (X₁ ==> Y₁) f (ε/3)) as [f₂[Cf Bf]]. red in Cf.
    mc_replace (q + ε) with (q + (ε/3+ε/3) + ε/3) on Q by subfield Q.
    apply (ball_triangle _ _ _ (m f₂) _); try solve [ subsymmetry ].
    rewrite <-(isometric m _ _ _).
    pose proof _ : ε/3 ∊ Q₊ . pose proof _ : q + (ε/3+ε/3) ∊ Q₊ .
    split. apply _. intros x ?. rewrite (isometric h _ _ _).
    apply (ball_triangle _ _ _ (ufm_cont_extension f (g x)) _).
    now apply P.
    assert (f₂ x ∊ ufm_cont_ext_net f (g x) (ε/3+ε/3)).
      apply Pel; trivial. apply _. subsymmetry.
    unfold ufm_cont_extension. subsymmetry. apply (map_limit_spec _ _ _ _).
  Qed.

  Lemma ufm_cont_ext_extends_2 f `{!UniformlyContinuous X₁ Y₁ f}
    : ufm_cont_extension (m f) ∘ g = h ∘ f.
  Proof. rewrite <-(ball_separated (X:=X₁ ⇒ Y₂) _ _).
    subsymmetry. now rewrite <-(ufm_cont_ext_extends _ _ _).
  Qed.

  Lemma ufm_cont_ext_strong q `{q ∊ Q⁺} f `{f ∊ M} f' `{!StronglyUniformlyContinuous X₁ Y₁ f'} :
    ball q (m f') f → StronglyUniformlyContinuous X₂ Y₂ (ufm_cont_extension f).
  Proof. intro.
    assert (ball q (h ∘ f') (ufm_cont_extension f ∘ g)) as Bf'.
      apply ufm_cont_ext_extends; trivial; apply _.
    destruct Bf' as [? Bf']. unfold compose in Bf'.
    pose proof (ufm_cont_ext_cont f). split; trivial.
    intros U ??. pose proof _ : U ⊆ X₂ . split; try apply _.
    destruct (bounded U) as [d[eld BU]].
    destruct (inhabited U) as [u ?].
    destruct (dense_image g X₁ u 1) as [x[? Bx]].
    destruct (uniform_continuity (ufm_cont_extension f) 1) as [δ'[elδ Cf']].
    ae_rat_set_min δ δ' 1 Eδ1 Eδ2. pose proof (ae_pos_finite_bound δ _ Eδ2).
    assert (∀ `{x ∊ X₂} `{y ∊ X₂}, ball δ x y
          → ball 1 (ufm_cont_extension f x) (ufm_cont_extension f y)) as Cf.
      intros. apply (Cf' _ _ _ _). now rewrite <-(Qfull $ Eδ1).
    clear Cf' Eδ1 Eδ2.
    pose proof (strongly_ufm_cont X₁ Y₁ (B (X:=X₁) (1+d+δ) x)).
    destruct (bounded (X:=Y₁) f'⁺¹(B (X:=X₁) (1+d+δ) x)) as [s[? Bs]].
    exists_sub (1+q+s+q+1).
    intros ? [?[u1 [? E1]]] ? [?[u2 [? E2]]].
    destruct (dense_image g X₁ u1 δ) as [u1'[? Bu1]].
    destruct (dense_image g X₁ u2 δ) as [u2'[? Bu2]].
    assert (u1' ∊ B (X:=X₁) (1+d+δ) x).
      split; [|apply _]. red. rewrite (isometric g _ _ _).
      apply (ball_triangle _ _ _ u1 _); trivial.
      apply (ball_triangle _ _ _ u _). subsymmetry. now apply BU.
    assert (u2' ∊ B (X:=X₁) (1+d+δ) x).
      split; [|apply _]. red. rewrite (isometric g _ _ _).
      apply (ball_triangle _ _ _ u2 _); trivial.
      apply (ball_triangle _ _ _ u _). subsymmetry. now apply BU.
    apply (ball_triangle _ _ _ (ufm_cont_extension f (g u2')) _).
    apply (ball_triangle _ _ _ (h (f' u2')) _ ).
    apply (ball_triangle _ _ _ (h (f' u1')) _ ).
    apply (ball_triangle _ _ _ (ufm_cont_extension f (g u1')) _).
    rewrite <-(_ $ E1). now apply (Cf _ _ _ _).
    subsymmetry. apply Bf'. apply _.
    rewrite <-(isometric h _ _ _). apply Bs; apply _.
    apply Bf'. apply _.
    rewrite <-(_ $ E2). subsymmetry. now apply (Cf _ _ _ _).
  Qed.

End ufm_continuous_extension.

Hint Extern 2 (Morphism _ (ufm_cont_extension _ _ _ _)) => eapply @ufm_cont_ext_mor : typeclass_instances.
Hint Extern 2 (UniformlyContinuous _ _ (ufm_cont_extension _ _ _ _)) => eapply @ufm_cont_ext_cont : typeclass_instances.

Section ufm_continuous_equal_on_dense.
  Context `{Y:@Subset A} `{Z:Subset} (f:Y ⇀ Z) (g:Y ⇀ Z) (X:@Subset A).
  Context `{MetricSpace _ (X:=Y)}.
  Context `{MetricSpace _ (X:=Z)}.
  Hint Extern 0 AmbientSpace => eexact Y : typeclass_instances.
  Context `{!Dense X}.
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
    ae_rat_set_min δ a b Ea Eb.
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
    ae_rat_set_min δ ε b Ea Eb; pose proof (ae_pos_finite_bound δ _ Ea).
    assert (ε + (δ + q + δ) + ε ≤ q+a) as Er.
      subtransitivity (q + 2*ε + 2*δ). apply (eq_le _ _). subring Q.
      subtransitivity (q + 2*ε + 2*ε); [| apply (eq_le _ _); subst ε; subfield Q].
      apply (order_preserving (_ +) _ _).
      now apply (order_preserving (2 *.) _ _).
    rewrite <-(Qfull $ Er).
    destruct (dense X y₁ δ) as [x₁[??]].
    destruct (dense X y₂ δ) as [x₂[??]].
    apply (ball_triangle _ _ _ (f x₂) _); [| apply_cont Cf δ ].
    apply (ball_triangle _ _ _ (f x₁) _); [apply_cont Cf δ |].
    rewrite <-(isometric (f:X ⇀ Z) (δ + q + δ) _ _).
    apply (ball_triangle _ _ _ y₂ _); trivial.
    apply (ball_triangle _ _ _ y₁ _); trivial. subsymmetry.
  + intro. apply (ball_closed _ _ _). intros a ?.
    set (ε := a/(2*2)). assert (ε ∊ Q₊) by (subst ε; apply _).
    destruct (uniform_continuity f ε) as [b [el Cf]].
    ae_rat_set_min δ ε b Ea Eb; pose proof (ae_pos_finite_bound δ _ Ea).
    assert (δ + (ε + q + ε) + δ ≤ q+a) as Er.
      subtransitivity (q + 2*ε + 2*δ). apply (eq_le _ _). subring Q.
      subtransitivity (q + 2*ε + 2*ε); [| apply (eq_le _ _); subst ε; subfield Q].
      apply (order_preserving (_ +) _ _).
      now apply (order_preserving (2 *.) _ _).
    apply (ball_weaken_le (δ + (ε + q + ε) + δ) _ _); [| apply _ | trivial ] .
    destruct (dense X y₁ δ) as [x₁[??]].
    destruct (dense X y₂ δ) as [x₂[??]].
    apply (ball_triangle _ _ _ x₂ _); [| subsymmetry].
    apply (ball_triangle _ _ _ x₁ _); trivial.
    rewrite (isometric (f:X ⇀ Z) (ε + q + ε) _ _).
    apply (ball_triangle _ _ _ (f y₂) _); [| apply_cont Cf δ ].
    apply (ball_triangle _ _ _ (f y₁) _); trivial. apply_cont Cf δ.
  Qed.

  Context `{!PrelengthSpace X}.
  Lemma extend_modulus_of_uniform_continuity q `{q ∊ Q₊} p `{p ∊ Q∞₊} :
    ( ∀ `{x₁ ∊ X} `{x₂ ∊ X}, ball p x₁ x₂ → ball q (f x₁) (f x₂) )
  → ( ∀ `{y₁ ∊ Y} `{y₂ ∊ Y}, ball p y₁ y₂ → ball q (f y₁) (f y₂) ).
  Proof. intro Cf. intros. apply (ball_closed _ _ _). intros a ?.
    set (ε := a/3). assert (ε ∊ Q₊) by (subst ε; apply _).
    destruct (uniform_continuity f ε) as [b [el Cf']].
    pose proof (_ : b/3 ∊ Q∞₊). ae_rat_set_min δ 1 (b/3) Ea Eb. pose proof (ae_pos_finite_bound δ _ Ea).
    destruct (dense X y₁ δ) as [x₁[el' ?]].
    destruct (dense X y₂ δ) as [x₂[el'' ?]].
    assert (δ ≤ b). destruct (ae_decompose_pos b) as [E|?]. rewrite (_ $ E). exact (ae_inf_ub _).
      subtransitivity (b/3). rewrite <-(mult_inv_le_cancel_l _ _ _).
      apply (flip_nonneg_minus _ _). mc_replace (b*3-b) with (2*b) on Q by subring Q. apply _.
    mc_replace (q+a) with (ε+(q+ε)+ε) on Q by (subst ε; subfield Q).
    apply (ball_triangle _ _ _ (f x₂) _); [| apply_cont Cf' δ ].
    apply (ball_triangle _ _ _ (f x₁) _). apply_cont Cf' δ.
    destruct (ae_decompose_pos p) as [Ep|?].
      apply (ball_weaken_plus _ _ _); try apply _.
      apply (Cf _ _ _ _). rewrite (_ $ Ep). exact (msp_ball_inf _ _).
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
  Qed.

End ufm_continuous_equal_on_dense.

Section ufm_continuous_equal_on_dense_image.
  Context `{MetricSpace (X:=X)} `{MetricSpace (X:=Y)} `{MetricSpace (X:=Z)}.
  Context (k:X ⇀ Y) `{!Morphism (X ⇒ Y) k} `{!Dense (X:=Y) k⁺¹(X)}.
  Context f g `{!UniformlyContinuous Y Z f} `{!UniformlyContinuous Y Z g}.

  Lemma ufm_cont_ball_on_dense_image q `{q ∊ Qfull} : ball q (f ∘ k) (g ∘ k) ↔ ball q f g.
  Proof. rewrite <-(ufm_cont_ball_on_dense f g k⁺¹(X) _). split; intro E.
  + split. exact (msp_nonneg (X:=X ⇒ Z) _ _ _ E).
    intros ? [?[x[? Ex]]]. rewrite <- (Y $ Ex).
    destruct E as [_ P]. exact (P _ _).
  + pose proof (restrict_uniformly_continuous f k⁺¹(X)).
    pose proof (restrict_uniformly_continuous g k⁺¹(X)).
    split. exact (msp_nonneg (X:=k⁺¹(X) ⇒ Z) _ _ _ E).
    intros x ?. unfold compose.
    destruct E as [_ P]. exact (P _ _).
  Qed.

  Lemma ufm_cont_equal_on_dense_image : f ∘ k = g ∘ k ↔ f = g.
  Proof. rewrite <-(ball_separated (X:=Y⇒Z) _ _).
    rewrite <-(ball_separated (X:=X⇒Z) _ _).
    exact (ufm_cont_ball_on_dense_image _).
  Qed.

  Lemma ufm_cont_equal_on_dense_image_applied : (∀ `{x ∊ X}, f (k x) = g (k x)) → f = g.
  Proof. intro P.
    apply ufm_cont_equal_on_dense_image.
    intros ?? E. unfold_sigs. red_sig. unfold compose. rewrite <- (_ $ E). now apply P.
  Qed.

End ufm_continuous_equal_on_dense_image.

Section ufm_cont_ext_unique.
  Context `{MetricSpace (X:=X₁)} `{MetricSpace (X:=X₂)}.
  Context (g:X₁ ⇀ X₂) `{!Isometry X₁ X₂ g} `{!Dense (X:=X₂) g⁺¹(X₁)}.
  Context `{MetricSpace (X:=Y₁)} `{CompleteMetricSpace (X:=Y₂)}.
  Context (h:Y₁ ⇀ Y₂) `{!Isometry Y₁ Y₂ h}.
  Context `{MetricSpace (X:=M)}.
  Context (m:(X₁==>Y₁) ⇀ M) `{!Isometry (X₁==>Y₁) M m} `{!Dense (X:=M) m⁺¹(X₁==>Y₁)}.

  Hint Extern 0 AmbientSpace => eexact X₂ : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact M  : typeclass_instances.

  Notation "#" := (ufm_cont_extension g h m).

  Lemma ufm_cont_ext_unique f `{f ∊ M} (cf:X₂ ⇀ Y₂) `{!UniformlyContinuous X₂ Y₂ cf}
  : (∀ `{q ∊ Q⁺} `{f' ∊ X₁ ==> Y₁}, ball q (m f') f ↔ ball q (h ∘ f') (cf ∘ g) )
    → cf = # f.
  Proof. intro P.
    apply (ufm_cont_equal_on_dense_image g _ _).
    apply (equal_by_ball_closed (X:=X₁ ⇒ Y₂)  _ _). intros q ?.
    destruct (dense_image m (X₁ ==> Y₁) f (q/2)) as [f'[Cf Bf]].
    red in Cf. subsymmetry in Bf.
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
        destruct (dense_image m (X₁ ==> Y₁) f₁ a) as [f₁' [Cf1 Bf1]].
        destruct (dense_image m (X₁ ==> Y₁) f₂ a) as [f₂' [Cf2 Bf2]].
        red in Cf1,Cf2. subsymmetry in Bf1. subsymmetry in Bf2.
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
        destruct (dense_image m (X₁ ==> Y₁) f₁ a) as [f₁' [Cf1 Bf1]].
        destruct (dense_image m (X₁ ==> Y₁) f₂ a) as [f₂' [Cf2 Bf2]].
        red in Cf1,Cf2. subsymmetry in Bf1. subsymmetry in Bf2.
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

