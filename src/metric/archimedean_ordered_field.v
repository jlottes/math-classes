Require Import
  abstract_algebra interfaces.orders interfaces.integers interfaces.rationals 
  interfaces.archimedean_ordered_field interfaces.metric_spaces
  theory.setoids theory.products theory.fields theory.rationals orders.rationals
  metric.metric_spaces metric.maps metric.prelength metric.rationals metric.products
  orders.affinely_extended_field stdlib_field misc.quote
  the_integers nonneg_integers_naturals theory.naturals
  the_rationals the_ae_rationals
  orders.minmax orders.lattices orders.abs.
Require Export
  theory.archimedean_ordered_field.

Section rationals_archimedean_field.
  Context `{Rationals (Q:=Q)} `{Le _} `{Lt _} `{!FullPseudoSemiRingOrder Q}.

  Notation f := (rationals_to_field the_ae_rationals Q).

  Lemma rationals_archimedean_field_metric : ArchimedeanOrderedField_Metric Q.
  Proof. split. apply _.
  + exact msp_nonneg.
  + exact msp_ball_inf.
  + intros. now rewrite (rationals_ball_def f _ _ _), (abs.abs_le_iff _ _).
  Qed.
End rationals_archimedean_field.

Hint Extern 2 (ArchimedeanOrderedField the_ae_rationals) => eapply @rationals_archimedean_field : typeclass_instances.
Hint Extern 2 (ArchimedeanOrderedField_Metric the_rationals) => eapply @rationals_archimedean_field_metric : typeclass_instances.
Hint Extern 2 (ArchimedeanOrderedField_Metric the_ae_rationals) => eapply @rationals_archimedean_field_metric : typeclass_instances.

Local Notation Q := the_ae_rationals.
Local Notation "Q∞" := (aff_ext Q).
Local Notation Qfull := (aff_ext_full Q).

Section arch_ord_field_is_metric_space.
  Context `{ArchimedeanOrderedField A (F:=F)}.

  Local Notation "#" := (rationals_to_field Q F).

  Definition arch_ord_field_default_metric : Ball F
    := λ ε x y, ε = ∞ ∨ (ε ∊ Q⁺ ∧ - #ε ≤ x-y ≤ #ε ).

  Instance arch_ord_field_default_metric_correct
    : ArchimedeanOrderedField_Metric F (Aball:=arch_ord_field_default_metric).
  Proof. split; unfold ball, arch_ord_field_default_metric.
  + intros p q Eq ?? E1 ?? E2 [E|[? E]]; unfold_sigs.
    left. subtransitivity p. subsymmetry.
    right. assert (q ∊ Q⁺) by now rewrite <-(Qfull $ Eq). split. apply _.
    now rewrite <-(Q $ Eq), <-(F $ E1), <-(F $ E2).
  + intros ε ? x ? y ? [E|[? _]]. rewrite (_ $ E). apply _. apply _.
  + intros x ? y ?. now left.
  + intros ε ? x ? y ?. split.
    * intros [E|[??]]; trivial. destruct (ae_inf_not_el). now rewrite <-(Qfull $ E).
    * intro E. right. cut (ε ∊ Q⁺). intuition.
      apply (reflects_nonneg #). apply _.
      apply (between_nonneg _). subtransitivity (x-y); now destruct E.
  Qed.

  Context {Aball: Ball A} `{!ArchimedeanOrderedField_Metric F}.

  Add Ring F' : (stdlib_ring_theory F).

  Instance arch_ord_field_metric: MetricSpace F.
  Proof. split. apply _.
  + exact arch_ord_field_ball_proper.
  + exact arch_ord_field_ball_nonneg.
  + exact arch_ord_field_ball_inf.
  + intros ε ? x ?. rewrite (arch_ord_field_ball _ _ _).
    rewrite (_ $ plus_negate_r _).
    destruct (_ : # ε ∊ F⁺). destruct (_ : - # ε ∊ F⁻). intuition.
  + intros ε ? x ? y ?. rewrite !(arch_ord_field_ball _ _ _). intro E.
    split; rewrite <-(flip_le_negate _ _), <-(_ $ negate_swap_r _ _);
    [ rewrite (_ $ negate_involutive _) |]; now destruct E.
  + intros x ? y ?. rewrite (arch_ord_field_ball _ _ _).
    preserves_simplify #. rewrite (_ $ negate_0).
    rewrite <- (equal_by_zero_sum _ _), (eq_iff_le _ _). tauto.
  + intros ε₁ ? ε₂ ? x ? y ? z ?. rewrite !(arch_ord_field_ball _ _ _). intros E1 E2.
    mc_replace (x-z) with ((x-y)+(y-z)) on F by subring F.
    rewrite (_ $ preserves_plus _ _), (_ $ negate_plus_distr _ _).
    now apply (plus_le_compat_2 _ _ _ _ _ _).
  + intros ε ? x ? y ? P. rewrite (arch_ord_field_ball _ _ _).
    rewrite 2!(le_iff_not_lt_flip _ _).
    split; intro E.
    * destruct (archimedean_rationals_dense _ _ E) as [q[?[? E2]]].
      assert (-ε -q ∊ Q₊). apply (reflects_pos #). apply _.
        mc_replace (# (- ε - q)) with (- #ε - #q) on F by now preserves_simplify #.
        now rewrite (flip_pos_minus _ _).
      destruct (le_not_lt_flip (x-y) (#q)); trivial.
      pose proof P (- ε - q) _ as E3. rewrite (arch_ord_field_ball _ _ _) in E3.
      destruct E3 as [E3 _].
      match type of E3 with le ?a _ => subtransitivity a end. apply (eq_le _ _).
      preserves_simplify #. subring F.
    * destruct (archimedean_rationals_dense _ _ E) as [q[?[? E2]]].
      assert (q-ε ∊ Q₊). apply (reflects_pos #). apply _.
        mc_replace (# (q - ε)) with (#q - #ε) on F by now preserves_simplify #.
        now rewrite (flip_pos_minus _ _).
      destruct (le_not_lt_flip (#q) (x-y)); trivial.
      pose proof P (q-ε) _ as E3. rewrite (arch_ord_field_ball _ _ _) in E3.
      destruct E3 as [_ E3].
      match type of E3 with le _ ?a => subtransitivity a end. apply (eq_le _ _).
      preserves_simplify #. subring F.
  Qed.
End arch_ord_field_is_metric_space.

Hint Extern 50 (Ball (elt_type ?F)) =>
  let H := constr:(_ : ArchimedeanOrderedField F) in exact arch_ord_field_default_metric : typeclass_instances.
Hint Extern 2 (ArchimedeanOrderedField_Metric _ (Aball:=arch_ord_field_default_metric))
  => eapply @arch_ord_field_default_metric_correct : typeclass_instances.
Hint Extern 15 (MetricSpace ?F) =>
  let H := constr:(_ : ArchimedeanOrderedField F) in eapply (arch_ord_field_metric (H:=H)) : typeclass_instances.

Section maps.
  Context `{ArchimedeanOrderedField (F:=F1)} `{Ball F1} `{!ArchimedeanOrderedField_Metric F1}.
  Context `{ArchimedeanOrderedField (F:=F2)} `{Ball F2} `{!ArchimedeanOrderedField_Metric F2}.
  Context (f:F1 ⇀ F2) `{!Ring_Morphism F1 F2 f}.

  Notation "%" := (rationals_to_field Q F1).
  Notation "#" := (rationals_to_field Q F2).

  Instance arch_ord_field_dense: Dense (X:=F2) f⁺¹(F1).
  Proof. split; try apply _. split. now intros [??]. intro. split. apply _.
    intros. destruct (ae_decompose_pos ε) as [E|?].
      exists_sub 0. rewrite (_ $ E). exact (msp_ball_inf _ _).
    pose proof pos_plus_lt_compat_r x (#ε) as E. rewrite <-(flip_lt_minus_l _ _ _) in E.
    destruct (archimedean_rationals_dense _ _ E) as [q[? [E1 E2]]].
    assert (# q ∊ f⁺¹(F1)). split. apply _. exists_sub (%q). change ((f ∘ %) q = # q).
      rewrite (rationals_to_field_unique Q (f ∘ %) q q); try now red_sig. subreflexivity.
    exists_sub (# q). rewrite (arch_ord_field_ball _ _ _).
    split. subtransitivity 0. now destruct (_ : - # ε ∊ F2⁻).
      apply (lt_le _ _). rewrite <-(flip_pos_minus _ _) in E2. now destruct E2.
    apply (lt_le _ _). red.
    now rewrite (flip_lt_minus_l _ _ _), (_ $ commutativity (+) _ _), <-(flip_lt_minus_l _ _ _).
  Qed.

  Context `{!StrictOrderEmbedding F1 F2 f}.

  Existing Instance full_pseudo_order_preserving.
  Existing Instance full_pseudo_order_reflecting.

  Instance arch_ord_field_isometry: Isometry F1 F2 f.
  Proof. split; try apply _. intros q ? x ? y ?.
    rewrite !(arch_ord_field_ball _ _ _).
    rewrite <-(rationals_to_field_unique Q (f ∘ %) q q); try now red_sig.
    unfold compose. rewrite <-(_ $ preserves_minus _ _), <-(_ $ preserves_negate (f:=f) _).
    split; intros [??].
       split; now apply (order_preserving f _ _).
       split; now apply (order_reflecting f _ _).
  Qed.
End maps.

Hint Extern 10 (Isometry _ _ (rationals_to_field _ _)) => eapply @arch_ord_field_isometry : typeclass_instances.

Section more_maps.
  Context `{ArchimedeanOrderedField (F:=F1)} `{Ball F1} `{!ArchimedeanOrderedField_Metric F1}.
  Context `{ArchimedeanOrderedField (F:=F2)} `{Ball F2} `{!ArchimedeanOrderedField_Metric F2}.
  Context (f:F1 ⇀ F2) `{!Ring_Morphism F1 F2 f}.

  Hint Extern 0 AmbientSpace => eexact F1 : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact F2 : typeclass_instances.

  Notation "%" := (rationals_to_field Q F1).
  Notation "#" := (rationals_to_field Q F2).

  Existing Instance arch_ord_field_dense.

  Lemma arch_ord_field_continuous_embedding :
    UniformlyContinuous F1 F2 f → StrictOrderEmbedding F1 F2 f.
  Proof. intro.
    cut (StrictlyOrderPreserving F1 F2 f). intro. split. apply _.
      apply arch_ord_field_preserving_iff_reflecting; apply _.
    apply strictly_preserving_preserves_pos. apply _.
    intros x [? E].
    destruct (archimedean_rationals_dense _ _ E) as [q[? [E1 E2]]].
    assert (q ∊ Q₊). apply (reflects_pos %). apply _. split. apply _. exact E1.
    destruct (archimedean_rationals_dense _ _ E2) as [r[? [E3 E4]]].
    set (rq := r-q). assert (rq ∊ Q₊).
      unfold rq. apply (flip_pos_minus _ _). now apply (strictly_order_reflecting % _ _).
    assert ( x ∊ closure (%⁺¹(Q) ⊓ (%q ≤)) ).
      split. apply _. intros ε ?.
      ae_rat_set_min δ ε rq Eδ1 Eδ2. pose proof (ae_pos_finite_bound _ _ Eδ2).
      destruct (dense_image (%) Q x δ) as [s[? Bs]].
      cut ( %s ∊ %⁺¹(Q) ⊓ (%q ≤) ). intro. exists_sub (%s). now rewrite <-(Qfull $ Eδ1).
      split. apply _. red. rewrite (arch_ord_field_ball _ _ _) in Bs.
      apply (flip_le_negate _ _). apply (order_reflecting (x+) _ _).
      subtransitivity (%δ). now destruct Bs.
      subtransitivity (%(r-q)). fold rq. now apply (order_preserving % _ _).
      preserves_simplify %. apply (order_preserving (+(-%q)) (%r) x).
      now apply (lt_le _ _).
    assert (f x ∊ closure (#⁺¹(Q) ⊓ (#q ≤)) ) as [? P].
      assert ((%⁺¹(Q) ⊓ (%q ≤)) ⊆ F1). apply subsetoid_alt. apply _.
        intros ?? E' [??]. split. now rewrite <-E'. red. now rewrite <-E'.
        now intros ? [[??]?].
      apply ( uniformly_continuous_closure f (%⁺¹(Q) ⊓ (%q ≤)) ); trivial.
      intros ? [[? [p [? Ep]]] ?].
      pose proof (rationals_to_field_unique Q (f∘%) _ _ (_:Proper (Q,=) p)) as Ep'.
        unfold compose in Ep'.
      split. rewrite <-(F1 $ Ep), Ep'; apply _.
      red. rewrite <-(F1 $ Ep), Ep'.
      apply (order_preserving # _ _), (order_reflecting (%) q p).
      now rewrite (F1 $ Ep).
    split. apply _.
    destruct (P (q/2) _) as [y [[[??] Ey] By]]. red in Ey.
    rewrite (arch_ord_field_ball _ _ _) in By.
    apply (lt_le_trans _ (#(q/2)) _).
    now destruct  (_ : # (q / 2) ∊ F2₊).
    mc_replace (q/2) with (q-q/2) on Q by subfield Q.
    mc_replace (#(q-q/2)) with (#q - #(q/2)) on F2 by now preserves_simplify #.
    rewrite <-(F2 $ plus_negate_r_split_alt y (f x)).
    apply (plus_le_compat _ _ _ _). exact Ey. now destruct By.
  Qed.
End more_maps.

Section further_props.
  Context `{ArchimedeanOrderedField (F:=F)} `{Ball F} `{!ArchimedeanOrderedField_Metric F}.
  Notation "#" := (rationals_to_field Q F).

  Existing Instance arch_ord_field_dense.

  Lemma arch_ord_field_finite_points : FinitePoints F.
  Proof.
    pose proof isometric_image_finite_points #.
    exact ( dense_subset_finite_points #⁺¹(Q) ).
  Qed.

  Lemma arch_ord_field_located_points : LocatedPoints F.
  Proof.
    pose proof isometric_image_located_points #.
    exact ( dense_subset_located_points #⁺¹(Q) ).
  Qed.

  Lemma arch_ord_field_prelength : PrelengthSpace F.
  Proof.
    pose proof isometric_image_prelength #.
    exact ( dense_subset_prelength #⁺¹(Q) ).
  Qed.
  
  Lemma arch_ord_field_metric_inequality : MetricInequality F.
  Proof. intros x ? y ?. split.
  + rewrite (apart_iff_total_lt _ _).
    intros [E|E]; rewrite <-(flip_pos_minus _ _) in E; destruct E as [? E];
    destruct (archimedean_rationals_dense _ _ E) as [q[?[??]]];
    assert (q ∊ Q₊) by (apply (reflects_pos #); [apply _ | split; trivial; apply _]);
    exists_sub q; rewrite (arch_ord_field_ball _ _ _);
    rewrite !(le_iff_not_lt_flip _ _); [|tauto]. intros [E2 _]. destruct E2.
    apply (flip_lt_negate _ _). now rewrite (_ $ negate_involutive _), <-(_ $ negate_swap_r _ _).
  + intros [q[? Bxy]]. rewrite (apart_iff_total_lt _ _).
    assert (-#q < 0) as E' by now destruct (_ : - #q ∊ F₋).
    destruct (subcotransitivity E' (x-y)). clear E'.
    assert (0 < #q) as E' by now destruct (_ : #q ∊ F₊).
    destruct (subcotransitivity E' (x-y)). clear E'.
    right. apply (flip_pos_minus _ _). split; trivial. apply _.
    destruct Bxy. rewrite (arch_ord_field_ball _ _ _). split; now apply (lt_le _ _).
    left. apply (flip_neg_minus _ _). split; trivial. apply _.
  Qed.

End further_props.

Hint Extern 15 (FinitePoints ?F) =>
  let H := constr:(_ : ArchimedeanOrderedField F) in eapply (arch_ord_field_finite_points (H:=H)) : typeclass_instances.
Hint Extern 15 (LocatedPoints ?F) =>
  let H := constr:(_ : ArchimedeanOrderedField F) in eapply (arch_ord_field_located_points (H:=H)) : typeclass_instances.
Hint Extern 15 (PrelengthSpace ?F) =>
  let H := constr:(_ : ArchimedeanOrderedField F) in eapply (arch_ord_field_prelength (H:=H)) : typeclass_instances.
Hint Extern 15 (MetricInequality ?F) =>
  let H := constr:(_ : ArchimedeanOrderedField F) in eapply (arch_ord_field_metric_inequality (H:=H)) : typeclass_instances.

Section ops.
  Context `{ArchimedeanOrderedField (F:=F)} `{Ball F} `{!ArchimedeanOrderedField_Metric F}.
  Hint Extern 0 AmbientSpace => eexact F : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact (F*F)%subset : typeclass_instances.

  Add Ring F'' : (stdlib_ring_theory F).

  Notation "#" := (rationals_to_field Q F).
  Existing Instance arch_ord_field_dense.

  Instance arch_ord_field_negate_isometry : Isometry F F (-).
  Proof. split; try apply _. intros ??????. rewrite !(arch_ord_field_ball _ _ _).
    rewrite <-(_ $ negate_plus_distr x (-y)).
    rewrite <-(_ $ negate_involutive (# ε)) at 4 .
    rewrite 2!(flip_le_negate _ _). tauto.
  Qed.

  Instance arch_ord_field_plus_ufm_cont : UniformlyContinuous (F*F) F (uncurry (+)).
  Proof. split; try apply _. intros q ?. exists_sub (q/2).
    intros [x₁ x₂] [??] [y₁ y₂] [??] [B1 B2]. simpl in B1,B2. simpl.
    revert B1 B2. rewrite !(arch_ord_field_ball _ _ _). intros B1 B2.
    mc_replace q with (q/2+q/2) on Q by subfield Q.
    mc_replace (x₁ + x₂ - (y₁ + y₂)) with (x₁ - y₁ + (x₂ - y₂)) on F by subring F.
    rewrite (_ $ preserves_plus _ _), (_ $ negate_plus_distr _ _).
    now apply (plus_le_compat_2 _ _ _ _ _ _).
  Qed.

  Instance arch_ord_field_plus_str_ufm_cont : StronglyUniformlyContinuous (F*F) F (uncurry (+)).
  Proof. split. apply _. intros U ??. split; try apply _.
    destruct (bounded U) as [q[el P]].
    exists_sub (q+q). intros ? [?[[a b][? E1]]] ? [?[[x y][? E2]]]. simpl in E1,E2.
    pose proof (_ : U ⊆ F*F). destruct (_ : (a,b) ∊ F*F). destruct (_ : (x,y) ∊ F*F).
    rewrite <-(_ $ E1), <-(_ $ E2).
    destruct (P (a,b) _ (x,y) _) as [B1 B2]. simpl in B1,B2.
    revert B1 B2. rewrite !(arch_ord_field_ball _ _ _). intros B1 B2.
    mc_replace (a+b - (x+y)) with (a - x + (b - y)) on F by subring F.
    rewrite (_ $ preserves_plus _ _), (_ $ negate_plus_distr _ _).
    now apply (plus_le_compat_2 _ _ _ _ _ _).
  Qed.    
 
  Instance arch_ord_field_plus_isometry_1 a `{a ∊ F} : Isometry F F (a +).
  Proof. split; try apply _. intros ??????. rewrite !(arch_ord_field_ball _ _ _).
    now mc_replace (a + x - (a + y)) with (x-y) on F by subring F.
  Qed.

  Instance arch_ord_field_plus_isometry_2 a `{a ∊ F} : Isometry F F (+ a).
  Proof. split; try apply _. intros ??????. rewrite !(arch_ord_field_ball _ _ _).
    now mc_replace (x + a - (y + a)) with (x-y) on F by subring F.
  Qed.

  Instance arch_ord_field_mult_cont: Continuous (F*F) F (uncurry (.*.) : F*F ⇀ F).
  Proof. apply continuity_alt. apply _. intros U ?. pose proof (_ : U ⊆ F*F).
    assert (∃ `{M ∊ Q⁺}, ∀ x y, (x,y) ∊ U → -#M ≤ x ≤ #M ∧ -#M ≤ y ≤ #M) as P.
      destruct (bounded U) as [d[el P]].
      destruct (inhabited U) as [[a b]?]. destruct (_ : (a,b) ∊ F*F).
      destruct (finite_points (X:=(F*F)%subset) (a,b) (0,0)) as [M'[el' ?]].
      exists_sub (d+M'). intros x y ?. destruct (_ : (x,y) ∊ F*F).
      mc_replace x with (x-0) on F by subring F.
      mc_replace y with (y-0) on F by subring F.
      rewrite <-!(arch_ord_field_ball _ _ _).
      change (ball (A:=F*F) (d+M') (x,y) (0,0)).
      apply (ball_triangle (X:=F*F) _ _ _ (a,b) _ ); trivial.
      now apply P.
    destruct P as [M[Mel P]].
    pose proof sub_metric_space (X:=F*F) (Y:=U).
    destruct (decide_sub (=) M 0) as [E|?].
    + assert (∀ x y, (x, y) ∊ U → x*y = 0) as P'. intros x y ?. destruct (_ : (x,y) ∊ F*F).
        cut (x = 0). intro E2. rewrite (_ $ E2). exact (mult_0_l _).
        cut (-#0 ≤ x ≤ #0). preserves_simplify #. rewrite (_ $ negate_0).
          intro. subsymmetry. now apply (eq_iff_le _ _).
        rewrite <-(_ $ E). now destruct (P x y _).
      intuition.
      * split; try apply _.
        match goal with |- Morphism ?m _ => rewrite <-(_ : SubsetOf (F*F ⇒ F) m); apply _ end.
        intros ??. exists_sub ∞. intros [a b] ? [x y] ? _. simpl.
        destruct (_ : (a,b) ∊ F*F). destruct (_ : (x,y) ∊ F*F).
        now rewrite (_ $ P' a b _), (_ $ P' x y _).
      * split; try apply _. exists_sub (0:Q).
        intros ? [?[[a b][? E1]]] ? [?[[x y][? E2]]]. simpl in E1,E2.
        destruct (_ : (a,b) ∊ F*F). destruct (_ : (x,y) ∊ F*F).
        rewrite <-(_ $ E1), <-(_ $ E2).
        now rewrite (_ $ P' a b _), (_ $ P' x y _).
    + assert (M ∊ Q ₀). split. apply _. now rewrite (denial_inequality _ _).
      pose proof nonneg_nonzero_pos M.
      intuition.
      * split; try apply _.
        match goal with |- Morphism ?m _ => rewrite <-(_ : SubsetOf (F*F ⇒ F) m); apply _ end.
        intros ε ?. exists_sub (ε/2/M). intros [a b] ? [x y] ? [B1 B2]. simpl. simpl in B1,B2.
        destruct (_ : (a,b) ∊ F*F). destruct (_ : (x,y) ∊ F*F).
        mc_replace ε with ((ε/2/M)*M + M*(ε/2/M)) on Q by subfield Q.
        revert B1 B2. rewrite !(arch_ord_field_ball _ _ _). intros B1 B2.
        mc_replace (a * b - x * y) with ((a-x)*b + x*(b-y)) on F by subring F.
        rewrite (_ $ preserves_plus _ _), (_ $ negate_plus_distr _ _).
        apply (plus_le_compat_2 _ _ _ _ _ _);
          apply (between_mult_le_compat _ _ _ _); trivial.
        now destruct (P a b _). now destruct (P x y _).
      * split; try apply _. exists_sub (M*M+M*M).
        intros ? [?[[a b][? E1]]] ? [?[[x y][? E2]]]. simpl in E1,E2.
        destruct (_ : (a,b) ∊ F*F). destruct (_ : (x,y) ∊ F*F).
        rewrite <-(_ $ E1), <-(_ $ E2).
        rewrite (arch_ord_field_ball _ _ _).
        rewrite (_ $ preserves_plus _ _), (_ $ negate_plus_distr _ _).
        apply (plus_le_compat_2 _ _ _ _ _ _).
        apply (between_mult_le_compat _ _ _ _); now destruct (P a b _).
        cut (- # (M * M) ≤ x * y ≤ # (M * M)). intros [??].
          split; [| rewrite <- (_ $ negate_involutive (#(M*M)))]; now apply (flip_le_negate _ _).
        apply (between_mult_le_compat _ _ _ _); now destruct (P x y _).
  Qed.

  Local Open Scope grp_scope.

  Instance: 0 ∊ ∼ F ₀.
  Proof. rewrite <-zero_is_complement. apply _. Qed.

  Lemma arch_ord_field_bounded U `{U ⊆ F} `{!Bounded U} `{!Inhabited U}
    : ∃ `{M ∊ Q⁺}, ∀ x, x ∊ U → -#M ≤ x ≤ #M.
  Proof.
    destruct (bounded U) as [d[el P]].
    destruct (inhabited U) as [a ?].
    destruct (finite_points a 0) as [M'[el' ?]].
    exists_sub (d+M'). intros x ?.
    mc_replace x with (x-0) on F by subring F.
    rewrite <-!(arch_ord_field_ball _ _ _).
    apply (ball_triangle _ _ _ a _ ); trivial.
    now apply P.
  Qed.

  Lemma arch_ord_field_bounded_away U `{U ⊆ F} `{!SetApart U (∼ F ₀)}
    : ∃ `{c ∊ Q₊}, ∀ x, x ∊ U → x ≤ -#c ∨ #c ≤ x.
  Proof. destruct (set_apart_finite U (∼ F ₀)) as [c[elc P]].
    exists_sub c. intros x ?.
    pose proof (P x _ 0 _) as B.
    assert (0 < #c) as E by now destruct (_ : #c ∊ F₊).
    destruct (subcotransitivity E x); clear E.
    + right. apply (le_iff_not_lt_flip _ _). contradict B.
      rewrite (arch_ord_field_ball _ _ _), (_ $ negate_0), (_ $ plus_0_r _).
      split; apply (lt_le _ _); trivial.
      red. subtransitivity 0. now destruct (_ : - #c ∊ F₋).
    + left.  apply (le_iff_not_lt_flip _ _). contradict B.
      rewrite (arch_ord_field_ball _ _ _), (_ $ negate_0), (_ $ plus_0_r _).
      split; apply (lt_le _ _); trivial.
  Qed.

  Section inv.
    Context U `{U ⊂⊂ F ₀}.

    Instance: Morphism (U ⇒ F ₀) (⁻¹).
    Proof. rewrite <-(_ : SubsetOf (F ₀ ⇒ F ₀) (U ⇒ F ₀)). apply _. Qed.

    Instance: MetricSpace (F ₀) := sub_metric_space.
    Instance: MetricSpace U := sub_metric_space.

    Hint Extern 6 (_ ∊ F ₀) => apply (_ : U ⊆ F ₀) : typeclass_instances.
    Hint Extern 6 (_ ∊ F  ) => apply (_ : F ₀ ⊆ F) : typeclass_instances.

    Lemma bounded_alt : ∃ `{M ∊ Q₊}, ∀ x, x ∊ U → -#M < x < #M.
    Proof. destruct (arch_ord_field_bounded U) as [M[elM P]].
      exists_sub (M+1). intros x ?. split.
      + apply (lt_le_trans _ (- #M) _).
        apply (flip_pos_minus _ _). preserves_simplify #.
        mc_replace (- # M - - (# M + 1)) with 1 on F by subring F.
        exact one_pos. now destruct (P x _).
      + apply (le_lt_trans _ (#M) _). now destruct (P x _).
        apply (flip_pos_minus _ _). preserves_simplify #.
        mc_replace (# M + 1 - # M) with 1 on F by subring F.
        exact one_pos.
    Qed.

    Lemma bounded_away_alt : ∃ `{c ∊ Q₊}, ∀ x, x ∊ U → -#c⁻¹ ≤ x⁻¹ ≤ #c⁻¹.
    Proof. destruct (arch_ord_field_bounded_away U) as [c[elc P]].
      exists_sub c. intros x ?.
      preserves_simplify #. destruct (P x _).
      + assert (x ∊ F₋). split. apply _.
          apply (le_lt_trans _ (- #c) _); trivial. now destruct (_ : - #c ∊ F₋).
        split.
        * rewrite <-(flip_le_negate _ _), (_ $ negate_involutive _), <-(_ $ mult_inv_negate _).
          apply (flip_le_mult_inv _ _).
          now rewrite <-(flip_le_negate _ _), (_ $ negate_involutive _).
        * apply (lt_le _ _). subtransitivity 0. now destruct (_ : x⁻¹ ∊ F₋).
          now destruct (_ : (# c)⁻¹ ∊ F₊).
      + assert (x ∊ F₊). split. apply _. apply (lt_le_trans _ (#c) _); trivial.
          now destruct (_ : # c ∊ F₊).
        split.
        * apply (lt_le _ _). subtransitivity 0. now destruct (_ : -(# c)⁻¹ ∊ F₋).
            now destruct (_ : x⁻¹ ∊ F₊).
        * now apply (flip_le_mult_inv _ _).
    Qed.

    Instance inv_cont_ufm: UniformlyContinuous U (F ₀) (⁻¹).
    Proof. split; try apply _. intros ε ?.
      destruct (bounded_away_alt) as [c[elc P]].
      exists_sub (ε*c*c). intros x ? y ?.
      pose proof (P x _). pose proof (P y _).
      rewrite !(arch_ord_field_ball _ _ _).
      intros [??]. assert (- # (ε * c * c) ≤ y - x ≤ # (ε * c * c)).
        split; rewrite <-(flip_le_negate _ _), <-(_ $ negate_swap_r _ _); trivial.
        now rewrite (_ $ negate_involutive _).
      assert (x⁻¹ - y⁻¹ = (y-x)*(x⁻¹/y)) as E.
        apply (right_cancellation (.*.) (x*y) F _ _).
        subtransitivity (y * (x/x) - x * (y/y)). subring F.
        subtransitivity ((y-x)*(x/x)*(y/y)); [|subring F].
        rewrite !(_ $ field_inv_r _). subring F.
      rewrite (_ $ E).
      mc_replace ε with ((ε*c*c)*(c⁻¹/c)) on Q by subfield Q.
      apply (between_mult_le_compat _ _ _ _); trivial.
      apply (between_mult_le_compat _ _ _ _); trivial.
    Qed.

    Notation Uinv := (image (X:=F ₀) (Y:=F ₀) inv U).

    Instance inv_cont_bounded: Bounded Uinv.
    Proof. split; try apply _. transitivity (F ₀); apply _.
      destruct (bounded_away_alt) as [c[elc P]].
      exists_sub (c⁻¹+c⁻¹).
      intros ? [?[x[? Ex]]] ? [?[y[? Ey]]].
      pose proof (P x _). pose proof (P y _).
      rewrite (arch_ord_field_ball _ _ _).
      rewrite (_ $ preserves_plus _ _), (_ $ negate_plus_distr _ _).
      apply (plus_le_compat_2 _ _ _ _ _ _).
      now rewrite <-(_ $ Ex). rewrite <-(_ $ Ey).
      rewrite <-(_ $ negate_involutive (# c⁻¹)) at 2.
      split; apply (flip_le_negate _ _); tauto.
    Qed.

    Instance inv_cont_apart: SetApart Uinv (∼F ₀).
    Proof. rewrite <-zero_is_complement.
      destruct bounded_alt as [M[elM P]].
      exists_sub (M⁻¹).
      intros ? [?[x[? Ex]]] z [? Ez]. rewrite <-(_ $ Ex), (_ $ Ez).
      destruct (P x _).
      rewrite (arch_ord_field_ball _ _ _).
      rewrite (_ $ negate_0), (_ $ plus_0_r _).
      preserves_simplify #. rewrite 2!(le_iff_not_lt_flip _ _).
      intros [En Ep]. destruct (decompose_nonzero x).
      * destruct Ep. now apply (flip_lt_mult_inv _ _).
      * destruct En.
        rewrite <-(_ $ negate_involutive (inv x)).
        apply (flip_lt_negate _ _).
        rewrite <-(_ $ mult_inv_negate x).
        apply (flip_lt_mult_inv _ _).
        rewrite <-(_ $ negate_involutive (# M)).
        now apply (flip_lt_negate _ _).
    Qed.
  End inv.

  Instance arch_ord_field_inv_cont: Continuous (F ₀) (F ₀) (⁻¹).
  Proof. apply continuity_alt. apply _. intros U ?. intuition.
    exact (inv_cont_ufm _).
    exact (inv_cont_bounded _).
    exact (inv_cont_apart _).
  Qed.

End ops.

Hint Extern 15 (Isometry ?F ?F (-)) =>
  let H := constr:(_ : ArchimedeanOrderedField F) in eapply (arch_ord_field_negate_isometry (H:=H)) : typeclass_instances.
Hint Extern 15 (UniformlyContinuous (?F*?F) _ (uncurry (+))) =>
  let H := constr:(_ : ArchimedeanOrderedField F) in eapply (arch_ord_field_plus_ufm_cont (H:=H)) : typeclass_instances.
Hint Extern 15 (StronglyUniformlyContinuous (?F*?F) _ (uncurry (+))) =>
  let H := constr:(_ : ArchimedeanOrderedField F) in eapply (arch_ord_field_plus_str_ufm_cont (H:=H)) : typeclass_instances.
Hint Extern 15 (Continuous (?F*?F) _ (uncurry (.*.))) =>
  let H := constr:(_ : ArchimedeanOrderedField F) in eapply (arch_ord_field_mult_cont (H:=H)) : typeclass_instances.
Hint Extern 15 (Continuous (?F ₀) _ (⁻¹)) =>
  let H := constr:(_ : ArchimedeanOrderedField F) in eapply (arch_ord_field_inv_cont (H:=H)) : typeclass_instances.
