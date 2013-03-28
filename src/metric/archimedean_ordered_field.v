Require Import
  abstract_algebra interfaces.orders interfaces.integers interfaces.rationals interfaces.metric_spaces
  theory.setoids theory.products theory.fields theory.rationals orders.rationals
  metric.metric_spaces metric.prelength metric.rationals metric.product
  orders.affinely_extended_field stdlib_field misc.quote
  the_integers nonneg_integers_naturals theory.naturals
  the_ae_rationals
  orders.minmax orders.lattices orders.abs.


Section archimedean_property.
  Context `{ArchimedeanOrderedField (F:=F)}.
  Context `{Rationals (Q:=Q)}.
  Notation "#" := (rationals_to_field Q F).
  Notation Z := the_integers.
  Notation "%" := (integers_to_ring Z F).

  Add Ring F : (stdlib_ring_theory F).

  Lemma archimedean_int_bounds x `{x ∊ F} : ∃ `{a ∊ Z} `{b ∊ Z}, %a < x < %b.
  Proof. destruct (subcotransitivity (pos_plus_lt_compat_r x 1) 0).
  + assert (x ∊ F₋) by now split.
    destruct (archimedean (-x) 1) as [m [? Em]].
    rewrite (_ $ mult_1_r _), <-(_ $ negate_involutive (%m)), (flip_lt_negate _ _) in Em.
    assert (x-(-%m) ∊ F₊) by now rewrite (flip_pos_minus _ _).
    destruct (archimedean (x-(-%m)) 1) as [M [? EM]].
    rewrite (_ $ mult_1_r _), (flip_lt_minus_l _ _ _) in EM.
    exists_sub (-m) (M-m). preserves_simplify %. intuition.
  + assert (x+1 ∊ F₊) by (split; trivial; apply _).
    destruct (archimedean (x+1) 1) as [M [? EM]].
    rewrite (_ $ mult_1_r _), <-(flip_lt_minus_r _ _ _) in EM.
    assert ((%M-1)-x ∊ F₊) by now rewrite (flip_pos_minus _ _).
    destruct (archimedean (%M-1-x) 1) as [m [? Em]].
    rewrite (_ $ mult_1_r _), (flip_lt_minus_l _ _ _),
      (_ $ commutativity (+) _ x), <-(flip_lt_minus_l _ _ _) in Em.
    exists_sub (M-1-m) (M-1). preserves_simplify %. intuition.
  Qed.

  Lemma archimedean_int_between x `{x ∊ F} y `{y ∊ F} : 1 + x < y
    → ∃ `{i ∊ Z}, x < %i < y.
  Proof. intro E.
    assert (x<y). subtransitivity (1+x). exact (pos_plus_lt_compat_l _ _).
    destruct (archimedean_int_bounds x) as [m[?[_[_[Em _]]]]].
    destruct (archimedean_int_bounds y) as [_[_[M[?[_ EM]]]]].
    cut (∀ `{a ∊ Z⁺}, %m + %a < y ∨ ∃ `{i ∊ Z}, x < %i < y). intro P.
      assert (M - m ∊ Z₊). rewrite (flip_pos_minus _ _).
        apply (strictly_order_reflecting % _ _). subtransitivity x. subtransitivity y.
      destruct (P (M-m) _) as [E'|[i[? E']]]. contradict E'. apply (lt_flip _ _).
        preserves_simplify %. now mc_replace (%m+(%M-%m)) with (%M) on F by subring F.
      now exists_sub i.
    apply naturals.induction.
    + intros ?? E'. intuition; left. now rewrite <- E'. now rewrite E'.
    + left. preserves_simplify %. rewrite (_ $ plus_0_r _). subtransitivity x.
    + intros a ? [Ea|?]; [| now right].
      destruct (subcotransitivity E (%m+%(1+a))) as [E'|?]; [right | now left].
      exists_sub (m+a). revert E'. preserves_simplify %. intro E'. split; trivial.
      mc_replace (%m+(1+%a)) with (1+(%m+%a)) on F in E' by subring F.
      now apply (strictly_order_reflecting (1+) _ _).
  Qed.

  Lemma archimedean_rationals_dense x `{x ∊ F} y `{y ∊ F}
  : x < y → ∃ `{q ∊ Q}, x < # q < y.
  Proof. intro E. assert (y-x ∊ F₊) by now rewrite flip_pos_minus.
    destruct (archimedean 1 (y-x)) as [n [? En]].
    rewrite (_ $ mult_minus_distr_l _ _ _), (flip_lt_minus_r _ _ _) in En.
    destruct (archimedean_int_between _ _ En) as [i[??]].
    exists_sub (integers_to_ring Z Q i / integers_to_ring Z Q n).
    preserves_simplify #. rewrite <-(mult_inv_lt_cancel_l _ _ _),<-(mult_inv_lt_cancel_r _ _ _).
    let f := constr:(# ∘ integers_to_ring Z Q) in
      change (x*(f n) < f i < y * (f n)); rewrite !(_ $ integers.to_ring_unique f _).
    now rewrite 2!(_ $ commutativity (.*.) _ (%n)).
  Qed.
End archimedean_property.

Section archimedean_property_converse.
  Context `{Field (F:=F)} {Ale: Le _} {Alt: Lt _} `{!FullPseudoSemiRingOrder F}.
  Context `{Rationals (Q:=Q)}.
  Notation "#" := (rationals_to_field Q F).
  Notation Z := the_integers.
  Notation "%" := (integers_to_ring Z F).

  Lemma rationals_dense_archimedean :
    (∀ `{x ∊ F} `{y ∊ F}, x < y → ∃ `{q ∊ Q}, x < # q < y)
  →  ∀ `{x ∊ F₊} `{y ∊ F₊}, ∃ `{n ∊ Z₊}, x < % n * y.
  Proof. intros P x ? y ?.
    destruct (P _ _ _ _ (pos_plus_lt_compat_r (x/y) 1)) as [q[?[E _]]].
    destruct (rationals_int_strict_bound (integers_to_ring Z Q) q) as [n[? E2]].
    apply (strictly_order_preserving # _ _) in E2.
    let f := constr:(# ∘ integers_to_ring Z Q) in
      change (# q < f n) in E2; rewrite (_ $ integers.to_ring_unique f _) in E2.
    assert (n ∊ Z₊). apply (reflects_pos %). apply _. split. apply _.
      subtransitivity (# q). subtransitivity (x/y). now destruct (_ : x/y ∊ F₊).
    exists_sub n. rewrite (mult_inv_lt_cancel_l _ _ _). subtransitivity (# q).
  Qed.
End archimedean_property_converse.

Section rationals_archimedean_field.
  Context `{Rationals (Q:=Q)} `{Le _} `{Lt _} `{!FullPseudoSemiRingOrder Q}.

  Notation f := (rationals_to_field the_ae_rationals Q).

  Lemma rationals_archimedean_field : ArchimedeanOrderedField Q.
  Proof. split; try apply _.
  + apply rationals_dense_archimedean. intros x ? y ? E.
    exists_sub ((x+y)/2). rewrite <-(_ $ to_rationals_unique id _). unfold id.
    rewrite <-(mult_inv_lt_cancel_l _ _ _),<-(mult_inv_lt_cancel_r _ _ _).
    rewrite !(_ $ mult_2_plus_r _). split.
    now apply (strictly_order_preserving (x+) _ _).
    now apply (strictly_order_preserving (+y) _ _).
  + exact msp_nonneg.
  + exact msp_ball_inf.
  + intros. now rewrite (rationals_ball_def f _ _ _), (abs.abs_le_iff _ _).
  Qed.
End rationals_archimedean_field.

Hint Extern 2 (ArchimedeanOrderedField the_ae_rationals) => eapply @rationals_archimedean_field : typeclass_instances.

Local Notation B := TheAERationals.A.
Local Notation Q := the_ae_rationals.
Local Notation "Q∞" := (aff_ext Q).
Local Notation Qfull := (aff_ext_full Q).


Section contents.
  Context `{ArchimedeanOrderedField (F:=F)}.

  Local Notation "#" := (rationals_to_field Q F).

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

End contents.

Hint Extern 15 (MetricSpace ?F) =>
  let H := constr:(_ : ArchimedeanOrderedField F) in eapply (arch_ord_field_metric (H:=H)) : typeclass_instances.

Section maps.
  Context `{ArchimedeanOrderedField (F:=F1)}.
  Context `{ArchimedeanOrderedField (F:=F2)}.
  Context (f:F1 ⇀ F2) `{!Ring_Morphism F1 F2 f}.

  Notation "%" := (rationals_to_field Q F1).
  Notation "#" := (rationals_to_field Q F2).

  Instance arch_ord_field_dense: Dense F2 f⁺¹(F1).
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

  Lemma arch_ord_field_preserving_iff_reflecting :
    StrictlyOrderPreserving F1 F2 f ↔ StrictlyOrderReflecting F1 F2 f.
  Proof. split; intro; split; try apply _; intros x ? y ? E.
  + destruct (archimedean_rationals_dense _ _ E) as [q'[? [Eq1' Eq2']]].
    destruct (archimedean_rationals_dense _ _ Eq1') as [q[? [Eq1 Eq2]]].
    destruct (archimedean_rationals_dense _ _ Eq2') as [q''[? [Eq1'' Eq2'']]].
    assert (% q < % q') as E'.
      apply (strictly_order_preserving % _ _). now apply (strictly_order_reflecting # _ _).
    destruct (subcotransitivity E' x) as [Ex|Ex].
      apply (strictly_order_preserving f _ _) in Ex.
      setoid_rewrite (rationals_to_field_unique Q (f ∘ %) q q) in Ex; try now red_sig.
      now destruct (lt_flip _ _ Ex).
    subtransitivity (% q').
    assert (% q' < % q'') as E''.
      apply (strictly_order_preserving % _ _). now apply (strictly_order_reflecting # _ _).
    destruct (subcotransitivity E'' y) as [Ey|Ey]; trivial.
      apply (strictly_order_preserving f _ _) in Ey.
      setoid_rewrite (rationals_to_field_unique Q (f ∘ %) q'' q'') in Ey; try now red_sig.
      now destruct (lt_flip _ _ Ey).
  + destruct (archimedean_rationals_dense _ _ E) as [q'[? [Eq1' Eq2']]].
    destruct (archimedean_rationals_dense _ _ Eq1') as [q[? [Eq1 Eq2]]].
    destruct (archimedean_rationals_dense _ _ Eq2') as [q''[? [Eq1'' Eq2'']]].
    assert (# q < # q') as E'.
      apply (strictly_order_preserving # _ _). now apply (strictly_order_reflecting % _ _).
    destruct (subcotransitivity E' (f x)) as [Ex|Ex].
      rewrite <-(rationals_to_field_unique Q (f ∘ %) q q) in Ex; try now red_sig.
      unfold compose in Ex. apply (strictly_order_reflecting f _ _) in Ex.
      now destruct (lt_flip _ _ Ex).
    subtransitivity (# q').
    assert (# q' < # q'') as E''.
      apply (strictly_order_preserving # _ _). now apply (strictly_order_reflecting % _ _).
    destruct (subcotransitivity E'' (f y)) as [Ey|Ey]; trivial.
      rewrite <-(rationals_to_field_unique Q (f ∘ %) q'' q'') in Ey; try now red_sig.
      unfold compose in Ey. apply (strictly_order_reflecting f _ _) in Ey.
      now destruct (lt_flip _ _ Ey).
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

Lemma arch_ord_field_prelength `{ArchimedeanOrderedField (F:=F)}
  : PrelengthMetricSpace F.
Proof.
  pose proof isometric_image_prelength (rationals_to_field Q F).
  pose proof arch_ord_field_dense (rationals_to_field Q F).
  exact ( dense_subset_prelength (rationals_to_field Q F)⁺¹(Q) ).
Qed.

Hint Extern 15 (PrelengthMetricSpace ?F) =>
  let H := constr:(_ : ArchimedeanOrderedField F) in eapply (arch_ord_field_prelength (H:=H)) : typeclass_instances.

Hint Extern 0 (_ ∊ UniformlyContinuous _ _) => red : typeclass_instances.

Section misc.
  Context `{ArchimedeanOrderedField (F:=F)}.
  Notation "#" := (rationals_to_field Q F).

  Lemma split_sum_bound q `{q ∊ Q} a₁ `{a₁ ∊ F} a₂ `{a₂ ∊ F}
    : #q < a₁ + a₂ → ∃ `{q₁ ∊ Q} `{q₂ ∊ Q}, q = q₁ + q₂ ∧ #q₁ < a₁ ∧ #q₂ < a₂.
  Proof. intro E. rewrite <-(flip_lt_minus_l _ _ _) in E.
    destruct (archimedean_rationals_dense _ _ E) as [q₁[? [E1 E2]]].
    exists_sub q₁ (q-q₁). split. subring Q. split; trivial.
    preserves_simplify #.
    now rewrite  (flip_lt_minus_l _ _ _), (_ $ commutativity (+) _ _),
               <-(flip_lt_minus_l _ _ _).
  Qed.

  Lemma split_prod_bound q `{q ∊ Q₊} a₁ `{a₁ ∊ F₊} a₂ `{a₂ ∊ F₊}
    : #q < a₁ * a₂ → ∃ `{q₁ ∊ Q₊} `{q₂ ∊ Q₊}, q = q₁ * q₂ ∧ #q₁ < a₁ ∧ #q₂ < a₂.
  Proof. intro E. rewrite (mult_inv_lt_cancel_l _ _ _) in E.
    destruct (archimedean_rationals_dense _ _ E) as [q₁[? [E1 E2]]].
    assert (q₁ ∊ Q₊). apply (reflects_pos #). apply _. split. apply _.
      subtransitivity (#q / a₂). now destruct (_ : #q / a₂ ∊ F₊).
    exists_sub q₁ (q/q₁). split. subfield Q. split; trivial.
    preserves_simplify #.
    now rewrite <-(mult_inv_lt_cancel_l _ _ _), (_ $ commutativity (.*.) _ _),
                  (mult_inv_lt_cancel_l _ _ _).
  Qed.

  Lemma between_mult_le_compat p `{p ∊ Q₊} q `{q ∊ Q₊} x `{x ∊ F} y `{y ∊ F}
    : - #p ≤ x ≤ #p → - #q ≤ y ≤ #q → - #(p*q) ≤ x*y ≤ #(p*q).
  Proof. cut (∀ `{a ∊ F} `{b ∊ F}, #(p*q) < a*b → #p < a ∨ #p < -a ∨ #q < b ∨ #q < -b).
      intro P. rewrite !(le_iff_not_lt_flip _ _). intros [E1 E2] [E3 E4].
      rewrite <-(flip_lt_negate _ _), (_ $ negate_involutive _) in E1.
      rewrite <-(flip_lt_negate _ _), (_ $ negate_involutive _) in E3.
      split; intro E; [
        rewrite <-(flip_lt_negate _ _), (_ $ negate_involutive _),
                  (_ $ negate_mult_distr_l _ _) in E |];
        destruct (P _ _ _ _ E) as [?|[?|[?|?]]]; try contradiction.
      rewrite <-(_ $ negate_involutive x) in E2. now destruct E2.
    clear dependent x. clear dependent y.
    cut (∀ `{x ∊ F₊} `{y ∊ F₊}, #(p*q) < x*y → #p < x ∨ #q < y).
      intros P x ? y ? E.
      assert (x*y ∊ F₊). split. apply _. subtransitivity (#(p*q)).
        now destruct (_ : #(p*q) ∊ F₊).
      destruct (pos_mult_decompose x y) as [[??]|[??]];
        [| rewrite <-(_ $ negate_mult_negate x y) in E];
        pose proof (P _ _ _ _ E); tauto.
    intros x ? y ? E.
    destruct (split_prod_bound _ _ _ E) as [p'[?[q'[? [E1[E2 E3]]]]]].
    destruct (decide_sub (≤) p p') as [Ep|Ep]; [left|right].
      apply (le_lt_trans _ (#p') _); trivial. now apply (order_preserving # _ _).
    cut (q ≤ q'). intro Eq.
      apply (le_lt_trans _ (#q') _); trivial. now apply (order_preserving # _ _).
    apply (order_reflecting (p*.) _ _). rewrite (_ $ E1).
      apply (order_preserving (.*q') _ _). now apply (le_flip _ _).
  Qed.
End misc.

Section ops.
  Context `{ArchimedeanOrderedField (F:=F)}.

  Add Ring F'' : (stdlib_ring_theory F).

  Notation "#" := (rationals_to_field Q F).

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

  Instance arch_ord_field_plus_isometry_1 a `{a ∊ F} : Isometry F F (a +).
  Proof. split; try apply _. intros ??????. rewrite !(arch_ord_field_ball _ _ _).
    now mc_replace (a + x - (a + y)) with (x-y) on F by subring F.
  Qed.

  Instance arch_ord_field_plus_isometry_2 a `{a ∊ F} : Isometry F F (+ a).
  Proof. split; try apply _. intros ??????. rewrite !(arch_ord_field_ball _ _ _).
    now mc_replace (x + a - (y + a)) with (x-y) on F by subring F.
  Qed.

  Local Ltac set_min δ a b Ea Eb :=
    set (δ := @meet _ (min (X:=Q)) a b); assert (δ ∊ Q₊) by (subst δ; apply _);
    assert (δ ≤ a) as Ea by (subst δ; exact (meet_lb_l (Ameet:=(min (X:=Q))) (L:=Q) _ _));
    assert (δ ≤ b) as Eb by (subst δ; exact (meet_lb_r (Ameet:=(min (X:=Q))) (L:=Q) _ _)).


  Instance arch_ord_field_mult_ufm_cont b `{b ∊ Q₊} c `{c ∊ Q₊} :
    UniformlyContinuous ((F ⊓ ball b 0) * (F ⊓ ball c 0)) (Aball:=_:Ball (F*F) ) F
      (uncurry (.*.) : F*F ⇀ F).
  Proof.
    pose proof sub_metric_space (X:=(F*F)) : MetricSpace ((F ⊓ ball b 0) * (F ⊓ ball c 0)).
    split; try apply _.
    rewrite <-(_:SubsetOf (F*F ⇒ F) ((F ⊓ ball b 0) * (F ⊓ ball c 0) ⇒ F)). apply _.
    intros q ?. set_min a (q/2/b) (q/2/c) Eb Ec. exists_sub a.
    intros [x₁ x₂] [[? Bx1][? Bx2]] [y₁ y₂] [[? By1][? By2]] [B1 B2]. simpl in B1,B2. simpl.
    red in Bx1,Bx2,By1,By2.
    subsymmetry in Bx1. subsymmetry in Bx2. subsymmetry in By1. subsymmetry in By2.
    revert Bx1 Bx2 By1 By2 B1 B2. rewrite !(arch_ord_field_ball _ _ _).
    intros Bx1 Bx2 By1 By2 B1 B2.
    rewrite (_ $ negate_0), (_ $ plus_0_r _) in Bx1.
    rewrite (_ $ negate_0), (_ $ plus_0_r _) in Bx2.
    rewrite (_ $ negate_0), (_ $ plus_0_r _) in By1.
    rewrite (_ $ negate_0), (_ $ plus_0_r _) in By2.
    mc_replace (x₁ * x₂ - y₁ * y₂) with ((x₁-y₁)*x₂ + y₁*(x₂-y₂)) on F by subring F.
    mc_replace q with (q/2+q/2) on Q by subfield Q.
    rewrite (_ $ preserves_plus _ _), (_ $ negate_plus_distr _ _).
    apply (plus_le_compat_2 _ _ _ _ _ _).
    + mc_replace (q/2) with ((q/2/c)*c) on Q by subfield Q.
      apply (between_mult_le_compat _ _ _ _); trivial.
      split. subtransitivity (-#a); try easy.
        apply (flip_le_negate _ _). now apply (order_preserving # _ _).
      subtransitivity (#a); try easy. now apply (order_preserving # _ _).
    + mc_replace (q/2) with (b*(q/2/b)) on Q by subfield Q.
      apply (between_mult_le_compat _ _ _ _); trivial.
      split. subtransitivity (-#a); try easy.
        apply (flip_le_negate _ _). now apply (order_preserving # _ _).
      subtransitivity (#a); try easy. now apply (order_preserving # _ _).
  Qed.

(*
  Instance arch_ord_field_mult_cont_1 b `{b ∊ Q₊} a {el:a ∊ F ⊓ (ball b 0)} : UniformlyContinuous F F (a *.).
  Proof. destruct el as [? E]. red in E. subsymmetry in E. split; try apply _. intros ??.
    exists_sub (ε/b). intros ????. revert E. rewrite !(arch_ord_field_ball _ _ _).
    mc_replace (a-0) with a on F by subring F.
    mc_replace (a*x-a*y) with (a*(x-y)) on F by subring F.
    intros E1 E2. mc_replace ε with (b*(ε/b)) on Q by subfield Q.
    now apply (between_mult_le_compat _ _ _ _).
  Qed.

  Instance arch_ord_field_mult_cont b `{b ∊ Q₊} c `{c ∊ Q₊}
    : UniformlyContinuous (F ⊓ (ball b 0)) (UniformlyContinuous (F ⊓ (ball c 0)) F) (.*.).
  Proof. split.
  + exact sub_metric_space.
  + pose proof sub_metric_space : MetricSpace (F ⊓ ball c 0). apply _.
  + intros ?? [[el1 el2]E]. split. split; red; apply (restrict_uniformly_continuous _ _).
    intros ?? [[[??][??]]E2]. destruct el1,el2. red_sig. now rewrite (_ $ E), (_ $ E2).
  + intros ε ?. exists_sub (ε/c). intros x [? Ex] y [? Ey].
    rewrite !(arch_ord_field_ball _ _ _). intros E. split. apply _. intros z [? Ez].
    red in Ez. subsymmetry in Ez. revert Ez.
    rewrite !(arch_ord_field_ball _ _ _), (_ $ negate_0), (_ $ plus_0_r _).
    intro. rewrite <-(_ $ mult_minus_distr_r _ _ _).
    mc_replace ε with ((ε/c)*c) on Q by subfield Q.
    now apply (between_mult_le_compat _ _ _ _).
  Qed.
*)

  Instance: ∀ `{b ∊ Q₊}, (F ⊓ ((≤ -#b) ⊔ (#b ≤))) ⊆ F ₀.
  Proof. split. apply _.
  + intros ?? E [? E2].
    split. now rewrite <-E.
    destruct E2 as [?|?]; [left|right]; red; now rewrite <-E.
  + intros x [?[E1|E2]]; [apply neg_nonzero | apply pos_nonzero]; split; try apply _.
    * red in E1. apply (le_lt_trans _ (-#b) _); trivial. now destruct (_ : - # b ∊ F₋).
    * red in E2. apply (lt_le_trans _ ( #b) _); trivial. now destruct (_ :   # b ∊ F₊).
  Qed.


  Instance: ∀ `{b ∊ Q₊}, (F ⊓ ((≤ -#b) ⊔ (#b ≤))) ⊆ F.
  Proof. transitivity (F ₀); apply _. Qed.

  Local Open Scope grp_scope.


  Lemma bounded_away_from_zero `{b ∊ Q₊} x `{el: x ∊ (F ⊓ ((≤ -#b) ⊔ (#b ≤)))}
    : x ∊ F ₀ ∧ - #b⁻¹ ≤ x⁻¹ ≤ #b⁻¹ .
  Proof.  assert (x ∊ F ₀) by now apply (_ : SubsetOf (F ⊓ ((≤ -#b) ⊔ (#b ≤))) (F ₀)).
    split; trivial. preserves_simplify #.
    destruct el as [_ [E|E]]; red in E.
    + assert (x ∊ F₋). split. apply _. apply (le_lt_trans _ (-#b) _); trivial.
        now destruct (_ : - # b ∊ F₋).
      split.
      * rewrite <-(flip_le_negate _ _), (_ $ negate_involutive _), <-(_ $ mult_inv_negate _).
        apply (flip_le_mult_inv _ _).
        now rewrite <-(flip_le_negate _ _), (_ $ negate_involutive _).
      * apply (lt_le _ _). subtransitivity 0. now destruct (_ : x⁻¹ ∊ F₋).
        now destruct (_ : (# b)⁻¹ ∊ F₊).
    + assert (x ∊ F₊). split. apply _. apply (lt_le_trans _ (#b) _); trivial.
        now destruct (_ : # b ∊ F₊).
      split.
      * apply (lt_le _ _). subtransitivity 0. now destruct (_ : -(# b)⁻¹ ∊ F₋).
          now destruct (_ : x⁻¹ ∊ F₊).
      * now apply (flip_le_mult_inv _ _).
  Qed.

  Instance arch_ord_field_inv_cont b `{b ∊ Q₊}
    : UniformlyContinuous (F ⊓ ((≤ -#b) ⊔ (#b ≤))) (F ₀) inv.
  Proof. split; try exact sub_metric_space.
  + rewrite <-(_ : SubsetOf (F ₀ ⇒ F ₀) (F ⊓ ((≤ -#b) ⊔ (#b ≤)) ⇒ F ₀)). apply _.
  + intros ε ?. exists_sub (ε*b*b). intros x ? y ?.
    destruct (bounded_away_from_zero x) as [? Ex].
    destruct (bounded_away_from_zero y) as [? Ey].
    rewrite !(arch_ord_field_ball _ _ _).
    intros [??]. assert (- # (ε * b * b) ≤ y - x ≤ # (ε * b * b)).
      split; rewrite <-(flip_le_negate _ _), <-(_ $ negate_swap_r _ _); trivial.
      now rewrite (_ $ negate_involutive _).
    assert (x⁻¹ - y⁻¹ = (y-x)*(x⁻¹/y)) as E.
      apply (right_cancellation (.*.) (x*y) F _ _).
      subtransitivity (y * (x/x) - x * (y/y)). subring F.
      subtransitivity ((y-x)*(x/x)*(y/y)); [|subring F].
      rewrite !(_ $ field_inv_r _). subring F.
    rewrite (_ $ E).
    mc_replace ε with ((ε*b*b)*(b⁻¹/b)) on Q by subfield Q.
    apply (between_mult_le_compat _ _ _ _); trivial.
    apply (between_mult_le_compat _ _ _ _); trivial.
  Qed.

End ops.

Section misc2.
  Context `{ArchimedeanOrderedField (F:=F)}.

  Add Ring F4 : (stdlib_ring_theory F).

  Notation "#" := (rationals_to_field Q F).

  Open Scope mc_abs_scope.

  Lemma arch_ord_field_point_bounded x `{x ∊ F} : ∃ `{b ∊ Q₊}, x ∊ F ⊓ ball b 0.
  Proof. destruct (archimedean_int_bounds x) as [a'[?[b'[? E]]]].
    rewrite <-2!(_ $ integers.to_ring_unique (# ∘ integers_to_ring _ Q) _) in E.
    revert E. unfold compose.
    set (a:=integers_to_ring _ Q a'). assert (a ∊ Q). subst a. apply _.
    set (b:=integers_to_ring _ Q b'). assert (b ∊ Q). subst b. apply _.
    intro E. assert ((|a| ⊔ |b|) ∊ Q₊).
      split. apply _. red. rewrite (lt_iff_le_apart _ _). split.
      subtransitivity (|a|). now destruct (_ : (|a|) ∊ Q⁺). exact (join_ub_l _ _).
      rewrite (standard_uneq _ _). intro E'.
      cut (a=b). apply (lt_ne _ _). apply (strictly_order_reflecting # _ _).
        now subtransitivity x.
      apply (subtransitivity (S:=Q)) with 0; try apply _; [|subsymmetry];
        rewrite <-(abs_0_iff _), (eq_iff_le _ _).
      split. rewrite (_ $ E'). exact (join_ub_l _ _). now destruct (_ : |a| ∊ Q⁺).
      split. rewrite (_ $ E'). exact (join_ub_r _ _). now destruct (_ : |b| ∊ Q⁺).
    exists_sub ((|a| ⊔ |b|)).
    pose proof (join_ub_l (|a|) (|b|)) as Ea. rewrite (abs_le_iff _ _) in Ea.
    pose proof (join_ub_r (|a|) (|b|)) as Eb. rewrite (abs_le_iff _ _) in Eb.
    split. apply _. red. subsymmetry. rewrite (arch_ord_field_ball _ _ _).
    mc_replace (x-0) with x on F by subring F.
    split; apply (lt_le _ _); red.
      apply (le_lt_trans _ (#a) _); try easy. rewrite <-(_ $ preserves_negate _).
        now apply (order_preserving # _ _).
      apply (lt_le_trans _ (#b) _); try easy.
        now apply (order_preserving # _ _).
  Qed.


  Instance open_upper_interval a `{a ∊ F} : Open F (F ⊓ (a <)).
  Proof.
    assert (F ⊓ (a <) ⊆ F).
      split; try apply _. intros ?? E [??]. unfold_sigs. split. apply _. red. now rewrite <-(_ $ E).
    split; try apply _.
    intros x [? E]. red in E.
      destruct (archimedean_rationals_dense _ _ E) as [p [? [Ep1 Ep2]]].
      destruct (archimedean_rationals_dense _ _ Ep2) as [q [? [Eq1 Eq2]]].
    assert (q-p ∊ Q₊). apply (flip_pos_minus _ _). now apply (strictly_order_reflecting # _ _).
    exists_sub (q-p).
    intros y [? By]. split. apply _. red.
    red in By. rewrite (arch_ord_field_ball _ _ _) in By. destruct By as [_ By].
    subtransitivity (#p). apply (lt_le_trans _ (x-#q+#p) _).
      apply (pos_plus_lt_compat_l _). now apply (flip_pos_minus _ _).
    mc_replace (x-#q+#p) with (x+#p-#q) on F by subring F.
    rewrite (flip_le_minus_l _ _ _), (_ $ commutativity (+) y _),
      <-(flip_le_minus_l _ _ _).
    mc_replace (x+#p-y) with (x-y+#p) on F by subring F.
    rewrite <-(flip_le_minus_r _ _ _).
    revert By. preserves_simplify #. tauto.
  Qed.

  Instance open_lower_interval a `{a ∊ F} : Open F (F ⊓ (< a)).
  Proof.
    assert (F ⊓ (< a) ⊆ F).
      split; try apply _. intros ?? E [??]. unfold_sigs. split. apply _. red. now rewrite <-(_ $ E).
    split; try apply _.
    intros x [? E]. red in E.
      destruct (archimedean_rationals_dense _ _ E) as [p [? [Ep1 Ep2]]].
      destruct (archimedean_rationals_dense _ _ Ep1) as [q [? [Eq1 Eq2]]].
    assert (p-q ∊ Q₊). apply (flip_pos_minus _ _). now apply (strictly_order_reflecting # _ _).
    exists_sub (p-q).
    intros y [? By]. split. apply _. red.
    red in By. rewrite (arch_ord_field_ball _ _ _) in By. destruct By as [By _].
    subtransitivity (#p). apply (le_lt_trans _ (x+#p-#q) _).
    rewrite (flip_le_minus_r _ _ _), (_ $ commutativity (+) y _),
      <-(flip_le_minus_r _ _ _).
    mc_replace (x+#p-y) with (x-y+#p) on F by subring F.
    rewrite <-(flip_le_minus_l _ _ _).
    revert By. preserves_simplify #. rewrite <-(_ $ negate_swap_r _ _). tauto.
    rewrite (flip_lt_minus_l _ _ _), (_ $ commutativity (+) _ (#q)).
    pose proof (strictly_order_preserving (+ (#p)) x (#q)) as P. now apply P.
  Qed.

  Lemma split_interval a `{a ∊ F} b `{b ∊ F} : (F ⊓ ((a <) ⊓ (< b))) = (F ⊓ (a <)) ⊓ (F ⊓ (< b)).
  Proof. firstorder. Qed.

  Instance open_interval a `{a ∊ F} b `{b ∊ F} : Open F (F ⊓ ((a <) ⊓ (< b))).
  Proof. rewrite (split_interval _ _). apply _. Qed.

  Instance open_ball_at_0 r `{r ∊ Q₊} : (F ⊓ ((-#r <) ⊓ (< #r))) ⊆ (F ⊓ ball r 0).
  Proof. split; try apply _. exact subsetoid_a.
    intros x [?[??]]. split; trivial. red. subsymmetry. rewrite (arch_ord_field_ball _ _ _).
    mc_replace (x-0) with x on F by subring F.
    split; now apply (lt_le _ _).
  Qed.


End misc2.


