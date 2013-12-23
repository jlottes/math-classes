Require Import
  abstract_algebra interfaces.orders interfaces.integers interfaces.rationals 
  interfaces.archimedean_fields
  theory.setoids theory.fields theory.rationals orders.fields orders.rationals
  stdlib_field_dec misc.quote
  the_integers the_rationals nonneg_integers_naturals theory.naturals
  orders.minmax orders.lattices lattice_ordered_rings orders.abs.


Local Open Scope grp_scope.

Section archimedean_property.
  Context `{ArchimedeanField (F:=F)}.
  Context `{Rationals (Q:=Q)}.
  Notation "#" := (rationals_to_field Q F).
  Notation Z := the_integers.
  Notation "%" := (integers_to_ring Z F).

  Add Ring F : (stdlib_ring_theory F).

  Lemma archimedean x `{x ∊ F₊} y `{y ∊ F₊} : ∃ `{n ∊ Z₊}, x < %n * y .
  Proof. destruct (archimedean_def (N:=Z⁺) x y) as [n[? E]].
    assert (naturals_to_semiring Z⁺ F⁺ n ∊ F). apply (_ : F⁺ ⊆ F). apply _.
    rewrite <-( F $ to_semiring_unique (%:Z⁺ ⇀ F⁺) n ) in E.
    destruct (pos_or_nonpos n). now exists_sub n.
    destruct (pos_not_neg x). split. apply _. red.
    now rewrite (Z $ nonneg_nonpos_0 n), (_ $ preserves_0), (_ $ mult_0_l _) in E.
  Qed.

  Lemma archimedean_int_bounds x `{x ∊ F} : ∃ `{a ∊ Z} `{b ∊ Z}, %a < x < %b.
  Proof. destruct (cotransitivity (pos_plus_lt_compat_r x 1) 0).
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
        preserves_simplify %. now mc_replace (%m+(%M-%m)) with (%M) on F by setring F.
      now exists_sub i.
    apply naturals.induction.
    + intros ?? E'; unfold_sigs. intuition; left. now rewrite <- (_ $ E'). now rewrite (_ $ E').
    + left. preserves_simplify %. rewrite (_ $ plus_0_r _). subtransitivity x.
    + intros a ? [Ea|?]; [| now right].
      destruct (cotransitivity E (%m+%(1+a))) as [E'|?]; [right | now left].
      exists_sub (m+a). revert E'. preserves_simplify %. intro E'. split; trivial.
      mc_replace (%m+(1+%a)) with (1+(%m+%a)) on F in E' by setring F.
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

  Lemma archimedean_rational_bounds x `{x ∊ F}
    : ∃ `{p ∊ Q} `{q ∊ Q}, # p < x < # q.
  Proof.
    destruct (archimedean_rationals_dense (x-1) x) as [p[elp[_ E1]]].
      apply (flip_pos_minus _ _). mc_replace (x-(x-1)) with (1:F) on F by setring F. apply _.
    destruct (archimedean_rationals_dense x (x+1)) as [q[elq[E2 _]]].
      apply (flip_pos_minus _ _). mc_replace (x+1-x) with (1:F) on F by setring F. apply _.
    exists_sub p q. intuition.
  Qed.

  Context `{Le _} `{Lt _} `{!FullPseudoSemiRingOrder Q}.

  Lemma archimedean_rationals_dense_pos x `{x ∊ F₊} : ∃ `{q ∊ Q₊}, #q < x.
  Proof. destruct (archimedean_rationals_dense 0 x) as [q[elq[E1 E2]]]. apply (_ : x ∊ F₊).
    assert (q ∊ Q₊). apply (reflects_pos #). apply _. split. apply _. exact E1.
    now exists_sub q.
  Qed.

  Lemma archimedean_rationals_bound_pos x `{x ∊ F₊} : ∃ `{q ∊ Q₊}, x < #q.
  Proof. destruct (archimedean_rationals_dense_pos x⁻¹) as [q[elq E]].
    exists_sub q⁻¹. preserves_simplify #. now apply (flip_lt_mult_inv_r _ _).
  Qed.

  Lemma archimedean_rationals_bound_nonneg x `{x ∊ F⁺} : ∃ `{q ∊ Q⁺}, x < #q.
  Proof. destruct (archimedean_rational_bounds x) as [_[_[q[elq[_ E]]]]].
    cut (q ∊ Q⁺). intro. now exists_sub q.
    apply (reflects_nonneg #). apply _. split. apply _. red.
    subtransitivity x. apply (_ : x ∊ F⁺). now apply (lt_le _ _).
  Qed.

End archimedean_property.

Section archimedean_property_converse.
  Context `{Field (F:=F)} {Ale: Le _} {Alt: Lt _} `{!FullPseudoSemiRingOrder F}.
  Context `{Rationals (Q:=Q)}.
  Notation "#" := (rationals_to_field Q F).
  Notation Z := the_integers.
  Notation "%" := (integers_to_ring Z F).

  Context (rationals_dense : ∀ `{x ∊ F} `{y ∊ F}, x < y → ∃ `{q ∊ Q}, x < # q < y) .

  Lemma rationals_dense_archimedean_aux x `{x ∊ F₊} y `{y ∊ F₊} : ∃ `{n ∊ Z₊}, x < % n * y.
  Proof.
    destruct (rationals_dense _ _ _ _ (pos_plus_lt_compat_r (x/y) 1)) as [q[?[E _]]].
    destruct (rationals_int_bounds (integers_to_ring Z Q) q) as [n[? [? E2]]].
    mc_replace (integers_to_ring Z Q n + 1) with (integers_to_ring Z Q (n+1)) on Q in E2
      by now preserves_simplify (integers_to_ring Z Q).    
    apply (strictly_order_preserving # _ _) in E2.
    let f := constr:(# ∘ integers_to_ring Z Q) in
      change (# q < f (n+1)) in E2; rewrite (_ $ integers.to_ring_unique f _) in E2.
    assert (n+1 ∊ Z₊). apply (reflects_pos %). apply _. split. apply _. red.
      subtransitivity (# q). subtransitivity (x/y). now destruct (_ : x/y ∊ F₊).
    exists_sub (n+1). rewrite (mult_inv_lt_cancel_l _ _ _). subtransitivity (# q).
  Qed.

  Lemma rationals_dense_archimedean `{Naturals (N:=N)} x `{x ∊ F₊} y `{y ∊ F₊}
      : ∃ `{n ∊ N}, x < (naturals_to_semiring N F⁺ n) * y .
  Proof. destruct (rationals_dense_archimedean_aux x y) as [n[? E]].
    exists_sub (naturals_to_semiring Z⁺ N n).
    assert ((naturals_to_semiring N F⁺ ∘ naturals_to_semiring Z⁺ N) n ∊ F).
      apply (_ : F⁺ ⊆ F). apply _.
    now setoid_rewrite <-(F $ to_semiring_unique_alt (%:Z⁺ ⇀ F⁺) 
        (naturals_to_semiring N F⁺ ∘ naturals_to_semiring Z⁺ N) n ).
  Qed.

End archimedean_property_converse.

Section rationals_archimedean_field.
  Context `{Rationals (Q:=Q)} `{Le _} `{Lt _} `{!FullPseudoSemiRingOrder Q}.

  Lemma rationals_archimedean_field : ArchimedeanField Q.
  Proof. split; try apply _.
  + apply rationals_dense_archimedean. intros x ? y ? E.
    exists_sub ((x+y)/2). rewrite <-(_ $ to_rationals_unique id _). unfold id.
    rewrite <-(mult_inv_lt_cancel_l _ _ _),<-(mult_inv_lt_cancel_r _ _ _).
    rewrite !(_ $ mult_2_plus_r _). split.
    now apply (strictly_order_preserving (x+) _ _).
    now apply (strictly_order_preserving (+y) _ _).
  Qed.
End rationals_archimedean_field.

Hint Extern 2 (ArchimedeanField the_rationals) => eapply @rationals_archimedean_field : typeclass_instances.
Hint Extern 15 (ArchimedeanField ?Q) =>
  let H := constr:(_ : Rationals Q) in eapply (rationals_archimedean_field (H:=H)) : typeclass_instances.

Section maps.
  Context `{ArchimedeanField (F:=F1)}.
  Context `{ArchimedeanField (F:=F2)}.
  Context (f:F1 ⇀ F2) `{!SemiRing_Morphism F1 F2 f}.

  Notation Q := the_rationals.

  Notation "%" := (rationals_to_field Q F1).
  Notation "#" := (rationals_to_field Q F2).

  Lemma arch_field_preserving_iff_reflecting :
    StrictlyOrderPreserving F1 F2 f ↔ StrictlyOrderReflecting F1 F2 f.
  Proof. split; intro; split; try apply _; intros x ? y ? E.
  + destruct (archimedean_rationals_dense _ _ E) as [q'[? [Eq1' Eq2']]].
    destruct (archimedean_rationals_dense _ _ Eq1') as [q[? [Eq1 Eq2]]].
    destruct (archimedean_rationals_dense _ _ Eq2') as [q''[? [Eq1'' Eq2'']]].
    assert (% q < % q') as E'.
      apply (strictly_order_preserving % _ _). now apply (strictly_order_reflecting # _ _).
    destruct (cotransitivity E' x) as [Ex|Ex].
      apply (strictly_order_preserving f _ _) in Ex.
      setoid_rewrite (rationals_to_field_unique Q (f ∘ %) q q) in Ex; try now red_sig.
      now destruct (lt_flip _ _ Ex).
    subtransitivity (% q').
    assert (% q' < % q'') as E''.
      apply (strictly_order_preserving % _ _). now apply (strictly_order_reflecting # _ _).
    destruct (cotransitivity E'' y) as [Ey|Ey]; trivial.
      apply (strictly_order_preserving f _ _) in Ey.
      setoid_rewrite (rationals_to_field_unique Q (f ∘ %) q'' q'') in Ey; try now red_sig.
      now destruct (lt_flip _ _ Ey).
  + destruct (archimedean_rationals_dense _ _ E) as [q'[? [Eq1' Eq2']]].
    destruct (archimedean_rationals_dense _ _ Eq1') as [q[? [Eq1 Eq2]]].
    destruct (archimedean_rationals_dense _ _ Eq2') as [q''[? [Eq1'' Eq2'']]].
    assert (# q < # q') as E'.
      apply (strictly_order_preserving # _ _). now apply (strictly_order_reflecting % _ _).
    destruct (cotransitivity E' (f x)) as [Ex|Ex].
      rewrite <-(rationals_to_field_unique Q (f ∘ %) q q) in Ex; try now red_sig.
      unfold compose in Ex. apply (strictly_order_reflecting f _ _) in Ex.
      now destruct (lt_flip _ _ Ex).
    subtransitivity (# q').
    assert (# q' < # q'') as E''.
      apply (strictly_order_preserving # _ _). now apply (strictly_order_reflecting % _ _).
    destruct (cotransitivity E'' (f y)) as [Ey|Ey]; trivial.
      rewrite <-(rationals_to_field_unique Q (f ∘ %) q'' q'') in Ey; try now red_sig.
      unfold compose in Ey. apply (strictly_order_reflecting f _ _) in Ey.
      now destruct (lt_flip _ _ Ey).
  Qed.

End maps.

Section misc.
  Context `{Rationals (Q:=Q)} `{Le _} `{Lt _} `{!FullPseudoSemiRingOrder Q}.
  Context `{ArchimedeanField (F:=F)}.
  Notation "#" := (rationals_to_field Q F).

  Add Field Q : (stdlib_field_dec_theory Q).

  Lemma split_sum_bound_l q `{q ∊ Q} a₁ `{a₁ ∊ F} a₂ `{a₂ ∊ F}
    : #q < a₁ + a₂ → ∃ `{q₁ ∊ Q} `{q₂ ∊ Q}, q = q₁ + q₂ ∧ #q₁ < a₁ ∧ #q₂ < a₂.
  Proof. intro E. rewrite <-(flip_lt_minus_l _ _ _) in E.
    destruct (archimedean_rationals_dense _ _ E) as [q₁[? [E1 E2]]].
    exists_sub q₁ (q-q₁). split. setring Q. split; trivial.
    preserves_simplify #.
    now rewrite  (flip_lt_minus_l _ _ _), (_ $ commutativity (+) _ _),
               <-(flip_lt_minus_l _ _ _).
  Qed.

  Lemma split_sum_bound_r q `{q ∊ Q} a₁ `{a₁ ∊ F} a₂ `{a₂ ∊ F}
    : a₁ + a₂ < #q → ∃ `{q₁ ∊ Q} `{q₂ ∊ Q}, q = q₁ + q₂ ∧ a₁ < #q₁ ∧ a₂ < #q₂.
  Proof. intro E. rewrite <-(flip_lt_minus_r _ _ _) in E.
    destruct (archimedean_rationals_dense _ _ E) as [q₁[? [E1 E2]]].
    exists_sub q₁ (q-q₁). split. setring Q. split; trivial.
    preserves_simplify #.
    now rewrite  (flip_lt_minus_r _ _ _), (_ $ commutativity (+) _ _),
               <-(flip_lt_minus_r _ _ _).
  Qed.

  Lemma split_prod_bound_l q `{q ∊ Q₊} a₁ `{a₁ ∊ F₊} a₂ `{a₂ ∊ F₊}
    : #q < a₁ * a₂ → ∃ `{q₁ ∊ Q₊} `{q₂ ∊ Q₊}, q = q₁ * q₂ ∧ #q₁ < a₁ ∧ #q₂ < a₂.
  Proof. intro E. rewrite (mult_inv_lt_cancel_l _ _ _) in E.
    destruct (archimedean_rationals_dense _ _ E) as [q₁[? [E1 E2]]].
    assert (q₁ ∊ Q₊). apply (reflects_pos #). apply _. split. apply _. red.
      subtransitivity (#q / a₂). apply (_ : #q / a₂ ∊ F₊).
    exists_sub q₁ (q/q₁). split. decfield Q. split; trivial.
    preserves_simplify #.
    now rewrite <-(mult_inv_lt_cancel_l _ _ _), (_ $ commutativity (.*.) _ _),
                  (mult_inv_lt_cancel_l _ _ _).
  Qed.

  Lemma split_prod_bound_r q `{q ∊ Q} a₁ `{a₁ ∊ F₊} a₂ `{a₂ ∊ F₊}
    : a₁ * a₂ < #q → ∃ `{q₁ ∊ Q₊} `{q₂ ∊ Q₊}, q = q₁ * q₂ ∧ a₁ < #q₁ ∧ a₂ < #q₂.
  Proof. intro E. assert (q ∊ Q₊).
      apply (reflects_pos #). apply _. split. apply _. red.
      subtransitivity (a₁ * a₂). apply (_ : a₁ * a₂ ∊ F₊).
    rewrite (mult_inv_lt_cancel_r _ _ _) in E.
    destruct (archimedean_rationals_dense _ _ E) as [q₁[? [E1 E2]]].
    assert (q₁ ∊ Q₊). apply (reflects_pos #). apply _. split. apply _. red.
      subtransitivity a₁ . apply (_ : a₁ ∊ F₊).
    exists_sub q₁ (q/q₁). split. decfield Q. split; trivial.
    preserves_simplify #.
    now rewrite <-(mult_inv_lt_cancel_r _ _ _), (_ $ commutativity (.*.) _ _),
                  (mult_inv_lt_cancel_r _ _ _).
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
      assert (x*y ∊ F₊). split. apply _. red. subtransitivity (#(p*q)).
        now destruct (_ : #(p*q) ∊ F₊).
      destruct (pos_mult_decompose x y) as [[??]|[??]];
        [| rewrite <-(_ $ negate_mult_negate x y) in E];
        pose proof (P _ _ _ _ E); tauto.
    intros x ? y ? E.
    destruct (split_prod_bound_l _ _ _ E) as [p'[?[q'[? [E1[E2 E3]]]]]].
    destruct (decide_sub (≤) p p') as [Ep|Ep]; [left|right].
      apply (le_lt_trans _ (#p') _); trivial. now apply (order_preserving # _ _).
    cut (q ≤ q'). intro Eq.
      apply (le_lt_trans _ (#q') _); trivial. now apply (order_preserving # _ _).
    apply (order_reflecting (p*.) _ _). rewrite (_ $ E1).
      apply (order_preserving (.*q') _ _). now apply (le_flip _ _).
  Qed.

  Lemma le_closed x `{x ∊ F} y `{y ∊ F} : (∀ `{ε ∊ Q₊}, x ≤ y + #ε) → x ≤ y.
  Proof. intro P. rewrite (le_iff_not_lt_flip _ _). intro E.
    rewrite <-(flip_pos_minus _ _) in E. destruct E as [_ E]. red in E.
    destruct (archimedean_rationals_dense _ _ E) as [q[? [E1 E2]]].
    assert (q ∊ Q₊). apply (reflects_pos #). apply _. split; trivial. apply _.
    revert E2. setoid_rewrite <-(le_iff_not_lt_flip _ _).
    apply (flip_le_minus_l _ _ _). rewrite (_ $ commutativity (+) _ _).
    now apply (P _ _).
  Qed.

  Lemma eq_closed x `{x ∊ F} y `{y ∊ F} : (∀ `{ε ∊ Q₊}, y - #ε ≤ x ≤ y + #ε) → x = y.
  Proof. intro P. apply (antisymmetry le _ _).
  + apply (le_closed _ _). intros ε ?. apply (P _ _).
  + apply (le_closed _ _). intros ε ?. apply (flip_le_minus_l _ _ _). apply (P _ _).
  Qed.

End misc.

Section more_misc.
  Context `{ArchimedeanField (F:=F)}.
  Notation Q := the_rationals.
  Notation "#" := (rationals_to_field Q F).

  Lemma le_closed_alt x `{x ∊ F} y `{y ∊ F} : (∀ `{ε ∊ F₊}, x ≤ y + ε) → x ≤ y.
  Proof. intro P. apply (le_closed _ _). intros ε ?. exact (P _ _). Qed.

  Lemma eq_closed_alt x `{x ∊ F} y `{y ∊ F} : (∀ `{ε ∊ F₊}, y - ε ≤ x ≤ y + ε) → x = y.
  Proof. intro P. apply (eq_closed _ _). intros ε ?. exact (P _ _). Qed.

  Lemma sum_of_squares_pos_iff x `{x ∊ F} y `{y ∊ F}
    : x*x + y*y ∊ F₊ ↔ x ∊ F ₀ ∨ y ∊ F ₀ .
  Proof. split.
  + intros [_ E]. red in E.
    cut (∃ `{q ∊ Q₊}, #(q*q)+#(q*q) < x*x + y*y). intros [q[? Eq]].
      destruct (_ : #q ∊ F₊) as [_ Eqp]. red in Eqp.
      destruct (_ : -#q ∊ F₋) as [_ Eqn]. red in Eqn.
      destruct (cotransitivity Eqp x) as [?|?].
        left. cut (x ∊ F₊). intro. apply _. now split.
      destruct (cotransitivity Eqp y) as [?|?].
        right. cut (y ∊ F₊). intro. apply _. now split.
      destruct (cotransitivity Eqn x) as [?|?].
        destruct (cotransitivity Eqn y) as [?|?].
          contradict Eq. apply (le_iff_not_lt_flip _ _).
          apply (plus_le_compat _ _ _ _).
            cut (- # (q * q) ≤ x * x ≤ # (q * q)). now intros [??].
            cut (- # q ≤ x ≤ # q). intro. now apply (between_mult_le_compat _ _ _ _).
            split; now apply (lt_le _ _).
          cut (- # (q * q) ≤ y * y ≤ # (q * q)). now intros [??].
          cut (- # q ≤ y ≤ # q). intro. now apply (between_mult_le_compat _ _ _ _).
          split; now apply (lt_le _ _).
        right. cut (y ∊ F₋). intro. apply _. now split.
      left. cut (x ∊ F₋). intro. apply _. now split.
    destruct (archimedean_rationals_dense _ _ E) as [p[?[??]]].
    assert (p ∊ Q₊). apply (reflects_pos #). apply _. split; trivial; apply _.
    set (q:= (1 ⊓ (p/2))). assert (q ∊ Q₊). unfold q. apply _.
    exists_sub q. apply (le_lt_trans _ (#p) _); trivial.
    subtransitivity (#(q*q+q*q)). now rewrite (_ $ preserves_plus _ _).
    apply (order_preserving # _ _).
    subtransitivity (q*q*2). apply (eq_le _ _). setring Q.
    apply (mult_inv_le_cancel_r _ _ _).
    subtransitivity q. rewrite <-(_ $ mult_1_r q) at 3.
      apply (order_preserving (q *.) _ _). unfold q. apply (meet_lb_l _ _).
    unfold q. apply (meet_lb_r _ _).
  + intros [?|?].
    * pose proof square_pos x. pose proof square_nonneg y. apply _.
    * pose proof square_nonneg x. pose proof square_pos y. apply _.
  Qed.
End more_misc.

Section lattice.
  Context `{ArchimedeanField (F:=F)}.
  Context `{Join _} `{Meet _} `{!LatticeOrder F}.
  Notation Q := the_rationals.
  Notation "#" := (rationals_to_field Q F).

  Lemma field_mult_join_distr x `{x ∊ F₊} y `{y ∊ F} z `{z ∊ F}
    : x * (y ⊔ z) = x * y ⊔ x * z.
  Proof. apply (antisymmetry le _ _).
  + apply (order_reflecting (x⁻¹ *.) _ _).
    rewrite (_ $ associativity (.*.) _ _ _), (_ $ field_inv_l x), (_ $ mult_1_l _).
    apply (join_lub _ _ _); apply (order_reflecting (x *.) _ _);
    rewrite (_ $ associativity (.*.) x _ _), (_ $ field_inv_r x), (_ $ mult_1_l _);
    lattice_order_tac.
  + apply (join_lub _ _ _); apply (order_preserving (x *.) _ _); lattice_order_tac.
  Qed.

  Ltac nonzero_tac :=
        match goal with
          | E : # ?q < ?x, _ : ?q ∊ Q⁺ |- ?x ∊ F ₀ =>
            apply (_ : Subset F₊ (F ₀)); split; [apply _ | red];
            apply (le_lt_trans _ (#q) _); trivial; apply (_ : #q ∊ F⁺)
          | E : ?x < # ?q, _ : ?q ∊ Q⁻ |- ?x ∊ F ₀ =>
            apply (_ : Subset F₋ (F ₀)); split; [apply _ | red];
            apply (lt_le_trans _ (#q) _); trivial; apply (_ : #q ∊ F⁻)
        end.

  Instance arch_field_lattice : SemiRingLatticeOrder F.
  Proof. apply from_comring_lattice_order. intros x ? y ? z ?.
    assert (x ∊ F ₀ → x ∊ F₊). intro. destruct (decompose_nonzero x); trivial.
      now destruct (neg_not_nonneg x).
    assert (x * (y ⊔ z) ∊ F ₀ → x ∊ F ₀).
      intro. apply (nonzero_product x (join y z)).
    assert (x * y ∊ F ₀ → x ∊ F ₀). intro. apply (nonzero_product x y).
    assert (x * z ∊ F ₀ → x ∊ F ₀). intro. apply (nonzero_product x z).
    apply (antisymmetry le _ _).
  + apply (le_iff_not_lt_flip _ _); intro E.
    destruct (archimedean_rationals_dense _ _ E) as [q[? [??]]].
    cut (x ∊ F ₀). intro. destruct (irreflexivity (<) (x * (y ⊔ z))).
      now rewrite (_ $ field_mult_join_distr _ _ _) at 1.
    destruct (nonneg_or_nonpos q).
    * cut (x * (y ⊔ z) ∊ F ₀); trivial. nonzero_tac.
    * cut (x * y ∊ F ₀); trivial.
      apply (_ : Subset F₋ (F ₀)). split. apply _. red.
      apply (lt_le_trans _ (#q) _); [| apply (_ : #q ∊ F⁻) ].
      apply (le_lt_trans _ (x * y ⊔ x * z) _); trivial. lattice_order_tac.
  + apply (join_lub _ _ _); apply (le_iff_not_lt_flip _ _); intro E;
    destruct (archimedean_rationals_dense _ _ E) as [q[? [??]]].
    * cut (x ∊ F ₀). intro.
        cut (y ⊔ z < y). apply (le_iff_not_lt_flip _ _). lattice_order_tac.
        now apply (strictly_order_reflecting (x *.) _ _).
      destruct (nonneg_or_nonpos q).
      - cut (x * y ∊ F ₀); trivial. nonzero_tac.
      - cut (x * (y ⊔ z) ∊ F ₀); trivial. nonzero_tac.
    * cut (x ∊ F ₀). intro.
        cut (y ⊔ z < z). apply (le_iff_not_lt_flip _ _). lattice_order_tac.
        now apply (strictly_order_reflecting (x *.) _ _).
      destruct (nonneg_or_nonpos q).
      - cut (x * z ∊ F ₀); trivial. nonzero_tac.
      - cut (x * (y ⊔ z) ∊ F ₀); trivial. nonzero_tac.
  Qed.
End lattice.
