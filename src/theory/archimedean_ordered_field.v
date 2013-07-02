Require Import
  abstract_algebra interfaces.orders interfaces.integers interfaces.rationals 
  interfaces.archimedean_ordered_field
  theory.setoids theory.fields theory.rationals orders.fields orders.rationals
  stdlib_field misc.quote
  the_integers the_rationals nonneg_integers_naturals theory.naturals
  orders.minmax orders.lattices orders.abs.


Section archimedean_property.
  Context `{ArchimedeanOrderedField (F:=F)}.
  Context `{Rationals (Q:=Q)}.
  Notation "#" := (rationals_to_field Q F).
  Notation Z := the_integers.
  Notation "%" := (integers_to_ring Z F).

  Add Ring F : (stdlib_ring_theory F).

  Lemma archimedean x `{x ∊ F₊} y `{y ∊ F₊} : ∃ `{n ∊ Z₊}, x < %n * y .
  Proof. destruct (archimedean_def (N:=Z⁺) x y) as [n[? E]].
    pose proof Zpos_semiring_mor_nonneg %.
    assert (naturals_to_semiring Z⁺ F⁺ n ∊ F). apply (_ : F⁺ ⊆ F). apply _.
    rewrite <-( F $ to_semiring_unique (%:Z⁺ ⇀ F⁺) n ) in E.
    destruct (pos_or_nonpos n). now exists_sub n.
    rewrite (Z $ nonneg_nonpos_0 n), (_ $ preserves_0), (_ $ mult_0_l _) in E.
    exists_sub (1:Z). rewrite (_ $ preserves_1), (_ $ mult_1_l _).
    subtransitivity (0:F). now destruct (_ : y ∊ F₊).
  Qed.

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

  Context (rationals_dense : ∀ `{x ∊ F} `{y ∊ F}, x < y → ∃ `{q ∊ Q}, x < # q < y) .

  Lemma rationals_dense_archimedean_aux x `{x ∊ F₊} y `{y ∊ F₊} : ∃ `{n ∊ Z₊}, x < % n * y.
  Proof.
    destruct (rationals_dense _ _ _ _ (pos_plus_lt_compat_r (x/y) 1)) as [q[?[E _]]].
    destruct (rationals_int_strict_bound (integers_to_ring Z Q) q) as [n[? E2]].
    apply (strictly_order_preserving # _ _) in E2.
    let f := constr:(# ∘ integers_to_ring Z Q) in
      change (# q < f n) in E2; rewrite (_ $ integers.to_ring_unique f _) in E2.
    assert (n ∊ Z₊). apply (reflects_pos %). apply _. split. apply _.
      subtransitivity (# q). subtransitivity (x/y). now destruct (_ : x/y ∊ F₊).
    exists_sub n. rewrite (mult_inv_lt_cancel_l _ _ _). subtransitivity (# q).
  Qed.

  Lemma rationals_dense_archimedean `{Naturals (N:=N)} x `{x ∊ F₊} y `{y ∊ F₊}
      : ∃ `{n ∊ N}, x < (naturals_to_semiring N F⁺ n) * y .
  Proof. destruct (rationals_dense_archimedean_aux x y) as [n[? E]].
    exists_sub (naturals_to_semiring Z⁺ N n).
    pose proof Zpos_semiring_mor_nonneg %.
    assert ((naturals_to_semiring N F⁺ ∘ naturals_to_semiring Z⁺ N) n ∊ F).
      apply (_ : F⁺ ⊆ F). apply _.
    now setoid_rewrite <-(F $ to_semiring_unique_alt (%:Z⁺ ⇀ F⁺) 
        (naturals_to_semiring N F⁺ ∘ naturals_to_semiring Z⁺ N) n ).
  Qed.

End archimedean_property_converse.

Section rationals_archimedean_field.
  Context `{Rationals (Q:=Q)} `{Le _} `{Lt _} `{!FullPseudoSemiRingOrder Q}.

  Lemma rationals_archimedean_field : ArchimedeanOrderedField Q.
  Proof. split; try apply _.
  + apply rationals_dense_archimedean. intros x ? y ? E.
    exists_sub ((x+y)/2). rewrite <-(_ $ to_rationals_unique id _). unfold id.
    rewrite <-(mult_inv_lt_cancel_l _ _ _),<-(mult_inv_lt_cancel_r _ _ _).
    rewrite !(_ $ mult_2_plus_r _). split.
    now apply (strictly_order_preserving (x+) _ _).
    now apply (strictly_order_preserving (+y) _ _).
  Qed.
End rationals_archimedean_field.

Hint Extern 2 (ArchimedeanOrderedField the_rationals) => eapply @rationals_archimedean_field : typeclass_instances.
Hint Extern 15 (ArchimedeanOrderedField ?Q) =>
  let H := constr:(_ : Rationals Q) in eapply (rationals_archimedean_field (H:=H)) : typeclass_instances.

Section maps.
  Context `{ArchimedeanOrderedField (F:=F1)}.
  Context `{ArchimedeanOrderedField (F:=F2)}.
  Context (f:F1 ⇀ F2) `{!Ring_Morphism F1 F2 f}.

  Notation Q := the_rationals.

  Notation "%" := (rationals_to_field Q F1).
  Notation "#" := (rationals_to_field Q F2).

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

End maps.

Section misc.
  Context `{Rationals (Q:=Q)} `{Le _} `{Lt _} `{!FullPseudoSemiRingOrder Q}.
  Context `{ArchimedeanOrderedField (F:=F)}.
  Notation "#" := (rationals_to_field Q F).

  Add Field Q : (stdlib_field_theory Q).

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

