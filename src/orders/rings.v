Require Import
  abstract_algebra interfaces.orders theory.sub_strong_setoids theory.common_props theory.rings.
Require Export
  orders.semirings.

Lemma ring_partial_minus `{Ring A (R:=R)} (l:relation A) x `{x ∊ R} y `{y ∊ R} : l x y → ∃ `{z ∊ R}, y = x + z.
Proof. intro. exists_sub (- x + y).
     rewrite (associativity _ _ _). rewrite_on R -> (plus_negate_r x). now rewrite (plus_0_l _).
Qed.

Lemma ring_embedding `{Ring A (R:=R)} (l:relation A) `{!Proper ((R,=)==>(R,=)==>iff) l}
  (plus_spec : ∀ `{z ∊ R} `{x ∊ R} `{y ∊ R}, l x y → l (z + x) (z + y))
  z `{z ∊ R} x `{x ∊ R} y `{y ∊ R} : l (z + x) (z + y) → l x y.
Proof.
  rewrite_on R <- (plus_0_l x) at 2. rewrite_on R <- (plus_0_l y) at 2.
  rewrite_on R <- (plus_negate_l z).
  rewrite_on R <- (associativity (f:=(+)) (-z) z x).
  rewrite_on R <- (associativity (f:=(+)) (-z) z y).
  apply (plus_spec _ _ _ _ _ _).
Qed.

Lemma from_ring_order
 `{Ring A (R:=R)} `{Le A} `{!PartialOrder R}
  (plus_spec : ∀ `{z ∊ R}, OrderPreserving (z +) R R)
  (mult_spec : Closed (R⁺ ==> R⁺ ==> R⁺) (.*.))
  : SemiRingOrder R.
Proof. intros. repeat (split; try apply _). apply ring_partial_minus.
  exact (ring_embedding (≤) (λ z (_:z ∊ R), order_preserving (z+)) z).
Qed.

Lemma from_strict_ring_order
 `{Ring A (R:=R)} `{Lt A} `{!SubStrictOrder R}
  (plus_spec : ∀ `{z ∊ R}, StrictlyOrderPreserving (z +) R R)
  (mult_spec : Closed (R₊ ==> R₊ ==> R₊) (.*.))
  : StrictSemiRingOrder R.
Proof. intros. repeat (split; try apply _). apply ring_partial_minus.
  exact (ring_embedding (<) (λ z (_:z ∊ R), strictly_order_preserving (z+)) z).
Qed.

Lemma from_pseudo_ring_order
 `{Ring A (R:=R)} `{UnEq A} `{Lt A} `{!PseudoOrder R}
  (plus_spec : ∀ `{z ∊ R}, StrictlyOrderPreserving (z +) R R)
  (mult_ext : SubStrongSetoid_Binary_Morphism (.*.) R R R)
  (mult_spec : Closed (R₊ ==> R₊ ==> R₊) (.*.))
  : PseudoSemiRingOrder R.
Proof. intros. repeat (split; try apply _). apply ring_partial_minus.
  exact (ring_embedding (<) (λ z (_:z ∊ R), strictly_order_preserving (z+)) z).
Qed.

Lemma from_full_pseudo_ring_order
 `{Ring A (R:=R)} `{UnEq A} `{Le A} `{Lt A} `{!FullPseudoOrder R}
  (plus_spec : ∀ `{z ∊ R}, StrictlyOrderPreserving (z +) R R)
  (mult_ext : SubStrongSetoid_Binary_Morphism (.*.) R R R)
  (mult_spec : Closed (R₊ ==> R₊ ==> R₊) (.*.))
  : FullPseudoSemiRingOrder R.
Proof. split. now apply from_pseudo_ring_order. now apply le_iff_not_lt_flip. Qed.

Section ring_lemmas.

  Context `{Ring (R:=R)}.

  Lemma plus_negate_l_split x `{x ∊ R} y `{y ∊ R} : -x + y + x = y.
  Proof.
    rewrite_on R -> (commutativity (f:=(+)) (-x) y).
    rewrite <- (associativity _ _ _).
    rewrite_on R -> (plus_negate_l x).
    exact (plus_0_r _).
  Qed.

  Lemma plus_negate_r_split x `{x ∊ R} y `{y ∊ R} : x + y - x = y.
  Proof. rewrite_on R <- (negate_involutive x) at 1. exact (plus_negate_l_split _ _). Qed.

  Lemma plus_negate_l_split_alt x `{x ∊ R} y `{y ∊ R} : -x + (y + x) = y.
  Proof. rewrite -> (associativity _ _ _). exact (plus_negate_l_split _ _). Qed.

  Lemma plus_negate_r_split_alt x `{x ∊ R} y `{y ∊ R} : x + (y - x) = y.
  Proof. rewrite -> (associativity _ _ _). exact (plus_negate_r_split _ _). Qed.

  Lemma plus_plus_negate_l x `{x ∊ R} y `{y ∊ R} : x - y + y = x.
  Proof. rewrite_on R -> (commutativity (f:=(+)) x (-y)). exact (plus_negate_l_split _ _). Qed.

End ring_lemmas.

Section ring_order.
  Context `{Ring A (R:=R)} `{Le A} `{!SemiRingOrder R}.

  Lemma flip_le_negate x `{x ∊ R} y `{y ∊ R} : -y ≤ -x ↔ x ≤ y.
  Proof. cut (∀ `{a ∊ R} `{b ∊ R}, a ≤ b → -b ≤ -a). intro P.
  + split; intros; auto. 
    rewrite_on R <-(negate_involutive x). rewrite_on R <-(negate_involutive y).
    now apply (P _ _ _ _).
  + intros a ? b ? E.
    rewrite_on R <- (plus_plus_negate_l (-a) b).
    rewrite_on R <- (plus_negate_l_split a (-b)) at 1.
    now apply (order_preserving _).
  Qed.

  Lemma nonneg_negate x `{x ∊ R⁺} : -x ∊ R⁻.
  Proof. destruct (_:x ∊ R⁺). split. apply _. rewrite_on R <- negate_0. now apply (flip_le_negate _ _). Qed.

  Lemma nonpos_negate x `{x ∊ R⁻} : -x ∊ R⁺.
  Proof. destruct (_:x ∊ R⁻). split. apply _. rewrite_on R <- negate_0. now apply (flip_le_negate _ _). Qed.

  Lemma negate_nonpos_nonneg x `{x ∊ R} : -x ∊ R⁻ → x ∊ R⁺.
  Proof. intros [_?]. split. apply _. apply (flip_le_negate _ _). now rewrite_on R -> negate_0. Qed.

  Lemma negate_nonneg_nonpos x `{x ∊ R} : -x ∊ R⁺ → x ∊ R⁻.
  Proof. intros [_?]. split. apply _. apply (flip_le_negate _ _). now rewrite_on R -> negate_0. Qed.

  Lemma flip_le_minus_r x `{x ∊ R} y `{y ∊ R} z `{z ∊ R} : z ≤ y - x ↔ z + x ≤ y.
  Proof. split; intro.
  + rewrite_on R -> (commutativity (f:=(+)) z x).
    rewrite_on R <- (plus_negate_r_split_alt x y).
    now apply (order_preserving _ _ _).
  + rewrite_on R -> (commutativity (f:=(+)) y (-x)).
    rewrite_on R <- (plus_negate_l_split_alt x z).
    now apply (order_preserving _ _ _).
  Qed.

  Lemma flip_le_minus_l x `{x ∊ R} y `{y ∊ R} z `{z ∊ R} : y - x ≤ z ↔ y ≤ z + x.
  Proof.
    rewrite_on R <-(negate_involutive x) at 2.
    split; apply (flip_le_minus_r _ _ _).
  Qed.

  Lemma flip_nonneg_minus x `{x ∊ R} y `{y ∊ R} : y - x ∊ R⁺ ↔ x ≤ y.
  Proof. rewrite_on R <- (plus_0_l x) at 2. rewrite <- (flip_le_minus_r _ _ _).
    pose proof (_ : y - x ∊ R). firstorder.
  Qed.

  Lemma flip_nonpos_minus x `{x ∊ R} y `{y ∊ R} : y - x ∊ R⁻ ↔ y ≤ x.
  Proof. rewrite_on R <- (plus_0_l x) at 2. rewrite <- (flip_le_minus_l _ _ _).
    pose proof (_ : y - x ∊ R). firstorder.
  Qed.

  Existing Instance NonNeg_subset.

  Lemma nonneg_minus_compat x `{x ∊ R} y `{y ∊ R} z `{z ∊ R⁺} : x ≤ y → x - z ≤ y.
  Proof. intros.
    rewrite_on R -> (commutativity (f:=(+)) x (-z)).
    rewrite_on R <- (plus_negate_l_split_alt z y).
    apply (order_preserving (-z +) _ _).
    subtransitivity y.
    exact (nonneg_plus_le_compat_r _ _).
  Qed.

  Lemma nonneg_minus_compat_back x `{x ∊ R} y `{y ∊ R} z `{z ∊ R⁺} : x ≤ y - z → x ≤ y.
  Proof. intros. subtransitivity (y-z). apply (nonneg_minus_compat _ _ _). subreflexivity. Qed.

  Lemma between_nonneg x `{x ∊ R⁺} : -x ≤ x.
  Proof. pose proof (nonneg_negate x). subtransitivity 0; firstorder. Qed.

End ring_order.

Section strict_ring_order.
  Context `{Ring A (R:=R)} `{Lt A} `{!StrictSemiRingOrder R}.

  Lemma flip_lt_negate x `{x ∊ R} y `{y ∊ R} : -y < -x ↔ x < y.
  Proof. cut (∀ `{a ∊ R} `{b ∊ R}, a < b → -b < -a). intro P.
  + split; intros; auto. 
    rewrite_on R <-(negate_involutive x). rewrite_on R <-(negate_involutive y).
    now apply (P _ _ _ _).
  + intros a ? b ? E.
    rewrite_on R <- (plus_plus_negate_l (-a) b).
    rewrite_on R <- (plus_negate_l_split a (-b)) at 1.
    now apply (strictly_order_preserving _).
  Qed.

  Lemma pos_negate x `{x ∊ R₊} : -x ∊ R₋.
  Proof. destruct (_:x ∊ R₊). split. apply _. rewrite_on R <- negate_0. now apply (flip_lt_negate _ _). Qed.

  Lemma neg_negate x `{x ∊ R₋} : -x ∊ R₊.
  Proof. destruct (_:x ∊ R₋). split. apply _. rewrite_on R <- negate_0. now apply (flip_lt_negate _ _). Qed.

  Lemma negate_neg_pos x `{x ∊ R} : -x ∊ R₋ → x ∊ R₊.
  Proof. intros [_?]. split. apply _. apply (flip_lt_negate _ _). now rewrite_on R -> negate_0. Qed.

  Lemma negate_pos_neg x `{x ∊ R} : -x ∊ R₊ → x ∊ R₋.
  Proof. intros [_?]. split. apply _. apply (flip_lt_negate _ _). now rewrite_on R -> negate_0. Qed.


  Lemma flip_lt_minus_r x `{x ∊ R} y `{y ∊ R} z `{z ∊ R} : z < y - x ↔ z + x < y.
  Proof. split; intro.
  + rewrite_on R -> (commutativity (f:=(+)) z x).
    rewrite_on R <- (plus_negate_r_split_alt x y).
    now apply (strictly_order_preserving _ _ _).
  + rewrite_on R -> (commutativity (f:=(+)) y (-x)).
    rewrite_on R <- (plus_negate_l_split_alt x z).
    now apply (strictly_order_preserving _ _ _).
  Qed.

  Lemma flip_lt_minus_l x `{x ∊ R} y `{y ∊ R} z `{z ∊ R} : y - x < z ↔ y < z + x.
  Proof.
    rewrite_on R <-(negate_involutive x) at 2.
    split; apply (flip_lt_minus_r _ _ _).
  Qed.

  Lemma flip_pos_minus x `{x ∊ R} y `{y ∊ R} : y - x ∊ R₊ ↔ x < y.
  Proof. rewrite_on R <- (plus_0_l x) at 2. rewrite <- (flip_lt_minus_r _ _ _).
    pose proof (_ : y - x ∊ R). firstorder.
  Qed.

  Lemma flip_neg_minus x `{x ∊ R} y `{y ∊ R} : y - x ∊ R₋ ↔ y < x.
  Proof. rewrite_on R <- (plus_0_l x) at 2. rewrite <- (flip_lt_minus_l _ _ _).
    pose proof (_ : y - x ∊ R). firstorder.
  Qed.

  Existing Instance Pos_subset.

  Lemma pos_minus_compat x `{x ∊ R} y `{y ∊ R} z `{z ∊ R₊} : x < y → x - z < y.
  Proof. intros.
    rewrite_on R -> (commutativity (f:=(+)) x (-z)).
    rewrite_on R <- (plus_negate_l_split_alt z y).
    apply (strictly_order_preserving (-z +) _ _).
    subtransitivity y.
    exact (pos_plus_lt_compat_r _ _).
  Qed.

  Lemma between_pos x `{x ∊ R₊} : -x < x.
  Proof. pose proof (pos_negate x). subtransitivity 0; firstorder. Qed.

End strict_ring_order.

Section another_ring_order.
  Context `{Ring A (R:=R1)} `{Le A} `{!SemiRingOrder R1} `{Ring B (R:=R2)} `{Le B}.

  Lemma projected_ring_order f `{!Ring_Morphism f R2 R1} `{!Injective f R2 R1} :
    (∀ `{x ∊ R2} `{y ∊ R2}, x ≤ y ↔ f x ≤ f y) → SemiRingOrder R2.
  Proof. intros P. apply (projected_srorder f P). apply ring_partial_minus. Qed.

  Context `{!SemiRingOrder R2} `{!Ring_Morphism f R1 R2}.

  Lemma reflecting_preserves_nonneg : (∀ x `{x ∊ R1} `{f x ∊ R2⁺}, x ∊ R1⁺) → OrderReflecting f R1 R2.
  Proof.
    intro. repeat (split; try apply _). intros x ? y ? F.
    apply (flip_nonneg_minus _ _). cut (f (y - x) ∊ R2⁺). intro. apply _.
    rewrite (preserves_plus _ _). rewrite_on R2 -> (preserves_negate x).
    now apply (flip_nonneg_minus _ _).
  Qed.

  Lemma preserves_ge_negate1 `{!OrderPreserving f R1 R2} x `{x ∊ R1} : -1 ≤ x → -1 ≤ f x.
  Proof. intros. rewrite_on R2 <- preserves_1. rewrite_on R2 <- (preserves_negate 1). now apply (order_preserving f _ _). Qed.

  Lemma preserves_le_negate1 `{!OrderPreserving f R1 R2} x `{x ∊ R1} : x ≤ -1 → f x ≤ -1.
  Proof. intros. rewrite_on R2 <- preserves_1. rewrite_on R2 <- (preserves_negate 1). now apply (order_preserving f _ _). Qed.

End another_ring_order.

Section another_strict_ring_order.
  Context `{Ring A (R:=R1)} `{Lt A} `{!StrictSemiRingOrder R1} `{Ring B (R:=R2)} `{Lt B}.

  Existing Instance Pos_subset.

  Lemma projected_strict_ring_order f `{!Ring_Morphism f R2 R1} :
    (∀ `{x ∊ R2} `{y ∊ R2}, x < y ↔ f x < f y) → StrictSemiRingOrder R2.
  Proof. intros P. apply (projected_strict_srorder f P). apply ring_partial_minus. Qed.
End another_strict_ring_order.

Section another_pseudo_ring_order.
  Context `{Ring A (R:=R1)} `{UnEq A} `{Lt A} `{!PseudoSemiRingOrder R1}
          `{Ring B (R:=R2)} `{UnEq B} `{Lt B}.

  Lemma projected_pseudo_ring_order f `{!Ring_Morphism f R2 R1} `{!StrongInjective f R2 R1} :
    (∀ `{x ∊ R2} `{y ∊ R2}, x < y ↔ f x < f y) → PseudoSemiRingOrder R2.
  Proof.
    intros P. pose proof (projected_pseudo_order f P).
    pose proof (projected_strict_ring_order f P).
    apply from_pseudo_ring_order. apply _.
    pose proof (pseudo_order_setoid : SubStrongSetoid R1).
    pose proof (pseudo_order_setoid : SubStrongSetoid R2).
    pose proof (strong_injective_mor f).
    repeat (split; try apply _).
    intros x₁ ? y₁ ? x₂ ? y₂ ? E.
    apply (strong_injective f _ _) in E. rewrite 2!(preserves_mult _ _) in E.
    destruct (strong_binary_extensionality (.*.) _ _ _ _ E); [left | right]; now apply (strong_extensionality f).
    exact pos_mult_compat.
  Qed.
End another_pseudo_ring_order.

Section another_full_pseudo_ring_order.
  Context `{Ring A (R:=R1)} `{UnEq A} `{Le A} `{Lt A} `{!FullPseudoSemiRingOrder R1}
          `{Ring B (R:=R2)} `{UnEq B} `{Le B} `{Lt B}.

  Lemma projected_full_pseudo_ring_order f `{!Ring_Morphism f R2 R1} `{!StrongInjective f R2 R1} :
      (∀ `{x ∊ R2} `{y ∊ R2}, x ≤ y ↔ f x ≤ f y)
    → (∀ `{x ∊ R2} `{y ∊ R2}, x < y ↔ f x < f y)
    → FullPseudoSemiRingOrder R2.
  Proof. intros P1 P2. pose proof (projected_full_pseudo_order f P1 P2).
    pose proof (projected_pseudo_ring_order f P2).
    split. apply _. apply le_iff_not_lt_flip.
  Qed.
End another_full_pseudo_ring_order.
