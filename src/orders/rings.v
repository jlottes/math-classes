Require Import
  abstract_algebra interfaces.orders theory.strong_setoids theory.common_props theory.rings.
Require Export
  orders.semirings.

Lemma ring_partial_minus `{Ring (R:=R)} (l:relation _) x `{x ∊ R} y `{y ∊ R} : l x y → ∃ `{z ∊ R}, y = x + z.
Proof. intro. exists_sub (- x + y).
  now rewrite_on R -> (associativity (+) x (-x) y), (plus_negate_r x), (plus_0_l y).
Qed.

Lemma ring_embedding `{Ring (R:=R)} (l:relation _) `{!Proper ((R,=)==>(R,=)==>iff) l}
  (plus_spec : ∀ `{z ∊ R} `{x ∊ R} `{y ∊ R}, l x y → l (z + x) (z + y))
  z `{z ∊ R} x `{x ∊ R} y `{y ∊ R} : l (z + x) (z + y) → l x y.
Proof.
  rewrite_on R <- (plus_0_l x) at 2. rewrite_on R <- (plus_0_l y) at 2.
  rewrite_on R <- (plus_negate_l z).
  rewrite <- 2!(R $ associativity (+) (-z) _ _).
  apply (plus_spec _ _ _ _ _ _).
Qed.

Lemma from_ring_order
 `{Ring (R:=R)} `{Le _} `{!PartialOrder R}
  (plus_spec : ∀ `{z ∊ R}, OrderPreserving R R (z +))
  (mult_spec : Closed (R⁺ ⇀ R⁺ ⇀ R⁺) (.*.))
  : SemiRingOrder R.
Proof. intros. repeat (split; try apply _). apply ring_partial_minus.
  exact (ring_embedding (≤) (λ z (_:z ∊ R), order_preserving (z+)) z).
Qed.

Lemma from_strict_ring_order
 `{Ring (R:=R)} `{Lt _} `{!StrictSetoidOrder R}
  (plus_spec : ∀ `{z ∊ R}, StrictlyOrderPreserving R R (z +))
  (mult_spec : Closed (R₊ ⇀ R₊ ⇀ R₊) (.*.))
  : StrictSemiRingOrder R.
Proof. intros. repeat (split; try apply _). apply ring_partial_minus.
  exact (ring_embedding (<) (λ z (_:z ∊ R), strictly_order_preserving (z+)) z).
Qed.

Lemma from_pseudo_ring_order
 `{Ring (R:=R)} `{UnEq _} `{Lt _} `{!PseudoOrder R}
  (plus_spec : ∀ `{z ∊ R}, StrictlyOrderPreserving R R (z +))
  (mult_ext : Strong_Binary_Morphism R R R (.*.))
  (mult_spec : Closed (R₊ ⇀ R₊ ⇀ R₊) (.*.))
  : PseudoSemiRingOrder R.
Proof. intros. repeat (split; try apply _). apply ring_partial_minus.
  exact (ring_embedding (<) (λ z (_:z ∊ R), strictly_order_preserving (z+)) z).
Qed.

Lemma from_full_pseudo_ring_order
 `{Ring (R:=R)} `{UnEq _} `{Le _} `{Lt _} `{!FullPseudoOrder R}
  (plus_spec : ∀ `{z ∊ R}, StrictlyOrderPreserving R R (z +))
  (mult_ext : Strong_Binary_Morphism R R R (.*.))
  (mult_spec : Closed (R₊ ⇀ R₊ ⇀ R₊) (.*.))
  : FullPseudoSemiRingOrder R.
Proof. split. now apply from_pseudo_ring_order. now apply le_iff_not_lt_flip. Qed.

Section ring_order.
  Context `{Ring (R:=R)} `{Le _} `{!SemiRingOrder R}.

  Lemma flip_le_negate x `{x ∊ R} y `{y ∊ R} : -y ≤ -x ↔ x ≤ y.
  Proof. cut (∀ `{a ∊ R} `{b ∊ R}, a ≤ b → -b ≤ -a). intro P.
  + split; intros; auto. 
    rewrite_on R <-(negate_involutive x), <-(negate_involutive y).
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
End ring_order.

Hint Extern 4 (-_ ∊ _⁻) => eapply @nonneg_negate : typeclass_instances.
Hint Extern 4 (-_ ∊ _⁺) => eapply @nonpos_negate : typeclass_instances.

Section more_ring_order.
  Context `{Ring (R:=R)} `{Le _} `{!SemiRingOrder R}.

  Lemma negate_nonpos_nonneg x `{x ∊ R} : -x ∊ R⁻ → x ∊ R⁺.
  Proof. intro. rewrite_on R <- (negate_involutive x). apply _. Qed.

  Lemma negate_nonneg_nonpos x `{x ∊ R} : -x ∊ R⁺ → x ∊ R⁻.
  Proof. intro. rewrite_on R <- (negate_involutive x). apply _. Qed.

  Lemma nonneg_nonpos_zero x `{x ∊ R⁺} `{x ∊ R⁻} : x = 0.
  Proof. apply (subantisymmetry (≤) _ _); firstorder. Qed.

  Lemma flip_le_minus_r x `{x ∊ R} y `{y ∊ R} z `{z ∊ R} : z ≤ y - x ↔ z + x ≤ y.
  Proof. split; intro.
  + rewrite_on R -> (commutativity (+) z x), <- (plus_negate_r_split_alt x y).
    now apply (order_preserving _ _ _).
  + rewrite_on R -> (commutativity (+) y (-x)), <- (plus_negate_l_split_alt x z).
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

  Definition minus_nonneg x `{x ∊ R} y `{y ∊ R} := proj2 (flip_nonneg_minus x y).

  Lemma flip_nonpos_minus x `{x ∊ R} y `{y ∊ R} : y - x ∊ R⁻ ↔ y ≤ x.
  Proof. rewrite_on R <- (plus_0_l x) at 2. rewrite <- (flip_le_minus_l _ _ _).
    pose proof (_ : y - x ∊ R). firstorder.
  Qed.

  Definition minus_nonpos x `{x ∊ R} y `{y ∊ R} := proj2 (flip_nonpos_minus x y).

  Lemma nonneg_minus_compat x `{x ∊ R} y `{y ∊ R} z `{z ∊ R⁺} : x ≤ y → x - z ≤ y.
  Proof. intros.
    rewrite_on R -> (commutativity (+) x (-z)), <- (plus_negate_l_split_alt z y).
    apply (order_preserving (-z +) _ _).
    subtransitivity y.
    exact (nonneg_plus_le_compat_r _ _).
  Qed.

  Lemma nonneg_minus_compat_back x `{x ∊ R} y `{y ∊ R} z `{z ∊ R⁺} : x ≤ y - z → x ≤ y.
  Proof. intros. subtransitivity (y-z). now apply (nonneg_minus_compat _ _ _). Qed.

  Lemma between_nonneg x `{x ∊ R⁺} : -x ≤ x.
  Proof. pose proof (nonneg_negate x). subtransitivity 0; firstorder. Qed.

End more_ring_order.

Section strict_ring_order.
  Context `{Ring (R:=R)} `{Lt _} `{!StrictSemiRingOrder R}.

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
End strict_ring_order.

Hint Extern 4 (-_ ∊ _₋) => eapply @pos_negate : typeclass_instances.
Hint Extern 4 (-_ ∊ _₊) => eapply @neg_negate : typeclass_instances.

Section more_strict_ring_order.
  Context `{Ring (R:=R)} `{Lt _} `{!StrictSemiRingOrder R}.

  Lemma negate_neg_pos x `{x ∊ R} : -x ∊ R₋ → x ∊ R₊.
  Proof. intro. rewrite_on R <- (negate_involutive x). apply _. Qed.

  Lemma negate_pos_neg x `{x ∊ R} : -x ∊ R₊ → x ∊ R₋.
  Proof. intro. rewrite_on R <- (negate_involutive x). apply _. Qed.

  Lemma flip_lt_minus_r x `{x ∊ R} y `{y ∊ R} z `{z ∊ R} : z < y - x ↔ z + x < y.
  Proof. split; intro.
  + rewrite_on R -> (commutativity (+) z x), <- (plus_negate_r_split_alt x y).
    now apply (strictly_order_preserving _ _ _).
  + rewrite_on R -> (commutativity (+) y (-x)), <- (plus_negate_l_split_alt x z).
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

  Lemma pos_minus_compat x `{x ∊ R} y `{y ∊ R} z `{z ∊ R₊} : x < y → x - z < y.
  Proof. intros.
    rewrite_on R -> (commutativity (+) x (-z)), <- (plus_negate_l_split_alt z y).
    apply (strictly_order_preserving (-z +) _ _).
    subtransitivity y.
    exact (pos_plus_lt_compat_r _ _).
  Qed.

  Lemma between_pos x `{x ∊ R₊} : -x < x.
  Proof. pose proof (pos_negate x). subtransitivity 0; firstorder. Qed.

End more_strict_ring_order.

Section another_ring_order.
  Context `{Ring A (R:=R1)} `{Le A} `{!SemiRingOrder R1} `{Ring B (R:=R2)} `{Le B}.

  Lemma projected_ring_order (f:R2 ⇀ R1) `{!Ring_Morphism R2 R1 f} `{!Injective R2 R1 f} :
    (∀ `{x ∊ R2} `{y ∊ R2}, x ≤ y ↔ f x ≤ f y) → SemiRingOrder R2.
  Proof. intros P. apply (projected_srorder f P). apply ring_partial_minus. Qed.

  Context `{!SemiRingOrder R2} {f:R1 ⇀ R2} `{!Ring_Morphism R1 R2 f}.

  Lemma reflecting_preserves_nonneg : (∀ `{x ∊ R1} `{f x ∊ R2⁺}, x ∊ R1⁺) → OrderReflecting R1 R2 f.
  Proof.
    intro. repeat (split; try apply _). intros x ? y ? F.
    apply (flip_nonneg_minus _ _). cut (f (y - x) ∊ R2⁺). intro. apply _.
    rewrite_on R2 -> (preserves_plus y (-x)), (preserves_negate x).
    now apply (flip_nonneg_minus _ _).
  Qed.

  Lemma preserves_ge_negate1 `{!OrderPreserving R1 R2 f} x `{x ∊ R1} : -1 ≤ x → -1 ≤ f x.
  Proof. intros. rewrite_on R2 <- preserves_1, <- (preserves_negate 1). now apply (order_preserving f _ _). Qed.

  Lemma preserves_le_negate1 `{!OrderPreserving R1 R2 f} x `{x ∊ R1} : x ≤ -1 → f x ≤ -1.
  Proof. intros. rewrite_on R2 <- preserves_1, <- (preserves_negate 1). now apply (order_preserving f _ _). Qed.

End another_ring_order.

Section another_strict_ring_order.
  Context `{Ring A (R:=R1)} `{Lt A} `{!StrictSemiRingOrder R1} `{Ring B (R:=R2)} `{Lt B}.

  Lemma projected_strict_ring_order (f:R2 ⇀ R1) `{!Ring_Morphism R2 R1 f} :
    (∀ `{x ∊ R2} `{y ∊ R2}, x < y ↔ f x < f y) → StrictSemiRingOrder R2.
  Proof. intros P. apply (projected_strict_srorder f P). apply ring_partial_minus. Qed.
End another_strict_ring_order.

Section another_pseudo_ring_order.
  Context `{Ring A (R:=R1)} `{UnEq A} `{Lt A} `{!PseudoSemiRingOrder R1}
          `{Ring B (R:=R2)} `{UnEq B} `{Lt B} `{!StrongSetoid R2}.

  Existing Instance pseudo_order_setoid.

  Lemma projected_pseudo_ring_order (f:R2 ⇀ R1) `{!Ring_Morphism R2 R1 f} `{!StrongInjective R2 R1 f} :
    (∀ `{x ∊ R2} `{y ∊ R2}, x < y ↔ f x < f y) → PseudoSemiRingOrder R2.
  Proof.
    intros P.
    pose proof (projected_pseudo_order f P).
    pose proof (projected_strict_ring_order f P).
    apply from_pseudo_ring_order. apply _.
    pose proof (strong_injective_mor f).
    repeat (split; try apply _). rewrite strong_ext_equiv_2.
    intros x₁ ? y₁ ? x₂ ? y₂ ? E.
    apply (strong_injective f _ _) in E.
    rewrite 2!(R1 $ preserves_mult _ _) in E.
    destruct (strong_binary_extensionality (.*.) E); [left | right]; now apply (strong_extensionality f).
    exact pos_mult_compat.
  Qed.
End another_pseudo_ring_order.

Section another_full_pseudo_ring_order.
  Context `{Ring A (R:=R1)} `{UnEq A} `{Le A} `{Lt A} `{!FullPseudoSemiRingOrder R1}
          `{Ring B (R:=R2)} `{UnEq B} `{Le B} `{Lt B} `{!StrongSetoid R2}.

  Lemma projected_full_pseudo_ring_order (f:R2 ⇀ R1) `{!Ring_Morphism R2 R1 f} `{!StrongInjective R2 R1 f} :
      (∀ `{x ∊ R2} `{y ∊ R2}, x ≤ y ↔ f x ≤ f y)
    → (∀ `{x ∊ R2} `{y ∊ R2}, x < y ↔ f x < f y)
    → FullPseudoSemiRingOrder R2.
  Proof. intros P1 P2. pose proof (projected_full_pseudo_order f P1 P2).
    pose proof (projected_pseudo_ring_order f P2).
    split. apply _. apply le_iff_not_lt_flip.
  Qed.
End another_full_pseudo_ring_order.
