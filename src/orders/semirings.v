Require Import
  abstract_algebra interfaces.orders theory.subsetoids theory.sub_strong_setoids
  theory.common_props theory.rings theory.strong_rings.
Require Export
  orders.orders orders.maps.

Local Existing Instance srorder_semiring.
Local Existing Instance strict_srorder_semiring.
Local Existing Instance pseudo_srorder_semiring.

Local Ltac subsetoid_tac R :=
  split; try apply _; intros ? y E [??]; assert (y ∊ R) by (rewrite <- E; apply _);
  split; [| rewrite_on R <-E ]; apply _.

Lemma NonNeg_subsetoid    `{SemiRingOrder (R:=R)} : SubSetoid R⁺. Proof. subsetoid_tac R. Qed.
Lemma NonPos_subsetoid    `{SemiRingOrder (R:=R)} : SubSetoid R⁻. Proof. subsetoid_tac R. Qed.
Lemma Pos_subsetoid `{StrictSemiRingOrder (R:=R)} : SubSetoid R₊. Proof. subsetoid_tac R. Qed.
Lemma Neg_subsetoid `{StrictSemiRingOrder (R:=R)} : SubSetoid R₋. Proof. subsetoid_tac R. Qed.

Hint Extern 0 (SubSetoid _⁺) => eapply @NonNeg_subsetoid : typeclass_instances. 
Hint Extern 0 (SubSetoid _⁻) => eapply @NonPos_subsetoid : typeclass_instances. 
Hint Extern 0 (SubSetoid _₊) => eapply @Pos_subsetoid    : typeclass_instances. 
Hint Extern 0 (SubSetoid _₋) => eapply @Neg_subsetoid    : typeclass_instances. 


Section semiring_order.
  Context `{SemiRingOrder (R:=R)}.

  Existing Instance NonNeg_subset.

  Global Instance: ∀ `{z ∊ R}, OrderEmbedding (+z) R R.
  Proof.
    intros. split.
     apply order_preserving_flip.
    apply order_reflecting_flip.
  Qed.

  Global Instance: ∀ `{z ∊ R}, LeftCancellation (+) z R.
  Proof.
    intros z ? x ? y ? E.
    apply (subantisymmetry (≤)); trivial;
    apply (order_reflecting (z+)); trivial;
    apply eq_le; now try apply _.
  Qed.

  Global Instance: ∀ `{z ∊ R}, RightCancellation (+) z R.
  Proof. intros. apply right_cancel_from_left. Qed.

  Lemma nonneg_plus_le_compat_r x `{x ∊ R} z `{z ∊ R⁺} : x ≤ x + z.
  Proof. rewrite_on R <-(plus_0_r x) at 1. apply (order_preserving (x+) 0 z); firstorder. Qed.

  Lemma plus_le_compat_nonneg_r x `{x ∊ R} z `{z ∊ R} : x ≤ x + z → z ∊ R⁺.
  Proof. rewrite_on R <-(plus_0_r x) at 1. split. apply _. now apply (order_reflecting (x+) 0 z). Qed.

  Lemma nonneg_plus_le_compat_l x `{x ∊ R} z `{z ∊ R⁺} : x ≤ z + x.
  Proof. rewrite_on R -> (commutativity (f:=(+)) z x). exact (nonneg_plus_le_compat_r x z). Qed.

  Lemma plus_le_compat_nonneg_l x `{x ∊ R} z `{z ∊ R} : x ≤ z + x → z ∊ R⁺.
  Proof. rewrite_on R -> (commutativity (f:=(+)) z x). exact (plus_le_compat_nonneg_r x z). Qed.

  Lemma plus_le_compat x₁ `{x₁ ∊ R} y₁ `{y₁ ∊ R} x₂ `{x₂ ∊ R} y₂ `{y₂ ∊ R}
    : x₁ ≤ y₁ → x₂ ≤ y₂ → x₁ + x₂ ≤ y₁ + y₂.
  Proof.
    intros E1 E2.
    subtransitivity (y₁ + x₂).
     now apply (order_preserving (+ x₂)).
    now apply (order_preserving (y₁ +)).
  Qed.

  Lemma plus_le_compat_r x `{x ∊ R} y `{y ∊ R} z `{z ∊ R⁺} : x ≤ y → x ≤ y + z.
  Proof. intros. rewrite_on R <-(plus_0_r x). apply plus_le_compat; firstorder. Qed.

  Lemma plus_le_compat_l x `{x ∊ R} y `{y ∊ R} z `{z ∊ R⁺} : x ≤ y → x ≤ z + y.
  Proof. rewrite_on R -> (commutativity (f:=(+)) z y). exact (plus_le_compat_r x y z). Qed.

  Lemma nonpos_plus_compat : Closed (R⁻ ==> R⁻ ==> R⁻) (+).
  Proof. intros x [??] y [??]. split. apply _. rewrite_on R <-(plus_0_r 0).
    apply (plus_le_compat x 0 y 0); solve_propholds.
  Qed.

  Lemma nonneg_plus_compat : Closed (R⁺ ==> R⁺ ==> R⁺) (+).
  Proof. intros ?? ??. split. apply _. apply plus_le_compat_l; try apply _; firstorder. Qed.

  Lemma decompose_le `{x ∊ R} `{y ∊ R} : x ≤ y → ∃ `{z ∊ R⁺}, y = x + z.
  Proof.
    intros E.
    destruct (srorder_partial_minus x y E) as [z [? Ez]].
    exists z. assert (PropHolds (0 ≤ z)).
    apply (order_reflecting (x+) 0 z).
    rewrite_on R -> (plus_0_r x). now rewrite_on R <-Ez.
    now exists (NonNeg_element R : z ∊ R⁺ ).
  Qed.

  Lemma compose_le x `{x ∊ R} y `{y ∊ R} z `{z ∊ R⁺} : y = x + z → x ≤ y.
  Proof. intros E2. rewrite_on R -> E2. exact (nonneg_plus_le_compat_r x z). Qed.

  Global Instance: ∀ `{z ∊ R⁺}, OrderPreserving (z *.) R R.
  Proof.
    intros z ?.
    repeat (split; try apply _).
    intros x ? y ? F.
    destruct (decompose_le F) as [a [? Ea]].
    rewrite_on R -> Ea. rewrite_on R -> (distribute_l z x a).
    exact (nonneg_plus_le_compat_r (z*x) (z*a)).
  Qed.

  Global Instance: ∀ `{z ∊ R⁺}, OrderPreserving (.* z) R R.
  Proof.
    intros z ?.
    repeat (split; try apply _).
    intros x ? y ? F.
    destruct (decompose_le F) as [a [? Ea]].
    rewrite_on R -> Ea. rewrite_on R -> (distribute_r x a z).
    exact (nonneg_plus_le_compat_r (x*z) (a*z)).
  Qed.

  Lemma mult_le_compat x₁ `{x₁ ∊ R⁺} y₁ `{y₁ ∊ R} x₂ `{x₂ ∊ R⁺} y₂ `{y₂ ∊ R} :
    x₁ ≤ y₁ → x₂ ≤ y₂ → x₁ * x₂ ≤ y₁ * y₂.
  Proof.
    intros E1 E2.
    assert (y₁ ∊ R⁺) by (split; [|subtransitivity x₁]; firstorder).
    subtransitivity (y₁ * x₂).
    exact (order_preserving (.* x₂) _ _ E1).
    exact (order_preserving (y₁ *.) _ _ E2).
  Qed.

  Lemma ge_1_mult_le_compat_r x `{x ∊ R} y `{y ∊ R⁺} z `{z ∊ R} : 1 ≤ z → x ≤ y → x ≤ y * z.
  Proof.
    intros. subtransitivity y.
    rewrite_on R <-(mult_1_r y) at 1.
    now apply (order_preserving (y *.) 1 z).
  Qed.

  Lemma ge_1_mult_le_compat_l x `{x ∊ R} y `{y ∊ R⁺} z `{z ∊ R} : 1 ≤ z → x ≤ y → x ≤ z * y.
  Proof.
    intros. subtransitivity y.
    rewrite_on R <-(mult_1_l y) at 1.
    now apply (order_preserving (.* y) 1 z).
  Qed.

  Lemma flip_nonpos_mult_l x `{x ∊ R} y `{y ∊ R} z `{z ∊ R⁻} : x ≤ y → z * y ≤ z * x.
  Proof.
    destruct (_ : z ∊ R⁻) as [? Ez]. intros Exy.
    destruct (decompose_le Ez) as [a [? Ea]], (decompose_le Exy) as [b [? Eb]].
    rewrite_on R -> Eb.
    apply compose_le with (a * b); try apply _.
    rewrite_on R -> (distribute_l z x b).
    rewrite <- (associativity (z*x) (z*b) (a*b)).
    rewrite_on R <- (distribute_r z a b).
    rewrite_on R <- Ea.
    rewrite_on R -> (mult_0_l b).
    now rewrite_on R -> (plus_0_r (z*x)).
  Qed.

  Lemma flip_nonpos_mult_r x `{x ∊ R} y `{y ∊ R} z `{z ∊ R⁻} : x ≤ y → y * z ≤ x * z.
  Proof.
    destruct (_ : z ∊ R⁻) as [? Ez]. intros Exy.
    destruct (decompose_le Ez) as [a [? Ea]], (decompose_le Exy) as [b [? Eb]].
    rewrite_on R -> Eb.
    apply compose_le with (b * a); try apply _.
    rewrite_on R -> (distribute_r x b z).
    rewrite <- (associativity (x*z) (b*z) (b*a)).
    rewrite_on R <- (distribute_l b z a).
    rewrite_on R <- Ea.
    rewrite_on R -> (mult_0_r b).
    now rewrite_on R -> (plus_0_r (x*z)).
  Qed.

  Lemma nonpos_mult : Closed (R⁻ ==> R⁻ ==> R⁺) (.*.).
  Proof.
    intros x ? y [??]. destruct (_ : x ∊ R⁻). split. apply _.
    rewrite_on R <- (mult_0_r x).
    apply (flip_nonpos_mult_l y 0 x). solve_propholds.
  Qed.

  Lemma nonpos_nonneg_mult : Closed (R⁻ ==> R⁺ ==> R⁻) (.*.).
  Proof.
    intros x ? y [??]. destruct (_ : x ∊ R⁻). split. apply _.
    rewrite_on R <- (mult_0_r x).
    apply (flip_nonpos_mult_l 0 y x). solve_propholds.
  Qed.

  Lemma nonneg_nonpos_mult : Closed (R⁺ ==> R⁻ ==> R⁻) (.*.).
  Proof.
    intros x [??] y ?. destruct (_ : y ∊ R⁻). split. apply _.
    rewrite_on R <- (mult_0_l y).
    apply (flip_nonpos_mult_r 0 x y). solve_propholds.
  Qed.
End semiring_order.

Hint Extern 0 (_ + _ ∊ _⁺) => eapply @nonneg_plus_compat : typeclass_instances. 
Arguments nonpos_mult        {A _ _ _ _ _ _ R _} _ {_} _ {_}. 
Arguments nonpos_nonneg_mult {A _ _ _ _ _ _ R _} _ {_} _ {_}. 
Arguments nonneg_nonpos_mult {A _ _ _ _ _ _ R _} _ {_} _ {_}. 

Section strict_semiring_order.
  Context `{StrictSemiRingOrder (R:=R)}.

  Existing Instance Pos_subset.

  Lemma pos_not_neg x `{x ∊ R₊} : ¬ x ∊ R₋ .
  Proof. intros [? E]. apply (lt_flip _ _ E). firstorder. Qed.

  Lemma neg_not_pos x `{x ∊ R₋} : ¬ x ∊ R₊ .
  Proof. intros [? E]. apply (lt_flip _ _ E). firstorder. Qed.

  Global Instance: ∀ `{z ∊ R}, StrictOrderEmbedding (+z) R R.
  Proof.
    intros. split.
     now apply strictly_order_preserving_flip.
    now apply strictly_order_reflecting_flip.
  Qed.

  Lemma pos_plus_lt_compat_r x `{x ∊ R} z `{z ∊ R₊} : x < x + z.
  Proof. rewrite_on R <-(plus_0_r x) at 1. apply (strictly_order_preserving (x+) 0 z); firstorder. Qed.

  Lemma plus_lt_compat_pos_r x `{x ∊ R} z `{z ∊ R} : x < x + z → z ∊ R₊.
  Proof. rewrite_on R <-(plus_0_r x) at 1. split. apply _. now apply (strictly_order_reflecting (x+) 0 z). Qed.

  Lemma pos_plus_lt_compat_l x `{x ∊ R} z `{z ∊ R₊} : x < z + x.
  Proof. rewrite_on R -> (commutativity (f:=(+)) z x). exact (pos_plus_lt_compat_r x z). Qed.

  Lemma plus_lt_compat_pos_l x `{x ∊ R} z `{z ∊ R} : x < z + x → z ∊ R₊.
  Proof. rewrite_on R -> (commutativity (f:=(+)) z x). exact (plus_lt_compat_pos_r x z). Qed.

  Lemma plus_lt_compat x₁ `{x₁ ∊ R} y₁ `{y₁ ∊ R} x₂ `{x₂ ∊ R} y₂ `{y₂ ∊ R}
    : x₁ < y₁ → x₂ < y₂ → x₁ + x₂ < y₁ + y₂.
  Proof.
    intros E1 E2.
    subtransitivity (y₁ + x₂).
     now apply (strictly_order_preserving (+ x₂)).
    now apply (strictly_order_preserving (y₁ +)).
  Qed.

  Lemma plus_lt_compat_r x `{x ∊ R} y `{y ∊ R} z `{z ∊ R₊} : x < y → x < y + z.
  Proof. intros. rewrite_on R <-(plus_0_r x). apply (plus_lt_compat x y 0 z); firstorder. Qed.

  Lemma plus_lt_compat_l x `{x ∊ R} y `{y ∊ R} z `{z ∊ R₊} : x < y → x < z + y.
  Proof. rewrite_on R -> (commutativity (f:=(+)) z y). exact (plus_lt_compat_r x y z). Qed.

  Lemma neg_plus_compat : Closed (R₋ ==> R₋ ==> R₋) (+).
  Proof. intros x [??] y [??]. split. apply _. rewrite_on R <-(plus_0_r 0). now apply (plus_lt_compat x 0 y 0). Qed.

  Instance pos_plus_compat : Closed (R₊ ==> R₊ ==> R₊) (+).
  Proof. intros x ? y ?. split. apply _. apply (plus_lt_compat_l 0 y x); firstorder. Qed.

  Lemma compose_lt x `{x ∊ R} y `{y ∊ R} z `{z ∊ R₊} : y = x + z → x < y.
  Proof.
    intros E2. rewrite_on R -> E2.
    exact (pos_plus_lt_compat_r x z).
  Qed.

  Lemma decompose_lt `{x ∊ R} `{y ∊ R} : x < y → ∃ `{z ∊ R₊}, y = x + z.
  Proof.
    intros E.
    destruct (strict_srorder_partial_minus x y E) as [z [? Ez]].
    exists z. assert (PropHolds (0 < z)).
    apply (strictly_order_reflecting (x+) 0 z).
    rewrite_on R <- Ez. now rewrite_on R -> (plus_0_r x).
    now exists (Pos_element R : z ∊ R₊).
  Qed.

  Global Instance: ∀ `{z ∊ R₊}, StrictlyOrderPreserving (z *.) R R.
  Proof.
    intros z ?. repeat (split; try apply _). intros x ? y ? F.
    destruct (decompose_lt F) as [a [? Ea]].
    rewrite_on R -> Ea. rewrite_on R -> (plus_mult_distr_l z x a).
    exact (pos_plus_lt_compat_r (z*x) (z*a)).
  Qed.

  Global Instance: ∀ `{z ∊ R₊}, StrictlyOrderPreserving (.* z) R R.
  Proof.
    intros z ?. repeat (split; try apply _). intros x ? y ? F.
    destruct (decompose_lt F) as [a [? Ea]].
    rewrite_on R -> Ea. rewrite_on R -> (plus_mult_distr_r x a z).
    exact (pos_plus_lt_compat_r (x*z) (a*z)).
  Qed.

  Lemma mult_lt_compat x₁ `{x₁ ∊ R₊} y₁ `{y₁ ∊ R} x₂ `{x₂ ∊ R₊} y₂ `{y₂ ∊ R} :
    x₁ < y₁ → x₂ < y₂ → x₁ * x₂ < y₁ * y₂.
  Proof.
    intros E1 E2.
    assert (y₁ ∊ R₊) by (split; [| subtransitivity x₁]; firstorder).
    subtransitivity (y₁ * x₂).
    exact (strictly_order_preserving (.* x₂) _ _ E1).
    exact (strictly_order_preserving (y₁ *.) _ _ E2).
  Qed.

  Lemma gt_1_mult_lt_compat_r x `{x ∊ R} y `{y ∊ R₊} z `{z ∊ R} : 1 < z → x < y → x < y * z.
  Proof.
    intros. subtransitivity y.
    rewrite_on R <- (mult_1_r y) at 1.
    now apply (strictly_order_preserving (y *.) 1 z).
  Qed.

  Lemma gt_1_mult_lt_compat_l x `{x ∊ R} y `{y ∊ R₊} z `{z ∊ R} : 1 < z → x < y → x < z * y.
  Proof.
    intros. subtransitivity y.
    rewrite_on R <- (mult_1_l y) at 1.
    now apply (strictly_order_preserving (.* y) 1 z).
  Qed.

  Lemma flip_neg_mult_l x `{x ∊ R} y `{y ∊ R} z `{z ∊ R₋} : x < y → z * y < z * x.
  Proof.
    destruct (_:z ∊ R₋) as [? Ez]. intros Exy.
    destruct (decompose_lt Ez) as [a [? Ea]], (decompose_lt Exy) as [b [? Eb]].
    rewrite_on R -> Eb.
    apply compose_lt with (a * b); try apply _.
    rewrite_on R -> (distribute_l z x b).
    rewrite <- (associativity (z*x) (z*b) (a*b)).
    rewrite_on R <- (distribute_r z a b).
    rewrite_on R <- Ea.
    rewrite_on R -> (mult_0_l b).
    now rewrite_on R -> (plus_0_r (z*x)).
  Qed.

  Lemma flip_neg_mult_r x `{x ∊ R} y `{y ∊ R} z `{z ∊ R₋} : x < y → y * z < x * z.
  Proof.
    destruct (_:z ∊ R₋) as [? Ez]. intros Exy.
    destruct (decompose_lt Ez) as [a [? Ea]], (decompose_lt Exy) as [b [? Eb]].
    rewrite_on R -> Eb.
    apply compose_lt with (b * a); try apply _.
    rewrite_on R -> (distribute_r x b z).
    rewrite <- (associativity (x*z) (b*z) (b*a)).
    rewrite_on R <- (distribute_l b z a).
    rewrite_on R <- Ea.
    rewrite_on R -> (mult_0_r b).
    now rewrite_on R -> (plus_0_r (x*z)).
  Qed.

  Lemma neg_mult : Closed (R₋ ==> R₋ ==> R₊) (.*.).
  Proof.
    intros x ? y [??]. destruct (_ : x ∊ R₋). split. apply _.
    rewrite_on R <- (mult_0_r x).
    apply (flip_neg_mult_l y 0 x). solve_propholds.
  Qed.

  Lemma neg_pos_mult : Closed (R₋ ==> R₊ ==> R₋) (.*.).
  Proof.
    intros x ? y [??]. destruct (_ : x ∊ R₋). split. apply _.
    rewrite_on R <- (mult_0_r x).
    apply (flip_neg_mult_l 0 y x). solve_propholds.
  Qed.

  Lemma pos_neg_mult : Closed (R₊ ==> R₋ ==> R₋) (.*.).
  Proof.
    intros x [??] y ?. destruct (_ : y ∊ R₋). split. apply _.
    rewrite_on R <- (mult_0_l y).
    apply (flip_neg_mult_r 0 x y). solve_propholds.
  Qed.

End strict_semiring_order.

Hint Extern 0 (_ + _ ∊ _₊) => eapply @pos_plus_compat : typeclass_instances. 
Arguments neg_mult     {A _ _ _ _ _ _ R _} _ {_} _ {_}.
Arguments neg_pos_mult {A _ _ _ _ _ _ R _} _ {_} _ {_}.
Arguments pos_neg_mult {A _ _ _ _ _ _ R _} _ {_} _ {_}.

Section pseudo_semiring_order.
  Context `{PseudoSemiRingOrder (R:=R)}.

  Existing Instance pseudo_order_setoid.

  Global Instance: StrictSemiRingOrder R.
  Proof.
    split; try apply _.
     intros. now apply pseudo_srorder_partial_minus, lt_flip.
    now apply pseudo_srorder_pos_mult_compat.
  Qed.

  Global Instance: SubStrongSetoid_Binary_Morphism (+) R R R.
  Proof.
    assert (∀ `{z ∊ R}, SubStrongSetoid_Morphism (z +) R R).
     intros. apply pseudo_order_embedding_ext.
    now apply strong_binary_setoid_morphism_commutative.
  Qed.

 Global Instance: ∀ `{z ∊ R}, StrongLeftCancellation (+) z R.
  Proof.
    intros z ? x ? y ?.
    rewrite !apart_iff_total_lt; try apply _.
    intros [|]; [left | right]; now apply (strictly_order_preserving (z +)).
  Qed.

  Global Instance: ∀ `{z ∊ R}, StrongRightCancellation (+) z R.
  Proof. intros. apply strong_right_cancel_from_left. Qed.

  Lemma pos_nonzero : R₊ ⊆ R ₀.
  Proof. intros x [??]. split. apply _. unfold PropHolds in *.
    apply (apart_iff_total_lt _ _); tauto.
  Qed. 

  Lemma neg_nonzero : R₋ ⊆ R ₀.
  Proof. intros x [??]. split. apply _. unfold PropHolds in *.
    apply (apart_iff_total_lt _ _); tauto.
  Qed. 

  Lemma decompose_nonzero x `{x ∊ R ₀} : x ∊ R₊ ∨ x ∊ R₋ .
  Proof. destruct (_ : x ∊ R ₀).
    assert (0 ≠ x) as Ex by now symmetry.
    rewrite (apart_iff_total_lt 0 x) in Ex.
    destruct Ex; [left | right]; now split.
  Qed.

  Global Instance strong_mult_nonzero: SubStrongSetoid_Binary_Morphism (.*.) (R ₀) (R ₀) (R ₀).
  Proof. split; try (split; apply _).
  + intros x ? y ?; destruct (decompose_nonzero x), (decompose_nonzero y).
      apply pos_nonzero, _.
      apply neg_nonzero, (pos_neg_mult x _ y _).
      apply neg_nonzero, (neg_pos_mult x _ y _).
      apply pos_nonzero, (neg_mult     x _ y _).
  + intros x₁ ? y₁ ? x₂ ? y₂ ?. exact (strong_binary_extensionality (.*.) x₁ y₁ x₂ y₂).
  Qed.

  Lemma neg_mult_decompose x `{x ∊ R} y `{y ∊ R} `{x * y ∊ R₋} : (x ∊ R₋ ∧ y ∊ R₊) ∨ (x ∊ R₊ ∧ y ∊ R₋).
  Proof.
    assert (x * y ∊ R ₀) by now apply neg_nonzero.
    destruct (nonzero_product x y).
    destruct (decompose_nonzero x), (decompose_nonzero y); try tauto;
    pose proof (neg_not_pos (x*y)) as E; contradict E.
    apply _. now apply neg_mult.
  Qed.

  Lemma pos_mult_decompose x `{x ∊ R} y `{y ∊ R} `{x * y ∊ R₊} : (x ∊ R₊ ∧ y ∊ R₊) ∨ (x ∊ R₋ ∧ y ∊ R₋).
  Proof.
    assert (x * y ∊ R ₀) by now apply pos_nonzero.
    destruct (nonzero_product x y).
    destruct (decompose_nonzero x), (decompose_nonzero y); try tauto;
    pose proof (pos_not_neg (x*y)) as E; contradict E.
    now apply pos_neg_mult. now apply neg_pos_mult.
  Qed.

  Existing Instance Pos_subset.

  Global Instance: ∀ `{z ∊ R₊}, StrictlyOrderReflecting (z *.) R R.
  Proof.
    intros z ?. repeat (split; try apply _). intros x ? y ? E1.
    apply (not_lt_apart_lt_flip _ _).
     intros E2. apply (lt_flip _ _ E1).
     now apply (strictly_order_preserving (z *.)).
    apply (strong_extensionality (z *.) _ _).
    now apply (pseudo_order_lt_apart_flip _ _).
  Qed.

  Global Instance: ∀ `{z ∊ R₊}, StrictlyOrderReflecting (.* z) R R.
  Proof.
    intros z ?. repeat (split; try apply _). intros x ? y ? E1.
    apply (not_lt_apart_lt_flip _ _).
     intros E2. apply (lt_flip _ _ E1).
     now apply (strictly_order_preserving (.* z)).
    apply (strong_extensionality (.* z) _ _).
    now apply (pseudo_order_lt_apart_flip _ _).
  Qed.

  Global Instance: ∀ `{z ∊ R ₀}, StrongLeftCancellation (.*.) z R.
  Proof.
    intros z ? x ? y ? E. destruct (_: z ∊ R ₀).
    rewrite apart_iff_total_lt in E |- *; try apply _.
    destruct E as [E|E]; destruct (decompose_nonzero z).
    + left. now apply (strictly_order_preserving (z *.) _ _).
    + right. now apply (flip_neg_mult_l _ _ _).
    + right. now apply (strictly_order_preserving (z *.) _ _).
    + left. now apply (flip_neg_mult_l _ _ _).
  Qed.

  Global Instance: ∀ `{z ∊ R ₀}, StrongRightCancellation (.*.) z R.
  Proof.
    intros z ? x ? y ? E. destruct (_: z ∊ R ₀).
    rewrite apart_iff_total_lt in E |- *; try apply _.
    destruct E as [E|E]; destruct (decompose_nonzero z).
    + left. now apply (strictly_order_preserving (.* z) _ _).
    + right. now apply (flip_neg_mult_r _ _ _).
    + right. now apply (strictly_order_preserving (.* z) _ _).
    + left. now apply (flip_neg_mult_r _ _ _).
  Qed.

  Global Instance: ∀ `{z ∊ R ₀}, LeftCancellation (.*.) z R.
  Proof. intros. now apply _. Qed.

  Global Instance: ∀ `{z ∊ R ₀}, RightCancellation (.*.) z R.
  Proof. intros. now apply _. Qed.

  Lemma square_pos x `{x ∊ R ₀} : x * x ∊ R₊ .
  Proof. destruct (decompose_nonzero x). apply _. now apply neg_mult. Qed.

  Lemma pos_mult_rev_l x `{x ∊ R} y `{y ∊ R₊} `{x * y ∊ R₊} : x ∊ R₊ .
  Proof. split. apply _. apply (strictly_order_reflecting (.* y) _ _). rewrite_on R -> (mult_0_l y). firstorder. Qed.

  Lemma pos_mult_rev_r x `{x ∊ R₊} y `{y ∊ R} `{x * y ∊ R₊} : y ∊ R₊ .
  Proof. split. apply _. apply (strictly_order_reflecting (x *.) _ _). rewrite_on R -> (mult_0_r x). firstorder. Qed.

  Context `{PropHolds (1 ≠ 0)}.

  Instance one_pos : 1 ∊ R₊.
  Proof. rewrite <- (mult_1_r 1). exact (square_pos 1). Qed.

  Instance lt_0_1 : PropHolds (0 < 1).
  Proof. now destruct (_:1 ∊ R₊). Qed.

  Instance lt_0_2 : PropHolds (0 < 2).
  Proof. now destruct (_:2 ∊ R₊). Qed.

  Instance lt_0_3 : PropHolds (0 < 3).
  Proof. now destruct (_:3 ∊ R₊). Qed.

  Instance lt_0_4 : PropHolds (0 < 4).
  Proof. now destruct (_:4 ∊ R₊). Qed.

  Lemma lt_1_2 : 1 < 2.
  Proof. apply (pos_plus_lt_compat_r _ _). Qed.

  Lemma lt_1_3 : 1 < 3.
  Proof. apply (pos_plus_lt_compat_r _ _). Qed.

  Lemma lt_1_4 : 1 < 4.
  Proof. apply (pos_plus_lt_compat_r _ _). Qed.

  Lemma lt_2_3 : 2 < 3.
  Proof. apply (strictly_order_preserving (1+) _ _), lt_1_2. Qed.

  Lemma lt_2_4 : 2 < 4.
  Proof. apply (strictly_order_preserving (1+) _ _), lt_1_3. Qed.

  Lemma lt_3_4 : 3 < 4.
  Proof. apply (strictly_order_preserving (1+) _ _), lt_2_3. Qed.

  Instance apart_0_2 : PropHolds (2 ≠ 0).
  Proof. red. symmetry. apply (pseudo_order_lt_apart _ _), lt_0_2. Qed.
End pseudo_semiring_order.

Hint Extern 7 (PropHolds (0 < 1)) => eapply @lt_0_1 : typeclass_instances.
Hint Extern 7 (PropHolds (0 < 2)) => eapply @lt_0_2 : typeclass_instances.
Hint Extern 7 (PropHolds (0 < 3)) => eapply @lt_0_3 : typeclass_instances.
Hint Extern 7 (PropHolds (0 < 4)) => eapply @lt_0_4 : typeclass_instances.
Hint Extern 7 (PropHolds (2 ≠ 0)) => eapply @apart_0_2 : typeclass_instances.

Section full_pseudo_semiring_order.
  Context `{FullPseudoSemiRingOrder (R:=R)}.

  Global Instance: FullPseudoOrder R.
  Proof. split. apply _. apply full_pseudo_srorder_le_iff_not_lt_flip. Qed.

  Lemma nonneg_not_neg x `{x ∊ R⁺} : ¬ x ∊ R₋ .
  Proof. destruct (_ : x ∊ R⁺) as [? E]. rewrite (le_iff_not_lt_flip _ _) in E. firstorder. Qed.

  Lemma nonpos_not_pos x `{x ∊ R⁻} : ¬ x ∊ R₊ .
  Proof. destruct (_ : x ∊ R⁻) as [? E]. rewrite (le_iff_not_lt_flip _ _) in E. firstorder. Qed.

  Lemma neg_not_nonneg x `{x ∊ R₋} : ¬ x ∊ R⁺ .
  Proof. intros [? E]. rewrite (le_iff_not_lt_flip _ _) in E. firstorder. Qed.

  Lemma pos_not_nonpos x `{x ∊ R₊} : ¬ x ∊ R⁻ .
  Proof. intros [? E]. rewrite (le_iff_not_lt_flip _ _) in E. firstorder. Qed.

  Lemma not_neg_nonneg x `{x ∊ R} : ¬ x ∊ R₋ → x ∊ R⁺.
  Proof. split. apply _. apply (le_iff_not_lt_flip _ _). firstorder. Qed.

  Lemma not_pos_nonpos x `{x ∊ R} : ¬ x ∊ R₊ → x ∊ R⁻.
  Proof. split. apply _. apply (le_iff_not_lt_flip _ _). firstorder. Qed.

  Lemma pos_nonneg : R₊ ⊆ R⁺ .
  Proof. intros x ?. pose proof (Pos_subset). apply (not_neg_nonneg x), (pos_not_neg x). Qed.

  Lemma neg_nonpos : R₋ ⊆ R⁻ .
  Proof. intros x ?. pose proof (Neg_subset). apply (not_pos_nonpos x), (neg_not_pos x). Qed.

  Global Instance: SemiRingOrder R.
  Proof. split. apply _. apply _.
  + intros x ? y ?. rewrite (le_iff_not_lt_flip _ _).
    now apply pseudo_srorder_partial_minus.
  + intros z ?. repeat (split; try apply _); intros x ? y ?;
    rewrite (le_iff_not_lt_flip x y); rewrite (le_iff_not_lt_flip (z+x) (z+y));
    intro E; contradict E.
    apply (strictly_order_reflecting (z+) _ _ E).
    apply (strictly_order_preserving (z+) _ _ E).
  + intros x ? y ?. pose proof (NonNeg_subset R).
    apply (not_neg_nonneg (x*y)). intro.
    destruct (neg_mult_decompose x y) as [[??]|[??]].
    apply (nonneg_not_neg x _).
    apply (nonneg_not_neg y _).
  Qed.

  Global Instance: ∀ `{z ∊ R₊}, OrderReflecting (z *.) R R.
  Proof. intros. now apply full_pseudo_order_reflecting. Qed.

  Global Instance: ∀ `{z ∊ R₊}, OrderReflecting (.* z) R R.
  Proof. intros. now apply full_pseudo_order_reflecting. Qed.

  Lemma plus_lt_le_compat x₁ `{x₁ ∊ R} y₁ `{y₁ ∊ R} x₂ `{x₂ ∊ R} y₂ `{y₂ ∊ R}
    : x₁ < y₁ → x₂ ≤ y₂ → x₁ + x₂ < y₁ + y₂.
  Proof.
    intros E1 E2.
    apply (lt_le_trans _ (y₁ + x₂) _).
     now apply (strictly_order_preserving (+ x₂)).
    now apply (order_preserving (y₁ +)).
  Qed.

  Lemma plus_le_lt_compat x₁ `{x₁ ∊ R} y₁ `{y₁ ∊ R} x₂ `{x₂ ∊ R} y₂ `{y₂ ∊ R}
    : x₁ ≤ y₁ → x₂ < y₂ → x₁ + x₂ < y₁ + y₂.
  Proof.
    intros E1 E2.
    apply (le_lt_trans _ (y₁ + x₂) _).
     now apply (order_preserving (+ x₂)).
    now apply (strictly_order_preserving (y₁ +)).
  Qed.

  Lemma nonneg_plus_lt_compat_r x `{x ∊ R} y `{y ∊ R} z `{z ∊ R⁺} : x < y → x < y + z.
  Proof. intros. pose proof (NonNeg_subset R).
    rewrite_on R <-(plus_0_r x). apply (plus_lt_le_compat _ _ _ _); firstorder.
  Qed.

  Lemma nonneg_plus_lt_compat_l x `{x ∊ R} y `{y ∊ R} z `{z ∊ R⁺} : x < y → x < z + y.
  Proof. intros. pose proof (NonNeg_subset R). rewrite_on R -> (commutativity (f:=(+)) z y).
    now apply nonneg_plus_lt_compat_r.
  Qed.

  Lemma pos_plus_le_lt_compat_r x `{x ∊ R} y `{y ∊ R} z `{z ∊ R₊} : x ≤ y → x < y + z.
  Proof. intros. pose proof (Pos_subset R).
    rewrite_on R <-(plus_0_r x). apply (plus_le_lt_compat _ _ _ _); firstorder.
  Qed.

  Lemma pos_plus_le_lt_compat_l x `{x ∊ R} y `{y ∊ R} z `{z ∊ R₊} : x ≤ y → x < z + y.
  Proof. intros. pose proof (Pos_subset R). rewrite_on R -> (commutativity (f:=(+)) z y).
    now apply pos_plus_le_lt_compat_r.
  Qed.

  Lemma square_nonneg x `{x ∊ R} : x * x ∊ R⁺ .
  Proof.
    apply (not_neg_nonneg _). intro.
    destruct (neg_mult_decompose x x) as [[??]|[??]];
    apply (pos_not_neg x _).
  Qed.

  Lemma nonneg_mult_rev_l x `{x ∊ R} y `{y ∊ R₊} `{x * y ∊ R⁺} : x ∊ R⁺ .
  Proof. split. apply _. apply (order_reflecting (.* y) _ _). pose proof (Pos_subset R). rewrite_on R -> (mult_0_l y). firstorder. Qed.

  Lemma nonneg_mult_rev_r x `{x ∊ R₊} y `{y ∊ R} `{x * y ∊ R⁺} : y ∊ R⁺ .
  Proof. split. apply _. apply (order_reflecting (x *.) _ _). pose proof (Pos_subset R). rewrite_on R -> (mult_0_r x). firstorder. Qed.

  Instance one_nonneg : 1 ∊ R⁺.
  Proof. rewrite_on R <- (mult_1_r 1). exact (square_nonneg 1). Qed.

  Instance le_0_1 : PropHolds (0 ≤ 1).
  Proof. now destruct (_:1 ∊ R⁺). Qed.

  Instance le_0_2 : PropHolds (0 ≤ 2).
  Proof. now destruct (_:2 ∊ R⁺). Qed.

  Instance le_0_3 : PropHolds (0 ≤ 3).
  Proof. now destruct (_:3 ∊ R⁺). Qed.

  Instance le_0_4 : PropHolds (0 ≤ 4).
  Proof. now destruct (_:4 ∊ R⁺). Qed.

  Lemma le_1_2 : 1 ≤ 2.
  Proof. apply (nonneg_plus_le_compat_r _ _). Qed.

  Lemma le_1_3 : 1 ≤ 3.
  Proof. apply (nonneg_plus_le_compat_r _ _). Qed.

  Lemma le_1_4 : 1 ≤ 4.
  Proof. apply (nonneg_plus_le_compat_r _ _). Qed.

  Lemma le_2_3 : 2 ≤ 3.
  Proof. apply (order_preserving (1+) _ _), le_1_2. Qed.

  Lemma le_2_4 : 2 ≤ 4.
  Proof. apply (order_preserving (1+) _ _), le_1_3. Qed.

  Lemma le_3_4 : 3 ≤ 4.
  Proof. apply (order_preserving (1+) _ _), le_2_3. Qed.

  Lemma ge_1_mult_compat x `{x ∊ R} y `{y ∊ R} : 1 ≤ x → 1 ≤ y → 1 ≤ x * y.
  Proof.
    intros. assert (x ∊ R⁺) by (split; [ apply _ | subtransitivity 1; exact le_0_1 ]).
    now apply (ge_1_mult_le_compat_r _).
  Qed.

  Lemma gt_1_ge_1_mult_compat x `{x ∊ R} y `{y ∊ R} : 1 < x → 1 ≤ y → 1 < x * y.
  Proof.
    intros. assert (x ∊ R⁺) by (split; [ apply _ | subtransitivity 1; [ exact le_0_1 | now apply (lt_le _ _) ] ]).
    apply (lt_le_trans _ x _); trivial.
    apply (ge_1_mult_le_compat_r _ _ _); trivial. subreflexivity.
  Qed.

  Lemma ge_1_gt_1_mult_compat x `{x ∊ R} y `{y ∊ R} : 1 ≤ x → 1 < y → 1 < x * y.
  Proof.
    intros. assert (y ∊ R⁺) by (split; [ apply _ | subtransitivity 1; [ exact le_0_1 | now apply (lt_le _ _) ] ]).
    apply (lt_le_trans _ y _); trivial.
    apply (ge_1_mult_le_compat_l _ _ _); trivial. subreflexivity.
  Qed.

  Context `{PropHolds (1 ≠ 0)}.

  Lemma not_le_1_0 : ¬1 ≤ 0.
  Proof. now apply (lt_not_le_flip _ _), lt_0_1. Qed.

  Lemma not_le_2_0 : ¬2 ≤ 0.
  Proof. now apply (lt_not_le_flip _ _), lt_0_2. Qed.
End full_pseudo_semiring_order.

(* Due to bug #2528 *)
Hint Extern 7 (PropHolds (0 ≤ 1)) => eapply @le_0_1 : typeclass_instances.
Hint Extern 7 (PropHolds (0 ≤ 2)) => eapply @le_0_2 : typeclass_instances.
Hint Extern 7 (PropHolds (0 ≤ 3)) => eapply @le_0_3 : typeclass_instances.
Hint Extern 7 (PropHolds (0 ≤ 4)) => eapply @le_0_4 : typeclass_instances.

Section dec_semiring_order.
  (* Maybe these assumptions can be weakened? *)
  Context `{SemiRingOrder A (R:=R)} `{UnEq A} `{!StandardUnEq A}
    `{!NoZeroDivisors R} `{!TotalRelation (≤) R} `{∀ x y, Decision (x = y)}.

  Context `{Lt A} (lt_correct : ∀ `{x ∊ R} `{y ∊ R}, x < y ↔ x ≤ y ∧ x ≠ y).

  Instance: FullPseudoOrder R := dec_full_pseudo_order lt_correct.

  Existing Instance pseudo_order_setoid.

  Instance dec_pseudo_srorder: PseudoSemiRingOrder R.
  Proof. split. apply _. apply _.
  + intros x ? y ? E. now apply srorder_partial_minus, not_lt_le_flip.
  + intros z. repeat (split; try apply _).
    intros x ? y ?. rewrite !lt_correct; try apply _. rewrite !standard_uneq.
    intros [E2a E2b]. split.
      now apply (order_preserving (z+)).
      contradict E2b. now apply (left_cancellation (+) z R).
  + exact (dec_strong_binary_morphism (.*.) R R R).
  + intros x [? Ex] y [? Ey]. split. apply _.
    rewrite lt_correct in Ex, Ey |- *; try apply _. split.
    * assert (x ∊ R⁺) by firstorder; assert (y ∊ R⁺) by firstorder.
      pose proof (_ : x * y ∊ R⁺). firstorder.
    * assert (x ∊ R ₀) by (split; [| red; symmetry]; firstorder).
      assert (y ∊ R ₀) by (split; [| red; symmetry]; firstorder).
      pose proof (_ : x * y ∊ R ₀). symmetry. firstorder.
  Qed.

  Instance dec_full_pseudo_srorder: FullPseudoSemiRingOrder R.
  Proof.
    split; try apply _.
    now apply le_iff_not_lt_flip.
  Qed.
End dec_semiring_order.

Section another_semiring.
  Context `{SemiRingOrder (R:=R1)}.

  Existing Instance NonNeg_subset.
  
  Lemma projected_srorder `{SemiRing B (R:=R2)} `{Le B} f
      `{!SemiRing_Morphism f R2 R1} `{!Injective f R2 R1} :
    (∀ `{x ∊ R2} `{y ∊ R2}, x ≤ y ↔ f x ≤ f y) 
  → (∀ `{x ∊ R2} `{y ∊ R2}, x ≤ y → ∃ `{z ∊ R2}, y = x + z) → SemiRingOrder R2.
  Proof.
    intros P ?. pose proof (projected_partial_order f P).
    split. apply _. apply _. assumption.
    split; (split; [split; apply _ |]); intros; apply (P _ _ _ _).
    + rewrite_on R1 -> (preserves_plus z x).
      rewrite_on R1 -> (preserves_plus z y).
      now apply (order_preserving _ _ _), P.
    + apply (order_reflecting (f z +) _ _).
      rewrite_on R1 <- (preserves_plus z x).
      rewrite_on R1 <- (preserves_plus z y).
      now apply (P _ _ _ _).
    + intros x ? y ?.
      cut (f x * f y ∊ R1⁺).
        intros [??]. split. apply _. apply (P _ _ _ _).
        rewrite_on R1 -> (preserves_mult x y). now rewrite_on R1 -> preserves_0.
      assert (∀ z, z ∊ R2⁺ → f z ∊ R1⁺).
        split. apply _. red. rewrite_on R1 <- preserves_0. apply (P _ _ _ _). firstorder.
      apply _.
   Qed.

 Context `{SemiRingOrder (R:=R2)} `{!SemiRing_Morphism f R1 R2}.

  (* If a morphism agrees on the positive cone then it is order preserving *)
  Lemma preserving_preserves_nonneg : (∀ `{x ∊ R1⁺}, f x ∊ R2⁺) → OrderPreserving f R1 R2.
  Proof.
    intro. repeat (split; try apply _). intros x ? y ? F.
    destruct (decompose_le F) as [z [? Ez]].
    apply (compose_le _ _ (f z)).
    rewrite_on R1 -> Ez. now rewrite (preserves_plus _ _).
  Qed.

  Instance preserves_nonneg `{!OrderPreserving f R1 R2} x `{x ∊ R1⁺} : f x ∊ R2⁺ .
  Proof. split. apply _. rewrite_on R2 <- preserves_0. apply (order_preserving f _ _). firstorder. Qed.

  Instance preserves_nonpos `{!OrderPreserving f R1 R2} x `{x ∊ R1⁻} : f x ∊ R2⁻ .
  Proof. destruct (_:x ∊ R1⁻). split. apply _. rewrite_on R2 <- preserves_0. now apply (order_preserving f _ _). Qed.

  Lemma preserves_ge_1 `{!OrderPreserving f R1 R2} x `{x ∊ R1} : 1 ≤ x → 1 ≤ f x.
  Proof. intros. rewrite_on R2 <-preserves_1. now apply (order_preserving f _ _). Qed.

  Lemma preserves_le_1 `{!OrderPreserving f R1 R2} x `{x ∊ R1} : x ≤ 1 → f x ≤ 1.
  Proof. intros. rewrite_on R2 <-preserves_1. now apply (order_preserving f _ _). Qed.
End another_semiring.

Section another_semiring_strict.
  Context `{StrictSemiRingOrder (R:=R1)}. 

  Existing Instance Pos_subset.
  
  Lemma projected_strict_srorder `{SemiRing B (R:=R2)} `{Lt B} f
      `{!SemiRing_Morphism f R2 R1} :
    (∀ `{x ∊ R2} `{y ∊ R2}, x < y ↔ f x < f y) 
  → (∀ `{x ∊ R2} `{y ∊ R2}, x < y → ∃ `{z ∊ R2}, y = x + z) → StrictSemiRingOrder R2.
  Proof.
    intros P ?. pose proof (projected_sub_strict_order f P).
    split. apply _. apply _. assumption.
    split; (split; [split; apply _ |]); intros; apply (P _ _ _ _).
    + rewrite_on R1 -> (preserves_plus z x).
      rewrite_on R1 -> (preserves_plus z y).
      now apply (strictly_order_preserving _ _ _), P.
    + apply (strictly_order_reflecting (f z +) _ _).
      rewrite_on R1 <- (preserves_plus z x).
      rewrite_on R1 <- (preserves_plus z y).
      now apply (P _ _ _ _).
    + intros x ? y ?.
      cut (f x * f y ∊ R1₊).
        intros [??]. split. apply _. apply (P _ _ _ _).
        rewrite_on R1 -> (preserves_mult x y). now rewrite_on R1 -> preserves_0.
      assert (∀ z, z ∊ R2₊ → f z ∊ R1₊).
        split. apply _. red. rewrite_on R1 <- preserves_0. apply (P _ _ _ _). firstorder.
      apply _.
  Qed.

  Context `{StrictSemiRingOrder (R:=R2)} `{!SemiRing_Morphism f R1 R2}.

  Lemma strictly_preserving_preserves_pos : (∀ `{x ∊ R1₊}, f x ∊ R2₊) → StrictlyOrderPreserving f R1 R2.
  Proof.
    intro. repeat (split; try apply _). intros x ? y ? F.
    destruct (decompose_lt F) as [z [? Ez]].
    apply (compose_lt _ _ (f z)).
    rewrite_on R1 -> Ez. now rewrite (preserves_plus _ _).
  Qed.

  Instance preserves_pos `{!StrictlyOrderPreserving f R1 R2} x `{x ∊ R1₊} : f x ∊ R2₊ .
  Proof. split. apply _. rewrite_on R2 <- preserves_0. apply (strictly_order_preserving f _ _). firstorder. Qed.

  Instance preserves_neg `{!StrictlyOrderPreserving f R1 R2} x `{x ∊ R1₋} : f x ∊ R2₋ .
  Proof. destruct (_:x ∊ R1₋). split. apply _. rewrite_on R2 <- preserves_0. now apply (strictly_order_preserving f _ _). Qed.

  Lemma preserves_gt_1 `{!StrictlyOrderPreserving f R1 R2} x `{x ∊ R1} : 1 < x → 1 < f x.
  Proof. intros. rewrite_on R2 <-preserves_1. now apply (strictly_order_preserving f _ _). Qed.

  Lemma preserves_lt_1 `{!StrictlyOrderPreserving f R1 R2} x `{x ∊ R1} : x < 1 → f x < 1.
  Proof. intros. rewrite_on R2 <-preserves_1. now apply (strictly_order_preserving f _ _). Qed.

End another_semiring_strict.

(* Due to bug #2528 *)
(*
Hint Extern 15 (PropHolds (_ ≤ _ _)) => eapply @preserves_nonneg : typeclass_instances.
Hint Extern 15 (PropHolds (_ < _ _)) => eapply @preserves_pos : typeclass_instances.
*)
(* Oddly enough, the above hints do not work for goals of the following shape? *)
(*
Hint Extern 15 (PropHolds (_ ≤ '_)) => eapply @preserves_nonneg : typeclass_instances.
Hint Extern 15 (PropHolds (_ < '_)) => eapply @preserves_pos : typeclass_instances.
*)
