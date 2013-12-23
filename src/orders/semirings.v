Require Import
  abstract_algebra interfaces.orders theory.strong_setoids
  theory.common_props theory.rings theory.strong_rings.
Require Export
  orders.orders orders.maps.

Local Ltac subsetoid_tac R :=
  first [ pose proof po_setoid | pose proof so_setoid ];
  apply subsetoid_alt; [apply _ | | apply _]; intros ?? E [??]; unfold_sigs;
  split; [apply _ |red]; now rewrite_on R <- E.

Lemma NonNeg_subsetoid   `{PartialOrder A (P:=R)} `{Zero A} `{0 ∊ R}: R⁺ ⊆ R. Proof. subsetoid_tac R. Qed.
Lemma NonPos_subsetoid   `{PartialOrder A (P:=R)} `{Zero A} `{0 ∊ R}: R⁻ ⊆ R. Proof. subsetoid_tac R. Qed.
Lemma Pos_subsetoid `{StrictSetoidOrder A (S:=R)} `{Zero A} `{0 ∊ R}: R₊ ⊆ R. Proof. subsetoid_tac R. Qed.
Lemma Neg_subsetoid `{StrictSetoidOrder A (S:=R)} `{Zero A} `{0 ∊ R}: R₋ ⊆ R. Proof. subsetoid_tac R. Qed.

Hint Extern 2 (?R⁺ ⊆ ?R) => eapply @NonNeg_subsetoid : typeclass_instances.
Hint Extern 2 (?R⁻ ⊆ ?R) => eapply @NonPos_subsetoid : typeclass_instances.
Hint Extern 2 (?R₊ ⊆ ?R) => eapply @Pos_subsetoid    : typeclass_instances.
Hint Extern 2 (?R₋ ⊆ ?R) => eapply @Neg_subsetoid    : typeclass_instances.

Section semiring_order.
  Context `{SemiRingOrder (R:=R)}.
  Instance: SemiRing R := srorder_semiring.

  Lemma nonneg_or_nonpos `{!TotalOrder R} x `{x ∊ R} : x ∊ R⁺ ∨ x ∊ R⁻.
  Proof. destruct (total le 0 x); [left | right]; firstorder. Qed.

  Lemma nonneg_nonpos_0 x `{p:x ∊ R⁺} `{n:x ∊ R⁻} : x = 0.
  Proof. destruct p, n. now apply (antisymmetry (≤) _ _). Qed.

  Global Instance: ∀ `{z ∊ R}, OrderEmbedding R R (+z).
  Proof.
    intros. split.
     apply order_preserving_flip.
    apply order_reflecting_flip.
  Qed.

  Global Instance: ∀ `{z ∊ R}, LeftCancellation (+) z R.
  Proof.
    intros z ? x ? y ? E.
    apply (antisymmetry (≤)); trivial;
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
  Proof. rewrite_on R -> (commutativity (+) z x). exact (nonneg_plus_le_compat_r x z). Qed.

  Lemma plus_le_compat_nonneg_l x `{x ∊ R} z `{z ∊ R} : x ≤ z + x → z ∊ R⁺.
  Proof. rewrite_on R -> (commutativity (+) z x). exact (plus_le_compat_nonneg_r x z). Qed.

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
  Proof. rewrite_on R -> (commutativity (+) z y). exact (plus_le_compat_r x y z). Qed.

  Lemma plus_le_compat_2 a `{a ∊ R} b `{b ∊ R} c `{c ∊ R}
                         x `{x ∊ R} y `{y ∊ R} z `{z ∊ R}
    : a ≤ b ≤ c → x ≤ y ≤ z → a + x ≤ b + y ≤ c + z.
  Proof. intros [??] [??]. split; now apply (plus_le_compat _ _ _ _). Qed.

  Lemma nonpos_plus_compat : Closed (R⁻ ⇀ R⁻ ⇀ R⁻) (+).
  Proof. intros x [??] y [??]. split. apply _. red. rewrite_on R <-(plus_0_r 0).
    now apply (plus_le_compat x 0 y 0).
  Qed.

  Lemma nonneg_plus_compat : Closed (R⁺ ⇀ R⁺ ⇀ R⁺) (+).
  Proof. intros ?? ??. split. apply _. apply plus_le_compat_l; try apply _; firstorder. Qed.

  Lemma decompose_le `{x ∊ R} `{y ∊ R} : x ≤ y → ∃ `{z ∊ R⁺}, y = x + z.
  Proof.
    intros E.
    destruct (srorder_partial_minus x y E) as [z [? Ez]].
    assert (z ∊ R⁺). split. apply _. red.
    apply (order_reflecting (x+) 0 z).
    now rewrite_on R -> (plus_0_r x), <-Ez.
    now exists_sub z.
  Qed.

  Lemma compose_le x `{x ∊ R} y `{y ∊ R} z `{z ∊ R⁺} : y = x + z → x ≤ y.
  Proof. intros E2. rewrite_on R -> E2. exact (nonneg_plus_le_compat_r x z). Qed.

  Global Instance: ∀ `{z ∊ R⁺}, OrderPreserving R R (z *.).
  Proof.
    intros z ?.
    repeat (split; try apply _).
    intros x ? y ? F.
    destruct (decompose_le F) as [a [? Ea]].
    rewrite_on R -> Ea, (plus_mult_distr_l z x a).
    exact (nonneg_plus_le_compat_r (z*x) (z*a)).
  Qed.

  Global Instance: ∀ `{z ∊ R⁺}, OrderPreserving R R (.* z).
  Proof.
    intros z ?.
    repeat (split; try apply _).
    intros x ? y ? F.
    destruct (decompose_le F) as [a [? Ea]].
    rewrite_on R -> Ea, (plus_mult_distr_r x a z).
    exact (nonneg_plus_le_compat_r (x*z) (a*z)).
  Qed.

  Lemma mult_le_compat x₁ `{x₁ ∊ R⁺} y₁ `{y₁ ∊ R} x₂ `{x₂ ∊ R⁺} y₂ `{y₂ ∊ R} :
    x₁ ≤ y₁ → x₂ ≤ y₂ → x₁ * x₂ ≤ y₁ * y₂.
  Proof.
    intros E1 E2.
    assert (y₁ ∊ R⁺) by (split; [|red; subtransitivity x₁]; firstorder).
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
    apply (compose_le _ _ (a*b)).
    rewrite (R $ plus_mult_distr_l _ _ _), <- (R $ associativity (+) _ _ _), <- (R $ plus_mult_distr_r _ _ _).
    now rewrite_on R <- Ea, (mult_0_l b), (plus_0_r (z*x)).
  Qed.

  Lemma flip_nonpos_mult_r x `{x ∊ R} y `{y ∊ R} z `{z ∊ R⁻} : x ≤ y → y * z ≤ x * z.
  Proof.
    destruct (_ : z ∊ R⁻) as [? Ez]. intros Exy.
    destruct (decompose_le Ez) as [a [? Ea]], (decompose_le Exy) as [b [? Eb]].
    rewrite_on R -> Eb.
    apply (compose_le _ _ (b * a)).
    rewrite (R $ plus_mult_distr_r _ _ _), <- (R $ associativity (+) _ _ _), <- (R $ plus_mult_distr_l _ _ _).
    now rewrite_on R <- Ea, (mult_0_r b), (plus_0_r (x*z)).
  Qed.

  Lemma nonpos_mult : Closed (R⁻ ⇀ R⁻ ⇀ R⁺) (.*.).
  Proof.
    intros x ? y [??]. destruct (_ : x ∊ R⁻). split. apply _. red.
    rewrite_on R <- (mult_0_r x).
    apply (flip_nonpos_mult_l y 0 x). solve_propholds.
  Qed.

  Lemma nonpos_nonneg_mult : Closed (R⁻ ⇀ R⁺ ⇀ R⁻) (.*.).
  Proof.
    intros x ? y [??]. destruct (_ : x ∊ R⁻). split. apply _. red.
    rewrite_on R <- (mult_0_r x).
    apply (flip_nonpos_mult_l 0 y x). solve_propholds.
  Qed.

  Lemma nonneg_nonpos_mult : Closed (R⁺ ⇀ R⁻ ⇀ R⁻) (.*.).
  Proof.
    intros x [??] y ?. destruct (_ : y ∊ R⁻). split. apply _. red.
    rewrite_on R <- (mult_0_l y).
    apply (flip_nonpos_mult_r 0 x y). solve_propholds.
  Qed.
End semiring_order.

Hint Extern 4 (_ + _ ∊ _⁺) => eapply @nonneg_plus_compat : typeclass_instances. 
Hint Extern 4 (_ + _ ∊ _⁻) => eapply @nonpos_plus_compat : typeclass_instances. 
Hint Extern 8 (_ * _ ∊ _⁺) => eapply @nonpos_mult : typeclass_instances. 
Hint Extern 8 (_ * _ ∊ _⁻) => eapply @nonpos_nonneg_mult : typeclass_instances. 
Hint Extern 8 (_ * _ ∊ _⁻) => eapply @nonneg_nonpos_mult : typeclass_instances. 

Section strict_order.
  Context `{StrictSetoidOrder A (S:=R)} `{Zero A} `{!0 ∊ R}.

  Lemma pos_not_neg x `{x ∊ R₊} : ¬ x ∊ R₋ .
  Proof. intros [? E]. apply (lt_flip _ _ E). firstorder. Qed.

  Lemma neg_not_pos x `{x ∊ R₋} : ¬ x ∊ R₊ .
  Proof. intros [? E]. apply (lt_flip _ _ E). firstorder. Qed.
End strict_order.

Section strict_semiring_order.
  Context `{StrictSemiRingOrder (R:=R)}.
  Instance: SemiRing R := strict_srorder_semiring.

  Global Instance: ∀ `{z ∊ R}, StrictOrderEmbedding R R (+z).
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
  Proof. rewrite_on R -> (commutativity (+) z x). exact (pos_plus_lt_compat_r x z). Qed.

  Lemma plus_lt_compat_pos_l x `{x ∊ R} z `{z ∊ R} : x < z + x → z ∊ R₊.
  Proof. rewrite_on R -> (commutativity (+) z x). exact (plus_lt_compat_pos_r x z). Qed.

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
  Proof. rewrite_on R -> (commutativity (+) z y). exact (plus_lt_compat_r x y z). Qed.

  Lemma plus_lt_compat_2 a `{a ∊ R} b `{b ∊ R} c `{c ∊ R}
                         x `{x ∊ R} y `{y ∊ R} z `{z ∊ R}
    : a < b < c → x < y < z → a + x < b + y < c + z.
  Proof. intros [??] [??]. split; now apply (plus_lt_compat _ _ _ _). Qed.

  Lemma neg_plus_compat : Closed (R₋ ⇀ R₋ ⇀ R₋) (+).
  Proof. intros x [??] y [??]. split. apply _. red. rewrite_on R <-(plus_0_r 0). now apply (plus_lt_compat x 0 y 0). Qed.

  Instance pos_plus_compat : Closed (R₊ ⇀ R₊ ⇀ R₊) (+).
  Proof. intros x ? y ?. split. apply _. red. apply (plus_lt_compat_l 0 y x); firstorder. Qed.

  Lemma compose_lt x `{x ∊ R} y `{y ∊ R} z `{z ∊ R₊} : y = x + z → x < y.
  Proof.
    intros E2. rewrite_on R -> E2.
    exact (pos_plus_lt_compat_r x z).
  Qed.

  Lemma decompose_lt `{x ∊ R} `{y ∊ R} : x < y → ∃ `{z ∊ R₊}, y = x + z.
  Proof.
    intros E.
    destruct (strict_srorder_partial_minus x y E) as [z [? Ez]].
    assert (z ∊ R₊). split. apply _. red.
    apply (strictly_order_reflecting (x+) 0 z).
    now rewrite_on R <- Ez, (plus_0_r x).
    now exists_sub z.
  Qed.

  Global Instance: ∀ `{z ∊ R₊}, StrictlyOrderPreserving R R (z *.).
  Proof.
    intros z ?. repeat (split; try apply _). intros x ? y ? F.
    destruct (decompose_lt F) as [a [? Ea]].
    rewrite_on R -> Ea, (plus_mult_distr_l z x a).
    exact (pos_plus_lt_compat_r (z*x) (z*a)).
  Qed.

  Global Instance: ∀ `{z ∊ R₊}, StrictlyOrderPreserving R R (.* z).
  Proof.
    intros z ?. repeat (split; try apply _). intros x ? y ? F.
    destruct (decompose_lt F) as [a [? Ea]].
    rewrite_on R -> Ea, (plus_mult_distr_r x a z).
    exact (pos_plus_lt_compat_r (x*z) (a*z)).
  Qed.

  Lemma mult_lt_compat x₁ `{x₁ ∊ R₊} y₁ `{y₁ ∊ R} x₂ `{x₂ ∊ R₊} y₂ `{y₂ ∊ R} :
    x₁ < y₁ → x₂ < y₂ → x₁ * x₂ < y₁ * y₂.
  Proof.
    intros E1 E2.
    assert (y₁ ∊ R₊) by (split; [| red; subtransitivity x₁]; firstorder).
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
    apply (compose_lt _ _ (a * b)).
    rewrite (R $ plus_mult_distr_l _ _ _), <- (R $ associativity (+) _ _ _), <- (R $ plus_mult_distr_r _ _ _).
    now rewrite_on R <- Ea, (mult_0_l b), (plus_0_r (z*x)).
  Qed.

  Lemma flip_neg_mult_r x `{x ∊ R} y `{y ∊ R} z `{z ∊ R₋} : x < y → y * z < x * z.
  Proof.
    destruct (_:z ∊ R₋) as [? Ez]. intros Exy.
    destruct (decompose_lt Ez) as [a [? Ea]], (decompose_lt Exy) as [b [? Eb]].
    rewrite_on R -> Eb.
    apply (compose_lt _ _ (b * a)).
    rewrite (R $ plus_mult_distr_r _ _ _), <- (R $ associativity (+) _ _ _), <- (R $ plus_mult_distr_l _ _ _).
    now rewrite_on R <- Ea, (mult_0_r b), (plus_0_r (x*z)).
  Qed.

  Lemma neg_mult : Closed (R₋ ⇀ R₋ ⇀ R₊) (.*.).
  Proof.
    intros x ? y [??]. destruct (_ : x ∊ R₋). split. apply _. red.
    rewrite_on R <- (mult_0_r x).
    apply (flip_neg_mult_l y 0 x). solve_propholds.
  Qed.

  Lemma neg_pos_mult : Closed (R₋ ⇀ R₊ ⇀ R₋) (.*.).
  Proof.
    intros x ? y [??]. destruct (_ : x ∊ R₋). split. apply _. red.
    rewrite_on R <- (mult_0_r x).
    apply (flip_neg_mult_l 0 y x). solve_propholds.
  Qed.

  Lemma pos_neg_mult : Closed (R₊ ⇀ R₋ ⇀ R₋) (.*.).
  Proof.
    intros x [??] y ?. destruct (_ : y ∊ R₋). split. apply _. red.
    rewrite_on R <- (mult_0_l y).
    now apply (flip_neg_mult_r 0 x y).
  Qed.

End strict_semiring_order.

Hint Extern 5 (_ + _ ∊ _₊) => eapply @pos_plus_compat : typeclass_instances. 
Hint Extern 4 (_ + _ ∊ _₋) => eapply @neg_plus_compat : typeclass_instances. 
Hint Extern 8 (_ * _ ∊ _₊) => eapply @neg_mult : typeclass_instances. 
Hint Extern 8 (_ * _ ∊ _₋) => eapply @neg_pos_mult : typeclass_instances. 
Hint Extern 8 (_ * _ ∊ _₋) => eapply @pos_neg_mult : typeclass_instances. 

Lemma pos_nonzero `{PseudoSemiRingOrder (R:=R)} : Subset R₊ (R ₀).
Proof. intros x [??]. split. apply _. red.
  pose proof pseudo_srorder_semiring.
  apply (apart_iff_total_lt _ _); tauto.
Qed. 
Hint Extern 5 (Subset _₊ (_ ₀)) => eapply @pos_nonzero : typeclass_instances.

Lemma neg_nonzero `{PseudoSemiRingOrder (R:=R)} : Subset R₋ (R ₀).
Proof. intros x [??]. split. apply _. red.
  pose proof pseudo_srorder_semiring.
  apply (apart_iff_total_lt _ _); tauto.
Qed. 
Hint Extern 5 (Subset _₋ (_ ₀)) => eapply @neg_nonzero : typeclass_instances.

Hint Extern 15 (?x ∊ ?R ₀) => match goal with
  | el : x ∊ R₊  |- _ => eapply (pos_nonzero (R:=R) x el)
  | el : x ∊ R₋  |- _ => eapply (neg_nonzero (R:=R) x el)
end : typeclass_instances.

Section pseudo_semiring_order.
  Context `{PseudoSemiRingOrder (R:=R)}.
  Instance: StrongSetoid R := pseudo_order_setoid.
  Instance: SemiRing R := pseudo_srorder_semiring.

  Global Instance: StrictSemiRingOrder R.
  Proof.
    split; [ apply _ | apply _ | | apply _ |].
     intros. now apply pseudo_srorder_partial_minus, lt_flip.
    now apply pseudo_srorder_pos_mult_compat.
  Qed.

  Instance: Strong_Binary_Morphism R R R (+).
  Proof.
    assert (∀ `{z ∊ R}, Strong_Morphism R R (z +)).
     intros. apply pseudo_order_embedding_ext.
    exact (strong_binary_morphism_commutative (+) _ _).
  Qed.

  Instance pseudo_sring_order_strong_rng_ops: StrongRngOps R.
  Proof. repeat (split; try apply _). Qed.

  Global Instance: ∀ `{z ∊ R}, StrongLeftCancellation (+) z R.
  Proof.
    intros z ? x ? y ?.
    rewrite !apart_iff_total_lt; try apply _.
    intros [|]; [left | right]; now apply (strictly_order_preserving (z +)).
  Qed.

  Global Instance: ∀ `{z ∊ R}, StrongRightCancellation (+) z R.
  Proof. intros. apply strong_right_cancel_from_left. Qed.

  Lemma decompose_nonzero x `{x ∊ R ₀} : x ∊ R₊ ∨ x ∊ R₋ .
  Proof. destruct (_ : x ∊ R ₀).
    assert (0 ≠ x) as Ex by subsymmetry.
    rewrite (apart_iff_total_lt 0 x) in Ex.
    destruct Ex; [left | right]; now split.
  Qed.

  Global Instance strong_mult_nonzero: Strong_Binary_Morphism (R ₀) (R ₀) (R ₀) (.*.).
  Proof. split.
  + intros x ? y ?; destruct (decompose_nonzero x), (decompose_nonzero y).
      apply pos_nonzero. apply _.
      apply neg_nonzero. apply _.
      apply neg_nonzero. apply _.
      apply pos_nonzero. apply _.
  + rewrite strong_ext_equiv_2. intros. now apply (strong_binary_extensionality (.*.)).
  Qed.

  Lemma neg_mult_decompose x `{x ∊ R} y `{y ∊ R} `{x * y ∊ R₋} : (x ∊ R₋ ∧ y ∊ R₊) ∨ (x ∊ R₊ ∧ y ∊ R₋).
  Proof.
    destruct (nonzero_product x y).
    destruct (decompose_nonzero x), (decompose_nonzero y); try tauto;
    pose proof (neg_not_pos (x*y)) as E; contradict E; apply _.
  Qed.

  Lemma pos_mult_decompose x `{x ∊ R} y `{y ∊ R} `{x * y ∊ R₊} : (x ∊ R₊ ∧ y ∊ R₊) ∨ (x ∊ R₋ ∧ y ∊ R₋).
  Proof.
    destruct (nonzero_product x y).
    destruct (decompose_nonzero x), (decompose_nonzero y); try tauto;
    pose proof (pos_not_neg (x*y)) as E; contradict E; apply _.
  Qed.

  Global Instance: ∀ `{z ∊ R₊}, StrictlyOrderReflecting R R (z *.).
  Proof.
    intros z ?. repeat (split; try apply _). intros x ? y ? E1.
    apply (not_lt_apart_lt_flip _ _).
     intros E2. apply (lt_flip _ _ E1).
     now apply (strictly_order_preserving (z *.)).
    apply (strong_extensionality (z *.)).
    now apply (pseudo_order_lt_apart_flip _ _).
  Qed.

  Global Instance: ∀ `{z ∊ R₊}, StrictlyOrderReflecting R R (.* z).
  Proof.
    intros z ?. repeat (split; try apply _). intros x ? y ? E1.
    apply (not_lt_apart_lt_flip _ _).
     intros E2. apply (lt_flip _ _ E1).
     now apply (strictly_order_preserving (.* z)).
    apply (strong_extensionality (.* z)).
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
  Proof. intros. apply _. Qed.

  Global Instance: ∀ `{z ∊ R ₀}, RightCancellation (.*.) z R.
  Proof. intros. apply _. Qed.

  Lemma square_pos x `{x ∊ R ₀} : x * x ∊ R₊ .
  Proof. destruct (decompose_nonzero x); apply _. Qed.

  Lemma pos_mult_rev_l x `{x ∊ R} y `{y ∊ R₊} `{x * y ∊ R₊} : x ∊ R₊ .
  Proof. split. apply _. apply (strictly_order_reflecting (.* y) _ _). rewrite_on R -> (mult_0_l y). firstorder. Qed.

  Lemma pos_mult_rev_r x `{x ∊ R₊} y `{y ∊ R} `{x * y ∊ R₊} : y ∊ R₊ .
  Proof. split. apply _. apply (strictly_order_reflecting (x *.) _ _). rewrite_on R -> (mult_0_r x). firstorder. Qed.

  Context `{1 ∊ R ₀}.

  Instance one_pos : 1 ∊ R₊.
  Proof. rewrite_on R <- (mult_1_r 1). exact (square_pos 1). Qed.

  Lemma lt_0_1 : 0 < 1.
  Proof. now destruct (_:1 ∊ R₊). Qed.

  Lemma lt_0_2 : 0 < 2.
  Proof. now destruct (_:2 ∊ R₊). Qed.

  Lemma lt_0_3 : 0 < 3.
  Proof. now destruct (_:3 ∊ R₊). Qed.

  Lemma lt_0_4 : 0 < 4.
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
  Proof. red. subsymmetry. apply (pseudo_order_lt_apart _ _), lt_0_2. Qed.

  Lemma gt_1_mult_compat x `{x ∊ R} y `{y ∊ R} : 1 < x → 1 < y → 1 < x * y.
  Proof.
    intros. assert (x ∊ R₊) by (split; [ apply _ | red; subtransitivity 1; exact lt_0_1 ]).
    now apply (gt_1_mult_lt_compat_r _).
  Qed.

End pseudo_semiring_order.

Hint Extern 5 (StrongRngOps _) => eapply @pseudo_sring_order_strong_rng_ops : typeclass_instances.

Hint Extern 2 (1 ∊ ?R₊) => eapply @one_pos : typeclass_instances.

Hint Extern 7 (PropHolds (2 ≠ 0)) => eapply @apart_0_2 : typeclass_instances.

Hint Extern 5 (2 ∊ ?R ₀) => eapply (pos_nonzero (R:=R)) : typeclass_instances.
Hint Extern 5 (3 ∊ ?R ₀) => eapply (pos_nonzero (R:=R)) : typeclass_instances.
Hint Extern 5 (4 ∊ ?R ₀) => eapply (pos_nonzero (R:=R)) : typeclass_instances.

Section full_pseudo_order.
  Context `{FullPseudoOrder A (S:=R)} `{Zero A} `{!0 ∊ R}.

  Lemma nonneg_not_neg x `{x ∊ R⁺} : ¬ x ∊ R₋ .
  Proof. destruct (_ : x ∊ R⁺) as [? E]. red in E. rewrite (le_iff_not_lt_flip _ _) in E. firstorder. Qed.

  Lemma nonpos_not_pos x `{x ∊ R⁻} : ¬ x ∊ R₊ .
  Proof. destruct (_ : x ∊ R⁻) as [? E]. red in E. rewrite (le_iff_not_lt_flip _ _) in E. firstorder. Qed.

  Lemma neg_not_nonneg x `{x ∊ R₋} : ¬ x ∊ R⁺ .
  Proof. intros [? E]. red in E. rewrite (le_iff_not_lt_flip _ _) in E. firstorder. Qed.

  Lemma pos_not_nonpos x `{x ∊ R₊} : ¬ x ∊ R⁻ .
  Proof. intros [? E]. red in E. rewrite (le_iff_not_lt_flip _ _) in E. firstorder. Qed.

  Lemma not_neg_nonneg x `{x ∊ R} : ¬ x ∊ R₋ → x ∊ R⁺.
  Proof. split. apply _. red. apply (le_iff_not_lt_flip _ _). firstorder. Qed.

  Lemma not_pos_nonpos x `{x ∊ R} : ¬ x ∊ R₊ → x ∊ R⁻.
  Proof. split. apply _. red. apply (le_iff_not_lt_flip _ _). firstorder. Qed.

  Lemma pos_nonneg : Subset R₊ R⁺ .
  Proof. intros x ?. pose proof (Pos_subset). apply (not_neg_nonneg x), (pos_not_neg x). Qed.

  Lemma neg_nonpos : Subset R₋ R⁻ .
  Proof. intros x ?. pose proof (Neg_subset). apply (not_pos_nonpos x), (neg_not_pos x). Qed.

  Lemma nonneg_or_neg `{!DenialInequality R} `{!SubDecision R R (=)} x `{x ∊ R} : x ∊ R⁺ ∨ x ∊ R₋ .
  Proof. destruct (le_or_lt 0 x); [left|right]; firstorder. Qed.

  Lemma pos_or_nonpos `{!DenialInequality R} `{!SubDecision R R (=)} x `{x ∊ R} : x ∊ R₊ ∨ x ∊ R⁻ .
  Proof. destruct (le_or_lt x 0); [right|left]; firstorder. Qed.

  Lemma pos_or_zero `{!DenialInequality R} `{!SubDecision R R (=)} x `{x ∊ R⁺} : x ∊ R₊ ∨ x = 0 .
  Proof. destruct (pos_or_nonpos x); intuition. right. apply (antisymmetry le _ _); firstorder. Qed.

End full_pseudo_order.

Hint Extern 5 (Subset _₊ _⁺) => eapply @pos_nonneg : typeclass_instances.
Hint Extern 5 (Subset _₋ _⁻) => eapply @neg_nonpos : typeclass_instances.

Hint Extern 15 (?x ∊ ?R⁺) => match goal with
  | el : x ∊ R₊  |- _ => eapply (pos_nonneg (R:=R) x el)
end : typeclass_instances.
Hint Extern 15 (?x ∊ ?R⁻) => match goal with
  | el : x ∊ R₋  |- _ => eapply (neg_nonpos (R:=R) x el)
end : typeclass_instances.

Section full_pseudo_semiring_order.
  Context `{FullPseudoSemiRingOrder (R:=R)}.
  Instance: SemiRing R := pseudo_srorder_semiring.

  Global Instance: FullPseudoOrder R.
  Proof. split. apply _. apply full_pseudo_srorder_le_iff_not_lt_flip. Qed.

  Lemma nonneg_nonzero_pos x `{x ∊ R⁺} `{x ∊ R ₀} : x ∊ R₊ .
  Proof. destruct (decompose_nonzero x). trivial. now destruct (nonneg_not_neg x). Qed.

  Lemma nonpos_nonzero_neg x `{x ∊ R⁻} `{x ∊ R ₀} : x ∊ R₋ .
  Proof. destruct (decompose_nonzero x); [| trivial]. now destruct (nonpos_not_pos x). Qed.

  Global Instance: SemiRingOrder R.
  Proof. split. apply _. apply _.
  + intros x ? y ?. rewrite (le_iff_not_lt_flip _ _).
    now apply pseudo_srorder_partial_minus.
  + intros z ?. repeat (split; try apply _); intros x ? y ?;
    rewrite (le_iff_not_lt_flip x y); rewrite (le_iff_not_lt_flip (z+x) (z+y));
    intro E; contradict E.
    apply (strictly_order_reflecting (z+) _ _ E).
    apply (strictly_order_preserving (z+) _ _ E).
  + intros x ? y ?.
    apply (not_neg_nonneg (x*y)). intro.
    destruct (neg_mult_decompose x y) as [[??]|[??]].
    apply (nonneg_not_neg x _).
    apply (nonneg_not_neg y _).
  Qed.

  Lemma not_neg_pos_0 x `{x ∊ R} : ¬ x ∊ R₋ → ¬ x ∊ R₊ → x = 0.
  Proof. intros E1 E2. pose proof not_neg_nonneg x E1. pose proof not_pos_nonpos x E2.
    exact (nonneg_nonpos_0 x).
  Qed.

  Global Instance: ∀ `{z ∊ R₊}, OrderEmbedding R R (z *.).
  Proof. split. pose proof pos_nonneg z _. apply _. now apply full_pseudo_order_reflecting. Qed.

  Global Instance: ∀ `{z ∊ R₊}, OrderEmbedding R R (.* z).
  Proof. split. pose proof pos_nonneg z _. apply _. now apply full_pseudo_order_reflecting. Qed.

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
  Proof. intros. pose proof (NonNeg_subset R). rewrite_on R -> (commutativity (+) z y).
    now apply nonneg_plus_lt_compat_r.
  Qed.

  Lemma pos_plus_le_lt_compat_r x `{x ∊ R} y `{y ∊ R} z `{z ∊ R₊} : x ≤ y → x < y + z.
  Proof. intros. pose proof (Pos_subset R).
    rewrite_on R <-(plus_0_r x). apply (plus_le_lt_compat _ _ _ _); firstorder.
  Qed.

  Lemma pos_plus_le_lt_compat_l x `{x ∊ R} y `{y ∊ R} z `{z ∊ R₊} : x ≤ y → x < z + y.
  Proof. intros. pose proof (Pos_subset R). rewrite_on R -> (commutativity (+) z y).
    now apply pos_plus_le_lt_compat_r.
  Qed.

  Lemma nonneg_pos_plus : Closed (R⁺ ⇀ R₊ ⇀ R₊) (+).
  Proof. intros x ? y ?. split. apply _. apply (nonneg_plus_lt_compat_l _ _ _). firstorder. Qed.

  Lemma pos_nonneg_plus : Closed (R₊ ⇀ R⁺ ⇀ R₊) (+).
  Proof. intros x ? y ?. split. apply _. apply (nonneg_plus_lt_compat_r _ _ _). firstorder. Qed.

  Lemma square_nonneg x `{x ∊ R} : x * x ∊ R⁺ .
  Proof.
    apply (not_neg_nonneg _). intro.
    destruct (neg_mult_decompose x x) as [[??]|[??]];
    apply (pos_not_neg x _).
  Qed.

  Lemma nonneg_mult_rev_l x `{x ∊ R} y `{y ∊ R₊} `{x * y ∊ R⁺} : x ∊ R⁺ .
  Proof. split. apply _. apply (order_reflecting (.* y) _ _). rewrite_on R -> (mult_0_l y). firstorder. Qed.

  Lemma nonneg_mult_rev_r x `{x ∊ R₊} y `{y ∊ R} `{x * y ∊ R⁺} : y ∊ R⁺ .
  Proof. split. apply _. apply (order_reflecting (x *.) _ _). rewrite_on R -> (mult_0_r x). firstorder. Qed.

  Instance one_nonneg : 1 ∊ R⁺.
  Proof. rewrite_on R <- (mult_1_r 1). exact (square_nonneg 1). Qed.

  Lemma le_0_1 : 0 ≤ 1.
  Proof. now destruct (_:1 ∊ R⁺). Qed.

  Lemma le_0_2 : 0 ≤ 2.
  Proof. now destruct (_:2 ∊ R⁺). Qed.

  Lemma le_0_3 : 0 ≤ 3.
  Proof. now destruct (_:3 ∊ R⁺). Qed.

  Lemma le_0_4 : 0 ≤ 4.
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
    intros. assert (x ∊ R⁺) by (split; [ apply _ | red; subtransitivity 1; exact le_0_1 ]).
    now apply (ge_1_mult_le_compat_r _).
  Qed.

  Lemma gt_1_ge_1_mult_compat x `{x ∊ R} y `{y ∊ R} : 1 < x → 1 ≤ y → 1 < x * y.
  Proof.
    intros. assert (x ∊ R⁺) by (split; [ apply _ | red; subtransitivity 1; [ exact le_0_1 | now apply (lt_le _ _) ] ]).
    apply (lt_le_trans _ x _); trivial.
    apply (ge_1_mult_le_compat_r _ _ _); trivial. subreflexivity.
  Qed.

  Lemma ge_1_gt_1_mult_compat x `{x ∊ R} y `{y ∊ R} : 1 ≤ x → 1 < y → 1 < x * y.
  Proof.
    intros. assert (y ∊ R⁺) by (split; [ apply _ | red; subtransitivity 1; [ exact le_0_1 | now apply (lt_le _ _) ] ]).
    apply (lt_le_trans _ y _); trivial.
    apply (ge_1_mult_le_compat_l _ _ _); trivial. subreflexivity.
  Qed.

  Lemma nonneg_pos_is_pos : (R⁺)₊ = R₊ .
  Proof. intro x. split. firstorder. intro. pose proof pos_nonneg x _. firstorder. Qed.

End full_pseudo_semiring_order.

Hint Extern 3 (?x * ?x ∊ _⁺) => eapply @square_nonneg : typeclass_instances.

Hint Extern 4 (_ + _ ∊ _₊) => eapply @nonneg_pos_plus : typeclass_instances. 
Hint Extern 4 (_ + _ ∊ _₊) => eapply @pos_nonneg_plus : typeclass_instances. 

Hint Extern 2 (1 ∊ ?R⁺) => eapply @one_nonneg : typeclass_instances.

Hint Extern 10 (_ ∊ (_⁺)₊) => apply nonneg_pos_is_pos : typeclass_instances.


Section dec_semiring_order.
  (* Maybe these assumptions can be weakened? *)
  Context `{SemiRingOrder A (R:=R)} `{UnEq A} `{!DenialInequality R}
    `{!NoZeroDivisors R} `{!TotalRelation R (≤)} `{!SubDecision R R (=)}.

  Context `{Lt A} (lt_correct : ∀ `{x ∊ R} `{y ∊ R}, x < y ↔ x ≤ y ∧ x ≠ y).

  Instance: FullPseudoOrder R := dec_full_pseudo_order lt_correct.

  Existing Instance srorder_semiring.
  Existing Instance pseudo_order_setoid.
  Existing Instance sg_op_proper.

  Instance dec_pseudo_srorder: PseudoSemiRingOrder R.
  Proof. split. apply _. apply _.
  + intros x ? y ? E. now apply srorder_partial_minus, not_lt_le_flip.
  + intros z ?. repeat (split; try apply _).
    intros x ? y ?. rewrite !(lt_correct _ _ _ _), !(denial_inequality _ _).
    intros [E2a E2b]. split.
      now apply (order_preserving (z+)).
      contradict E2b. now apply (left_cancellation (+) z R).
  + exact (dec_strong_binary_morphism (.*.)).
  + intros x [? Ex] y [? Ey]. split. apply _. red in Ex,Ey. red.
    rewrite lt_correct in Ex, Ey |- *; try apply _. split.
    * assert (x ∊ R⁺) by firstorder; assert (y ∊ R⁺) by firstorder.
      pose proof (_ : x * y ∊ R⁺). firstorder.
    * assert (x ∊ R ₀) by (split; [| red; subsymmetry]; firstorder).
      assert (y ∊ R ₀) by (split; [| red; subsymmetry]; firstorder).
      pose proof (dec_mult_nonzero x _ y _). subsymmetry. firstorder.
  Qed.

  Instance dec_full_pseudo_srorder: FullPseudoSemiRingOrder R.
  Proof.
    split; try apply _.
    now apply le_iff_not_lt_flip.
  Qed.
End dec_semiring_order.

Section another_semiring.
  Context `{SemiRingOrder (R:=R1)}.
  Existing Instance srorder_semiring.

  Lemma projected_srorder `{SemiRing (R:=R2)} `{Le _} (f : R2 ⇀ R1)
      `{!SemiRing_Morphism R2 R1 f} `{!Injective R2 R1 f} :
    (∀ `{x ∊ R2} `{y ∊ R2}, x ≤ y ↔ f x ≤ f y) 
  → (∀ `{x ∊ R2} `{y ∊ R2}, x ≤ y → ∃ `{z ∊ R2}, y = x + z) → SemiRingOrder R2.
  Proof.
    intros P ?. pose proof (projected_partial_order f P).
    split. apply _. apply _. assumption.
    split; (split; [split; apply _ |]); intros; apply (P _ _ _ _).
    + rewrite 2!(R1 $ preserves_plus _ _).
      now apply (order_preserving _ _ _), P.
    + apply (order_reflecting (f z +) _ _).
      rewrite <- 2!(R1 $ preserves_plus _ _).
      now apply (P _ _ _ _).
    + intros x ? y ?.
      cut (f x * f y ∊ R1⁺).
        intros [??]. split. apply _. apply (P _ _ _ _).
        now rewrite_on R1 -> (preserves_mult x y), preserves_0.
      assert (∀ z, z ∊ R2⁺ → f z ∊ R1⁺).
        split. apply _. red. rewrite_on R1 <- preserves_0. apply (P _ _ _ _). firstorder.
      apply _.
   Qed.

  Context `{SemiRingOrder (R:=R2)} (f : R1 ⇀ R2).

  Section preserves_sign.
    Context `{!AdditiveMonoid_Morphism R1 R2 f}.

    Instance preserves_nonneg `{!OrderPreserving R1 R2 f} x `{x ∊ R1⁺} : f x ∊ R2⁺ .
    Proof. split. apply _. red. rewrite_on R2 <- preserves_0. apply (order_preserving f _ _). firstorder. Qed.

    Instance preserves_nonpos `{!OrderPreserving R1 R2 f} x `{x ∊ R1⁻} : f x ∊ R2⁻ .
    Proof. destruct (_:x ∊ R1⁻). split. apply _. red. rewrite_on R2 <- preserves_0. now apply (order_preserving f _ _). Qed.

    Instance reflects_nonneg `{!OrderReflecting R1 R2 f} x `{x ∊ R1} `{f x ∊ R2⁺} : x ∊ R1⁺.
    Proof. split. apply _. red. apply (order_reflecting f _ _). rewrite_on R2 ->preserves_0. firstorder. Qed.

    Instance reflects_nonpos `{!OrderReflecting R1 R2 f} x `{x ∊ R1} `{f x ∊ R2⁻} : x ∊ R1⁻ .
    Proof. split. apply _. red. apply (order_reflecting f _ _). rewrite_on R2 ->preserves_0. firstorder. Qed.

    Lemma embeds_nonneg `{!OrderEmbedding R1 R2 f} x `{x ∊ R1} : x ∊ R1⁺ ↔ f x ∊ R2⁺ .
    Proof. split; intro; apply _. Qed.

    Lemma embeds_nonpos `{!OrderEmbedding R1 R2 f} x `{x ∊ R1} : x ∊ R1⁻ ↔ f x ∊ R2⁻ .
    Proof. split; intro; apply _. Qed.

  End preserves_sign.

  Context `{!SemiRing_Morphism R1 R2 f}.

  Existing Instance closed_range.

  (* If a morphism agrees on the positive cone then it is order preserving *)
  Lemma preserving_preserves_nonneg `{!Closed (R1⁺ ⇀ R2⁺) f} : OrderPreserving R1 R2 f.
  Proof.
    repeat (split; try apply _). intros x ? y ? F.
    destruct (decompose_le F) as [z [? Ez]].
    apply (compose_le _ _ (f z)).
    rewrite_on R1 -> Ez. now rewrite_on R2 -> (preserves_plus x z).
  Qed.

  Lemma preserves_ge_1 `{!OrderPreserving R1 R2 f} x `{x ∊ R1} : 1 ≤ x → 1 ≤ f x.
  Proof. intros. rewrite_on R2 <- preserves_1. now apply (order_preserving f _ _). Qed.

  Lemma preserves_le_1 `{!OrderPreserving R1 R2 f} x `{x ∊ R1} : x ≤ 1 → f x ≤ 1.
  Proof. intros. rewrite_on R2 <- preserves_1. now apply (order_preserving f _ _). Qed.
End another_semiring.

Section another_semiring_strict.
  Context `{StrictSemiRingOrder (R:=R1)}. 
  Existing Instance strict_srorder_semiring.

  Lemma projected_strict_srorder `{SemiRing (R:=R2)} `{Lt _} (f : R2 ⇀ R1)
      `{!SemiRing_Morphism R2 R1 f} :
    (∀ `{x ∊ R2} `{y ∊ R2}, x < y ↔ f x < f y) 
  → (∀ `{x ∊ R2} `{y ∊ R2}, x < y → ∃ `{z ∊ R2}, y = x + z) → StrictSemiRingOrder R2.
  Proof.
    intros P ?. pose proof (projected_strict_order f P).
    split. apply _. apply _. assumption.
    split; (split; [split; apply _ |]); intros; apply (P _ _ _ _).
    + rewrite 2!(R1 $ preserves_plus _ _).
      now apply (strictly_order_preserving _ _ _), P.
    + apply (strictly_order_reflecting (f z +) _ _).
      rewrite <- 2!(R1 $ preserves_plus _ _).
      now apply (P _ _ _ _).
    + intros x ? y ?.
      cut (f x * f y ∊ R1₊).
        intros [??]. split. apply _. apply (P _ _ _ _).
        now rewrite_on R1 -> (preserves_mult x y), preserves_0.
      assert (∀ z, z ∊ R2₊ → f z ∊ R1₊).
        split. apply _. red. rewrite_on R1 <- preserves_0. apply (P _ _ _ _). firstorder.
      apply _.
  Qed.

  Context `{StrictSemiRingOrder (R:=R2)} (f : R1 ⇀ R2).

  Section preserves_sign.
    Context `{!AdditiveMonoid_Morphism R1 R2 f}.

    Instance preserves_pos `{!StrictlyOrderPreserving R1 R2 f} x `{x ∊ R1₊} : f x ∊ R2₊ .
    Proof. split. apply _. red. rewrite_on R2 <- preserves_0. apply (strictly_order_preserving f _ _). firstorder. Qed.

    Instance preserves_neg `{!StrictlyOrderPreserving R1 R2 f} x `{x ∊ R1₋} : f x ∊ R2₋ .
    Proof. destruct (_:x ∊ R1₋). split. apply _. red. rewrite_on R2 <- preserves_0. now apply (strictly_order_preserving f _ _). Qed.

    Instance reflects_pos `{!StrictlyOrderReflecting R1 R2 f} x `{x ∊ R1} `{f x ∊ R2₊} : x ∊ R1₊ .
    Proof. split. apply _. red. apply (strictly_order_reflecting f _ _). rewrite_on R2 ->preserves_0. firstorder. Qed.

    Instance reflects_neg `{!StrictlyOrderReflecting R1 R2 f} x `{x ∊ R1} `{f x ∊ R2₋} : x ∊ R1₋ .
    Proof. split. apply _. red. apply (strictly_order_reflecting f _ _). rewrite_on R2 ->preserves_0. firstorder. Qed.

    Lemma embeds_pos `{!StrictOrderEmbedding R1 R2 f} x `{x ∊ R1} : x ∊ R1₊ ↔ f x ∊ R2₊ .
    Proof. split; intro; apply _. Qed.

    Lemma embeds_neg `{!StrictOrderEmbedding R1 R2 f} x `{x ∊ R1} : x ∊ R1₋ ↔ f x ∊ R2₋ .
    Proof. split; intro; apply _. Qed.

  End preserves_sign.

  Context `{!SemiRing_Morphism R1 R2 f}.

  Existing Instance closed_range.

  Lemma strictly_preserving_preserves_pos `{!Closed (R1₊ ⇀ R2₊) f} : StrictlyOrderPreserving R1 R2 f.
  Proof.
    repeat (split; try apply _). intros x ? y ? F.
    destruct (decompose_lt F) as [z [? Ez]].
    apply (compose_lt _ _ (f z)).
    rewrite_on R1 -> Ez. now rewrite_on R2 -> (preserves_plus x z).
  Qed.

  Lemma preserves_gt_1 `{!StrictlyOrderPreserving R1 R2 f} x `{x ∊ R1} : 1 < x → 1 < f x.
  Proof. intros. rewrite_on R2 <- preserves_1. now apply (strictly_order_preserving f _ _). Qed.

  Lemma preserves_lt_1 `{!StrictlyOrderPreserving R1 R2 f} x `{x ∊ R1} : x < 1 → f x < 1.
  Proof. intros. rewrite_on R2 <- preserves_1. now apply (strictly_order_preserving f _ _). Qed.

End another_semiring_strict.

Ltac preserves_sign_tac lem:= 
  match goal with |- ?f ?x ∊ _ => match type of f with
  | elt_type (_ ⇀ _) => eapply lem
  end end.

Hint Extern 7 (_ ∊ _⁺) => preserves_sign_tac @preserves_nonneg : typeclass_instances.
Hint Extern 7 (_ ∊ _₊) => preserves_sign_tac @preserves_pos : typeclass_instances.
Hint Extern 7 (_ ∊ _⁻) => preserves_sign_tac @preserves_nonpos : typeclass_instances.
Hint Extern 7 (_ ∊ _₋) => preserves_sign_tac @preserves_neg : typeclass_instances.

Section nonneg.

  Section semiringorder.
    Context `{SemiRingOrder (R:=R)}.
    Instance: SemiRing R := srorder_semiring.
  
    Instance nonneg_semirng : SemiRng R⁺.
    Proof.
      repeat match goal with
      | |- Setoid _ => apply _
      | |- mon_unit ∊ R⁺ => eexact (_ : 0 ∊ R⁺)
      | |- Morphism _ (@sg_op _ ?op) =>
           let op := match op with
           | plus_is_sg_op => constr:(plus)
           | mult_is_sg_op => constr:(mult)
           end in change (Morphism (R⁺ ⇒ R⁺ ⇒ R⁺) op);
           apply binary_morphism_proper_back; intros ?? E1 ?? E2; unfold_sigs; red_sig;
           now rewrite_on R -> E1,E2
      | |- _ => split
      | |- _ => rewrite (_:R⁺ ⊆ R); apply _
      end.
    Qed.

    Context `{1 ∊ R⁺}.

    Instance nonneg_semiring : SemiRing R⁺.
    Proof. split; try apply _; rewrite (_:R⁺ ⊆ R); apply _. Qed.

    Instance nonneg_comsemiring `{!CommutativeSemiRing R} : CommutativeSemiRing R⁺.
    Proof. apply comsemiring_from_semiring. rewrite (_:R⁺ ⊆ R). apply _. Qed.

    Instance: PartialOrder R⁺.
    Proof. rewrite (_:R⁺ ⊆ R). apply _. Qed.

    Instance nonneg_semiring_order : SemiRingOrder R⁺.
    Proof. split. apply _. apply _.
    + intros x ? y ? E. exact (decompose_le E).
    + intros z ?. split; (split; [split;apply _|]); intros x ? y ?.
      exact (order_preserving (z+) x y).
      exact (order_reflecting (z+) x y).
    + intros x[??]y[??]. split; apply (_ : x * y ∊ R⁺).
    Qed.
  End semiringorder.

  Existing Instance nonneg_semiring.

  Context `{FullPseudoSemiRingOrder (R:=R)}.
  Instance: SemiRing R := pseudo_srorder_semiring.

  Instance: PseudoOrder R⁺.
  Proof. rewrite (_:R⁺ ⊆ R); apply _. Qed.

  Instance : PseudoSemiRingOrder R⁺.
  Proof. split. apply _. apply _.
  + intros x ? y ? E. exact (decompose_le (not_lt_le_flip _ _ E)).
  + intros z ?. split; (split; [split;apply _|]); intros x ? y ?.
    exact (strictly_order_preserving (z+) x y).
    exact (strictly_order_reflecting (z+) x y).
  + split. apply _. rewrite strong_ext_equiv_2. intros.
    now apply (strong_binary_extensionality (.*.)).
  + assert (Subset (R⁺)₊ R₊) by (rewrite nonneg_pos_is_pos; apply _).
    assert (Subset R₊ (R⁺)₊) by (rewrite nonneg_pos_is_pos; apply _).
    rewrite <-( _ : Subset (R₊ ⇀ R₊ ⇀ R₊) ((R⁺)₊ ⇀ (R⁺)₊ ⇀ (R⁺)₊) ).
    exact  pseudo_srorder_pos_mult_compat.
  Qed.

  Instance nonneg_semiring_full_order : FullPseudoSemiRingOrder R⁺.
  Proof. split. apply _. intros x ? y ?. exact (le_iff_not_lt_flip _ _). Qed.

End nonneg.

Hint Extern 2 (SemiRng _⁺) => eapply @nonneg_semirng : typeclass_instances.
Hint Extern 2 (SemiRing _⁺) => eapply @nonneg_semiring : typeclass_instances.
Hint Extern 2 (CommutativeSemiRing _⁺) => eapply @nonneg_comsemiring : typeclass_instances.
Hint Extern 2 (SemiRingOrder _⁺) => eapply @nonneg_semiring_order : typeclass_instances.
Hint Extern 2 (FullPseudoSemiRingOrder _⁺) => eapply @nonneg_semiring_full_order : typeclass_instances.

Section nonneg_mor.

  Context `{SemiRingOrder (R:=R1)} `{SemiRingOrder (R:=R2)}.
  Context  (f : R1 ⇀ R2).

  Instance: SemiRing R1 := srorder_semiring.
  Instance: SemiRing R2 := srorder_semiring.

  Lemma srng_mor_nonneg_dom `{!SemiRng_Morphism R1 R2 f} : SemiRng_Morphism R1⁺ R2 f .
  Proof. apply semirng_morphism_alt. apply _. apply _.
  + rewrite <-(_ : Subset (R1 ⇒ R2) (R1⁺ ⇒ R2)). apply _.
  + intros ????. exact (preserves_plus _ _).
  + intros ????. exact (preserves_mult _ _).
  + exact preserves_0.
  Qed.

  Lemma srng_mor_nonneg `{!SemiRng_Morphism R1 R2 f} `{!OrderPreserving R1 R2 f}
    : SemiRng_Morphism R1⁺ R2⁺ f .
  Proof. apply semirng_morphism_alt. apply _. apply _.
  + intros ?? E. unfold_sigs. red_sig. now rewrite (_ $ E).
  + intros ????. exact (preserves_plus _ _).
  + intros ????. exact (preserves_mult _ _).
  + exact preserves_0.
  Qed.

  Context `{1 ∊ R1⁺} `{1 ∊ R2⁺}.

  Lemma sring_mor_nonneg_dom `{!SemiRing_Morphism R1 R2 f} : SemiRing_Morphism R1⁺ R2 f .
  Proof. split. apply _. apply _. apply srng_mor_nonneg_dom. exact preserves_1. Qed.

  Lemma sring_mor_nonneg `{!SemiRing_Morphism R1 R2 f} `{!OrderPreserving R1 R2 f}
    : SemiRing_Morphism R1⁺ R2⁺ f.
  Proof. split. apply _. apply _. apply srng_mor_nonneg. exact preserves_1. Qed.
End nonneg_mor.

Hint Extern 9 (SemiRing_Morphism _⁺ _⁺ _) => eapply @sring_mor_nonneg : typeclass_instances.
Hint Extern 9 (SemiRng_Morphism _⁺ _⁺ _) => eapply @srng_mor_nonneg : typeclass_instances.
Hint Extern 10 (SemiRing_Morphism _⁺ _ _) => eapply @sring_mor_nonneg_dom : typeclass_instances.
Hint Extern 10 (SemiRng_Morphism _⁺ _ _) => eapply @srng_mor_nonneg_dom : typeclass_instances.

