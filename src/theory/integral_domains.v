Require Import
  abstract_algebra theory.strong_setoids theory.strong_groups.
Require Export
  theory.strong_rings.

Lemma intdomain_proper: Find_Proper_Signature (@IntegralDomain) 0
  (∀ A Aplus Amult Azero Aone Anegate Ae Aue,
   Proper ((=)==>impl) (@IntegralDomain A Aplus Amult Azero Aone Anegate Ae Aue)).
Proof with try apply _. red. intros. intros S T E. destruct 1. split...
  rewrite <- E... rewrite <- E... rewrite <- E...
  intros ? el ? el2. rewrite <- E in el, el2 |- *...
  now apply intdom_nozeroes.
Qed.
Hint Extern 0 (Find_Proper_Signature (@IntegralDomain) 0 _) => eexact intdomain_proper : typeclass_instances.

Section contents.
  Context `{IntegralDomain (D:=D)}.

  Instance intdom_strong_mult_sg: StrongSemiGroupOp (op:=mult_is_sg_op) (D ₀).
  Proof. split. apply _. split. exact intdom_nozeroes. rewrite strong_ext_equiv_2.
    intros x₁ ? x₂ ? y₁ ? y₂ ?. exact (strong_binary_extensionality (.*.)).
  Qed.

  Instance intdom_strong_mult_nonzero: Strong_Binary_Morphism (D ₀) (D ₀) (D ₀) (.*.).
  Proof. change (Strong_Binary_Morphism (D ₀) (D ₀) (D ₀) (@sg_op _ mult_is_sg_op)). apply _. Qed.

  Instance intdom_strong_left_cancel z `{z ∊ D ₀} : StrongLeftCancellation (.*.) z D.
  Proof. intros x ? y ? E.
    assert (x-y ∊ D ₀). split. apply _.
      rewrite <- (D $ plus_negate_r y).
      exact (strong_right_cancellation (+) (-y) D _ _ E).
    apply (strong_extensionality (+ -(z*y))). rewrite (D $ plus_negate_r _).
    rewrite <- (D $ mult_minus_distr_l _ _ _).
    now destruct (_ : z * (x - y) ∊ D ₀).
  Qed.

  Instance intdom_strong_right_cancel z `{z ∊ D ₀} : StrongRightCancellation (.*.) z D.
  Proof strong_right_cancel_from_left.

  Global Instance intdom_nozerodivs: NoZeroDivisors D.
  Proof. intros x Z. destruct Z as [? [y [? [E|E]]]];
    rewrite <- (tight_apart _ _) in E; destruct E;
    match goal with |- ?a * ?b ≠ 0 => now destruct (_ : a * b ∊ D ₀) end.
  Qed.
End contents.

Hint Extern 5 (StrongSemiGroupOp (_ ₀)) => class_apply @intdom_strong_mult_sg : typeclass_instances.
Hint Extern 5 (Strong_Binary_Morphism (_ ₀) (_ ₀) (_ ₀) (.*.)) => class_apply @intdom_strong_mult_nonzero : typeclass_instances.
Hint Extern 5 (StrongLeftCancellation  (.*.) _ _) => class_apply @intdom_strong_left_cancel  : typeclass_instances.
Hint Extern 5 (StrongRightCancellation (.*.) _ _) => class_apply @intdom_strong_right_cancel : typeclass_instances.

Lemma dec_intdom `{CommutativeRing A (R:=R)} `{UnEq A} `{!StandardUnEq R}
  `{1 ∊ R ₀} `{!NoZeroDivisors R} `{!SubDecision R R (=)}
  : IntegralDomain R.
Proof. pose proof dec_strong_setoid. split; try apply _. split; try apply _.
  exact (dec_strong_binary_morphism (+)).
  exact (dec_strong_binary_morphism (.*.)).
Qed.

Lemma dec_intdom_zero_product `{IntegralDomain (D:=D)} `{!StandardUnEq D} `{!SubDecision D D (=)}
  : ZeroProduct D.
Proof. intros x ? y ? E. destruct (decide_sub (=) x 0) as [Ex|Ex]. now left. right.
  rewrite <-(tight_apart _ _) in E.
  rewrite <-(tight_apart _ _). contradict E.
  rewrite <-(standard_uneq _ _) in Ex.
  assert (x ∊ D ₀) by firstorder.
  assert (y ∊ D ₀) by firstorder.
  now destruct (_ : x * y ∊ D ₀).
Qed.

Hint Extern 10 (ZeroProduct _) => eapply @dec_intdom_zero_product : typeclass_instances.
