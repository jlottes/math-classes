Require Import
  abstract_algebra theory.strong_setoids theory.strong_groups.
Require Export
  theory.rings.

Lemma NonZero_strong_setoid       `{Zero}   `{StrongSetoid _ (S:=R)} : StrongSetoid (R ₀). Proof. now rewrite (_:SubsetOf (R ₀) R). Qed.
Lemma NonNeg_strong_setoid  `{Le} `{Zero _} `{StrongSetoid _ (S:=R)} : StrongSetoid R⁺.    Proof. now rewrite (_:SubsetOf R⁺  R). Qed.
Lemma NonPos_strong_setoid  `{Le} `{Zero _} `{StrongSetoid _ (S:=R)} : StrongSetoid R⁻.    Proof. now rewrite (_:SubsetOf R⁻  R). Qed.
Lemma Pos_strong_setoid     `{Lt} `{Zero _} `{StrongSetoid _ (S:=R)} : StrongSetoid R₊.    Proof. now rewrite (_:SubsetOf R₊  R). Qed.
Lemma Neg_strong_setoid     `{Lt} `{Zero _} `{StrongSetoid _ (S:=R)} : StrongSetoid R₋.    Proof. now rewrite (_:SubsetOf R₋  R). Qed.

Hint Extern 2 (StrongSetoid (_ ₀)) => eapply @NonZero_strong_setoid : typeclass_instances. 
Hint Extern 2 (StrongSetoid _⁺   ) => eapply @NonNeg_strong_setoid  : typeclass_instances. 
Hint Extern 2 (StrongSetoid _₊   ) => eapply @Pos_strong_setoid     : typeclass_instances. 
Hint Extern 2 (StrongSetoid _⁻   ) => eapply @NonPos_strong_setoid  : typeclass_instances. 
Hint Extern 2 (StrongSetoid _₋   ) => eapply @Neg_strong_setoid     : typeclass_instances. 

Lemma strong_rng_ops_proper: Find_Proper_Signature (@StrongRngOps) 0
  (∀ A Aplus Amult Ae Aue, Proper ((=)==>impl) (@StrongRngOps A Aplus Amult Ae Aue)).
Proof. structure_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@StrongRngOps) 0 _) => eexact strong_rng_ops_proper : typeclass_instances.

Instance: ∀ `{StrongRngOps (R:=R)}, StrongSemiGroupOp (op:=plus_is_sg_op) R.
Proof. split. apply _. change (Strong_Binary_Morphism R R R (+)). apply _. Qed.

Instance: ∀ `{StrongRngOps (R:=R)}, StrongSemiGroupOp (op:=mult_is_sg_op) R.
Proof. split. apply _. change (Strong_Binary_Morphism R R R (.*.)). apply _. Qed.

Section semirngs.
  Context `{SemiRng (R:=R)} {Aue:UnEq _} `{!StrongRngOps R}.

  Global Instance: NonZeroProduct R.
  Proof. intros x ? y ? ?. split; (split; [apply _|]); [
      apply (strong_extensionality (.* y)); rewrite_on R -> (mult_0_l y)
    | apply (strong_extensionality (x *.)); rewrite_on R -> (mult_0_r x) ];
    firstorder.
  Qed.

End semirngs.

Section rngs.
  Context `{Rng (R:=R)} {Aue:UnEq _} `{!StrongRngOps R}.

  Instance rng_negate_strong_mor: Strong_Morphism R R (-) := _ : Strong_Morphism R R (@inv _ negate_is_inv).
  Instance rng_negate_strong_inj: StrongInjective R R (-) := _ : StrongInjective R R (@inv _ negate_is_inv).
  Instance rng_plus_strong_left_cancel z `{z ∊ R} : StrongLeftCancellation (+) z R
    := _ : StrongLeftCancellation (&) z R.
  Instance rng_plus_strong_right_cancel z `{z ∊ R} : StrongRightCancellation (+) z R
    := _ : StrongRightCancellation (&) z R.

  Lemma mult_apart_zero_l x `{x ∊ R} y `{y ∊ R} : x * y ∊ R ₀ → x ∊ R ₀.
  Proof. intro. apply (nonzero_product x y). Qed.

  Lemma mult_apart_zero_r x `{x ∊ R} y `{y ∊ R} : x * y ∊ R ₀ → y ∊ R ₀.
  Proof. intro. apply (nonzero_product x y). Qed.

  Lemma negate_nonzero x `{x ∊ R ₀} : -x ∊ R ₀.
  Proof. split. apply _. rewrite <- (R $ negate_0). apply (strong_injective (-) _ _). firstorder. Qed.

End rngs.

Hint Extern 5 (Strong_Morphism _ _ (-)) => class_apply @rng_negate_strong_mor : typeclass_instances.
Hint Extern 5 (StrongInjective _ _ (-)) => class_apply @rng_negate_strong_inj : typeclass_instances.
Hint Extern 5 (StrongLeftCancellation  (+) _ _) => class_apply @rng_plus_strong_left_cancel  : typeclass_instances.
Hint Extern 5 (StrongRightCancellation (+) _ _) => class_apply @rng_plus_strong_right_cancel : typeclass_instances.
Hint Extern 5 (-_ ∊ _ ₀) => class_apply @negate_nonzero : typeclass_instances.

Section rings.
  Context `{Ring (R:=R)} {Aue:UnEq _} `{!StrongRngOps R}.

  Notation U := RingUnits.

  Lemma RingUnit_strong_left_cancel z `{z ∊ U R} : StrongLeftCancellation (.*.) z R.
  Proof. intros x ? y ? E. destruct (_ : z ∊ U R) as [?[zi[? [E1 E2]]]].
    apply (strong_extensionality (zi *.)).
    now rewrite 2!(R $ associativity (.*.) _ _ _), (R $ E2), 2!(R $ mult_1_l _).
  Qed.

  Lemma RingUnit_strong_right_cancel z `{z ∊ U R} : StrongRightCancellation (.*.) z R.
  Proof. intros x ? y ? E. destruct (_ : z ∊ U R) as [?[zi[? [E1 E2]]]].
    apply (strong_extensionality (.* zi)).
    now rewrite <- 2!(R $ associativity (.*.) _ _ _), (R $ E1), 2!(R $ mult_1_r _).
  Qed.
End rings.

Section morphisms_semirngs.
  Context `{SemiRng A (R:=R1)} {Aue:UnEq A} `{!StrongRngOps R1}
          `{SemiRng B (R:=R2)} {Bue:UnEq B} `{!StrongRngOps R2}
           {f:R1 ⇀ R2} `{!SemiRng_Morphism R1 R2 f}.

  Lemma strong_injective_nonzero `{inj:!StrongInjective R1 R2 f} :
    Strong_Morphism (R1 ₀) (R2 ₀) f.
  Proof. split; try apply _.
  + intros x [? E]. split. apply _. red. rewrite_on R2 <- preserves_0.
    exact (strong_injective _ _ _ E).
  + intros x ? y ? E. destruct inj. now apply (strong_extensionality f).
  Qed.
End morphisms_semirngs.

Hint Extern 10 (Strong_Morphism _ (_ ₀) _) => class_apply @strong_injective_nonzero : typeclass_instances.

Section morphisms_rngs.
  Context `{Rng A (R:=R1)} {Aue:UnEq A} `{!StrongRngOps R1}
          `{Rng B (R:=R2)} {Bue:UnEq B} `{!StrongRngOps R2}
           {f:R1 ⇀ R2} `{!Rng_Morphism R1 R2 f}.

  Lemma strong_injective_preserves_0 `{!Strong_Morphism R1 R2 f} :
    (∀ `{x ∊ R1 ₀}, f x ∊ R2 ₀) → StrongInjective R1 R2 f.
  Proof. intros E1. split; try apply _. intros x ? y ? E2.
    apply (strong_extensionality (+ -f y)).
    rewrite (R2 $ plus_negate_r _).
    rewrite_on R2 <- (preserves_minus x y).
    assert (x - y ∊ R1 ₀). split. apply _.
      apply (strong_extensionality (+ y)).
      now rewrite (R1 $ plus_plus_negate_l _ _), (R1 $ plus_0_l _).
    now destruct (_ : f (x-y) ∊ R2 ₀).
  Qed.

End morphisms_rngs.
