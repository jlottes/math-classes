Require Import
  abstract_algebra theory.subsetoids theory.common_props theory.groups.

Section plus.
  Context {A Ae} {Aplus: Plus A} {Azero: Zero A} {R:Subset A}
         `{@CommutativeMonoid A Ae plus_is_sg_op zero_is_mon_unit R}.

  Lemma plus_closed `{x ∊ R} `{y ∊ R} : x + y ∊ R. Proof _.

  Lemma plus_0_l: LeftIdentity (+) 0 R. Proof _.
  Lemma plus_0_r: RightIdentity (+) 0 R. Proof _.
End plus.
Arguments plus_0_l {A Ae Aplus Azero R _} _ {_}.
Arguments plus_0_r {A Ae Aplus Azero R _} _ {_}.

Hint Extern 0 (@Element _ _ (@plus _ _ _ _)) => eapply @plus_closed : typeclass_instances. 

Lemma plus_proper: Find_Proper_Signature (@plus) 0
  (∀ A Ae (Aplus:Plus A) (Azero:Zero A) R
     `{@CommutativeMonoid A Ae plus_is_sg_op zero_is_mon_unit  R},
   Proper ((R,=)==>(R,=)==>(R,=)) (+)).
Proof. intro. intros. apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@plus) 0 _) => eexact plus_proper : typeclass_instances.

Lemma mult_proper: Find_Proper_Signature (@mult) 0
  (∀ A Ae (Amult:Mult A) R `{@SemiGroup A Ae mult_is_sg_op R},
   Proper ((R,=)==>(R,=)==>(R,=)) (.*.)).
Proof. intro. intros. apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@mult) 0 _) => eexact mult_proper : typeclass_instances.

Lemma mult_closed {A Ae R} {Amult:Mult A} `{@SemiGroup A Ae mult_is_sg_op R}
  `{x ∊ R} `{y ∊ R} : x * y ∊ R.
Proof _.
Hint Extern 0 (@Element _ _ (@mult _ _ _ _)) => eapply @mult_closed : typeclass_instances. 

Lemma semirng_proper: Find_Proper_Signature (@SemiRng) 0
  (∀ A Ae Aplus Amult Azero, Proper ((=)==>impl) (@SemiRng A Ae Aplus Amult Azero)).
Proof. structure_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@SemiRng) 0 _) => eexact semirng_proper : typeclass_instances.

Lemma semiring_proper: Find_Proper_Signature (@SemiRing) 0
  (∀ A Ae Aplus Amult Azero Aone, Proper ((=)==>impl) (@SemiRing A Ae Aplus Amult Azero Aone)).
Proof. structure_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@SemiRing) 0 _) => eexact semiring_proper : typeclass_instances.

Instance semiring_mult_monoid `{SemiRing (R:=R)}
  : @Monoid _ _ mult_is_sg_op one_is_mon_unit R := {}.


Lemma negate_closed A Ae (Aplus:Plus A) (Azero:Zero A) (Anegate:Negate A) {R}
     `{@AbGroup A Ae plus_is_sg_op zero_is_mon_unit negate_is_inv R}
  `{x ∊ R} : -x ∊ R.
Proof _.
Hint Extern 0 (@Element _ _ (@negate _ _ _)) => eapply @negate_closed : typeclass_instances. 

Lemma negate_proper: Find_Proper_Signature (@negate) 0
  (∀ A Ae (Aplus:Plus A) (Azero:Zero A) (Anegate:Negate A) R
     `{@AbGroup A Ae plus_is_sg_op zero_is_mon_unit negate_is_inv R},
   Proper ((R,=)==>(R,=)) (-)).
Proof. intro. intros. apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@negate) 0 _) => eexact negate_proper : typeclass_instances.


Lemma rng_proper: Find_Proper_Signature (@Rng) 0
  (∀ A Ae Aplus Amult Azero Anegate,
   Proper ((=)==>impl) (@Rng A Ae Aplus Amult Azero Anegate)).
Proof. structure_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@Rng) 0 _) => eexact rng_proper : typeclass_instances.

Lemma ring_proper: Find_Proper_Signature (@Ring) 0
  (∀ A Ae Aplus Amult Azero Aone Anegate,
   Proper ((=)==>impl) (@Ring A Ae Aplus Amult Azero Aone Anegate)).
Proof. structure_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@Ring) 0 _) => eexact ring_proper : typeclass_instances.

Instance ring_is_rng `{Ring (R:=R)} : Rng R := {}.

Lemma comring_proper: Find_Proper_Signature (@CommutativeRing) 0
  (∀ A Ae Aplus Amult Azero Aone Anegate,
   Proper ((=)==>impl) (@CommutativeRing A Ae Aplus Amult Azero Aone Anegate)).
Proof. structure_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@CommutativeRing) 0 _) => eexact comring_proper : typeclass_instances.

Instance comring_is_ring `{CommutativeRing (R:=R)} : Ring R.
Proof. split; try apply _.
  intros x ? y ? z ?.
  rewrite (commutativity (x+y) z).
  rewrite_on R -> (commutativity x z).
  rewrite_on R -> (commutativity y z).
  exact (distribute_l z x y).
Qed.

Lemma intdomain_proper: Find_Proper_Signature (@IntegralDomain) 0
  (∀ A Ae Aplus Amult Azero Aone Anegate,
   Proper ((=)==>impl) (@IntegralDomain A Ae Aplus Amult Azero Aone Anegate)).
Proof. intro. intros. intros S T E [???]. split; try apply _; rewrite <- E; apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@IntegralDomain) 0 _) => eexact intdomain_proper : typeclass_instances.

Lemma rng_is_ring `{Rng (A:=A) (R:=R)} {Aone: One A} `{!1 ∊ R} :
    LeftIdentity (.*.) 1 R → RightIdentity (.*.) 1 R → Ring R.
Proof. intros ??. repeat (split; try apply _). Qed.
Arguments rng_is_ring {A Ae Aplus Amult Azero Anegate} R {_} Aone {_} _ _.

Section rng_props.
  Context `{Rng (R:=R)}.

  Global Instance rng_left_absorb : LeftAbsorb (.*.) 0 R.
  Proof. intros y ?. apply (right_cancellation (+) (0*y) R); try apply _.
    rewrite <-(distribute_r 0 0 y).
    rewrite_on R ->(plus_0_r 0).
    now rewrite (plus_0_l (0*y)).
  Qed.

  Global Instance rng_right_absorb : RightAbsorb (.*.) 0 R.
  Proof. intros y ?. apply (left_cancellation (+) (y*0) R); try apply _.
    rewrite <-(distribute_l y 0 0).
    rewrite_on R ->(plus_0_l 0).
    now rewrite (plus_0_r (y*0)).
  Qed.

  Global Instance rng_is_semirng : SemiRng R := {}.

  Definition negate_involutive x `{!x ∊ R} : - - x = x := inverse_involutive x _.
  Lemma plus_negate_r x `{!x ∊ R} : x + -x = 0. Proof right_inverse x.
  Lemma plus_negate_l x `{!x ∊ R} : -x + x = 0. Proof left_inverse x.
  Lemma negate_swap_r x `{!x ∊ R} y `{!y ∊ R} : x - y = -(y - x).
  Proof. rewrite inv_sg_op_distr; try apply _. rewrite_on R ->(negate_involutive x). reflexivity. Qed.
  Lemma negate_swap_l x `{!x ∊ R} y `{!y ∊ R} : -x + y = -(x - y).
  Proof. rewrite abgroup_inv_distr; try apply _. rewrite_on R ->(negate_involutive y). reflexivity. Qed.
  Lemma negate_plus_distr x `{!x ∊ R} y `{!y ∊ R} : -(x + y) = -x + -y. Proof abgroup_inv_distr x y.

  Lemma negate_mult_distr_l x `{!x ∊ R} y `{!y ∊ R} : -(x * y) = -x * y.
  Proof. apply (left_cancellation (+) (x*y) R); try apply _.
    rewrite (plus_negate_r (x*y)). rewrite <-(distribute_r x (-x) y).
    rewrite_on R ->(plus_negate_r x). now rewrite (left_absorb y).
  Qed.

  Lemma negate_mult_distr_r x `{!x ∊ R} y `{!y ∊ R} : -(x * y) = x * -y.
  Proof. apply (left_cancellation (+) (x*y) R); try apply _.
    rewrite (plus_negate_r (x*y)). rewrite <-(distribute_l x y (-y)).
    rewrite_on R ->(plus_negate_r y). now rewrite (right_absorb x).
  Qed.

  Lemma negate_mult_negate x `{!x ∊ R} y `{!y ∊ R} : -x * -y = x * y.
  Proof. rewrite <-(negate_mult_distr_l x (-y)).
    rewrite_on R <-(negate_mult_distr_r x y).
    now rewrite (negate_involutive (x*y)).
  Qed.

  Lemma negate_0: -0 = 0. Proof inv_mon_unit.

  Lemma mult_minus_distr_l x `{!x ∊ R} y `{!y ∊ R} z `{!z ∊ R} : x * (y - z) = x*y - x*z.
  Proof. rewrite_on R ->(negate_mult_distr_r x z). exact (distribute_l x y (-z)). Qed.

  Lemma mult_minus_distr_r x `{!x ∊ R} y `{!y ∊ R} z `{!z ∊ R} : (x - y) * z = x*z - y*z.
  Proof. rewrite_on R ->(negate_mult_distr_l y z). exact (distribute_r x (-y) z). Qed.


  Lemma equal_by_zero_sum x `{!x ∊ R} y `{!y ∊ R} : x - y = 0 ↔ x = y.
  Proof.
    split; intros E.
     rewrite <- (plus_0_l y). rewrite_on R <- E.
     rewrite <-(associativity x (-y) y). rewrite_on R ->(plus_negate_l y).
     now rewrite (plus_0_r x).
    rewrite_on R ->E. exact (plus_negate_r y).
  Qed.

  Lemma flip_negate x `{!x ∊ R} y `{!y ∊ R} : -x = y ↔ x = -y.
  Proof. split; intros E. rewrite_on R <-E. now rewrite involutive.
                          rewrite_on R ->E. now rewrite involutive. Qed.

  Lemma flip_negate_0 x `{!x ∊ R} : -x = 0 ↔ x = 0.
  Proof. now rewrite (flip_negate x 0), negate_0. Qed.

  Lemma flip_negate_ne_0 x `{!x ∊ R} : -x ≠ 0 ↔ x ≠ 0.
  Proof. split; intros E ?; apply E; now apply flip_negate_0. Qed.

  Lemma negate_zero_prod_l x `{!x ∊ R} y `{!y ∊ R} : -x * y = 0 ↔ x * y = 0.
  Proof.
    split; intros E.
     apply (injective (-) (x*y) 0). now rewrite negate_mult_distr_l, negate_0.
    apply (injective (-) (-x * y) 0). rewrite (negate_mult_distr_l (- x) y), negate_0.
    now rewrite_on R ->(negate_involutive x).
  Qed.

  Lemma negate_zero_prod_r x `{!x ∊ R} y `{!y ∊ R} : x * -y = 0 ↔ x * y = 0.
  Proof.
    split; intros E.
     apply (injective (-) (x*y) 0). now rewrite negate_mult_distr_r, negate_0.
    apply (injective (-) (x * -y) 0). rewrite (negate_mult_distr_r x (- y)), negate_0.
    now rewrite_on R ->(negate_involutive y).
  Qed.


End rng_props.

Global Instance ring_is_semiring `{Ring (R:=R)} : SemiRing R := {}.

Section ring_props.
  Context `{Ring (R:=R)}.
  Lemma negate_mult x `{!x ∊ R} : -x = -1 * x.
  Proof. rewrite <-(negate_mult_distr_l 1 x). now rewrite_on R ->(mult_1_l x). Qed.
End ring_props.

Lemma NonZero_subsetoid `{Equiv A} `{Zero A} R `{!SubSetoid R} : SubSetoid (R ₀).
Proof. split; try apply _. intros ?? E [??]. split; now rewrite <-E. Qed.
Hint Extern 0 (@SubSetoid _ ?Ae (@NonZero _ ?Ae _ _)) => eapply @NonZero_subsetoid : typeclass_instances. 

Existing Instance NonZero_subset.

Lemma ZeroDivisor_proper2: Find_Proper_Signature (@ZeroDivisor) 1
  (∀ A Ae Azero Amult R `{!@SemiGroup A Ae mult_is_sg_op R},
   Proper ((=)==>impl) (@ZeroDivisor A Ae Azero Amult R)).
Proof. intro. intros. intros x x' E [?[y[? Z]]].
  assert (x' ∊ R ₀) by now rewrite <-E. split. easy. exists y.
  split. apply _. destruct Z; [ left | right ]; now rewrite_on R <-E.
Qed.
Hint Extern 0 (Find_Proper_Signature (@ZeroDivisor) 1 _) => eexact ZeroDivisor_proper2 : typeclass_instances.

Instance mult_nonzero `{Rng (R:=R)} `{!NoZeroDivisors R} : Closed (R ₀ ==> R ₀ ==> R ₀) (.*.).
Proof. intros x ? y ?. split. apply _.
  pose proof (no_zero_divisors x) as nzd. mc_contradict nzd.
  split. apply _. exists y. split. apply _. now left.
Qed.
Hint Extern 0 (?x * ?y ∊ ?R ₀) => eapply @mult_nonzero : typeclass_instances.
  
Section cancellation.
  Context `{Rng (R:=R)} `{!NoZeroDivisors R} `{∀ x y, Stable (x = y)}.

  Global Instance mult_left_cancellation z `{!z ∊ R ₀} : LeftCancellation (.*.) z R.
  Proof. intros x ? y ? E.
    rewrite <-(equal_by_zero_sum (z*x) (z*y)) in E.
    rewrite <-(mult_minus_distr_l z x y) in E.
    pose proof (no_zero_divisors z) as nzd.
    apply stable. unfold DN. contradict nzd.
    split. apply _. exists (x-y). intuition. split. apply _.
    now rewrite (equal_by_zero_sum x y).
  Qed.

  Global Instance mult_right_cancellation z `{!z ∊ R ₀} : RightCancellation (.*.) z R.
  Proof. intros x ? y ? E.
    rewrite <-(equal_by_zero_sum (x*z) (y*z)) in E.
    rewrite <-(mult_minus_distr_r x y z) in E.
    pose proof (no_zero_divisors z) as nzd.
    apply stable. unfold DN. contradict nzd.
    split. apply _. exists (x-y). intuition. split. apply _.
    now rewrite (equal_by_zero_sum x y).
  Qed.

End cancellation.

Local Notation U := RingUnits.

Lemma RingUnits_subsetoid {A Ae} `{Mult A} `{One A} R 
  `{!@SemiGroup A Ae mult_is_sg_op R} : SubSetoid (U R).
Proof. split; try apply _. intros ? x' E [?[y[?[??]]]].
  assert (x' ∊ R) by now rewrite <-E.
  split. assumption. exists y. split. assumption. split; now rewrite_on R <-E.
Qed.
Hint Extern 0 (@SubSetoid _ ?Ae (@RingUnits _ ?Ae _ _ _)) => eapply @RingUnits_subsetoid : typeclass_instances.

Lemma RingUnit_not_zero_divisor `{Ring (R:=R)} x {ru:x ∊ U R} : ¬ZeroDivisor R x.
Proof. destruct ru as [?[y[? [E1 E2]]]]. intros [[??][z[[? zn0][E|E]]]]; mc_contradict zn0.
+ rewrite <- (mult_1_l z).
  rewrite_on R <- E2.
  rewrite <- (associativity y x z).
  rewrite_on R -> E. apply (right_absorb y).
+ rewrite <- (mult_1_r z).
  rewrite_on R <- E1.
  rewrite -> (associativity z x y).
  rewrite_on R -> E. apply (left_absorb y).
Qed.

Lemma semirng_morphism_proper: Find_Proper_Signature (@SemiRng_Morphism) 0
  (∀ A Ae B Be Aplus Amult Azero Bplus Bmult Bzero f,
    Proper ((=) ==> (=) ==> impl)
   (@SemiRng_Morphism A Ae B Be Aplus Amult Azero Bplus Bmult Bzero f)).
Proof. structure_mor_proper ltac:(pose proof srngmor_a) ltac:(pose proof srngmor_b).
  rewrite <-ES, <-ET. apply _.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SemiRng_Morphism) 0 _) => eexact semirng_morphism_proper : typeclass_instances.

Lemma semiring_morphism_proper: Find_Proper_Signature (@SemiRing_Morphism) 0
  (∀ A Ae B Be Aplus Amult Azero Aone Bplus Bmult Bzero Bone f,
    Proper ((=) ==> (=) ==> impl)
   (@SemiRing_Morphism A Ae B Be Aplus Amult Azero Aone Bplus Bmult Bzero Bone f)).
Proof. structure_mor_proper ltac:(pose proof sringmor_a) ltac:(pose proof sringmor_b).
  apply preserves_1.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SemiRing_Morphism) 0 _) => eexact semiring_morphism_proper : typeclass_instances.

Lemma rng_morphism_proper: Find_Proper_Signature (@Rng_Morphism) 0
  (∀ A Ae B Be Aplus Amult Azero Anegate Bplus Bmult Bzero Bnegate f,
    Proper ((=) ==> (=) ==> impl)
   (@Rng_Morphism A Ae B Be Aplus Amult Azero Anegate Bplus Bmult Bzero Bnegate f)).
Proof. structure_mor_proper ltac:(pose proof rngmor_a) ltac:(pose proof rngmor_b).
  rewrite <-ES, <-ET. apply _.
Qed.
Hint Extern 0 (Find_Proper_Signature (@Rng_Morphism) 0 _) => eexact rng_morphism_proper : typeclass_instances.

Lemma ring_morphism_proper: Find_Proper_Signature (@Ring_Morphism) 0
  (∀ A Ae B Be Aplus Amult Azero Aone Anegate Bplus Bmult Bzero Bone Bnegate f,
    Proper ((=) ==> (=) ==> impl)
   (@Ring_Morphism A Ae B Be Aplus Amult Azero Aone Anegate Bplus Bmult Bzero Bone Bnegate f)).
Proof. structure_mor_proper ltac:(pose proof ringmor_a) ltac:(pose proof ringmor_b).
  destruct ringmor_image_has_1 as [x [el ?]]. exists x. rewrite ES in el. exists el. assumption.
Qed.
Hint Extern 0 (Find_Proper_Signature (@Ring_Morphism) 0 _) => eexact ring_morphism_proper : typeclass_instances.

Instance rng_morphism_is_srng_morphism `{Rng_Morphism (f:=f) (R:=R) (S:=R')}
  : SemiRng_Morphism f R R'.
Proof. pose proof rngmor_a. pose proof rngmor_b. split; apply _. Qed.


Section semirng_morphisms.
  Context `{SemiRng_Morphism (f:=f) (R:=R) (S:=R')}.

  Existing Instance srngmor_a.
  Existing Instance srngmor_b.

  Lemma preserves_plus x `{!x ∊ R} y `{!y ∊ R} : f (x+y) = f x + f y. Proof preserves_sg_op x y.
  Lemma preserves_mult x `{!x ∊ R} y `{!y ∊ R} : f (x*y) = f x * f y. Proof preserves_sg_op x y.
  Lemma preserves_0: f 0 = 0. Proof preserves_mon_unit.

End semirng_morphisms.

Section rng_morphisms.
  Context `{Rng_Morphism (f:=f) (R:=R) (S:=R')}.

  Existing Instance rngmor_a.
  Existing Instance rngmor_b.

  Lemma preserves_negate x `{!x ∊ R} : f (-x) = - f x. Proof preserves_inverse x.
End rng_morphisms.

Instance ring_morphism_is_sring_morphism `{Ring_Morphism (f:=f) (R:=R) (S:=R')}
  : SemiRing_Morphism f R R'.
Proof. pose proof ringmor_a. pose proof ringmor_b. split; try apply _.
  rewrite <- (mult_1_r (f 1)).
  destruct ringmor_image_has_1 as [x [? E]].
  rewrite_on R' <- E. rewrite <- (preserves_mult 1 x).
  now rewrite_on R -> (mult_1_l x).
Qed.


