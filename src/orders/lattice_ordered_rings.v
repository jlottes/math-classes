Require Import
  abstract_algebra interfaces.orders theory.strong_setoids theory.common_props theory.rings
  theory.lattices orders.rings orders.lattices.

Lemma meet_nonneg `{MeetSemiLatticeOrder (L:=L)} `{Zero _} `{0 ∊ L}
  x `{x ∊ L⁺} y `{y ∊ L⁺} : x ⊓ y ∊ L⁺ .
Proof. split. apply _. apply (meet_glb _ _ _); firstorder. Qed.
Hint Extern 5 (_ ⊓ _ ∊ _⁺) => eapply @meet_nonneg : typeclass_instances.

Lemma join_nonpos `{JoinSemiLatticeOrder (L:=L)} `{Zero _} `{0 ∊ L}
  x `{x ∊ L⁻} y `{y ∊ L⁻} : x ⊔ y ∊ L⁻ .
Proof. split. apply _. apply (join_lub _ _ _); firstorder. Qed.
Hint Extern 5 (_ ⊔ _ ∊ _⁻) => eapply @join_nonpos : typeclass_instances.

Lemma join_nonneg_l `{JoinSemiLatticeOrder (L:=L)} `{Zero _} `{0 ∊ L}
  x `{x ∊ L⁺} y `{y ∊ L} : x ⊔ y ∊ L⁺ .
Proof. split. apply _. red. subtransitivity x. firstorder. lattice_order_tac. Qed.

Lemma join_nonneg_r `{JoinSemiLatticeOrder (L:=L)} `{Zero _} `{0 ∊ L}
  x `{x ∊ L} y `{y ∊ L⁺} : x ⊔ y ∊ L⁺ .
Proof. split. apply _. red. subtransitivity y. firstorder. lattice_order_tac. Qed.

Hint Extern 5 (_ ⊔ _ ∊ _⁺) => eapply @join_nonneg_l : typeclass_instances.
Hint Extern 5 (_ ⊔ _ ∊ _⁺) => eapply @join_nonneg_r : typeclass_instances.

Lemma meet_nonpos_l `{MeetSemiLatticeOrder (L:=L)} `{Zero _} `{0 ∊ L}
  x `{x ∊ L⁻} y `{y ∊ L} : x ⊓ y ∊ L⁻ .
Proof. split. apply _. red. subtransitivity x. lattice_order_tac. firstorder. Qed.

Lemma meet_nonpos_r `{MeetSemiLatticeOrder (L:=L)} `{Zero _} `{0 ∊ L}
  x `{x ∊ L} y `{y ∊ L⁻} : x ⊓ y ∊ L⁻ .
Proof. split. apply _. red. subtransitivity y. lattice_order_tac. firstorder. Qed.

Hint Extern 5 (_ ⊓ _ ∊ _⁻) => eapply @meet_nonpos_l : typeclass_instances.
Hint Extern 5 (_ ⊓ _ ∊ _⁻) => eapply @meet_nonpos_r : typeclass_instances.

Lemma join_0_nonneg `{JoinSemiLatticeOrder (L:=L)} `{Zero _} `{0 ∊ L}
  x `{el: x ∊ L⁺} : 0 ⊔ x = x.
Proof. apply (join_r _ _). now apply el. Qed.

Lemma join_0_nonpos `{JoinSemiLatticeOrder (L:=L)} `{Zero _} `{0 ∊ L}
  x `{el: x ∊ L⁻} : 0 ⊔ x = 0.
Proof. apply (join_l _ _). now apply el. Qed.


Lemma meet_pos `{FullMeetSemiLatticeOrder (L:=L)} `{Zero _} `{0 ∊ L}
  x `{x ∊ L₊} y `{y ∊ L₊} : x ⊓ y ∊ L₊ .
Proof. split. apply _. apply (meet_lt _ _ _); firstorder. Qed.
Hint Extern 5 (_ ⊓ _ ∊ _₊) => eapply @meet_pos : typeclass_instances.

Lemma join_neg `{FullJoinSemiLatticeOrder (L:=L)} `{Zero _} `{0 ∊ L}
  x `{x ∊ L₋} y `{y ∊ L₋} : x ⊔ y ∊ L₋ .
Proof. split. apply _. apply (join_lt _ _ _); firstorder. Qed.
Hint Extern 5 (_ ⊔ _ ∊ _₋) => eapply @join_neg : typeclass_instances.

Lemma join_pos_l `{JoinSemiLatticeOrder (L:=L)} `{UnEq _} `{Lt _} `{!FullPartialOrder L} `{Zero _} `{0 ∊ L}
  x `{x ∊ L₊} y `{y ∊ L} : x ⊔ y ∊ L₊ .
Proof. split. apply _. red. apply (join_lt_compat_r _ _ _). firstorder. Qed.

Lemma join_pos_r `{JoinSemiLatticeOrder (L:=L)} `{UnEq _} `{Lt _} `{!FullPartialOrder L} `{Zero _} `{0 ∊ L}
  x `{x ∊ L} y `{y ∊ L₊} : x ⊔ y ∊ L₊ .
Proof. split. apply _. red. apply (join_lt_compat_l _ _ _). firstorder. Qed.

Hint Extern 5 (_ ⊔ _ ∊ _₊) => eapply @join_pos_l : typeclass_instances.
Hint Extern 5 (_ ⊔ _ ∊ _₊) => eapply @join_pos_r : typeclass_instances.

Lemma meet_neg_l `{MeetSemiLatticeOrder (L:=L)} `{UnEq _} `{Lt _} `{!FullPartialOrder L} `{Zero _} `{0 ∊ L}
  x `{x ∊ L₋} y `{y ∊ L} : x ⊓ y ∊ L₋ .
Proof. split. apply _. red. apply (meet_lt_compat_r _ _ _). firstorder. Qed.

Lemma meet_neg_r `{MeetSemiLatticeOrder (L:=L)} `{UnEq _} `{Lt _} `{!FullPartialOrder L} `{Zero _} `{0 ∊ L}
  x `{x ∊ L} y `{y ∊ L₋} : x ⊓ y ∊ L₋ .
Proof. split. apply _. red. apply (meet_lt_compat_l _ _ _). firstorder. Qed.

Hint Extern 5 (_ ⊓ _ ∊ _₋) => eapply @meet_neg_l : typeclass_instances.
Hint Extern 5 (_ ⊓ _ ∊ _₋) => eapply @meet_neg_r : typeclass_instances.

Section dec.
  Context `{SemiRingOrder (R:=R)}.
  Context `{Meet _} `{Join _} `{!LatticeOrder R}.
  Context `{!TotalOrder R}.

  Instance: DistributiveLattice R.
  Proof. split. apply _. intros x ? y ? z ?.
    destruct (total (≤) x y) as [E1|E1];
    destruct (total (≤) x z) as [E2|E2];
    lattice_order_simplify R;
    [ apply (join_r _ _); now apply (meet_glb _ _ _)
    | apply (join_l _ _); first [ now apply (meet_le_compat_l _ _ _)
                                | now apply (meet_le_compat_r _ _ _)]..].
  Qed.

  Existing Instance srorder_semiring.

  Instance dec_semiring_lattice_order : SemiRingLatticeOrder R.
  Proof. split; try apply _; intros x ? y ? z ?; destruct (total (≤) y z) as [E1|E1];
    pose proof (order_preserving (x +) _ _ E1);
    try pose proof (order_preserving (x *.) _ _ E1);
    try pose proof (order_preserving (.* x) _ _ E1);
    now lattice_order_simplify R.
  Qed.
End dec.

Section semirings.
  Context `{SemiRingLatticeOrder (R:=R)}.

  Existing Instance srorder_semiring.

  Lemma plus_join_distr_r: RightDistribute (+) (⊔) R.
  Proof right_distr_from_left.

  Lemma plus_meet_distr_r: RightDistribute (+) (⊓) R.
  Proof right_distr_from_left.
End semirings.
Hint Extern 2 (RightDistribute (+) (⊔) _) => class_apply @plus_join_distr_r : typeclass_instances.
Hint Extern 2 (RightDistribute (+) (⊓) _) => class_apply @plus_meet_distr_r : typeclass_instances.

Arguments plus_meet_distr_r {_ _ _ _ _ _ _ _ _ R _} x {_} y {_} z {_}.
Arguments plus_join_distr_r {_ _ _ _ _ _ _ _ _ R _} x {_} y {_} z {_}.

Section rings.
  Context `{Ring (R:=R)} `{Le _} `{!SemiRingOrder R}.
  Context `{Meet _} `{Join _} `{!LatticeOrder R}.

  Instance: LeftDistribute (+) (⊔) R.
  Proof. intros x ? y ? z ?. apply (antisymmetry le _ _).
  + apply (order_reflecting (+ -x) _ _).
    rewrite (_ $ plus_negate_r_split _ _).
    apply (join_lub _ _ _); apply (flip_le_minus_r _ _ _); rewrite (_ $ commutativity (+) _ x);
    lattice_order_tac.
  + apply (join_lub _ _ _); apply (order_preserving (x +) _ _); lattice_order_tac.
  Qed.

  Instance: RightDistribute (+) (⊔) R.
  Proof right_distr_from_left.

  Instance: LeftDistribute (+) (⊓) R.
  Proof. intros x ? y ? z ?. apply (antisymmetry le _ _).
  + apply (meet_glb _ _ _); apply (order_preserving (x +) _ _); lattice_order_tac.
  + apply (order_reflecting (+ -x) _ _).
    rewrite (_ $ plus_negate_r_split _ _).
    apply (meet_glb _ _ _); apply (flip_le_minus_l _ _ _); rewrite (_ $ commutativity (+) _ x);
    lattice_order_tac.
  Qed.

  Instance: RightDistribute (+) (⊓) R.
  Proof right_distr_from_left.

  Lemma negate_join x `{x ∊ R} y `{y ∊ R} : -(x ⊔ y) = (-x) ⊓ (-y).
  Proof. apply (antisymmetry le _ _).
  + apply (meet_glb _ _ _); apply (flip_le_negate _ _); lattice_order_tac.
  + apply (flip_le_negate _ _). rewrite (_ $ negate_involutive _).
    apply (join_lub _ _ _); apply (flip_le_negate _ _); rewrite (_ $ negate_involutive _);
    lattice_order_tac.
  Qed.

  Lemma negate_meet x `{x ∊ R} y `{y ∊ R} : -(x ⊓ y) = (-x) ⊔ (-y).
  Proof. apply (antisymmetry le _ _).
  + apply (flip_le_negate _ _). rewrite (_ $ negate_involutive _).
    apply (meet_glb _ _ _); apply (flip_le_negate _ _); rewrite (_ $ negate_involutive _);
    lattice_order_tac.
  + apply (join_lub _ _ _); apply (flip_le_negate _ _); lattice_order_tac.
  Qed.

  Ltac minus_nonpos :=
    match goal with |- ?a ≤ 0 => cut (a ∊ R⁻); [intro E;apply E|] end;
    apply (flip_nonpos_minus _ _).

  Instance: DistributiveLattice R.
  Proof. split. apply _. intros y ? x₁ ? x₂ ?.
    set (x:=x₁ ⊓ x₂). assert (x ∊ R) by (unfold x; apply _).
    apply (equal_by_zero_sum _ _).
    rewrite (_ $ negate_meet _ _ ).
    rewrite (_ $ distribute_l _ _ _).
    apply (antisymmetry le _ _).
    + apply (join_lub _ _ _); minus_nonpos; apply (order_preserving (y ⊔) _ _); unfold x;
      lattice_order_tac.
    + subtransitivity ( (x-x₁) ⊔ (x-x₂) ).
      * apply (eq_le _ _). unfold x.
        now rewrite <-(_ $ distribute_l _ _ _), <-(_ $ negate_meet _ _), (_ $ plus_negate_r _).
      * apply (join_le_compat _ _ _ _);
        apply (flip_le_minus_r _ _ _);
        rewrite (_ $ distribute_l _ _ _), (_ $ plus_plus_negate_l _ _);
        apply (order_preserving (⊔ x) _ _);
        apply (flip_le_minus_r _ _ _); rewrite (_ $ plus_negate_r y); minus_nonpos; unfold x;
        lattice_order_tac.
  Qed.

  Lemma from_ring_lattice_order :
     (∀ `{x ∊ R⁺} `{y ∊ R} `{z ∊ R}, x * (y ⊔ z) = x*y ⊔ x*z)
   → (∀ `{x ∊ R⁺} `{y ∊ R} `{z ∊ R}, (y ⊔ z) * x = y*x ⊔ z*x)
   → SemiRingLatticeOrder R.
  Proof. intros P1 P2. split; try apply _; [ exact P1 | | exact P2 | ]; intros x ? y ? z ?.
  + now rewrite <-(_ $ negate_involutive (y ⊓ z)),
            <-(_ $ negate_mult_distr_r _ _), (_ $ negate_meet _ _),
            (_ $ P1 x _ _ _ _ _),
            <-2!(_ $ negate_mult_distr_r _ _), <-(_ $ negate_meet _ _),
            (_ $ negate_involutive _).
  + now rewrite <-(_ $ negate_involutive (y ⊓ z)),
            <-(_ $ negate_mult_distr_l _ _), (_ $ negate_meet _ _),
            (_ $ P2 x _ _ _ _ _),
            <-2!(_ $ negate_mult_distr_l _ _), <-(_ $ negate_meet _ _),
            (_ $ negate_involutive _).
  Qed.
End rings.

Section comrings.
  Context `{CommutativeRing (R:=R)} `{Le _} `{!SemiRingOrder R}.
  Context `{Meet _} `{Join _} `{!LatticeOrder R}.

  Lemma from_comring_lattice_order :
     (∀ `{x ∊ R⁺} `{y ∊ R} `{z ∊ R}, x * (y ⊔ z) = x*y ⊔ x*z)
   → SemiRingLatticeOrder R.
  Proof. intro P. apply from_ring_lattice_order. exact P.
    intros x ? y ? z ?. rewrite 3!(_ $ commutativity (.*.) _ x). now apply P.
  Qed.
End comrings.

Section full_pseudo_order.
  Context `{Ring (R:=R)} `{UnEq _} `{Le _} `{Lt _} `{!FullPseudoSemiRingOrder R}.
  Context `{Meet _} `{Join _} `{!LatticeOrder R}.

  Lemma join_negate_nonneg x `{x ∊ R} : x ⊔ -x ∊ R⁺.
  Proof. split. apply _. red. apply (le_iff_not_lt_flip _ _). intro E.
    assert (x ∊ R₋). split. apply _. red.
      apply (le_lt_trans _ (x ⊔ -x) _);trivial. lattice_order_tac.
    assert (-x ∊ R₋). split. apply _. red.
      apply (le_lt_trans _ (x ⊔ -x) _);trivial. lattice_order_tac.
    destruct (neg_not_pos x).
    rewrite <-(_ $ negate_involutive x). apply _.
  Qed.
End full_pseudo_order.

Hint Extern 5 (?x ⊔ -?x ∊ _⁺) => eapply @join_negate_nonneg : typeclass_instances.
