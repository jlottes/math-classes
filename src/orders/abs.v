Require Import
  abstract_algebra interfaces.orders theory.strong_setoids theory.common_props theory.rings
  theory.lattices orders.rings orders.lattices
  lattice_ordered_rings.

Local Open Scope mc_abs_scope.

Hint Extern 20 (Closed _ _ abs) => eapply abs_closed : typeclass_instances.
Hint Extern 5 (abs ?x ∊ _⁺) => eapply (abs_closed x) : typeclass_instances.

Section abs.
  Context `{Ring (R:=R)} `{Le _} `{!SemiRingOrder R} `{Meet _} `{Join _} `{!LatticeOrder R}.
  Context `{Abs _} `{!LatticeAbs R}.

  Instance abs_el x `{x ∊ R} : |x| ∊ R.
  Proof. apply (_ : Subset R⁺ R). apply _. Qed.

  Instance abs_morphism_nonneg : Morphism (R ⇒ R⁺) |·|.
  Proof. intros ?? E. unfold_sigs. red_sig.
    now rewrite 2!(_ $ abs_def _), (_ $ E).
  Qed.

  Instance abs_morphism : Morphism (R ⇒ R) |·|.
  Proof. rewrite <-(_ : Subset (R ⇒ R⁺) (R ⇒ R)). apply _. Qed.

  Lemma abs_of_nonneg x `{x ∊ R⁺} : |x| = x.
  Proof. rewrite (_ $ abs_def _). apply (join_l _ _). exact (nonneg_between _). Qed.

  Lemma abs_of_nonpos x `{x ∊ R⁻} : |x| = -x.
  Proof. rewrite (_ $ abs_def _).
    apply (join_r _ _). rewrite <-(_ $ negate_involutive x) at 1. exact (nonneg_between _).
  Qed.

  Lemma abs_nonneg_plus x `{x ∊ R⁺} y `{y ∊ R⁺} : |x+y| = |x|+|y|.
  Proof. now rewrite 3!(R $ abs_of_nonneg _). Qed.

  Lemma abs_nonpos_plus x `{x ∊ R⁻} y `{y ∊ R⁻} : |x+y| = |x|+|y|.
  Proof. rewrite 3!(R $ abs_of_nonpos _). exact (negate_plus_distr _ _). Qed.

  Lemma abs_0 : | 0 | = 0.
  Proof abs_of_nonneg 0.

  Lemma abs_1 `{1 ∊ R⁺} : | 1 | = 1.
  Proof abs_of_nonneg 1.

  Lemma abs_negate x `{x ∊ R} : | -x | = |x|.
  Proof. now rewrite 2!(_ $ abs_def _), (_ $ negate_involutive _), (_ $ commutativity _ x _). Qed.

  Lemma abs_minus_swap x `{x ∊ R} y `{y ∊ R} : |x-y| = |y-x|.
  Proof. rewrite (_ $ negate_swap_r x y). exact (abs_negate _). Qed.

  Lemma abs_between x `{x ∊ R} : - (|x|) ≤ x ≤ |x|.
  Proof. rewrite (_ $ abs_def x). split; [| lattice_order_tac].
    rewrite <-(_ $ negate_involutive x) at 3. apply (flip_le_negate _ _). lattice_order_tac.
  Qed.

  Lemma abs_le_between x `{x ∊ R} y `{y ∊ R} : |x| ≤ y → -y ≤ x ≤ y.
  Proof.
    intro E. assert (y ∊ R⁺). split. apply _. red. subtransitivity (|x|). apply (_ : |x| ∊ R⁺).
    destruct (abs_between x). split; [subtransitivity (-(|x|))| subtransitivity (|x|)].
    now apply (flip_le_negate _ _).
  Qed.

  Lemma abs_0_iff x `{x ∊ R} : |x| = 0 ↔ x = 0.
  Proof. split; intro E. 2: rewrite (R $ E); exact abs_0.
    pose proof abs_between x as E2. rewrite (R $ E), (R $ negate_0) in E2.
    now apply (antisymmetry le _ _).
  Qed.

  Lemma abs_le_iff x `{x ∊ R} y `{y ∊ R} : |x| ≤ y ↔ -y ≤ x ≤ y.
  Proof. split. exact (abs_le_between _ _).
    intros [E1 E2]. rewrite (_ $ abs_def _). apply (join_lub _ _ _); trivial.
    rewrite <-(_ $ negate_involutive y). now apply (flip_le_negate _ _).
  Qed.

  Lemma abs_triangle x `{x ∊ R} y `{y ∊ R} : |x+y| ≤ |x|+|y|.
  Proof. rewrite (abs_le_iff _ _), (R $ negate_plus_distr _ _).
    apply (plus_le_compat_2 _ _ _ _ _ _); exact (abs_between _).
  Qed.

End abs.

Hint Extern 2 (Morphism (_ ⇒ _⁺) abs) => eapply @abs_morphism_nonneg : typeclass_instances.
Hint Extern 3 (Morphism _ abs) => eapply @abs_morphism : typeclass_instances.
Hint Extern 6 (abs _ ∊ ?R) => eapply @abs_el : typeclass_instances.

Section order_preserving.
  Context `{Ring (R:=R1)} {le1:Le _} `{!SemiRingOrder R1} `{Join _} `{!JoinSemiLatticeOrder R1} {a1:Abs _} `{!LatticeAbs R1}.
  Context `{Ring (R:=R2)} {le2:Le _} `{!SemiRingOrder R2} `{Join _} `{!JoinSemiLatticeOrder R2} {a2:Abs _} `{!LatticeAbs R2}.
  Context (f: R1 ⇀ R2) `{!JoinSemiLattice_Morphism R1 R2 f} `{!SemiRing_Morphism R1 R2 f}.

  Lemma preserves_abs x `{x ∊ R1} : f (|x|) = |f x|.
  Proof. now rewrite 2!(_ $ abs_def _), (_ $ preserves_join f _ _), (_ $ preserves_negate _). Qed.
End order_preserving.

Section from_full_order.
  Context `{Ring (R:=R)} `{UnEq _} `{Le _} `{Lt _} `{!FullPseudoSemiRingOrder R}.
  Context `{Meet _} `{Join _} `{!LatticeOrder R}.

  Context `{Abs _} (C:Closed (R ⇀ R) |·|) (abs_correct: ∀ `{x ∊ R}, |x| = x ⊔ -x).

  Instance: ∀ `{x ∊ R}, |x| ∊ R.    Proof. intros. now apply C. Qed.
  Instance: ∀ `{x ∊ R}, |x| ∊ R⁺ .
  Proof. intros. rewrite (_ $ abs_correct _ _). apply _. Qed.

  Instance lattice_abs_from_full : LatticeAbs R.
  Proof. split. intros ??. apply _. exact abs_correct. Qed.

End from_full_order.

Section full_order.
  Context `{Ring (R:=R)} `{UnEq _} `{Le _} `{Lt _} `{!FullPseudoSemiRingOrder R}.
  Context `{Meet _} `{Join _} `{!FullLatticeOrder R}.
  Context `{Abs _} `{!LatticeAbs R}.

  Existing Instance pseudo_order_setoid.

  Instance abs_pos x `{x ∊ R ₀} : |x| ∊ R₊ .
  Proof. rewrite (_ $ abs_def _). destruct (decompose_nonzero x); apply _. Qed.

  Lemma abs_pos_nonzero x `{x ∊ R} : |x| ∊ R₊ → x ∊ R ₀ .
  Proof. rewrite (_ $ abs_def _). intros [_ E]. red in E.
    destruct (join_sub _ _ _ E).
    assert (x ∊ R₊) by now split. apply _.
    assert (-x ∊ R₊) by (split; trivial; apply _).
    rewrite <-(R $ negate_involutive x). apply _.
  Qed.

  Lemma abs_lt_between x `{x ∊ R} y `{y ∊ R} : |x| < y → -y < x < y.
  Proof. intro E. destruct (abs_between x).
    split. apply (lt_le_trans _ (-(|x|)) _); trivial. now apply (flip_lt_negate _ _).
    now apply (le_lt_trans _ (|x|) _).
  Qed.

  Lemma abs_lt_iff x `{x ∊ R} y `{y ∊ R} : |x| < y ↔ -y < x < y.
  Proof. split. exact (abs_lt_between _ _).
    intros [E1 E2]. rewrite (_ $ abs_def _).
    apply (join_lt _ _ _); trivial.
    rewrite <-(_ $ negate_involutive y). now apply (flip_lt_negate _ _).
  Qed.

  Lemma abs_mult_nonzero x `{x ∊ R ₀} y `{y ∊ R ₀} : |x*y| = |x|*|y| .
  Proof.
    destruct (decompose_nonzero x); destruct (decompose_nonzero y);
    repeat match goal with
    | |- context [ abs ?x ] => rewrite ( R $ abs_of_nonneg x )
    | |- context [ abs ?x ] => rewrite ( R $ abs_of_nonpos x )
    end.
    * subreflexivity.
    * now rewrite (_ $ negate_mult_distr_r _ _).
    * now rewrite (_ $ negate_mult_distr_l _ _).
    * now rewrite (R $ negate_mult_negate _ _).
  Qed.

  Lemma abs_mult_ub x `{x ∊ R} y `{y ∊ R} : |x*y| ≤ |x|*|y| .
  Proof. apply (le_iff_not_lt_flip _ _); intro E.
    assert (x * y ∊ R ₀). apply abs_pos_nonzero. apply _.
      split. apply _. red.
      apply (le_lt_trans _ (abs x * abs y) _); trivial.
      apply (_ : abs x * abs y ∊ R⁺).
    destruct (nonzero_product x y).
    revert E. apply (le_iff_not_lt_flip _ _). apply (eq_le _ _).
    exact (abs_mult_nonzero _ _).
  Qed.

  Lemma abs_mult_lb x `{x ∊ R} y `{y ∊ R} : (|x|) * (|y|) ≤ |x*y| .
  Proof. apply (le_iff_not_lt_flip _ _); intro E.
    assert (abs x * abs y ∊ R₊). split. apply _. red.
      apply (le_lt_trans _ (|x*y|) _); trivial. apply (_ : (|x*y|) ∊ R⁺).
    destruct (nonzero_product (|x|) (|y|)).
    destruct (decompose_nonzero (|x|)); [| destruct (neg_not_nonneg (abs x)); apply _].
    destruct (decompose_nonzero (|y|)); [| destruct (neg_not_nonneg (abs y)); apply _].
    pose proof (abs_pos_nonzero x _).
    pose proof (abs_pos_nonzero y _).
    revert E. apply (le_iff_not_lt_flip _ _).
    apply (eq_le _ _). subsymmetry. exact (abs_mult_nonzero _ _).
  Qed.

  Global Instance abs_mult_full : AbsMult R.
  Proof. intros x ? y ?. apply (antisymmetry le _ _).
    exact (abs_mult_ub _ _). exact (abs_mult_lb _ _).
  Qed.

End full_order.

Hint Extern 5 (abs _ ∊ _₊) => eapply @abs_pos : typeclass_instances.


Section dec_abs.
  Context `{Ring (R:=R)} `{Le _} `{!SemiRingOrder R} `{Meet _} `{Join _} `{!LatticeOrder R}.
  Context `{!TotalOrder R}.

  Instance abs_mult_total `{Abs _} `{!LatticeAbs R} : AbsMult R.
  Proof.
    intros x ? y ?.
    destruct (nonneg_or_nonpos x); destruct (nonneg_or_nonpos y);
    rewrite ?(_ $ abs_of_nonneg _);
    repeat match goal with |- context [ abs ?x ] => rewrite ( R $ abs_of_nonpos x ) end.
  + subreflexivity.
  + exact (negate_mult_distr_r _ _).
  + exact (negate_mult_distr_l _ _).
  + now rewrite (R $ negate_mult_negate _ _).
  Qed.

  Context `{Abs _} (C:Closed (R ⇀ R) |·|) (abs_correct: ∀ `{x ∊ R}, |x| = x ⊔ -x).

  Instance: ∀ `{x ∊ R}, |x| ∊ R.    Proof. intros. now apply C. Qed.
  Instance: ∀ `{x ∊ R}, |x| ∊ R⁺ .
  Proof. intros. split. apply _. red.
    rewrite (_ $ abs_correct _ _). destruct (nonneg_or_nonpos x).
    + apply (join_le_compat_r _ _ _). apply (_ : x ∊ R⁺).
    + apply (join_le_compat_l _ _ _). apply (_ : -x ∊ R⁺).
  Qed.

  Instance dec_abs : LatticeAbs R.
  Proof. split. intros ??. apply _. exact abs_correct. Qed.
End dec_abs.

Hint Extern 10 (AbsMult _) => eapply @abs_mult_total : typeclass_instances.

Instance default_abs {A} `{Join A} `{Negate A} : Abs A | 20 := λ x, x ⊔ -x.

Section default_abs_full.
  Context `{Ring (R:=R)} `{UnEq _} `{Le _} `{Lt _} `{!FullPseudoSemiRingOrder R}.
  Context `{Meet _} `{Join _} `{!LatticeOrder R}.

  Instance default_abs_full_spec : LatticeAbs R.
  Proof. apply lattice_abs_from_full; unfold abs, default_abs.
  + intros ??. apply _.
  + now intros ??.
  Qed.
End default_abs_full.

Hint Extern 5 (LatticeAbs (a:=default_abs) _) => eapply @default_abs_full_spec : typeclass_instances.

Section default_abs_total.
  Context `{Ring (R:=R)} `{Le _} `{!SemiRingOrder R} `{Meet _} `{Join _} `{!LatticeOrder R}.
  Context `{!TotalOrder R}.

  Instance default_abs_total_spec : LatticeAbs R.
  Proof. apply dec_abs; unfold abs, default_abs.
  + intros ??. apply _.
  + now intros ??.
  Qed.
End default_abs_total.

Hint Extern 30 (LatticeAbs (a:=default_abs) _) => eapply @default_abs_total_spec : typeclass_instances.

