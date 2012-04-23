Require Import
  abstract_algebra theory.subsetoids theory.common_props
  theory.subgroups theory.subrings.

Local Open Scope grp_scope. (* notation for inverse *)

Existing Instance NonZero_subset.

Lemma field_proper: Find_Proper_Signature (@Field) 0
  (∀ A Ae Aplus Amult Azero Aone Anegate Ainv,
   Proper ((=)==>impl) (@Field A Ae Aplus Amult Azero Aone Anegate Ainv)).
Proof. structure_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@Field) 0 _) => eexact field_proper : typeclass_instances.

Lemma mult_inv_closed `{Field (F:=F)} x `{!x ∊ F ₀} : x⁻¹ ∊ F ₀.
Proof closed_range (F ₀) (F ₀) (⁻¹) (x:=x).
Hint Extern 0 (@Element _ _ (@inv _ _ _)) => eapply @mult_inv_closed : typeclass_instances. 

Section props.
  Context `{Field (F:=F)}.

  Global Instance field_multgroup : @AbGroup _ _ mult_is_sg_op one_is_mon_unit _ (F ₀).
  Proof with try apply _.
    split. split...
    apply (submonoid F (F ₀)). split. split... change (PropHolds (1 ≠ 0))...
    intros x ? y [? yn0]. change (x*y ∊ F ₀). split...
    intro E. mc_contradict yn0.
      rewrite <- (mult_1_l y).
      rewrite_on F <- (field_inv_l x).
      rewrite <- (associativity x⁻¹ x y).
      rewrite_on F -> E.
      exact (right_absorb x⁻¹).
    intros x ?.
    rewrite (commutativity x x⁻¹). exact (field_inv_l x).
    rewrite (_:F ₀ ⊆ F)...
  Qed.

  Lemma mult_inv_l x `{!x ∊ F ₀} : x⁻¹ * x = 1. Proof field_inv_l x.
  Lemma mult_inv_r x `{!x ∊ F ₀} : x / x = 1. Proof inverse_r (G:=(F ₀)) x.
  Lemma mult_inv_involutive x `{!x ∊ F ₀} : (x⁻¹)⁻¹ = x. Proof involutive (S:=(F ₀)) x.

  Lemma field_units : RingUnits F = F ₀.
  Proof. split. intros [?[y[?[E ?]]]]. split. apply _. mc_contradict E.
    rewrite_on F -> E. rewrite (left_absorb y). apply not_symmetry. solve_propholds.
    intros ?. split. apply _. exists x⁻¹. split. apply _.
    split. exact (mult_inv_r x). exact (mult_inv_l x).
  Qed.

  Global Instance : IntegralDomain F.
  Proof. split; try apply _.
    intros x ?. destruct (zero_divisor x).
    assert (x ∊ RingUnits F) by now rewrite field_units.
    pose proof (RingUnit_not_zero_divisor x). contradiction.
  Qed.

End props.

Section subfield_test.

  Context `{Field (F:=F)} `{∀ x y, Decision (x=y)}.

  Existing Instance field_nontrivial.

  Lemma subfield_test (S:Subset A) `{!SubSetoid S} {sub: S ⊆ F} : 
      (∃ x : A, x ∊ S ₀)
    ∧ (∀ a `{!a ∊ S} b `{!b ∊ S}, a - b ∊ S) 
    ∧ (∀ a `{!a ∊ S} b `{!b ∊ S ₀}, a / b ∊ S) ↔ Field S.
  Proof with try apply _. split.
  + intros [[x[? xn0]] [Cm Cd]]. 
    assert (1 ∊ S). rewrite <- (mult_inv_r x). exact (Cd x _ x _).
    assert (∀ a, a ∊ S ₀ → a⁻¹ ∊ S ₀) as Ci. intros a [??]. split.
      rewrite <- (mult_1_l a⁻¹). exact (Cd 1 _ a _). now destruct (_:a⁻¹ ∊ F ₀).
    assert (Rng S). apply (subrng_test F S).
      split. now exists x. intros a ? b ?. split. exact (Cm a _ b _).
      destruct (decide (b=0)) as [E|bn0].
        rewrite_on F -> E. rewrite (right_absorb a), <- (plus_negate_r a). exact (Cm a _ a _).
        change (PropHolds (b ≠ 0)) in bn0.
        assert (b⁻¹ ∊ S ₀). split. rewrite <- (mult_1_l b⁻¹). exact (Cd 1 _ b _).
          now destruct (_:b⁻¹ ∊ F ₀).
        rewrite_on F <- (mult_inv_involutive b). exact (Cd a _ b⁻¹ _).
    split... split... split... split...
    rewrite sub... rewrite sub... rewrite sub...
    split... intros a b E. destruct E as [[[??][??]] E]. split.
      split. exact (Ci a _). exact (Ci b _).
      now rewrite_on (F ₀) -> E.
    rewrite sub...
  + intro. split. exists 1... split; intros; apply _.
  Qed.
End subfield_test.

