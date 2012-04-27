Require Import
  abstract_algebra theory.sub_strong_setoids theory.common_props
  theory.subgroups theory.subrings
  theory.strong_groups theory.strong_rings.

Local Open Scope grp_scope. (* notation for inverse *)

Existing Instance NonZero_subset.

Lemma field_proper: Find_Proper_Signature (@Field) 0
  (∀ A Ae Aplus Amult Azero Aone Anegate Ainv Aue,
   Proper ((=)==>impl) (@Field A Ae Aplus Amult Azero Aone Anegate Ainv Aue)).
Proof. structure_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@Field) 0 _) => eexact field_proper : typeclass_instances.

Lemma mult_inv_closed `{Field (F:=F)} x `{!x ∊ F ₀} : x⁻¹ ∊ F ₀.
Proof closed_range (F ₀) (F ₀) (⁻¹) (x:=x).
Hint Extern 0 (@Element _ _ (@inv _ _ _)) => eapply @mult_inv_closed : typeclass_instances. 

Section props.
  Context `{Field (F:=F)}.

  Lemma field_units : RingUnits F = F ₀.
  Proof. intro x. split.
  + intros [?[y[?[E ?]]]]. split. apply _.
    red. apply (strong_extensionality (.* y) x 0). rewrite E.
    rewrite (left_absorb y). solve_propholds.
  + intros ?. split. apply _. exists x⁻¹. split. apply _.
    split; [ rewrite (commutativity x x⁻¹) | ]; exact (field_inv_l x).
  Qed.

  Global Instance field_multgroup : @AbGroup _ _ mult_is_sg_op one_is_mon_unit _ (F ₀).
  Proof. rewrite <- field_units. apply RingUnits_abgroup; rewrite field_units; apply _. Qed.

  Global Instance strong_mult_nonzero: SubStrongSetoid_Binary_Morphism (.*.) (F ₀) (F ₀) (F ₀).
  Proof. split; try (split; apply _). apply _.
    intros x₁ ? y₁ ? x₂ ? y₂ ?. exact (strong_binary_extensionality (.*.) x₁ y₁ x₂ y₂).
  Qed.

  Instance field_mult_nonzero: Closed (F ₀ ==> F ₀ ==> F ₀) (.*.) := _.

  Lemma mult_inv_l x `{!x ∊ F ₀} : x⁻¹ * x = 1. Proof field_inv_l x.
  Lemma mult_inv_r x `{!x ∊ F ₀} : x / x = 1. Proof inverse_r (G:=(F ₀)) x.
  Lemma mult_inv_involutive x `{!x ∊ F ₀} : (x⁻¹)⁻¹ = x. Proof involutive (S:=(F ₀)) x.

  (* We have the following instances from strong_groups: *)
  
  Instance: StrongInjective (-) F F := _.
  Instance: StrongInjective (⁻¹) (F ₀) (F ₀) := _.

  Global Instance : IntegralDomain F.
  Proof. split; try apply _.
    intros x ?. destruct (zero_divisor x).
    assert (x ∊ RingUnits F) by now rewrite field_units.
    pose proof (RingUnit_not_zero_divisor x). contradiction.
  Qed.

End props.

Hint Extern 0 (?x * ?y ∊ ?F ₀) => eapply @field_mult_nonzero : typeclass_instances.

Section dec_field.
  Context `{StandardUnEq A} `{∀ x y, Decision (x = y)} `{Inv A}.

  Lemma dec_field (F:Subset A) `{CommutativeRing (A:=A) (Ae:=_) (R:=F)} `{PropHolds (1 ≠ 0)}
    : SubSetoid_Morphism (⁻¹) (F ₀) (F ₀)
    → LeftInverse (.*.) (⁻¹) 1 (F ₀)
    → Field F.
  Proof. pose proof dec_strong_setoid. split; try apply _.
    exact (dec_strong_binary_morphism (+)   F F F).
    exact (dec_strong_binary_morphism (.*.) F F F).
  Qed.
End dec_field.

(*
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
*)
