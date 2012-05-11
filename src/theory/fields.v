Require Import
  abstract_algebra theory.strong_setoids theory.common_props
  theory.subgroups theory.subrings
  theory.strong_groups theory.strong_rings.

Local Open Scope grp_scope. (* notation for inverse *)

(* Existing Instance NonZero_subset. *)

Lemma field_proper: Find_Proper_Signature (@Field) 0
  (∀ A Ae Aplus Amult Azero Aone Anegate Ainv Aue,
   Proper ((=)==>impl) (@Field A Ae Aplus Amult Azero Aone Anegate Ainv Aue)).
Proof. structure_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@Field) 0 _) => eexact field_proper : typeclass_instances.

Lemma mult_inv_closed `{Field (F:=F)} x `{x ∊ F ₀} : x⁻¹ ∊ F ₀.
Proof _.
Hint Extern 4 (_⁻¹ ∊ _ ₀) => eapply @mult_inv_closed : typeclass_instances. 

Lemma mult_inv_closed2 `{Field (F:=F)} x `{x ∊ F ₀} : x⁻¹ ∊ F.
Proof. pose proof _ : x⁻¹ ∊ F ₀. apply _. Qed.
Hint Extern 6 (_⁻¹ ∊ _) => eapply @mult_inv_closed2 : typeclass_instances. 


Section props.
  Context `{Field (F:=F)}.

  Lemma field_inv_r x `{x ∊ F ₀} : x / x = 1.
  Proof. rewrite (F $ commutativity (.*.) _ _). exact (field_inv_l x). Qed.

  Lemma field_units : RingUnits F = F ₀.
  Proof. intro x. split.
  + intros [?[y[?[E ?]]]]. split. apply _.
    apply (strong_extensionality (.* y) _ _). rewrite_on F -> E, (mult_0_l y).
    solve_propholds.
  + intros ?. split. apply _. exists_sub (x⁻¹).
    split; [ exact (field_inv_r x) | exact (field_inv_l x) ].
  Qed.

  Global Instance field_multgroup : MultiplicativeAbGroup (F ₀).
  Proof. rewrite <- field_units. apply RingUnits_abgroup; rewrite field_units; apply _. Qed.

  Instance field_mult_nonzero: Closed (F ₀ ==> F ₀ ==> F ₀) (.*.) := _.

  Instance strong_mult_nonzero: StrongSetoid_Binary_Morphism (F ₀) (F ₀) (F ₀) (.*.).
  Proof. split; try apply _.
    intros x₁ ? y₁ ? x₂ ? y₂ ?. exact (strong_binary_extensionality (.*.) x₁ y₁ x₂ y₂).
  Qed.

  Lemma mult_inv_involutive x `{x ∊ F ₀} : (x⁻¹)⁻¹ = x. Proof involutive (S:=(F ₀)) x.

  (* We have the following instances from strong_groups: *)
  
  Instance: StrongInjective F F (-) := _.
  Instance: StrongInjective (F ₀) (F ₀) (⁻¹) := _.

  Global Instance : IntegralDomain F.
  Proof. split; try apply _.
    intros z el. rewrite <- field_units in el.
    exact (RingUnit_left_cancellation z).
  Qed.

End props.

Hint Extern 4 (_ * _ ∊ _ ₀) => eapply @field_mult_nonzero : typeclass_instances.

Section dec_field.
  Context `{CommutativeRing A (R:=F)} `{Inv A}.
  Context `{UnEq A} `{!StandardUnEq F} `{!SubDecision F F (=)}.

  Lemma dec_field `{!PropHolds (1 ≠ 0)}
    : Setoid_Morphism (F ₀) (F ₀) (⁻¹)
    → LeftInverse (.*.) (⁻¹) 1 (F ₀)
    → Field F.
  Proof. pose proof dec_strong_setoid. split; try apply _.
    exact (dec_strong_binary_morphism (+)).
    exact (dec_strong_binary_morphism (.*.)).
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
