Require Import
  abstract_algebra interfaces.integers interfaces.naturals interfaces.rationals
  interfaces.field_of_fractions
  theory.strong_setoids theory.integers theory.fields theory.field_of_fractions
  peano_naturals natpair_integers.

Local Notation Zc := (SRpair (every nat)).

Section hints.
  Context `{Rationals (Q:=Q)}.
  Context `{Integers (Z:=Z)} `{UnEq _} `{!StandardUnEq Z}
      `{Field (F:=F)} `{!StrongInjective Z F (integers_to_ring Z F)}.

  Notation toF := (rationals_to_field Q F).

  Instance: Ring_Morphism Q F toF := _.
  Instance rationals_to_field_strong    : Strong_Morphism Q F toF := dec_strong_morphism _.
  Instance rationals_to_field_srng_mor  : SemiRng_Morphism Q F toF := _.
  Instance rationals_to_field_sring_mor : SemiRing_Morphism Q F toF := _.
  Instance rationals_to_field_rng_mor   : Rng_Morphism Q F toF := _.

  Lemma rationals_to_field_unique_alt (f:Q ⇀ F) (g:Q ⇀ F)
    `{!Ring_Morphism Q F f} `{!Ring_Morphism Q F g} : f = g.
  Proof. transitivity toF; [|symmetry]; exact (rationals_to_field_unique Q _). Qed.

End hints.

Hint Extern 2 (Strong_Morphism   _ _ (rationals_to_field _ _)) => eapply @rationals_to_field_strong    : typeclass_instances.
Hint Extern 2 (SemiRng_Morphism  _ _ (rationals_to_field _ _)) => eapply @rationals_to_field_srng_mor  : typeclass_instances.
Hint Extern 2 (SemiRing_Morphism _ _ (rationals_to_field _ _)) => eapply @rationals_to_field_sring_mor : typeclass_instances.
Hint Extern 2 (Rng_Morphism      _ _ (rationals_to_field _ _)) => eapply @rationals_to_field_rng_mor   : typeclass_instances.

Hint Extern 2 (AdditiveMonoid_Morphism _ _ (rationals_to_field _ _)) => class_apply @srngmor_plus_mor : typeclass_instances.
Hint Extern 2 (AdditiveSemiGroup_Morphism _ _ (rationals_to_field _ _)) => class_apply @rngmor_plus_mor : typeclass_instances.
Hint Extern 2 (MultiplicativeSemiGroup_Morphism _ _ (rationals_to_field _ _)) => class_apply @rngmor_mult_mor : typeclass_instances.


Instance integers_to_field_of_fracs `{Integers (Z:=Z)} `{Rationals (Q:=Q)}
  : ToFieldOfFracs Z Q | 15 := integers_to_ring Z Q.

Instance rationals_frac_to_field `{Integers (Z:=Z)} `{Rationals (Q:=Q)}
  : FracToField Z Q | 15 := λ _ F _ _ _ _ _ _ _, rationals_to_field Q F.

Instance rationals_is_field_of_fracs
  `{Integers (Z:=Z)} `{UnEq _} `{!StandardUnEq Z} `{Rationals (Q:=Q)}
  : Field_of_Fractions Z Q | 15.
Proof. split. apply _. apply _.
+ exact (dec_strong_injective _).
+ unfold to_field_of_fracs, integers_to_field_of_fracs. apply _.
+ intros ????????? F ? h ??.
  assert (StrongInjective Z F (integers_to_ring Z F)).
    now rewrite <- (integers_initial h).
  unfold frac_to_field, rationals_frac_to_field. split; try apply _.
* unfold to_field_of_fracs, integers_to_field_of_fracs.
  match goal with |- ?f = ?g =>
    rewrite (integers_initial f), <-(integers_initial h)
  end. subreflexivity.
* intros g ?? E. exact (rationals_to_field_unique Q g).
Qed.

Instance rationals_strong_subdec_eq_slow `{Rationals (Q:=Q)} : StrongSubDecision Q Q (=) | 10
  := field_of_fracs_strong_subdec_eq_slow (D:=Zc).

Lemma rationals_embed_ints_strong `{Rationals (Q:=Q)}
  `{Integers (Z:=Z)} `{UnEq _} `{!StandardUnEq Z}
  : StrongInjective Z Q (integers_to_ring Z Q).
Proof dec_strong_injective _.

Hint Extern 10 (StrongInjective _ _ (integers_to_ring _ _)) => eapply @rationals_embed_ints_strong : typeclass_instances.

Section alt_Build_Rationals.
  Context `(Z:Subset) `{Integers _ (Z:=Z)} `{UnEq _} `{!StandardUnEq Z}.
  Context `(Q:Subset) `{Field _ (F:=Q)} `{!StandardUnEq Q} `{!RationalsToField Q}.
  Context `{!Injective Z Q (integers_to_ring Z Q)}.

  Instance alt_Build_Rationals :
    (∀ `{Field (F:=F)} `{!StrongInjective Z F (integers_to_ring Z F)},
      RationalsToFieldSpec Q (rationals_to_field Q F))
  → Rationals Q.
  Proof. intro spec. split; try apply _.
  + intros ??????? Z2 ??.
    rewrite <- (integers_initial ((integers_to_ring Z Q) ∘ integers_to_ring Z2 Z)).
    apply _.
  + intros ??????? Z2 ?? ??. intros ????????? F ??.
    assert (StrongInjective Z F (integers_to_ring Z F)).
      rewrite <- (integers_initial ((integers_to_ring Z2 F) ∘ integers_to_ring Z Z2)).
      pose proof dec_strong_injective _ : StrongInjective Z Z2 (integers_to_ring Z Z2).
      apply _.
    now eapply spec.
  Qed.
End alt_Build_Rationals.

Section from_field_of_fracs.
  Context `{Integers (Z:=Z)} `{UnEq _} `{!StandardUnEq Z} `{Field (F:=Q)}
          `{!ToFieldOfFracs Z Q} `{!FracToField Z Q}
          `{!Field_of_Fractions Z Q}.

  Instance from_intfracs_to_field: RationalsToField Q
    := λ _ F _ _ _ _ _ _, frac_to_field Q F (integers_to_ring Z F).

  Instance: StandardUnEq Q := field_of_fracs_standard_uneq.

  Instance: StrongInjective Z Q (integers_to_ring Z Q).
  Proof. rewrite <- (integers_initial (to_field_of_fracs Q)). apply _. Qed.

  Instance from_intfracs: Rationals Q.
  Proof. apply (alt_Build_Rationals Z Q). intros ????????? F ??.
    unfold rationals_to_field, from_intfracs_to_field. split; try apply _.
    intros g ?. pose proof dec_strong_morphism g.
    apply (frac_to_field_unique Z Q F (integers_to_ring Z F) g).
    exact (integers_initial _).
  Qed.
End from_field_of_fracs.

Section another_integers.
  Context `{Rationals (Q:=Q)} `{Integers B (Z:=Z)} `{UnEq B} `{!StandardUnEq Z}.
  Context (f : Z ⇀ Q) `{!Ring_Morphism Z Q f}.

  Instance int_to_rat_strong_inj: StrongInjective Z Q f.
  Proof. rewrite (integers_initial f). exact (dec_strong_injective _). Qed.

  Lemma rationals_decompose_dec x : { (n,d) : B*B | x ∊ Q → (n ∊ Z ∧ d ∊ Z ₀) ∧ x = f n / f d }.
  Proof. destruct (field_of_fracs_decompose_dec x) as [[n d] P].
    exists (n,d). intro. destruct (P _) as [[??] E].
    split. split; apply _. rewrite (Q $ E).
    rewrite <- (mult_inv_cancel_both _ _ _ _).
    rewrite 2!(Q $ integers.to_ring_unique_alt (to_field_of_fracs Q) f _).
    exact (commutativity (.*.) _ _).
  Qed.

  Lemma rationals_decompose x `{x ∊ Q} : ∃ `{n ∊ Z} `{d ∊ Z ₀}, x = f n / f d.
  Proof.
    destruct (rationals_decompose_dec x) as [[n d] P]. destruct (P _) as [[??] E].
    exists_sub n. exists_sub d. trivial.
  Qed.
End another_integers.

Hint Extern 10 (Inverse (rationals_to_field ?Q1 ?Q2)) => eexact (rationals_to_field Q2 Q1) : typeclass_instances.

Lemma rationals_to_rationals_unique `{Rationals (Q:=Q1)} `{Rationals (Q:=Q2)}
  (f:Q1 ⇀ Q2) (g:Q1 ⇀ Q2) `{!Ring_Morphism Q1 Q2 f} `{!Ring_Morphism Q1 Q2 g}
: f = g.
Proof rationals_to_field_unique_alt (Z:=Zc) _ _.

Section another_rationals.
  Context `{Rationals (Q:=Q1)} `{Rationals (Q:=Q2)}.

  Notation f := (rationals_to_field Q1 Q2).

  Instance: Surjective Q1 Q2 f.
  Proof. split; unfold inverse; try apply _.
    exact (rationals_to_rationals_unique _ _).
  Qed.

  Instance rationals_to_rationals_bij: Bijective Q1 Q2 f := {}.

  Lemma to_rationals_unique_alt
    (f : Q1 ⇀ Q2) `{!Ring_Morphism Q1 Q2 f}
    (g : Q1 ⇀ Q2) `{!Ring_Morphism Q1 Q2 g}
    x `{x ∊ Q1} : f x = g x.
  Proof. now destruct (rationals_to_rationals_unique f g x x (_:Proper (Q1,=) x)). Qed.

  Lemma to_rationals_unique (f : Q1 ⇀ Q2) `{!Ring_Morphism Q1 Q2 f} x `{x ∊ Q1} :
    f x = rationals_to_field Q1 Q2 x.
  Proof to_rationals_unique_alt _ _ _.

  Lemma to_rationals_involutive x `{x ∊ Q1} :
    rationals_to_field Q2 Q1 (rationals_to_field Q1 Q2 x) = x.
  Proof jections.bijective_applied _ x.

  Lemma morphisms_involutive
    (f : Q1 ⇀ Q2) `{!Ring_Morphism Q1 Q2 f}
    (g : Q2 ⇀ Q1) `{!Ring_Morphism Q2 Q1 g}
    x `{x ∊ Q2} : f (g x) = x.
  Proof. now destruct (rationals_to_rationals_unique (f∘g) (id:Q2 ⇀ Q2) x x (_:Proper (Q2,=) x)). Qed.

End another_rationals.

Hint Extern 10 (Bijective _ _ (rationals_to_field _ _)) => eapply @rationals_to_rationals_bij : typeclass_instances.

Lemma injective_nats `{Rationals (Q:=Q)} `{Naturals (N:=N)}
  (f:N ⇀ Q) `{!SemiRing_Morphism N Q f} : Injective N Q f.
Proof. split; try apply _. intros x ? y ? E.
  apply (injective (naturals_to_semiring N Zc) _ _).
  apply (injective (integers_to_ring Zc Q) _ _).
  now rewrite 2!(Q $ naturals.to_semiring_unique_alt f (integers_to_ring Zc Q ∘ naturals_to_semiring N Zc) _) in E.
Qed.

Section isomorphic_image_is_rationals.
  Context `{Rationals (Q:=Q)} `{Field (F:=Q2)} `{!StandardUnEq Q2}.
  Context (f : Q ⇀ Q2) `{!Inverse f} `{!Bijective Q Q2 f} `{!Ring_Morphism Q Q2 f}.
  Open Scope mc_fun_scope.

  Instance iso_to_field: RationalsToField Q2 := λ _ F _ _ _ _ _ _, rationals_to_field Q F ∘ f⁻¹.
  Hint Unfold iso_to_field: typeclass_instances.

  Instance: Bijective Q2 Q f⁻¹ := _.
  Instance: Ring_Morphism Q2 Q f⁻¹ := _.

  Lemma iso_is_rationals: Rationals Q2.
  Proof. split; try apply _; intros ??????? Z ??.
  + split; try apply _. intros x ? y ? E.
    apply (injective (f ∘ integers_to_ring Z Q) _ _).
    now rewrite 2!(Q2 $ to_ring_unique (f ∘ integers_to_ring Z Q) _).
  + intros ??. intros ????????? F ??. unfold rationals_to_field, iso_to_field.
    split. apply _.
    intros g ?. rewrite <- (rationals_to_field_unique Q (g ∘ f)).
    change (g = g ∘ (f ∘ f⁻¹)). rewrite (surjective f). subreflexivity.
  Qed.
End isomorphic_image_is_rationals.

Section injective_preimage_is_rationals.
  Context `{Field (F:=Q2)} `{!StandardUnEq Q2}.
  Context `{Integers  (Z:=Z)} (h : Z ⇀ Q2) `{!Injective Z Q2 h} `{!Ring_Morphism Z Q2 h}.
  Context `{Rationals (Q:=Q)} (f : Q2 ⇀ Q) `{!Injective Q2 Q f} `{!Ring_Morphism Q2 Q f}.
  Open Scope mc_fun_scope.

  Instance: StandardUnEq Z := _.
  Instance: StrongInjective Z Q2 (integers_to_ring Z Q2).
  Proof. rewrite <- (integers_initial h). exact (dec_strong_injective _). Qed.

  Instance inj_pre_inv: Inverse f := rationals_to_field Q Q2.
  Instance: Surjective Q2 Q f.
  Proof. split; unfold inverse, inj_pre_inv; try apply _.
    exact (rationals_to_rationals_unique _ _).
  Qed.
  Instance inj_pre_bij: Bijective Q2 Q f := {}.

  Instance inj_pre_to_field: RationalsToField Q2 := iso_to_field f⁻¹.
  Instance inj_pre_is_rationals: Rationals Q2 := iso_is_rationals f⁻¹.
End injective_preimage_is_rationals.
