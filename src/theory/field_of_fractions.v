Require Import
  abstract_algebra interfaces.field_of_fractions
  theory.strong_setoids theory.fields
  implementations.field_of_fractions
  stdlib_ring misc.quote.

Local Existing Instance field_of_frac_intdom.

Section hints.
  Context `{Field_of_Fractions (D:=D) (Q:=Q)}.
  Notation toQ := (to_field_of_fracs Q).

  Instance: Ring_Morphism D Q toQ := _.

  Instance to_field_of_fracs_strong_mor : Strong_Morphism D Q toQ := strong_injective_mor _.
  Instance to_field_of_fracs_srng_mor  : SemiRng_Morphism D Q toQ := _.
  Instance to_field_of_fracs_sring_mor : SemiRing_Morphism D Q toQ := _.
  Instance to_field_of_fracs_rng_mor   : Rng_Morphism D Q toQ := _.

  Section another_field.
    Context `{Field (F:=F)} {h:D ⇀ F} `{!StrongInjective D F h} `{!Ring_Morphism D F h}.
    Notation fromQ := (frac_to_field Q F h).

    Instance: Ring_Morphism Q F fromQ := _.

    Instance frac_to_field_srng_mor  : SemiRng_Morphism Q F fromQ := _.
    Instance frac_to_field_sring_mor : SemiRing_Morphism Q F fromQ := _.
    Instance frac_to_field_rng_mor   : Rng_Morphism Q F fromQ := _.
  End another_field.

End hints.

Hint Extern 2 (Strong_Morphism   _ _ (to_field_of_fracs _)) => eapply @to_field_of_fracs_strong_mor : typeclass_instances.
Hint Extern 2 (SemiRng_Morphism  _ _ (to_field_of_fracs _)) => eapply @to_field_of_fracs_srng_mor  : typeclass_instances.
Hint Extern 2 (SemiRing_Morphism _ _ (to_field_of_fracs _)) => eapply @to_field_of_fracs_sring_mor : typeclass_instances.
Hint Extern 2 (Rng_Morphism      _ _ (to_field_of_fracs _)) => eapply @to_field_of_fracs_rng_mor   : typeclass_instances.
Hint Extern 2 (SemiRng_Morphism  _ _ (frac_to_field _ _ _)) => eapply @frac_to_field_srng_mor  : typeclass_instances.
Hint Extern 2 (SemiRing_Morphism _ _ (frac_to_field _ _ _)) => eapply @frac_to_field_sring_mor : typeclass_instances.
Hint Extern 2 (Rng_Morphism      _ _ (frac_to_field _ _ _)) => eapply @frac_to_field_rng_mor   : typeclass_instances.

Section contents.
  Context `{D:@Subset A} `{Field_of_Fractions _ (D:=D) (Q:=Q)}.

  Add Ring D : (stdlib_ring_theory D).

  Notation toQ := (to_field_of_fracs Q).

  Section another_field.
    Context `{Field (F:=F)} {h:D ⇀ F} `{!StrongInjective D F h} `{!Ring_Morphism D F h}.

    Lemma frac_to_field_extend_applied x `{x ∊ D} : frac_to_field Q F h (toQ x) = h x.
    Proof. now destruct (frac_to_field_extend D Q F h x x (_:Proper (D,=) x)). Qed.
  End another_field.

  Notation toFracD := (frac_to_field Q (Frac D) (')).

  Lemma field_of_fracs_decompose_dec x : { (n,d) : A * A | x ∊ Q → (n ∊ D ∧ d ∊ D ₀) ∧ x = toQ n / toQ d }.
  Proof. exists (pair (num (toFracD x)) (den (toFracD x))). intro.
    pose proof (_ : toFracD x ∊ Frac D) as el.
    split. destruct (toFracD x), el. now split.
    apply (injective toFracD _ _). preserves_simplify (toFracD).
    destruct (toFracD x) as [n d]; clear dependent x; simpl in *.
    destruct (_ : {| num := n; den := d |} ∊ Frac D).
    rewrite <- (mult_inv_cancel_r _ _ _).
    rewrite 2!(Frac D $ frac_to_field_extend_applied (h:=cast D (Frac D)) _).
    change ( n*d*1 = d*1*n ). subring D.
  Qed.

  Lemma field_of_fracs_decompose x `{x ∊ Q} : ∃ `{n ∊ D} `{d ∊ D ₀}, x = toQ n / toQ d.
  Proof. destruct (field_of_fracs_decompose_dec x) as [[n d] P]. destruct (P _) as [[??] ?].
         exists_sub n. now exists_sub d.
  Qed.

  Instance field_of_fracs_denial_inequality `{!DenialInequality D} : DenialInequality Q.
  Proof. split. exact (uneq_ne _ _).
    intro E. apply (strong_extensionality toFracD).
    rewrite (denial_inequality _ _). contradict E. now apply (injective toFracD _ _).
  Qed.

  Instance field_of_fracs_strong_subdec_eq_slow `{!StrongSubDecision D D (=)} : StrongSubDecision Q Q (=).
  Proof. intros x y. destruct (decide_sub_strong (=) (toFracD x) (toFracD y)) as [E|E]; [left|right]; intros ??.
  + apply (injective toFracD _ _). apply E; apply _.
  + intro E2. apply E; try apply _. now apply (extensionality toFracD).
  Qed.

  Instance field_of_fracs_subdec_eq_slow `{!SubDecision D D (=)} : SubDecision Q Q (=).
  Proof. intros x ? y ?. destruct (decide_sub (=) (toFracD x) (toFracD y)) as [E|E]; [left|right].
  + now apply (injective toFracD _ _).
  + contradict E. now apply (extensionality toFracD).
  Qed.

End contents.

Section morphisms.
  Context `{Field_of_Fractions (D:=D1) (Q:=Q1)}.
  Context `{IntegralDomain (D:=D2)}.
  Context `{Field (F:=F)} (h:D2 ⇀ F) `{!StrongInjective D2 F h} `{!Ring_Morphism D2 F h}.

  Context (f:D1 ⇀ D2) `{!StrongInjective D1 D2 f} `{!Ring_Morphism D1 D2 f}.

  Definition frac_lift : Q1 ⇀ F := frac_to_field Q1 F (h ∘ f).
  Hint Unfold frac_lift : typeclass_instances.

  Notation toQ1 := (to_field_of_fracs Q1).

  Instance frac_lift_strong: Strong_Morphism Q1 F frac_lift := _.
  Instance frac_lift_mor: Ring_Morphism Q1 F frac_lift := _.
  Lemma frac_lift_extend: frac_lift ∘ toQ1 = h ∘ f.
  Proof frac_to_field_extend D1 Q1 F _.

  Lemma frac_lift_unique (g:Q1 ⇀ F) `{!Strong_Morphism Q1 F g} `{!Ring_Morphism Q1 F g}
    : g ∘ toQ1 = h ∘ f → g = frac_lift.
  Proof frac_to_field_unique D1 Q1 F _ g.

End morphisms.

  