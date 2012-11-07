Require Import
  abstract_algebra interfaces.orders theory.setoids theory.jections theory.subgroups.
Require Export theory.rings.

(* We will prove RngIdeal I R -> Rng I *)
Class RngIdeal {A Aplus Amult Azero Anegate Ae} I R :=
  { rngideal_b : @Rng A Aplus Amult Azero Anegate Ae R
  ; rngideal_sub :>> I ⊆ R
  ; rngideal_add : AdditiveGroup I
  ; rngideal_l r `{r ∊ R} x `{x ∊ I} : r * x ∊ I
  ; rngideal_r r `{r ∊ R} x `{x ∊ I} : x * r ∊ I
  }.

Section substructure_tests.

Existing Instance subsetoid_a.

Lemma subsemirng `{SemiRng (R:=R)} {S} `{S ⊆ R}
  `{0 ∊ S} `{!Closed (S ⇀ S ⇀ S) (.*.)} `{!Closed (S ⇀ S ⇀ S) (+)}
  : SemiRng S.
Proof. apply (projected_semirng (id:S ⇀ R)); now intros. Qed.

Lemma subsemiring `{SemiRing (R:=R)} {S} `{S ⊆ R}
  `{0 ∊ S} `{1 ∊ S} `{!Closed (S ⇀ S ⇀ S) (.*.)} `{!Closed (S ⇀ S ⇀ S) (+)}
  : SemiRing S.
Proof. apply (projected_semiring (id:S ⇀ R)); now intros. Qed.

Lemma subcomsemiring `{CommutativeSemiRing (R:=R)} {S} `{S ⊆ R}
  `{0 ∊ S} `{1 ∊ S} `{!Closed (S ⇀ S ⇀ S) (.*.)} `{!Closed (S ⇀ S ⇀ S) (+)}
  : CommutativeSemiRing S.
Proof. apply (projected_com_semiring (id:S ⇀ R)); now intros. Qed.

Lemma subrng `{Rng (R:=R)} {S} `{S ⊆ R}
  x `{x ∊ S} `{!Closed (S ⇀ S ⇀ S) (.*.)} `{!Closed (S ⇀ S ⇀ S) (+)} `{!Closed (S ⇀ S) (-)}
  : Rng S.
Proof. pose proof subabgroup x. apply (projected_rng (id:S ⇀ R)); now intros. Qed.

Lemma subrng_alt `{Rng (R:=R)} {S} `{S ⊆ R}
  x `{x ∊ S} `{!Closed (S ⇀ S ⇀ S) (.*.)}
  : (∀ `{a ∊ S} `{b ∊ S}, a - b ∊ S) → Rng S.
Proof. intro P. pose proof subabgroup_alt x P. apply (projected_rng (id:S ⇀ R)); now intros. Qed.

Lemma subring `{Ring (R:=R)} {S} `{S ⊆ R}
  `{1 ∊ S} `{!Closed (S ⇀ S ⇀ S) (.*.)} `{!Closed (S ⇀ S ⇀ S) (+)} `{!Closed (S ⇀ S) (-)}
  : Ring S.
Proof. pose proof subabgroup 1. apply (projected_ring (id:S ⇀ R)); now intros. Qed.

Lemma subcomring `{CommutativeRing (R:=R)} {S} `{S ⊆ R}
  `{1 ∊ S} `{!Closed (S ⇀ S ⇀ S) (.*.)} `{!Closed (S ⇀ S ⇀ S) (+)} `{!Closed (S ⇀ S) (-)}
  : CommutativeRing S.
Proof. pose proof subring : Ring S. apply comring_from_ring. rewrite (_ : S ⊆ R); apply _. Qed.

End substructure_tests.

Lemma rngideal_a `{I:Subset} `{RngIdeal _ (I:=I) (R:=R)} : Rng I.
Proof. destruct (_:RngIdeal I R).
  assert (Closed (I ⇀ I ⇀ I) (.*.)). intros x ? y ?. apply (rngideal_l _ _).
  apply (subrng 0).
Qed.



Lemma trivial_subrng_ideal `{Rng (R:=R)} : RngIdeal {{0}} R.
Proof. split; [ apply _ | apply _ | exact trivial_subgroup_abelian |..];
  intros r ? x [? E]; (split; [ apply _ |]); rewrite_on R -> E.
  exact (mult_0_r r). exact (mult_0_l r).
Qed.
Hint Extern 10 (RngIdeal {{0}} _) => eapply @trivial_subrng_ideal : typeclass_instances.

Lemma trivial_subrng `{Rng (R:=R)} : Rng {{0}}. Proof rngideal_a.
Hint Extern 10 (Rng {{0}}) => eapply @trivial_subrng : typeclass_instances.


Lemma image_preserves_semirng `{S:Subset} `{SemiRng _ (R:=S)} `{S ⊆ R} `{!SemiRng R} `{SemiRng (R:=R')}
  (f:R ⇀ R') `{!SemiRng_Morphism R R' f} : SemiRng f⁺¹(S).
Proof. split; try apply _; rewrite (_ : f⁺¹(S) ⊆ R'); apply _. Qed.
Hint Extern 5 (SemiRng _⁺¹(_)) => class_apply @image_preserves_semirng : typeclass_instances.

Lemma image_preserves_semiring `{S:Subset} `{SemiRing _ (R:=S)} `{S ⊆ R} `{!SemiRing R} `{SemiRing (R:=R')}
  (f:R ⇀ R') `{!SemiRing_Morphism R R' f} : SemiRing f⁺¹(S).
Proof. split; try apply _; [ | rewrite (_ : f⁺¹(S) ⊆ R'); apply _..].
  split. apply _. exists_sub (1:S). exact preserves_1.
Qed.
Hint Extern 5 (SemiRing _⁺¹(_)) => class_apply @image_preserves_semiring : typeclass_instances.

Lemma image_preserves_comsemiring `{S:Subset} `{CommutativeSemiRing _ (R:=S)} `{S ⊆ R} `{!SemiRing R} `{SemiRing (R:=R')}
  (f:R ⇀ R') `{!SemiRing_Morphism R R' f} : CommutativeSemiRing f⁺¹(S).
Proof. apply comsemiring_from_semiring. apply _. Qed.
Hint Extern 5 (CommutativeSemiRing _⁺¹(_)) => class_apply @image_preserves_comsemiring : typeclass_instances.

Lemma image_preserves_rng `{S:Subset} `{Rng _ (R:=S)} `{S ⊆ R} `{!Rng R} `{Rng (R:=R')}
  (f:R ⇀ R') `{!Rng_Morphism R R' f} : Rng f⁺¹(S).
Proof. split; apply _. Qed.
Hint Extern 5 (Rng _⁺¹(_)) => class_apply @image_preserves_rng : typeclass_instances.

Lemma image_preserves_ring `{S:Subset} `{Ring _ (R:=S)} `{S ⊆ R} `{!Ring R} `{Ring (R:=R')}
  (f:R ⇀ R') `{!Ring_Morphism R R' f} : Ring f⁺¹(S).
Proof. split; apply _. Qed.
Hint Extern 5 (Ring _⁺¹(_)) => class_apply @image_preserves_ring : typeclass_instances.

Lemma image_preserves_comring `{S:Subset} `{CommutativeRing _ (R:=S)} `{S ⊆ R} `{!Ring R} `{Ring (R:=R')}
  (f:R ⇀ R') `{!Ring_Morphism R R' f} : CommutativeRing f⁺¹(S).
Proof. split; try apply _. now destruct (_ : CommutativeSemiRing f⁺¹(S)). Qed.
Hint Extern 5 (CommutativeRing _⁺¹(_)) => class_apply @image_preserves_ring : typeclass_instances.


Lemma inv_image_preserves_semirng `{S:Subset} `{SemiRng _ (R:=S)} `{S ⊆ R'} `{!SemiRng R'} `{SemiRng (R:=R)}
  (f:R ⇀ R') `{!SemiRng_Morphism R R' f} : SemiRng f⁻¹(S).
Proof. split; try apply _; rewrite (_ : f⁻¹(S) ⊆ R); apply _. Qed.
Hint Extern 5 (SemiRng _⁻¹(_)) => class_apply @inv_image_preserves_semirng : typeclass_instances.

Lemma inv_image_preserves_semiring `{S:Subset} `{SemiRing _ (R:=S)} `{S ⊆ R'} `{!SemiRing R'} `{SemiRing (R:=R)}
  (f:R ⇀ R') `{!SemiRing_Morphism R R' f} : SemiRing f⁻¹(S).
Proof. split; try apply _; [| rewrite (_ : f⁻¹(S) ⊆ R); apply _..].
  split. apply _. rewrite (R' $ preserves_1). apply _.
Qed.
Hint Extern 5 (SemiRing _⁻¹(_)) => class_apply @inv_image_preserves_semiring : typeclass_instances.

Lemma inv_image_preserves_comsemiring `{S:Subset} `{SemiRing _ (R:=S)} `{S ⊆ R'} `{!SemiRing R'} `{CommutativeSemiRing (R:=R)}
  (f:R ⇀ R') `{!SemiRing_Morphism R R' f} : CommutativeSemiRing f⁻¹(S).
Proof. apply comsemiring_from_semiring. rewrite (_ : f⁻¹(S) ⊆ R); apply _. Qed.
Hint Extern 5 (CommutativeSemiRing _⁻¹(_)) => class_apply @inv_image_preserves_comsemiring : typeclass_instances.

Lemma inv_image_preserves_rng `{S:Subset} `{Rng _ (R:=S)} `{S ⊆ R'} `{!Rng R'} `{Rng (R:=R)}
  (f:R ⇀ R') `{!Rng_Morphism R R' f} : Rng f⁻¹(S).
Proof. split; apply _. Qed.
Hint Extern 5 (Rng _⁻¹(_)) => class_apply @inv_image_preserves_rng : typeclass_instances.

Lemma inv_image_preserves_ring `{S:Subset} `{Ring _ (R:=S)} `{S ⊆ R'} `{!Ring R'} `{Ring (R:=R)}
  (f:R ⇀ R') `{!Ring_Morphism R R' f} : Ring f⁻¹(S).
Proof. split; apply _. Qed.
Hint Extern 5 (Ring _⁻¹(_)) => class_apply @inv_image_preserves_ring : typeclass_instances.

Lemma inv_image_preserves_comring `{S:Subset} `{Ring _ (R:=S)} `{S ⊆ R'} `{!Ring R'} `{CommutativeRing (R:=R)}
  (f:R ⇀ R') `{!Ring_Morphism R R' f} : CommutativeRing f⁻¹(S).
Proof. apply comring_from_ring. rewrite (_ : f⁻¹(S) ⊆ R); apply _. Qed.
Hint Extern 5 (CommutativeRing _⁻¹(_)) => class_apply @inv_image_preserves_comring : typeclass_instances.

Lemma inv_image_preserves_ideal `{Rng (R:=R)} `{I:Subset} `{RngIdeal _ (I:=I) (R:=R')} (f:R ⇀ R') `{!Rng_Morphism R R' f}
  : RngIdeal f⁻¹(I) R.
Proof. destruct (_:RngIdeal I R').
  split; [ apply _ | apply _ | apply _ |..];
  intros r ? x [??]; (split; [apply _ |]); rewrite (R' $ preserves_mult _ _).
  exact (rngideal_l _ _). exact (rngideal_r _ _).
Qed.
Hint Extern 10 (RngIdeal _⁻¹(_) _) => class_apply @inv_image_preserves_ideal : typeclass_instances.

Definition rng_kern {A B} `{Equiv A} `{Equiv B} `{Zero B} {R:@Subset A} {S:@Subset B} (f:R ⇀ S) := f⁻¹( {{0}} ).
Local Notation kern := rng_kern.

Section morphisms.
  Context `{Rng (R:=R)} `{Rng (R:=R')} (f:R ⇀ R') `{!Rng_Morphism R R' f}.

  Hint Unfold kern : typeclass_instances.

  Instance kern_ideal : RngIdeal (kern f) R := _.

  Lemma rng_kern_trivial_iff_injective : kern f = {{0}} ↔ Injective R R' f.
  Proof grp_kern_trivial_iff_injective f.

  Lemma rng_mor_injective : (∀ `{x ∊ R}, f x = 0 → x = 0) ↔ Injective R R' f.
  Proof grp_mor_injective f.
End morphisms.
Hint Extern 5 (RngIdeal (kern _) _) => class_apply @kern_ideal : typeclass_instances.


Definition quotient_rng_equiv `(R: @Subset A) (I:@Subset A) `{Equiv A} `{Plus A} `{Negate A} : Equiv (R/I)
  := (λ a b, (λ a b, a - b ∊ I) (rep a) (rep b)).

Local Existing Instance quotient_rng_equiv.

Hint Extern 5 (SubEquivalence _ (λ a b, a - b ∊ _)) => eapply @coset_equiv : typeclass_instances.
Hint Extern 5 (SubRelation _ (=) (λ a b, a - b ∊ _)) => eapply @coset_equiv_sub : typeclass_instances.

Section quotient_rng.

  Context `{Rng (R:=R)} I `{!RngIdeal I R}.

  Notation "(∼)" := (λ a b, a - b ∊ I).

  Existing Instance rngideal_a.
  Instance: Setoid (R/I) := quotient_setoid.

  Existing Instance rngideal_l.
  Existing Instance rngideal_r.

  Lemma quotient_rng : Rng (R/I).
  Proof with try apply _. split... split...
  + apply (quotient_binary_morphism (.*.)).
    intros a b E1 c d E2. unfold_sigs. red_sig.
    rewrite_on R <- (plus_0_r (a*c)), <- (plus_negate_l (b*c)).
    rewrite (R $ associativity (+) (a*c) _ _), <- (R $ associativity (+) _ (b*c) _).
    rewrite <- (R $ mult_minus_distr_r _ _ _), <- (R $ mult_minus_distr_l _ _ _).
    apply _.
  Qed.

End quotient_rng.

Hint Extern 5 (Rng (_/_)) => eapply @quotient_rng : typeclass_instances.

Lemma quotient_ring `{Ring (R:=R)} I `{!RngIdeal I R} : Ring (R/I).
Proof. pose proof rngideal_a. split; apply _. Qed.

Hint Extern 5 (Ring (_/_)) => eapply @quotient_ring : typeclass_instances.
