Require Import
  abstract_algebra substructures theory.setoids theory.subgroups.
Require Export theory.rings.

Local Existing Instance subsetoid_a.
Local Existing Instance subsetoid_b.
Local Existing Instance subgroup_a.
Local Existing Instance subrng_a.
Local Existing Instance subrng_b.
Local Existing Instance rngideal_b.

Section subrng_test.
  Context `{Rng (R:=R)} {S} `{!SubSetoid S R}.

  Context x `{x ∊ S} `{!Closed (S ==> S ==> S) (.*.)}.

  Local Existing Instance subsemigroup_a.

  Let lemma `{!AdditiveSubGroup S R} : SubRng S R.
  Proof with try apply _. pose proof subsemigroup (op:=mult_is_sg_op).
    split... split...
    exact absubgroup_abelian.
    rewrite (_:S ⊆ R)... rewrite (_:S ⊆ R)...
  Qed.

  Lemma subrng `{!Closed (S ==> S ==> S) (+)} `{!Closed (S ==> S) (-)} : SubRng S R.
  Proof. pose proof subgroup x. exact lemma. Qed.

  Lemma subrng_alt : (∀ `{a ∊ S} `{b ∊ S}, a - b ∊ S) → SubRng S R.
  Proof. intro P. pose proof subgroup_alt x P. exact lemma. Qed.

End subrng_test.

Instance rngideal_subrng {A I} `{RngIdeal A (I:=I) (R:=R)} : SubRng I R.
Proof. pose proof absubgroup_abelian.
  assert (Closed (I ==> I ==> I) (.*.)) by (intros ????; exact (rngideal_l _ _)).
  exact (subrng 0).
Qed.

Lemma rngideal_a {A I} `{ideal: RngIdeal A (I:=I) (R:=R)} : Rng I. Proof subrng_a.
Local Existing Instance rngideal_a.


Lemma trivial_subrng_ideal `{Rng (R:=R)} : RngIdeal {{0}} R.
Proof. split; [ apply _ | exact trivial_subgroup |..];
  intros r ? x [? E]; (split; [ apply _ |]); rewrite_on R -> E.
  exact (mult_0_r r). exact (mult_0_l r).
Qed.
Hint Extern 10 (RngIdeal {{0}} _) => eapply @trivial_subrng_ideal : typeclass_instances.

Lemma trivial_subrng `{Rng (R:=R)} : SubRng {{0}} R. Proof rngideal_subrng.
Hint Extern 10 (SubRng {{0}} _) => eapply @trivial_subrng : typeclass_instances.

Lemma trivial_subrng_rng `{Rng (R:=R)} : Rng {{0}}. Proof subrng_a.
Hint Extern 10 (Rng {{0}}) => eapply @trivial_subrng_rng : typeclass_instances.

Instance subrng_plus_subgroup `{SubRng A (R:=X) (S:=Y)} : AdditiveSubGroup X Y := {}.

Section image.
  Context {A S} `{SubRng A (R:=S) (S:=R)} `{Rng (R:=R')} (f:R ⇀ R') `{!Rng_Morphism R R' f}.

  Instance: AdditiveSubGroup f⁺¹(S) R' := image_preserves_subgroup f.
  Instance: AdditiveGroup f⁺¹(S) := absubgroup_abelian.

  Instance: Closed (f⁺¹(S) ==> f⁺¹(S) ==> f⁺¹(S)) (.*.).
  Proof. intros b1 [? [a1 [? E1]]] b2 [? [a2 [? E2]]]. split. apply _.
    exists_sub (a1 * a2). now rewrite_on R' -> (preserves_mult a1 a2), E1, E2.
  Qed.

  Instance image_preserves_subrng: SubRng f⁺¹(S) R' := subrng 0.
End image.

Section inv_image.
  Context {A B} `{Rng A (R:=R)} {S} `{SubRng B (R:=S) (S:=R')} (f:R ⇀ R') `{!Rng_Morphism R R' f}.

  Instance: AdditiveSubGroup f⁻¹(S) R := inv_image_preserves_subgroup f.
  Instance: AdditiveGroup f⁻¹(S) := absubgroup_abelian.

  Instance: Closed (f⁻¹(S) ==> f⁻¹(S) ==> f⁻¹(S)) (.*.).
  Proof. intros a1 [? E1] a2 [? E2]. split. apply _. rewrite_on R' -> (preserves_mult a1 a2). apply _. Qed.

  Instance inv_image_preserves_subrng: SubRng f⁻¹(S) R := subrng 0.
End inv_image.

Lemma inv_image_preserves_ideal {A B} `{Rng A (R:=R)} {I} `{RngIdeal B (I:=I) (R:=R')} (f:R ⇀ R') `{!Rng_Morphism R R' f}
  : RngIdeal f⁻¹(I) R.
Proof. pose proof inv_image_preserves_subrng f.
  split; try apply _; intros r ? x [??]; (split; [apply _ |]); rewrite (R' $ preserves_mult _ _).
  exact (rngideal_l _ _). exact (rngideal_r _ _).
Qed.

Definition rng_kern {A B} `{Equiv A} `{Equiv B} `{Zero B} {R:Subset A} {S:Subset B} (f:R ⇀ S) := f⁻¹( {{0}} ).
Local Notation kern := rng_kern.

Section morphisms.
  Context `{Rng (R:=R)} `{Rng (R:=R')} (f:R ⇀ R') `{!Rng_Morphism R R' f}.

  Lemma kern_ideal : RngIdeal (kern f) R.
  Proof inv_image_preserves_ideal (I:={{0}}) f.

  Lemma rng_kern_trivial_iff_injective : kern f = {{0}} ↔ Injective R R' f.
  Proof grp_kern_trivial_iff_injective f.

  Lemma rng_mor_injective : (∀ `{x ∊ R}, f x = 0 → x = 0) ↔ Injective R R' f.
  Proof grp_mor_injective f.
End morphisms.

Hint Extern 5 (SubRelation _ (=) (λ a b, a - b ∊ _)) => eapply @coset_equiv_sub : typeclass_instances.

Section quotient_rng.

  Context `{Rng (R:=R)} I `{!RngIdeal I R}.

  Notation "(∼)" := (λ a b, a - b ∊ I).

  Instance: Setoid (Ae:=(∼)) R := coset_equiv.

  Existing Instance rngideal_l.
  Existing Instance rngideal_r.

  Lemma quotient_rng : Rng (Ae:=(∼)) R.
  Proof with try apply _. split. exact ab_quotient_group. split...
  + rewrite <- (_:SubRelation R (=) (∼))...
  + split... change (Proper ((R,(∼))==>(R,(∼))==>(R,(∼))) (.*.)).
    intros a b E1 c d E2. unfold_sigs. red_sig.
    rewrite_on R <- (plus_0_r (a*c)), <- (plus_negate_l (b*c)).
    rewrite (R $ associativity (+) (a*c) _ _), <- (R $ associativity (+) _ (b*c) _).
    rewrite <- (R $ mult_minus_distr_r _ _ _), <- (R $ mult_minus_distr_l _ _ _).
    apply _.
  + rewrite <- (_:SubRelation R (=) (∼))...
  + rewrite <- (_:SubRelation R (=) (∼))...
  Qed.

End quotient_rng.

Section quotient_ring.

  Context `{Ring (R:=R)} I `{!RngIdeal I R}.

  Notation "(∼)" := (λ a b, a - b ∊ I).

  Lemma quotient_ring : Ring (Ae:=(∼)) R.
  Proof. split; [ exact (quotient_rng I) | | rewrite <- (_:SubRelation R (=) (∼)) ..]; apply _. Qed.
End quotient_ring.
