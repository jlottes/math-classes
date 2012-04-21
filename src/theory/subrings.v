Require Import
  abstract_algebra theory.subsetoids theory.subgroups.
Require Export theory.rings.

Class Ideal {A Ae Aplus Amult Azero Anegate} R I :=
  { ideal_rng_r : @Rng A Ae Aplus Amult Azero Anegate R
  ; ideal_rng_i : Rng I
  ; ideal_sub : I ⊆ R
  ; ideal_l r `{!r ∊ R} x `{!x ∊ I} : x * r ∊ I
  ; ideal_r r `{!r ∊ R} x `{!x ∊ I} : r * x ∊ I
  }.

Section subrng_test.
  Context `{Rng (R:=R)}.

  Lemma subrng_test {S:Subset A} `{!SubSetoid S} {sub: S ⊆ R} : 
   (∃ x, x ∊ S) ∧ (∀ a `{!a ∊ S} b `{!b ∊ S}, a - b ∊ S ∧ a * b ∊ S ) ↔ Rng S.
  Proof with try apply _. split.
  + intros [? C]. split. split. apply (subgroup_test_alt R S).
    split. assumption. intros a ? b ?. apply (C a _ b _).
    rewrite sub... apply (subsemigroup R S).
    intros a ? b ?. apply (C a _ b _). rewrite sub... rewrite sub...
  + intro. split. exists 0... intros. split...
  Qed.
End subrng_test.
Arguments subrng_test {A Ae Aplus Amult Azero Anegate} R {_} S {_ _}.

Lemma trivial_subrng_sub `{Rng (R:=R)} : {{0}} ⊆ R.
Proof. intros ? E. rewrite E. apply _. Qed.
Hint Extern 1 (@SubsetOf _ (@singleton _ _ _ (@zero _ _)) _) => eapply @trivial_subrng_sub : typeclass_instances.

Lemma trivial_subrng `{Rng (R:=R)} : Rng {{0}}.
Proof. apply (subrng_test R {{0}}). split. exists 0. apply _.
  intros a Ea b Eb.
  change (a - b = 0 /\ a * b = 0). change (a = 0) in Ea. change (b = 0) in Eb.
  assert (a ∊ R) by (rewrite Ea; apply _).
  assert (b ∊ R) by (rewrite Eb; apply _).
  split; rewrite_on R ->Ea; rewrite_on R ->Eb.
  rewrite (right_inverse 0). reflexivity.
  now rewrite (right_absorb 0).
Qed.
Hint Extern 1 (@Rng _ _ _ _ _ _ (@singleton _ _ _ (@zero _ _))) => eapply @trivial_subrng : typeclass_instances.

Lemma trivial_ideal `{Rng (R:=R)} : Ideal R {{0}}.
Proof. split. apply _. apply _. apply _.
+ intros r ? x E. change (x=0) in E. assert (x ∊ R) by (rewrite E; apply _). rewrite_on R -> E. exact (left_absorb r).
+ intros r ? x E. change (x=0) in E. assert (x ∊ R) by (rewrite E; apply _). rewrite_on R -> E. exact (right_absorb r).
Qed.

Definition rng_kern `{Rng (R:=R)} `{Rng (R:=R')} f `{!Rng_Morphism f R R'} := f⁻¹( {{0}} ).
Local Notation kern := rng_kern.

Section morphisms.
  Context `{Rng (A:=A) (R:=R)} `{Rng (A:=B) (R:=R')} f `{!Rng_Morphism f R R'}.

  Lemma rng_kern_trivial_iff_injective : kern f = {{0}} ↔ Injective f R R'.
  Proof kern_trivial_iff_injective f.

  Lemma rng_mor_injective : (∀ `{x ∊ R}, f x = 0 → x = 0) ↔ Injective f R R'.
  Proof sg_mor_injective f.

  Lemma image_preserves_subrng S `{!S ⊆ R} `{!Rng S} : Rng f⁺¹(S).
  Proof with try apply _. apply (subrng_test R' f⁺¹(S) ). split.
  + exists (0:B). exists (0:A). split... apply preserves_0.
  + intros b1 [a1 [? E1]] b2 [a2 [? E2]]. 
    assert (b1 ∊ R'). rewrite <- E1. apply _.
    assert (b2 ∊ R'). rewrite <- E2. apply _.
    split.
    * exists (a1 - a2). split... rewrite (preserves_plus a1 (-a2)).
      rewrite_on R' -> (preserves_negate a2).
      rewrite_on R' -> E1. now rewrite_on R' -> E2.
    * exists (a1 * a2). split... rewrite (preserves_mult a1 a2).
      rewrite_on R' -> E1. now rewrite_on R' -> E2.
  Qed.

  Lemma inv_image_preserves_subrng S `{!S ⊆ R'}  `{!Rng S} : Rng f⁻¹(S).
  Proof with try apply _. apply (subrng_test R f⁻¹(S) ). split.
  + exists (0:A). split. apply _. rewrite preserves_0...
  + intros a1 [? E1] a2 [? E2]. split.
    * split. apply _. rewrite (preserves_plus a1 (-a2)).
      rewrite_on R' -> (preserves_negate a2)...
    * split. apply _. rewrite (preserves_mult a1 a2)...
  Qed.

  Lemma kern_is_rng : Rng (kern f). Proof inv_image_preserves_subrng {{0}}.

  Lemma preserves_unity `{One A} `{!Ring R} : Ring (Aone := f 1) f⁺¹(R).
  Proof. pose proof (image_preserves_subrng R). apply (rng_is_ring f⁺¹(R)).
  + change (f 1 ∊ f⁺¹(R)). apply _.
  + intros x ?. destruct (_:x ∊ f⁺¹(R)) as [a [? E]].
    change (f 1 * x = x). rewrite_on f⁺¹(R) <- E.
    rewrite <- (preserves_mult 1 a). now rewrite_on R -> (mult_1_l a).
  + intros x ?. destruct (_:x ∊ f⁺¹(R)) as [a [? E]].
    change (x * f 1 = x). rewrite_on f⁺¹(R) <- E.
    rewrite <- (preserves_mult a 1). now rewrite_on R -> (mult_1_r a).
  Qed.

  Lemma kern_is_ideal : Ideal R (kern f).
  Proof. split. apply _. exact kern_is_rng. unfold kern. apply _.
  + intros r ? x [? E]. change (f x = 0) in E.
    split. apply _. change (f (x*r) = 0). rewrite (preserves_mult x r).
    rewrite_on R' -> E. exact (left_absorb (f r)).
  + intros r ? x [? E]. change (f x = 0) in E.
    split. apply _. change (f (r*x) = 0). rewrite (preserves_mult r x).
    rewrite_on R' -> E. exact (right_absorb (f r)).
  Qed.

End morphisms.

(** [ideal_equiv] and [coset_equiv_r] are convertible. *)
Definition ideal_equiv {A} I {Aplus:Plus A} {Anegate:Negate A} a b := a - b ∊ I.

Lemma ideal_equiv_proper : Find_Proper_Signature (@ideal_equiv) 0
  (∀ A R I `{!I ⊆ R} `{Rng (A:=A) (R:=R)} `{!SubSetoid I},
   Proper ((R,=)==>(R,=)==>impl) (ideal_equiv I)).
Proof. intro. intros.
  change (Proper ((R,=) ==> (R,=) ==> impl) (@coset_equiv_r A I Aplus Anegate)).
  find_proper.
Qed.
Hint Extern 0 (Find_Proper_Signature (@ideal_equiv) 0 _) => eexact ideal_equiv_proper : typeclass_instances.


Section quotient_ring.

  Context `{Rng (R:=R)} I `{!Ideal R I}.

  Existing Instance ideal_rng_i.
  Existing Instance ideal_sub.

  Global Instance ideal_subequiv : SubEquivalence R (ideal_equiv I) := _.

  Local Notation "(∼)" := (equiv_ext R (ideal_equiv I)).

  Lemma quotient_rng : Rng (Ae:=(∼)) R.
  Proof with try apply _. split. exact (ab_quotient_group R I). split...
  + rewrite <- (_:subrelation (=) (∼))...
  + split... assert (eq (@sg_op A (@mult_is_sg_op A Amult)) (.*.) ) as Eop by reflexivity.
    rewrite Eop. intros a b E1 c d E2. unfold_sigs. red_sig.
    do 2 red. red in E1, E2.
    rewrite (equiv_ext_correct R (ideal_equiv I) a b) in E1.
    rewrite (equiv_ext_correct R (ideal_equiv I) c d) in E2.
    unfold ideal_equiv in *.
    left. red_sig.
    pose proof (ideal_l c (a-b)) as E1'. rewrite (mult_minus_distr_r (R:=R) a b c) in E1'.
    pose proof (ideal_r b (c-d)) as E2'. rewrite (mult_minus_distr_l (R:=R) b c d) in E2'.
    pose proof (_:(a*c - b*c) + (b*c - b*d) ∊ I) as E3.
    rewrite (associativity (S:=R) (f:=(+)) (a*c - b*c) (b*c) (- (b*d))) in E3.
    rewrite_on R <- (associativity (S:=R) (f:=(+)) (a*c) (-(b*c)) (b*c) ) in E3.
    rewrite_on R -> (plus_negate_l (R:=R) (b*c)) in E3.
    now rewrite_on R -> (plus_0_r (R:=R) (a*c)) in E3.
  + rewrite <- (_:subrelation (=) (∼))...
  + rewrite <- (_:subrelation (=) (∼))...
  Qed.
  
End quotient_ring.
