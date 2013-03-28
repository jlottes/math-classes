(* General results about arbitrary integer implementations. *)
Require
  theory.nat_distance.
Require Import
  interfaces.naturals abstract_algebra natpair_integers
  theory.setoids misc.quote theory.integral_domains.
Require Export
  interfaces.integers.

Section integers_to_ring_hints.
  Context `{Integers (Z:=Z)} `{CommutativeRing (R:=R)}.
  Existing Instance integers_to_ring_mor.
  Instance integers_to_ring_morphism : Morphism (Z ⇒ R) (integers_to_ring Z R) := _.
End integers_to_ring_hints.
Hint Extern 2 (Morphism _ (integers_to_ring _ _)) => class_apply @integers_to_ring_morphism : typeclass_instances.
Hint Extern 2 (Rng_Morphism _ _ (integers_to_ring _ _)) => class_apply @ringmor_rngmor : typeclass_instances.
Hint Extern 2 (SemiRng_Morphism _ _ (integers_to_ring _ _)) => class_apply @sringmor_srng_mor : typeclass_instances.
Hint Extern 2 (AdditiveMonoid_Morphism _ _ (integers_to_ring _ _)) => class_apply @srngmor_plus_mor : typeclass_instances.
Hint Extern 2 (AdditiveSemiGroup_Morphism _ _ (integers_to_ring _ _)) => class_apply @rngmor_plus_mor : typeclass_instances.
Hint Extern 2 (MultiplicativeSemiGroup_Morphism _ _ (integers_to_ring _ _)) => class_apply @rngmor_mult_mor : typeclass_instances.

Lemma to_ring_unique `{Integers (Z:=Z)} `{CommutativeRing (R:=R)} (f:Z ⇀ R) `{!Ring_Morphism Z R f} x `{x ∊ Z} :
  f x = integers_to_ring Z R x.
Proof. apply (integers_initial f). now red_sig. Qed.

Lemma to_ring_unique_alt `{Integers (Z:=Z)} `{CommutativeRing (R:=R)}
  (f:Z ⇀ R) (g:Z ⇀ R) `{!Ring_Morphism Z R f} `{!Ring_Morphism Z R g} x `{x ∊ Z} :
  f x = g x.
Proof. now rewrite (R $ to_ring_unique f _), (R $ to_ring_unique g _). Qed.

Lemma morphisms_involutive `{Integers (Z:=Z)} `{CommutativeRing (R:=R)}
  (f:R ⇀ Z) (g:Z ⇀ R) `{!Ring_Morphism R Z f} `{!Ring_Morphism Z R g} x `{x ∊ Z} :
  f (g x) = x.
Proof to_ring_unique_alt (f ∘ g) id x.

Lemma to_ring_involutive `{Integers (Z:=Z)} `{Integers (Z:=Z2)} x `{x ∊ Z} :
  integers_to_ring Z2 Z (integers_to_ring Z Z2 x) = x.
Proof morphisms_involutive (integers_to_ring Z2 Z) (integers_to_ring Z Z2) x.
Arguments to_ring_involutive {_ _ _ _ _ _ _} Z {_ _ _ _ _ _ _ _ _} Z2 {_ _} x {_}.

Lemma to_ring_twice `{Integers (Z:=Z)} `{CommutativeRing (R:=R1)} `{CommutativeRing (R:=R2)}
  (f:R1 ⇀ R2) (g:Z ⇀ R1) (h:Z ⇀ R2) `{!Ring_Morphism R1 R2 f} `{!Ring_Morphism Z R1 g} `{!Ring_Morphism Z R2 h} x `{x ∊ Z} :
  f (g x) = h x.
Proof to_ring_unique_alt (f ∘ g) h x.

Lemma to_ring_self `{Integers (Z:=Z)} (f:Z ⇀ Z) `{!Ring_Morphism Z Z f} x `{x ∊ Z} : f x = x.
Proof to_ring_unique_alt f id x.

(** A ring morphism from integers to another ring is injective if there's an injection in the other direction: *)
Lemma to_ring_injective `{Integers (Z:=Z)} `{CommutativeRing (R:=R)}
   (f:R ⇀ Z) (g:Z ⇀ R) `{!Ring_Morphism R Z f} `{!Ring_Morphism Z R g}: Injective Z R g.
Proof.
  repeat (split; try apply _).
  intros x ? y ? E.
  rewrite_on Z <- (morphisms_involutive f g x), <- (morphisms_involutive f g y).
  now rewrite_on R -> E.
Qed.

Instance integers_to_integers_injective `{Integers (Z:=Z)} `{Integers (Z:=Z2)} (f:Z ⇀ Z2) `{!Ring_Morphism Z Z2 f}:
  Injective Z Z2 f | 15.
Proof to_ring_injective (integers_to_ring Z2 Z) f.

Instance naturals_to_integers_injective `{Integers (Z:=Z)} `{Naturals (N:=N)} (f: N ⇀ Z) `{!SemiRing_Morphism N Z f} :
  Injective N Z f.
Proof.
  split; try apply _. intros x ? y ? E.
  apply (injective (cast N (SRpair N)) _ _).
  rewrite <- 2!(SRpair N $ naturals.to_semiring_twice (integers_to_ring Z (SRpair N)) f (cast N (SRpair N)) _).
  now rewrite_on Z -> E.
Qed.

Section retract_is_int.
  Local Open Scope mc_fun_scope.
  Context `{Integers (Z:=Z)} `{CommutativeRing (R:=Z2)}.
  Context (f:Z ⇀ Z2) `{!Inverse f} `{!Surjective Z Z2 f} `{!Ring_Morphism Z Z2 f} `{!Ring_Morphism Z2 Z (f⁻¹)}.

  (* If we make this an instance, then instance resolution will often loop *)
  Definition retract_is_int_to_ring : IntegersToRing Z2 := λ _ R _ _ _ _ _, integers_to_ring Z R ∘ f⁻¹.

  (* If we make this an instance, then instance resolution will often loop *)
  Program Instance retract_is_int: Integers Z2 (U:=retract_is_int_to_ring).
  Next Obligation. unfold integers_to_ring, retract_is_int_to_ring. apply _. Qed.
  Next Obligation. unfold integers_to_ring, retract_is_int_to_ring.
    intros x y F. unfold_sigs. red_sig. rewrite_on Z2 -> F.
    subtransitivity ((h ∘ (f ∘ f⁻¹)) y); unfold compose.
      now rewrite_on Z2 -> (jections.surjective_applied f y).
    exact (to_ring_unique (h ∘ f) _).
  Qed.
End retract_is_int.

Section contents.
Context `{Integers (Z:=Z)}.
Notation nat := (every nat).
Notation Z_to_natp := (integers_to_ring Z (SRpair nat)).

Global Program Instance: StrongSubDecision Z Z (=) | 10 := λ x y,
  match decide_sub (=) (Z_to_natp x) (Z_to_natp y) with
  | left E => left _
  | right E => right _
  end.
Next Obligation. now apply (injective Z_to_natp). Qed.
Next Obligation. intros F. apply E. now rewrite_on Z -> F. Qed.

Global Program Instance slow_int_abs `{Naturals (N:=N)} : IntAbs Z N | 10 := λ x, 
  match int_abs_sig (SRpair N) N (integers_to_ring Z (SRpair N) x) with
  | inl (exist _ n p) => inl n
  | inr (exist _ n p) => inr n
  end.
Next Obligation.  pose proof p _ as [? E]. clear dependent p. split. apply _.
  apply (injective (integers_to_ring Z (SRpair N)) _ _).
  rewrite_on (SRpair N) <- E. exact (naturals.to_semiring_twice _ _ _ _).
Qed.
Next Obligation. pose proof p _ as [? E]. clear dependent p. split. apply _.
  apply (injective (integers_to_ring Z (SRpair N)) _ _).
  rewrite (SRpair N $ rings.preserves_negate _), <- (SRpair N $ E).
  exact (naturals.to_semiring_twice _ _ _ _).
Qed.

Context `{UnEq _} `{!StandardUnEq Z}.

Lemma int_nontrivial: 1 ∊ Z ₀.
Proof. split. apply _. destruct naturals.nat_nontrivial as [_ P]. generalize P. rewrite 2!(standard_uneq _ _).
  intro E. mc_contradict E.
  apply (injective (naturals_to_semiring nat Z) _ _). now preserves_simplify (naturals_to_semiring nat Z).
Qed.
Hint Extern 6 (1 ∊ _ ₀) => eapply @int_nontrivial : typeclass_instances.

Global Instance: ZeroProduct Z.
Proof. intros x ? y ? E.
  assert (Z_to_natp x * Z_to_natp y = 0) as E'.
    now rewrite <- (SRpair nat $ rings.preserves_mult _ _), (Z $ E), (SRpair nat $ rings.preserves_0).
  destruct (zero_product _ _ E'); [left|right];
    apply (injective Z_to_natp _ _); now preserves_simplify (Z_to_natp).
Qed.

Global Instance: IntegralDomain Z := dec_intdom.
End contents.
