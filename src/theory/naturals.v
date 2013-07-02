Require Import
  abstract_algebra peano_naturals theory.setoids theory.common_props theory.jections theory.rings
  misc.quote.
Require Export
  interfaces.naturals.

Section naturals_to_semiring_hints.
  Context `{Naturals (N:=N)} `{CommutativeSemiRing (R:=R)}.
  Existing Instance naturals_to_semiring_mor.
  Instance naturals_to_semiring_morphism : Morphism (N ⇒ R) (naturals_to_semiring N R) := _.
End naturals_to_semiring_hints.
Hint Extern 2 (Morphism _ (naturals_to_semiring _ _)) => class_apply @naturals_to_semiring_morphism : typeclass_instances.
Hint Extern 2 (SemiRng_Morphism _ _ (naturals_to_semiring _ _)) => class_apply @sringmor_srng_mor : typeclass_instances.
Hint Extern 2 (AdditiveMonoid_Morphism _ _ (naturals_to_semiring _ _)) => class_apply @srngmor_plus_mor : typeclass_instances.
Hint Extern 2 (MultiplicativeSemiGroup_Morphism _ _ (naturals_to_semiring _ _)) => class_apply @srngmor_mult_mor : typeclass_instances.

Lemma to_semiring_unique `{Naturals (N:=N)} `{CommutativeSemiRing (R:=R)} (f:N ⇀ R) `{!SemiRing_Morphism N R f} x `{x ∊ N} :
  f x = naturals_to_semiring N R x.
Proof. apply (naturals_initial f). now red_sig. Qed.

Lemma to_semiring_unique_alt `{Naturals (N:=N)} `{CommutativeSemiRing (R:=R)}
  (f:N ⇀ R) (g:N ⇀ R) `{!SemiRing_Morphism N R f} `{!SemiRing_Morphism N R g} x `{x ∊ N} :
  f x = g x.
Proof. now rewrite (R $ to_semiring_unique f _), (R $ to_semiring_unique g _). Qed.

Lemma morphisms_involutive `{Naturals (N:=N)} `{CommutativeSemiRing (R:=R)}
  (f:R ⇀ N) (g:N ⇀ R) `{!SemiRing_Morphism R N f} `{!SemiRing_Morphism N R g} x `{x ∊ N} :
  f (g x) = x.
Proof to_semiring_unique_alt (f ∘ g) id x.

Lemma to_semiring_involutive `{Naturals (N:=N)} `{Naturals (N:=N2)} x `{x ∊ N} :
  naturals_to_semiring N2 N (naturals_to_semiring N N2 x) = x.
Proof morphisms_involutive (naturals_to_semiring N2 N) (naturals_to_semiring N N2) x.
Arguments to_semiring_involutive {_ _ _ _ _ _} N {_ _ _ _ _ _ _ _} N2 {_ _} x {_}.

Lemma to_semiring_twice `{Naturals (N:=N)} `{CommutativeSemiRing (R:=R1)} `{CommutativeSemiRing (R:=R2)}
  (f:R1 ⇀ R2) (g:N ⇀ R1) (h:N ⇀ R2) `{!SemiRing_Morphism R1 R2 f} `{!SemiRing_Morphism N R1 g} `{!SemiRing_Morphism N R2 h} x `{x ∊ N} :
  f (g x) = h x.
Proof to_semiring_unique_alt (f ∘ g) h x.

Lemma to_semiring_self `{Naturals (N:=N)} (f:N ⇀ N) `{!SemiRing_Morphism N N f} x `{x ∊ N} : f x = x.
Proof to_semiring_unique_alt f id x.

Lemma to_semiring_injective `{Naturals (N:=N)} `{CommutativeSemiRing (R:=R)}
   (f:R ⇀ N) (g:N ⇀ R) `{!SemiRing_Morphism R N f} `{!SemiRing_Morphism N R g}: Injective N R g.
Proof.
  repeat (split; try apply _).
  intros x ? y ? E.
  rewrite_on N <- (morphisms_involutive f g x), <- (morphisms_involutive f g y).
  now rewrite_on R -> E.
Qed.

Instance naturals_to_naturals_injective `{Naturals (N:=N)} `{Naturals (N:=N2)} (f:N ⇀ N2) `{!SemiRing_Morphism N N2 f}:
  Injective N N2 f | 15.
Proof to_semiring_injective (naturals_to_semiring N2 N) f.

Section retract_is_nat.
  Local Open Scope mc_fun_scope.
  Context `{Naturals (N:=N)} `{CommutativeSemiRing (R:=SR)}.
  Context (f:N ⇀ SR) {inv_f:Inverse f} `{!Surjective N SR f} `{!SemiRing_Morphism N SR f} `{!SemiRing_Morphism SR N (f⁻¹)}.

  (* If we make this an instance, instance resolution will loop *)
  Definition retract_is_nat_to_sr : NaturalsToSemiRing SR := λ _ R _ _ _ _ , naturals_to_semiring N R ∘ f⁻¹.

  Lemma retract_is_nat : Naturals SR (U:=retract_is_nat_to_sr).
  Proof. split; [ apply _ |..]; intros; unfold naturals_to_semiring, retract_is_nat_to_sr. apply _.
    intros x y F. unfold_sigs. red_sig. rewrite_on SR -> F. subtransitivity ((h ∘ (f ∘ f⁻¹)) y).
    unfold compose. now rewrite_on SR -> (surjective_applied f y).
    exact (to_semiring_unique (h ∘ f) (f⁻¹ y)).
  Qed.
End retract_is_nat.

Section contents.
Context `{Naturals (N:=N)} `{UnEq _} `{!DenialInequality N}.

Section borrowed_from_nat.

  Notation nat := (every nat).

  Local Ltac quote_to_nat := quote_inj (naturals_to_semiring N nat).
  Local Ltac simplify_N := preserves_simplify (naturals_to_semiring nat N).
  Local Ltac var n := generalize (naturals_to_semiring N nat n); clear dependent n.

  Lemma induction
    P `{!Proper ((N,=) ==> iff) P}:
    P 0 → (∀ `{n ∊ N}, P n → P (1 + n)) → ∀ `{n ∊ N}, P n.
  Proof.
    intros ? IH n ?.
    rewrite_on N <- (morphisms_involutive (naturals_to_semiring nat N) (naturals_to_semiring N nat) n). var n.
    apply nat_induction; intros; simplify_N. assumption. now apply (IH _ _).
  Qed.

  Global Instance: Biinduction N.
  Proof. intros ? ? ? IH n ?. apply (induction P); trivial. intros n' ?. apply (IH n' _). Qed.

  Global Instance: ∀ `{z ∊ N}, LeftCancellation (+) z N.
  Proof. intros z ? x ? y ?. quote_to_nat. apply Plus.plus_reg_l. Qed.

  Global Instance: ∀ `{z ∊ N}, RightCancellation (+) z N.
  Proof. intros. apply right_cancel_from_left. Qed.

  Global Instance: ∀ `{z ∊ N ₀}, LeftCancellation (.*.) z N.
  Proof. intros z [? E] x ? y ?.
    rewrite (denial_inequality _ _) in E. red in E. generalize E.
    quote_to_nat. var y. var x. var z.
    intros z y x E. assert (z ∊ nat ₀). split. apply _. trivial.
    exact (left_cancellation (.*.) z nat _ _).
  Qed.

  Global Instance: ∀ `{z ∊ N ₀}, RightCancellation (.*.) z N.
  Proof. intros. apply right_cancel_from_left. Qed.

  Instance nat_nontrivial: 1 ∊ N ₀.
  Proof. split. apply _. red. rewrite (denial_inequality _ _). now quote_to_nat. Qed.

  Lemma zero_sum x `{x ∊ N} y `{y ∊ N} : x + y = 0 → x = 0 ∧ y = 0.
  Proof. quote_to_nat. apply Plus.plus_is_O. Qed.

  Lemma one_sum x `{x ∊ N} y `{y ∊ N} : x + y = 1 → (x = 1 ∧ y = 0) ∨ (x = 0 ∧ y = 1).
  Proof. quote_to_nat. intros. edestruct Plus.plus_is_one; eauto. Qed.

  Global Instance: ZeroProduct N.
  Proof. intros x ? y ?. quote_to_nat. intros E. destruct (Mult.mult_is_O _ _ E); intuition. Qed.

End borrowed_from_nat.

Lemma nat_1_plus_ne_0 x `{x ∊ N} : ¬ 1 + x = 0.
Proof. intro E. destruct (zero_sum 1 x E).
  destruct nat_nontrivial as [_ T]. rewrite (denial_inequality _ _) in T. contradiction.
Qed.

Global Program Instance: StrongSubDecision N N (=) | 10 := λ x y,
  match decide (naturals_to_semiring _ (every nat) x = naturals_to_semiring _ (every nat) y) with
  | left E => left _
  | right E => right _
  end.
Next Obligation. rewrite_on N <-(to_semiring_involutive _ (every nat) x), <-(to_semiring_involutive _ (every nat) y). now rewrite E. Qed.
Next Obligation. intro E2. destruct E. now rewrite_on N -> E2. Qed.

Section with_a_ring.
  Context `{CommutativeRing (R:=R)} (f:N ⇀ R) `{!SemiRing_Morphism N R f} `{!Injective N R f}.

  Lemma to_ring_zero_sum x `{x ∊ N} y `{y ∊ N} : -f x = f y → x = 0 ∧ y = 0.
  Proof.
    intros E. apply (zero_sum _ _). apply (injective f _ _).
    preserves_simplify f. rewrite_on R <- E. exact (plus_negate_r _).
  Qed.

  Lemma negate_to_ring x `{x ∊ N} y `{y ∊ N} : -f x = f y → f x = f y.
  Proof. intros E. destruct (to_ring_zero_sum x y E) as [E2 E3]. now rewrite_on N -> E2, E3. Qed.
End with_a_ring.
End contents.

(* Due to bug #2528 *)
Hint Extern 6 (1 ∊ _ ₀) => eapply @nat_nontrivial : typeclass_instances.
(*
Hint Extern 6 (PropHolds (1 ≶ 0)) => eapply @nat_nontrivial_apart : typeclass_instances.
*)

Ltac nat_induction n E :=
  pattern n; apply induction; [solve_proper | | | trivial]; clear dependent n; [| intros n ? E].
