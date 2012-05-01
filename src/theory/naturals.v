Require Import
  abstract_algebra peano_naturals theory.subsetoids theory.common_props theory.jections theory.rings
  misc.quote.
Require Export
  interfaces.naturals.

Lemma to_semiring_unique `{Naturals (N:=N)} `{CommutativeSemiRing (R:=R)} f `{!SemiRing_Morphism f N R} x `{x ∊ N} :
  f x = naturals_to_semiring N R x.
Proof. apply (naturals_initial f). now red_sig. Qed.

Lemma to_semiring_unique_alt `{Naturals (N:=N)} `{CommutativeSemiRing (R:=R)}
  f g `{!SemiRing_Morphism f N R} `{!SemiRing_Morphism g N R} x `{x ∊ N} :
  f x = g x.
Proof. now rewrite (to_semiring_unique f _), (to_semiring_unique g _). Qed.

Lemma morphisms_involutive `{Naturals (N:=N)} `{CommutativeSemiRing (R:=R)}
  f g `{!SemiRing_Morphism f R N} `{!SemiRing_Morphism g N R} x `{x ∊ N} :
  f (g x) = x.
Proof to_semiring_unique_alt (f ∘ g) id x.

Lemma to_semiring_involutive `{Naturals (N:=N)} `{Naturals (N:=N2)} x `{x ∊ N} :
  naturals_to_semiring N2 N (naturals_to_semiring N N2 x) = x.
Proof morphisms_involutive (naturals_to_semiring N2 N) (naturals_to_semiring N N2) x.
Arguments to_semiring_involutive {_ _ _ _ _ _} N {_ _ _ _ _ _ _ _} N2 {_ _} x {_}.

Lemma to_semiring_twice `{Naturals (N:=N)} `{CommutativeSemiRing (R:=R1)} `{CommutativeSemiRing (R:=R2)}
  f g h `{!SemiRing_Morphism f R1 R2} `{!SemiRing_Morphism g N R1} `{!SemiRing_Morphism h N R2} x `{x ∊ N} :
  f (g x) = h x.
Proof to_semiring_unique_alt (f ∘ g) h x.

Lemma to_semiring_self `{Naturals (N:=N)} f `{!SemiRing_Morphism f N N} x `{x ∊ N} : f x = x.
Proof to_semiring_unique_alt f id x.

Lemma to_semiring_injective `{Naturals (N:=N)} `{CommutativeSemiRing (R:=R)}
   f g `{!SemiRing_Morphism f R N} `{!SemiRing_Morphism g N R}: Injective g N R.
Proof.
  repeat (split; try apply _).
  intros x ? y ? E.
  rewrite <- (morphisms_involutive f g x), <- (morphisms_involutive f g y).
  now rewrite_on R -> E.
Qed.

Instance naturals_to_naturals_injective `{Naturals (N:=N)} `{Naturals (N:=N2)} f `{!SemiRing_Morphism f N N2}:
  Injective f N N2 | 15.
Proof. now apply (to_semiring_injective (naturals_to_semiring N2 N) _). Qed.

Section retract_is_nat.
  Local Open Scope mc_fun_scope.
  Context `{Naturals (N:=N)} `{CommutativeSemiRing (R:=SR)}.
  Context f {inv_f:Inverse f} `{!Surjective f N SR} `{!SemiRing_Morphism f N SR} `{!SemiRing_Morphism (f⁻¹) SR N}.

  (* If we make this an instance, instance resolution will loop *)
  Definition retract_is_nat_to_sr : NaturalsToSemiRing SR := λ _ R _ _ _ _ , naturals_to_semiring N R ∘ f⁻¹.

  Lemma retract_is_nat : Naturals SR (U:=retract_is_nat_to_sr).
  Proof. split; [ apply _ |..]; intros; unfold naturals_to_semiring, retract_is_nat_to_sr. apply _.
    intros x y F. unfold_sigs. rewrite_on SR -> F. transitivity ((h ∘ (f ∘ f⁻¹)) y).
    unfold compose. now rewrite_on SR -> (surjective_applied f y).
    exact (to_semiring_unique (h ∘ f) (f⁻¹ y)).
  Qed.
End retract_is_nat.

Section contents.
Context `{Naturals A (N:=N)} `{UnEq A} `{!StandardUnEq A}.

Section borrowed_from_nat.

  Notation Nat := (Every nat).

  Local Ltac quote_to_nat := quote_inj (naturals_to_semiring N Nat) N (Nat).
  Local Ltac simplify_N := preserves_simplify (naturals_to_semiring Nat N) (Nat) N.
  Local Ltac var n := generalize (naturals_to_semiring N Nat n); clear dependent n.

  Lemma induction
    P `{!Proper ((N,=) ==> iff) P}:
    P 0 → (∀ `{n ∊ N}, P n → P (1 + n)) → ∀ `{n ∊ N}, P n.
  Proof.
    intros ? IH n ?. quote_to_nat. rewrite_on N <-(to_semiring_involutive _ Nat n). var n.
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
    rewrite standard_uneq in E. red in E. generalize E.
    quote_to_nat. var y. var x. var z.
    intros z y x E. assert (z ∊ Nat ₀). split. apply _. trivial.
    exact (left_cancellation (.*.) z Nat _ _).
  Qed.

  Global Instance: ∀ `{z ∊ N ₀}, RightCancellation (.*.) z N.
  Proof. intros. apply right_cancel_from_left. Qed.

  Instance nat_nontrivial: PropHolds ((1:A) ≠ 0).
  Proof. red. rewrite standard_uneq. now quote_to_nat. Qed.

  Lemma zero_sum x `{x ∊ N} y `{y ∊ N} : x + y = 0 → x = 0 ∧ y = 0.
  Proof. quote_to_nat. apply Plus.plus_is_O. Qed.

  Lemma one_sum x `{x ∊ N} y `{y ∊ N} : x + y = 1 → (x = 1 ∧ y = 0) ∨ (x = 0 ∧ y = 1).
  Proof. quote_to_nat. intros. edestruct Plus.plus_is_one; eauto. Qed.

  Global Instance: ZeroProduct N.
  Proof. intros x ? y ?. quote_to_nat. intros E. destruct (Mult.mult_is_O _ _ E); intuition. Qed.

End borrowed_from_nat.

Lemma nat_1_plus_ne_0 x `{x ∊ N} : ¬ 1 + x = 0.
Proof. intro E. destruct (zero_sum 1 x E).
  pose proof nat_nontrivial as T. rewrite standard_uneq in T. contradiction.
Qed.

Global Program Instance: SubDecision (=) N N | 10 := λ x _ y _,
  match decide (naturals_to_semiring _ (Every nat) x = naturals_to_semiring _ (Every nat) y) with
  | left E => left _
  | right E => right _
  end.
Next Obligation. now rewrite <-(to_semiring_involutive _ (Every nat) x), <-(to_semiring_involutive _ (Every nat) y), E. Qed.
Next Obligation. intro E2. destruct E. now rewrite_on N -> E2. Qed.

Section with_a_ring.
  Context `{CommutativeRing (R:=R)} `{!SemiRing_Morphism f N R} `{!Injective f N R}.

  Lemma to_ring_zero_sum x `{x ∊ N} y `{y ∊ N} :
    -f x = f y → x = 0 ∧ y = 0.
  Proof.
    intros E. apply (zero_sum _ _). apply (injective f _ _).
    preserves_simplify f N R. rewrite_on R <- E.
    exact (plus_negate_r _).
  Qed.

  Lemma negate_to_ring x `{x ∊ N} y `{y ∊ N} :
    -f x = f y → f x = f y.
  Proof.
    intros E. destruct (to_ring_zero_sum x y E) as [E2 E3].
    rewrite_on N -> E2. now rewrite_on N -> E3.
  Qed.
End with_a_ring.
End contents.

(* Due to bug #2528 *)
Hint Extern 6 (PropHolds (1 ≠ 0)) => eapply @nat_nontrivial : typeclass_instances.
(*
Hint Extern 6 (PropHolds (1 ≶ 0)) => eapply @nat_nontrivial_apart : typeclass_instances.
*)
