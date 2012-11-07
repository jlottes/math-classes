Require
  theory.naturals.
Require Import
  abstract_algebra interfaces.naturals interfaces.orders
  theory.setoids theory.common_props theory.rings orders.rings.
Require Import misc.quote.
Require Export
  orders.nat_int.

Section naturals_order.
Context `{Naturals (N:=N)} `{UnEq _} `{Le _} `{Lt _} `{!StandardUnEq N} `{!FullPseudoSemiRingOrder N}.

Instance nat_nonneg x `{x ∊ N} : x ∊ N⁺.
Proof. now apply (to_semiring_nonneg (f:=id)). Qed.

Lemma nat_le_plus `{x ∊ N} `{y ∊ N} : x ≤ y ↔ ∃ `{z ∊ N}, y = x + z.
Proof.
  split; intros E.
   destruct (decompose_le E) as [z [? Ez]]. now exists_sub z.
  destruct E as [z [? Ez]]. exact (compose_le x y z Ez).
Qed.

Lemma nat_not_neg x `{x ∊ N} : ¬ x ∊ N₋.
Proof nonneg_not_neg x.

Lemma nat_0_or_pos x `{x ∊ N} : x = 0 ∨ x ∊ N₊.
Proof.
  destruct (trichotomy (<) x 0) as [?|[?|?]].
  destruct (nat_not_neg x); firstorder.
  now left.
  right. firstorder.
Qed.

Lemma nat_0_or_ge_1 x `{x ∊ N} : x = 0 ∨ 1 ≤ x.
Proof. destruct (nat_0_or_pos x); [left|right]. trivial. exact (pos_ge_1 x). Qed.

Lemma nat_ne_0_pos x `{x ∊ N ₀} : x ∊ N₊.
Proof. destruct (_:x ∊ N ₀) as [_ E]. rewrite (standard_uneq _ _) in E.
  destruct (nat_0_or_pos x); intuition.
Qed.

Lemma nat_ne_0_ge_1 x `{x ∊ N ₀} : 1 ≤ x.
Proof. pose proof nat_ne_0_pos x. exact (pos_ge_1 x). Qed.

Lemma nat_ge_1_ne_0 x `{x ∊ N} : 1 ≤ x → x ∊ N ₀.
Proof. intro E. pose proof ge_1_pos x E. apply _. Qed.

Global Instance: ∀ `{z ∊ N ₀}, OrderReflecting N N (z *.).
Proof. intros z ?. pose proof nat_ne_0_pos z. apply _. Qed.

Global Program Instance slow_nat_le_dec: StrongSubDecision N N (≤) | 10 := λ x y,
  match decide (naturals_to_semiring N (every nat) x ≤ naturals_to_semiring N (every nat) y) with
  | left E => left _
  | right E => right _
  end.
Next Obligation. now apply (order_reflecting (naturals_to_semiring N (every nat))). Qed.

Section another_ring.
  Context `{Ring B (R:=R)} `{UnEq B} `{Le B} `{Lt B} `{!FullPseudoSemiRingOrder R}
    {f : N ⇀ R} `{!SemiRing_Morphism N R f}.

  Existing Instance to_semiring_nonneg.

  Lemma negate_to_ring_nonpos n `{n ∊ N} : -f n ∊ R⁻.
  Proof nonneg_negate _.

  Lemma between_to_ring n `{n ∊ N} : -f n ≤ f n.
  Proof between_nonneg _.
End another_ring.
End naturals_order.

Hint Extern 20 (_ ∊ _⁺) => eapply @nat_nonneg : typeclass_instances.

(* A default order on the naturals *)
Instance nat_le `{Naturals (N:=N)} : Le _ | 11 :=  λ x y, ∃ `{z ∊ N}, x + z = y.
Instance nat_lt `{Naturals A (N:=N)} `{UnEq A} : Lt A | 11 := dec_lt.

Section default_order.
Context `{Naturals (N:=N)} `{UnEq _} `{!StandardUnEq N}.

Instance: Proper ((N,=) ==> (N,=) ==> impl) (≤).
Proof.
  intros x1 y1 E1 x2 y2 E2 [z [? p]]. do 2 red. exists_sub z.
  unfold_sigs. now rewrite_on N <- E1, <- E2.
Qed.

Instance: PartialOrder N.
Proof. split. apply _. apply _.
+ intros x ?. do 2 red. exists_sub 0. exact (plus_0_r _).
+ intros x ? y ? z ? [a [? Ea]] [b [? Eb]]. do 2 red. exists_sub (a+b).
  rewrite (N $ associativity (+) _ _ _). now rewrite_on N -> Ea, Eb.
+ intros x ? y ? [a [? Ea]] [b [? Eb]].
  destruct (naturals.zero_sum a b) as [E1 E2].
    apply (left_cancellation (+) x N _ _).
    rewrite (N $ associativity (+) _ _ _). now rewrite_on N -> Ea, Eb, (plus_0_r x).
  now rewrite_on N <- Ea, E1, (plus_0_r x).
Qed.

Instance: SemiRingOrder N.
Proof. split. apply _. apply _.
+ intros x ? y ? [a [? Ea]]. now exists_sub a.
+ intros z ?. split; (split; [split; apply _ |]); intros x ? y ? [a [? Ea]]; do 2 red; exists_sub a.
  rewrite_on N <- Ea. subsymmetry. exact (associativity (+) _ _ _).
  apply (left_cancellation (+) z N _ _). now rewrite (N $ associativity (+) _ _ _).
+ intros x ? y ?. split. apply _. do 3 red. exists_sub (x*y). exact (plus_0_l _).
Qed.

Notation n_to_sr := (naturals_to_semiring N (every nat)).

Instance: TotalRelation N (≤).
Proof.
  assert (∀ `{x ∊ N} `{y ∊ N}, n_to_sr x ≤ n_to_sr y → x ≤ y) as P.
   intros x ? y ? E.
   destruct (decompose_le E) as [a [_ Ea]].
   do 2 red. exists_sub (naturals_to_semiring (every nat) N a).
   apply (injective n_to_sr _ _). preserves_simplify (n_to_sr).
   now rewrite (naturals.to_semiring_involutive _ _ _).
  intros x ? y ?.
  destruct (total (≤) (n_to_sr x) (n_to_sr y)); [left | right]; now apply P.
Qed.

Global Instance: FullPseudoSemiRingOrder N.
Proof. now apply dec_full_pseudo_srorder. Qed.
End default_order.
