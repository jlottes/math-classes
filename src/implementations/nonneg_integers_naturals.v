Require 
  peano_naturals.
Require Import
  abstract_algebra interfaces.integers interfaces.naturals interfaces.orders
  interfaces.additional_operations 
  theory.setoids theory.rings theory.integers int_abs int_to_nat
  orders.semirings orders.rings orders.nat_int.

Local Open Scope mc_fun_scope.
Local Notation nat := (every nat).

Section nonneg_integers_naturals.
Context `{Integers A (Z:=Z)} `{UnEq A} `{Le A} `{Lt A} `{!StandardUnEq Z} `{!FullPseudoSemiRingOrder Z}.

Let of_nat := (naturals_to_semiring nat Z⁺).
Instance: Inverse of_nat := int_abs Z nat.

Instance: Setoid_Morphism Z⁺ nat of_nat⁻¹.
Proof. change (Setoid_Morphism Z⁺ nat (int_abs Z nat)). rewrite (_:Z⁺ ⊆ Z). apply _. Qed.

Instance: SemiRing_Morphism Z⁺ nat of_nat⁻¹.
Proof. apply semiring_morphism_alt; try apply _.
+ exact int_abs_nonneg_plus.
+ intros x ? y ?. exact (int_abs_mult _ _).
+ exact int_abs_0.
+ exact int_abs_1.
Qed.

Instance: Surjective nat Z⁺ of_nat.
Proof.
  split; [| apply _ | intros; apply _].
  intros x y E. unfold_sigs. unfold id, compose. red_sig.
  rewrite_on Z⁺ <- E.
  exact (int_abs_nonneg _).
Qed.

Global Instance: NaturalsToSemiRing Z⁺ := naturals.retract_is_nat_to_sr of_nat.
Global Instance: Naturals Z⁺ := naturals.retract_is_nat of_nat.

Context `{!IntAbs Z Z⁺}.

Lemma ZPos_int_abs_nonneg x `{x ∊ Z⁺} : int_abs Z Z⁺ x = x.
Proof int_abs_nonneg (f:=id:Z⁺⇀Z) x.

Lemma ZPos_int_abs_nonpos x `{x ∊ Z⁻} : int_abs Z Z⁺ x = -x.
Proof int_abs_nonpos (f:=id:Z⁺⇀Z) x.

Lemma ZPos_int_to_nat_nonneg x `{x ∊ Z⁺} : int_to_nat Z Z⁺ x = x.
Proof int_to_nat_nonneg (f:=id:Z⁺⇀Z) x.

Lemma ZPos_int_to_nat_nonpos x `{x ∊ Z⁻} : int_to_nat Z Z⁺ x = 0.
Proof int_to_nat_nonpos (f:=id:Z⁺⇀Z) x.


Instance ZPos_cut_minus : CutMinus A := λ x y, int_to_nat Z Z⁺ (x - y).

Global Instance: CutMinusSpec Z⁺ _.
Proof. split; unfold cut_minus, ZPos_cut_minus.
+ split; try apply _. intros ?? E1 ?? E2. unfold_sigs. red_sig. rewrite_on Z -> E1, E2.
  exact (subreflexivity (S:=Z⁺) _).
+ intros x ? y ? E. pose proof minus_nonneg _ _ E.
  rewrite (Z⁺ $ ZPos_int_to_nat_nonneg (x-y)).
  exact (plus_plus_negate_l _ _).
+ intros x ? y ? E. pose proof minus_nonpos _ _ E.
  exact (ZPos_int_to_nat_nonpos _).
Qed.

End nonneg_integers_naturals.
