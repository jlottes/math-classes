Require Import
  abstract_algebra interfaces.integers interfaces.naturals interfaces.orders
  interfaces.additional_operations
  the_naturals 
  theory.setoids theory.rings theory.integers int_abs int_to_nat
  orders.semirings orders.rings orders.nat_int.

Local Open Scope mc_fun_scope.
Local Notation N := the_naturals.

Section nonneg_integers_naturals.
Context `{Integers (Z:=Z)} `{UnEq _} `{Le _} `{Lt _} `{!DenialInequality Z} `{!FullPseudoSemiRingOrder Z}.

Let of_nat := (naturals_to_semiring N Z⁺).
Instance: Inverse of_nat := int_abs Z N.

Instance: Morphism (N ⇒ Z⁺) of_nat. Proof. unfold of_nat. exact _. Qed.
Instance: Morphism (N ⇒ Z) of_nat.
Proof. rewrite <-(_:Subset (N ⇒ Z⁺) (N ⇒ Z)). exact _. Qed.

Instance: SemiRing_Morphism N Z⁺ of_nat. Proof. unfold of_nat. exact _. Qed.
Instance: SemiRing_Morphism N Z of_nat.
Proof. rewrite <- ( SemiRing $ (_ : Z⁺ ⊆ Z) ). apply _. Qed.

Instance: Morphism (Z⁺ ⇒ N) of_nat⁻¹.
Proof. change (Morphism (Z⁺ ⇒ N) (int_abs Z N)).
  rewrite <-(_:Subset (Z ⇒ N) (Z⁺ ⇒ N)). apply _.
Qed.

Instance: SemiRing_Morphism Z⁺ N of_nat⁻¹.
Proof. apply semiring_morphism_alt; try apply _.
+ exact int_abs_nonneg_plus.
+ intros x ? y ?. exact (int_abs_mult _ _).
+ exact int_abs_0.
+ exact int_abs_1.
Qed.

Instance: Surjective N Z⁺ of_nat.
Proof. split; [| apply _ | intros; apply _].
  intros x y E. unfold_sigs. unfold id, compose. red_sig.
  rewrite_on Z⁺ <- E.
  exact (int_abs_nonneg _).
Qed.

Instance ZPos_to_semiring: NaturalsToSemiRing Z⁺ := naturals.retract_is_nat_to_sr of_nat.
Instance ZPos_naturals: Naturals Z⁺ := naturals.retract_is_nat of_nat.

Instance ZPos_denial_inequality: DenialInequality Z⁺.
Proof. now rewrite (_:Z⁺ ⊆ Z). Qed.

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

Instance ZPos_cut_minus_spec: CutMinusSpec Z⁺ _.
Proof. split; unfold cut_minus, ZPos_cut_minus.
+ apply binary_morphism_proper_back.
  intros ?? E1 ?? E2. unfold_sigs. red_sig. rewrite_on Z -> E1, E2.
  exact (reflexivity (S:=Z⁺) _).
+ intros x ? y ? E. pose proof minus_nonneg _ _ E.
  rewrite (Z⁺ $ ZPos_int_to_nat_nonneg (x-y)).
  exact (plus_plus_negate_l _ _).
+ intros x ? y ? E. pose proof minus_nonpos _ _ E.
  exact (ZPos_int_to_nat_nonpos _).
Qed.

Section another_semiring.
  Context `{FullPseudoSemiRingOrder (R:=R)} (f:Z ⇀ R) `{!SemiRing_Morphism Z R f}.

  Instance Zpos_semiring_mor_nonneg : SemiRing_Morphism Z⁺ R⁺ f.
  Proof to_semiring_nonneg_mor (N:=Z⁺) (f:=f).

End another_semiring.

End nonneg_integers_naturals.

Hint Extern 20 (NaturalsToSemiRing ?Z⁺) =>
  let H := constr:(_ : Integers Z) in eapply (ZPos_to_semiring (H:=H)) : typeclass_instances.
Hint Extern 20 (Naturals ?Z⁺) =>
  let H := constr:(_ : Integers Z) in eapply (ZPos_naturals (H:=H)) : typeclass_instances.
Hint Extern 20 (DenialInequality ?Z⁺) =>
  let H := constr:(_ : Integers Z) in eapply @ZPos_denial_inequality : typeclass_instances.
