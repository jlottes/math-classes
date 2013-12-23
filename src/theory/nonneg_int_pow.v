Require Import
  abstract_algebra interfaces.naturals interfaces.orders interfaces.additional_operations
  theory.setoids theory.rings orders.semirings lattice_ordered_rings.
Require Export
  theory.nat_pow.

(* choose subsets R and Z by looking for a NonnegIntPowSpec instance *)
Hint Extern 4 (Morphism _ (@pow ?A ?B ?pw)) =>
  let X := fresh "X" in let Y := fresh "Y" in
  evar (X:@set A); evar (Y:@set B);
  let X' := eval unfold X in X in clear X;
  let Y' := eval unfold Y in Y in clear Y;
  let spec := constr:(_ : NonnegIntPowSpec X' Y' pw) in
  instantiate; eapply (nonneg_int_pow_proper (NonnegIntPowSpec:=spec))
: typeclass_instances.

Lemma nonneg_int_pow_closed `{spec:NonnegIntPowSpec (R:=R) (Z:=Z) (pw:=pw)} `{!Setoid R} `{!Setoid Z}:
  Closed (R ⇀ Z ⇀ R) (^).
Proof _.

Hint Extern 4 (@pow ?A ?B ?pw _ _ ∊ _) =>
  let X := fresh "X" in let Y := fresh "Y" in
  evar (X:@set A); evar (Y:@set B);
  let X' := eval unfold X in X in clear X;
  let Y' := eval unfold Y in Y in clear Y;
  let spec := constr:(_ : NonnegIntPowSpec X' Y' pw) in
  instantiate; eapply (nonneg_int_pow_closed (spec:=spec))
: typeclass_instances.

Section properties.
  Context `{Z:@set B} `{Le _} `{Naturals _ (N:=Z⁺)}.
  Context `{Lt _} `{UnEq _} `{!FullPseudoSemiRingOrder Z} `{!DenialInequality Z}.

  Instance: DenialInequality Z⁺.
  Proof. now rewrite (_ : Subset Z⁺ Z). Qed.

  Instance: 0 ∊ Z.
  Proof. apply (_ : Subset Z⁺ Z). apply _. Qed.

  Section semiring.
    Context `{SemiRing (R:=R)} {pw} `{!NonnegIntPowSpec R Z pw}.

    Lemma nonneg_int_pow_base_0 n `{n ∊ Z₊} : 0 ^ n = 0.
    Proof. apply (nat_pow_base_0 (N:=Z⁺)). split. apply _. red.
      apply (_ : n ∊ Z ₀).
    Qed.

    Lemma nonneg_int_pow_0 x `{x ∊ R} : x ^ 0 = 1.
    Proof nat_pow_0 (N:=Z⁺) x.

    Lemma nonneg_int_pow_S x `{x ∊ R} n `{n ∊ Z⁺} : x ^ (1 + n) = x * x ^ n.
    Proof nat_pow_S (N:=Z⁺) x n.

    Instance nonneg_int_pow_1: RightIdentity (^) 1 R.
    Proof nat_pow_1 (N:=Z⁺).

    Lemma nonneg_int_pow_2 x `{x ∊ R} : x ^ 2 = x * x.
    Proof nat_pow_2 (N:=Z⁺) x.

    Lemma nonneg_int_pow_3 x `{x ∊ R} : x ^ 3 = x * (x * x).
    Proof nat_pow_3 (N:=Z⁺) x.

    Lemma nonneg_int_pow_4 x `{x ∊ R} : x ^ 4 = x * (x * (x * x)).
    Proof nat_pow_4 (N:=Z⁺) x.

    Instance nonneg_int_pow_base_1: LeftAbsorb (^) 1 Z⁺.
    Proof nat_pow_base_1.

    Lemma nonneg_int_pow_exp_plus x `{x ∊ R} n `{n ∊ Z⁺} m `{m ∊ Z⁺} :
      x ^ (n + m) = x ^ n * x ^ m.
    Proof nat_pow_exp_plus (N:=Z⁺) x n m.

    Lemma nonneg_int_pow_exp_mult x `{x ∊ R} n `{n ∊ Z⁺} m `{m ∊ Z⁺} :
      x ^ (n * m) = (x ^ n) ^ m.
    Proof nat_pow_exp_mult (N:=Z⁺) x n m.
  End semiring.

  Section comsemiring.
    Context `{CommutativeSemiRing (R:=R)} {pw} `{!NonnegIntPowSpec R Z pw}.

    Lemma nonneg_int_pow_base_mult x `{x ∊ R} y `{y ∊ R} n `{n ∊ Z⁺} :
      (x * y) ^ n = x ^ n * y ^ n.
    Proof nat_pow_base_mult (N:=Z⁺) x y n.
  End comsemiring.

  Section default.
    Context `{Join _} `{!JoinSemiLatticeOrder Z}.
    Context `{SemiRing A (R:=R)}.

    Instance nonneg_int_pow_default : Pow A B :=
      λ x n, x ^ (naturals_to_semiring Z⁺ (every nat) (0 ⊔ n)).

    Instance: Morphism (R ⇒ Z ⇒ R) (^).
    Proof. unfold pow, nonneg_int_pow_default.
      apply binary_morphism_proper_back. intros ?? E1 m n E2. unfold_sigs. red_sig.
      rewrite (_ $ E1). mc_replace (0 ⊔ m) with (0 ⊔ n) on Z⁺. easy.
      now rewrite (_ $ E2).
    Qed.

    Instance nonneg_int_pow_default_spec : NonnegIntPowSpec R Z nonneg_int_pow_default.
    Proof. split; [| apply _]; split; [| unfold pow, nonneg_int_pow_default..].
    + apply binary_morphism_proper_back. intros ?? E1 m n E2. unfold_sigs.
      apply binary_morphism_proper; [apply _ | now red_sig..].
    + intros ??. rewrite (Z⁺ $ join_0_nonneg _), (_ $ preserves_0). exact (nat_pow_0 _).
    + intros ?? n ?. rewrite 2!(Z⁺ $ join_0_nonneg _).
      rewrite (_ $ preserves_plus _ _), (preserves_1 (f:=naturals_to_semiring  Z⁺ (every nat))).
      exact (nat_pow_S _ _).
    Qed.
  End default.

End properties.

Arguments nonneg_int_pow_1 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _ {_}.
Arguments nonneg_int_pow_base_1 {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _ {_}.

Hint Extern 2 (NonnegIntPowSpec _ _ nonneg_int_pow_default) => class_apply @nonneg_int_pow_default_spec : typeclass_instances.
Arguments nonneg_int_pow_default {_} Z {_ _ _ _ _ _ _} _ _.
Typeclasses Opaque nonneg_int_pow_default.
