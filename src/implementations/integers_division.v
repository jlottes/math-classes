Require Import
  abstract_algebra interfaces.integers interfaces.orders
  interfaces.additional_operations
  theory.setoids theory.strong_rings
  theory.integers orders.integers
  implementations.stdlib_binary_integers.

Notation bZ := (every BinNums.Z).

Section contents.
  Context `{Integers (Z:=Z)}.

  Notation "#" := (integers_to_ring Z bZ).
  Notation "%" := (integers_to_ring bZ Z).

  Instance int_div_slow : DivEuclid _ := λ x y, % (# x `div` # y).
  Instance int_mod_slow : ModEuclid _ := λ x y, % (# x `mod` # y).

  Context `{UnEq _} `{!DenialInequality Z}.
  Context `{Le _} `{Lt _} `{!FullPseudoSemiRingOrder Z}.

  Instance int_euclid_slow : EuclidSpec Z.
  Proof. unfold int_div_slow, int_mod_slow. split.
  + unfold div_euclid at 1. apply binary_morphism_proper_back.
    intros x1 x2 Ex y1 y2 Ey. unfold_sigs. red_sig.
    cut ((bZ,=)%signature (# x1 `div` # y1) (# x2 `div` # y2)). intro E. now rewrite E.
    apply (_ : Proper ((bZ,=)==>(bZ ₀,=)==>(bZ,=)) (@div_euclid _ Z_div)); red_sig.
    now rewrite (Z $ Ex). now rewrite (Z $ Ey).
  + unfold mod_euclid at 1. apply binary_morphism_proper_back.
    intros x1 x2 Ex y1 y2 Ey. unfold_sigs. red_sig.
    cut ((bZ,=)%signature (# x1 `mod` # y1) (# x2 `mod` # y2)). intro E. now rewrite E.
    apply (_ : Proper ((bZ,=)==>(bZ ₀,=)==>(bZ,=)) (@mod_euclid _ Z_mod)); red_sig.
    now rewrite (Z $ Ex). now rewrite (Z $ Ey).
  + unfold div_euclid at 1, mod_euclid at 1. intros x ? y ?.
    rewrite <-(Z $ integers.morphisms_involutive % # x) at 1.
    rewrite <-(Z $ integers.morphisms_involutive % # y) at 1.
    rewrite <-(_ $ preserves_mult _ _), <-(_ $ preserves_plus _ _).
    now rewrite <-( bZ $ div_mod (# x) (# y) ).
  + unfold mod_euclid at 1 3 5 7. intros x ? y ?.
    destruct (mod_rem (# x) (# y)) as [[??]|[??]]; [left|right]; split.
    * rewrite <-(Z $ preserves_0 (f:=%)).
      now apply (order_preserving % _ _).
    * rewrite <-(Z $ integers.morphisms_involutive % # y) at 2.
      now apply (strictly_order_preserving % _ _).
    * rewrite <-(Z $ integers.morphisms_involutive % # y) at 1.
      now apply (strictly_order_preserving % _ _).
    * rewrite <-(Z $ preserves_0 (f:=%)).
      now apply (order_preserving % _ _).
  Qed.
End contents.

Hint Extern 20 (DivEuclid ?A) =>
  let H := constr:(_ : Integers (A:=A) _) in
  match type of H with @Integers A ?p ?m ?z ?o ?n ?e ?Z ?U =>
    exact (@int_div_slow A p m z o n Z U)
  end : typeclass_instances.
Hint Extern 20 (ModEuclid ?A) =>
  let H := constr:(_ : Integers (A:=A) _) in
  match type of H with @Integers A ?p ?m ?z ?o ?n ?e ?Z ?U =>
    exact (@int_mod_slow A p m z o n Z U)
  end : typeclass_instances.
Hint Extern 2 (EuclidSpec _ (d:=int_div_slow) (m:=int_mod_slow)) => eapply @int_euclid_slow : typeclass_instances.

