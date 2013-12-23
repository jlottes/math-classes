Require Import
  abstract_algebra interfaces.naturals interfaces.orders
  interfaces.additional_operations
  theory.setoids theory.strong_rings
  theory.naturals orders.naturals
  implementations.stdlib_binary_naturals.

Notation bN := (every BinNums.N).

Section contents.
  Context `{Naturals (N:=N)}.

  Notation "#" := (naturals_to_semiring N bN).
  Notation "%" := (naturals_to_semiring bN N).

  Instance nat_div_slow : DivEuclid _ := λ x y, % (# x `div` # y).
  Instance nat_mod_slow : ModEuclid _ := λ x y, % (# x `mod` # y).

  Context `{UnEq _} `{!DenialInequality N}.
  Context `{Le _} `{Lt _} `{!FullPseudoSemiRingOrder N}.

  Instance nat_euclid_slow : EuclidSpec N.
  Proof. unfold nat_div_slow, nat_mod_slow. split.
  + unfold div_euclid at 1. apply binary_morphism_proper_back.
    intros x1 x2 Ex y1 y2 Ey. unfold_sigs. red_sig.
    cut ((bN,=)%signature (# x1 `div` # y1) (# x2 `div` # y2)). intro E. now rewrite E.
    apply (_ : Proper ((bN,=)==>(bN ₀,=)==>(bN,=)) (@div_euclid _ N_div)); red_sig.
    now rewrite (N $ Ex). now rewrite (N $ Ey).
  + unfold mod_euclid at 1. apply binary_morphism_proper_back.
    intros x1 x2 Ex y1 y2 Ey. unfold_sigs. red_sig.
    cut ((bN,=)%signature (# x1 `mod` # y1) (# x2 `mod` # y2)). intro E. now rewrite E.
    apply (_ : Proper ((bN,=)==>(bN ₀,=)==>(bN,=)) (@mod_euclid _ N_mod)); red_sig.
    now rewrite (N $ Ex). now rewrite (N $ Ey).
  + unfold div_euclid at 1, mod_euclid at 1. intros x ? y ?.
    rewrite <-(N $ naturals.morphisms_involutive % # x) at 1.
    rewrite <-(N $ naturals.morphisms_involutive % # y) at 1.
    rewrite <-(_ $ preserves_mult _ _), <-(_ $ preserves_plus _ _).
    now rewrite <-( bN $ div_mod (# x) (# y) ).
  + unfold mod_euclid at 1 3 5 7. intros x ? y ?.
    destruct (mod_rem (# x) (# y)) as [[??]|[??]].
    * left. split. now destruct (nat_nonneg (% (# x `mod` # y))).
      rewrite <-(N $ naturals.morphisms_involutive % # y) at 2.
      now apply (strictly_order_preserving % _ _).
    * destruct (nat_not_neg (# y)). split. apply _.
      now apply (lt_le_trans _ (# x `mod` # y) _).
  Qed.
End contents.

Hint Extern 25 (DivEuclid ?A) =>
  let H := constr:(_ : Naturals (A:=A) _) in
  match type of H with @Naturals A ?p ?m ?z ?o ?e ?N ?U =>
    exact (@nat_div_slow A p m z o N U)
  end : typeclass_instances.
Hint Extern 25 (ModEuclid ?A) =>
  let H := constr:(_ : Naturals (A:=A) _) in
  match type of H with @Naturals A ?p ?m ?z ?o ?e ?N ?U =>
    exact (@nat_mod_slow A p m z o N U)
  end : typeclass_instances.
Hint Extern 2 (EuclidSpec _ (d:=nat_div_slow) (m:=nat_mod_slow)) => eapply @nat_euclid_slow : typeclass_instances.

