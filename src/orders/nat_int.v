Require Import
  abstract_algebra interfaces.naturals interfaces.orders
  theory.setoids theory.common_props theory.naturals theory.rings peano_naturals.
Require Import stdlib_ring misc.quote.
Require Export
  orders.semirings.

(*
We axiomatize the order on the naturals and the integers as a non trivial
pseudo semiring order that satisfies the biinduction principle. We prove
some results that hold for the order on the naturals and the integers.
In particular, we show that given another non trivial pseudo semiring order
(that not necessarily has to satisfy the biinduction principle, for example
the rationals or the reals), any morphism to it is an order embedding.
*)
Section to_semiring_nonneg.
  Context `{Naturals (N:=N)} `{SemiRingOrder (R:=R)} `{1 ∊ R⁺}
    {f: N ⇀ R} `{!SemiRing_Morphism N R f}.
  Instance: SemiRing R := srorder_semiring.

  Instance to_semiring_nonneg n `{n ∊ N} : f n ∊ R⁺.
  Proof.
    pose proof srorder_semiring (R:=R).
    generalize dependent n. apply naturals.induction; [ solve_proper |..];
    intros; preserves_simplify f; apply _.
  Qed.

  Lemma to_semiring_nonneg_mor : SemiRing_Morphism N R⁺ f.
  Proof. apply semiring_morphism_alt; try apply _.
  + intros ?? E. unfold_sigs. red_sig. now rewrite_on N -> E.
  + exact preserves_plus.
  + exact preserves_mult.
  + exact preserves_0.
  + firstorder.
  Qed.
End to_semiring_nonneg.

Section nat_int_order.
Context `{FullPseudoSemiRingOrder (R:=R)} `{!CommutativeSemiRing R} `{!Biinduction R} `{1 ∊ R ₀}.

Add Ring R : (stdlib_semiring_theory R).

Existing Instance to_semiring_nonneg.

(* Hmm, can we avoid using nat here? *)
Notation nat := (every nat).
Notation "#" := (naturals_to_semiring nat R).
Ltac pres_simp := preserves_simplify #.

Lemma nat_int_to_semiring x `{x ∊ R} : ∃ z, x = #z ∨ x + #z = 0.
Proof. generalize dependent x. apply biinduction. solve_proper.
  exists (0:nat). left. now pres_simp.
  intros n ?. split.
  + intros [z [Ez|Ez]].
    - exists (1+z). left. pres_simp. now rewrite_on R -> Ez.
    - destruct z as [|z].
      * exists (1:nat). left. rewrite O_nat_0, (R $ preserves_0), (R $ plus_0_r _) in Ez.
        pres_simp. rewrite_on R -> Ez. exact (plus_0_r _).
      * exists z. right. rewrite_on R <- Ez. rewrite S_nat_1_plus. pres_simp. setring R.
  + intros [z [Ez|Ez]].
    - destruct z as [|z].
      * exists (1:nat). right. rewrite O_nat_0, (R $ preserves_0) in Ez.
        pres_simp. rewrite_on R <- Ez. exact (commutativity (+) _ _).
      * exists z. left. apply (left_cancellation (+) 1 R _ _).
        rewrite (R $ Ez), S_nat_1_plus. now pres_simp.
    - exists (1+z). right. pres_simp. rewrite_on R <- Ez. setring R.
Qed.

Lemma nat_int_nonneg_decompose x `{x ∊ R⁺} : ∃ z, x = # z.
Proof. destruct (nat_int_to_semiring x) as [z [Ez1 | Ez2]]. now exists z.
  exists (0:nat). pres_simp. apply (antisymmetry (≤) _ _); [|firstorder].
  rewrite_on R <- Ez2. apply (nonneg_plus_le_compat_r _ _).
Qed.

Lemma nat_int_le_plus x `{x ∊ R} y `{y ∊ R} : x ≤ y ↔ ∃ z, y = x + # z.
Proof.
  split.
   intros E. destruct (decompose_le E) as [z [? Ez]].
   destruct (nat_int_nonneg_decompose z) as [u Eu].
   exists u. now rewrite_on R <-Eu.
  intros [z Ez]. rewrite_on R -> Ez.
  apply (nonneg_plus_le_compat_r _ _).
Qed.

Lemma nat_int_lt_plus x `{x ∊ R} y `{y ∊ R} : x < y ↔ ∃ z, y = x + 1 + # z.
Proof.
  split.
   intros E. destruct (proj1 (nat_int_le_plus x y)) as [[|z] Ez].
     now apply lt_le.
    rewrite O_nat_0, (R $ preserves_0), (R $ plus_0_r _) in Ez.
    now destruct (lt_ne_flip x y).
   exists z. rewrite_on R -> Ez. rewrite S_nat_1_plus. pres_simp. exact (associativity (+) _ _ _).
  intros [z Ez]. rewrite_on R -> Ez.
  apply (nonneg_plus_lt_compat_r _ _ _).
  apply (pos_plus_lt_compat_r _ _).
Qed.

Lemma lt_iff_plus_1_le x `{x ∊ R} y `{y ∊ R} : x < y ↔ x + 1 ≤ y.
Proof. now rewrite (nat_int_lt_plus _ _), (nat_int_le_plus _ _). Qed.

Lemma lt_iff_S_le x `{x ∊ R} y `{y ∊ R} : x < y ↔ 1 + x ≤ y.
Proof. rewrite_on R -> (commutativity (+) 1 x). now apply lt_iff_plus_1_le. Qed.

Lemma pos_ge_1 x `{x ∊ R₊} : 1 ≤ x.
Proof.
  rewrite_on R <-(plus_0_l 1). apply (lt_iff_plus_1_le _ _). firstorder.
Qed.

Lemma ge_1_pos x `{x ∊ R} : 1 ≤ x → x ∊ R₊.
Proof.
  intros E. split. apply _. red. apply (lt_le_trans _ 1 _); [exact lt_0_1 | easy].
Qed.

Lemma le_iff_lt_plus_1 x `{x ∊ R} y `{y ∊ R} : x ≤ y ↔ x < y + 1.
Proof.
  split; intros E.
   apply (lt_iff_plus_1_le _ _). now apply (order_preserving (+1)).
  apply (order_reflecting (+1) _ _). now apply (lt_iff_plus_1_le _ _).
Qed.

Lemma le_iff_lt_S x `{x ∊ R} y `{y ∊ R} : x ≤ y ↔ x < 1 + y.
Proof. rewrite (R $ commutativity (+) _ _). now apply le_iff_lt_plus_1. Qed.

Section another_semiring.
  Context `{FullPseudoSemiRingOrder (R:=R2)} `{!CommutativeSemiRing R2} `{1 ∊ R2 ₀}.
  Context {f : R ⇀ R2} `{!SemiRing_Morphism R R2 f}.

  Instance: OrderPreserving R R2 f.
  Proof.
    repeat (split; try apply _).
    intros x ? y ? E. apply (nat_int_le_plus _ _) in E. destruct E as [z E].
    rewrite_on R -> E. preserves_simplify f. rewrite_on R2 -> (naturals.to_semiring_twice f _ _ z).
    apply (nonneg_plus_le_compat_r _ _).
  Qed.

  Global Instance nat_int_strictly_order_preserving : StrictlyOrderPreserving R R2 f | 50.
  Proof.
    repeat (split; try apply _).
    intros x ? y ? E. apply (nat_int_lt_plus _ _) in E. destruct E as [z E].
    rewrite_on R -> E. preserves_simplify f. rewrite_on R2 -> (naturals.to_semiring_twice f _ _ z).
    apply (nonneg_plus_lt_compat_r _ _ _). apply (pos_plus_lt_compat_r _ _).
  Qed.

  Instance nat_int_injective `{!DenialInequality R} : StrongInjective R R2 f.
  Proof pseudo_order_dec_preserving_inj.

  Global Instance nat_int_order_embedding : OrderEmbedding R R2 f | 50.
  Proof. split; try apply _. apply full_pseudo_order_reflecting. Qed.

End another_semiring.
End nat_int_order.

Hint Extern 5 (naturals_to_semiring _ _ _ ∊ _⁺) => eapply @to_semiring_nonneg : typeclass_instances.

Hint Extern 5 (StrictlyOrderPreserving _ _ (naturals_to_semiring _ _)) => eapply @nat_int_strictly_order_preserving : typeclass_instances.
Hint Extern 5 (StrongInjective _ _ (naturals_to_semiring _ _)) => eapply @nat_int_injective : typeclass_instances.
Hint Extern 5 (OrderEmbedding _ _ (naturals_to_semiring _ _)) => eapply @nat_int_order_embedding : typeclass_instances.
