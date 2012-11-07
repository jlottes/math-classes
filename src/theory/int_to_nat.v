Require Import
  interfaces.naturals abstract_algebra interfaces.orders
  orders.nat_int theory.setoids theory.integers theory.rings orders.rings.

Lemma int_to_nat_el `{IntAbs (Z:=Z) (N:=N)} `{Zero _} `{0 ∊ N} x `{x ∊ Z} : int_to_nat Z N x ∊ N.
Proof. unfold int_to_nat. destruct (int_abs_sig Z N x) as [[z p]|[z p]]; tauto. Qed.

Section proper.
Context `{Integers (Z:=Z)} `{Naturals (N:=N)}.

Hint Extern 5 (int_to_nat _ _ _ ∊ _) => eapply @int_to_nat_el : typeclass_instances.

Notation N_to_Z := (naturals_to_semiring N Z).

Lemma int_to_nat_unique_respectful {a b : IntAbs Z N} : int_to_nat Z N (ia:=a) = int_to_nat Z N (ia:= b).
Proof. intros x y E. unfold_sigs. red_sig.
  apply (injective N_to_Z _ _). unfold int_to_nat, int_abs_sig.
  destruct a as [[z1 p1]|[z1 p1]], b as [[z2 p2]|[z2 p2]];
  destruct (p1 _) as [? E1], (p2 _) as [? E2]; clear p1; clear p2;
  repeat match goal with
  | |- N_to_Z z1 = _ => rewrite_on Z -> E1
  | |- _ = N_to_Z z2 => rewrite_on Z -> E2
  | |- context [ N_to_Z 0 ] => rewrite (Z $ preserves_0)
  end;
  [ trivial | subsymmetry | | easy ];
  (destruct (naturals.to_ring_zero_sum N_to_Z z1 z2) as [Ez1 Ez2];
   [ rewrite_on Z -> E1,E2,E |]).
  easy.
  subtransitivity (N_to_Z z1). rewrite (N $ Ez1). subsymmetry. exact preserves_0.
  exact (negate_involutive _).
  subtransitivity (N_to_Z z2). rewrite (N $ Ez2). subsymmetry. exact preserves_0.
Qed.

Lemma int_to_nat_unique {a b: IntAbs Z N} z `{z ∊ Z} : 
  int_to_nat Z N (ia:=a) z = int_to_nat Z N (ia:= b) z.
Proof. apply int_to_nat_unique_respectful; now red_sig. Qed.

Lemma int_to_nat_proper `{!IntAbs Z N} : Morphism (Z ⇒ N) (int_to_nat Z N).
Proof int_to_nat_unique_respectful.

End proper.

Hint Extern 0 (Morphism _ (int_to_nat _ _)) => eapply @int_to_nat_proper : typeclass_instances.

Section contents.
Context `{Z:Subset} `{N:Subset} {f : N ⇀ Z}.
Context `{Integers _ (Z:=Z)} `{UnEq _} `{Le _} `{Lt _} `{!StandardUnEq Z} `{!FullPseudoSemiRingOrder Z}.
Context `{Naturals _ (N:=N)} `{!SemiRing_Morphism N Z f} `{!IntAbs Z N}.

Lemma int_to_nat_spec x `{x ∊ Z} :
  { x ∊ Z⁺ ∧ f (int_to_nat Z N x) = x } + { x ∊ Z⁻ ∧ f (int_to_nat Z N x) = 0 }.
Proof.
  unfold int_to_nat. destruct (int_abs_sig Z N x) as [[n p]|[n p]]; destruct (p _) as [? E]; clear p.
  left. split; rewrite_on Z <- E. apply _. exact (naturals.to_semiring_unique _ _).
  right. split. apply (negate_nonneg_nonpos _). rewrite_on Z <- E. apply _. exact preserves_0.
Qed.

Existing Instance to_semiring_nonneg.

Lemma int_to_nat_nat n `{n ∊ N} :
  int_to_nat Z N (f n) = n.
Proof.
  apply (injective f _ _). destruct (int_to_nat_spec (f n)) as [[? E]|[? E]]; intuition.
  pose proof nonneg_nonpos_zero (f n). subtransitivity (0:A). subsymmetry.
Qed.

Lemma int_to_nat_cancel_l x `{x ∊ Z} n `{n ∊ N} :
  x = f n → int_to_nat Z N x = n.
Proof. intros E. rewrite_on Z -> E. exact (int_to_nat_nat _). Qed.

Lemma int_to_nat_cancel_r x `{x ∊ Z} n `{n ∊ N} :
  f n = x → n = int_to_nat Z N x.
Proof. intros E. rewrite_on Z <- E. subsymmetry. exact (int_to_nat_nat _). Qed.

Lemma int_to_nat_0 : int_to_nat Z N 0 = 0.
Proof. apply (int_to_nat_cancel_l _ _). subsymmetry. exact preserves_0. Qed.

Lemma int_to_nat_negate_nat n `{n ∊ N} : 
  int_to_nat Z N (-f n) = 0.
Proof.
  apply (injective f _ _). destruct (int_to_nat_spec (-f n)) as [[? E]|[? E]];
  subtransitivity (0:A); try match goal with |- 0 = f 0 => subsymmetry; exact preserves_0 end.
  rewrite_on Z -> (nonneg_nonpos_zero (- f n)).
  rewrite_on N -> int_to_nat_0. exact preserves_0.
Qed. 

Lemma int_to_nat_nonneg x `{x ∊ Z⁺} :
  f (int_to_nat Z N x) = x.
Proof.
  destruct (int_to_nat_spec x); intuition.
  subtransitivity (0:A). subsymmetry. exact (nonneg_nonpos_zero x).
Qed.

Lemma int_to_nat_nonpos x `{x ∊ Z⁻} :
  f (int_to_nat Z N x) = 0.
Proof.
  destruct (int_to_nat_spec x); intuition.
  subtransitivity x. exact (nonneg_nonpos_zero x).
Qed.

Lemma int_to_nat_1 : int_to_nat Z N 1 = 1.
Proof. apply (int_to_nat_cancel_l _ _). subsymmetry. exact preserves_1. Qed.

Lemma int_to_nat_nonneg_plus x `{x ∊ Z⁺} y `{y ∊ Z⁺} :
  int_to_nat Z N (x + y) = int_to_nat Z N x + int_to_nat Z N y.
Proof.
  apply (injective f _ _).
  now rewrite (Z $ preserves_plus _ _), !(Z $ int_to_nat_nonneg _).
Qed.

Lemma int_to_nat_mult_nonneg_l x `{x ∊ Z⁺} y `{y ∊ Z} :
  int_to_nat Z N (x * y) = int_to_nat Z N x * int_to_nat Z N y.
Proof. apply (injective f _ _). rewrite (Z $ preserves_mult _ _).
  destruct (int_to_nat_spec y) as [[? Ey]|[? Ey]]; rewrite_on Z -> Ey.
  now rewrite !(Z $ int_to_nat_nonneg _).
  now rewrite (Z $ int_to_nat_nonpos _), (Z $ mult_0_r _).
Qed.

Lemma int_to_nat_mult_nonneg_r x `{x ∊ Z} y `{y ∊ Z⁺} :
  int_to_nat Z N (x * y) = int_to_nat Z N x * int_to_nat Z N y.
Proof. rewrite (Z $ commutativity (.*.) x y), (N $ commutativity (.*.) _ _).
  exact (int_to_nat_mult_nonneg_l y x).
Qed.

Context `{UnEq _} `{Le _} `{Lt _} `{!StandardUnEq N} `{!FullPseudoSemiRingOrder N}.

(*
Global Instance int_to_nat_nonneg x :
  PropHolds (0 ≤ int_to_nat Z N x).
Proof.
  destruct (int_to_nat_spec x) as [[? E]|[? E]].
   apply (order_reflecting f). now rewrite preserves_0, E.
  rewrite E. solve_propholds.
Qed.
*)

Lemma int_to_nat_pos x `{x ∊ Z₊} : int_to_nat Z N x ∊ N₊ .
Proof. split. apply _. cut (0 < x). rewrite !(lt_iff_le_ne _ _). intros [_ E].
  split. now destruct (_ : int_to_nat Z N x ∊ N⁺). contradict E.
  subtransitivity (f 0). subsymmetry. exact preserves_0.
  rewrite_on N -> E. exact (int_to_nat_nonneg x).
  firstorder.
Qed.

(*
Lemma int_to_nat_le_l x y :
  0 ≤ x → x ≤ y → f (int_to_nat Z N x) ≤ y.
Proof. intros. now rewrite int_to_nat_of_nonneg. Qed.

Lemma int_to_nat_le_cancel_l x n :
  0 ≤ x → x ≤ f n → int_to_nat Z N x ≤ n.
Proof. intros. now apply (order_reflecting f), int_to_nat_le_l. Qed.

Lemma int_to_nat_le_r x y :
  x ≤ y → x ≤ f (int_to_nat Z N y).
Proof. 
  intros E1. destruct (int_to_nat_spec y) as [[? E2]|[? E2]].
   now rewrite E2.
  rewrite E2, preserves_0. now transitivity y.
Qed.

Lemma int_to_nat_le_cancel_r x n :
  f n ≤ x → n ≤ int_to_nat Z N x.
Proof. intros. now apply (order_reflecting f), int_to_nat_le_r. Qed.

Global Instance: OrderPreserving (int_to_nat Z N).
Proof.
  repeat (split; try apply _). intros x y E.
  destruct (total (≤) 0 x).
   now apply int_to_nat_le_cancel_r, int_to_nat_le_l.
  rewrite int_to_nat_of_nonpos. solve_propholds. easy.
Qed.

Lemma int_to_nat_le_back x y :
  0 ≤ y → int_to_nat Z N x ≤ int_to_nat Z N y → x ≤ y.
Proof.
  intros. rewrite <-(int_to_nat_of_nonneg y) by easy.
  transitivity (f (int_to_nat Z N x)).
   now apply int_to_nat_le_r.
  now apply (order_preserving f).
Qed.

Lemma int_to_nat_lt_l x y :
  0 ≤ x → x < y → f (int_to_nat Z N x) < y.
Proof. intros. now rewrite int_to_nat_of_nonneg. Qed.

Lemma int_to_nat_lt_cancel_l x n :
  0 ≤ x → x < f n → int_to_nat Z N x < n.
Proof. intros. now apply (strictly_order_reflecting f), int_to_nat_lt_l. Qed.

Lemma int_to_nat_lt_r x y :
  x < y → x < f (int_to_nat Z N y).
Proof. 
  intros E1. destruct (int_to_nat_spec y) as [[? E2]|[? E2]].
   now rewrite E2.
  rewrite E2, preserves_0. now apply lt_le_trans with y.
Qed.

Lemma int_to_nat_lt_cancel_r x n :
  f n < x → n < int_to_nat Z N x.
Proof. intros. now apply (strictly_order_reflecting f), int_to_nat_lt_r. Qed.

Lemma int_to_nat_lt x y :
  0 < y → x < y → int_to_nat Z N x < int_to_nat Z N y.
Proof.
  intros Ey Exy. destruct (total (≤) 0 x).
   now apply int_to_nat_lt_cancel_r, int_to_nat_lt_l.
  rewrite int_to_nat_of_nonpos by easy. now apply int_to_nat_pos.
Qed.

Lemma int_to_nat_lt_back x y :
  0 ≤ y → int_to_nat Z N x < int_to_nat Z N y → x < y.
Proof.
  intros. rewrite <-(int_to_nat_of_nonneg y) by easy.
  apply le_lt_trans with (f (int_to_nat Z N x)).
   now apply int_to_nat_le_r.
  now apply (strictly_order_preserving f).
Qed.
*)
End contents.
