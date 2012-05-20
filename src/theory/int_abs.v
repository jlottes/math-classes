Require Import
  interfaces.naturals abstract_algebra interfaces.orders
  orders.nat_int theory.setoids theory.integers theory.rings orders.rings.

Lemma int_abs_el `{IntAbs (Z:=Z) (N:=N)} x `{x ∊ Z} : int_abs Z N x ∊ N.
Proof. unfold int_abs. destruct (int_abs_sig Z N x) as [[z p]|[z p]]; tauto. Qed.

Local Existing Instance int_abs_el.

Section proper.
Context `{Integers A (Z:=Z)} `{Naturals (N:=N)}.

Lemma int_abs_unique_respectful {a b : IntAbs Z N} : int_abs Z N (ia:=a) = int_abs Z N (ia:= b).
Proof. intros x y E. unfold_sigs. red_sig.
  apply (injective (naturals_to_semiring N Z) _ _). unfold int_abs, int_abs_sig.
  destruct a as [[z1 p1]|[z1 p1]], b as [[z2 p2]|[z2 p2]];
  destruct (p1 _) as [? E1], (p2 _) as [? E2]; clear p1; clear p2;
  [| subsymmetry; apply (naturals.negate_to_ring _ _ _)
   | apply (naturals.negate_to_ring _ _ _)
   | apply (injective (-) _ _)];
  rewrite_on Z -> E1,E2;
  rewrite ?(Z $ negate_involutive _); trivial; subsymmetry.
Qed.

Lemma int_abs_unique {a b: IntAbs Z N} z `{z ∊ Z} : 
  int_abs Z N (ia:=a) z = int_abs Z N (ia:= b) z.
Proof. apply int_abs_unique_respectful; now red_sig. Qed.

Lemma int_abs_proper `{!IntAbs Z N} : Setoid_Morphism Z N (int_abs Z N).
Proof. split; try apply _. exact int_abs_unique_respectful. Qed.

End proper.

Hint Extern 0 (Setoid_Morphism _ _ (int_abs _ _)) => eapply @int_abs_proper : typeclass_instances.

Section contents.
Context {A B} {Z:Subset A} {N:Subset B} {f : N ⇀ Z}.
Context `{Integers A (Z:=Z)} `{UnEq A} `{Le A} `{Lt A} `{!StandardUnEq Z} `{!FullPseudoSemiRingOrder Z}.
Context `{Naturals B (N:=N)} `{!SemiRing_Morphism N Z f} `{!IntAbs Z N}.

Existing Instance to_semiring_nonneg.

Lemma int_abs_spec x `{x ∊ Z} :
  { x ∊ Z⁺ ∧ f (int_abs Z N x) = x } + { x ∊ Z⁻ ∧ f (int_abs Z N x) = -x }.
Proof.
  unfold int_abs. destruct (int_abs_sig Z N x) as [[n p]|[n p]]; destruct (p _) as [? E]; clear p;
  [ left; split
  | right; split; [ apply (negate_nonneg_nonpos _) |]];
  rewrite_on Z <- E; try apply _; exact (naturals.to_semiring_unique _ _).
Qed.

Lemma int_abs_sig_alt x `{x ∊ Z} :
  {n | n ∊ N ∧ f n = x } + {n | n ∊ N ∧ f n = -x }.
Proof. destruct (int_abs_spec x) as [[??]|[??]]; [left|right];
  exists (int_abs Z N x); (split; [apply _|trivial]).
Qed.

Lemma int_abs_nat n `{n ∊ N} :
  int_abs Z N (f n) = n.
Proof.
  apply (injective f _ _). destruct (int_abs_spec (f n)) as [[? E]|[? E]]; intuition.
  apply (naturals.negate_to_ring _ _ _). now rewrite (Z $ E), (Z $ negate_involutive _).
Qed.

Lemma int_abs_negate_nat n `{n ∊ N} :
  int_abs Z N (-f n) = n.
Proof.
  apply (injective f _ _). destruct (int_abs_spec (-f n)) as [[? E]|[? E]].
   subsymmetry. now apply (naturals.negate_to_ring _ _ _).
  now rewrite (Z $ negate_involutive _) in E.
Qed.

Lemma int_abs_negate x `{x ∊ Z} :
  int_abs Z N (-x) = int_abs Z N x.
Proof.
  destruct (int_abs_spec x) as [[_ E]|[_ E]]; rewrite_on Z <- E at 1.
    exact (int_abs_negate_nat _). exact (int_abs_nat _).
Qed.

Lemma int_abs_0_alt x `{x ∊ Z} : int_abs Z N x = 0 ↔ x = 0.
Proof.
  split; intros E1.
   destruct (int_abs_spec x) as [[_ E2]|[_ E2]]; [| apply (flip_negate_0 _)];
    now rewrite <- (Z $ E2), (N $ E1), (Z $ preserves_0).
  rewrite (Z $ E1), <- (Z $ preserves_0 (f:=f)). exact (int_abs_nat _).
Qed.

Lemma int_abs_ne_0 x `{x ∊ Z} : ¬ int_abs Z N x = 0 ↔ x ≠ 0.
Proof. rewrite (standard_uneq _ _). destruct (int_abs_0_alt x). tauto. Qed.

Lemma int_abs_0 : int_abs Z N 0 = 0.
Proof. now apply (int_abs_0_alt 0). Qed.

Lemma int_abs_nonneg x `{x ∊ Z⁺} :
  f (int_abs Z N x) = x.
Proof.
  destruct (int_abs_spec x); intuition.
  rewrite_on Z -> (nonneg_nonpos_zero x).
  rewrite_on N -> int_abs_0.
  exact preserves_0.
Qed.

Lemma int_abs_nonpos x `{x ∊ Z⁻} :
  f (int_abs Z N x) = -x.
Proof.
  rewrite_on N <- (int_abs_negate x). exact (int_abs_nonneg (-x)).
Qed.

Lemma int_abs_1 : int_abs Z N 1 = 1.
Proof.
  apply (injective f _ _). subtransitivity (1:A).
  exact (int_abs_nonneg 1). subsymmetry. exact preserves_1.
Qed.

Lemma int_abs_nonneg_plus x `{x ∊ Z⁺} y `{y ∊ Z⁺} :
  int_abs Z N (x + y) = int_abs Z N x + int_abs Z N y.
Proof.
  apply (injective f _ _).
  now rewrite (Z $ preserves_plus _ _), !(Z $ int_abs_nonneg _).
Qed.

Lemma int_abs_mult x `{x ∊ Z} y `{y ∊ Z} :
  int_abs Z N (x * y) = int_abs Z N x * int_abs Z N y.
Proof. apply (injective f _ _). rewrite (Z $ preserves_mult _ _).
  destruct (int_abs_spec x) as [[? Ex]|[? Ex]],
     (int_abs_spec y) as [[? Ey]|[? Ey]]; rewrite_on Z -> Ex, Ey.
  + rewrite (Z $ int_abs_nonneg _). easy.
  + rewrite (Z $ int_abs_nonpos _). exact (negate_mult_distr_r _ _).
  + rewrite (Z $ int_abs_nonpos _). exact (negate_mult_distr_l _ _).
  + rewrite (Z $ int_abs_nonneg _). subsymmetry. exact (negate_mult_negate _ _).
Qed.
End contents.
