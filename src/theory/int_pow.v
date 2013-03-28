Require Import
  abstract_algebra interfaces.naturals interfaces.integers
  interfaces.additional_operations interfaces.orders
  theory.strong_setoids theory.common_props theory.nat_pow theory.int_abs theory.fields
  theory.naturals orders.semirings orders.naturals orders.integers orders.fields
  implementations.nonneg_integers_naturals.
Require Import
  stdlib_ring.

Local Open Scope grp_scope. (* notation for inverse *)

Local Ltac biinduction n :=
  pattern n; apply biinduction; [solve_proper | | | trivial]; clear dependent n; [| intros n ?].

(* * Properties of Int Pow *)
Section int_pow_properties.
Context `{Field (F:=F)} `{Integers (Z:=Z)} `{UnEq _} `{Le _} `{Lt _} `{!StandardUnEq Z} `{!FullPseudoSemiRingOrder Z}.

Add Ring F : (stdlib_ring_theory F).
Add Ring Z : (stdlib_ring_theory Z).

Context `{!IntPowSpec F Z ipw}.

Instance: Naturals Z⁺ := _.

Instance int_pow_nonzero: Closed (F ₀ ⇀ Z ⇀ F ₀) (^).
Proof. intros.
  intros x ? n ?. destruct (nonneg_or_neg n). now apply (nat_pow_nonzero (N:=Z⁺)).
  assert (x^n ∊ F) by (apply int_pow_neg_closed; apply _).
  split. apply _.
  apply (strong_extensionality (.* x^(-n))).
  rewrite (F $ int_pow_neg x n), (F $ mult_0_l (x^(-n))). now destruct field_nontrivial.
Qed.

Hint Extern 4 (_ ^ _ ∊ _ ₀) => eapply @int_pow_nonzero : typeclass_instances.

Lemma int_pow_nonzero2: Closed (F ₀ ⇀ Z ⇀ F) (^).
Proof. intros ????. apply NonZero_subset. apply _. Qed.

Lemma int_pow_neg_alt x `{x ∊ F ₀} n `{n ∊ Z₋} : x ^ n = (x ^ (-n))⁻¹.
Proof. apply (right_cancellation (.*.) (x ^ (-n)) (F ₀) (x^n) _).
  now rewrite_on (F ₀) -> (int_pow_neg x n), (field_inv_l (x ^ (- n))).
Qed.

Global Instance int_pow_strong_nonzero : Strong_Binary_Morphism (F ₀) Z (F ₀) (^).
Proof. 
  split; try apply _.
  + assert (∀ `{x ∊ F ₀} `{y ∊ F ₀} `{n ∊ Z⁺} `{m ∊ Z}, n = m -> x^n ≠ y^m -> x ≠ y) as P.
      pose proof nat_pow_strong (R:=F) (N:=Z⁺).
      intros x ? y ? n ? m ? E IE.
      assert (m ∊ Z⁺) by now rewrite <- (Z $ E).
      destruct (strong_binary_extensionality (X:=F) (Y:=Z⁺) (^) IE); try trivial.
      contradict E. now rewrite <- (standard_uneq n m).
    rewrite strong_ext_equiv_2. intros x ? y ? n ? m ?.
    destruct (decide_sub (=) n m) as [E|IE]; [intro IE; left | right].
    * destruct (nonneg_or_neg n).
      - now apply (P _ _ _ _ n _ m _ E).
      - assert (m ∊ Z₋) by now rewrite <- (Z $ E).
        rewrite (F ₀ $ int_pow_neg_alt x n), (F ₀ $ int_pow_neg_alt y m) in IE.
        apply (P _ _ _ _ (-n) _ (-m) _). now rewrite (Z $ E).
        now apply (strong_extensionality (X:=F ₀) (Y:=F ₀) (⁻¹)).
    * now rewrite (standard_uneq n m).
Qed.

Lemma int_pow_0 x `{x ∊ F} : x^0 = 1. Proof nat_pow_0 (N:=Z⁺) x.
Instance int_pow_1 : RightIdentity (^) 1 F := nat_pow_1 (N:=Z⁺).
Lemma int_pow_2 x `{x ∊ F} : x^2 = x * x. Proof nat_pow_2 (N:=Z⁺) x.
Lemma int_pow_3 x `{x ∊ F} : x^3 = x * (x * x). Proof nat_pow_3 (N:=Z⁺) x.
Lemma int_pow_4 x `{x ∊ F} : x^4 = x * (x * (x * x)). Proof nat_pow_4 (N:=Z⁺) x.

Lemma int_pow_negate_alt x `{x ∊ F ₀} n `{n ∊ Z} : x ^ n = (x ^ (-n))⁻¹.
Proof. destruct (int_neg_0_or_pos n) as [?|[E|?]].
+ exact (int_pow_neg_alt x n).
+ rewrite (Z $ E), (Z $ negate_0). rewrite_on (F ₀) -> (int_pow_0 x). subsymmetry. exact mult_inv_1.
+ rewrite_on (F ₀) -> (int_pow_neg_alt x (-n)), (mult_inv_involutive (x ^ (- - n))).
  now rewrite (Z $ negate_involutive n).
Qed.

Lemma int_pow_negate x `{x ∊ F ₀} n `{n ∊ Z} : x ^ (-n) = (x ^ n)⁻¹ .
Proof. rewrite <- (Z $ negate_involutive n) at 2. exact (int_pow_negate_alt x (-n)). Qed.

Lemma int_pow_mult_nonneg x `{x ∊ F} y `{y ∊ F} n `{n ∊ Z⁺} : (x * y) ^ n = x ^ n * y ^ n.
Proof nat_pow_base_mult (N:=Z⁺) x y n.

Lemma int_pow_mult x `{x ∊ F ₀} y `{y ∊ F ₀} n `{n ∊ Z} : (x * y) ^ n = x ^ n * y ^ n.
Proof. destruct (nonneg_or_neg n).
+ exact (int_pow_mult_nonneg x y n).
+ rewrite ?(F ₀ $ int_pow_negate_alt _ n).
  rewrite (F ₀ $ int_pow_mult_nonneg x y (-n)).
  exact (mult_inv_distr _ _).
Qed.

Lemma int_pow_inv x `{x ∊ F ₀} n `{n ∊ Z} : (x⁻¹)^n = (x^n)⁻¹ .
Proof.
  assert (∀ `{x ∊ F ₀} `{n ∊ Z⁺}, (x⁻¹)^n = (x^n)⁻¹) as P.
  intros y ? m ?. pattern m. apply (naturals.induction (N:=Z⁺)); try trivial.
  * intros i j E; unfold_sigs; split; intro; [ rewrite <- (Z $ E) | rewrite (Z $ E) ]; trivial.
  * rewrite_on (F ₀) -> (int_pow_0 y), (int_pow_0 (y⁻¹)). subsymmetry. exact mult_inv_1.
  * intros i ? IH. rewrite_on (F ₀) -> (nat_pow_S (N:=Z⁺) y i), (nat_pow_S (N:=Z⁺) (inv y) i), IH.
    subsymmetry. exact (mult_inv_distr _ _).
* destruct (nonneg_or_neg n).
+ exact (P _ _ _ _).
+ rewrite ?(F ₀ $ int_pow_negate_alt _ n).
  rewrite (F ₀ $ mult_inv_involutive _). subsymmetry.
  rewrite <- (F ₀ $ mult_inv_involutive x) at 1.
  exact (P _ _ _ _).
Qed.

Lemma int_pow_neg_1 x `{x ∊ F ₀} : x ^ (-1) = x⁻¹.
Proof. now rewrite_on (F ₀) -> (int_pow_negate x 1), (int_pow_1 x _). Qed.

Lemma int_pow_nat_pow `{Naturals (N:=N)} `{!NatPowSpec F N pw} {f : N ⇀ Z} `{!SemiRing_Morphism N Z f}
  x `{x ∊ F} n `{n ∊ N} : x ^ (f n) = x ^ n.
Proof. pose proof nat_int.to_semiring_nonneg_mor (f:=f).
 exact (preserves_nat_pow_exp (N2:=Z⁺) x n).
Qed.

Instance int_pow_base_1 : LeftAbsorb (^) 1 Z.
Proof. intros n ?. destruct (nonneg_or_neg n).
+ exact (nat_pow_base_1 (N:=Z⁺) _).
+ rewrite ?(F ₀ $ int_pow_negate_alt _ n).
  rewrite_on (F ₀) -> (nat_pow_base_1 (R:=F) (N:=Z⁺) (-n)).
  exact mult_inv_1.
Qed.

Lemma int_pow_S x `{x ∊ F ₀} n `{n ∊ Z} : x ^ (1 + n) = x * x ^ n.
Proof. destruct (nonneg_or_neg n).
+ exact (nat_pow_S (R:=F) (N:=Z⁺) _ _).
+ mc_replace n with (-(1+(-n-1))) on Z by subring Z.
  mc_replace (1-(1+(-n-1))) with (-(-n-1)) on Z by subring Z.
  generalize (int_pos_minus_1_nonneg (-n)). generalize (-n-1).
  clear dependent n. intros n ?.
  rewrite_on (F ₀) -> (int_pow_negate x n), (int_pow_negate x (1+n)).
  rewrite_on (F ₀) -> (nat_pow_S (R:=F) (N:=Z⁺) x n).
  rewrite (F ₀ $ mult_inv_distr _ _), (F ₀ $ associativity (.*.) _ _ _), (F ₀ $ field_inv_r x).
  now rewrite (F ₀ $ mult_1_l _).
Qed.

Lemma int_pow_exp_plus x `{x ∊ F ₀} n `{n ∊ Z} m `{m ∊ Z} :
  x ^ (n + m) = x ^ n * x ^ m.
Proof. pose proof _:(x^m)∊ F ₀. biinduction n.
+ rewrite (F ₀ $ int_pow_0 x). pose proof _:(x^m)∊ F ₀. now rewrite (F ₀ $ mult_1_l _), (Z $ plus_0_l _).
+ pose proof _:(x^n)∊ F ₀.
  rewrite <- (Z $ associativity (+) _ _ _), 2!(F ₀ $ int_pow_S _ _).
  split; intro E; [| apply (left_cancellation (.*.) x (F ₀) _ _)];
  rewrite_on (F ₀) -> E; [| subsymmetry]; exact (associativity (.*.) _ _ _).
Qed.

Lemma int_pow_exp_mult x `{x ∊ F ₀} n `{n ∊ Z} m `{m ∊ Z} :
  x ^ (n * m) = (x ^ n) ^ m.
Proof. pose proof _:(x^n)∊ F ₀. biinduction m.
+ now rewrite (Z $ mult_0_r _), ?(F ₀ $ int_pow_0 _).
+ rewrite (F ₀ $ int_pow_S _ _).
  rewrite (Z $ plus_mult_distr_l _ _ _), (Z $ mult_1_r _).
  rewrite (F ₀ $ int_pow_exp_plus _ _ _).
  split; intro E; [| apply (left_cancellation (.*.) (x^n) (F ₀) _ _)];
  rewrite_on (F ₀) -> E; exact (subreflexivity (S:=F ₀) _).
Qed.

Context `{Le _} `{Lt _} `{!FullPseudoSemiRingOrder F}.

Instance int_pow_nonneg : Closed (F⁺ ⇀ Z⁺ ⇀ F⁺) (^).
Proof nat_pow_nonneg (R:=F) (N:=Z⁺).

Instance int_pow_pos : Closed (F₊ ⇀ Z ⇀ F₊) (^).
Proof. pose proof nat_pow_pos (R:=F) (N:=Z⁺).
  intros x ? n ?. destruct (nonneg_or_neg n).
+ apply _.
+ rewrite <- (Z $ negate_involutive n), (F ₀ $ int_pow_negate x (-n)).
  apply _.
Qed.

Instance int_pow_nonneg_2 : Closed (F₊ ⇀ Z ⇀ F⁺) (^).
Proof. intros x ? n ?. apply pos_nonneg. now apply int_pow_pos. Qed.

Lemma int_pow_ge_1 x `{x ∊ F} n `{n ∊ Z⁺} : 1 ≤ x → 1 ≤ x ^ n.
Proof nat_pow_ge_1 (R:=F) (N:=Z⁺) x n.

Lemma int_pow_gt_1 x `{x ∊ F} n `{n ∊ Z₊} : 1 < x → 1 < x ^ n.
Proof. intro E. destruct (int_pos_decompose n) as [i[? Ei]].
  rewrite (Z⁺ $ Ei). clear dependent n.
  pattern i. apply (naturals.induction (N:=Z⁺)); try trivial. solve_proper.
  + now rewrite (Z⁺ $ plus_0_r 1), (F $ int_pow_1 x _).
  + intros n ? E2. rewrite_on F -> (nat_pow_S (R:=F) (N:=Z⁺) x (1+n)).
    exact (gt_1_mult_compat _ _ E E2).
Qed.

(*
Instance int_pow_pos_mor x `{x ∊ F₊} : Setoid_Morphism Z (F₊) (x^).
Proof. split; try apply _.
    intros n1 n2 E. unfold_sigs.
    pose proof int_pow_pos x _ n1 _.
    pose proof int_pow_pos x _ n2 _.
    red_sig. now rewrite (Z $ E).
Qed.
*)

Instance int_pow_pos_mor x `{x ∊ F₊} : Morphism (Z ⇒ F) (x^).
Proof.
    intros n1 n2 E. unfold_sigs.
    pose proof int_pow_pos x _ n1 _.
    pose proof int_pow_pos x _ n2 _.
    red_sig. now rewrite (Z $ E).
Qed.


(* Making these instances Global is not useful, we don't have PropHolds (1 ≤ x)
  instances and it will only slow down instance resolution (it increases the
  compilation time of dyadics from 1:35 to 2:28). *)
Instance int_pow_exp_le x `{x ∊ F} :
  PropHolds (1 ≤ x) → OrderPreserving Z F (x^).
Proof. intro. assert (x ∊ F₊). split. apply _.
    apply (lt_le_trans _ 1 _); solve_propholds.
  split. split; try apply _. (* rewrite (_:F₊ ⊆ F). apply _. *)
  intros n ? m ? E. pose proof int_pow_pos x _ n _.
  destruct (decompose_le E) as [z [? Eb]].
  rewrite (Z $ Eb).
  rewrite (F ₀ $ int_pow_exp_plus x n z).
  rewrite_on F <- (mult_1_r (x^n)) at 1.
  assert (x ^ n ∊ F⁺) by now apply semirings.pos_nonneg.
  apply (order_preserving (x ^ n *.) 1 (x^z)).
  now apply (int_pow_ge_1 x z).
Qed.

Instance int_pow_exp_lt x `{x ∊ F} :
  PropHolds (1 < x) → StrictlyOrderPreserving Z F (x^).
Proof. intro. assert (x ∊ F₊). split. apply _. apply (subtransitivity _ 1 _); solve_propholds.
  split. split; try apply _. (* rewrite (_:F₊ ⊆ F). apply _. *)
  intros n ? m ? E. pose proof int_pow_pos x _ n _.
  destruct (decompose_lt E) as [z [? Eb]].
  rewrite (Z $ Eb).
  rewrite (F ₀ $ int_pow_exp_plus x n z).
  rewrite_on F <- (mult_1_r (x^n)) at 1.
  apply (strictly_order_preserving (x ^ n *.) 1 (x^z)).
  now apply (int_pow_gt_1 x z).
Qed.

Instance int_pow_exp_le_back x `{x ∊ F} :
  PropHolds (1 < x) → OrderReflecting Z F (x^).
Proof. intro. assert (x ∊ F₊). split. apply _. apply (subtransitivity _ 1 _); solve_propholds.
  split. split; try apply _.
  intros n ? m ? E.
  destruct (total (≤) n m) as [E2|E2]; trivial.
  destruct (le_equiv_lt _ _ E2) as [E3|E3].
   now rewrite (Z $ E3).
  contradict E.
  pose proof (_ : x ∊ F ₀).
  pose proof (_ : x ^ n ∊ F ₀).
  pose proof (_ : x ^ m ∊ F ₀).
  apply (lt_not_le_flip _ _).
  exact (strictly_order_preserving (x^) _ _ E3).
Qed.

Instance int_pow_exp_lt_back x `{x ∊ F} :
  PropHolds (1 < x) → StrictlyOrderReflecting Z F (x^).
Proof. intros E1. 
  assert (x ∊ F₊). split. apply _. apply (subtransitivity _ 1 _); solve_propholds.
  assert (Strong_Morphism Z F (x^)).
    split. apply _.
    intros ?? ??. now apply (strong_extensionality (Y:=F ₀) (x^)).
  pose proof int_pow_exp_le_back x _.
  apply _.
Qed.

Instance int_pow_inj x `{x ∊ F} : PropHolds (1 < x) → Injective Z F (x^).
Proof. intro. assert (x ∊ F₊). split. apply _. apply (subtransitivity _ 1 _); solve_propholds.
  split; try apply _. intros n ? m ? E. pose proof int_pow_exp_le_back x _.
  pose proof _ : x^m ∊ F ₀. pose proof _ : x^n ∊ F ₀.
  apply (subantisymmetry (≤) n m); apply (order_reflecting (x^) _ _); now rewrite (F $ E).
Qed.
End int_pow_properties.

(*
(* Due to bug #2528 *)
Hint Extern 18 (PropHolds (_ ^ _ ≠ 0)) => eapply @int_pow_ne_0 : typeclass_instances.
Hint Extern 18 (PropHolds (0 ≤ _ ^ _)) => eapply @int_pow_nonneg : typeclass_instances.
Hint Extern 18 (PropHolds (0 < _ ^ _)) => eapply @int_pow_pos : typeclass_instances.
*)

Hint Extern 4 (_ ^ _ ∊ _ ₀) => eapply @int_pow_nonzero : typeclass_instances.
Hint Extern 5 (_ ^ _ ∊ _) => eapply @int_pow_nonzero2 : typeclass_instances.
Hint Extern 4 (_ ^ _ ∊ _⁺) => eapply @int_pow_nonneg : typeclass_instances.
Hint Extern 3 (_ ^ _ ∊ _⁺) => eapply @int_pow_nonneg_2 : typeclass_instances.
Hint Extern 4 (_ ^ _ ∊ _₊) => eapply @int_pow_pos : typeclass_instances.

Section preservation.
  Context
    `{Integers (Z:=Z)} `{UnEq _} `{Le _} `{Lt _} `{!StandardUnEq Z} `{!FullPseudoSemiRingOrder Z}.
  Context
    `{Field (F:=F1)} `{!IntPowSpec F1 Z ip1}
    `{Field (F:=F2)} `{!IntPowSpec F2 Z ip2}
    {f : F1 ⇀ F2} `{!Strong_Morphism F1 F2 f} `{!Ring_Morphism F1 F2 f}.

  Existing Instance field_mor_nonzero.

  Lemma preserves_int_pow x `{x ∊ F1 ₀} n `{n ∊ Z} :  f (x ^ n) = (f x) ^ n.
  Proof. destruct (nonneg_or_neg n).
  + exact (preserves_nat_pow (N:=Z⁺) (R1:=F1) (R2:=F2) (f:=f) x n).
  + pose proof (_ : f x ^ n ∊ F2 ₀).
  rewrite (F1 ₀ $ int_pow_negate_alt x n).
  rewrite (F2 ₀ $ preserves_mult_inv (f:=f) (x^(-n))).
  rewrite (F2 ₀ $ preserves_nat_pow (N:=Z⁺) (f:=f) x (-n)).
  subsymmetry. exact (int_pow_negate_alt _ _).
  Qed.

End preservation.

Section exp_preservation.
  Context `{Integers (Z:=Z1)} `{UnEq _} `{Le _} `{Lt _} `{!StandardUnEq Z1} `{!FullPseudoSemiRingOrder Z1}.
  Context `{Integers (Z:=Z2)} `{UnEq _} `{Le _} `{Lt _} `{!StandardUnEq Z2} `{!FullPseudoSemiRingOrder Z2}.
  Context `{Field (F:=F)} {f : Z1 ⇀ Z2} `{!Ring_Morphism Z1 Z2 f}.
  Context `{!IntPowSpec F Z1 ip1} `{!IntPowSpec F Z2 ip2}.

  Existing Instance Zpos_semiring_mor_nonneg.

  Lemma preserves_int_pow_exp x `{x ∊ F ₀} n `{n ∊ Z1} :  x ^ (f n) = x ^ n.
  Proof. destruct (nonneg_or_neg n).
  + exact (preserves_nat_pow_exp (N1:=Z1⁺) (N2:=Z2⁺) (f:=f) x n).
  + pose proof (_ : x ^ n ∊ F ₀).
  rewrite (F ₀ $ int_pow_negate_alt x (f n) ).
  rewrite <- (Z2 $ preserves_negate (f:=f) n).
  rewrite (F ₀ $ preserves_nat_pow_exp (N1:=Z1⁺) (N2:=Z2⁺) (f:=f) x (-n)).
  subsymmetry. exact (int_pow_negate_alt _ _).
  Qed.

End exp_preservation.

Require Import peano_naturals misc.quote.

(* Very slow default implementation by translation into Peano *)
Section int_pow_default.
  Context `{Field A (F:=F)} `{Integers B (Z:=Z)} `{UnEq _} `{Le _} `{Lt _} `{!StandardUnEq Z} `{!FullPseudoSemiRingOrder Z}.

  Notation nat := (every nat).
  Existing Instance to_semiring_nonneg_mor.

  Instance int_pow_default: Pow A B := λ x n,
    match (int_abs_sig Z nat n) with
    | inl (exist _ n p) => x ^ n
    | inr (exist _ O p) => 1
    | inr (exist _ (S n) p) => x⁻¹ ^ (S n)
    end.

  Instance: ∀ n, naturals_to_semiring nat Z (S n) ∊ Z₊ .
  Proof. intro.
    rewrite <- nonneg_pos_is_pos.
    apply nat_ne_0_pos. apply nat_ge_1_ne_0. apply _.
    rewrite S_nat_1_plus.
    preserves_simplify (naturals_to_semiring nat Z).
    rewrite (nat_le_plus (N:=Z⁺)).
    now exists_sub (naturals_to_semiring nat Z n).
  Qed.

  Lemma int_pow_default_nonneg x `{x ∊ F} n `{n ∊ Z⁺}
  : int_pow_default x n ∊ F ∧ int_pow_default x n = x^(naturals_to_semiring Z⁺ nat n).
  Proof. intros. unfold int_pow_default. 
    destruct (int_abs_sig Z nat n) as [[n' p]|[[| ?] p]]; destruct (p _) as [_ E].
  + split. apply _. rewrite <- (Z⁺ $ E).
      assert (naturals_to_semiring Z⁺ nat (naturals_to_semiring nat Z n') ≡ n') as E'
        by exact (morphisms_involutive (R:=Z⁺) _ _ n'). now rewrite E'.
  + split. apply _. assert (n = 0) as E'.
      rewrite <- (Z $ negate_0). apply (flip_negate _ _). rewrite <- (Z $ E). exact preserves_0.
      rewrite (Z⁺ $ E'). rewrite (nat $ preserves_0). subsymmetry. exact (nat_pow_0 x).
  + assert (- n ∊ Z₊). rewrite <- (Z $ E). apply _.
    pose proof nonpos_not_pos (-n). contradiction.
  Qed.

  Lemma int_pow_default_neg x `{x ∊ F ₀} n `{n ∊ Z₋}
  : int_pow_default x n ∊ F ₀ ∧ int_pow_default x n = x⁻¹ ^ (naturals_to_semiring Z⁺ nat (-n)).
  Proof. intros. unfold int_pow_default. 
    destruct (int_abs_sig Z nat n) as [[n' p]|[[| n'] p]]; destruct (p _) as [_ E].
  + pose proof (neg_not_nonneg n) as Q. contradict Q. rewrite <- (Z $ E). apply _.
  + pose proof (neg_not_nonneg n) as Q. contradict Q. assert (n = 0) as E'.
      rewrite <- (Z $ negate_0). apply (flip_negate _ _). rewrite <- (Z $ E). exact preserves_0. rewrite (Z $ E'). apply _.
  + split. apply _. rewrite <- (Z⁺ $ E).
      assert (naturals_to_semiring Z⁺ nat (naturals_to_semiring nat Z (S n')) ≡ S n') as E'
        by exact (morphisms_involutive (R:=Z⁺) _ _ _). now rewrite E'.
  Qed.

  Add Ring F2 : (stdlib_ring_theory F).

  Global Instance int_pow_default_spec: IntPowSpec F Z int_pow_default.
  Proof. split; unfold pow. split; unfold pow.
  + apply binary_morphism_proper_back.
    intros x1 y1 E1 n m E2. unfold_sigs.
    destruct (int_pow_default_nonneg x1 n) as [? Ex].
    destruct (int_pow_default_nonneg y1 m) as [? Ey].
    red_sig. now rewrite (F $ Ex), (F $ Ey), (F $ E1), (Z⁺ $ E2).
  + intros x ?. 
    destruct (int_pow_default_nonneg x 0) as [? Ex]. rewrite (F $ Ex).
    rewrite (nat $ preserves_0). exact (nat_pow_0 _).
  + intros x ? n ?.
    destruct (int_pow_default_nonneg x n) as [? E1].
    destruct (int_pow_default_nonneg x (1+n)) as [? E2].
    rewrite (F $ E1), (F $ E2).
    rewrite (nat $ preserves_plus 1 n), (nat $ preserves_1). exact (nat_pow_S _ _).
  + intros x ? n ?. destruct (int_pow_default_neg x n). apply _.
  + intros x ? n ?.
    destruct (int_pow_default_neg x n) as [? E1].
    destruct (int_pow_default_nonneg x (-n)) as [? E2].
    set (n' :=  naturals_to_semiring Z⁺ nat (- n) ) in E1,E2. rewrite (F $ E1), (F $ E2).
    clear E1 E2. pattern n'. apply naturals.induction; try apply _. solve_proper.
    * rewrite ?(F $ nat_pow_0 (N:=nat) _). exact (mult_1_r 1).
    * intros i _ IH. rewrite ?(F $ nat_pow_S (N:=nat) _ _).
      subtransitivity (  (x⁻¹ ^ i * x ^ i) * (x / x) ). subring F.
      rewrite (F $ IH), (F $ mult_1_l _). exact (field_inv_r x).
  Qed.
End int_pow_default.

Typeclasses Opaque int_pow_default.

(* Make some attempt to choose an appropriate default pow instance *)
Hint Extern 20 (Pow ?A ?B) =>
  first [
    let H := constr:(_ : Integers (A:=B) _) in first [
      let H' := constr:(_ : Field (A:=A) _) in eapply (int_pow_default (H0:=H))
    | let H' := constr:(_ : SemiRing (A:=A) _) in
      match type of H with Integers ?Z => eapply (nat_pow_default (N:=Z⁺)) end
    | fail 2
    ]
  | eapply @nat_pow_default
  ] : typeclass_instances. 
