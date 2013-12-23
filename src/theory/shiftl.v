Require
  orders.integers theory.nat_pow theory.int_pow.
Require Import
  abstract_algebra interfaces.naturals interfaces.integers
  interfaces.additional_operations interfaces.orders
  theory.setoids theory.rings orders.semirings.

Lemma shiftl_spec_from_nat_pow `{SemiRing (R:=R)} `{SemiRing (R:=N)} `{!NatPowSpec R N pw} sl :
  Closed (R ⇀ N ⇀ R) (≪) → (∀ `{x ∊ R} `{n ∊ N}, x ≪ n = 2 ^ n * x) → ShiftLSpec R N sl.
Proof. intros ? spec. pose proof @closed_binary. split.
+ apply binary_morphism_proper_back.
  intros ?? E1 ?? E2. unfold_sigs. red_sig.
  now rewrite !(R $ spec _ _ _ _), (R $ E1), (N $ E2).
+ intros x ?. now rewrite (R $ spec _ _ _ _), (R $ nat_pow_0 _), (R $ mult_1_l _).
+ intros x ? n ?. rewrite !(R $ spec _ _ _ _), (R $ nat_pow_S _ _).
  subsymmetry. exact (associativity (.*.) _ _ _).
Qed.

Lemma shiftl_spec_from_int_pow
  `{Field (F:=F)} `{2 ∊ F ₀}
  `{Integers (Z:=Z)} `{UnEq _} `{Le _} `{Lt _} `{!DenialInequality Z} `{!FullPseudoSemiRingOrder Z}
  `{!IntPowSpec F Z pw} sl :
   Closed (F ⇀ Z ⇀ F) (≪) → (∀ `{x ∊ F} `{n ∊ Z}, x ≪ n = 2 ^ n * x) → ShiftLSpec F Z sl.
Proof. intros ? spec. pose proof @closed_binary. split.
+ apply binary_morphism_proper_back.
  intros x y E1 m n E2. unfold_sigs. red_sig.
  now rewrite 2!(F $ spec _ _ _ _), (F $ E1), (Z $ E2).
+ intros x ?. now rewrite (F $ spec _ _ _ _), (F $ int_pow.int_pow_0 _), (F $ mult_1_l _).
+ intros x ? n ?. rewrite !(F $ spec _ _ _ _), (F $ int_pow.int_pow_S _ _).
  subsymmetry. exact (associativity (.*.) _ _ _).
Qed.

Local Ltac nat_induction n E :=
  pattern n; apply naturals.induction; [solve_proper | | | trivial]; clear dependent n; [| intros n ? E].
Local Ltac biinduction n :=
  pattern n; apply biinduction; [solve_proper | | | trivial]; clear dependent n; [| intros n ?].

Lemma shiftl_closed `{SemiRing (R:=R)} `{SemiRing (R:=N)} {sl} {spec:ShiftLSpec R N sl} :
  Closed (R ⇀ N ⇀ R) (≪).
Proof _.

(* Choose subsets R and N by looking for a ShiftLSpec instance *)
Hint Extern 3 (@shiftl ?A ?B ?sl _ _ ∊ _) =>
  let X := fresh "X" in let Y := fresh "Y" in
  evar (X:@set A); evar (Y:@set B);
  let X' := eval unfold X in X in clear X;
  let Y' := eval unfold Y in Y in clear Y;
  let spec := constr:(_ : ShiftLSpec X' Y' sl) in
  instantiate; eapply (shiftl_closed (R:=X') (N:=Y'))
: typeclass_instances.

Section shiftl.
Context `{SemiRing (R:=R)} `{!LeftCancellation (.*.) 2 R} `{SemiRing (R:=N)} `{!Biinduction N} `{!ShiftLSpec R N sl}.

Lemma shiftl_nat_pow_alt `{Naturals (N:=N2)} `{!NatPowSpec R N2 pw} {f : N2 ⇀ N}
  `{!SemiRing_Morphism N2 N f} x `{x ∊ R} n `{n ∊ N2} : x ≪ f n = 2 ^ n * x.
Proof. nat_induction n E.
+ now rewrite (N $ preserves_0), (R $ shiftl_0 _), (R $ nat_pow_0 _), (R $ mult_1_l _).
+ rewrite (N $ preserves_plus _ _), (N $ preserves_1), (R $ shiftl_S _ _), (R $ E).
  rewrite (R $ nat_pow_S _ _). exact (associativity (.*.) _ _ _).
Qed.

Lemma shiftl_nat_pow `{!NaturalsToSemiRing N} `{!Naturals N} `{!NatPowSpec R N np} 
   x `{x ∊ R} n `{n ∊ N} : x ≪ n = 2 ^ n * x.
Proof shiftl_nat_pow_alt (f:= id: N ⇀ N) x n.

Lemma shiftl_1 x `{x ∊ R} : x ≪ 1 = 2 * x.
Proof. now rewrite <-(N $ plus_0_r 1), (R $ shiftl_S _ _), (R $ shiftl_0 _). Qed.

Lemma shiftl_2 x `{x ∊ R} : x ≪ 2 = 4 * x.
Proof. now rewrite (R $ shiftl_S _ _), (R $ shiftl_1 _), (R $ associativity (.*.) _ _ _), (R $ mult_2_2). Qed.

Hint Extern 4 (@zero _ ?c ∊ _) => eapply (@monoid_unit_exists _ plus_is_sg_op (@zero_is_mon_unit _ c)) : typeclass_instances.
Hint Extern 4 (@one  _ ?c ∊ _) => eapply (@monoid_unit_exists _ mult_is_sg_op (@one_is_mon_unit  _ c)) : typeclass_instances.


Instance shiftl_base_0: LeftAbsorb (≪) 0 N.
Proof. intros n ?. biinduction n.
+ exact (shiftl_0 0).
+ split; intros E.
  - rewrite (R $ shiftl_S _ _), (R $ E). exact (mult_0_r _).
  - apply (left_cancellation (.*.) 2 R _ _). rewrite <- (R $ shiftl_S _ _), (R $ E).
    subsymmetry. exact (mult_0_r _).
Qed.

Lemma shiftl_exp_plus x `{x ∊ R} n `{n ∊ N} m `{m ∊ N} : x ≪ (n + m) = x ≪ n ≪ m.
Proof. biinduction m.
+ now rewrite (R $ shiftl_0 _), (N $ plus_0_r _).
+ mc_replace (n+(1+m)) with (1+(n+m)) on N by now rewrite !(N $ associativity (+) _ _ _), (N $ commutativity (+) n 1).
  rewrite ?(R $ shiftl_S _ _). split; intro E.
  - now rewrite (R $ E).
  - now apply (left_cancellation (.*.) 2 R _ _).
Qed.

Lemma shiftl_order x `{x ∊ R} n `{n ∊ N} m `{m ∊ N}: x ≪ n ≪ m  = x ≪ m ≪ n.
Proof. rewrite <-?(R $ shiftl_exp_plus _ _ _). now rewrite (N $ commutativity (+) n m). Qed.

Lemma shiftl_reverse  x `{x ∊ R} n `{n ∊ N} m `{m ∊ N} : n + m = 0 → x ≪ n ≪ m = x.
Proof. intros E. now rewrite <-(R $ shiftl_exp_plus _ _ _), (N $ E), (R $ shiftl_0 _). Qed.

Lemma shiftl_mult_l x `{x ∊ R} y `{y ∊ R} n `{n ∊ N} : x * (y ≪ n) = (x * y) ≪ n.
Proof. biinduction n.
+ now rewrite ?(R $ shiftl_0 _).
+ rewrite ?(R $ shiftl_S _ _).
  rewrite (R $ associativity (.*.) _ _ _), <- (R $ mult_2_comm x),
       <- (R $ associativity (.*.) 2 x _).
  split; intro E.
  - now rewrite_on R -> E.
  - now apply (left_cancellation (.*.) 2 R _ _).
Qed.

Lemma shiftl_mult_r x `{x ∊ R} y `{y ∊ R} n `{n ∊ N} : (x ≪ n) * y = (x * y) ≪ n.
Proof. biinduction n.
+ now rewrite ?(R $ shiftl_0 _).
+ rewrite ?(R $ shiftl_S _ _).
  rewrite <- (R $ associativity (.*.) 2 _ y).
  split; intro E.
  - now rewrite_on R -> E.
  - now apply (left_cancellation (.*.) 2 R _ _).
Qed.

Lemma shiftl_base_plus x `{x ∊ R} y `{y ∊ R} n `{n ∊ N} : (x + y) ≪ n  = x ≪ n + y ≪ n.
Proof. biinduction n.
+ now rewrite ?(R $ shiftl_0 _).
+ rewrite ?(R $ shiftl_S _ _). rewrite <- (R $ plus_mult_distr_l 2 _ _). split; intros E.
  - now rewrite (R $ E).
  - now apply (left_cancellation (.*.) 2 R _ _).
Qed.

Lemma shiftl_base_nat_pow `{Naturals (N:=N2)} `{!NatPowSpec R N2 pw} {f : N2 ⇀ N} `{!SemiRing_Morphism N2 N f}
  x `{x ∊ R} n `{n ∊ N} m `{m ∊ N2} : (x ≪ n) ^ m = (x ^ m) ≪ (n * f m).
Proof. nat_induction m E.
+ rewrite ?(R $ nat_pow_0 _). now rewrite (N $ preserves_0), (N $ mult_0_r _), (R $ shiftl_0 _).
+ rewrite (N $ preserves_plus _ _), (N $ preserves_1).
  rewrite (N $ plus_mult_distr_l _ _ _), (N $ mult_1_r _), (R $ shiftl_exp_plus _ _ _).
  rewrite !(R $ nat_pow_S _ _), (R $ E).
  now rewrite (R $ shiftl_mult_l _ _ _), (R $ shiftl_mult_r _ _ _).
Qed.

Lemma shiftl_negate `{Negate A} `{!Ring R} x `{x ∊ R} n `{n ∊ N} : (-x) ≪ n = -(x ≪ n).
Proof.
  rewrite (R $ negate_mult x), (R $ negate_mult (x ≪ n)).
  subsymmetry. exact (shiftl_mult_l _ _ _).
Qed.

Instance shiftl_inj n `{n ∊ N} : Injective R R (≪ n).
Proof. split; try apply _. intros x ? y ?. biinduction n.
+ rewrite ?(R $ shiftl_0 _); tauto.
+ rewrite ?(R $ shiftl_S _ _). split; intros E1 E2; apply E1.
  - now apply (left_cancellation (.*.) 2 R _ _).
  - now rewrite_on R -> E2.
Qed.

Instance shiftl_ne_0 `{UnEq A} `{!DenialInequality R} : Closed (R ₀ ⇀ N ⇀ R ₀) (≪).
Proof. intros x [? E1] n ?. red in E1.
  split. apply _. red. revert E1. rewrite !(denial_inequality _ _).
  intro E1. contradict E1.
  apply (injective (≪ n) _ _).
  now rewrite (R $ shiftl_base_0 _ _).
Qed.

Context `{UnEq _} `{Le _} `{Lt _} `{!FullPseudoSemiRingOrder R} `{1 ∊ R ₀}.

Let shiftl_strict_order_embedding_lemma x `{x ∊ R} y `{y ∊ R} n `{n ∊ N} : x < y ↔ x ≪ n < y ≪ n.
Proof. biinduction n.
+ rewrite !(R $ shiftl_0 _); tauto.
+ cut (x ≪ n < y ≪ n ↔ 2 * x ≪ n < 2 * y ≪ n). intro. rewrite !(R $ shiftl_S _ _). tauto.
  split; intro E.
  - now apply (strictly_order_preserving (2 *.) _ _).
  - now apply (strictly_order_reflecting (2 *.) _ _).
Qed.

Instance shiftl_strict_order_embedding n `{n ∊ N} : StrictOrderEmbedding R R (≪ n).
Proof. 
  repeat (split; try apply _); intros.
   now apply shiftl_strict_order_embedding_lemma.
  eapply shiftl_strict_order_embedding_lemma; trivial. eassumption. assumption.
Qed.

Instance shiftl_order_embedding n `{n ∊ N} : OrderEmbedding R R (≪ n).
Proof. split.
   now apply maps.full_pseudo_order_preserving.
  now apply maps.full_pseudo_order_reflecting.
Qed.

Instance shiftl_strong_inj n `{n ∊ N} : StrongInjective R R (≪ n)
  := maps.pseudo_order_embedding_inj.

Lemma shiftl_le_flip_r `{Negate _} `{!Ring N} x `{x ∊ R} y `{y ∊ R} n `{n ∊ N} :
  x ≤ y ≪ (-n)  ↔  x ≪ n ≤ y.
Proof.
  split; intros E.
   apply (order_reflecting (≪ -n) _ _).
   now rewrite (R $ shiftl_reverse _ _ _ (plus_negate_r n)).
  apply (order_reflecting (≪ n) _ _).
  now rewrite (R $ shiftl_reverse _ _ _ (plus_negate_l n)).
Qed.

Lemma shiftl_le_flip_l `{Negate _} `{!Ring N} x `{x ∊ R} y `{y ∊ R} n `{n ∊ N} :
  x ≪ (-n) ≤ y  ↔  x ≤ y ≪ n.
Proof. now rewrite <-(shiftl_le_flip_r _ _ _), (N $ negate_involutive _). Qed.

Instance shiftl_nonneg  : Closed (R⁺ ⇀ N ⇀ R⁺) (≪).
Proof. intros x [??] n ?. split. apply _. red.
  rewrite <- (R $ shiftl_base_0 n _). now apply (order_preserving (≪ n) _ _).
Qed.

Instance shiftl_pos  : Closed (R₊ ⇀ N ⇀ R₊) (≪).
Proof. intros x [??] n ?. split. apply _. red.
  rewrite <- (R $ shiftl_base_0 n _). now apply (strictly_order_preserving (≪ n) _ _).
Qed.

End shiftl.

Arguments shiftl_base_0 {_ _ _ _ _ _ R _ _ _ _ _ _ _ _ N _ _ sl _} _ {_}.

Hint Extern 5 (LeftAbsorb (≪) _ _) => class_apply @shiftl_base_0 : typeclass_instances.
Hint Extern 5 (Injective _ _ (≪ _)) => class_apply @shiftl_inj : typeclass_instances.
Hint Extern 5 (StrictOrderEmbedding _ _ (≪ _)) => class_apply @shiftl_strict_order_embedding : typeclass_instances.
Hint Extern 5 (OrderEmbedding _ _ (≪ _)) => class_apply @shiftl_order_embedding : typeclass_instances.
Hint Extern 5 (StrongInjective _ _ (≪ _)) => class_apply @shiftl_strong_inj : typeclass_instances.
Hint Extern 9 (_ ≪ _ ∊ _ ₀) => eapply @shiftl_ne_0 : typeclass_instances.
Hint Extern 5 (_ ≪ _ ∊ _⁺) => eapply @shiftl_nonneg : typeclass_instances.
Hint Extern 5 (_ ≪ _ ∊ _₊) => eapply @shiftl_pos : typeclass_instances.

(* Choose subsets R and N by looking for a ShiftLSpec instance *)
Hint Extern 2 (@shiftl ?A ?B ?sl _ _ ∊ ?X ₀) =>
  let Y := fresh "Y" in evar (Y:@set B);
  let Y' := eval unfold Y in Y in clear Y;
  let spec := constr:(_ : ShiftLSpec X Y' sl) in
  instantiate; eapply (shiftl_ne_0 (R:=X) (N:=Y'))
: typeclass_instances.

Section preservation.
  Context `{SemiRing (R:=N)} `{!Biinduction N}
    `{SemiRing (R:=R1)} `{!ShiftLSpec R1 N sl1} `{SemiRing (R:=R2)} `{!LeftCancellation (.*.) 2 R2} `{!ShiftLSpec R2 N sl2}
    `{f : R1 ⇀ R2} `{!SemiRing_Morphism R1 R2 f}.

  Lemma preserves_shiftl x `{x ∊ R1} n `{n ∊ N} : f (x ≪ n) = (f x) ≪ n.
  Proof. biinduction n.
  + now rewrite (R1 $ shiftl_0 _), (R2 $ shiftl_0 _).
  + rewrite (R1 $ shiftl_S _ _), (R2 $ shiftl_S _ _).
    rewrite (R2 $ preserves_mult _ _), (R2 $ preserves_2).
    split; intro E.
    - now rewrite_on R2 -> E.
    - now apply (left_cancellation (.*.) 2 R2 _ _).
  Qed.
End preservation.

Section exp_preservation.
  Context `{SemiRing (R:=N1)} `{!Biinduction N1} `{SemiRing (R:=N2)} `{!Biinduction N2}
   `{SemiRing (R:=R)} `{!LeftCancellation (.*.) 2 R} `{!ShiftLSpec R N1 sl1} `{!ShiftLSpec R N2 sl2}
   `{f : N1 ⇀ N2} `{!SemiRing_Morphism N1 N2 f}.

  Lemma preserves_shiftl_exp x `{x ∊ R} n `{n ∊ N1} : x ≪ f n = x ≪ n.
  Proof. biinduction n.
  + now rewrite (N2 $ preserves_0), ?(R $ shiftl_0 _).
  + rewrite (N2 $ preserves_plus _ _), (N2 $ preserves_1), ?(R $ shiftl_S _ _).
    split; intro E.
    - now rewrite_on R -> E.
    - now apply (left_cancellation (.*.) 2 R _ _).
  Qed.
End exp_preservation.

(*
Section shiftl_dec_field.
  Context `{SemiRing R} `{Integers Z} `{!ShiftLSpec R Z sl}
     `{DecField F} `{∀ x y : F, Decision (x = y)} `{!PropHolds ((2:F) ≠ 0)} `{!IntPowSpec F Z ipw}
     `{!SemiRing_Morphism (f : R → F)}.

  Add Ring F: (rings.stdlib_ring_theory F).
  Add Ring Z: (rings.stdlib_ring_theory Z).

  Existing Instance int_pow_proper.

  Lemma shiftl_to_int_pow x n : f (x ≪ n) = f x * 2 ^ n.
  Proof.
    revert n. apply biinduction.
      solve_proper.
     now rewrite shiftl_0, int_pow_0, rings.mult_1_r.
    intros n.
    rewrite shiftl_S, int_pow_S by solve_propholds.
    rewrite rings.preserves_mult, rings.preserves_2.
    rewrite associativity, (commutativity (f x) 2), <-associativity.
    split; intros E.
     now rewrite E.
    now apply (left_cancellation (.*.) 2).
  Qed.

  Lemma shiftl_base_1_to_int_pow n : f (1 ≪ n) = 2 ^ n.
  Proof. now rewrite shiftl_to_int_pow, rings.preserves_1, rings.mult_1_l. Qed.

  Lemma shiftl_negate_1_to_half x : f (x ≪ -1) = f x / 2.
  Proof.
    rewrite shiftl_to_int_pow.
    apply (left_cancellation (.*.) 2).
    transitivity (f x * (2 * 2 ^ (-1))); [ring |].
    transitivity (f x * (2 / 2)); [| ring].
    rewrite dec_recip_inverse, <-int_pow_S by assumption.
    now rewrite rings.plus_negate_r, int_pow_0.
 Qed.

  Lemma shiftl_negate_1_to_fourth x : f (x ≪ -2) = f x / 4.
  Proof.
    rewrite shiftl_to_int_pow.
    apply (left_cancellation (.*.) (2 * 2)).
    transitivity (f x * (2 * (2 * 2 ^ (-2)))); [ring |].
    transitivity (f x * (4 / 4)); [| ring].
    assert ((4:F) ≠ 0).
     setoid_replace 4 with (2*2) by ring.
     solve_propholds.
    rewrite dec_recip_inverse, <-!int_pow_S by assumption.
    setoid_replace (1 + (1 - 2) : Z) with (0 : Z) by ring.
    now rewrite int_pow_0.
 Qed.
End shiftl_dec_field.

Section more_shiftl_dec_field.
  Context `{DecField A} `{Integers B} `{∀ x y : A, Decision (x = y)}
    `{!PropHolds ((2:A) ≠ 0)} `{!ShiftLSpec A B sl} `{!IntPowSpec A B ipw}.

  Lemma shiftl_int_pow x n : x ≪ n = x * 2 ^ n.
  Proof. change (id (x ≪ n) = id x * 2 ^ n). apply shiftl_to_int_pow. Qed.

  Lemma shiftl_base_1_int_pow n : 1 ≪ n = 2 ^ n.
  Proof. now rewrite shiftl_int_pow, rings.mult_1_l. Qed.

  Lemma shiftl_negate_1_half x : x ≪ (-1) = x / 2.
  Proof. change (id (x ≪ (-1)) = id x / 2). now apply shiftl_negate_1_to_half. Qed.

  Lemma shiftl_negate_1_fourth x : x ≪ (-2) = x / 4.
  Proof. change (id (x ≪ (-2)) = id x / 4). now apply shiftl_negate_1_to_fourth. Qed.
End more_shiftl_dec_field.

Section shiftl_field.
  Context `{Ring R} `{Integers Z} `{!ShiftLSpec R Z sl}
    `{Field F} `{!PropHolds ((2:F) ≶ 0)} `{Naturals N} `{!NatPowSpec F N npw}
    `{!SemiRing_Morphism (g : N → Z)} `{!SemiRing_Morphism (f : R → F)}.

  Add Ring F2: (rings.stdlib_ring_theory F).
  Add Ring Z2: (rings.stdlib_ring_theory Z).

  Lemma shiftl_negate_nat_pow x n : f (x ≪ (-g n)) * 2 ^ n = f x.
  Proof.
    pose proof nat_pow_proper.
    pattern n. apply naturals.induction; clear n.
      solve_proper.
     rewrite rings.preserves_0, rings.negate_0, shiftl_0.
     rewrite nat_pow_0. ring.
    intros n E.
    rewrite rings.preserves_plus, rings.preserves_1.
    etransitivity; [| eassumption].
    setoid_replace (-g n) with (1 - (1 + g n)) by ring.
    rewrite shiftl_S, rings.preserves_mult, rings.preserves_2.
    rewrite nat_pow_S. ring.
  Qed.

  Lemma shiftl_negate_to_recip_nat_pow x n P2n : f (x ≪ (-g n)) = f x // (2 ^ n)↾P2n.
  Proof.
    apply (right_cancellation (.*.) (2 ^ n)).
    rewrite shiftl_negate_nat_pow.
    transitivity (f x * (2 ^ n // (2 ^ n)↾P2n)); [| ring].
    rewrite fields.reciperse_alt. ring.
  Qed.
End shiftl_field.
*)

Section default_shiftl_naturals.
  Context `{SemiRing A (R:=R)} `{Naturals B (N:=N)} `{!NatPowSpec R N pw}.

  Instance shiftl_default: ShiftL A B := λ x n, 2 ^ n * x.

  Instance: Closed (R ⇀ N ⇀ R) (≪).
  Proof. intros ????. unfold shiftl, shiftl_default. apply _. Qed.

  Global Instance shiftl_default_spec: ShiftLSpec R N shiftl_default.
  Proof. apply shiftl_spec_from_nat_pow. apply _. easy. Qed.
End default_shiftl_naturals.

Typeclasses Opaque shiftl_default.

Section default_shiftl_integers.
  Context `{Field A (F:=F)} `{2 ∊ F ₀}
    `{Integers B (Z:=Z)} `{UnEq _} `{Le _} `{Lt _} `{!DenialInequality Z} `{!FullPseudoSemiRingOrder Z}
    `{!IntPowSpec F Z ipw}.

  Instance shiftl_default_int: ShiftL A B := λ x n, 2 ^ n * x.

  Instance: Closed (F ⇀ Z ⇀ F) (≪).
  Proof. intros ????. unfold shiftl, shiftl_default_int. apply _. Qed.

  Global Instance shiftl_default_int_spec: ShiftLSpec F Z shiftl_default_int.
  Proof. apply shiftl_spec_from_int_pow. apply _. easy. Qed.
End default_shiftl_integers.

Typeclasses Opaque shiftl_default_int.

(* Make some attempt to choose an appropriate default shiftl instance *)
Hint Extern 20 (ShiftL ?A ?B) =>
  first [
    let H := constr:(_ : Integers (A:=B) _) in first [
      let H' := constr:(_ : Field (A:=A) _) in eapply @shiftl_default_int
    | let H' := constr:(_ : SemiRing (A:=A) _) in eapply @shiftl_default
    | fail 2
    ]
  | eapply @shiftl_default
  ] : typeclass_instances. 
