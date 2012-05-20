Require
  theory.integers theory.int_abs.
Require Import
  abstract_algebra interfaces.integers interfaces.naturals
  interfaces.additional_operations interfaces.orders
  theory.setoids theory.rings natpair_integers orders.rings.
Require Import misc.quote.
Require Export
  orders.nat_int.

Local Notation nat := (every nat).
Local Coercion subset_to_type: Subset >-> Sortclass.

Section integers.
Context `{Integers A (Z:=Z)} `{UnEq A} `{Le A} `{Lt A} `{!StandardUnEq Z} `{!FullPseudoSemiRingOrder Z}.

Notation nat_to_Z := (naturals_to_semiring nat Z).

Existing Instance to_semiring_nonneg.

Lemma induction
  P `{!Proper ((Z,=) ==> iff) P}:
  P 0 → (∀ `{n ∊ Z⁺}, P n → P (1 + n))
      → (∀ `{n ∊ Z⁻}, P n → P (n - 1)) → ∀ `{n ∊ Z}, P n.
Proof.
  intros P0 Psuc1 Psuc2 n ?.
  destruct (int_abs_sig Z nat n) as [[a p]|[a p]]; destruct (p _) as [_ Ea]; clear p;
  [| rewrite_on Z <- (negate_involutive n) ];
  rewrite_on Z <- Ea; clear Ea; revert a;
  apply peano_naturals.nat_induction; intros; preserves_simplify (nat_to_Z).
  exact P0. now apply (Psuc1 _ _).
  now rewrite_on Z -> negate_0.
  rewrite (Z $ commutativity (+) _ _), (Z $ negate_plus_distr _ _).
  now apply (Psuc2 _ _).
Qed.

(*
Lemma induction_nonneg
  (P: Z → Prop) `{!Proper ((=) ==> iff) P}:
  P 0 → (∀ n, 0 ≤ n → P n → P (1 + n)) → ∀ n, 0 ≤ n → P n.
Proof.
  intros P0 PS. rapply induction; auto.
   solve_proper.
  intros n E1 ? E2.
  destruct (rings.is_ne_0 1).
  apply (antisymmetry (≤)).
   apply (order_reflecting ((n - 1) +)). ring_simplify. now transitivity 0.
  transitivity (n - 1). easy. apply (order_reflecting (1 +)). ring_simplify.
  transitivity 0. easy. apply semirings.le_0_2.
Qed.
*)

Global Instance: Biinduction Z.
Proof.
  intros P ? P0 Psuc. apply induction; trivial.
  intros n ?. apply (Psuc n _).
  intros n ??. apply (Psuc _ _). now rewrite_on Z -> (plus_negate_r_split_alt 1 n).
Qed.

Notation Z_to_natp := (integers_to_ring Z (SRpair nat)).

Global Program Instance: SubDecision Z Z (≤) | 10 := λ x xe y ye,
  match decide_sub (≤) (Z_to_natp x) (Z_to_natp y) with
  | left E => left _
  | right E => right _
  end.
Next Obligation. now apply (order_reflecting (Z_to_natp)). Qed.
End integers.

(* A default order on the integers *)
Instance int_le `{Integers A (Z:=Z)} : Le A | 10 :=  λ x y, ∃ z, y = x + naturals_to_semiring nat Z z.
Instance int_lt `{Integers A (Z:=Z)} `{UnEq A} : Lt A | 10 := dec_lt.

Section default_order.
Context `{Integers A (Z:=Z)} `{UnEq A} `{!StandardUnEq Z}.

Notation nat_to_Z := (naturals_to_semiring nat Z).

Instance: Proper ((Z,=) ==> (Z,=) ==> impl) (≤).
Proof.
  intros x1 y1 E1 x2 y2 E2. unfold_sigs.
  intros [z p]; exists z. now rewrite_on Z <-E1, <-E2.
Qed.

Instance: PartialOrder Z.
Proof. split. apply _. apply _.
+ intros x ?. exists (0:nat). preserves_simplify (nat_to_Z). subsymmetry. exact (plus_0_r _).
+ intros x ? y ? z ? [a Ea] [b Eb]. exists (a+b). preserves_simplify (nat_to_Z).
  now rewrite (Z $ associativity (+) _ _ _), <- (Z $ Ea), (Z $ Eb).
+ intros x ? y ? [a Ea] [b Eb].
  destruct (naturals.zero_sum a b) as [E1 E2].
    apply (injective (nat_to_Z) _ _). preserves_simplify (nat_to_Z).
    apply (left_cancellation (+) x Z _ _).
    now rewrite (Z $ plus_0_r _), (Z $ associativity (+) _ _ _), <- (Z $ Ea), <- (Z $ Eb).
  change (a ≡ 0) in E1. rewrite (Z $ Ea), E1, (Z $ preserves_0). subsymmetry. exact (plus_0_r _).
Qed.

Instance: SemiRingOrder Z.
Proof.
  apply from_ring_order.
  intros z ?. split. split; apply _.
    intros x ? y ? [a Ea]. exists a. rewrite_on Z -> Ea. exact (associativity (+) _ _ _).
  intros x [? [a Ea]] y [? [b Eb]]. split. apply _. exists (a*b).
    rewrite (Z $ Ea), (Z $ Eb), 3!(Z $ plus_0_l _).
    subsymmetry. exact (preserves_mult _ _).
Qed.

Notation Z_to_r := (integers_to_ring Z (SRpair nat)).

Let P x `{x ∊ Z} y `{y ∊ Z} : Z_to_r x ≤ Z_to_r y → x ≤ y.
Proof. intro E. destruct (decompose_le E) as [a [[? Ea] Eb]].
  exists (pos a ∸ neg a). 
  apply (injective Z_to_r _ _). preserves_simplify (Z_to_r).
  rewrite (SRpair nat $ naturals.to_semiring_twice _ _ (SRpair_inject) _).
  assert (SRpair_inject (pos a ∸ neg a) = a) as F.
    destruct a as [a b]. unfold equiv, SRpair_equiv. simpl. rewrite (plus_0_r a).
    unfold le, SRpair_le in Ea. simpl in Ea. rewrite (plus_0_r a), (plus_0_l b) in Ea.
    now apply cut_minus_le.
  now rewrite_on (SRpair nat) -> F.
Qed.

Instance: TotalRelation Z (≤).
Proof. intros x ? y ?.
  now destruct (total (≤) (Z_to_r x) (Z_to_r y)); [left|right]; eapply P.
Qed.

Global Instance: FullPseudoSemiRingOrder Z.
Proof. now apply dec_full_pseudo_srorder. Qed.
End default_order.
