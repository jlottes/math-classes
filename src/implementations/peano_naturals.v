Require Import
  Arith_base abstract_algebra interfaces.naturals interfaces.orders
  theory.setoids theory.common_props theory.rings orders.semirings.
Require Import Ring stdlib_ring misc.quote.

Instance nat_equiv: Equiv nat := eq.
Instance nat_uneq: UnEq nat := _.
Instance nat_plus: Plus nat := Peano.plus.
Instance nat_0: Zero nat := 0%nat.
Instance nat_1: One nat := 1%nat.
Instance nat_mult: Mult nat := Peano.mult.

Instance nat_le: Le nat := Peano.le.
Instance nat_lt: Lt nat := Peano.lt.

Hint Extern 10 (Subset nat) => eexact (every nat) : typeclass_instances.

Local Coercion subset_to_type: Subset >-> Sortclass.
Local Notation nat := (every nat).

Instance: Setoid nat.
Proof. repeat (split; try apply _). Qed.

Instance: CommutativeSemiRing nat.
Proof with try apply _. split.
+ split... split... split...
  * red. intros. now apply plus_assoc.
  * split... intros ?? E1 ?? E2. unfold_sigs. red_sig. lazy in E1,E2. now rewrite E1,E2.
  * red. intros. now apply Plus.plus_comm.
  * red. intros. now lazy.
+ split... split... split...
  * red. intros. now apply mult_assoc.
  * split... intros ?? E1 ?? E2. unfold_sigs. red_sig. lazy in E1,E2. now rewrite E1,E2.
  * red. intros. now apply mult_comm.
  * red. intros. now apply Mult.mult_1_l.
+ red. intros. now apply mult_plus_distr_l.
+ now lazy.
Qed.

(* misc *)
Instance: Injective nat nat S.
Proof. split. intros ???? E. now injection E.
 split; try apply _. intros ?? E. unfold_sigs. red_sig. lazy in E. now rewrite E.
Qed.

Instance: Setoid_Morphism nat nat S := injective_mor S.

Global Instance nat_dec: ∀ x y, Decision (x = y) := eq_nat_dec.

Add Ring nat: (stdlib_semiring_theory nat).

Close Scope nat_scope.

Instance: NaturalsToSemiRing nat :=
  λ _ _ _ _ _ _, fix f n := match n with 0%nat => 0 | S n' => f n' + 1 end.

Section for_another_semiring.
  Context `{CommutativeSemiRing (R:=R)}.

  Notation toR := (naturals_to_semiring nat R).

  Add Ring R: (stdlib_semiring_theory R).

  Instance: Closed (nat ==> R) toR.
  Proof. intros n _. induction n; [ change (0 ∊ R) | change (toR n + 1 ∊ R) ]; apply _. Qed.

  Instance: Proper ((nat,=) ==> (R,=)) toR.
  Proof. intros n ? [_ E]. lazy in E. rewrite <- E. now red_sig. Qed.

  Let f_preserves_0: toR 0 = 0.
  Proof. subreflexivity. Qed.

  Let f_preserves_1: toR 1 = 1.
  Proof. unfold naturals_to_semiring. simpl. exact (plus_0_l _). Qed.

  Let f_preserves_plus a a': toR (a + a') = toR a + toR a'.
  Proof with subring R.
   induction a. change (toR a' = 0 + toR a')... 
   change (toR (a + a') + 1 = toR (a) + 1 + toR a'). rewrite_on R -> IHa...
  Qed.

  Let f_preserves_mult a a': toR (a * a') = toR a * toR a'.
  Proof with subring R.
   induction a. change (0 = 0 * toR a')...
   change (toR (a' + a * a') = (toR a + 1) * toR a').
   rewrite (R $ f_preserves_plus _ _), (R $ IHa)...
  Qed.

  Global Instance: SemiRing_Morphism nat R (naturals_to_semiring nat R).
  Proof. repeat (split; try apply _); repeat intro.
      apply f_preserves_plus.
     apply f_preserves_0.
    apply f_preserves_mult.
   apply f_preserves_1.
  Qed.
End for_another_semiring.

Lemma O_nat_0 : O ≡ 0.
Proof. reflexivity. Qed.

Lemma S_nat_plus_1 x : S x ≡ x + 1.
Proof. rewrite (commutativity (+) _ _). reflexivity. Qed.

Lemma S_nat_1_plus x : S x ≡ 1 + x.
Proof. reflexivity. Qed.

Lemma nat_induction (P : Datatypes.nat → Prop) :
  P 0 → (∀ n, P n → P (1 + n)) → ∀ n, P n.
Proof nat_ind P.

Instance: Naturals nat.
Proof. split; try apply _. intros.
  intros x y [_ E]. lazy in E. subst y. red_sig.
  induction x; [
    replace 0%nat with (zero:nat) by reflexivity
  | rewrite S_nat_1_plus ];
  preserves_simplify h; preserves_simplify (naturals_to_semiring nat R).
  subreflexivity. now rewrite_on R -> IHx.
Qed.

(* Misc *)
Instance: NoZeroDivisors nat.
Proof. intros x [[_ Ex] [y [[_ Ey1] [Ey2|Ey2]]]]; destruct (Mult.mult_is_O _ _ Ey2); intuition. Qed.

Instance: ∀ `{z ∊ nat ₀}, LeftCancellation (.*.) z nat.
Proof. intros z [_ Ez] x _ y _. now apply NPeano.Nat.mul_cancel_l. Qed.

(* Order *)

Instance: FullPseudoSemiRingOrder nat.
Proof.
  assert (TotalRelation nat nat_le).
   intros x _ y _. now destruct (le_ge_dec x y); intuition.
  assert (PartialOrder nat).
   split; try apply _. intros ?? [_ E1] ?? [_ E2]. lazy in E1, E2. red. now rewrite E1, E2.
   intros x _ y _ E. now apply Le.le_antisym.
  assert (SemiRingOrder nat). split. apply _. apply _.
      intros x _ y _ E. exists_sub (y - x)%nat. now apply le_plus_minus.
     intros z _. repeat (split; try apply _). intros. now apply Plus.plus_le_compat_l.
    intros. now apply plus_le_reg_l with z.
   intros x [_ ?] y [_ ?]. split. apply _. change (0 * 0 <= x * y)%nat. now apply Mult.mult_le_compat.
  apply dec_full_pseudo_srorder.
  intros. now apply NPeano.Nat.le_neq.
Qed.

Instance: OrderEmbedding nat nat S.
Proof. repeat (split; try apply _); intros ? _ ? _. apply le_n_S. apply le_S_n. Qed.

Instance: StrictOrderEmbedding nat nat S.
Proof. split; try apply _. Qed.

Instance nat_le_dec: Decision (x ≤ y) := le_dec.

(*
Instance nat_cut_minus: CutMinus nat := minus.
Instance: CutMinusSpec nat nat_cut_minus.
Proof.
  split.
   symmetry. rewrite commutativity.
   now apply le_plus_minus.
  intros x y E. destruct (orders.le_equiv_lt x y E) as [E2|E2].
   rewrite E2. now apply minus_diag.
  apply not_le_minus_0. now apply orders.lt_not_le_flip.
Qed.
*)
