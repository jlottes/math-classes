Require Import
  Arith_base abstract_algebra interfaces.naturals interfaces.orders
  theory.subsetoids theory.common_props theory.rings orders.semirings.
Require Import Ring stdlib_ring misc.quote.

Instance nat_equiv: Equiv nat := eq.
Instance nat_uneq: UnEq nat := _.
Instance nat_plus: Plus nat := Peano.plus.
Instance nat_0: Zero nat := 0%nat.
Instance nat_1: One nat := 1%nat.
Instance nat_mult: Mult nat := Peano.mult.

Local Notation N := (Every nat).

Instance: SubSetoid N.
Proof. repeat (split; try apply _). Qed.

Instance: CommutativeSemiRing N.
Proof with try apply _. split.
+ split. split... split...
  * red. intros. now apply plus_assoc.
  * split... intros ?? E1 ?? E2. unfold_sigs. red_sig. lazy in E1,E2. now rewrite E1,E2.
  * red. intros. now lazy.
  * red. intros. now apply Plus.plus_0_r.
  * red. intros. now apply Plus.plus_comm.
+ split. split... split...
  * red. intros. now apply mult_assoc.
  * split... intros ?? E1 ?? E2. unfold_sigs. red_sig. lazy in E1,E2. now rewrite E1,E2.
  * red. intros. now apply Mult.mult_1_l.
  * red. intros. now apply Mult.mult_1_r.
  * red. intros. now apply mult_comm.
+ red. intros. now apply mult_plus_distr_l.
+ now lazy.
Qed.

(* misc *)
Instance: Injective S N N.
Proof. split. intros ???? E. now injection E.
 split; try apply _. intros ?? E. unfold_sigs. red_sig. lazy in E. now rewrite E.
Qed.

Instance: SubSetoid_Morphism S N N := injective_mor S.

Global Instance nat_dec: ∀ x y: nat, Decision (x = y) := eq_nat_dec.

Add Ring nat: (stdlib_semiring_theory N).

Close Scope nat_scope.

Instance: NaturalsToSemiRing N :=
  λ _ _ _ _ _ _, fix f (n: nat) := match n with 0%nat => 0 | S n' => f n' + 1 end.

Section for_another_semiring.
  Context `{CommutativeSemiRing (R:=R)}.

  Notation toR := (naturals_to_semiring N R).

  Add Ring R: (stdlib_semiring_theory R).

  Instance: Proper ((=) ==> (=)) toR.
  Proof. unfold equiv, nat_equiv. repeat intro. subst. reflexivity. Qed.

  Instance f_closed: Closed (N ==> R) toR.
  Proof. intros n _. induction n. apply _. change (toR n + 1 ∊ R). apply _. Qed.

  Instance: SubProper ((N,=) ==> (R,=)) toR.
  Proof. intros ?? E. unfold_sigs. red_sig. now rewrite E. Qed.

  Let f_preserves_0: toR 0 = 0.
  Proof. reflexivity. Qed.

  Let f_preserves_1: toR 1 = 1.
  Proof. unfold naturals_to_semiring. simpl. subring R. Qed.

  Let f_preserves_plus a a': toR (a + a') = toR a + toR a'.
  Proof with subring R.
   induction a. change (toR a' = 0 + toR a')... 
   change (toR (a + a') + 1 = toR (a) + 1 + toR a'). rewrite_on R -> IHa...
  Qed.

  Let f_preserves_mult a a': toR (a * a') = toR a * toR a'.
  Proof with subring R.
   induction a. change (0 = 0 * toR a')...
   change (toR (a' + a * a') = (toR a + 1) * toR a').
   rewrite f_preserves_plus. rewrite_on R -> IHa...
  Qed.

  Global Instance: SemiRing_Morphism (naturals_to_semiring N R) N R.
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
Proof. rewrite (commutativity (S:=N) _ _). reflexivity. Qed.

Lemma S_nat_1_plus x : S x ≡ 1 + x.
Proof. reflexivity. Qed.

Lemma nat_induction (P : nat → Prop) :
  P 0 → (∀ n, P n → P (1 + n)) → ∀ n, P n.
Proof nat_ind P.

Instance: Naturals N.
Proof. split; try apply _. intros. pose proof (f_closed (R:=R)).
  intros x y E. unfold_sigs. unfold equiv, nat_equiv in E. subst y.
  induction x; [
    replace 0%nat with (zero:nat) by reflexivity
  | rewrite S_nat_1_plus ];
  preserves_simplify h (N) R;
  preserves_simplify (naturals_to_semiring N R) (N) R.
  reflexivity. now rewrite_on R -> (IHx _ _).
Qed.

(* Misc *)
Instance: NoZeroDivisors N.
Proof. intros x [[_ Ex] [y [[_ Ey1] [Ey2|Ey2]]]]; destruct (Mult.mult_is_O _ _ Ey2); intuition. Qed.

Instance: ∀ `{z ∊ N ₀}, LeftCancellation (.*.) z N.
Proof. intros z [_ Ez] x _ y _. now apply NPeano.Nat.mul_cancel_l. Qed.

(* Order *)
Instance nat_le: Le nat := Peano.le.
Instance nat_lt: Lt nat := Peano.lt.

Instance: FullPseudoSemiRingOrder N.
Proof.
  assert (TotalRelation nat_le N).
   intros x _ y _. now destruct (le_ge_dec x y); intuition.
  assert (PartialOrder N).
   split; try apply _. intros ?? E1 ?? E2. unfold_sigs. lazy in E1, E2. red. now rewrite E1, E2.
   intros x _ y _ E. now apply Le.le_antisym.
  assert (SemiRingOrder N). split. apply _. apply _.
      intros x _ y _ E. exists_sub (y - x)%nat. now apply le_plus_minus.
     intros z _. repeat (split; try apply _). intros. now apply Plus.plus_le_compat_l.
    intros. now apply plus_le_reg_l with z.
   intros x [_ ?] y [_ ?]. split. apply _. change (0 * 0 <= x * y)%nat. now apply Mult.mult_le_compat.
  apply dec_full_pseudo_srorder.
  intros. now apply NPeano.Nat.le_neq.
Qed.

Instance: OrderEmbedding S N N.
Proof. repeat (split; try apply _); intros ? _ ? _. apply le_n_S. apply le_S_n. Qed.

Instance: StrictOrderEmbedding S N N.
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
