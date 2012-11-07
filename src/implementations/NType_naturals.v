Require
  stdlib_binary_integers theory.integers orders.semirings.
Require Import
  NSig NSigNAxioms NArith ZArith
  abstract_algebra interfaces.naturals interfaces.integers
  interfaces.orders interfaces.additional_operations
  theory.setoids theory.jections theory.rings theory.shiftl.

Module NType_Integers (Import anyN: NType).

Module axioms := NTypeIsNAxioms anyN.

Instance NType_equiv : Equiv t := eq.
Instance NType_plus : Plus t := add.
Instance NType_0 : Zero t := zero.
Instance NType_1 : One t := one.
Instance NType_mult : Mult t := mul.

Instance  NType_le: Le t := le.
Instance  NType_lt: Lt t := lt.

Hint Extern 10 (@Subset t) => eexact (every t) : typeclass_instances.

Local Notation T := (every t).
Local Notation N := (every N).
Local Notation Z := (every Z).
Local Open Scope mc_fun_scope.

Instance: Setoid T | 10 := {}.

Program Instance: ∀ x y: t, Decision (x = y) := λ x y, match compare x y with
  | Eq => left _
  | _ => right _
  end.
Next Obligation.
  apply Zcompare_Eq_eq. now rewrite <-spec_compare.
Qed.
Next Obligation.
  rewrite spec_compare in *. intros E.
  apply Zcompare_Eq_iff_eq in E. auto.
Qed.

Instance: StandardUnEq T := _.
Instance: StrongSetoid T := strong_setoids.dec_strong_setoid.

Instance: CommutativeSemiRing T | 10.
Proof. repeat match goal with
 | |- Morphism _ (@sg_op _ ?op) =>
      apply binary_morphism_proper_back; intros ?? [_ E1] ?? [_ E2];
      unfold equiv, NType_equiv in E1,E2; red_sig; now rewrite E1,E2
 | _ => split; try apply _
 end; repeat intro; lazy; axioms.zify; auto with zarith.
Qed.

Ltac unfold_equiv := unfold equiv, NType_equiv, eq in *.

Instance inject_NType_N: Cast T N := to_N.

Instance: SemiRing_Morphism T N (').
Proof. apply (semiring_morphism_alt _); [| intros; unfold cast, inject_NType_N, to_N ..].
  + intros ?? E. unfold_sigs. unfold_equiv. red_sig.
    unfold cast, inject_NType_N, to_N. now rewrite E.
  + now rewrite spec_add, Z2N.inj_add by apply spec_pos.
  + now rewrite spec_mul, Z2N.inj_mul by apply spec_pos.
  + unfold canonical_names.zero, NType_0. now rewrite spec_0.
  + unfold canonical_names.one, NType_1. now rewrite spec_1.
Qed.

Instance inject_N_NType: Cast N T := of_N.
Instance: Inverse (cast T N) := cast N T.

Instance: Surjective T N (').
Proof.
  split; try apply _. intros x y [_ E]. red_sig.
  rewrite <-E. change (to_N (of_N x) = x). unfold to_N. rewrite spec_of_N.
  apply N2Z.id.
  intros ??; apply _.
Qed.

Instance: Injective T N (').
Proof.
  split; try apply _. intros x _ y _ E.
  unfold equiv, NType_equiv, eq. unfold cast, inject_NType_N, to_N in E.
  rewrite <-(Z2N.id (to_Z x)), <-(Z2N.id (to_Z y)) by now apply spec_pos.
  now rewrite E.
Qed.

Instance: Bijective T N (') := {}.

Instance: Inverse (cast N T) := cast T N.

Instance: Bijective N T (') := flip_bijection _.

Instance: SemiRing_Morphism N T (') := _ : SemiRing_Morphism N T (')⁻¹.

Instance: NaturalsToSemiRing T := naturals.retract_is_nat_to_sr (cast N T).
Instance: Naturals T := naturals.retract_is_nat (cast N T).

Instance inject_NType_Z: Cast T Z := to_Z.

Instance: SemiRing_Morphism T Z (').
Proof. apply (semiring_morphism_alt _).
+ intros ?? [_ E]. red_sig. exact E.
+ intros ? _ ? _. exact (spec_add _ _).
+ intros ? _ ? _. exact (spec_mul _ _).
+ exact spec_0.
+ exact spec_1.
Qed.

(* Order *)
Instance: SemiRingOrder T.
Proof. apply (semirings.projected_srorder (cast T Z)); intros x _ y _. reflexivity.
  intro E. exists_sub (sub y x).
  unfold_equiv. rewrite spec_add, spec_sub.
  rewrite Zmax_r by now apply Z.le_0_sub.
  ring.
Qed.

Instance: OrderEmbedding T Z (').
Proof. now repeat (split; try apply _). Qed.

Instance: TotalRelation T (≤).
Proof. now apply (maps.projected_total_order (cast T Z)). Qed.

Instance: FullPseudoSemiRingOrder T.
Proof.
  apply semirings.dec_full_pseudo_srorder.
  intros x _ y _. split.
   intro. split.
    apply axioms.lt_eq_cases. now left.
   intros E. destruct (subirreflexivity (<) (to_Z x)).
   unfold_equiv. now rewrite E at 2.
  intros [E1 E2].
  now destruct (proj1 (axioms.lt_eq_cases _ _) E1).
Qed.

(* Efficient comparison *)
Program Instance: ∀ x y: t, Decision (x ≤ y) := λ x y, match (compare x y) with
  | Gt => right _
  | _ => left _
  end.
Next Obligation.
  rewrite spec_compare in *.
  destruct (Zcompare_spec (to_Z x) (to_Z y)); try discriminate.
  now apply orders.lt_not_le_flip.
Qed.
Next Obligation.
  rewrite spec_compare in *.
  destruct (Zcompare_spec (to_Z x) (to_Z y)); try discriminate; try intuition.
   now apply Zeq_le.
  now apply orders.lt_le.
Qed.

Lemma NType_preserves_1 : to_Z 1 ≡ 1.
Proof preserves_1.

Lemma NType_succ_1_plus x : succ x = 1 + x.
Proof.
  unfold_equiv. rewrite spec_succ, (preserves_plus _ _), NType_preserves_1.
  now rewrite (commutativity (+) _ _).
Qed.

Lemma NType_two_2 : two = 2.
Proof.
  unfold_equiv. rewrite spec_2.
  now rewrite (preserves_plus _ _), NType_preserves_1.
Qed.

(* Efficient [nat_pow] *)
Program Instance NType_pow: Pow t t := pow.

Instance: NatPowSpec T T _.
Proof. split.
+ apply binary_morphism_proper_back. intros x1 y1 [_ E1] x2 y2 [_ E2]. red_sig.
  now apply axioms.pow_wd.
+ intros x1 _. apply axioms.pow_0_r.
+ intros x _ n _.
  unfold_equiv. unfold "^", NType_pow.
  rewrite <-axioms.pow_succ_r by (red; rewrite spec_0; apply spec_pos).
  pose proof NType_succ_1_plus n as E.
  now apply axioms.pow_wd.
Qed.

(* Efficient [shiftl] *)
Program Instance NType_shiftl: ShiftL t t := shiftl.

Instance: ShiftLSpec T T NType_shiftl.
Proof.
  apply shiftl_spec_from_nat_pow. intros ? _ ? _; exact _.
  intros x ? y ?.
  unfold additional_operations.pow, NType_pow, additional_operations.shiftl, NType_shiftl.
  unfold_equiv. simpl.
  rewrite rings.preserves_mult, spec_pow; try apply _.
  rewrite spec_shiftl, Z.shiftl_mul_pow2 by apply spec_pos.
  rewrite <-NType_two_2, spec_2.
  exact (commutativity (.*.) _ _).
Qed.

(* Efficient [shiftr] *)
Program Instance: ShiftR t t := shiftr.
End NType_Integers.
