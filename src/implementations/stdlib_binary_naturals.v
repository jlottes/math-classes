Require Import
  NArith peano_naturals theory.naturals
  abstract_algebra interfaces.naturals interfaces.orders
  interfaces.additional_operations
  theory.setoids theory.jections
  orders.lattices orders.minmax lattice_ordered_rings.

(* canonical names for relations/operations/constants: *)
Instance N_equiv : Equiv N := eq.
Instance N_uneq : UnEq N := _.
Instance N_0 : Zero N := 0%N.
Instance N_1 : One N := 1%N.
Instance N_plus : Plus N := N.add.
Instance N_mult : Mult N := N.mul.

Instance N_le: Le N := N.le.
Instance N_lt: Lt N := N.lt.

Instance N_cut_minus: CutMinus N := N.sub.

Instance N_div : DivEuclid N := N.div.
Instance N_mod : ModEuclid N := N.modulo.

Hint Extern 10 (@set N) => eexact (every N) : typeclass_instances.

Local Notation N   := (every N  ).
Local Notation nat := (every nat).
Local Open Scope mc_fun_scope.

Instance: Setoid N := {}.

Instance: DenialInequality N.
Proof. unfold N_uneq. apply _. Qed.

(* properties: *)
Instance: CommutativeSemiRing N.
Proof.
  repeat match goal with
  | |- Morphism (_ ⇒ _ ⇒ _) _ => apply binary_morphism_proper_back; intros ?? [_ E1] ?? [_ E2];
       red_sig; lazy in E1,E2; now rewrite E1,E2
  | |- Morphism _ _ => intros ?? [_ E1];
       red_sig; lazy in E1; now rewrite E1
  | |- _ => split; try apply _
  end; repeat intro.
+ now apply Nplus_assoc.
+ now apply Nplus_comm.
+ now apply Nmult_assoc.
+ now apply Nmult_comm.
+ now apply Nmult_1_l.
+ now apply Nmult_plus_distr_l.
Qed.

Instance: ∀ x y, Decision (x = y) := N_eq_dec.

Instance inject_nat_N: Cast nat N := N_of_nat.
Instance inject_N_nat: Cast N nat := nat_of_N.

Instance: SemiRing_Morphism N nat (').
Proof. apply rings.semiring_morphism_alt; try apply _.
+ eapply every_Morphism; apply _.
+ intros. apply nat_of_Nplus.
+ intros. apply nat_of_Nmult.
+ reflexivity.
+ reflexivity.
Qed.

Instance: Inverse (cast N nat) := (cast nat N).

Instance: Surjective N nat (').
Proof. split; [| apply _ | intros ??; apply _].
  intros x y [_ E]. lazy in E. red_sig. rewrite <- E. now apply nat_of_N_of_nat.
Qed.

Instance: Injective N nat (').
Proof. constructor. intros x _ y _. exact (nat_of_N_inj _ _). apply _. Qed.

Instance: Bijective N nat (') := {}.

Instance: Inverse (cast nat N) := (cast N nat).

Instance: Bijective nat N (') := flip_bijection _.

Instance: SemiRing_Morphism nat N (') := _ : SemiRing_Morphism nat N (')⁻¹.

Instance: NaturalsToSemiRing N := retract_is_nat_to_sr (cast nat N).
Instance: Naturals N := retract_is_nat (cast nat N).

(* order *)
Section order.
  Instance: PartialOrder N.
  Proof.
    repeat (split; try apply _).
    intros ?? [_ E1] ?? [_ E2]. lazy in E1, E2. now rewrite E1,E2.
    intros ? _ ? _. exact (N.le_antisymm _ _).
  Qed.

  Instance: SemiRingOrder N.
  Proof. split. apply _. apply _.
  + intros x _ y _ E. exists_sub (y-x)%N.
      symmetry. rewrite (commutativity (+) _ _). now apply N.sub_add.
  + intros z _. split; (split; [split; apply _ |]); intros x _ y _;
    eapply N.add_le_mono_l.
  + intros x [_ ?] y [_ ?]. split. apply _. now apply Nle_0.
  Qed.

  Instance: TotalRelation N (≤).
  Proof. intros x _ y _. now apply N.le_ge_cases. Qed.

  Global Instance: FullPseudoSemiRingOrder N.
  Proof. apply semirings.dec_full_pseudo_srorder.
    intros x _ y _. split. apply N.le_neq. intros [??]. now apply N.Private_Tac.le_neq_lt.
  Qed.
End order.

Program Instance: ∀ x y, Decision (x ≤ y) := λ y x,
  match Ncompare y x with
  | Gt => right _
  | _ => left _
  end.
Next Obligation. now apply not_symmetry. Qed.

Instance: FullLatticeOrder N := dec_full_lattice_order.
Instance: SemiRingLatticeOrder N := dec_semiring_lattice_order.

Local Ltac binary_mor_tac := apply binary_morphism_proper_back;
  intros ?? [_ E1] ?? [_ E2]; red_sig; lazy in E1,E2; now rewrite E1,E2.

Instance: CutMinusSpec N _.
Proof. split.
+ binary_mor_tac.
+ intros x _ y _. now apply N.sub_add.
+ intros x _ y _. now apply Nminus_N0_Nle.
Qed.

Instance: EuclidSpec N.
Proof. split.
+ binary_mor_tac.
+ binary_mor_tac.
+ intros x ? y [??]. now apply N.div_mod.
+ intros x ? y [??]. left. split. apply Nle_0. now apply N.mod_lt.
Qed.
