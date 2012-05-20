Require Import
  NArith peano_naturals theory.naturals
  abstract_algebra interfaces.naturals interfaces.orders
  interfaces.additional_operations
  theory.setoids theory.jections.

(* canonical names for relations/operations/constants: *)
Instance N_equiv : Equiv N := eq.
Instance N_0 : Zero N := 0%N.
Instance N_1 : One N := 1%N.
Instance N_plus : Plus N := Nplus.
Instance N_mult : Mult N := Nmult.

Instance N_le: Le N := Nle.
Instance N_lt: Lt N := Nlt.

Instance N_cut_minus: CutMinus N := Nminus.

Hint Extern 10 (Subset N) => eexact (every N) : typeclass_instances.

Local Notation N   := (every N  ).
Local Notation nat := (every nat).
Local Open Scope mc_fun_scope.

Instance: Setoid N := {}.

(* properties: *)
Instance: CommutativeSemiRing N.
Proof.
  repeat match goal with
  | |- Setoid_Binary_Morphism _ _ _ _ => split; try apply _; intros ?? [_ E1] ?? [_ E2];
       red_sig; lazy in E1,E2; now rewrite E1,E2
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

Instance: SemiRing_Morphism N nat (cast N nat).
Proof.
  repeat (split; try apply _); repeat intro.
  + unfold_sigs. match goal with E : _ = _ |- _ => lazy in E; now rewrite E end.
  + now apply nat_of_Nplus.
  + unfold_sigs. match goal with E : _ = _ |- _ => lazy in E; now rewrite E end.
  + now apply nat_of_Nmult.
Qed.

Instance: Inverse (cast N nat) := (cast nat N).

Instance: Surjective N nat (cast N nat).
Proof. split; [| apply _ | intros ??; apply _].
  intros x y [_ E]. lazy in E. red_sig. rewrite <- E. now apply nat_of_N_of_nat.
Qed.

Instance: Injective N nat (cast N nat).
Proof. constructor. intros x _ y _. exact (nat_of_N_inj _ _). apply _. Qed.

Instance: Bijective N nat (cast N nat) := {}.

Instance: Inverse (cast nat N) := (cast N nat).

Instance: Bijective nat N (cast nat N) := flip_bijection.

Instance: SemiRing_Morphism nat N (cast nat N).
Proof _ : SemiRing_Morphism nat N (cast N nat)⁻¹. 

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
  Proof. split; try apply _.
  + intros x _ y _ E. exists_sub (Nminus y x).
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

Instance: CutMinusSpec N _.
Proof.
  split; try apply _.
  + split; try apply _. intros ?? [_ E1] ?? [_ E2]. red_sig. lazy in E1,E2. now rewrite E1,E2.
  + intros x _ y _. now apply N.sub_add.
  + intros x _ y _. now apply Nminus_N0_Nle.
Qed.
