Require
  stdlib_binary_integers theory.integers orders.semirings.
Require Import
  ZSig ZSigZAxioms NArith ZArith
  nonneg_integers_naturals interfaces.orders
  abstract_algebra interfaces.integers interfaces.additional_operations
  theory.setoids theory.jections theory.rings theory.shiftl.

Module ZType_Integers (Import anyZ: ZType).

Module axioms := ZTypeIsZAxioms anyZ.

Instance ZType_equiv : Equiv t := eq.
Instance ZType_plus : Plus t := add.
Instance ZType_0 : Zero t := zero.
Instance ZType_1 : One t := one.
Instance ZType_mult : Mult t := mul.
Instance ZType_negate: Negate t := opp.

Instance  ZType_le: Le t := le.
Instance  ZType_lt: Lt t := lt.

Hint Extern 10 (@Subset t) => eexact (every t) : typeclass_instances.

Local Notation T := (every t).
Local Notation N := (every N).
Local Notation Z := (every Z).
Local Open Scope mc_fun_scope.

Instance: Setoid T | 10 := {}.

Program Instance: ∀ x y: t, Decision (x = y) := λ x y,
  match compare x y with
  | Eq => left _
  | _ => right _
  end.
Next Obligation.
  apply Zcompare_Eq_eq. now rewrite <-spec_compare.
Qed.
Next Obligation.
  rewrite spec_compare in *.
  intros E.
  apply Zcompare_Eq_iff_eq in E. auto.
Qed.

Instance: DenialInequality T := _.
Instance: StrongSetoid T := strong_setoids.dec_strong_setoid.

Instance: CommutativeRing T | 10.
Proof. repeat match goal with
 | |- Morphism _ (@sg_op _ ?op) =>
      apply binary_morphism_proper_back; intros ?? [_ E1] ?? [_ E2];
      unfold equiv, ZType_equiv in E1,E2; red_sig; now rewrite E1,E2
 | |- Morphism _ (@inv _ ?op) =>
      intros ?? [_ E1];
      unfold equiv, ZType_equiv in E1; red_sig; now rewrite E1
 | _ => split; try apply _
 end; repeat intro; lazy; axioms.zify; auto with zarith.
Qed.

Ltac unfold_equiv := unfold equiv, ZType_equiv, 
  stdlib_binary_integers.Z_equiv, stdlib_binary_naturals.N_equiv, eq in *.

Instance inject_ZType_Z: Cast T Z := to_Z.

Instance: Ring_Morphism T Z (').
Proof. apply (ring_morphism_alt _); [| intros; unfold cast, inject_ZType_Z ..].
  + intros ?? [_ E]. now red_sig.
  + exact (spec_add _ _).
  + exact (spec_mul _ _).
  + exact spec_1.
Qed.

Instance inject_Z_ZType: Cast Z T := of_Z.
Instance: Inverse (cast T Z) := (cast Z T).

Instance: Surjective T Z (').
Proof.
  split; try apply _. intros x y [_ E]. red_sig.
  rewrite <-E. change (to_Z (of_Z x) = x). now rewrite spec_of_Z.
  intros ??; apply _.
Qed.

Instance: Injective T Z (').
Proof. split; try apply _. now intros x _ y _ E. Qed.

Instance: Bijective T Z (') := {}.

Instance: Inverse (cast Z T) := cast T Z.

Instance: Bijective Z T (') := flip_bijection _.

Instance: Ring_Morphism Z T (') := _ : Ring_Morphism Z T (')⁻¹.

Instance: IntegersToRing T := integers.retract_is_int_to_ring (cast Z T).
Instance: Integers T := integers.retract_is_int (cast Z T).

(* Order *)
Instance: SemiRingOrder T.
Proof. apply (semirings.projected_srorder (cast T Z)); intros x _ y _. reflexivity.
  intro E. exists_sub (sub y x).
  unfold_equiv. rewrite spec_add, spec_sub. ring.
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
Program Instance: ∀ x y: t, Decision (x ≤ y) := λ x y,
  match compare x y with
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

(*
Program Instance: Abs t := abs.
Next Obligation.
  split; intros E; unfold_equiv; rewrite spec_abs.
   apply Z.abs_eq.
   apply (order_preserving to_Z) in E.
   now rewrite rings.preserves_0 in E.
  rewrite rings.preserves_negate.
  apply Z.abs_neq.
  apply (order_preserving to_Z) in E.
  now rewrite rings.preserves_0 in E.
Qed.

(* Efficient division *)
Instance ZType_div: DivEuclid t := anyZ.div.
Instance ZType_mod: ModEuclid t := modulo.

Instance: EuclidSpec t ZType_div ZType_mod.
Proof.
  split; try apply _; unfold div_euclid, ZType_div.
     intros x y E. now apply axioms.div_mod.
    intros x y Ey.
    destruct (Z_mod_remainder (to_Z x) (to_Z y)) as [[Hl Hr] | [Hl Hr]].
      intro. apply Ey. apply (injective to_Z). now rewrite rings.preserves_0.
     left; split.
      apply (order_reflecting to_Z). now rewrite spec_modulo, rings.preserves_0.
     apply (strictly_order_reflecting to_Z). now rewrite spec_modulo.
    right; split.
      apply (strictly_order_reflecting to_Z). now rewrite spec_modulo.
     apply (order_reflecting to_Z). now rewrite spec_modulo, rings.preserves_0.
   intros x. unfold_equiv. rewrite spec_div, rings.preserves_0. now apply Zdiv_0_r.
  intros x. unfold_equiv. rewrite spec_modulo, rings.preserves_0. now apply Zmod_0_r.
Qed.
*)

Lemma ZType_preserves_1 : to_Z 1 ≡ 1.
Proof preserves_1.

Lemma ZType_succ_1_plus x : succ x = 1 + x.
Proof.
  unfold_equiv. rewrite spec_succ, (preserves_plus _ _), ZType_preserves_1.
  exact (commutativity (+) _ _).
Qed.

Lemma ZType_two_2 : two = 2.
Proof.
  unfold_equiv. rewrite spec_2.
  now rewrite (preserves_plus _ _), ZType_preserves_1.
Qed.

(* Efficient [nat_pow] *)
Instance ZType_pow: Pow t t := pow.

Instance: NatPowSpec T T⁺ ZType_pow.
Proof. split.
+ apply binary_morphism_proper_back.
  intros x1 y1 [_ E1] x2 y2 [_ E2]. red_sig.
  now apply axioms.pow_wd.
+ intros x1 _. apply axioms.pow_0_r.
+ intros x _ n [_ ?].
  unfold_equiv. unfold "^", ZType_pow. simpl.
  rewrite <-axioms.pow_succ_r; try easy.
  pose proof ZType_succ_1_plus n as E.
  now apply axioms.pow_wd.
Qed.

Instance ZType_Npow: Pow t BinNums.N := pow_N.

Instance: NatPowSpec T N ZType_Npow.
Proof. split; unfold "^", ZType_Npow.
+ apply binary_morphism_proper_back.
    intros x1 y1 [_ E1] x2 y2 [_ E2]. red_sig. unfold_equiv.
    now rewrite 2!spec_pow_N, E1, E2.
+ intros x1 _. unfold_equiv.
   now rewrite spec_pow_N, ZType_preserves_1.
+ intros x _ n _. unfold_equiv.
  rewrite spec_mul, 2!spec_pow_N.
  pose proof preserves_plus (f:=Z.of_N) 1 n as E. unfold_equiv. rewrite E.
  rewrite Z.pow_add_r.
    pose proof preserves_1 (f:=Z.of_N) as E'. unfold_equiv. rewrite E'.
    now rewrite Z.pow_1_r.
   easy.
  now apply Z_of_N_le_0.
Qed.

(*
(* Efficient [log 2] *)
Program Instance: Log (2:t) (t⁺) := log2.
Next Obligation with auto.
  intros x.
  apply to_Z_Zle_sr_le.
  rewrite spec_log2, preserves_0.
  apply Z.log2_nonneg.
Qed.

Next Obligation with auto.
  intros [x Ex].
  destruct (axioms.log2_spec x) as [E1 E2].
   apply to_Z_sr_le_Zlt...
  unfold nat_pow, nat_pow_sig, ZType_pow; simpl.
  apply to_Z_Zle_sr_le in E1. apply to_Z_Zlt_sr_le in E2.
  rewrite ZType_two_2 in E1, E2.
  rewrite ZType_succ_plus_1, commutativity in E2...
Qed.
*)

(* Efficient [shiftl] *)
Instance ZType_shiftl: ShiftL t t := shiftl.

Instance: ShiftLSpec T T⁺ ZType_shiftl.
Proof.
  apply shiftl_spec_from_nat_pow.  intros ? _ ? _; exact _.
  intros x _ y [_ Ey].
  unfold additional_operations.pow, ZType_pow, additional_operations.shiftl, ZType_shiftl.
  unfold_equiv.
  rewrite (preserves_mult _ _), spec_pow.
  rewrite spec_shiftl, Z.shiftl_mul_pow2.
   rewrite <-ZType_two_2, spec_2. exact (commutativity (.*.) _ _).
  apply (order_preserving to_Z _ _) in Ey. now rewrite preserves_0 in Ey.
Qed.

(* Efficient [shiftr] *)
Instance: ShiftR t t := shiftr.

End ZType_Integers.
