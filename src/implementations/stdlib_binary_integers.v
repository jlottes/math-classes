Require
  interfaces.naturals theory.naturals peano_naturals theory.integers.
Require Import
  BinInt Ring Arith NArith ZArith ZBinary
  abstract_algebra interfaces.integers
  natpair_integers stdlib_binary_naturals
  interfaces.additional_operations interfaces.orders
  nonneg_integers_naturals
  theory.setoids theory.jections theory.rings
  stdlib_ring misc.quote.

(* canonical names: *)
Instance Z_equiv: Equiv Z := eq.
Instance Z_plus: Plus Z := Zplus.
Instance Z_0: Zero Z := 0%Z.
Instance Z_1: One Z := 1%Z.
Instance Z_mult: Mult Z := Zmult.
Instance Z_negate: Negate Z := Zopp.
  (* some day we'd like to do this with [Existing Instance] *)

Instance Z_le: Le Z := Zle.
Instance Z_lt: Lt Z := Zlt.


Hint Extern 10 (Subset Z) => eexact (every Z) : typeclass_instances.

Local Notation Z   := (every Z  ).
Local Notation N   := (every N  ).
Local Notation nat := (every nat).
Local Coercion subset_to_type: Subset >-> Sortclass.
Local Open Scope mc_fun_scope.

Instance: Setoid Z := {}.

Instance: CommutativeRing Z.
Proof.
  repeat match goal with
  | |- Setoid_Binary_Morphism _ _ _ _ => split; try apply _; intros ?? [_ E1] ?? [_ E2];
       red_sig; lazy in E1,E2; now rewrite E1,E2
  | |- Setoid_Morphism _ _ _ => split; try apply _; intros ?? [_ E1];
       red_sig; lazy in E1; now rewrite E1
  | |- _ => split; try apply _
  end; repeat intro.
+ now apply Zplus_assoc.
+ now apply Zplus_comm.
+ now apply Zplus_opp_l.
+ now apply Zmult_assoc.
+ now apply Zmult_comm.
+ now apply Zmult_1_l.
+ now apply Zmult_plus_distr_r.
Qed.

(* misc: *)
Instance: ∀ x y, Decision (x = y) := ZArith_dec.Z_eq_dec.

Add Ring Z: (stdlib_ring_theory Z).

(* * Embedding N into Z *)
Instance inject_N_Z: Cast N Z := Z_of_N.

Instance: SemiRing_Morphism N Z (cast N Z).
Proof. apply (semiring_morphism_alt _).
+ split; try apply _. intros ?? [_ E1]; red_sig; lazy in E1; now rewrite E1.
+ intros x _ y _. exact (Znat.Z_of_N_plus _ _).
+ intros x _ y _. exact (Znat.Z_of_N_mult _ _).
+ reflexivity.
+ reflexivity.
Qed.

Instance: Injective N Z (cast N Z).
Proof.
  repeat (split; try apply _).
  intros x _ y _ E. now apply Znat.Z_of_N_eq_iff.
Qed.

(* SRpair N and Z are isomorphic *)
Definition Npair_to_Z : SRpair N ⇀ Z := λ x, 'pos x - 'neg x.

Instance: Ring_Morphism (SRpair N) Z Npair_to_Z.
Proof. apply (ring_morphism_alt _).
+ split; try apply _. intros [a b] [c d] [_ E]. do 2 red in E. red_sig. unfold Npair_to_Z.
  simpl. apply (right_cancellation (+) ('d+'b) Z _ _).
  transitivity ('a + 'd). subring (Z).
  transitivity ('c + 'b); [| subring (Z)].
  now rewrite <- !(Z $ preserves_plus _ _), (N $ E).
+ intros [a b] _ [c d] _. unfold Npair_to_Z. simpl. preserves_simplify (cast N Z). subring (Z).
+ intros [a b] _ [c d] _. unfold Npair_to_Z. simpl. preserves_simplify (cast N Z). subring (Z).
+ reflexivity.
Qed.

Instance: Injective (SRpair N) Z Npair_to_Z.
Proof. split; [| apply _].
  intros [a b] _ [c d] _ E. unfold Npair_to_Z in E. do 2 red. simpl in E.
  apply (injective (cast N Z) _ _). preserves_simplify (cast N Z).
  apply (right_cancellation (+) ('a - 'b) Z _ _). rewrite_on Z -> E at 1. subring (Z).
Qed.

Definition Z_to_Npair: Z ⇀ SRpair N := λ x,
  match x with
  | Z0 => C 0 0
  | Zpos p => C (Npos p) 0
  | Zneg p => C 0 (Npos p)
  end.
Instance: Inverse Npair_to_Z := Z_to_Npair.

Instance: Surjective (SRpair N) Z Npair_to_Z.
Proof. split; [| apply _ | intros x _; destruct (Npair_to_Z⁻¹ x); split; apply _ ].
  intros [|?|?] ? [_ E]; red_sig; now rewrite <- E.
Qed.

Instance: Bijective (SRpair N) Z Npair_to_Z := {}.

Instance: SemiRing_Morphism Z (SRpair N) Z_to_Npair := _ : SemiRing_Morphism _ _ (Npair_to_Z⁻¹).

Instance: IntegersToRing Z := integers.retract_is_int_to_ring Npair_to_Z.
Instance: Integers Z := integers.retract_is_int Npair_to_Z.


Instance: ∀ x y, Decision (x ≤ y) := ZArith_dec.Z_le_dec.
Instance: ∀ x y, Decision (x < y) := ZArith_dec.Z_lt_dec.

Instance: SemiRingOrder Z.
Proof.
  assert (PartialOrder Z).
   repeat (split; try apply _).
   intros ?? [_ E1] ?? [_ E2]. lazy in E1,E2. now rewrite E1,E2.
   intros ? _ ? _. exact (Zorder.Zle_antisym _ _).
  rapply rings.from_ring_order. intros z _.
   repeat (split; try apply _).
   intros x _ y _ E. now apply Zorder.Zplus_le_compat_l.
  intros x [_ E] y [_ F]. split. apply _. now apply Zorder.Zmult_le_0_compat.
Qed.

Instance: TotalRelation Z (≤).
Proof.
  intros x _ y _.
  destruct (Zorder.Zle_or_lt x y); intuition.
  right. now apply Zorder.Zlt_le_weak.
Qed.

Instance: FullPseudoSemiRingOrder Z.
Proof.
  rapply semirings.dec_full_pseudo_srorder.
  intros x _ y _. split.
   intro. split. now apply Zorder.Zlt_le_weak. now apply Zorder.Zlt_not_eq.
  intros [E1 E2]. destruct (Zorder.Zle_lt_or_eq _ _ E1). easy. now destruct E2.
Qed.

(* * Embedding of the Peano naturals into [Z] *)
Instance inject_nat_Z: Cast nat Z := Z_of_nat.

Instance: SemiRing_Morphism nat Z (cast nat Z).
Proof. apply (semiring_morphism_alt _).
+ split; try apply _. intros ?? [_ E]. red_sig. lazy in E. now rewrite E.
+ intros x _ y _. exact (Znat.inj_plus _ _).
+ intros x _ y _. exact (Znat.inj_mult _ _).
+ reflexivity.
+ reflexivity.
Qed.

(* absolute value *)
Program Instance Z_abs_nat: IntAbs Z nat := λ x,
  match x with
  | Z0 => inl (0:nat)
  | Zpos p => inl (nat_of_P p)
  | Zneg p => inr (nat_of_P p)
  end.
Next Obligation. split. apply _. reflexivity. Qed.
Next Obligation. split. apply _. now rewrite <-(naturals.to_semiring_unique Z_of_nat), Znat.Z_of_nat_of_P. Qed.
Next Obligation. split. apply _. now rewrite <-(naturals.to_semiring_unique Z_of_nat), Znat.Z_of_nat_of_P. Qed.

Program Instance Z_abs_N: IntAbs Z N := λ x,
  match x with
  | Z0 => inl (0:N)
  | Zpos p => inl (Npos p)
  | Zneg p => inr (Npos p)
  end.
Next Obligation. split. apply _. reflexivity. Qed.
Next Obligation. split. apply _. now rewrite <-(naturals.to_semiring_unique Z_of_N). Qed.
Next Obligation. split. apply _. now rewrite <-(naturals.to_semiring_unique Z_of_N). Qed.

Lemma Zpos_pos p : Zpos p ∊ Z₊.
Proof. split. apply _. apply Zgt_lt. exact (Zgt_pos_0 _). Qed.
Hint Extern 2 (Zpos _ ∊ (every BinNums.Z)₊) => eapply Zpos_pos : typeclass_instances.

Lemma Zpos_nonneg p : Zpos p ∊ Z⁺.
Proof. pose proof Zpos_pos p. apply _. Qed.
Hint Extern 2 (Zpos _ ∊ (every BinNums.Z)⁺) => eapply Zpos_nonneg : typeclass_instances.

Program Instance Z_abs: IntAbs Z Z⁺ := λ x,
  match x with
  | Z0 => inl x
  | Zpos p => inl x
  | Zneg p => inr (Zpos p)
  end.
Next Obligation. split. exact (_:0 ∊ Z⁺). reflexivity. Qed.
Next Obligation. split. apply _. symmetry. exact (naturals.to_semiring_unique (id:Z⁺ ⇀ Z) _). Qed.
Next Obligation. split. apply _. now rewrite <- (naturals.to_semiring_unique (id:Z⁺ ⇀ Z) _). Qed.

(* Efficient nat_pow *)
Instance Z_pow: Pow Z Z := Z.pow.

Instance: NatPowSpec Z Z⁺ _.
Proof. split.
+ split; try apply _. intros ?? [_ E1] ?? [_ E2]. lazy in E1,E2. red_sig. now rewrite E1,E2.
+ intros x _. now apply Z.pow_0_r.
+ intros x _ n ?. rewrite <- (Z.pow_1_r x) at 2. apply Z.pow_add_r.
  auto with zarith. firstorder.
Qed.

(*
Instance Z_Npow: Pow Z N := λ x n, Z.pow x ('n).

Instance: NatPowSpec Z N Z_Npow.
Proof.
  split; unfold pow, Z_Npow.
    solve_proper.
   intros. now apply Z.pow_0_r.
  intros x n.
  rewrite rings.preserves_plus, rings.preserves_1.
  rewrite <-(Z.pow_1_r x) at 2. apply Z.pow_add_r.
   auto with zarith.
  now destruct n.
Qed.

(* Efficient shiftl *)
Program Instance Z_shiftl: ShiftL Z (Z⁺) := Z.shiftl.

Instance: ShiftLSpec Z (Z⁺) Z_shiftl.
Proof.
  apply shiftl_spec_from_nat_pow.
  intros x [n En].
  apply Z.shiftl_mul_pow2.
  now apply En.
Qed.

Instance Z_Nshiftl: ShiftL Z N := λ x n, Z.shiftl x ('n).

Instance: ShiftLSpec Z N Z_Nshiftl.
Proof.
  apply shiftl_spec_from_nat_pow.
  intros x n.
  apply Z.shiftl_mul_pow2.
  now destruct n.
Qed.

Program Instance Z_abs: Abs Z := Zabs.
Next Obligation.
  split; intros E.
   now apply Z.abs_eq.
  now apply Z.abs_neq.
Qed.

Instance Z_div: DivEuclid Z := Zdiv.
Instance Z_mod: ModEuclid Z := Zmod.

Instance: EuclidSpec Z _ _.
Proof.
  split; try apply _.
     exact Z_div_mod_eq_full.
    intros x y Ey. destruct (Z_mod_remainder x y); intuition.
   now intros [].
  now intros [].
Qed.
*)