Require
  theory.fields stdlib_rationals theory.int_pow.
Require Import
  QArith QSig
  abstract_algebra interfaces.orders
  interfaces.integers interfaces.rationals interfaces.additional_operations
  theory.strong_setoids theory.rings theory.rationals.

Module QType_Rationals (Import anyQ: QType).

Module Import props := QProperties anyQ.

Instance QType_equiv: Equiv t := eq.
Instance QType_plus: Plus t := add.
Instance QType_0: Zero t := zero.
Instance QType_1: One t := one.
Instance QType_mult: Mult t := mul.
Instance QType_negate: Negate t := opp.
Instance QType_inv: Inv t := inv.

Hint Extern 10 (@Subset t) => eexact (every t) : typeclass_instances.

Local Notation T := (every t).
Local Notation Q := (every Q).
Local Open Scope mc_fun_scope.

Instance: Setoid T | 10 := {}.

Instance: ∀ x y: t, Decision (x = y) := λ x y,
  (match anyQ.eq_bool x y as p return p ≡ Qeq_bool (to_Q x) (to_Q y) → Decision (x = y) with
  | true => λ e, left _
  | false => λ e, right _
  end) (anyQ.spec_eq_bool x y).
    (* hm, do we really need the anyQ.spec_eq_bool in here? *)

Proof with intuition. apply Qeq_bool_iff... apply Qeq_bool_neq... Qed.

  (* We could get the above for free from the fact that anyQ.eq is just projected Qeq,
   but that mean that any comparison would involve two conversion to Q, which is
   a premature pessimization. *)

Instance: StandardUnEq T := _.

Instance: CommutativeRing T.
Proof.
  repeat match goal with
  | |- Morphism _ (&) => apply binary_morphism_proper_back; intros ?? [_ E1] ?? [_ E2];
       red_sig; unfold equiv, QType_equiv in *; now rewrite E1,E2
  | |- Morphism _ _ => intros ?? [_ E1];
       red_sig; unfold equiv, QType_equiv in *; now rewrite E1
  | |- _ => split; try apply _
  end; repeat intro.
+ now apply add_assoc.
+ now apply add_comm.
+ now apply add_0_l.
+ rewrite (add_comm (-y) y). now apply add_opp_diag_r.
+ now apply mul_assoc.
+ now apply mul_comm.
+ now apply mul_1_l.
+ rewrite (mul_comm _ _), (mul_comm _ y), (mul_comm _ z). now apply mul_add_distr_r.
Qed.

Local Instance: ∀ `{x ∊ T ₀}, canonical_names.inv x ∊ T ₀.
Proof. intros x [_ E]. split. apply _. intro E2.
  pose proof mul_inv_diag_l x E as E3. rewrite E2 in E3.
  change (0*x = 1) in E3. rewrite (mult_0_l _) in E3.
  destruct neq_1_0. now symmetry.
Qed.

Instance: Field T.
Proof. apply fields.dec_field.
+ intros x y E. unfold_sigs. red_sig. now rewrite E.
+ split. apply _. exact neq_1_0.
+ intros x [_ E]. exact (mul_inv_diag_l x E).
Qed.

(* Type-classified facts about to_Q/of_Q: *)
Instance inject_QType_Q: Cast T Q := to_Q.

Instance: Morphism (T ⇒ Q) (').
Proof. intros x y [_ E]. red_sig. auto. Qed.

Instance: Ring_Morphism T Q to_Q.
Proof. apply ring_morphism_alt; try apply _; intros; qify; reflexivity. Qed.

Instance inject_Q_QType: Cast Q T := of_Q.
Instance: Inverse (cast T Q) := cast Q T.

Instance: Surjective T Q (').
Proof. split; try apply _. intros x y [_ E]. red_sig. rewrite <- E. apply spec_of_Q.
  intros ??. apply _.
Qed.

Instance: Injective T Q (').
Proof. split; try apply _. auto. Qed.

Instance: StrongInjective T Q (') := dec_strong_injective _.

Instance: Bijective T Q (') := {}.

Instance: Inverse (cast Q T) := (cast T Q).

Instance: Bijective Q T (') := jections.flip_bijection _.

Instance: Ring_Morphism Q T of_Q := _ : Ring_Morphism Q T (')⁻¹.

Instance: RationalsToField T := iso_to_field (cast Q T).
Instance: Rationals T := iso_is_rationals (cast Q T).

(* Order *)
Instance QType_le: Le t := le.
Instance QType_lt: Lt t := lt.

(*
Instance: Proper ((=) ==> (=) ==> iff) QType_le.
Proof.
  intros ? ? E1 ? ? E2. unfold QType_le, le, equiv, QType_equiv, eq in *.
  now rewrite E1, E2.
Qed.
*)

Instance: SemiRingOrder T.
Proof. apply (rings.projected_ring_order (cast T Q)). now intros. Qed.

Instance: OrderEmbedding T Q (').
Proof. now repeat (split; try apply _). Qed.

Instance: TotalRelation T (≤).
Proof. now apply (maps.projected_total_order (cast T Q)). Qed.

Instance: FullPseudoSemiRingOrder T.
Proof. apply semirings.dec_full_pseudo_srorder.
  intros x _ y _.
  change (to_Q x < to_Q y ↔ x ≤ y ∧ x ≠ y).
  now rewrite (orders.lt_iff_le_apart (P:=Q) _ _).
Qed.

(* Efficient comparison *)
Program Instance: ∀ x y: t, Decision (x ≤ y) := λ x y,
  match compare x y with
  | Gt => right _
  | _ => left _
  end.
Next Obligation.
  rewrite spec_compare in *.
  destruct (Qcompare_spec (to_Q x) (to_Q y)); try discriminate.
  now apply orders.lt_not_le_flip.
Qed.

Next Obligation.
  rewrite spec_compare in *.
  destruct (Qcompare_spec (to_Q x) (to_Q y)); try discriminate; try intuition.
   now apply Zeq_le.
  now apply orders.lt_le.
Qed.

(* Efficient [int_pow] *)
Instance QType_Zpow: Pow t Z := power.

Instance: IntPowSpec T (every Z) QType_Zpow.
Proof. split; [split |..]; unfold equiv, QType_equiv, eq.
+ apply binary_morphism_proper_back. intros x1 x2 [_ Ex] y1 y2 Ey. unfold_sigs. red_sig.
  unfold equiv, QType_equiv, eq in Ex |- *. change (y1 ≡ y2) in Ey.
  rewrite 2!spec_power. now rewrite Ex, Ey.
+ intros x _. rewrite spec_power. transitivity (1:QArith_base.Q).
  exact (nat_pow_0 (R:=Q) (N:=(every Z)⁺) (to_Q x)).
  symmetry. pose proof (preserves_1 (f:=to_Q:T⇀Q)). trivial.
+ intros x _ n ?. rewrite spec_power.
  transitivity (to_Q x * to_Q (x^n)).
  rewrite spec_power. exact (nat_pow_S (R:=Q) (N:=(every Z)⁺) (to_Q x) n).
  pose proof (preserves_mult (f:=to_Q:T⇀Q) x (x^n)). now symmetry.
+ intros ?? ??. apply _.
+ intros x ? n ?.
  transitivity (1:QArith_base.Q); [|pose proof (preserves_1 (f:=to_Q:T⇀Q)); now symmetry].
  transitivity (to_Q (x^n) * to_Q (x^(-n))).
    pose proof (preserves_mult (f:=to_Q:T⇀Q) (x^n) (x^(-n))); now symmetry.
  rewrite 2!spec_power.
  exact (int_pow_neg (F:=Q) (Z:=every Z) (' x) n).
Qed.

Instance QType_Npow: Pow t N := λ x n, power x (Z_of_N n).

Instance: NatPowSpec T (every N) QType_Npow.
Proof. split; unfold "^", QType_Npow.
+ apply binary_morphism_proper_back. intros x1 x2 Ex n1 n2 En. unfold_sigs. red_sig.
  now rewrite Ex, En.
+ intros x _. rewrite preserves_0. exact (nat_pow_0 (N:=(every Z)⁺) _).
+ intros x ? n ?. pose proof nat_int.to_semiring_nonneg n : Z.of_N n ∊ (every Z)⁺.
  rewrite (preserves_plus _ _), (preserves_1  : Z_of_N 1%mc ≡ 1).
  exact (nat_pow_S (R:=T) (N:=(every Z)⁺) x _).
Qed.

End QType_Rationals.
