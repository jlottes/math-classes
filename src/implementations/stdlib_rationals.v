Require
  stdlib_binary_integers Field QArith.Qfield theory.rationals.
Require Import
  QArith_base Qabs Qpower
  abstract_algebra interfaces.rationals
  interfaces.orders interfaces.additional_operations
  theory.strong_setoids theory.strong_rings
  orders.integers theory.shiftl
  implementations.field_of_fractions intfrac_rationals.

(* canonical names for relations/operations/constants: *)
Instance Q_eq: Equiv Q := Qeq.
Instance Q_0 : Zero Q := 0%Q.
Instance Q_1 : One Q := 1%Q.
Instance Q_opp : Negate Q := Qopp.
Instance Q_plus : Plus Q := Qplus.
Instance Q_mult : Mult Q := Qmult.
Instance Q_inv : Inv Q := Qinv.

Instance Q_le: Le Q := Qle.
Instance Q_lt: Lt Q := Qlt.

Hint Extern 10 (@Subset Q) => eexact (every Q) : typeclass_instances.

Local Notation Q   := (every Q  ).
Local Notation Z   := (every Z  ).
Local Notation N   := (every N  ).
Local Notation nat := (every nat).


(* properties: *)
Instance: Setoid Q := {}.

Instance: CommutativeRing Q.
Proof.
  repeat match goal with
  | |- Morphism (_ ⇒ _ ⇒ _) _ => apply binary_morphism_proper_back; intros ?? [_ E1] ?? [_ E2];
       red_sig; unfold equiv, Q_eq in *; now rewrite E1,E2
  | |- Morphism _ _ => intros ?? [_ E1];
       red_sig; unfold equiv, Q_eq in *; now rewrite E1
  | |- _ => split; try apply _
  end; repeat intro.
+ now apply Qplus_assoc.
+ now apply Qplus_comm.
+ now apply Qplus_0_l.
+ rewrite (Qplus_comm (-y) y). now apply Qplus_opp_r.
+ now apply Qmult_assoc.
+ now apply Qmult_comm.
+ now apply Qmult_1_l.
+ now apply Qmult_plus_distr_r.
Qed.

Instance: Field Q.
Proof. split. apply _.
+ pose proof dec_strong_setoid (S:=Q). split. apply _.
  exact (dec_strong_binary_morphism _).
  exact (dec_strong_binary_morphism _).
+ split. apply _. exact Q_apart_0_1.
+ intros x y [[[_ Ex] [_ Ey]] E1].
  split. split; (split; [apply _ | intro E2]).
    destruct Ex. now rewrite <- (Qinv_involutive x), E2.
    destruct Ey. now rewrite <- (Qinv_involutive y), E2.
    now rewrite E1.
+ intros x [_ E]. rewrite <- (Qinv_involutive x) at 2. apply Qmult_inv_r.
  intro E2. destruct E. now rewrite <- (Qinv_involutive x), E2.
Qed.

(* misc: *)
Instance: ∀ x y: QArith_base.Q, Decision (x = y) := Qeq_dec.

Instance: StandardUnEq Q := _.

Instance inject_Z_Q: Cast Z Q := inject_Z.

Instance: Morphism (Z ⇒ Q) (').
Proof. intros x y [_ H]. red_sig.
  unfold cast, inject_Z. repeat red. simpl. do 2 red in H. now rewrite H.
Qed.

Instance: Ring_Morphism Z Q (').
Proof.
  repeat (split; try apply _).
  intros x ? y ?. repeat red. simpl. now rewrite ?Zmult_1_r.
  now exists_sub (1:Z).
Qed.

Instance: Injective Z Q (').
Proof. split; try apply _.
 intros x ? y ?. change (x * 1 = y * 1 → x = y). rewrite 2!(mult_1_r _). intuition.
Qed.

Instance Q_to_fracZ: Cast Q (Frac Z) := λ x, frac (Qnum x) (QDen x).

Instance: Morphism (Q ⇒ Frac Z) (').
Proof. intros ? ? [_ E].
  split. split; (split; [apply _ |]; split; [apply _ | easy]).
  destruct x as [a b], y as [c d].
  do 2 red. simpl. now rewrite (commutativity (.*.) _ c).
Qed.

Instance: Ring_Morphism Q (Frac Z) (').
Proof. apply ring_morphism_alt; try apply _.
+ intros [a b] _ [c d] _. unfold cast, Q_to_fracZ, equiv, frac_equiv. simpl.
  change ((a * Zpos d + c * Zpos b) * ((Zpos b) * (Zpos d)) = (Zpos (Pos.mul b d)) * (a * (Zpos d) + (Zpos b) * c)).
  rewrite (Z $ commutativity (.*.) c (Zpos b)). 
  now rewrite (Z $ commutativity (.*.) (Zpos (Pos.mul b d)) _).
+ intros [a b] _ [c d] _. unfold cast, Q_to_fracZ, equiv, frac_equiv. simpl.
  now rewrite (Z $ commutativity (.*.) (Zpos (Pos.mul b d)) _).
+ easy.
Qed.

Instance: Injective Q (Frac Z) (').
Proof. split; try apply _. intros [a b] ? [c d] ? E.
 unfold equiv, frac_equiv in E. simpl in E.
 now rewrite (commutativity (.*.) (Zpos b) c) in E.
Qed.

Instance: RationalsToField Q := rationals.inj_pre_to_field (cast Q (Frac Z)).
Instance: Rationals Q := rationals.inj_pre_is_rationals (cast Z Q) (cast Q (Frac Z)).

(* order: *)

Instance: PartialOrder Q.
Proof. split; try apply _.
+ intros ?? [_ E1] ?? [_ E2] ?. unfold equiv, Q_eq in E1,E2. now rewrite <- E1, <- E2.
+ apply every_SubReflexive. exact Qle_refl.
+ apply every_SubTransitive. exact Qle_trans.
+ apply every_SubAntiSymmetric. exact Qle_antisym.
Qed.

Instance: SemiRingOrder Q.
Proof. apply rings.from_ring_order.
+ intros ? _. split. split; apply _. intros ? _ ? _. apply Qplus_le_compat. apply Qle_refl.
+ intros ? [_ ?] ? [_ ?]. split. apply _. now apply Qmult_le_0_compat.
Qed.

Instance: TotalRelation Q (≤).
Proof.
  intros x _ y _.
  destruct (Qlt_le_dec x y); auto.
  left. now apply Qlt_le_weak.
Qed.

Instance: FullPseudoSemiRingOrder Q.
Proof. apply semirings.dec_full_pseudo_srorder.
  split.
   intro. split. now apply Zorder.Zlt_le_weak. now apply Zorder.Zlt_not_eq.
  intros [E1 E2]. destruct (Zorder.Zle_lt_or_eq _ _ E1). easy. now destruct E2.
Qed.

Program Instance: ∀ x y: QArith_base.Q, Decision (x ≤ y) := λ y x,
  match Qlt_le_dec x y with
  | left _ => right _
  | right _ => left _
  end.
Next Obligation. now apply Qlt_not_le. Qed.

(* additional operations *)
Instance Q_abs : Abs QArith_base.Q := Qabs.
Instance: DecAbs Q.
Proof. split; [intros x ?; apply _ |..];
  intros x [??]; unfold abs, Q_abs; [now apply Qabs_pos | now apply Qabs_neg].
Qed.

Instance Q_pow: Pow QArith_base.Q BinNums.Z := Qpower.

Instance: IntPowSpec Q Z Q_pow.
Proof. split. split.
+ apply binary_morphism_proper_back. intros x1 y1 [_ E1] x2 y2 [[??] E2]. red_sig. now rewrite E1,E2.
+ now intros x _.
+ intros x _ n ?.
  apply (Qpower_plus' x 1 n ).
  assert (1 ≤ 1 + n) as E. rewrite (naturals.nat_le_plus (N:=Z⁺)). now exists_sub n.
  apply (naturals.nat_ge_1_ne_0 (N:=Z⁺) _) in E. now destruct E.
+ intros ????. exact _.
+ intros x [_ ?] n _.
  rewrite <- (Qpower_plus x n (-n)); [| easy].
  change (Qpower x (n-n)%mc = 1).
  now rewrite (plus_negate_r n).
Qed.

Instance Q_Npow: Pow QArith_base.Q BinNums.N := λ x n, Qpower x (cast N Z n).

Instance: NatPowSpec Q N Q_Npow.
Proof. split.
+ apply binary_morphism_proper_back. intros x1 y1 [_ E1] x2 y2 [[??] E2]. red_sig. 
  unfold pow, Q_Npow. now rewrite E1,E2.
+ intros x _. change (x ^ (cast N Z 0) = 1).
  rewrite preserves_0.
  exact (nat_pow_0 (R:=Q) (N:=Z⁺) x).
+ intros x _ n _. change (x ^ (cast N Z (1+n)) = x * x ^ (cast N Z n)).
  rewrite (preserves_plus _ _), (preserves_1 : cast N Z 1 ≡ 1).
  pose proof (nat_int.to_semiring_nonneg n : cast N Z n ∊ Z⁺).
  exact (nat_pow_S (R:=Q) (N:=Z⁺) x _).
Qed.

Instance Q_shiftl: ShiftL QArith_base.Q BinNums.Z := λ x k,
  match k with
  | Z0 => x
  | Zpos p => Qmake (Z.shiftl (Qnum x) (Zpos p)) (Qden x)
  | Zneg p => Qmake (Qnum x) (shift_pos p (Qden x))
  end.

Instance: ShiftLSpec Q Z Q_shiftl.
Proof. apply shiftl_spec_from_int_pow.
  intros ?? ??. apply _.
  unfold shiftl, Q_shiftl.
  intros [n d] _ [|p|p] _.
+ change ((n#d) = 1 * (n#d)).
  symmetry. exact (mult_1_l (R:=Q) _).
+ unfold Qnum, Qden.
  rewrite !Qmake_Qdiv. unfold Qdiv.
  rewrite Z.shiftl_mul_pow2 by auto with zarith.
  rewrite Zmult_comm, inject_Z_mult, Zpower_Qpower by now destruct p.
  now rewrite Qmult_assoc.
+ unfold Qnum, Qden.
  rewrite !Qmake_Qdiv. unfold Qdiv.
  rewrite shift_pos_correct.
  change (Zpower_pos 2 p) with (2 ^ (Zpos p))%Z.
  rewrite Zmult_comm, inject_Z_mult, Zpower_Qpower by now destruct p.
  rewrite Qinv_mult_distr, Qmult_assoc.
  now rewrite Qmult_comm.
Qed.
