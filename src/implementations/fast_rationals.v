Require
  theory.shiftl theory.int_pow.
Require Import
  QArith BigQ
  abstract_algebra
  interfaces.integers interfaces.rationals interfaces.additional_operations
  theory.setoids
  fast_naturals fast_integers implementations.field_of_fractions stdlib_rationals.
Require Export
  QType_rationals.

Module Import BigQ_Rationals := QType_Rationals BigQ.

Hint Extern 10 (@Subset bigQ) => eexact (every bigQ) : typeclass_instances.

Local Notation Z := (every Z).
Local Notation bigN := (every bigN).
Local Notation bigZ := (every bigZ).
Local Notation bigQ := (every bigQ).

(* Embedding of [bigZ] into [bigQ] *)
Instance inject_bigZ_bigQ: Cast bigZ bigQ := BigQ.Qz.
Instance inject_bigN_bigQ: Cast bigN bigQ := cast bigZ bigQ ∘ cast bigN bigZ.
Instance inject_Z_bigQ: Cast Z bigQ := cast bigZ bigQ ∘ cast Z bigZ.

Instance: Morphism (bigZ ⇒ bigQ) (').
Proof. intros x y [_ E]. red_sig.
  repeat red in E. repeat red; simpl. now rewrite E.
Qed.

Instance: Ring_Morphism bigZ bigQ (').
Proof. apply rings.ring_morphism_alt; try apply _; repeat (split; try apply _). Qed.

Instance: Injective bigZ bigQ (').
Proof. rewrite (integers_initial (cast bigZ bigQ)). apply _. Qed.

Instance: SemiRing_Morphism bigN bigQ (') :=
  _ : SemiRing_Morphism bigN bigQ (cast bigZ bigQ ∘ cast bigN bigZ).

Instance: Ring_Morphism Z bigQ (') :=
  _ : Ring_Morphism Z bigQ (cast bigZ bigQ ∘ cast Z bigZ).

Instance: StrongInjective bigN bigQ (') :=
  strong_setoids.dec_strong_injective (cast bigZ bigQ ∘ cast bigN bigZ).
Instance: StrongInjective bigZ bigQ (') := strong_setoids.dec_strong_injective _.

Instance: Proper ((=) ==> (=) ==> (=)) BigQ.Qq.
Proof.
  intros x1 y1 E1 x2 y2 E2.
  do 4 red. simpl.
  case_eq (BigN.eqb x2 BigN.zero); intros Ex2; case_eq (BigN.eqb y2 BigN.zero); intros Ey2.
     reflexivity.
    rewrite E2 in Ex2. edestruct eq_true_false_abs; eassumption.
   rewrite E2 in Ex2. edestruct eq_true_false_abs; eassumption.
  simpl. do 3 red in E1. do 3 red in E2. now rewrite E1, E2.
Qed.

(* Why is the below not in the stdlib? *)
Lemma bigQ_div_bigQq n d : BigQ.Qq n d = cast bigZ bigQ n / 'd.
Proof.
  change (n # d == 'n / (BigQ.Qz (BigZ.Pos d)))%bigQ.
  unfold BigQ.div, BigQ.inv.
  case_eq (BigZ.zero ?= BigZ.Pos d)%bigZ; intros Ed.
    transitivity BigQ.zero; [| ring].
    do 2 red. simpl.
    case_eq (BigN.eqb d BigN.zero); intros Ed2; [reflexivity |].
    rewrite BigZ.spec_compare in Ed.
    destruct (proj2 (not_true_iff_false _) Ed2).
    apply BigN.eqb_eq. symmetry. now apply Zcompare_Eq_eq.
   unfold BigQ.mul. simpl. rewrite (mult_1_r n : (n * BigZ.one = n)%bigZ). reflexivity.
  destruct (BigZ.compare_spec BigZ.zero (BigZ.Pos d)); try discriminate.
  destruct (orders.lt_not_le_flip (P:=bigZ) 0 (BigZ.Pos d)); trivial.
  now destruct (nat_int.to_semiring_nonneg (f:=cast bigN bigZ) d).
Qed.

Lemma bigQ_div_bigQq_alt n d : BigQ.Qq n d = cast bigZ bigQ n / 'cast bigN bigZ d.
Proof bigQ_div_bigQq n d.

Lemma bigQ_div_bigQq_zero_den n : BigQ.Qq n 0 = 0.
Proof. change (n # 0 == 0)%bigQ. now repeat red. Qed.

Lemma bigQ_div_bigQq_zero_den_alt n d : d = 0 → BigQ.Qq n d = 0.
Proof. intro E. change (n # d == 0)%bigQ. rewrite E. now repeat red. Qed.


(* Embedding of [bigQ] into [Frac bigZ] *)
Instance inject_bigQ_frac_bigZ: Cast bigQ (Frac bigZ) := λ x,
  match x with
  | BigQ.Qz n => 'n
  | BigQ.Qq n d =>
     match decide_rel (=) (cast bigN bigZ d) 0 with
     | left _ => 0
     | right E => frac n ('d)
     end
  end.

Local Instance: ∀ x, cast bigQ (Frac bigZ) x ∊ Frac bigZ.
Proof. intro x. unfold cast, inject_bigQ_frac_bigZ. destruct x as [?|n d]. apply _.
  destruct (decide_rel (=) (cast bigN bigZ d) 0) as [E|E]. apply _.
  split. apply _. split. apply _. trivial.
Qed.

Require Import misc.quote.

Lemma inject_bigQ_frac_bigZ_correct:
 cast bigQ (Frac bigZ) = rationals_to_field bigQ (Frac bigZ).
Proof.
  intros x y [_ E]. red_sig. rewrite <- (bigQ $ E). clear dependent y.
  unfold cast, inject_bigQ_frac_bigZ. destruct x as [n|n d].
  + change (cast bigZ (Frac bigZ) n = (rationals_to_field bigQ (Frac bigZ) ∘ cast bigZ bigQ) n).
    apply (integers.to_ring_unique_alt (Z:=bigZ) (R:=Frac bigZ)); apply _.
  + destruct (decide_rel (=) (cast bigN bigZ d) 0) as [E|E].
    * change (cast bigN bigZ d = cast bigN bigZ 0) in E.
      apply (injective (cast bigN bigZ) _ _) in E.
      rewrite (bigQ $ bigQ_div_bigQq_zero_den_alt n d E).
      subsymmetry. exact rings.preserves_0.
    * assert ('d ∊ bigZ ₀). split. apply _. trivial.
      assert (frac n ('d) ∊ Frac bigZ) by (split; apply _).
      rewrite (bigQ $ bigQ_div_bigQq_alt n d).
      preserves_simplify (rationals_to_field bigQ (Frac bigZ)).
      rewrite <- (fields.mult_inv_cancel_r _ _ _).
      rewrite 2!((Frac bigZ) $ integers.to_ring_twice _ (') (cast bigZ (Frac bigZ)) _).
      red. red. simpl. rewrite ?(mult_1_r _). exact (commutativity (.*.) _ _).
Qed.

Instance: Ring_Morphism bigQ (Frac bigZ) (').
Proof. rewrite inject_bigQ_frac_bigZ_correct. apply _. Qed.

Instance: Injective bigQ (Frac bigZ) (').
Proof. rewrite inject_bigQ_frac_bigZ_correct. apply _. Qed.

(* Efficient shiftl on [bigQ] *)
Instance bigQ_shiftl: ShiftL bigQ bigZ := λ x k,
  match k with
  | BigZ.Pos k =>
    match x with
    | BigQ.Qz n => '(n ≪ k)
    | BigQ.Qq n d => BigQ.Qq (n ≪ k) d
    end
  | BigZ.Neg k =>
    match x with
    | BigQ.Qz n => BigQ.Qq n (1 ≪ k)
    | BigQ.Qq n d => BigQ.Qq n (d ≪ k)
    end
  end.

Local Hint Extern 5 (Pow BigQ.t BigZ.t) => eapply @int_pow.int_pow_default : typeclass_instances.
Local Hint Extern 5 (IntPowSpec bigQ bigZ _) => eapply @int_pow.int_pow_default_spec : typeclass_instances.
Local Hint Extern 5 (Pow BigQ.t BigN.t) => eapply @nat_pow.nat_pow_default : typeclass_instances.
Local Hint Extern 5 (NatPowSpec bigQ bigN _) => eapply @nat_pow.nat_pow_default_spec : typeclass_instances.
Local Hint Extern 5 (ShiftL BigQ.t BigN.t) => eapply @shiftl.shiftl_default : typeclass_instances.
Local Hint Extern 5 (ShiftLSpec bigQ bigN _) => eapply @shiftl.shiftl_default_spec : typeclass_instances.

(*Local Existing Instance int_pow.int_pow_default.
Local Existing Instance int_pow.int_pow_default_spec.*)

Instance: ShiftLSpec bigQ bigZ _.
Proof.
  apply shiftl.shiftl_spec_from_int_pow.
  intros ????; apply _.
  unfold shiftl, bigQ_shiftl.
  intros [n|n d] _ [k|k] _.
+ rewrite (shiftl.preserves_shiftl (f:=cast bigZ bigQ) n k).
  rewrite (shiftl.shiftl_nat_pow _ _).
  now setoid_rewrite (int_pow.int_pow_nat_pow (f:=cast bigN bigZ) 2 k).
+ change (BigZ.Neg k) with (- (cast bigN bigZ k)).
  rewrite (int_pow.int_pow_negate _ _).
  rewrite bigQ_div_bigQq, (shiftl.preserves_shiftl _ _).
  rewrite (shiftl.shiftl_nat_pow _ _).
  setoid_rewrite (int_pow.int_pow_nat_pow (f:=cast bigN bigZ) 2 k).
  rewrite (preserves_1 (f:=cast bigN bigQ)), (mult_1_r _).
  exact (commutativity (.*.) _ _).
+ rewrite 2!bigQ_div_bigQq.
  rewrite (shiftl.preserves_shiftl _ _), (shiftl.shiftl_nat_pow _ _).
  setoid_rewrite (int_pow.int_pow_nat_pow (f:=cast bigN bigZ) 2 k).
  now rewrite (associativity (.*.) _ _ _).
+ destruct (decide_rel (=) d 0) as [E|E].
  * rewrite 2!bigQ_div_bigQq_zero_den_alt.
    now rewrite (mult_0_r _). trivial. now rewrite E, (shiftl.shiftl_base_0 _).
  * assert (d ∊ bigN ₀) by (split; try apply _; trivial).
  change (BigZ.Neg k) with (- (cast bigN bigZ k)).
  rewrite (int_pow.int_pow_negate _ _).
  rewrite 2!bigQ_div_bigQq.
  rewrite (shiftl.preserves_shiftl _ _), (shiftl.shiftl_nat_pow _ _).
  setoid_rewrite (int_pow.int_pow_nat_pow (f:=cast bigN bigZ) 2 k).
  rewrite (fields.mult_inv_distr _ _).
  now rewrite ?(associativity (.*.) _ _ _), (commutativity (.*.) ('n) _).
Qed.

Instance bigQ_Zshiftl: ShiftL bigQ Z := λ x k, x ≪ 'k.

Instance: ShiftLSpec bigQ Z _.
Proof.
  split; unfold shiftl, bigQ_Zshiftl.
+ apply binary_morphism_proper_back. intros x y E n m E2. red_sig. now rewrite E, E2.
+ intros x _. exact (shiftl_0 (R:=bigQ) (N:=bigZ) x).
+ intros x _ n _. rewrite (bigZ $ rings.preserves_plus _ _).
  exact (shiftl_S (R:=bigQ) (N:=bigZ) x _).
Qed.
