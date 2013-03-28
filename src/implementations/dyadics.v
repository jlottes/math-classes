(**
  The dyadic rationals are numbers of the shape [m * 2 ^ e] with [m : Z] and [e : Z]
   for some [Integers] implementation [Z]. These numbers form a ring and can be
   embedded into any [Rationals] implementation [Q].
*)
Require Import
  stdlib_rationals
  abstract_algebra theory.strong_setoids
  interfaces.integers interfaces.naturals interfaces.rationals
  interfaces.additional_operations interfaces.orders
  orders.rings orders.integers orders.rationals
  nonneg_integers_naturals
  theory.fields
  theory.rationals theory.shiftl theory.int_pow theory.nat_pow orders.abs
  misc.quote stdlib_ring.

Inductive DyadicT A := dyadic { mant : A ; expo : A }.
Arguments dyadic {A} _ _.
Arguments mant {A} _.
Arguments expo {A} _.

Infix "▼" := dyadic (at level 69).

Section def.
  Context `(Z : @Subset A).

  Definition Dyadic : @Subset (DyadicT A) := λ d, let (m,e) := d in m ∊ Z ∧ e ∊ Z.

  Lemma dyadic_closed : Closed (Z ⇀ Z ⇀ Dyadic) dyadic. Proof. split; apply _. Qed.
  Lemma mant_closed : Closed (Dyadic ⇀ Z) mant. Proof. now intros [??][??]. Qed.
  Lemma expo_closed : Closed (Dyadic ⇀ Z) expo. Proof. now intros [??][??]. Qed.
End def.

Hint Extern 10 (@Subset (DyadicT _)) => eapply @Dyadic : typeclass_instances.
Hint Extern 5 (_ ▼ _ ∊ _) => eapply @dyadic_closed : typeclass_instances.
Hint Extern 5 (mant _ ∊ _) => eapply @mant_closed : typeclass_instances.
Hint Extern 5 (expo _ ∊ _) => eapply @expo_closed : typeclass_instances.

Section ops.
  Context `{Integers A (Z:=Z)}.

  Notation Dyadic := (Dyadic Z).

  Global Instance dy_inject: Cast Z Dyadic := λ x, x ▼ 0.
  Instance dy_negate: Negate Dyadic := λ x, -mant x ▼ expo x.
  Instance dy_mult: Mult Dyadic := λ x y, mant x * mant y ▼ expo x + expo y.
  Instance dy_0: Zero Dyadic := cast Z Dyadic 0.
  Instance dy_1: One Dyadic := cast Z Dyadic 1.

  Instance dy_abs `{!Abs Z} : Abs Dyadic := λ x, abs (mant x) ▼ expo x.
  Instance dy_pow `{!Pow A A} : Pow Dyadic A := λ x n, (mant x)^n ▼ n * expo x.
  Instance dy_shiftl: ShiftL Dyadic A := λ x n, mant x ▼ n + expo x.

  Section DtoQ_slow.
    Context `{Rationals B (Q:=Q)} `{Pow B A} (ZtoQ: Z ⇀ Q).
    Definition DtoQ_slow : Dyadic ⇀ Q := λ x, 2 ^ (expo x) * ZtoQ (mant x).
  End DtoQ_slow.

  Context `{Le A} `{!StrongSubDecision Z Z (≤)} {sl:ShiftL A A}.

  Instance dy_plus : Plus Dyadic := λ x y,
    if decide_sub_strong (≤) (expo x) (expo y)
    then mant x + mant y ≪ (expo y - expo x) ▼ expo x
    else mant x ≪ (expo x - expo y) + mant y ▼ expo y.

  Instance dy_equiv: Equiv Dyadic := λ x y, mant (x - y) = 0.
  Instance dy_le   : Le    Dyadic := λ x y, mant (x - y) ≤ 0.
  Instance dy_lt   : Lt    Dyadic := dec_lt.

  Section DtoQ.
    Context `{Rationals B (Q:=Q)} (ZtoQ: Z ⇀ Q).
    Definition DtoQ : Dyadic ⇀ Q := λ x,
      if decide_sub_strong (≤) 0 (expo x)
      then ZtoQ (mant x ≪ expo x)
      else ZtoQ (mant x) / ZtoQ (1 ≪ (- expo x)).
  End DtoQ.
End ops.
Hint Extern 0 (Plus   (DyadicT _)  ) => eapply @dy_plus   : typeclass_instances.
Hint Extern 0 (Negate (DyadicT _)  ) => eapply @dy_negate : typeclass_instances.
Hint Extern 0 (Mult   (DyadicT _)  ) => eapply @dy_mult   : typeclass_instances.
Hint Extern 0 (Zero   (DyadicT _)  ) => eapply @dy_0      : typeclass_instances.
Hint Extern 0 (One    (DyadicT _)  ) => eapply @dy_1      : typeclass_instances.
Hint Extern 0 (Abs    (DyadicT _)  ) => eapply @dy_abs    : typeclass_instances.
Hint Extern 0 (Pow    (DyadicT _) _) => eapply @dy_pow    : typeclass_instances.
Hint Extern 0 (ShiftL (DyadicT _) _) => eapply @dy_shiftl : typeclass_instances.
Hint Extern 0 (Zero   (elt_type (Dyadic _))) => eapply @dy_0 : typeclass_instances.
Hint Extern 0 (One    (elt_type (Dyadic _))) => eapply @dy_1 : typeclass_instances.

Hint Extern 0 (Equiv (DyadicT _)) => eapply @dy_equiv : typeclass_instances.
Hint Extern 0 (UnEq  (DyadicT _)) => eapply @default_uneq : typeclass_instances.
Hint Extern 0 (Le    (DyadicT _)) => eapply @dy_le    : typeclass_instances.
Hint Extern 0 (Lt    (DyadicT _)) => eapply @dy_lt    : typeclass_instances.
Hint Extern 0 (Equiv (elt_type (Dyadic _))) => eapply @dy_equiv : typeclass_instances.
Hint Extern 0 (UnEq  (elt_type (Dyadic _))) => eapply @default_uneq : typeclass_instances.


Section contents.
  Context `{Integers A (Z:=Z)}.
  Context `{Le A} `{!StrongSubDecision Z Z (≤)} {sl:ShiftL A A}.

  Notation Dyadic := (Dyadic Z).

  Instance: Closed (Z ⇀ Dyadic) (').                 Proof. split; apply _. Qed.
  Instance: Closed (Dyadic ⇀ Dyadic) (-).            Proof. split; apply _. Qed.
  Instance: Closed (Dyadic ⇀ Dyadic ⇀ Dyadic) (.*.). Proof. split; apply _. Qed.
  Instance: 0 ∊ Dyadic.                              Proof. split; apply _. Qed.
  Instance: 1 ∊ Dyadic.                              Proof. split; apply _. Qed.

  Context `{UnEq _} `{!StandardUnEq Z} `{Lt _} `{!FullPseudoSemiRingOrder Z}.
  Context `{!StrongSubDecision Z Z (=)}.
  Context `{!ShiftLSpec Z Z⁺ sl}.

  Instance: Closed (Dyadic ⇀ Dyadic ⇀ Dyadic) (+).
  Proof. intros [xn xe] [??] [yn ye] [??]. unfold plus, dy_plus. simpl.
    destruct_dec_sub_strong E;
      [| apply (le_flip _ _) in E ];
      rewrite <-(flip_nonneg_minus _ _) in E;
      split; apply _.
  Qed.

  Add Ring Z : (stdlib_ring_theory Z).

  Section with_rationals.

    Instance: Pow A A := _.
    Instance: NatPowSpec Z Z⁺ _ := _.

    Context `{Rationals (Q:=Q)} `{!IntPowSpec Q Z ipw} `{!Ring_Morphism Z Q (ZtoQ: Z ⇀ Q)}
      `{Le _} `{Lt _} `{!FullPseudoSemiRingOrder Q}.
    Add Ring Q : (stdlib_ring_theory Q).

    Notation DtoQ_slow' := (DtoQ_slow ZtoQ).

    Instance : StrongInjective Z Q ZtoQ := int_to_rat_strong_inj _.

    Lemma ZtoQ_shift x `{x ∊ Z} n `{n ∊ Z⁺} : ZtoQ (x ≪ n) = 2 ^ n * ZtoQ x.
    Proof. rewrite (Z $ shiftl_nat_pow (N:=Z⁺) _ _).
      preserves_simplify ZtoQ.
      rewrite (Q $ preserves_nat_pow (N:=Z⁺) (f:=ZtoQ) _ _).
      now mc_replace (ZtoQ 2) with 2 on (Q ₀) by (now preserves_simplify ZtoQ).
    Qed.

    Instance DtoQ_slow_closed : Closed (Dyadic ⇀ Q) DtoQ_slow'.
    Proof. intros [xm xe] [??]. unfold DtoQ_slow. simpl. exact _. Qed.

    Lemma DtoQ_slow_preserves_plus x {elx:x ∊ Dyadic} y {ely:y ∊ Dyadic}
      : DtoQ_slow' (x + y) = DtoQ_slow' x + DtoQ_slow' y.
    Proof.
      destruct x as [xn xe], y as [yn ye], elx, ely.
      unfold plus at 1. unfold DtoQ_slow, dy_plus. simpl.
      destruct_dec_sub_strong E; simpl;
        [| apply (le_flip _ _) in E ];
        rewrite <-(flip_nonneg_minus _ _) in E;
        preserves_simplify ZtoQ; rewrite (Q $ ZtoQ_shift _ _);
        rewrite (Q $ plus_mult_distr_l _ _ _), (Q $ associativity (.*.) _ _ _);
        rewrite <- (Q $ int_pow_exp_plus 2 _ _).
      now mc_replace ((2:Q) ^ (xe + (ye - xe))) with ((2:Q) ^ ye) on Q by
        now rewrite (Z $ plus_negate_r_split_alt _ _).
      now mc_replace ((2:Q) ^ (ye + (xe - ye))) with ((2:Q) ^ xe) on Q by
        now rewrite (Z $ plus_negate_r_split_alt _ _).
    Qed.

    Lemma DtoQ_slow_preserves_negate x `{x ∊ Dyadic} : DtoQ_slow' (-x) = -DtoQ_slow' x.
    Proof. unfold DtoQ_slow. simpl. preserves_simplify ZtoQ. subring Q. Qed.

    Lemma DtoQ_slow_preserves_mult x {elx:x ∊ Dyadic} y {ely:y ∊ Dyadic}
      : DtoQ_slow' (x * y) = DtoQ_slow' x * DtoQ_slow' y.
    Proof.
      destruct x as [xn xe], y as [yn ye], elx, ely.
      unfold DtoQ_slow. simpl. preserves_simplify ZtoQ.
      rewrite (Q $ int_pow_exp_plus 2 _ _). subring Q.
    Qed.

    Lemma DtoQ_slow_preserves_0 : DtoQ_slow' 0 = 0.
    Proof. unfold DtoQ_slow. simpl. preserves_simplify ZtoQ. exact (mult_0_r _). Qed.

    Lemma DtoQ_slow_preserves_1 : DtoQ_slow' 1 = 1.
    Proof. unfold DtoQ_slow. simpl. preserves_simplify ZtoQ.
      rewrite (Q $ int_pow_0 _). exact (mult_1_r _).
    Qed.

    Lemma DtoQ_slow_0_iff_mant_0 x {elx:x ∊ Dyadic} : DtoQ_slow' x = 0 ↔ mant x = 0.
    Proof. destruct x as [xn xe], elx. unfold DtoQ_slow. simpl. split; intro E.
    + apply (injective ZtoQ _ _). preserves_simplify ZtoQ.
      apply (left_cancellation (.*.) (2^xe) Q _ _).
      now rewrite (Q $ mult_0_r _).
    + rewrite (Z $ E). preserves_simplify ZtoQ. exact (mult_0_r _).
    Qed.

    Lemma DtoQ_slow_nonpos_iff_mant_nonpos x {elx:x ∊ Dyadic} : DtoQ_slow' x ∊ Q⁻ ↔ mant x ∊ Z⁻.
    Proof. destruct x as [xn xe], elx. unfold DtoQ_slow. simpl. split.
    + intro E; (split; [apply _|]).
      apply (order_reflecting ZtoQ _ _). rewrite (Q $ preserves_0).
      apply (order_reflecting (2 ^ xe *.) _ _). rewrite (Q $ mult_0_r _).
      now destruct E.
    + intro E. apply _.
    Qed.

    Existing Instance closed_range.
    Existing Instance closed_binary.

    Lemma DtoQ_slow_preserves_equiv x {elx:x ∊ Dyadic} y {ely:y ∊ Dyadic}
      : x = y ↔ DtoQ_slow' x = DtoQ_slow' y.
    Proof.
      unfold equiv at 1. unfold dy_equiv.
      rewrite <-(DtoQ_slow_0_iff_mant_0 (x-y)).
      rewrite (Q $ DtoQ_slow_preserves_plus _ _).
      rewrite (Q $ DtoQ_slow_preserves_negate _).
      now rewrite (equal_by_zero_sum (DtoQ_slow' x) _).
    Qed.

    Instance DtoQ_slow_morphism : Morphism (Dyadic ⇒ Q) DtoQ_slow'.
    Proof. intros ?? E. unfold_sigs. red_sig. now apply DtoQ_slow_preserves_equiv. Qed.

    Instance DtoQ_slow_injective : Injective Dyadic Q DtoQ_slow'.
    Proof. split; try apply _. intros. now apply DtoQ_slow_preserves_equiv. Qed.

    Lemma DtoQ_slow_preserves_le x {elx:x ∊ Dyadic} y {ely:y ∊ Dyadic}
      : x ≤ y ↔ DtoQ_slow' x ≤ DtoQ_slow' y.
    Proof. unfold le at 1. unfold dy_le. transitivity (mant (x-y) ∊ Z⁻).
      pose proof _ : mant (x-y) ∊ Z. intuition. now split. firstorder.
      rewrite <- (DtoQ_slow_nonpos_iff_mant_nonpos _),
        (Q $ DtoQ_slow_preserves_plus _ _), (Q $ DtoQ_slow_preserves_negate _).
      exact (flip_nonpos_minus _ _).
    Qed.

  End with_rationals.

  Notation StdQ := (every QArith_base.Q).
  Notation ZtoStdQ := (integers.integers_to_ring Z StdQ).
  Notation DtoStdQ := (DtoQ_slow ZtoStdQ).

  Instance: Pow QArith_base.Q A := _.
  Instance: IntPowSpec StdQ Z _ := _.

  Existing Instance DtoQ_slow_closed.
  Existing Instance DtoQ_slow_morphism.
  Existing Instance DtoQ_slow_injective.

  Instance: Setoid Dyadic.
  Proof. apply (projected_setoid DtoStdQ). exact DtoQ_slow_preserves_equiv. Qed.

  Instance: CommutativeRing Dyadic.
  Proof. apply (projected_com_ring DtoStdQ).
  + exact DtoQ_slow_preserves_plus.
  + exact DtoQ_slow_preserves_mult.
  + exact DtoQ_slow_preserves_0.
  + exact DtoQ_slow_preserves_1.
  + exact DtoQ_slow_preserves_negate.
  Qed.

  Instance: Ring_Morphism Dyadic StdQ DtoStdQ.
  Proof. apply ring_morphism_alt; try apply _.
  + exact DtoQ_slow_preserves_plus.
  + exact DtoQ_slow_preserves_mult.
  + exact DtoQ_slow_preserves_1.
  Qed.

  Global Instance dyadic_morphism: Morphism (Z ⇒ Z ⇒ Dyadic) dyadic.
  Proof. apply binary_morphism_proper_back. intros xm ym E1 xe ye E2. unfold_sigs. red_sig.
    apply (injective DtoStdQ _ _). unfold DtoQ_slow. simpl.
    mc_replace ((2:StdQ) ^ xe) with ((2:StdQ) ^ ye) on StdQ by now rewrite (Z $ E2).
    now rewrite (Z $ E1).
  Qed.

  Instance dy_inject_morphism: Morphism (Z ⇒ Dyadic) (').
  Proof. intros x y E. unfold_sigs. unfold cast, dy_inject. red_sig.
    now rewrite (Z $ E).
  Qed.

  Global Instance dy_inject_ring_mor: Ring_Morphism Z Dyadic (').
  Proof. apply ring_morphism_alt. apply _. apply _. apply _.
  + intros x ? y ?. unfold plus at 2. unfold cast, dy_inject, dy_plus. simpl.
    destruct (decide_sub_strong le 0 0);
    mc_replace (0 - 0) with 0 on Z⁺ by subring Z.
    now rewrite_on Z ->(shiftl_0 (N:=Z⁺) y).
    now rewrite_on Z ->(shiftl_0 (N:=Z⁺) x).
  + intros x ? y ?. unfold mult at 2. unfold cast, dy_inject, dy_mult. simpl.
    now rewrite (Z $ plus_0_r _).
  + subreflexivity.
  Qed.

  Global Instance dy_inject_injective: Injective Z Dyadic (').
  Proof. split; try apply _. intros x ? y ? E.
    apply (injective ZtoStdQ _ _).
    rewrite <- 2!(integers.to_ring_unique (DtoStdQ ∘ (cast Z Dyadic)) _).
    unfold compose. now rewrite (Dyadic $ E).
  Qed.

  Lemma dy_le_dec_aux x {elx:x ∊ Dyadic} y {ely:y ∊ Dyadic} :
    expo x ≤ expo y → ((mant x ≤ mant y ≪ (expo y - expo x) ↔ x ≤ y)
                    ∧  (mant y ≪ (expo y - expo x) ≤ mant x ↔ y ≤ x)).
  Proof. intro Ee. apply (flip_nonneg_minus _ _) in Ee.
    rewrite 2!(DtoQ_slow_preserves_le (ZtoQ:=ZtoStdQ) _ _).
    rewrite 2!(order_embedding ZtoStdQ _ _).
    rewrite (StdQ $ ZtoQ_shift _ _).
    rewrite (order_embedding (2^expo x *.) _ _).
    rewrite (order_embedding (2^expo x *.) _ (ZtoStdQ (mant x))).
    rewrite (StdQ $ associativity (.*.) _ _ _).
    rewrite <-(StdQ $ int_pow_exp_plus 2 _ _).
    mc_replace ((2:StdQ) ^ (expo x + (expo y - expo x))) with ((2:StdQ) ^ expo y) on StdQ by
      now rewrite (Z $ plus_negate_r_split_alt _ _).
    now unfold DtoQ_slow.
  Qed.

  Lemma dy_le_dec_aux_1 x {elx:x ∊ Dyadic} y {ely:y ∊ Dyadic} :
    expo x ≤ expo y → mant x ≤ mant y ≪ (expo y - expo x) ↔ x ≤ y.
  Proof. pose proof dy_le_dec_aux x y. intuition. Qed.

  Lemma dy_le_dec_aux_2 x {elx:x ∊ Dyadic} y {ely:y ∊ Dyadic} :
    expo x ≤ expo y → mant y ≪ (expo y - expo x) ≤ mant x ↔ y ≤ x.
  Proof. pose proof dy_le_dec_aux x y. intuition. Qed.

  Lemma dy_eq_dec_aux x {elx:x ∊ Dyadic} y {ely:y ∊ Dyadic} :
    expo x ≤ expo y → mant x = mant y ≪ (expo y - expo x) ↔ x = y.
  Proof. intros Ee. assert (expo y - expo x ∊ Z⁺) by now apply (flip_nonneg_minus _ _).
    rewrite (DtoQ_slow_preserves_equiv (ZtoQ:=ZtoStdQ) _ _).
    split; intro E; (
      apply (subantisymmetry le _ _);
      try rewrite <-(DtoQ_slow_preserves_le (ZtoQ:=ZtoStdQ) _ _);
      [ apply (dy_le_dec_aux_1 _ _ Ee) | apply (dy_le_dec_aux_2 _ _ Ee) ];
      try now rewrite (Z $ E)
    ); rewrite (DtoQ_slow_preserves_le (ZtoQ:=ZtoStdQ) _ _), (StdQ $ E); subreflexivity.
  Qed.

  Ltac dy_dec_tac x y := 
    pose proof _ : expo x ∊ Z; pose proof _ : expo y ∊ Z;
    first [
      assert (expo y - expo x ∊ Z⁺) by (apply (flip_nonneg_minus _ _); auto);
      pose proof _ : mant x ∊ Z; pose proof _ : mant y ≪ (expo y - expo x) ∊ Z
    | assert (expo x - expo y ∊ Z⁺) by (apply (flip_nonneg_minus _ _); apply (le_flip _ _); auto);
      pose proof _ : mant y ∊ Z; pose proof _ : mant x ≪ (expo x - expo y) ∊ Z
    ].

  Global Program Instance dy_eq_dec: StrongSubDecision Dyadic Dyadic (=) := λ x y,
    if decide_sub_strong (≤) (expo x) (expo y)
    then if decide_sub_strong (=) (mant x) (mant y ≪ (expo y - expo x)) then left _ else right _
    else if decide_sub_strong (=) (mant x ≪ (expo x - expo y)) (mant y) then left _ else right _.
  Next Obligation. dy_dec_tac x y. apply dy_eq_dec_aux; auto. Qed.
  Next Obligation. dy_dec_tac x y. intro E. apply dy_eq_dec_aux in E; auto. contradict E. auto. Qed.
  Next Obligation. dy_dec_tac x y.
    subsymmetry. apply (dy_eq_dec_aux _ _). apply (le_flip _ _); auto. subsymmetry; auto.
  Qed.
  Next Obligation. dy_dec_tac x y. intro E. subsymmetry in E.
    apply (dy_eq_dec_aux _ _) in E. subsymmetry in E. contradict E. auto.
    apply (le_flip _ _); auto.
  Qed.

  Global Program Instance dy_le_dec: StrongSubDecision Dyadic Dyadic (≤) := λ x y,
    if decide_sub_strong (≤) (expo x) (expo y)
    then if decide_sub_strong (≤) (mant x) (mant y ≪ (expo y - expo x)) then left _ else right _
    else if decide_sub_strong (≤) (mant x ≪ (expo x - expo y)) (mant y) then left _ else right _.
  Next Obligation. dy_dec_tac x y. apply dy_le_dec_aux_1; auto. Qed.
  Next Obligation. dy_dec_tac x y. intro E. apply dy_le_dec_aux_1 in E; auto. contradict E. auto. Qed.
  Next Obligation. dy_dec_tac x y. apply dy_le_dec_aux_2; auto. apply (le_flip _ _); auto. Qed.
  Next Obligation. dy_dec_tac x y. intro E. apply dy_le_dec_aux_2 in E; auto. contradict E. auto. apply (le_flip _ _); auto. Qed.

  Instance: StrongSetoid Dyadic := dec_strong_setoid.
  Instance: StrongInjective Dyadic StdQ DtoStdQ := dec_strong_injective _.

  Instance: StrongRngOps Dyadic.
  Proof. split; [ apply _ | apply (dec_strong_binary_morphism _).. ]. Qed.

  Existing Instance strong_injective_nonzero.

  Instance: 1 ∊ Dyadic ₀.
  Proof. split. apply _. intro E.
    rewrite (DtoQ_slow_preserves_equiv (ZtoQ:=ZtoStdQ) 1 0),
            (StdQ $ DtoQ_slow_preserves_0), (StdQ $ DtoQ_slow_preserves_1) in E.
    revert E. now destruct (_ : 1 ∊ StdQ ₀).
  Qed.

  Instance dy_intdom: IntegralDomain Dyadic.
  Proof. split. apply _. apply _. apply _. intros x ? y ?.
    split. apply _. intro E.
    destruct (_ : DtoStdQ x * DtoStdQ y ∊ StdQ ₀) as [_ E2]; destruct E2.
    rewrite <- (StdQ $ preserves_mult _ _), (Dyadic $ E). exact preserves_0.
  Qed.

  Instance: SemiRingOrder Dyadic := projected_ring_order DtoStdQ DtoQ_slow_preserves_le.
  Instance: TotalRelation Dyadic (≤) := projected_total_relation DtoStdQ DtoQ_slow_preserves_le.

  Instance: OrderEmbedding Dyadic StdQ DtoStdQ.
  Proof. repeat (split; try apply _); intros;
    now apply (DtoQ_slow_preserves_le (ZtoQ:=ZtoStdQ) _ _).
  Qed.

  Global Instance: FullPseudoSemiRingOrder Dyadic.
  Proof. now apply dec_full_pseudo_srorder. Qed.

  Lemma nonneg_mant x `{x ∊ Dyadic} : x ∊ Dyadic⁺ ↔ mant x ∊ Z⁺.
  Proof. rewrite (embeds_nonneg DtoStdQ _). unfold DtoQ_slow.
    now rewrite <- ( embeds_nonneg (2^expo x *.) _), (embeds_nonneg ZtoStdQ _).
  Qed.

  Lemma nonpos_mant x `{x ∊ Dyadic} : x ∊ Dyadic⁻ ↔ mant x ∊ Z⁻.
  Proof. rewrite (embeds_nonpos DtoStdQ _). unfold DtoQ_slow.
    now rewrite <- ( embeds_nonpos (2^expo x *.) _), (embeds_nonpos ZtoStdQ _).
  Qed.

  Section abs.
    Context `{Abs Z} `{!DecAbs Z}.

    Instance dy_abs_closed: Closed (Dyadic ⇀ Dyadic) (abs).
    Proof. intros ??. unfold abs, dy_abs. apply _. Qed.

    Global Instance: DecAbs Dyadic.
    Proof. split; [ apply _ | intros; unfold abs, dy_abs ..].
    + assert (mant x ∊ Z⁺) by now apply (nonneg_mant x).
      rewrite (Z $ abs_nonneg (mant x)). now destruct x.
    + assert (mant x ∊ Z⁻) by now apply (nonpos_mant x).
      rewrite (Z $ abs_nonpos (mant x)). now destruct x.
    Qed.
  End abs.

  Section pow.
    Context `{!NatPowSpec Z Z⁺ pw}.

    Instance dy_pow_closed: Closed (Dyadic ⇀ Z⁺ ⇀ Dyadic) (^).
    Proof. intros ????. unfold pow, dy_pow. apply _. Qed.

    Hint Extern 2 (@pow _ _ dy_pow _ _ ∊ Dyadic) => eapply @dy_pow_closed : typeclass_instances.

    Lemma DtoStdQ_preserves_pow x `{x ∊ Dyadic} n `{n ∊ Z⁺}
      : DtoStdQ (x^n) = DtoStdQ x ^ n.
    Proof. unfold pow at 1, dy_pow. unfold DtoQ_slow. simpl.
      rewrite (StdQ $ preserves_nat_pow (N:=Z⁺) _ _).
      mc_replace ((2:StdQ) ^ (n * expo x)) with ((2:StdQ) ^ (expo x * n)) on StdQ by
        now rewrite (Z $ commutativity (.*.) n (expo x)).
      rewrite (StdQ $ int_pow_exp_mult 2 _ _).
      subsymmetry. exact (int_pow_mult_nonneg _ _ _).
    Qed.

    Global Instance: NatPowSpec Dyadic Z⁺ dy_pow.
    Proof. intros. split.
    + apply binary_morphism_proper_back. intros x y E1 n m E2. unfold_sigs. red_sig.
      apply (injective DtoStdQ _ _).
      rewrite 2!(StdQ $ DtoStdQ_preserves_pow _ _).
      apply (binary_morphism_proper (Y:=Z⁺) _). red_sig. now rewrite (Dyadic $ E1). now red_sig.
    + intros. apply (injective DtoStdQ _ _). rewrite (StdQ $ DtoStdQ_preserves_pow _ _).
      preserves_simplify (DtoStdQ). exact (int_pow_0 _).
    + intros. apply (injective DtoStdQ _ _).
      preserves_simplify (DtoStdQ). rewrite 2!(StdQ $ DtoStdQ_preserves_pow _ _).
      exact (nat_pow_S (N:=Z⁺) _ _).
    Qed.
  End pow.

  Section shiftl.
    Instance dy_shiftl_closed: Closed (Dyadic ⇀ Z ⇀ Dyadic) (≪).
    Proof. intros ????. unfold shiftl, dy_shiftl. apply _. Qed.

    Hint Extern 2 (@shiftl _ _ dy_shiftl _ _ ∊ Dyadic) => eapply @dy_shiftl_closed : typeclass_instances.

    Lemma DtoStdQ_preserves_shiftl x `{x ∊ Dyadic} n `{n ∊ Z}
      : DtoStdQ (x ≪ n) = DtoStdQ x ≪ n.
    Proof. unfold shiftl at 1, dy_shiftl, DtoQ_slow. simpl.
      now rewrite (StdQ $ int_pow_exp_plus 2 _ _), <-(StdQ $ associativity (.*.) _ _ _).
    Qed.

    Global Instance: ShiftLSpec Dyadic Z dy_shiftl.
    Proof. split.
    + apply binary_morphism_proper_back. intros x y E1 n m E2. unfold_sigs. red_sig.
      apply (injective DtoStdQ _ _).
      rewrite 2!(StdQ $ DtoStdQ_preserves_shiftl _ _).
      now rewrite (Dyadic $ E1), (Z $ E2).
    + intros x ?. apply (injective DtoStdQ _ _). rewrite (StdQ $ DtoStdQ_preserves_shiftl _ _).
      exact (shiftl_0 _).
    + intros. apply (injective DtoStdQ _ _).
      preserves_simplify (DtoStdQ). rewrite 2!(StdQ $ DtoStdQ_preserves_shiftl _ _).
      exact (shiftl_S _ _).
    Qed.
  End shiftl.

  Lemma dyadic_decompose x `{elx:x ∊ Dyadic} : x = '(mant x) ≪ expo x.
  Proof. destruct x as [xm xe], elx. unfold cast, dy_inject, shiftl, dy_shiftl. simpl.
    now rewrite (Z $ plus_0_r _).
  Qed.

  Section embed_rationals.
    Context `{Rationals B (Q:=Q)} `{!Ring_Morphism Z Q (ZtoQ: Z ⇀ Q)}.

    Notation DtoQ' := (DtoQ ZtoQ).
    Notation DtoQ_slow' := (DtoQ_slow ZtoQ).

    Instance: Pow B A := _.
    Instance: IntPowSpec Q Z _ := _.

    Instance: StrongInjective Z Q ZtoQ := int_to_rat_strong_inj _.

    Instance DtoQ_closed: Closed (Dyadic ⇀ Q) DtoQ'.
    Proof. intros [xm xe][??]. unfold DtoQ. simpl. destruct_dec_sub_strong E.
    + assert (xe ∊ Z⁺) by now split. apply _.
    + apply (le_flip _ _) in E. assert (xe ∊ Z⁻) by now split. apply _.
    Qed.

    Hint Extern 2 (DtoQ' _ ∊ _) => eapply @DtoQ_closed : typeclass_instances.

    Lemma DtoQ_correct : DtoQ' = DtoQ_slow'.
    Proof.
      intros x y E. rewrite <-E. destruct E as [[elx ?] E]. clear dependent y. red_sig.
      unfold DtoQ, DtoQ_slow.
      destruct x as [xm xe], elx. simpl.
      destruct_dec_sub_strong E.
      + assert (xe ∊ Z⁺) by now split. exact (ZtoQ_shift _ _).
      + apply (le_flip _ _) in E. assert (xe ∊ Z⁻) by now split.
        rewrite <- (mult_inv_cancel_l _ _ _).
        rewrite (Q $ commutativity (.*.) (2^xe) _ ), <-(Q $ associativity (.*.) _ _ _).
        assert (2 ^ xe * ZtoQ (1 ≪ (- xe)) = 1) as E'.
          now rewrite (Q $ ZtoQ_shift _ _), (Q $ associativity (.*.) _ _ _),
               <- (Q $ int_pow_exp_plus 2 _ _), (Z $ plus_negate_r _),
                  (Q $ int_pow_0 2), (Q $ preserves_1), (Q $ mult_1_l _).
        now rewrite (Q $ E'), (Q $ mult_1_r _).
    Qed.

    Global Instance: Ring_Morphism Dyadic Q DtoQ'.
    Proof. rewrite DtoQ_correct. apply ring_morphism_alt; try apply _.
    + exact DtoQ_slow_preserves_plus.
    + exact DtoQ_slow_preserves_mult.
    + exact DtoQ_slow_preserves_1.
    Qed.

    Global Instance: Injective Dyadic Q DtoQ'.
    Proof. rewrite DtoQ_correct. apply _. Qed.

    Context `{Le _} `{Lt _} `{!FullPseudoSemiRingOrder Q}.

    Global Instance: OrderEmbedding Dyadic Q DtoQ'.
    Proof. rewrite DtoQ_correct. repeat (split; try apply _); intros;
      now apply (DtoQ_slow_preserves_le _ _).
    Qed.

    Lemma DtoQ_unique (f:Dyadic ⇀ Q) `{!Ring_Morphism Dyadic Q f} : f = DtoQ'.
    Proof. intros x y [[elx ?]E]. red_sig.
      rewrite <- (Dyadic $ E). clear dependent y.
      rewrite (Dyadic $ dyadic_decompose x). destruct x as [xm xe], elx; simpl.
      rewrite 2!(Q $ preserves_shiftl (N:=Z) _ _).
      apply (binary_morphism_proper _); red_sig. 2:easy.
      exact (integers.to_ring_unique_alt (f ∘ (cast Z Dyadic)) (DtoQ' ∘ (cast Z Dyadic)) _).
    Qed.
  End embed_rationals.

End contents.

Hint Extern 2 (IntegralDomain (Dyadic _)) => eapply @dy_intdom : typeclass_instances.
Hint Extern 2 (StrongRngOps (Dyadic _)) => class_apply @intdom_strong : typeclass_instances.
Hint Extern 2 (CommutativeRing (Dyadic _)) => class_apply @intdom_comring : typeclass_instances.
Hint Extern 2 (AbGroup (Dyadic _)) => class_apply @comringplus_abgroup : typeclass_instances.
Hint Extern 2 (CommutativeMonoid (op:=plus_is_sg_op) (Dyadic _)) => class_apply @comsemiplus_monoid : typeclass_instances.
Hint Extern 2 (CommutativeMonoid (op:=mult_is_sg_op) (Dyadic _)) => class_apply @comringmult_commonoid : typeclass_instances.
Hint Extern 2 (SemiGroup (op:=mult_is_sg_op) (Dyadic _)) => class_apply @rngmult_semigroup : typeclass_instances.
Hint Extern 2 (Setoid (Dyadic _)) => eapply (sg_setoid (op:=mult_is_sg_op)) : typeclass_instances.

Require Import orders.integers.

(*
Section test.
  Context `{Integers (Z:=Z)}.

  Check _ : IntegralDomain (Dyadic Z).
  Check _ : CommutativeRing (Dyadic Z).
  Check _ : CommutativeSemiRing (Dyadic Z).
  Check _ : MultiplicativeSemiGroup (Dyadic Z).
  Check _ : AdditiveGroup (Dyadic Z).
  Check _ : AdditiveMonoid (Dyadic Z).
  Check _ : Setoid (Dyadic Z).
End test.
*)
