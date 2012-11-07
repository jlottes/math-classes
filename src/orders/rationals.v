Require Import
  abstract_algebra interfaces.orders
  interfaces.naturals interfaces.rationals interfaces.integers
  theory.strong_setoids natpair_integers theory.rationals theory.fields
  orders.semirings orders.integers orders.fields
  nonneg_integers_naturals.
Require Import stdlib_field misc.quote.

Local Open Scope grp_scope. (* notation for inverse *)

Local Notation nat := (every nat).

Section rationals_and_integers.
  Context `{Rationals (Q:=Q)} `{Le _} `{!SemiRingOrder Q}.
  Context `{Integers (Z:=Z)} `{UnEq _} `{!StandardUnEq _} `{Le _} `{Lt _} `{!FullPseudoSemiRingOrder Z}.
  Context  (f : Z ⇀ Q) `{!Ring_Morphism Z Q f}.

  Add Field Q : (stdlib_field_theory Q).

  Instance: StrongInjective Z Q f.
  Proof. rewrite (integers_initial f). apply _. Qed.

  Lemma rationals_decompose_pos_den_dec_slow x : { (n,d) : _ * _ | x ∊ Q → (n ∊ Z ∧ d ∊ Z₊) ∧ x = f n / f d }.
  Proof.
    destruct (rationals_decompose_dec f x) as [[n d] P].
    destruct (decide_sub_strong (<) 0 d) as [P1|P1]; [ exists (n,d) | exists (-n,-d) ];
      intro; destruct (P _) as [[??] E]; pose proof P1 _ _ as E1;
      (split; [split; [apply _|] |]); trivial.
    + split; apply _.
    + apply (not_lt_le_flip _ _) in E1.
      apply neg_negate, nonpos_nonzero_neg; trivial. split; apply _.
    + rewrite (Q $ E). preserves_simplify f. subfield Q.
  Qed.

  Lemma rationals_decompose_pos_den x `{x ∊ Q} :
    ∃ `{n ∊ Z} `{d ∊ Z₊}, x = f n / f d.
  Proof.
    destruct (rationals_decompose_pos_den_dec_slow x) as [[n d] P].
    destruct (P _) as [[??] E]. exists_sub n. now exists_sub d.
  Qed.
End rationals_and_integers.

(*
Section more_rationals_and_integers.
  Context `{Rationals (Q:=Q)} `{Le _} `{Lt _} `{!FullPseudoSemiRingOrder Q}.
  Context `{Integers (Z:=Z)} `{UnEq _} `{!StandardUnEq _} `{Le _} `{Lt _} `{!FullPseudoSemiRingOrder Z}.
  Context  (f : Z ⇀ Q) `{!Ring_Morphism Z Q f}.

  Instance: StrongInjective Z Q f.
  Proof. rewrite (integers_initial f). apply _. Qed.

  Instance: SemiRing_Morphism Z⁺ Q⁺ f := Zpos_semiring_mor_nonneg _.

  Instance int_to_rat_order_preserving : OrderPreserving Z Q f := _.
  Instance int_to_rat_strictly_order_preserving : StrictlyOrderPreserving Z Q f := _.
  Instance int_to_rat_order_reflecting : OrderReflecting Z Q f := _.

  Instance: Closed (Z⁺ ⇀ Q⁺) f.
  Proof. pose proof 
End more_rationals_and_integers.
*)


(* A PseudoRingOrder uniquely specifies the orders on the rationals *)
Section rationals_and_another_field.
  Context `{Rationals A (Q:=Q)} {Ale: Le A} {Alt: Lt A} `{!FullPseudoSemiRingOrder Q}.
  Context `{Field     B (F:=F)} {Ble: Le B} {Blt: Lt B} `{!FullPseudoSemiRingOrder F}.
  Context (f : Q ⇀ F) `{!Ring_Morphism Q F f}.

  Add Field Q1 : (stdlib_field_theory Q).

  Notation Z := (SRpair nat).
  Notation i_to_r := (integers.integers_to_ring Z Q).

  Instance : Strong_Morphism Q F f := dec_strong_morphism _.

  Instance f_preserves_nonneg : Closed (Q⁺ ⇀ F⁺) f.
  Proof. intros x el.
    destruct (rationals_decompose_pos_den i_to_r x) as [n [? [d [? E2]]]].
    rewrite (Q $ E2) in el  |- *. clear dependent x. preserves_simplify f.
    pose proof _ : i_to_r n / i_to_r d * i_to_r d ∊ Q⁺ as el2.
    mc_replace (i_to_r n / i_to_r d * i_to_r d) with (i_to_r n) on Q in el2 by subfield Q.
    pose proof reflects_nonneg (i_to_r) _ : n ∊ Z⁺.
    change ( (f ∘ i_to_r) n / (f ∘ i_to_r) d ∊ F⁺ ).
    apply nonneg_mult_compat; [| apply pos_nonneg, pos_mult_inv_compat ];
    rewrite (F $ integers.to_ring_unique _ _); apply _.
  Qed.

  Instance morphism_order_preserving: OrderPreserving Q F f.
  Proof semirings.preserving_preserves_nonneg _.
End rationals_and_another_field.

Section rationals_order_isomorphic.
  Context `{Rationals A (Q:=Q1)} {Ale: Le A} {Alt: Lt A} `{!FullPseudoSemiRingOrder Q1}.
  Context `{Rationals B (Q:=Q2)} {Ble: Le B} {Blt: Lt B} `{!FullPseudoSemiRingOrder Q2}.
  Context (f : Q1 ⇀ Q2) `{!Ring_Morphism Q1 Q2 f}.

  Existing Instance morphism_order_preserving.

  Global Instance: OrderEmbedding Q1 Q2 f.
  Proof. split. apply _.
    split. apply _.
    intros x ? y ? E.
    rewrite <- (Q1 $ to_rationals_involutive x (Q2:=Q2)).
    rewrite <- (Q1 $ to_rationals_involutive y (Q2:=Q2)).
    rewrite <- 2!(Q2 $ to_rationals_unique f _).
    now apply (order_preserving _ _ _).
  Qed.
End rationals_order_isomorphic.

Section strong_subdec_le.

  Context `{Rationals (Q:=Q)} `{Le _} `{Lt _} `{!FullPseudoSemiRingOrder Q}.

  Notation Zc := (SRpair (every nat)).
  Notation f := (integers_to_ring Zc Q).

  Global Instance rationals_strong_subdec_le_slow : StrongSubDecision Q Q (≤) | 20.
  Proof. intros x y.
    destruct (rationals_decompose_pos_den_dec_slow f x) as [[xn xd] Px].
    destruct (rationals_decompose_pos_den_dec_slow f y) as [[yn yd] Py].
    destruct (decide_rel (≤) (xn*yd) (xd*yn)) as [E|E]; [left|right]; intros;
      destruct (Px _) as [[??] Ex]; destruct (Py _) as [[??] Ey];
      rewrite_on Q ->Ex, Ey; rewrite <- (mult_inv_le_cancel_both _ _ _ _);
      rewrite <- 2!(Q $ preserves_mult _ _).
  + now apply (order_preserving (S:=Zc) f _ _).
  + contradict E. now apply (order_reflecting (S:=Zc) f _ _).
  Qed.

End strong_subdec_le.

Instance rationals_le `{Rationals A (Q:=Q)} : Le A | 10 := λ x y,
  ∃ n `{d ∊ nat ₀}, y = x + naturals_to_semiring nat Q n / naturals_to_semiring nat Q d.
Instance rationals_lt `{Rationals A (Q:=Q)} : Lt A | 10 := dec_lt.

Section default_order.
  Context `{Rationals (Q:=Q)}.

  Add Field Q2 : (stdlib_field_theory Q).

  Notation n_to_sr := (naturals_to_semiring nat Q).

  (* preservation of nonzeros follows from this instance *)
  Instance : StrongInjective nat Q n_to_sr.
  Proof. apply dec_strong_injective. exact (injective_nats _). Qed.

  Instance: Proper ((Q,=) ==> (Q,=) ==> impl) (≤).
  Proof. intros x1 y1 E1 x2 y2 E2 [n [d [? E]]]. unfold_sigs.
    exists n. exists_sub d. now rewrite <- (Q $ E1), <- (Q $ E2).
  Qed.

  Instance: SubReflexive Q (≤).
  Proof. intros x ?. exists (0:nat). exists_sub (1:nat).
    preserves_simplify (n_to_sr). subfield Q.
  Qed.

  Instance: SubTransitive Q (≤).
  Proof. intros x ? y ? z ? [n1 [d1 [? E1]]] [n2 [d2 [? E2]]].
    exists (n1*d2+n2*d1). exists_sub (d1*d2).
    preserves_simplify (n_to_sr).
    rewrite (Q $ E2), (Q $ E1).
    subfield Q.
  Qed.

  Instance: SubAntiSymmetric Q (≤).
  Proof. intros x ? y ? [n1 [d1 [? E1]]] [n2 [d2 [? E2]]].
    rewrite (Q $ E1) in E2 |- *.
    clear dependent y.
    rewrite <- (Q $ associativity (+) _ _ _) in E2.
    rewrite <- (Q $ plus_0_r x) in E2 at 1.
    apply (left_cancellation (+) x Q _ _) in E2.
    destruct (zero_product n1 d2) as [F|F].
    + assert (n1*d2 + n2*d1 = 0) as Ezs.
        apply (injective n_to_sr _ _). preserves_simplify (n_to_sr).
        apply (right_cancellation (.*.) (n_to_sr d1 * n_to_sr d2)⁻¹ _ _ _).
        rewrite (Q $ mult_0_l _).
        subtransitivity (n_to_sr n1 / n_to_sr d1 + n_to_sr n2 / n_to_sr d2).
        subfield Q. subsymmetry.
      now destruct (naturals.zero_sum _ _ Ezs).
    + change (n1 ≡ 0) in F. rewrite F. preserves_simplify (n_to_sr). subfield Q.
    + contradict F. rewrite <- (standard_uneq _ _). now destruct (_ : d2 ∊ nat ₀).
  Qed.

  Instance: PartialOrder Q := {}.

  Instance: SemiRingOrder Q.
  Proof. apply from_ring_order.
  + intros z ?. split. split; apply _. intros x ? y ? [n [d [? E]]].
    exists n. exists_sub d. rewrite (Q $ E). exact (associativity (+) _ _ _).
  + intros x [? [n1 [d1 [? E1]]]] y [? [n2 [d2 [? E2]]]].
    split. apply _. exists (n1*n2). exists_sub (d1*d2).
    preserves_simplify (n_to_sr).
    rewrite (Q $ E1), (Q $ E2). subfield Q.
  Qed.

  Notation Z := (SRpair nat).
  Notation i_to_r := (integers_to_ring Z Q).

  Add Ring Z : (stdlib_ring_theory Z).

  Instance: SemiRing_Morphism Z⁺ Q (i_to_r) | 5 := semiring_mor_nonneg_mor i_to_r.
  Instance: StrongInjective (Z⁺) (nat) (naturals_to_semiring Z⁺ nat) := dec_strong_injective _ .
  Instance: StrongInjective nat Q n_to_sr := dec_strong_injective _ .
  Instance: Strong_Morphism (Z ₀) (Q ₀) (i_to_r) := _.

  Instance: TotalRelation Q (≤).
  Proof.
    assert (∀ xn `{xd ∊ Z₊} yn `{yd ∊ Z₊}, xn * yd ≤ yn * xd → i_to_r xn / i_to_r xd ≤ i_to_r yn / i_to_r yd) as P.
      intros xn xd ? yn yd ? E.
      pose proof (_ : xd ∊ Z ₀). pose proof (_ : xd ∊ Z⁺).
      pose proof (_ : yd ∊ Z ₀). pose proof (_ : yd ∊ Z⁺).
      destruct (semirings.decompose_le (R:=Z) E) as [z [? Ez1]].
      assert (z = yn * xd - xn * yd) as Ez. rewrite (Z $ Ez1). subring (Z).
      assert (xd * yd ∊ (Z⁺) ₀). split. apply _. now destruct (_ : xd * yd ∊ Z ₀).
      exists (naturals_to_semiring Z⁺ nat z).
      exists_sub (naturals_to_semiring Z⁺ nat (xd*yd) ).
      pose proof (naturals.to_semiring_twice (n_to_sr) (naturals_to_semiring Z⁺ nat) i_to_r) as P2.
      destruct ((_ : Proper ((Q ₀,=) ==> (Q ₀,=)) inv) _ _ (Q ₀ $ P2 (xd * yd) _)) as [[??] E2].
      rewrite (Q $ P2 z _), (Q $ E2). clear E2. rewrite (Z $ Ez).
      preserves_simplify (i_to_r). subfield Q.
    intros x ? y ?.
    destruct (rationals_decompose_pos_den i_to_r x) as [xn [? [xd [? Ex]]]].
    destruct (rationals_decompose_pos_den i_to_r y) as [yn [? [yd [? Ey]]]].
    destruct (total (≤) (xn * yd) (yn * xd)); [left | right]; rewrite (Q $ Ex), (Q $ Ey); now apply P.
  Qed.

  Global Instance: FullPseudoSemiRingOrder Q.
  Proof. now apply dec_full_pseudo_srorder. Qed.
End default_order.
