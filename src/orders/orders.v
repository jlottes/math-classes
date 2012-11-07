Require Import
  abstract_algebra interfaces.orders theory.common_props theory.strong_setoids.

Lemma le_proper : Find_Proper_Signature (@le) 0  (∀ `{PartialOrder   (P:=P)}, Proper ((P,=) ==> (P,=) ==> impl) (≤)). Proof. red. intros. apply po_proper. Qed.
Lemma lt_proper : Find_Proper_Signature (@lt) 0  (∀ `{StrictSetoidOrder (S:=T)}, Proper ((T,=) ==> (T,=) ==> impl) (<)). Proof. red. intros. apply so_proper. Qed.

Hint Extern 0 (Find_Proper_Signature (@le) 0 _) => eexact le_proper : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@lt) 0 _) => eexact lt_proper : typeclass_instances.

(** Any subset of an order is still an order. *) 

Local Ltac proper_tac := red; intros; intros S1 S2 ES; destruct 1; unfold flip in ES; split; try rewrite ES; trivial.
Local Ltac proper_tac2 := let S1 := match goal with _ : SubsetOf _ ?S1 |- _ => S1 end in
  intros ?? E1 ?? E2 ?; unfold_sigs; rewrite_on S1 <- E1; now rewrite_on S1 <- E2.

Local Hint Extern 20 (?x ∊ ?T) => match goal with
  | sub : SubsetOf _ ?T |- _ => eapply (subset (SubsetOf:=sub) x)
end : typeclass_instances.

Lemma PartialOrder_proper     : Find_Proper_Signature (@PartialOrder     ) 0 (∀ A Ae     Ale    , Proper (SubsetOf-->impl) (@PartialOrder     A Ae     Ale    )).
Proof. proper_tac. proper_tac2. Qed.
Hint Extern 0 (Find_Proper_Signature (@PartialOrder    ) 0 _) => eexact PartialOrder_proper     : typeclass_instances.

Lemma TotalOrder_proper       : Find_Proper_Signature (@TotalOrder       ) 0 (∀ A Ae     Ale    , Proper (SubsetOf-->impl) (@TotalOrder       A Ae     Ale    )).
Proof. proper_tac. Qed.
Hint Extern 0 (Find_Proper_Signature (@TotalOrder      ) 0 _) => eexact TotalOrder_proper       : typeclass_instances.

Lemma StrictSetoidOrder_proper: Find_Proper_Signature (@StrictSetoidOrder) 0 (∀ A Ae         Alt, Proper (SubsetOf-->impl) (@StrictSetoidOrder   A Ae         Alt)).
Proof. proper_tac. proper_tac2. Qed.
Hint Extern 0 (Find_Proper_Signature (@StrictSetoidOrder  ) 0 _) => eexact StrictSetoidOrder_proper   : typeclass_instances.

Lemma PseudoOrder_proper      : Find_Proper_Signature (@PseudoOrder      ) 0 (∀ A Ae Aue     Alt, Proper (SubsetOf-->impl) (@PseudoOrder      A Ae Aue     Alt)).
Proof. proper_tac; intros. apply (pseudo_order_antisym _ _ _ _). apply (apart_iff_total_lt _ _ _ _). Qed.
Hint Extern 0 (Find_Proper_Signature (@PseudoOrder     ) 0 _) => eexact PseudoOrder_proper      : typeclass_instances.

Lemma FullPartialOrder_proper : Find_Proper_Signature (@FullPartialOrder ) 0 (∀ A Ae Aue Ale Alt, Proper (SubsetOf-->impl) (@FullPartialOrder A Ae Aue Ale Alt)).
Proof. proper_tac; intros. apply (lt_iff_le_apart _ _ _ _). Qed.
Hint Extern 0 (Find_Proper_Signature (@FullPartialOrder) 0 _) => eexact FullPartialOrder_proper : typeclass_instances.

Lemma FullPseudoOrder_proper  : Find_Proper_Signature (@FullPseudoOrder  ) 0 (∀ A Ae Aue Ale Alt, Proper (SubsetOf-->impl) (@FullPseudoOrder  A Ae Aue Ale Alt)).
Proof. proper_tac; intros. apply (le_iff_not_lt_flip _ _ _ _). Qed.
Hint Extern 0 (Find_Proper_Signature (@FullPseudoOrder ) 0 _) => eexact FullPseudoOrder_proper  : typeclass_instances.




Lemma le_flip `{Le} {S} `{!TotalRelation S (≤)} x `{x ∊ S} y `{y ∊ S} : ¬y ≤ x → x ≤ y.
Proof. firstorder. Qed.

Section partial_order.
  Context `{PartialOrder (P:=P)}.

  Existing Instance po_setoid.

  Lemma eq_le  x `{x ∊ P} y `{y ∊ P} : x = y → x ≤ y.
  Proof. intros E. now rewrite_on P -> E. Qed.

  Lemma eq_le_flip x `{x ∊ P} y `{y ∊ P} : x = y → y ≤ x.
  Proof. intros E. now rewrite_on P -> E. Qed.

  Lemma not_le_ne x `{x ∊ P} y `{y ∊ P} : ¬x ≤ y → ¬ x = y.
  Proof. intros E1 E2. destruct E1. now rewrite_on P -> E2. Qed.

  Lemma eq_iff_le x `{x ∊ P} y `{y ∊ P} : x = y ↔ x ≤ y ∧ y ≤ x.
  Proof. split; intros E. split; now rewrite_on P -> E.
         now apply (subantisymmetry (≤) x y). Qed.
End partial_order.

Section strict_order.
  Context `{S:Subset} `{StrictSetoidOrder _ (S:=S)}.

  Existing Instance so_setoid.

  Lemma lt_flip x `{x ∊ S} y `{y ∊ S} : x < y → ¬y < x.
  Proof.
    intros E1 E2.
    apply (subirreflexivity (<) x).
    subtransitivity y.
  Qed.

  Lemma lt_antisym x `{x ∊ S} y `{y ∊ S} : ¬(x < y < x).
  Proof.
    intros [E1 E2].
    now destruct (lt_flip x y).
  Qed.

  Lemma lt_ne x `{x ∊ S} y `{y ∊ S} : x < y → ¬ x = y.
  Proof. intros E1 E2. rewrite_on S -> E2 in E1. now destruct (subirreflexivity (<) y). Qed.

  Lemma lt_ne_flip x `{x ∊ S} y `{y ∊ S} : x < y → ¬ y = x.
  Proof. intro P. pose proof lt_ne x y P as E. contradict E. subsymmetry. Qed.

  Lemma eq_not_lt x `{x ∊ S} y `{y ∊ S} : x = y → ¬x < y.
  Proof. intros E. rewrite_on S -> E. now apply (subirreflexivity (<)). Qed.
End strict_order.

Section pseudo_order.
  Context `{S:Subset} `{PseudoOrder _ (S:=S)}.

  Existing Instance pseudo_order_setoid.

  Lemma apart_total_lt x `{x ∊ S} y `{y ∊ S} : x ≠ y → x < y ∨ y < x.
  Proof. intros. now apply (apart_iff_total_lt x y). Qed.

  Lemma pseudo_order_lt_apart x `{x ∊ S} y `{y ∊ S} : x < y → x ≠ y.
  Proof. intros. apply (apart_iff_total_lt x y). tauto. Qed.

  Lemma pseudo_order_lt_apart_flip x `{x ∊ S} y `{y ∊ S} : x < y → y ≠ x.
  Proof. intros. apply (apart_iff_total_lt y x). tauto. Qed.

  Lemma not_lt_apart_lt_flip x `{x ∊ S} y `{y ∊ S} : ¬x < y → x ≠ y → y < x.
  Proof. rewrite (apart_iff_total_lt x y). intuition. Qed.

  Lemma pseudo_order_cotrans_twice x₁ `{x₁ ∊ S} y₁ `{y₁ ∊ S} x₂ `{x₂ ∊ S} y₂ `{y₂ ∊ S}
    : x₁ < y₁ → x₂ < y₂ ∨ x₁ < x₂ ∨ y₂ < y₁.
  Proof.
    intros E1.
    destruct (subcotransitivity E1 x₂) as [E2|E2]; try tauto.
    destruct (subcotransitivity E2 y₂); try tauto.
  Qed.

  Lemma pseudo_order_lt_ext x₁ `{x₁ ∊ S} y₁ `{y₁ ∊ S} x₂ `{x₂ ∊ S} y₂ `{y₂ ∊ S}
    : x₁ < y₁ → x₂ < y₂ ∨ x₁ ≠ x₂ ∨ y₂ ≠ y₁.
  Proof.
    intros E.
    destruct (pseudo_order_cotrans_twice x₁ y₁ x₂ y₂ E) as [?|[?|?]]; auto using pseudo_order_lt_apart.
  Qed.

  Instance: Proper ((S,=) ==> (S,=) ==> impl) (<).
  Proof.
     intros x₁ x₂ Ex y₁ y₂ Ey E. unfold_sigs.
     destruct (pseudo_order_lt_ext x₁ y₁ x₂ y₂ E) as [?|[?|?]]; try tauto.
      contradict Ex. now apply uneq_ne.
     contradict Ey. apply (uneq_ne _ _). subsymmetry.
  Qed.

  Global Instance: StrictSetoidOrder S.
  Proof.
    repeat (split; try apply _).
     intros x ? E.
     destruct (pseudo_order_antisym x x); tauto.
    intros x ? y ? z ? E1 E2.
    destruct (subcotransitivity E1 z); trivial.
    destruct (pseudo_order_antisym y z); tauto.
  Qed.

  Global Instance: SubTransitive S (complement (<)).
  Proof.
    intros x ? y ? z ? E1 E2 E3.
    destruct (subcotransitivity E3 y); contradiction.
  Qed.

  Global Instance: SubAntiSymmetric S (complement (<)).
  Proof. intros x ? y ?. rewrite <-(tight_apart _ _), (apart_iff_total_lt x y). intuition. Qed.

  Lemma ne_total_lt `{!StandardUnEq S} x `{x ∊ S} y `{y ∊ S} : ¬ x = y → x < y ∨ y < x.
  Proof. rewrite <- (standard_uneq _ _). now apply apart_total_lt. Qed.

  Global Instance lt_trichotomy `{!StandardUnEq S} `{!SubDecision S S (=)} : Trichotomy S (<).
  Proof.
    intros x ? y ?.
    destruct (decide_sub (=) x y) as [?|?]; try tauto.
    destruct (ne_total_lt x y); tauto.
  Qed.
End pseudo_order.

Section full_partial_order.
  Context `{FullPartialOrder (P:=P)}.

  Existing Instance strict_po_setoid.
  Existing Instance po_setoid.

  Global Instance: StrictSetoidOrder P.
  Proof.
    split; try apply _.
     intros x1 y1 E1 x2 y2 E2. unfold_sigs.
     rewrite ?lt_iff_le_apart; trivial. intro.
     rewrite_on P <- E1. now rewrite_on P <- E2.
    intros x ?. rewrite (lt_iff_le_apart x x). intros [_ ?].
    now destruct (subirreflexivity (≠) x).
  Qed.

  Lemma lt_le x `{x ∊ P} y `{y ∊ P} : PropHolds (x < y) → PropHolds (x ≤ y).
  Proof. intro. now apply lt_iff_le_apart. Qed.

  Lemma not_le_not_lt x `{x ∊ P} y `{y ∊ P} : ¬x ≤ y → ¬x < y.
  Proof. intro E. contradict E. exact (lt_le x y E). Qed.

  Lemma lt_apart x `{x ∊ P} y `{y ∊ P} : x < y → x ≠ y.
  Proof. intro. now apply lt_iff_le_apart. Qed.

  Lemma lt_apart_flip x `{x ∊ P} y `{y ∊ P} : x < y → y ≠ x.
  Proof. intro. subsymmetry. now apply lt_iff_le_apart. Qed.

  Lemma le_not_lt_flip x `{x ∊ P} y `{y ∊ P} : y ≤ x → ¬x < y.
  Proof.
    rewrite (lt_iff_le_apart x y).
    intros E1 [E2a E2b].
    contradict E2b. rewrite_on P -> (subantisymmetry (≤) x y E2a E1).
     now apply (subirreflexivity _).
  Qed.

  Lemma lt_not_le_flip x `{x ∊ P} y `{y ∊ P} : y < x → ¬x ≤ y.
  Proof.
    intros E1 E2.
    now destruct (le_not_lt_flip y x).
  Qed.

  Lemma lt_le_trans x `{x ∊ P} y `{y ∊ P} z `{z ∊ P} : x < y → y ≤ z → x < z.
  Proof.
    rewrite !lt_iff_le_apart; trivial.
    intros [E1a E1b] E2.
    split. subtransitivity y.
    destruct (subcotransitivity E1b z) as [E3 | E3]; trivial.
    apply (lt_apart x z). subsymmetry in E3.
    subtransitivity y; rewrite lt_iff_le_apart; tauto.
  Qed.

  Lemma le_lt_trans x `{x ∊ P} y `{y ∊ P} z `{z ∊ P} : x ≤ y → y < z → x < z.
  Proof.
    rewrite !lt_iff_le_apart; trivial.
    intros E2 [E1a E1b].
    split. subtransitivity y.
    destruct (subcotransitivity E1b x) as [E3 | E3]; trivial.
    apply (lt_apart x z). subsymmetry in E3.
    subtransitivity y; rewrite lt_iff_le_apart; tauto.
  Qed.

  Lemma lt_iff_le_ne `{!StandardUnEq P} x `{x ∊ P} y `{y ∊ P} : x < y ↔ x ≤ y ∧ ¬ x = y.
  Proof. rewrite <- (standard_uneq _ _). now apply lt_iff_le_apart. Qed.

  Lemma le_equiv_lt `{!StandardUnEq P} `{!SubDecision P P (=)} x `{x ∊ P} y `{y ∊ P} : x ≤ y → x = y ∨ x < y.
  Proof.
    intros. destruct (decide_sub (=) x y); try tauto.
    right. rewrite lt_iff_le_ne; tauto.
  Qed.

  Program Instance strong_dec_from_lt_dec `{!StandardUnEq P} `{!StrongSubDecision P P (≤)} :
     StrongSubDecision P P (=) := λ x y,
    match decide_sub_strong (≤) x y with
    | left E1 => match decide_sub_strong (≤) y x with
       | left E2 => left _
       | right E2 => right _
       end
     | right E1 => right _
     end.
  Next Obligation. apply (subantisymmetry (≤)); auto. Qed.
  Next Obligation. intro E. subsymmetry in E. generalize E. apply not_le_ne; auto. Qed.
  Next Obligation. apply not_le_ne; auto. Qed.

  Program Instance dec_from_lt_dec `{!StandardUnEq P} `{!SubDecision P P (≤)} :
     SubDecision P P (=) := λ x xs y ys,
    match decide_sub (≤) x y with
    | left E1 => match decide_sub (≤) y x with
       | left E2 => left _
       | right E2 => right _
       end
     | right E1 => right _
     end.
  Next Obligation. now apply (subantisymmetry (≤)). Qed.
  Next Obligation. intro E. subsymmetry in E. generalize E. now apply not_le_ne. Qed.
  Next Obligation. now apply not_le_ne. Qed.

  Definition strong_lt_dec_slow `{!StandardUnEq P} `{!StrongSubDecision P P (≤)} : StrongSubDecision P P (<).
  Proof. intros x y.
    destruct (decide_sub_strong (≤) x y).
     destruct (decide_sub_strong (=) x y).
      right. intros. apply eq_not_lt; intuition.
     left. intros. apply lt_iff_le_ne; intuition.
    right. intros. apply not_le_not_lt; intuition.
  Defined.

  Definition lt_dec_slow `{!StandardUnEq P} `{!SubDecision P P (≤)} : SubDecision P P (<).
  Proof. intros x ? y ?.
    destruct (decide_sub (≤) x y).
     destruct (decide_sub (=) x y).
      right. now apply eq_not_lt.
     left. apply lt_iff_le_ne; intuition.
    right. now apply not_le_not_lt.
  Defined.
End full_partial_order.

Hint Extern 10 (PropHolds (_ ≤ _)) => eapply @lt_le : typeclass_instances.
Hint Extern 20 (StrongSubDecision _ _ (<)) => eapply @strong_lt_dec_slow : typeclass_instances.
Hint Extern 20 (SubDecision _ _ (<)) => eapply @lt_dec_slow : typeclass_instances.

Section full_pseudo_order.
  Context `{S:Subset} `{FullPseudoOrder _ (S:=S)}.

  Existing Instance pseudo_order_setoid.

  Lemma not_lt_le_flip x `{x ∊ S} y `{y ∊ S} : ¬y < x → x ≤ y.
  Proof. intros. now apply le_iff_not_lt_flip. Qed.

  Instance: PartialOrder S.
  Proof. split; try apply _.
  + intros ?? E1 ?? E2. unfold_sigs.
    rewrite !le_iff_not_lt_flip; trivial. intro.
    now rewrite_on S <- E1, <- E2.
  + intros x ?. now apply not_lt_le_flip, (subirreflexivity (<) x).
  + intros x ? y ? z ?.
    rewrite !le_iff_not_lt_flip; trivial.
    intros. change (complement (<) z x).
    subtransitivity y.
  + intros x ? y ?.
    rewrite !le_iff_not_lt_flip; trivial.
    intros. now apply (subantisymmetry (complement (<))).
  Qed.

  Global Instance: FullPartialOrder S.
  Proof. split; try apply _.
    intros x ? y ?. rewrite !le_iff_not_lt_flip; trivial. split.
     intros E. split.
      now apply lt_flip.
     now apply pseudo_order_lt_apart.
    intros [? E].
    now apply not_lt_apart_lt_flip.
  Qed.

  Global Instance: ∀ `{x ∊ S} `{y ∊ S}, Stable (x ≤ y).
  Proof.
    intros x ? y ?. unfold Stable, DN.
    rewrite !le_iff_not_lt_flip; tauto.
  Qed.

  Lemma le_or_lt `{!StandardUnEq S} `{!SubDecision S S (=)} x `{x ∊ S} y `{y ∊ S} : x ≤ y ∨ y < x.
  Proof.
    destruct (trichotomy (<) x y) as [|[|]]; try tauto.
     left. now apply lt_le.
    left. now apply eq_le_flip.
  Qed.

  Global Instance le_total `{!StandardUnEq S} `{!SubDecision S S (=)} : TotalOrder S.
  Proof. split; try apply _. intros x ? y ?. destruct (le_or_lt x y). tauto. right. now apply lt_le. Qed.

  Lemma not_le_lt_flip `{!StandardUnEq S} `{!SubDecision S S (=)} x `{x ∊ S} y `{y ∊ S} : ¬y ≤ x → x < y.
  Proof. intros. destruct (le_or_lt y x); intuition. Qed.

  Existing Instance strong_dec_from_lt_dec.
  Existing Instance dec_from_lt_dec.

  Program Definition strong_lt_dec `{!StandardUnEq S} `{!StrongSubDecision S S (≤)} : StrongSubDecision S S (<)
     := λ x y,
    match decide_sub_strong (≤) y x with
    | left E => right _
    | right E => left _
    end.
  Next Obligation. apply le_not_lt_flip; intuition. Qed.
  Next Obligation. apply not_le_lt_flip; intuition. Qed.

  Program Definition lt_dec `{!StandardUnEq S} `{!SubDecision S S (≤)} : SubDecision S S (<)
     := λ x xs y ys,
    match decide_sub (≤) y x with
    | left E => right _
    | right E => left _
    end.
  Next Obligation. now apply le_not_lt_flip. Qed.
  Next Obligation. now apply not_le_lt_flip. Qed.
End full_pseudo_order.

Hint Extern 8 (StrongSubDecision _ _ (<)) => eapply @strong_lt_dec : typeclass_instances.
Hint Extern 8 (SubDecision _ _ (<)) => eapply @lt_dec : typeclass_instances.
(*
The following instances would be tempting, but turn out to be a bad idea.

Hint Extern 10 (PropHolds (_ ≠ _)) => eapply @le_ne : typeclass_instances.
Hint Extern 10 (PropHolds (_ ≠ _)) => eapply @le_ne_flip : typeclass_instances.

It will then loop like:

semirings.lt_0_1 → lt_ne_flip → ...
*)

Section dec_strict_order.
  Context `{S:Subset} `{StrictSetoidOrder _ (S:=S)} `{UnEq _} `{!StandardUnEq S} `{!SubDecision S S (=)}.

  Existing Instance so_setoid.
  Instance: StrongSetoid S := dec_strong_setoid.

  Context `{!Trichotomy S (<)}.

  Instance dec_strict_pseudo_order: PseudoOrder S.
  Proof. split. apply _.
  + intros x ? y ? [??]. destruct (lt_antisym x y); tauto.
  + intros x ? y ? Exy z ?.
     destruct (trichotomy (<) x z) as [? | [Exz | Exz]]; try tauto.
      right. now rewrite_on S <- Exz.
     right. subtransitivity x.
  + intros x ? y ?. rewrite (standard_uneq _ _). split.
     destruct (trichotomy (<) x y); intuition.
    intros [?|?]. now apply lt_ne. now apply lt_ne_flip.
  Qed.
End dec_strict_order.

Section dec_partial_order.
  Context `{PartialOrder A (P:=P)} `{!SubDecision P P (=)}.

  Existing Instance po_setoid.

  Definition dec_lt `{UnEq A} : Lt A := λ x y, x ≤ y ∧ x ≠ y.

  Context `{UnEq A} `{!StandardUnEq P} `{Alt : Lt A}
          (lt_correct : ∀ `{x ∊ P} `{y ∊ P}, x < y ↔ x ≤ y ∧ x ≠ y).

  Instance dec_order: StrictSetoidOrder P.
  Proof. split; try apply _.
  + intros ? ? E1 ? ? E2. unfold_sigs.
    rewrite !lt_correct; trivial.
    now rewrite_on P -> E1, E2.
  + intros x ?. rewrite lt_correct; trivial. rewrite (standard_uneq _ _). now intros [_ []].
  + intros x ? y ? z ?. rewrite !lt_correct; trivial.
    rewrite !standard_uneq; trivial. intros [E1a E1b] [E2a E2b].
    split. subtransitivity y.
    intros E3. destruct E2b.
    apply (subantisymmetry (≤)); trivial.
    now rewrite_on P <- E3.
  Qed.

  Instance: StrongSetoid P := dec_strong_setoid.

  Instance dec_full_partial_order: FullPartialOrder P := {}.
  Proof. apply lt_correct. Qed.

  Context `{!TotalRelation P (≤)}.

  Instance: Trichotomy P (<).
  Proof.
    intros x ? y ?. rewrite !(lt_correct _ _ _ _), !(standard_uneq _ _).
    destruct (decide_sub (=) x y) as [|E]; try tauto.
    assert (¬y = x). contradict E. subsymmetry.
    destruct (total (≤) x y); intuition.
  Qed.

  Instance dec_pseudo_order: PseudoOrder P.
  Proof dec_strict_pseudo_order.

  Instance dec_full_pseudo_order: FullPseudoOrder P.
  Proof.
    split; try apply _.
    intros x ? y ?. rewrite (lt_correct _ _ _ _), (standard_uneq _ _). split.
     intros ? [? []]. now apply (subantisymmetry (≤)).
    intros E1.
    destruct (total (≤) x y); trivial.
    destruct (decide_sub (=) x y) as [E2|E2].
     rewrite_on P -> E2. subreflexivity.
    assert (¬y = x). contradict E2. subsymmetry.
    intuition.
  Qed.
End dec_partial_order.
