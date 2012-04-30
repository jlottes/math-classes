Require Import
  abstract_algebra interfaces.orders theory.common_props theory.sub_strong_setoids.

Lemma le_proper : Find_Proper_Signature (@le) 0  (∀ `{PartialOrder   (P:=P)}, Proper ((P,=) ==> (P,=) ==> impl) (≤)). Proof. red. intros. apply po_proper. Qed.
Lemma lt_proper : Find_Proper_Signature (@lt) 0  (∀ `{SubStrictOrder (S:=T)}, Proper ((T,=) ==> (T,=) ==> impl) (<)). Proof. red. intros. apply so_proper. Qed.

Hint Extern 0 (Find_Proper_Signature (@le) 0 _) => eexact le_proper : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@lt) 0 _) => eexact lt_proper : typeclass_instances.

Local Ltac proper_tac1 S1 ES intro_tac split_tac := red; intros; intros S1 S2 [[??] ES]; intro_tac; split_tac; try apply _.
Local Ltac proper_tac2 := let S1 := fresh "S1" in let ES := fresh "ES" in
  proper_tac1 S1 ES ltac:(intro Q; destruct Q) ltac:(split; [split | | rewrite ES..]);
  intros ?? E1 ?? E2 ?; unfold_sigs; rewrite_on S1 <- E1; now rewrite_on S1 <- E2.
Local Ltac proper_tac3 intro_tac split_tac := let S1 := fresh "S1" in let ES := fresh "ES" in
  proper_tac1 S1 ES intro_tac split_tac; intros x ? y ?.

(* Any well-formed subset of an order is still an order. *) 

Lemma PartialOrder_proper     : Find_Proper_Signature (@PartialOrder    ) 0 (∀ A Ae     Ale    , Proper ((ProperSubset,⊆)-->impl) (@PartialOrder     A Ae     Ale    )). Proof. proper_tac2. Qed.
Lemma TotalOrder_proper       : Find_Proper_Signature (@TotalOrder      ) 0 (∀ A Ae     Ale    , Proper ((ProperSubset,⊆)-->impl) (@TotalOrder       A Ae     Ale    )). Proof. red. intros. intros ?? ES ?. unfold flip in *. split; [ apply (PartialOrder_proper _ _ _ _ _ ES) | rewrite ES]; apply _. Qed.
Lemma SubStrictOrder_proper   : Find_Proper_Signature (@SubStrictOrder  ) 0 (∀ A Ae         Alt, Proper ((ProperSubset,⊆)-->impl) (@SubStrictOrder   A Ae         Alt)). Proof. proper_tac2. Qed.
Lemma PseudoOrder_proper      : Find_Proper_Signature (@PseudoOrder     ) 0 (∀ A Ae Aue     Alt, Proper ((ProperSubset,⊆)-->impl) (@PseudoOrder      A Ae Aue     Alt)). Proof. proper_tac3 ltac:(intros [? P1 ? P2]) ltac:(split; [split | | rewrite ES |]). exact (P1 x _ y _). exact (P2 x _ y _). Qed.
Lemma FullPartialOrder_proper : Find_Proper_Signature (@FullPartialOrder) 0 (∀ A Ae Aue Ale Alt, Proper ((ProperSubset,⊆)-->impl) (@FullPartialOrder A Ae Aue Ale Alt)). Proof. proper_tac3 ltac:(intros [??? P]) ltac:(split; [| apply (PartialOrder_proper _ _ _ _ _  (to_propersubset_rel ES)) | rewrite ES |]). exact (P x _ y _). Qed.
Lemma FullPseudoOrder_proper  : Find_Proper_Signature (@FullPseudoOrder ) 0 (∀ A Ae Aue Ale Alt, Proper ((ProperSubset,⊆)-->impl) (@FullPseudoOrder  A Ae Aue Ale Alt)). Proof. proper_tac3 ltac:(intros [?   P]) ltac:(split; [  apply (PseudoOrder_proper _ _ _ _ _ _ (to_propersubset_rel ES)) |]).              exact (P x _ y _). Qed.

Hint Extern 0 (Find_Proper_Signature (@PartialOrder    ) 0 _) => eexact PartialOrder_proper     : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@TotalOrder      ) 0 _) => eexact TotalOrder_proper       : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@SubStrictOrder  ) 0 _) => eexact SubStrictOrder_proper   : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@PseudoOrder     ) 0 _) => eexact PseudoOrder_proper      : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@FullPartialOrder) 0 _) => eexact FullPartialOrder_proper : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@FullPseudoOrder ) 0 _) => eexact FullPseudoOrder_proper  : typeclass_instances.

Local Ltac proper2 tac :=
  red; intros; intros S1 S2 ES ?; tac;
  assert (ProperSubset S2) by (rewrite <- ES; apply _);
  now rewrite_subset <- ES.

(* For equal subsets, the well-formedness condition (ProperSubset) follows from the subsets being equal. *)

Lemma PartialOrder_proper2     : Find_Proper_Signature (@PartialOrder)     1 (∀ A Ae     Ale    , Proper ((=)==>impl) (@PartialOrder     A Ae     Ale    )). Proof. proper2 ltac:(pose proof po_subsetoid). Qed.
Lemma TotalOrder_proper2       : Find_Proper_Signature (@TotalOrder)       1 (∀ A Ae     Ale    , Proper ((=)==>impl) (@TotalOrder       A Ae     Ale    )). Proof. proper2 ltac:(pose proof po_subsetoid). Qed.
Lemma SubStrictOrder_proper2   : Find_Proper_Signature (@SubStrictOrder)   1 (∀ A Ae         Alt, Proper ((=)==>impl) (@SubStrictOrder   A Ae         Alt)). Proof. proper2 ltac:(pose proof so_subsetoid). Qed.
Lemma PseudoOrder_proper2      : Find_Proper_Signature (@PseudoOrder)      1 (∀ A Ae Aue     Alt, Proper ((=)==>impl) (@PseudoOrder      A Ae Aue     Alt)). Proof. proper2 ltac:(pose proof pseudo_order_setoid). Qed.
Lemma FullPartialOrder_proper2 : Find_Proper_Signature (@FullPartialOrder) 1 (∀ A Ae Aue Ale Alt, Proper ((=)==>impl) (@FullPartialOrder A Ae Aue Ale Alt)). Proof. proper2 ltac:(pose proof po_subsetoid). Qed.
Lemma FullPseudoOrder_proper2  : Find_Proper_Signature (@FullPseudoOrder)  1 (∀ A Ae Aue Ale Alt, Proper ((=)==>impl) (@FullPseudoOrder  A Ae Aue Ale Alt)). Proof. proper2 ltac:(pose proof pseudo_order_setoid). Qed.

Hint Extern 0 (Find_Proper_Signature (@PartialOrder    ) 1 _) => eexact PartialOrder_proper2     : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@TotalOrder      ) 1 _) => eexact TotalOrder_proper2       : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@SubStrictOrder  ) 1 _) => eexact SubStrictOrder_proper2   : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@PseudoOrder     ) 1 _) => eexact PseudoOrder_proper2      : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@FullPartialOrder) 1 _) => eexact FullPartialOrder_proper2 : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@FullPseudoOrder ) 1 _) => eexact FullPseudoOrder_proper2  : typeclass_instances.



Lemma le_flip `{Le A} {S:Subset A} `{!TotalRelation (≤) S} x `{x ∊ S} y `{y ∊ S} : ¬y ≤ x → x ≤ y.
Proof. firstorder. Qed.

Section partial_order.
  Context `{PartialOrder (P:=P)}.

  Existing Instance po_subsetoid.

  Lemma eq_le  x `{x ∊ P} y `{y ∊ P} : x = y → x ≤ y.
  Proof. intros E. rewrite_on P -> E. subreflexivity. Qed.

  Lemma eq_le_flip x `{x ∊ P} y `{y ∊ P} : x = y → y ≤ x.
  Proof. intros E. rewrite_on P -> E. subreflexivity. Qed.

  Lemma not_le_ne x `{x ∊ P} y `{y ∊ P} : ¬x ≤ y → ¬ x = y.
  Proof. intros E1 E2. destruct E1. rewrite_on P -> E2. subreflexivity. Qed.

  Lemma eq_iff_le x `{x ∊ P} y `{y ∊ P} : x = y ↔ x ≤ y ∧ y ≤ x.
  Proof. split; intros E. split; rewrite_on P -> E; subreflexivity.
         now apply (subantisymmetry (≤) x y). Qed.
End partial_order.

Section strict_order.
  Context `{S:Subset A} `{SubStrictOrder (A:=A) (S:=S)}.

  Existing Instance so_subsetoid.

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
  Proof. intro. now apply not_symmetry, lt_ne. Qed.

  Lemma eq_not_lt x `{x ∊ S} y `{y ∊ S} : x = y → ¬x < y.
  Proof. intros E. rewrite_on S -> E. now apply (subirreflexivity (<)). Qed.
End strict_order.

Section pseudo_order.
  Context `{S:Subset A} `{PseudoOrder (A:=A) (S:=S)}.

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
     contradict Ey. now apply not_symmetry, uneq_ne.
  Qed.

  Global Instance: SubStrictOrder S.
  Proof.
    repeat (split; try apply _).
     intros x ? E.
     destruct (pseudo_order_antisym x x); tauto.
    intros x ? y ? z ? E1 E2.
    destruct (subcotransitivity E1 z); trivial.
    destruct (pseudo_order_antisym y z); tauto.
  Qed.

  Global Instance: SubTransitive (complement (<)) S.
  Proof.
    intros x ? y ? z ? E1 E2 E3.
    destruct (subcotransitivity E3 y); contradiction.
  Qed.

  Global Instance: SubAntiSymmetric (complement (<)) S.
  Proof. intros x ? y ?. rewrite <-tight_apart, (apart_iff_total_lt x y). intuition. Qed.

  Lemma ne_total_lt `{!StandardUnEq A} x `{x ∊ S} y `{y ∊ S} : ¬ x = y → x < y ∨ y < x.
  Proof. rewrite <- standard_uneq. now apply apart_total_lt. Qed.

  Global Instance lt_trichotomy `{!StandardUnEq A} `{!SubDecision (=) S S} : Trichotomy (<) S.
  Proof.
    intros x ? y ?.
    destruct (decide_sub (=) x y) as [?|?]; try tauto.
    destruct (ne_total_lt x y); tauto.
  Qed.
End pseudo_order.

Section full_partial_order.
  Context `{FullPartialOrder (P:=P)}.

  Existing Instance strict_po_setoid.
  Existing Instance po_subsetoid.

(*
  Instance strict_po_apart_ne x y : PropHolds (x ≶ y) → PropHolds (x ≠ y).
  Proof. intros. apply _. Qed.

  Global Instance apart_proper: Proper ((=) ==> (=) ==> iff) (≶).
  Proof. apply _. Qed.
*)

  Global Instance: SubStrictOrder P.
  Proof.
    split; try apply _.
     intros x1 y1 E1 x2 y2 E2. unfold_sigs.
     rewrite ?lt_iff_le_apart; trivial. intro.
     rewrite_on P <- E1. now rewrite_on P <- E2.
    intros x ?. rewrite (lt_iff_le_apart x x). intros [_ ?].
    now destruct (irreflexivity (≠) x).
  Qed.

  Lemma lt_le x `{x ∊ P} y `{y ∊ P} : PropHolds (x < y) → PropHolds (x ≤ y).
  Proof. intro. now apply lt_iff_le_apart. Qed.

  Lemma not_le_not_lt x `{x ∊ P} y `{y ∊ P} : ¬x ≤ y → ¬x < y.
  Proof. intro E. contradict E. exact (lt_le x y E). Qed.

  Lemma lt_apart x `{x ∊ P} y `{y ∊ P} : x < y → x ≠ y.
  Proof. intro. now apply lt_iff_le_apart. Qed.

  Lemma lt_apart_flip x `{x ∊ P} y `{y ∊ P} : x < y → y ≠ x.
  Proof. intro. now apply symmetry, lt_iff_le_apart. Qed.

  Lemma le_not_lt_flip x `{x ∊ P} y `{y ∊ P} : y ≤ x → ¬x < y.
  Proof.
    rewrite (lt_iff_le_apart x y).
    intros E1 [E2a E2b].
    contradict E2b. setoid_replace x with y.
     now apply (irreflexivity _).
    now apply (subantisymmetry (≤)).
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
    destruct (cotransitive E1b z) as [E3 | E3]; trivial.
    apply (lt_apart x z). symmetry in E3.
    subtransitivity y; rewrite lt_iff_le_apart; tauto.
  Qed.

  Lemma le_lt_trans x `{x ∊ P} y `{y ∊ P} z `{z ∊ P} : x ≤ y → y < z → x < z.
  Proof.
    rewrite !lt_iff_le_apart; trivial.
    intros E2 [E1a E1b].
    split. subtransitivity y.
    destruct (cotransitive E1b x) as [E3 | E3]; trivial.
    apply (lt_apart x z). symmetry in E3.
    subtransitivity y; rewrite lt_iff_le_apart; tauto.
  Qed.

  Lemma lt_iff_le_ne `{!StandardUnEq A} x `{x ∊ P} y `{y ∊ P} : x < y ↔ x ≤ y ∧ ¬ x = y.
  Proof. rewrite <- standard_uneq. now apply lt_iff_le_apart. Qed.

  Lemma le_equiv_lt `{!StandardUnEq A} `{∀ x y, Decision (x = y)} x `{x ∊ P} y `{y ∊ P} : x ≤ y → x = y ∨ x < y.
  Proof.
    intros. destruct (decide (x = y)); try tauto.
    right. rewrite lt_iff_le_ne; tauto.
  Qed.

  Program Instance dec_from_lt_dec `{!StandardUnEq A} `{!SubDecision (≤) P P} :
     SubDecision (=) P P := λ x xs y ys,
    match decide_sub (≤) x y with
    | left E1 => match decide_sub (≤) y x with
       | left E2 => left _
       | right E2 => right _
       end
     | right E1 => right _
     end.
  Next Obligation. now apply (subantisymmetry (≤)). Qed.
  Next Obligation. apply not_symmetry. now apply not_le_ne. Qed.
  Next Obligation. now apply not_le_ne. Qed.

  Definition lt_dec_slow `{!StandardUnEq A} `{!SubDecision (≤) P P} : SubDecision (<) P P.
  Proof. intros x ? y ?.
    destruct (decide_sub (≤) x y).
     destruct (decide_sub (=) x y).
      right. now apply eq_not_lt.
     left. apply lt_iff_le_ne; intuition.
    right. now apply not_le_not_lt.
  Defined.
End full_partial_order.

Hint Extern 10 (PropHolds (_ ≤ _)) => eapply @lt_le : typeclass_instances.
Hint Extern 20 (SubDecision (<) _ _) => eapply @lt_dec_slow : typeclass_instances.

Section full_pseudo_order.
  Context `{S:Subset A} `{FullPseudoOrder (A:=A) (S:=S)}.

  Existing Instance pseudo_order_setoid.

  Lemma not_lt_le_flip x `{x ∊ S} y `{y ∊ S} : ¬y < x → x ≤ y.
  Proof. intros. now apply le_iff_not_lt_flip. Qed.

  Instance: PartialOrder S.
  Proof. split; try apply _.
  + intros ?? E1 ?? E2. unfold_sigs.
    rewrite !le_iff_not_lt_flip; trivial. intro.
    rewrite_on S <- E1. now rewrite_on S <- E2.
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

  Lemma le_or_lt `{!StandardUnEq A} `{!SubDecision (=) S S} x `{x ∊ S} y `{y ∊ S} : x ≤ y ∨ y < x.
  Proof.
    destruct (trichotomy (<) x y) as [|[|]]; try tauto.
     left. now apply lt_le.
    left. now apply eq_le_flip.
  Qed.

  Global Instance le_total `{!StandardUnEq A} `{!SubDecision (=) S S} : TotalOrder S.
  Proof. split; try apply _. intros x ? y ?. destruct (le_or_lt x y). tauto. right. now apply lt_le. Qed.

  Lemma not_le_lt_flip `{!StandardUnEq A} `{!SubDecision (=) S S} x `{x ∊ S} y `{y ∊ S} : ¬y ≤ x → x < y.
  Proof. intros. destruct (le_or_lt y x); intuition. Qed.

  Existing Instance dec_from_lt_dec.

  Program Definition lt_dec `{!StandardUnEq A} `{!SubDecision (≤) S S} : SubDecision (<) S S
     := λ x xs y ys,
    match decide_sub (≤) y x with
    | left E => right _
    | right E => left _
    end.
  Next Obligation. now apply le_not_lt_flip. Qed.
  Next Obligation. now apply not_le_lt_flip. Qed.
End full_pseudo_order.

Hint Extern 8 (SubDecision (<) _ _) => eapply @lt_dec : typeclass_instances.
(*
The following instances would be tempting, but turn out to be a bad idea.

Hint Extern 10 (PropHolds (_ ≠ _)) => eapply @le_ne : typeclass_instances.
Hint Extern 10 (PropHolds (_ ≠ _)) => eapply @le_ne_flip : typeclass_instances.

It will then loop like:

semirings.lt_0_1 → lt_ne_flip → ...
*)

Section dec_sub_strict_order.
  Context `{S:Subset A} `{SubStrictOrder A (S:=S)} `{UnEq A} `{!StandardUnEq A} `{∀ x y, Decision (x = y)}.

  Existing Instance so_subsetoid.
  Instance: StrongSetoid A := dec_strong_setoid.

  Context `{!Trichotomy (<) S}.

  Instance dec_strict_pseudo_order: PseudoOrder S.
  Proof. split. split; apply _.
  + intros x ? y ? [??]. destruct (lt_antisym x y); tauto.
  + intros x ? y ? Exy z ?.
     destruct (trichotomy (<) x z) as [? | [Exz | Exz]]; try tauto.
      right. now rewrite_on S <- Exz.
     right. subtransitivity x.
  + intros x ? y ?. rewrite standard_uneq. split.
     destruct (trichotomy (<) x y); intuition.
    intros [?|?]. now apply lt_ne. now apply lt_ne_flip.
  Qed.
End dec_sub_strict_order.

Section dec_partial_order.
  Context `{PartialOrder A (P:=P)} `{∀ x y, Decision (x = y)}.

  Existing Instance po_subsetoid.

  Context `{StandardUnEq A (Ae:=_)} `{Alt : Lt A}
          (lt_correct : ∀ `{x ∊ P} `{y ∊ P}, x < y ↔ x ≤ y ∧ x ≠ y).

  Instance dec_order: SubStrictOrder P.
  Proof. split; try apply _.
  + intros ? ? E1 ? ? E2. unfold_sigs.
    rewrite !lt_correct; trivial.
    rewrite_on P -> E1. now rewrite_on P -> E2.
  + intros x ?. rewrite lt_correct; trivial. rewrite standard_uneq. now intros [_ []].
  + intros x ? y ? z ?. rewrite !lt_correct; trivial.
    rewrite !standard_uneq. intros [E1a E1b] [E2a E2b].
    split. subtransitivity y.
    intros E3. destruct E2b.
    apply (subantisymmetry (≤)); trivial.
    now rewrite_on P <- E3.
  Qed.

  Instance: StrongSetoid A := dec_strong_setoid.

  Instance dec_full_partial_order: FullPartialOrder P := {}.
  Proof. apply lt_correct. Qed.

  Context `{!TotalRelation (≤) P}.

  Instance: Trichotomy (<) P.
  Proof.
    intros x ? y ?. rewrite !lt_correct; trivial. rewrite !standard_uneq.
    destruct (decide (x = y)); try tauto.
    destruct (total (≤) x y); intuition.
  Qed.

  Instance dec_pseudo_order: PseudoOrder P.
  Proof dec_strict_pseudo_order.

  Instance dec_full_pseudo_order: FullPseudoOrder P.
  Proof.
    split; try apply _.
    intros x ? y ?. rewrite lt_correct; trivial. rewrite standard_uneq. split.
     intros ? [? []]. now apply (subantisymmetry (≤)).
    intros E1.
    destruct (total (≤) x y); trivial.
    destruct (decide (x = y)) as [E2|E2].
     rewrite_on P -> E2. subreflexivity.
    intuition.
  Qed.
End dec_partial_order.
