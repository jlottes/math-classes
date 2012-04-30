Require Import
  abstract_algebra interfaces.orders orders.orders
  theory.subsetoids theory.sub_strong_setoids.

Local Existing Instance order_morphism_po_a.
Local Existing Instance order_morphism_po_b.
Local Existing Instance strict_order_morphism_so_a.
Local Existing Instance strict_order_morphism_so_b.
Local Existing Instance order_morphism_mor.
Local Existing Instance strict_order_morphism_mor.

(* If a function between strict partial orders is order preserving (back), we can
  derive that it is strictly order preserving (back) *)
Section strictly_order_preserving.
  Context `{FullPartialOrder (P:=X)} `{FullPartialOrder (P:=Y)}.

  Existing Instance strict_po_setoid.

  Global Instance strictly_order_preserving_inj  `{!OrderPreserving f X Y} `{!StrongInjective f X Y} :
    StrictlyOrderPreserving f X Y | 20.
  Proof.
    repeat (split; try apply _).
    intros x ? y ?. rewrite !lt_iff_le_apart; try apply _. intros [E1 E2]. split.
     now apply (order_preserving f).
    now apply (strong_injective f).
  Qed.

  Global Instance strictly_order_reflecting_mor `{!OrderReflecting f X Y} `{!SubStrongSetoid_Morphism f X Y} :
    StrictlyOrderReflecting f X Y | 20.
  Proof.
    repeat (split; try apply _).
    intros x ? y ?. rewrite !lt_iff_le_apart; try apply _. intros [E1 E2]. split.
     now apply (order_reflecting f).
    now apply (strong_extensionality f).
  Qed.
End strictly_order_preserving.

(* For structures with a trivial apartness relation we have a stronger result of the above *)
Section strictly_order_preserving_dec.
  Context `{FullPartialOrder A (P:=X)} `{!StandardUnEq A}
          `{FullPartialOrder B (P:=Y)} `{!StandardUnEq B}.

  Local Existing Instance strict_po_setoid.

  Global Instance dec_strictly_order_preserving_inj  `{!OrderPreserving f X Y} `{!Injective f X Y} :
    StrictlyOrderPreserving f X Y | 19.
  Proof. pose proof (dec_strong_injective f X Y). apply _. Qed.

  Global Instance dec_strictly_order_reflecting_mor `{!OrderReflecting f X Y} :
    StrictlyOrderReflecting f X Y | 19.
  Proof. pose proof (order_morphism_mor f). pose proof (dec_strong_morphism f X Y). apply _. Qed.
End strictly_order_preserving_dec.

Section pseudo_injective.
  Context `{PseudoOrder (S:=X)} `{PseudoOrder (S:=Y)}.

  Local Existing Instance pseudo_order_setoid.

  Instance pseudo_order_embedding_ext `{!StrictOrderEmbedding f X Y} :
    SubStrongSetoid_Morphism f X Y.
  Proof.
    split; try apply _.
    intros x ? y ?. rewrite !apart_iff_total_lt; try apply _.
    intros [|]; [left | right]; now apply (strictly_order_reflecting f).
  Qed.

  Lemma pseudo_order_embedding_inj `{!StrictOrderEmbedding f X Y} :
    StrongInjective f X Y.
  Proof.
    split; try apply _.
    intros x ? y ?. rewrite !apart_iff_total_lt; try apply _.
    intros [|]; [left | right]; now apply (strictly_order_preserving f).
  Qed.
End pseudo_injective.

(* If a function between pseudo partial orders is strictly order preserving (back), we can
  derive that it is order preserving (back) *)
Section full_pseudo_strictly_preserving.
  Context `{FullPseudoOrder (S:=X)} `{FullPseudoOrder (S:=Y)}.

  Local Existing Instance pseudo_order_setoid.

  Lemma full_pseudo_order_preserving `{!StrictlyOrderReflecting f X Y} : OrderPreserving f X Y.
  Proof.
    pose proof (strict_order_morphism_mor f).
    repeat (split; try apply _).
    intros x ? y ?. rewrite !le_iff_not_lt_flip; try apply _.
    intros E1 E2. apply E1.
    now apply (strictly_order_reflecting f).
  Qed.

  Lemma full_pseudo_order_reflecting `{!StrictlyOrderPreserving f X Y} : OrderReflecting f X Y.
  Proof.
    pose proof (strict_order_morphism_mor f).
    repeat (split; try apply _).
    intros x ? y ?. rewrite !le_iff_not_lt_flip; try apply _.
    intros E1 E2. apply E1.
    now apply (strictly_order_preserving f).
  Qed.
End full_pseudo_strictly_preserving.

(* Some helper lemmas to easily transform order preserving instances. *)
Section order_preserving_ops.
  Context `{Equiv A} `{Le A} `{Lt A}.

  Lemma order_preserving_flip `{!Commutative op R} `{!SubProper ((R,=) ==> (R,=) ==> (R,=)) op} `{z ∊ R} `{!OrderPreserving (op z) R R} :
    OrderPreserving (λ y, op y z) R R.
  Proof with try apply _.
    pose proof (order_morphism_mor (op z)).
    pose proof (subsetoidmor_s (op z)).
    split. split... split... intros ?? E. unfold_sigs. red_sig.
      now rewrite_on R -> E.
    intros x ? y ? E.
    rewrite_on R -> (commutativity x z).
    rewrite_on R -> (commutativity y z).
    now apply (order_preserving (op z)).
  Qed.

  Lemma strictly_order_preserving_flip `{!Commutative op R} `{!SubProper ((R,=) ==> (R,=) ==> (R,=)) op} `{z ∊ R} `{!StrictlyOrderPreserving (op z) R R} :
    StrictlyOrderPreserving (λ y, op y z) R R.
  Proof with try apply _.
    pose proof (strict_order_morphism_mor (op z)).
    pose proof (subsetoidmor_s (op z)).
    split. split... split... intros ?? E. unfold_sigs. red_sig.
      now rewrite_on R -> E.
    intros x ? y ? E.
    rewrite_on R -> (commutativity x z).
    rewrite_on R -> (commutativity y z).
    now apply (strictly_order_preserving (op z)).
  Qed.

  Lemma order_reflecting_flip `{!Commutative op R} `{!SubProper ((R,=) ==> (R,=) ==> (R,=)) op} `{z ∊ R} `{!OrderReflecting (op z) R R} :
    OrderReflecting (λ y, op y z) R R.
  Proof with try apply _.
    pose proof (order_morphism_mor (op z)).
    pose proof (subsetoidmor_s (op z)).
    split. split... split... intros ?? E. unfold_sigs. red_sig.
      now rewrite_on R -> E.
    intros x ? y ? E.
    apply (order_reflecting (op z)); trivial.
    rewrite_on R -> (commutativity z x).
    now rewrite_on R -> (commutativity z y).
  Qed.

  Lemma strictly_order_reflecting_flip `{!Commutative op R} `{!SubProper ((R,=) ==> (R,=) ==> (R,=)) op} `{z ∊ R} `{!StrictlyOrderReflecting (op z) R R} :
    StrictlyOrderReflecting (λ y, op y z) R R.
  Proof with try apply _.
    pose proof (strict_order_morphism_mor (op z)).
    pose proof (subsetoidmor_s (op z)).
    split. split... split... intros ?? E. unfold_sigs. red_sig.
      now rewrite_on R -> E.
    intros x ? y ? E.
    apply (strictly_order_reflecting (op z)); trivial.
    rewrite_on R -> (commutativity z x).
    now rewrite_on R -> (commutativity z y).
  Qed.

(*
  Context (op:A → A → A) `{Zero A}.

  Lemma order_preserving_nonneg `{∀ `{z ∊ R⁺}, OrderPreserving (op z) R R} z `{z ∊ R⁺}
    x `{x ∊ R} y `{y ∊ R} : x ≤ y → op z x ≤ op z y.
  Proof. firstorder. Qed.

  Lemma order_preserving_flip_nonneg `{∀ `{z ∊ R⁺}, OrderPreserving (λ y, op y z) R R} z `{z ∊ R⁺}
    x `{x ∊ R} y `{y ∊ R} : x ≤ y → op x z ≤ op y z.
  Proof. firstorder. Qed.

  Lemma strictly_order_preserving_pos `{∀ `{z ∊ R₊}, StrictlyOrderPreserving (op z) R R} z `{z ∊ R₊}
    x `{x ∊ R} y `{y ∊ R} : x < y → op z x < op z y.
  Proof. firstorder. Qed.

  Lemma strictly_order_preserving_flip_pos `{∀ `{z ∊ R₊}, StrictlyOrderPreserving (λ y, op y z) R R} z `{z ∊ R₊}
    x `{x ∊ R} y `{y ∊ R} : x < y → op x z < op y z.
  Proof. firstorder. Qed.

  Lemma order_reflecting_pos `{∀ `{z ∊ R₊}, OrderReflecting (op z) R R} z `{z ∊ R₊}
    x `{x ∊ R} y `{y ∊ R} : op z x ≤ op z y → x ≤ y.
  Proof. firstorder. Qed.

  Lemma order_reflecting_flip_pos `{∀ `{z ∊ R₊}, OrderReflecting (λ y, op y z) R R} z `{z ∊ R₊}
    x `{x ∊ R} y `{y ∊ R} : op x z ≤ op y z → x ≤ y.
  Proof. firstorder. Qed.
*)

End order_preserving_ops.

(*
Lemma projected_partial_order `{Equiv A} `{Ale : Le A} `{Equiv B} `{Ble : Le B}
  (f : A → B) `{!Injective f} `{!PartialOrder Ble} : (∀ x y, x ≤ y ↔ f x ≤ f y) → PartialOrder Ale.
Proof.
  pose proof (injective_mor f).
  pose proof (setoidmor_a f).
  pose proof (setoidmor_b f).
  intros P. split; try apply _.
    intros ? ? E1 ? ? E2. now rewrite 2!P, E1, E2.
   split.
    intros x. now apply P.
   intros x y z E1 E2. apply P.
   transitivity (f y); now apply P.
  intros x y E1 E2. apply (injective f).
  apply (antisymmetry (≤)); now apply P.
Qed.

Lemma projected_total_order `{Equiv A} `{Ale : Le A} `{Equiv B} `{Ble : Le B}
  (f : A → B) `{!TotalRelation Ble} : (∀ x y, x ≤ y ↔ f x ≤ f y) → TotalRelation Ale.
Proof.
  intros P x y.
  destruct (total (≤) (f x) (f y)); [left | right]; now apply P.
Qed.

Lemma projected_strict_order `{Equiv A} `{Alt : Lt A} `{Equiv B} `{Blt : Lt B}
  (f : A → B) `{!StrictOrder Blt} : (∀ x y, x < y ↔ f x < f y) → StrictOrder Alt.
Proof.
  intros P. split.
   intros x E. destruct (irreflexivity (<) (f x)). now apply P.
  intros x y z E1 E2. apply P. transitivity (f y); now apply P.
Qed.

Lemma projected_strict_setoid_order `{Equiv A} `{Alt : Lt A} `{Equiv B} `{Blt : Lt B}
  (f : A → B) `{!Setoid_Morphism f} `{!StrictSetoidOrder Blt} : (∀ x y, x < y ↔ f x < f y) → StrictSetoidOrder Alt.
Proof.
  pose proof (setoidmor_a f).
  intros P. split; try apply _.
   intros ? ? E1 ? ? E2. now rewrite 2!P, E1, E2.
  now apply (projected_strict_order f).
Qed.

Lemma projected_pseudo_order `{Equiv A} `{Apart A} `{Alt : Lt A} `{Equiv B} `{Apart B} `{Blt : Lt B}
  (f : A → B) `{!StrongInjective f} `{!PseudoOrder Blt} : (∀ x y, x < y ↔ f x < f y) → PseudoOrder Alt.
Proof.
  pose proof (strong_injective_mor f).
  pose proof (strong_setoidmor_a f).
  pose proof (strong_setoidmor_b f).
  intros P. split; try apply _.
    intros x y E. destruct (pseudo_order_antisym (f x) (f y)). split; now apply P.
   intros x y E z. apply P in E.
   destruct (cotransitive E (f z)); [left | right]; now apply P.
  intros x y; split; intros E.
   apply (strong_injective f) in E.
   apply apart_iff_total_lt in E. destruct E; [left | right]; now apply P.
  apply (strong_extensionality f).
  apply apart_iff_total_lt. destruct E; [left | right]; now apply P.
Qed.

Lemma projected_full_pseudo_order `{Equiv A} `{Apart A} `{Ale : Le A} `{Alt : Lt A}
  `{Equiv B} `{Apart B} `{Ble : Le B} `{Blt : Lt B}
  (f : A → B) `{!StrongInjective f} `{!FullPseudoOrder Ble Blt} : (∀ x y, x ≤ y ↔ f x ≤ f y) → (∀ x y, x < y ↔ f x < f y) → FullPseudoOrder Ale Alt.
Proof.
  intros P1 P2. split.
   now apply (projected_pseudo_order f).
  intros x y; split; intros E.
   intros F. destruct (le_not_lt_flip (f y) (f x)); firstorder.
  apply P1. apply not_lt_le_flip.
  intros F. destruct E. now apply P2.
Qed.

Instance id_order_morphism `{PartialOrder A} : Order_Morphism (@id A).
Proof. pose proof po_setoid. repeat (split; try apply _). Qed.

Instance id_order_preserving `{PartialOrder A} : OrderPreserving (@id A).
Proof. split; try apply _. easy. Qed.

Instance id_order_reflecting `{PartialOrder A} : OrderReflecting (@id A).
Proof. split; try apply _. easy. Qed.
*)

Section composition.
  Context `{Equiv A} `{Equiv B} `{Equiv C}
    `{Le A} `{Le B} `{Le C} (f : A → B) (g : B → C)
    `{X:Subset A} `{Y:Subset B} `{Z:Subset C}.

  Existing Instance order_morphism_mor.
  Existing Instance po_subsetoid.

  Instance compose_order_morphism:
    Order_Morphism f X Y → Order_Morphism g Y Z → Order_Morphism (g ∘ f) X Z.
  Proof. split; [ apply _ | apply (order_morphism_po_a f) | apply (order_morphism_po_b g) ]. Qed.

  Instance compose_order_preserving:
    OrderPreserving f X Y → OrderPreserving g Y Z → OrderPreserving (g ∘ f) X Z.
  Proof.
    repeat (split; try apply _).
    intros. unfold compose.
    now do 2 (apply (order_preserving _); try apply _).
  Qed.

  Instance compose_order_reflecting:
    OrderReflecting f X Y → OrderReflecting g Y Z → OrderReflecting (g ∘ f) X Z.
  Proof.
    split; try apply _.
    intros x ? y ? E. unfold compose in E.
    do 2 apply (order_reflecting _) in E; trivial; apply _.
  Qed.

  Instance compose_order_embedding:
    OrderEmbedding f X Y → OrderEmbedding g Y Z → OrderEmbedding (g ∘ f) X Z := {}.
End composition.

Hint Extern 4 (Order_Morphism  (_ ∘ _) _ _) => class_apply @compose_order_morphism   : typeclass_instances.
Hint Extern 4 (OrderPreserving (_ ∘ _) _ _) => class_apply @compose_order_preserving : typeclass_instances.
Hint Extern 4 (OrderReflecting (_ ∘ _) _ _) => class_apply @compose_order_reflecting : typeclass_instances.
Hint Extern 4 (OrderEmbedding  (_ ∘ _) _ _) => class_apply @compose_order_embedding  : typeclass_instances.

Lemma partialorder_refl_eq  `{PartialOrder (P:=P)} : Proper (PartialOrder,=) P. Proof. apply restrict_rel_refl; apply _. Qed.
Lemma partialorder_refl_sub `{PartialOrder (P:=P)} : Proper (PartialOrder,⊆) P. Proof. apply restrict_rel_refl; apply _. Qed.

Hint Extern 0 (@Proper _ (@restrict_rel _ PartialOrder (@equiv _ (subset_equiv _))) _)  => eapply @partialorder_refl_eq  : typeclass_instances.
Hint Extern 0 (@Proper _ (@restrict_rel _ PartialOrder (@SubsetOf _)) _)                => eapply @partialorder_refl_sub : typeclass_instances.

Definition partialorder_refl_eq_fp  `{PartialOrder (P:=P)} : Find_Proper_Proper (PartialOrder,=) P := partialorder_refl_eq.
Definition partialorder_refl_sub_fp `{PartialOrder (P:=P)} : Find_Proper_Proper (PartialOrder,⊆) P := partialorder_refl_sub.

Hint Extern 0 (@Find_Proper_Proper _ (@restrict_rel _ PartialOrder (@equiv _ (subset_equiv _))) _) => eapply @partialorder_refl_eq_fp  : typeclass_instances.
Hint Extern 0 (@Find_Proper_Proper _ (@restrict_rel _ PartialOrder (@SubsetOf _)) _)               => eapply @partialorder_refl_sub_fp : typeclass_instances.

Lemma to_partialorder_rel `{PartialOrder (P:=X)} `{!PartialOrder Y} {R:relation _} (E:R X Y)
  : (PartialOrder,R)%signature X Y.
Proof. split. split; assumption. exact E. Qed.


Lemma Order_Morphism_proper: Find_Proper_Signature (@Order_Morphism) 0
  (∀ A B Ae Ale Be Ble f, Proper ((ProperSubset,⊆)-->(PartialOrder,⊆)++>impl) (@Order_Morphism A B Ae Ale Be Ble f)).
Proof. red. intros. intros S1 S2 [[??]ES] T1 T2 [[??]ET] [???].
  pose proof (po_subsetoid (P:=T1)). pose proof (po_subsetoid (P:=T2)).
  split; [rewrite_subset ES; rewrite_subset <- ET | rewrite_subset ES |]; apply _.
Qed.
Hint Extern 0 (Find_Proper_Signature (@Order_Morphism ) 0 _) => eexact Order_Morphism_proper : typeclass_instances.

Lemma Order_Morphism_proper2: Find_Proper_Signature (@Order_Morphism) 1
  (∀ A B Ae Ale Be Ble f, Proper ((=)==>(=)==>impl) (@Order_Morphism A B Ae Ale Be Ble f)).
Proof. red. intros. intros S1 S2 ES T1 T2 ET ?.
  pose proof (po_subsetoid (P:=S1)). assert (SubSetoid S2) by (rewrite <- ES; apply _).
  pose proof (order_morphism_po_b f). assert (PartialOrder T2) by (rewrite <- ET; apply _).
  rewrite_subset <- ES. now rewrite <- (to_partialorder_rel ET).
Qed.
Hint Extern 0 (Find_Proper_Signature (@Order_Morphism ) 1 _) => eexact Order_Morphism_proper2 : typeclass_instances.


(*
Section propers.
  Context `{Equiv A} `{Equiv B} `{Le A} `{Le B}.

  Global Instance order_morphism_proper: Proper ((=) ==> iff) (@Order_Morphism A B _ _ _ _).
  Proof.
    assert (∀ (f g : A → B), g = f → Order_Morphism f → Order_Morphism g) as P.
     intros f g E [[? ? ?] ?].
     split; auto. apply morphism_proper with f. easy. split; easy.
    firstorder.
  Qed.

  Global Instance order_preserving_proper: Proper ((=) ==> iff) (@OrderPreserving A B _ _ _ _).
  Proof.
    assert (∀ (f g : A → B), g = f → OrderPreserving f → OrderPreserving g) as P.
     intros f g E [[[? ?] ? ?] ?].
     split.
      eapply order_morphism_proper; eauto. now repeat (split; try apply _).
     intros x y ?. rewrite (E x x), (E y y); now auto.
    firstorder.
  Qed.

  Global Instance order_reflecting_proper: Proper ((=) ==> iff) (@OrderReflecting A B _ _ _ _).
  Proof.
    assert (∀ (f g : A → B), g = f → OrderReflecting f → OrderReflecting g) as P.
     intros f g E [[[? ?] ? ?] ?].
     split.
      eapply order_morphism_proper; eauto. now repeat (split; try apply _).
     intros x y F. rewrite (E x x), (E y y) in F; now auto.
    firstorder.
  Qed.

  Global Instance order_embedding_proper: Proper ((=) ==> iff) (@OrderEmbedding A B _ _ _ _).
  Proof.
    assert (∀ (f g : A → B), g = f → OrderEmbedding f → OrderEmbedding g) as P.
     intros f g E.
     split.
      eapply order_preserving_proper; eauto. now apply _.
     eapply order_reflecting_proper; eauto. now apply _.
    intros f g ?; split; intro E.
     apply P with f. destruct E as [[[[? ?]]]]. now symmetry. easy.
    now apply P with g.
  Qed.
End propers.
*)
