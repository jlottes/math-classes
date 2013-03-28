Require Import
  abstract_algebra interfaces.orders orders.orders theory.strong_setoids.

Local Existing Instance order_morphism_po_a.
Local Existing Instance order_morphism_po_b.
Local Existing Instance strict_order_morphism_so_a.
Local Existing Instance strict_order_morphism_so_b.
Local Existing Instance order_morphism_mor.
Local Existing Instance strict_order_morphism_mor.

Local Existing Instance po_setoid.
Local Existing Instance so_setoid.
Local Existing Instance pseudo_order_setoid.
Local Existing Instance strict_po_setoid.

(* If a function between strict partial orders is order preserving (back), we can
  derive that it is strictly order preserving (back) *)
Section strictly_order_preserving.
  Context `{FullPartialOrder (P:=X)} `{FullPartialOrder (P:=Y)}.
  Context {f:X ⇀ Y}.

  Existing Instance strict_po_setoid.

  Global Instance strictly_order_preserving_inj `{!OrderPreserving X Y f} `{!StrongInjective X Y f} :
    StrictlyOrderPreserving X Y f | 20.
  Proof.
    repeat (split; try apply _).
    intros x ? y ?. rewrite !lt_iff_le_apart; try apply _. intros [E1 E2]. split.
     now apply (order_preserving f).
    now apply (strong_injective f).
  Qed.

  Global Instance strictly_order_reflecting_mor `{!OrderReflecting X Y f} `{!Strong_Morphism X Y f} :
    StrictlyOrderReflecting X Y f | 20.
  Proof.
    repeat (split; try apply _).
    intros x ? y ?. rewrite !lt_iff_le_apart; try apply _. intros [E1 E2]. split.
     now apply (order_reflecting f).
    now apply (strong_extensionality f).
  Qed.
End strictly_order_preserving.

(* For structures with a trivial apartness relation we have a stronger result of the above *)
Section strictly_order_preserving_dec.
  Context `{FullPartialOrder (P:=X)} `{!StandardUnEq X}
          `{FullPartialOrder (P:=Y)} `{!StandardUnEq Y}.
  Context {f:X ⇀ Y}.

  Local Existing Instance strict_po_setoid.

  Global Instance dec_strictly_order_preserving_inj  `{!OrderPreserving X Y f} `{!Injective X Y f} :
    StrictlyOrderPreserving X Y f | 19.
  Proof. pose proof (dec_strong_injective f). apply _. Qed.

  Global Instance dec_strictly_order_reflecting_mor `{!OrderReflecting X Y f} :
    StrictlyOrderReflecting X Y f | 19.
  Proof. pose proof order_morphism_mor f. pose proof (dec_strong_morphism f). apply _. Qed.
End strictly_order_preserving_dec.

Section pseudo_injective.
  Context `{PseudoOrder (S:=X)} `{PseudoOrder (S:=Y)}.
  Context {f:X ⇀ Y}.

  Local Existing Instance pseudo_order_setoid.

  Instance pseudo_order_embedding_ext `{!StrictOrderEmbedding X Y f} :
    Strong_Morphism X Y f.
  Proof.
    split; try apply _.
    intros x ? y ?. rewrite !apart_iff_total_lt; try apply _.
    intros [|]; [left | right]; now apply (strictly_order_reflecting f).
  Qed.

  Lemma pseudo_order_embedding_inj `{!StrictOrderEmbedding X Y f} :
    StrongInjective X Y f.
  Proof.
    split; try apply _.
    intros x ? y ?. rewrite !apart_iff_total_lt; try apply _.
    intros [|]; [left | right]; now apply (strictly_order_preserving f).
  Qed.

  Lemma pseudo_order_dec_preserving_inj `{!StandardUnEq X} `{!StrictlyOrderPreserving X Y f} :
    StrongInjective X Y f.
  Proof. split; [| exact (dec_strong_morphism f)]. intros ????.
    rewrite !apart_iff_total_lt; try apply _.
    intros [|]; [left | right]; now apply (strictly_order_preserving f).
  Qed.

End pseudo_injective.

(* If a function between pseudo partial orders is strictly order preserving (back), we can
  derive that it is order preserving (back) *)
Section full_pseudo_strictly_preserving.
  Context `{FullPseudoOrder (S:=X)} `{FullPseudoOrder (S:=Y)}.
  Context {f:X ⇀ Y}.

  Local Existing Instance pseudo_order_setoid.

  Lemma full_pseudo_order_preserving `{!StrictlyOrderReflecting X Y f} : OrderPreserving X Y f.
  Proof.
    pose proof strict_order_morphism_mor f.
    repeat (split; try apply _).
    intros x ? y ?. rewrite !le_iff_not_lt_flip; try apply _.
    intros E1 E2. apply E1.
    now apply (strictly_order_reflecting f).
  Qed.

  Lemma full_pseudo_order_reflecting `{!StrictlyOrderPreserving X Y f} : OrderReflecting X Y f.
  Proof.
    pose proof strict_order_morphism_mor f.
    repeat (split; try apply _).
    intros x ? y ?. rewrite !le_iff_not_lt_flip; try apply _.
    intros E1 E2. apply E1.
    now apply (strictly_order_preserving f).
  Qed.
End full_pseudo_strictly_preserving.

(* Some helper lemmas to easily transform order preserving instances. *)
Section order_preserving_ops.
  Context `{Equiv A} `{Le A} `{Lt A} `{op:R ⇀ R ⇀ R} `{!Commutative op R} `{!Morphism (R ⇒ R ⇒ R) op} `{z ∊ R}.

  Lemma order_preserving_flip `{!OrderPreserving R R (op z)} : OrderPreserving R R (λ y, op y z).
  Proof with try apply _.
    split. split... intros x ? y ? E.
    rewrite_on R -> (commutativity op x z), (commutativity op y z).
    now apply (order_preserving (op z)).
  Qed.

  Lemma strictly_order_preserving_flip `{!StrictlyOrderPreserving R R (op z)} : StrictlyOrderPreserving R R (λ y, op y z).
  Proof with try apply _.
    split. split... intros x ? y ? E.
    rewrite_on R -> (commutativity op x z), (commutativity op y z).
    now apply (strictly_order_preserving (op z)).
  Qed.

  Lemma order_reflecting_flip `{!OrderReflecting R R (op z)} : OrderReflecting R R (λ y, op y z).
  Proof with try apply _.
    split. split... intros x ? y ? E.
    apply (order_reflecting (op z) _ _).
    now rewrite_on R -> (commutativity op z x), (commutativity op z y).
  Qed.

  Lemma strictly_order_reflecting_flip `{!StrictlyOrderReflecting R R (op z)} : StrictlyOrderReflecting R R (λ y, op y z).
  Proof with try apply _.
    split. split... intros x ? y ? E.
    apply (strictly_order_reflecting (op z) _ _).
    now rewrite_on R -> (commutativity op z x), (commutativity op z y).
  Qed.

End order_preserving_ops.

Lemma projected_partial_order `{Equiv A} `{Le A} `{Equiv B} `{Le B} {P1:@Subset A} {P2:@Subset B}
  `{!Setoid P1} (f:P1 ⇀ P2) `{!Injective P1 P2 f} `{!PartialOrder P2}
  : (∀ `{x ∊ P1} `{y ∊ P1}, x ≤ y ↔ f x ≤ f y) → PartialOrder P1.
Proof.
  pose proof (injective_mor f).
  intros P. split. apply _.
  + intros ?? E1 ?? E2. unfold_sigs. rewrite !(P _ _ _ _).
    intro. now rewrite_on P1 <- E1, <- E2.
  + intros x ?. now apply (P _ _ _ _).
  + intros x ? y ? z ? E1 E2. apply (P _ _ _ _).
    subtransitivity (f y); now apply (P _ _ _ _).
  + intros x ? y ? E1 E2. apply (injective f _ _).
    apply (subantisymmetry (≤) _ _); now apply (P _ _ _ _).
Qed.

Local Existing Instance closed_range.

Lemma projected_total_relation `{Equiv A} `{Le A} `{Equiv B} `{Le B} {S1:@Subset A} {S2:@Subset B}
  (f:S1 ⇀ S2) `{!Closed (S1 ⇀ S2) f} `{!TotalRelation S2 (≤)}
  : (∀ `{x ∊ S1} `{y ∊ S1}, x ≤ y ↔ f x ≤ f y) → TotalRelation S1 (≤).
Proof.
  intros P x ? y ?.
  destruct (total (≤) (f x) (f y)); [left | right]; now apply P.
Qed.

Lemma projected_total_order `{Equiv A} `{Le A} `{Equiv B} `{Le B} {S1:@Subset A} {S2:@Subset B}
  `{!Setoid S1} (f:S1 ⇀ S2) `{!Injective S1 S2 f} `{!TotalOrder S2}
  : (∀ `{x ∊ S1} `{y ∊ S1}, x ≤ y ↔ f x ≤ f y) → TotalOrder S1.
Proof. intro. split. now apply (projected_partial_order f).
  pose proof injective_mor f. now apply (projected_total_relation f).
Qed.

Lemma projected_strict_order `{Equiv A} `{Lt A} `{Equiv B} `{Lt B} {S1:@Subset A} {S2:@Subset B}
  `{!Setoid S1} (f:S1 ⇀ S2) `{!Morphism (S1 ⇒ S2) f} `{!StrictSetoidOrder S2}
  : (∀ `{x ∊ S1} `{y ∊ S1}, x < y ↔ f x < f y) → StrictSetoidOrder S1.
Proof. intros P. split. apply _.
  + intros ?? E1 ?? E2. unfold_sigs. rewrite 2!(P _ _ _ _).
    intro. now rewrite_on S1 <- E1, <- E2.
  + intros x ? E. destruct (subirreflexivity (<) (f x)). now apply P.
  + intros x ? y ? z ? E1 E2. apply (P _ _ _ _).
    subtransitivity (f y); now apply P.
Qed.

Lemma projected_pseudo_order `{Equiv A} `{UnEq A} `{Lt A} `{Equiv B} `{UnEq B} `{Lt B} {S1:@Subset A} {S2:@Subset B}
  `{!StrongSetoid S1} (f:S1 ⇀ S2) `{!StrongInjective S1 S2 f} `{!PseudoOrder S2}
  : (∀ `{x ∊ S1} `{y ∊ S1}, x < y ↔ f x < f y) → PseudoOrder S1.
Proof.
  pose proof strong_injective_mor f.
  intro P. split. apply _.
  + intros x ? y ? [??]. destruct (pseudo_order_antisym (f x) (f y)). split; now apply P.
  + intros x ? y ? E z ?. apply (P _ _ _ _) in E.
    destruct (subcotransitivity E (f z)); [left | right]; now apply P.
  + intros x ? y ?. split; intro E.
    * apply (strong_injective f _ _) in E.
      apply (apart_iff_total_lt _ _) in E. destruct E; [left | right]; now apply P.
    * apply (strong_extensionality f).
      apply (apart_iff_total_lt _ _). destruct E; [left | right]; now apply P.
Qed.

Lemma projected_full_pseudo_order 
  `{Equiv A} `{UnEq A} `{Le A} `{Lt A}
  `{Equiv B} `{UnEq B} `{Le B} `{Lt B}
  {S1:@Subset A} {S2:@Subset B} `{!StrongSetoid S1}
  (f:S1 ⇀ S2) `{!StrongInjective S1 S2 f} `{!FullPseudoOrder S2}
  : (∀ `{x ∊ S1} `{y ∊ S1}, x ≤ y ↔ f x ≤ f y)
  → (∀ `{x ∊ S1} `{y ∊ S1}, x < y ↔ f x < f y)
  → FullPseudoOrder S1.
Proof.
  pose proof strong_injective_mor f.
  intros P1 P2. split.
   now apply (projected_pseudo_order f).
  intros x ? y ?; split; intros E.
   intros F. destruct (le_not_lt_flip (f y) (f x)); [apply P1 | apply P2]; trivial.
  apply P1; trivial. apply (not_lt_le_flip _ _). contradict E. now apply P2.
Qed.

Lemma id_order_embedding `{PartialOrder (P:=P2)} {P1} `{!SubsetOf P1 P2} : OrderEmbedding P1 P2 id.
Proof. split; (split; [|easy]); split; try apply _; rewrite (_ : SubsetOf P1 P2); apply _. Qed.
Hint Extern 2 (OrderEmbedding _ _ id) => class_apply @id_order_embedding : typeclass_instances.

Section composition.
  Context `{Equiv A} `{Equiv B} `{Equiv C} `{Le A} `{Le B} `{Le C} `{X:@Subset A} `{Y:@Subset B} `{Z:@Subset C}.
  Context (f : X ⇀ Y) (g : Y ⇀ Z).

  Instance compose_order_morphism:
    Order_Morphism X Y f → Order_Morphism Y Z g → Order_Morphism X Z (g ∘ f).
  Proof. split; [ apply _ | apply (order_morphism_po_a _ _ f) | apply (order_morphism_po_b _ _ g) ]. Qed.

  Instance compose_order_preserving:
    OrderPreserving X Y f → OrderPreserving Y Z g → OrderPreserving X Z (g ∘ f).
  Proof.
    repeat (split; try apply _).
    intros. unfold compose.
    now do 2 (apply (order_preserving _); try apply _).
  Qed.

  Instance compose_order_reflecting:
    OrderReflecting X Y f → OrderReflecting Y Z g → OrderReflecting X Z (g ∘ f).
  Proof.
    split; try apply _.
    intros x ? y ? E. unfold compose in E.
    do 2 apply (order_reflecting _) in E; trivial; apply _.
  Qed.

  Instance compose_order_embedding:
    OrderEmbedding X Y f → OrderEmbedding Y Z g → OrderEmbedding X Z (g ∘ f) := {}.
End composition.

Hint Extern 4 (Order_Morphism  _ _ (_ ∘ _)) => class_apply @compose_order_morphism   : typeclass_instances.
Hint Extern 4 (OrderPreserving _ _ (_ ∘ _)) => class_apply @compose_order_preserving : typeclass_instances.
Hint Extern 4 (OrderReflecting _ _ (_ ∘ _)) => class_apply @compose_order_reflecting : typeclass_instances.
Hint Extern 4 (OrderEmbedding  _ _ (_ ∘ _)) => class_apply @compose_order_embedding  : typeclass_instances.

Lemma order_morphism_proper: Find_Proper_Signature (@Order_Morphism) 0
  (∀ A B Ae Ale Be Ble S T, Proper ((@equiv (S ⇀ T) _) ==> impl)
   (@Order_Morphism A B Ae Ale Be Ble S T)).
Proof. red; intros. intros f g E ?. split; try apply _; rewrite <- E; apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@Order_Morphism) 0 _) => eexact order_morphism_proper : typeclass_instances.

Lemma order_preserving_proper: Find_Proper_Signature (@OrderPreserving) 0
  (∀ A B Ae Ale Be Ble S T, Proper ((@equiv (S ⇀ T) _) ==> impl)
   (@OrderPreserving A B Ae Ale Be Ble S T)).
Proof. red; intros. intros f g E ?. split; try apply _. rewrite <- E; apply _.
  assert (Morphism (S ⇒ T) g) by (rewrite <-E; apply _).
  intros x ? y ? ?. 
  rewrite <-(E _ _ (_ : Proper (S,=) x)).
  rewrite <-(E _ _ (_ : Proper (S,=) y)).
  now apply (order_preserving f _ _).
Qed.
Hint Extern 0 (Find_Proper_Signature (@OrderPreserving) 0 _) => eexact order_preserving_proper : typeclass_instances.

Lemma order_reflecting_proper: Find_Proper_Signature (@OrderReflecting) 0
  (∀ A B Ae Ale Be Ble S T, Proper ((@equiv (S ⇀ T) _) ==> impl)
   (@OrderReflecting A B Ae Ale Be Ble S T)).
Proof. red; intros. intros f g E ?. split; try apply _. rewrite <- E; apply _.
  assert (Morphism (S ⇒ T) g) by (rewrite <-E; apply _).
  intros x ? y ? E2. 
  rewrite <-(E _ _ (_ : Proper (S,=) x)) in E2.
  rewrite <-(E _ _ (_ : Proper (S,=) y)) in E2.
  now apply (order_reflecting f _ _).
Qed.
Hint Extern 0 (Find_Proper_Signature (@OrderReflecting) 0 _) => eexact order_reflecting_proper : typeclass_instances.

Lemma order_embedding_proper: Find_Proper_Signature (@OrderEmbedding) 0
  (∀ A B Ae Ale Be Ble S T, Proper ((@equiv (S ⇀ T) _) ==> impl)
   (@OrderEmbedding A B Ae Ale Be Ble S T)).
Proof. red; intros. intros f g E ?. split; rewrite <- E; apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@OrderEmbedding) 0 _) => eexact order_embedding_proper : typeclass_instances.


(*
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
*)

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
