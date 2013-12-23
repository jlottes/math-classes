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
  Context `{FullPartialOrder (P:=X)} `{!DenialInequality X}
          `{FullPartialOrder (P:=Y)} `{!DenialInequality Y}.
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

  Lemma pseudo_order_dec_preserving_inj `{!DenialInequality X} `{!StrictlyOrderPreserving X Y f} :
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

Lemma projected_partial_order `{Equiv A} `{Le A} `{Equiv B} `{Le B} {P1:@set A} {P2:@set B}
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
    apply (antisymmetry (≤) _ _); now apply (P _ _ _ _).
Qed.

Local Existing Instance closed_range.

Lemma projected_total_relation `{Equiv A} `{Le A} `{Equiv B} `{Le B} {S1:@set A} {S2:@set B}
  (f:S1 ⇀ S2) `{!Closed (S1 ⇀ S2) f} `{!TotalRelation S2 (≤)}
  : (∀ `{x ∊ S1} `{y ∊ S1}, x ≤ y ↔ f x ≤ f y) → TotalRelation S1 (≤).
Proof.
  intros P x ? y ?.
  destruct (total (≤) (f x) (f y)); [left | right]; now apply P.
Qed.

Lemma projected_total_order `{Equiv A} `{Le A} `{Equiv B} `{Le B} {S1:@set A} {S2:@set B}
  `{!Setoid S1} (f:S1 ⇀ S2) `{!Injective S1 S2 f} `{!TotalOrder S2}
  : (∀ `{x ∊ S1} `{y ∊ S1}, x ≤ y ↔ f x ≤ f y) → TotalOrder S1.
Proof. intro. split. now apply (projected_partial_order f).
  pose proof injective_mor f. now apply (projected_total_relation f).
Qed.

Lemma projected_strict_order `{Equiv A} `{Lt A} `{Equiv B} `{Lt B} {S1:@set A} {S2:@set B}
  `{!Setoid S1} (f:S1 ⇀ S2) `{!Morphism (S1 ⇒ S2) f} `{!StrictSetoidOrder S2}
  : (∀ `{x ∊ S1} `{y ∊ S1}, x < y ↔ f x < f y) → StrictSetoidOrder S1.
Proof. intros P. split. apply _.
  + intros ?? E1 ?? E2. unfold_sigs. rewrite 2!(P _ _ _ _).
    intro. now rewrite_on S1 <- E1, <- E2.
  + intros x ? E. destruct (irreflexivity (<) (f x)). now apply P.
  + intros x ? y ? z ? E1 E2. apply (P _ _ _ _).
    subtransitivity (f y); now apply P.
Qed.

Lemma projected_pseudo_order `{Equiv A} `{UnEq A} `{Lt A} `{Equiv B} `{UnEq B} `{Lt B} {S1:@set A} {S2:@set B}
  `{!StrongSetoid S1} (f:S1 ⇀ S2) `{!StrongInjective S1 S2 f} `{!PseudoOrder S2}
  : (∀ `{x ∊ S1} `{y ∊ S1}, x < y ↔ f x < f y) → PseudoOrder S1.
Proof.
  pose proof strong_injective_mor f.
  intro P. split. apply _.
  + intros x ? y ? [??]. destruct (pseudo_order_antisym (f x) (f y)). split; now apply P.
  + intros x ? y ? E z ?. apply (P _ _ _ _) in E.
    destruct (cotransitivity E (f z)); [left | right]; now apply P.
  + intros x ? y ?. split; intro E.
    * apply (strong_injective f _ _) in E.
      apply (apart_iff_total_lt _ _) in E. destruct E; [left | right]; now apply P.
    * apply (strong_extensionality f).
      apply (apart_iff_total_lt _ _). destruct E; [left | right]; now apply P.
Qed.

Lemma projected_full_pseudo_order 
  `{Equiv A} `{UnEq A} `{Le A} `{Lt A}
  `{Equiv B} `{UnEq B} `{Le B} `{Lt B}
  {S1:@set A} {S2:@set B} `{!StrongSetoid S1}
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

Lemma id_order_embedding `{PartialOrder (P:=P2)} {P1} `{!Subset P1 P2} : OrderEmbedding P1 P2 id.
Proof. split; (split; [|easy]); split; try apply _; rewrite (_ : Subset P1 P2); apply _. Qed.
Hint Extern 2 (OrderEmbedding _ _ id) => class_apply @id_order_embedding : typeclass_instances.

Lemma id_strict_order_embedding `{StrictSetoidOrder (S:=S2)} {S1} `{!Subset S1 S2} : StrictOrderEmbedding S1 S2 id.
Proof. split; (split; [|easy]); split; try apply _; rewrite (_ : Subset S1 S2); apply _. Qed.
Hint Extern 2 (StrictOrderEmbedding _ _ id) => class_apply @id_strict_order_embedding : typeclass_instances.

Section composition.
  Context `{Equiv A} `{Equiv B} `{Equiv C} `{Le A} `{Le B} `{Le C} `{X:@set A} `{Y:@set B} `{Z:@set C}.
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

Section composition_strict.
  Context `{Equiv A} `{Equiv B} `{Equiv C} `{Lt A} `{Lt B} `{Lt C} `{X:@set A} `{Y:@set B} `{Z:@set C}.
  Context (f : X ⇀ Y) (g : Y ⇀ Z).

  Instance compose_strict_order_morphism:
    StrictOrder_Morphism X Y f → StrictOrder_Morphism Y Z g → StrictOrder_Morphism X Z (g ∘ f).
  Proof. split; [ apply _ | apply (strict_order_morphism_so_a _ _ f) | apply (strict_order_morphism_so_b _ _ g) ]. Qed.

  Instance compose_strictly_order_preserving:
    StrictlyOrderPreserving X Y f → StrictlyOrderPreserving Y Z g → StrictlyOrderPreserving X Z (g ∘ f).
  Proof.
    repeat (split; try apply _).
    intros. unfold compose.
    now do 2 (apply (strictly_order_preserving _); try apply _).
  Qed.

  Instance compose_strictly_order_reflecting:
    StrictlyOrderReflecting X Y f → StrictlyOrderReflecting Y Z g → StrictlyOrderReflecting X Z (g ∘ f).
  Proof.
    split; try apply _.
    intros x ? y ? E. unfold compose in E.
    do 2 apply (strictly_order_reflecting _) in E; trivial; apply _.
  Qed.

  Instance compose_strict_order_embedding:
    StrictOrderEmbedding X Y f → StrictOrderEmbedding Y Z g → StrictOrderEmbedding X Z (g ∘ f) := {}.
End composition_strict.

Hint Extern 4 (StrictOrder_Morphism    _ _ (_ ∘ _)) => class_apply @compose_strict_order_morphism     : typeclass_instances.
Hint Extern 4 (StrictlyOrderPreserving _ _ (_ ∘ _)) => class_apply @compose_strictly_order_preserving : typeclass_instances.
Hint Extern 4 (StrictlyOrderReflecting _ _ (_ ∘ _)) => class_apply @compose_strictly_order_reflecting : typeclass_instances.
Hint Extern 4 (StrictOrderEmbedding    _ _ (_ ∘ _)) => class_apply @compose_strict_order_embedding    : typeclass_instances.

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


Lemma strict_order_morphism_proper: Find_Proper_Signature (@StrictOrder_Morphism) 0
  (∀ A B Ae Ale Be Ble S T, Proper ((@equiv (S ⇀ T) _) ==> impl)
   (@StrictOrder_Morphism A B Ae Ale Be Ble S T)).
Proof. red; intros. intros f g E ?. split; try apply _; rewrite <- E; apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@StrictOrder_Morphism) 0 _) => eexact strict_order_morphism_proper : typeclass_instances.

Lemma strictly_order_preserving_proper: Find_Proper_Signature (@StrictlyOrderPreserving) 0
  (∀ A B Ae Ale Be Ble S T, Proper ((@equiv (S ⇀ T) _) ==> impl)
   (@StrictlyOrderPreserving A B Ae Ale Be Ble S T)).
Proof. red; intros. intros f g E ?. split; try apply _. rewrite <- E; apply _.
  assert (Morphism (S ⇒ T) g) by (rewrite <-E; apply _).
  intros x ? y ? ?. 
  rewrite <-(E _ _ (_ : Proper (S,=) x)).
  rewrite <-(E _ _ (_ : Proper (S,=) y)).
  now apply (strictly_order_preserving f _ _).
Qed.
Hint Extern 0 (Find_Proper_Signature (@StrictlyOrderPreserving) 0 _) => eexact strictly_order_preserving_proper : typeclass_instances.

Lemma strictly_order_reflecting_proper: Find_Proper_Signature (@StrictlyOrderReflecting) 0
  (∀ A B Ae Ale Be Ble S T, Proper ((@equiv (S ⇀ T) _) ==> impl)
   (@StrictlyOrderReflecting A B Ae Ale Be Ble S T)).
Proof. red; intros. intros f g E ?. split; try apply _. rewrite <- E; apply _.
  assert (Morphism (S ⇒ T) g) by (rewrite <-E; apply _).
  intros x ? y ? E2. 
  rewrite <-(E _ _ (_ : Proper (S,=) x)) in E2.
  rewrite <-(E _ _ (_ : Proper (S,=) y)) in E2.
  now apply (strictly_order_reflecting f _ _).
Qed.
Hint Extern 0 (Find_Proper_Signature (@StrictlyOrderReflecting) 0 _) => eexact strictly_order_reflecting_proper : typeclass_instances.

Lemma strict_order_embedding_proper: Find_Proper_Signature (@StrictOrderEmbedding) 0
  (∀ A B Ae Ale Be Ble S T, Proper ((@equiv (S ⇀ T) _) ==> impl)
   (@StrictOrderEmbedding A B Ae Ale Be Ble S T)).
Proof. red; intros. intros f g E ?. split; rewrite <- E; apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@StrictOrderEmbedding) 0 _) => eexact strict_order_embedding_proper : typeclass_instances.

