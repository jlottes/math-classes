Require Import
  abstract_algebra interfaces.orders theory.common_props theory.subsetoids.

Lemma le_proper : Find_Proper_Signature (@le) 0
  (∀ `{PartialOrder (P:=P)}, Proper ((P,=) ==> (P,=) ==> impl) (≤)).
Proof. red. intros. apply po_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@le) 0 _) => eexact le_proper : typeclass_instances.

Lemma lt_proper : Find_Proper_Signature (@lt) 0
  (∀ `{SubStrictOrder (S:=T)}, Proper ((T,=) ==> (T,=) ==> impl) (<)).
Proof. red. intros. apply so_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@lt) 0 _) => eexact lt_proper : typeclass_instances.


Lemma PartialOrder_proper : Find_Proper_Signature (@PartialOrder) 0
  (∀ A Ae Ale, Proper ((SubSetoid,⊆)-->impl) (@PartialOrder A Ae Ale)).
Proof. red. intros. intros S1 S2 ES ?. unfold flip in *. unfold_sigs.
  unfold Element in el, el0. split; try apply _; rewrite ES; apply _.
Qed.
Hint Extern 0 (Find_Proper_Signature (@PartialOrder) 0 _) => eexact PartialOrder_proper : typeclass_instances.

Lemma PartialOrder_proper2 : Find_Proper_Signature (@PartialOrder) 1
  (∀ A Ae Ale, Proper ((=)==>impl) (@PartialOrder A Ae Ale)).
Proof. red; intros; intros S1 S2 ES ?. pose proof (po_subsetoid). find_subsetoid S2.
  now rewrite_subsetoid <- ES.
Qed.
Hint Extern 0 (Find_Proper_Signature (@PartialOrder) 1 _) => eexact PartialOrder_proper2 : typeclass_instances.

Lemma TotalOrder_proper : Find_Proper_Signature (@TotalOrder) 0
  (∀ A Ae Ale, Proper ((SubSetoid,⊆)-->impl) (@TotalOrder A Ae Ale)).
Proof. red. intros. intros S1 S2 ES ?. unfold flip in *. split; rewrite ES; apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@TotalOrder) 0 _) => eexact TotalOrder_proper : typeclass_instances.

Lemma TotalOrder_proper2 : Find_Proper_Signature (@TotalOrder) 1
  (∀ A Ae Ale, Proper ((=)==>impl) (@TotalOrder A Ae Ale)).
Proof. red; intros; intros S1 S2 ES ?. pose proof (po_subsetoid). find_subsetoid S2.
  now rewrite_subsetoid <- ES.
Qed.
Hint Extern 0 (Find_Proper_Signature (@TotalOrder) 1 _) => eexact TotalOrder_proper2 : typeclass_instances.

Lemma SubStrictOrder_proper : Find_Proper_Signature (@SubStrictOrder) 0
  (∀ A Ae Alt, Proper ((SubSetoid,⊆)-->impl) (@SubStrictOrder A Ae Alt)).
Proof. red. intros. intros S1 S2 ES ?. unfold flip in *. unfold_sigs.
  unfold Element in el, el0. split; try apply _; rewrite ES; apply _.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SubStrictOrder) 0 _) => eexact SubStrictOrder_proper : typeclass_instances.

Lemma SubStrictOrder_proper2 : Find_Proper_Signature (@SubStrictOrder) 1
  (∀ A Ae Alt, Proper ((=)==>impl) (@SubStrictOrder A Ae Alt)).
Proof. red; intros; intros S1 S2 ES ?. pose proof (so_subsetoid). find_subsetoid S2.
  now rewrite_subsetoid <- ES.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SubStrictOrder) 1 _) => eexact SubStrictOrder_proper2 : typeclass_instances.


Lemma le_flip `{Le A} {S:Subset A} `{!TotalRelation (≤) S} x `{!x ∊ S} y `{!y ∊ S} : ¬y ≤ x → x ≤ y.
Proof. firstorder. Qed.

Section partial_order.
  Context `{PartialOrder (P:=P)}.

  Existing Instance po_subsetoid.

  Lemma eq_le  x `{!x ∊ P} y `{!y ∊ P} : x = y → x ≤ y.
  Proof. intros E. rewrite_on P -> E. now apply subreflexivity. Qed.

  Lemma eq_le_flip x `{!x ∊ P} y `{!y ∊ P} : x = y → y ≤ x.
  Proof. intros E. rewrite_on P -> E. now apply subreflexivity. Qed.

  Lemma not_le_ne x `{!x ∊ P} y `{!y ∊ P} : ¬x ≤ y → x ≠ y.
  Proof. intros E1 E2. destruct E1. rewrite_on P -> E2. now apply subreflexivity. Qed.

  Lemma eq_iff_le x `{!x ∊ P} y `{!y ∊ P} : x = y ↔ x ≤ y ∧ y ≤ x.
  Proof. split; intros E. split; rewrite_on P -> E; now apply subreflexivity.
         now apply (subantisymmetry (≤) x y). Qed.
End partial_order.

Section strict_order.
  Context `(S:Subset A) `{SubStrictOrder (A:=A) (S:=S)}.

  Existing Instance so_subsetoid.

  Lemma lt_flip x `{!x ∊ S} y `{!y ∊ S} : x < y → ¬y < x.
  Proof.
    intros E1 E2.
    apply (subirreflexivity (<) x).
    now apply (subtransitivity x y x).
  Qed.

  Lemma lt_antisym x `{!x ∊ S} y `{!y ∊ S} : ¬(x < y < x).
  Proof.
    intros [E1 E2].
    now destruct (lt_flip x y).
  Qed.

  Lemma lt_ne x `{!x ∊ S} y `{!y ∊ S} : x < y → x ≠ y.
  Proof. intros E1 E2. rewrite_on S -> E2 in E1. now destruct (subirreflexivity (<) y). Qed.

  Lemma lt_ne_flip x `{!x ∊ S} y `{!y ∊ S} : x < y → y ≠ x.
  Proof. intro. now apply not_symmetry, lt_ne. Qed.

  Lemma eq_not_lt x `{!x ∊ S} y `{!y ∊ S} : x = y → ¬x < y.
  Proof. intros E. rewrite_on S -> E. now apply (subirreflexivity (<)). Qed.
End strict_order.
