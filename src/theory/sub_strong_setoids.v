Require Import
  abstract_algebra.
Require Export theory.subsetoids theory.strong_setoids.

Instance: ∀ `{SubStrongSetoid (S:=X)}, SubSetoid X := {}.

Instance: ∀ `{sm: SubStrongSetoid_Morphism (f:=f) (S:=X) (T:=Y)},
  SubSetoid_Morphism f X Y.
Proof. intros. destruct sm as [??? ext].
  split; try apply _.
  intros x₁ x₂ Ex. unfold_sigs. red_sig.
  rewrite <- tight_apart. rewrite <- tight_apart in Ex.
  intro E. pose proof (ext x₁ _ x₂ _ E). contradiction.
Qed.

Instance: ∀ `{sbm: SubStrongSetoid_Binary_Morphism (f:=f) (S:=X) (T:=Y) (U:=Z)},
  SubSetoid_Binary_Morphism f X Y Z.
Proof. intros. destruct sbm as [???? ext].
  split; try apply _.
  intros x₁ x₂ Ex y₁ y₂ Ey. unfold_sigs. red_sig.
  rewrite <- tight_apart. rewrite <- tight_apart in Ex. rewrite <- tight_apart in Ey.
  intro E. destruct (ext x₁ _ y₁ _ x₂ _ y₂ _ E); contradiction.
Qed.

Instance strong_setoid_morphism_1 :
  ∀ `{sbm: SubStrongSetoid_Binary_Morphism (f:=f) (S:=X) (T:=Y) (U:=Z)} `{x ∊ X},
    SubStrongSetoid_Morphism (f x) Y Z.
Proof. intros. destruct sbm as [???? ext].
  split; try apply _. intros ??; apply _.
  intros y₁ ? y₂ ? E.
  destruct (ext x _ y₁ _ x _ y₂ _ E); trivial.
  now destruct (irreflexivity (≠) x).
Qed.

Instance strong_setoid_morphism_2 :
  ∀ `{sbm: SubStrongSetoid_Binary_Morphism (f:=f) (S:=X) (T:=Y) (U:=Z)} `{y ∊ Y},
    SubStrongSetoid_Morphism (λ x, f x y) X Z.
Proof. intros. destruct sbm as [???? ext].
  split; try apply _. intros ??; apply _.
  intros x₁ ? x₂ ? E.
  destruct (ext x₁ _ y _ x₂ _ y _ E); trivial.
  now destruct (irreflexivity (≠) y).
Qed.

Lemma strong_submorphism_proper: Find_Proper_Signature (@SubStrongSetoid_Morphism) 0
  (∀ A Ae B Be Aue Bue f,
     Proper ((ProperSubset,⊆)-->(ProperSubset,⊆)++>impl)
            (@SubStrongSetoid_Morphism A Ae B Be Aue Bue f) ).
Proof. red. intros.
  intros S1 S2 [[??]ES] T1 T2 [[??]ET] [??? ext].
  split; try (split; apply _).
  intros ??; apply _.
  intros x₁ ? x₂ ?. exact (ext x₁ _ x₂ _).
Qed.
Hint Extern 0 (Find_Proper_Signature (@SubStrongSetoid_Morphism) 0 _) => eexact strong_submorphism_proper : typeclass_instances.

Lemma strong_submorphism_proper2: Find_Proper_Signature (@SubStrongSetoid_Morphism) 1
  (∀ A Ae B Be Aue Bue f, Proper ((=)==>(=)==>impl)
                              (@SubStrongSetoid_Morphism A Ae B Be Aue Bue f) ).
Proof. red. intros.
  intros S1 S2 ES T1 T2 ET [????].
  assert (ProperSubset S2) by (rewrite <- ES; apply _).
  assert (ProperSubset T2) by (rewrite <- ET; apply _).
  rewrite_subset <-ES. rewrite_subset <-ET. now split.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SubStrongSetoid_Morphism) 1 _) => eexact strong_submorphism_proper2 : typeclass_instances.

Lemma strong_submorphism_binary_proper: Find_Proper_Signature (@SubStrongSetoid_Binary_Morphism) 0
  (∀ A Ae B Be C Ce Aue Bue Cue f,
     Proper ((ProperSubset,⊆)-->(ProperSubset,⊆)-->(ProperSubset,⊆)++>impl)
            (@SubStrongSetoid_Binary_Morphism A Ae B Be C Ce Aue Bue Cue f) ).
Proof. red. intros.
  intros S1 S2 [[??]ES] T1 T2 [[??]ET] U1 U2 [[??]EU] [???? ext].
  split; try (split; apply _).
  intros ????; apply _.
  intros x₁ ? y₁ ? x₂ ? y₂ ?. exact (ext x₁ _ y₁ _ x₂ _ y₂ _).
Qed.
Hint Extern 0 (Find_Proper_Signature (@SubStrongSetoid_Binary_Morphism) 0 _) => eexact strong_submorphism_binary_proper : typeclass_instances.

Lemma strong_submorphism_binary_proper2: Find_Proper_Signature (@SubStrongSetoid_Binary_Morphism) 1
  (∀ A Ae B Be C Ce Aue Bue Cue f, Proper ((=)==>(=)==>(=)==>impl)
                              (@SubStrongSetoid_Binary_Morphism A Ae B Be C Ce Aue Bue Cue f) ).
Proof. red. intros.
  intros S1 S2 ES T1 T2 ET U1 U2 EU [?????].
  assert (ProperSubset S2) by (rewrite <- ES; apply _).
  assert (ProperSubset T2) by (rewrite <- ET; apply _).
  assert (ProperSubset U2) by (rewrite <- EU; apply _).
  rewrite_subset <-ES. rewrite_subset <-ET. rewrite_subset <-EU. now split.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SubStrongSetoid_Binary_Morphism) 1 _) => eexact strong_submorphism_binary_proper2 : typeclass_instances.

Section dec_setoid_morphisms.
  Context `{StrongSetoid A} `{!StandardUnEq A} `{StrongSetoid B}.

  Instance dec_strong_morphism f (S:Subset A) (T:Subset B)
    `{sm: !SubSetoid_Morphism f S T} : SubStrongSetoid_Morphism f S T.
  Proof. destruct sm as [???].
    split; try (split; apply _). apply _.
    intros x ? y ? E. rewrite standard_uneq. contradict E.  apply equiv_nue.
    now rewrite_on S -> E.
  Qed.

  Context `{!StandardUnEq B}.

  Instance dec_strong_injective f (S:Subset A) (T:Subset B)
    `{!Injective f S T} : StrongInjective f S T.
  Proof. pose proof (injective_mor f).
    split; try apply _.
    intros x ? y ?. setoid_rewrite standard_uneq. intro E. contradict E.
    exact (injective f x y E).
  Qed.

  Context `{StrongSetoid C}.

  Instance dec_strong_binary_morphism f (S:Subset A) (T:Subset B) (U:Subset C)
    `{sbm: !SubSetoid_Binary_Morphism f S T U} : SubStrongSetoid_Binary_Morphism f S T U.
  Proof. destruct sbm as [????].
    split; try (split; apply _). apply _.
    intros x₁ ? y₁ ? x₂ ? y₂ ? E1.
    case (cotransitive E1 (f x₂ y₁)); setoid_rewrite standard_uneq; intro E2;
    [ left | right ]; intro E3; destruct (uneq_ne _ _ E2).
    now rewrite_on S -> E3. now rewrite_on T -> E3.
  Qed.

End dec_setoid_morphisms.
