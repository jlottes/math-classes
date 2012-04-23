Require Import abstract_algebra theory.subset.

(* When the following properties hold, they hold also on subsets, and for any subrelations of (=). *)

Local Ltac solve := intro; intros; intros R1 R2 ER S1 S2 ES P ?; intros; unfold flip in *; apply ER; apply P; apply _.
Lemma SubReflexive_proper   : Find_Proper_Signature (@SubReflexive)    0 (∀ A                , Proper (subrelation++>(⊆)-->impl) (@SubReflexive    A                )). Proof. solve. Qed.
Lemma Associative_proper    : Find_Proper_Signature (@Associative)     0 (∀ A f              , Proper (subrelation++>(⊆)-->impl) (@Associative     A f              )). Proof. solve. Qed.
Lemma Commutative_proper    : Find_Proper_Signature (@Commutative)     0 (∀ A B f            , Proper (subrelation++>(⊆)-->impl) (@Commutative     A B f            )). Proof. solve. Qed.
Lemma LeftIdentity_proper   : Find_Proper_Signature (@LeftIdentity)    0 (∀ A B op x         , Proper (subrelation++>(⊆)-->impl) (@LeftIdentity    A B op x         )). Proof. solve. Qed.
Lemma RightIdentity_proper  : Find_Proper_Signature (@RightIdentity)   0 (∀ A B op x         , Proper (subrelation++>(⊆)-->impl) (@RightIdentity   A B op x         )). Proof. solve. Qed.
Lemma LeftAbsorb_proper     : Find_Proper_Signature (@LeftAbsorb)      0 (∀ A B op x         , Proper (subrelation++>(⊆)-->impl) (@LeftAbsorb      A B op x         )). Proof. solve. Qed.
Lemma RightAbsorb_proper    : Find_Proper_Signature (@RightAbsorb)     0 (∀ A B op x         , Proper (subrelation++>(⊆)-->impl) (@RightAbsorb     A B op x         )). Proof. solve. Qed.
Lemma LeftInverse_proper    : Find_Proper_Signature (@LeftInverse)     0 (∀ A B C op inv unit, Proper (subrelation++>(⊆)-->impl) (@LeftInverse     A B C op inv unit)). Proof. solve. Qed.
Lemma RightInverse_proper   : Find_Proper_Signature (@RightInverse)    0 (∀ A B C op inv unit, Proper (subrelation++>(⊆)-->impl) (@RightInverse    A B C op inv unit)). Proof. solve. Qed.
Lemma Involutive_proper     : Find_Proper_Signature (@Involutive)      0 (∀ A f              , Proper (subrelation++>(⊆)-->impl) (@Involutive      A f              )). Proof. solve. Qed.
Lemma LeftDistribute_proper : Find_Proper_Signature (@LeftDistribute)  0 (∀ A f g            , Proper (subrelation++>(⊆)-->impl) (@LeftDistribute  A f g            )). Proof. solve. Qed.
Lemma RightDistribute_proper: Find_Proper_Signature (@RightDistribute) 0 (∀ A f g            , Proper (subrelation++>(⊆)-->impl) (@RightDistribute A f g            )). Proof. solve. Qed.

Hint Extern 0 (Find_Proper_Signature (@SubReflexive   ) 0 _) => eexact SubReflexive_proper    : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@Associative    ) 0 _) => eexact Associative_proper     : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@Commutative    ) 0 _) => eexact Commutative_proper     : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@LeftIdentity   ) 0 _) => eexact LeftIdentity_proper    : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@RightIdentity  ) 0 _) => eexact RightIdentity_proper   : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@LeftAbsorb     ) 0 _) => eexact LeftAbsorb_proper      : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@RightAbsorb    ) 0 _) => eexact RightAbsorb_proper     : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@LeftInverse    ) 0 _) => eexact LeftInverse_proper     : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@RightInverse   ) 0 _) => eexact RightInverse_proper    : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@Involutive     ) 0 _) => eexact Involutive_proper      : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@LeftDistribute ) 0 _) => eexact LeftDistribute_proper  : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@RightDistribute) 0 _) => eexact RightDistribute_proper : typeclass_instances.

Lemma SubIrreflexive_proper : Find_Proper_Signature (@SubIrreflexive) 0
  (∀ A, Proper (subrelation-->(⊆)-->impl) (@SubIrreflexive A)).
Proof. red. intros. intros R1 R2 ER S1 S2 ES P ?. intros. unfold flip in *.
  pose proof (subirreflexivity R1 x) as Q. contradict Q. now apply ER.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SubIrreflexive) 0 _) => eexact SubIrreflexive_proper : typeclass_instances.

Lemma SubSymmetric_proper : Find_Proper_Signature (@SubSymmetric) 0
  (∀ A, Proper (relation_equivalence==>(⊆)-->impl) (@SubSymmetric A)).
Proof. intro. intros R1 R2 ER S1 S2 ES P ?. intros. unfold flip in *. apply ER. apply P; try apply _. now apply ER. Qed.
Hint Extern 0 (Find_Proper_Signature (@SubSymmetric) 0 _) => eexact SubSymmetric_proper : typeclass_instances.

Lemma SubTransitive_proper : Find_Proper_Signature (@SubTransitive) 0
  (∀ A, Proper (relation_equivalence==>(⊆)-->impl) (@SubTransitive A)).
Proof. intro. intros R1 R2 ER S1 S2 ES P x ? y ? z ? ??. unfold flip in *. apply ER.
  apply (P x _ y _ z _); now apply ER.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SubTransitive) 0 _) => eexact SubTransitive_proper : typeclass_instances.

Lemma SubEquivalence_proper : Find_Proper_Signature (@SubEquivalence) 0
  (∀ A, Proper (relation_equivalence==>(⊆)-->impl) (@SubEquivalence A)).
Proof. intro. intros R1 R2 ER S1 S2 ES ?. unfold flip in *. split; rewrite <- ER, ES; apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@SubEquivalence) 0 _) => eexact SubEquivalence_proper : typeclass_instances.

Lemma SubAntiSymmetric_proper : Find_Proper_Signature (@SubAntiSymmetric) 0
  (∀ A Ae, Proper (relation_equivalence==>(⊆)-->impl) (@SubAntiSymmetric A Ae)).
Proof. red. intros. intros R1 R2 ER S1 S2 ES ?. unfold flip in *.
  intros x ? y ? ??. apply (subantisymmetry R1 x y); now apply ER.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SubAntiSymmetric) 0 _) => eexact SubAntiSymmetric_proper : typeclass_instances.

Lemma TotalRelation_proper : Find_Proper_Signature (@TotalRelation) 0
  (∀ A, Proper (subrelation++>(⊆)-->impl) (@TotalRelation A)).
Proof. intro. intros R1 R2 ER S1 S2 ES P x ? y ?. unfold flip in *.
  destruct (total R1 x y); [ left | right ]; now apply ER.
Qed.
Hint Extern 0 (Find_Proper_Signature (@TotalRelation) 0 _) => eexact TotalRelation_proper : typeclass_instances.

Lemma NonZero_proper : Find_Proper_Signature (@NonZero) 0
  (∀ A Ae Azero, Proper ((=)==>(=)) (@NonZero A Ae Azero)).
Proof. intro. intros. intros ?? ES. split; intros [??]; split; try assumption.
  now rewrite <-ES. now rewrite ES.
Qed.
Hint Extern 0 (Find_Proper_Signature (@NonZero) 0 _) => eexact NonZero_proper : typeclass_instances.

Lemma NonZero_proper2 : Find_Proper_Signature (@NonZero) 1
  (∀ A Ae Azero, Proper ((⊆)++>(⊆)) (@NonZero A Ae Azero)).
Proof. intro. intros. intros ?? ES x [??]. split. now rewrite <-ES. assumption. Qed.
Hint Extern 0 (Find_Proper_Signature (@NonZero) 1 _) => eexact NonZero_proper2 : typeclass_instances.

Lemma NonZero_subset `{Equiv A} `{Zero A} (S:Subset A) : S ₀ ⊆ S. Proof. firstorder. Qed.
Hint Extern 0 (@SubsetOf _ (@NonZero _ _ _ ?S) ?S) => eapply @NonZero_subset : typeclass_instances. 

Lemma NonZero_element `{Equiv A} `{Zero A} S x `{!x ∊ S} `{PropHolds (x ≠ 0)} : x ∊ S ₀.
Proof. now split. Qed.
Hint Extern 0 (@Element _ (@NonZero _ _ _ _) _) => eapply @NonZero_element : typeclass_instances.

Lemma ZeroProduct_proper : Find_Proper_Signature (@ZeroProduct) 0
  (∀ A Ae Amult Azero, Proper ((⊆)-->impl) (@ZeroProduct A Ae Amult Azero)).
Proof. intro. intros. intros ?? ES P x ? y ?. unfold flip in ES.
  exact (zero_product x y).
Qed.
Hint Extern 0 (Find_Proper_Signature (@ZeroProduct) 0 _) => eexact ZeroProduct_proper : typeclass_instances.

Instance ZeroProduct_no_zero_divisors `{ZeroProduct (R:=R)} : NoZeroDivisors R.
Proof. intros x [[? xn0][y[[? yn0][E|E]]]].
  destruct (zero_product x y E); contradiction.
  destruct (zero_product y x E); contradiction.
Qed.

Lemma ZeroDivisor_proper: Find_Proper_Signature (@ZeroDivisor) 0
  (∀ A Ae Azero Amult, Proper ((⊆)++>eq==>impl) (@ZeroDivisor A Ae Azero Amult)).
Proof. intro. intros. intros ?? ES ?? Ex [?[y[??]]]. rewrite <-Ex.
  split. now rewrite <-ES. exists y. intuition; now rewrite <-ES.
Qed.
Hint Extern 0 (Find_Proper_Signature (@ZeroDivisor) 0 _) => eexact ZeroDivisor_proper : typeclass_instances.

Lemma NoZeroDivisors_proper: Find_Proper_Signature (@NoZeroDivisors) 0
  (∀ A Ae Azero Amult, Proper ((⊆)-->impl) (@NoZeroDivisors A Ae Azero Amult)).
Proof. intro. intros. intros ?? E P x. pose proof (P x) as Px.
  contradict Px. unfold flip in E. now rewrite <-E.
Qed.
Hint Extern 0 (Find_Proper_Signature (@NoZeroDivisors) 0 _) => eexact NoZeroDivisors_proper : typeclass_instances.

Lemma RingUnits_proper : Find_Proper_Signature (@RingUnits) 0
  (∀ A Ae Amult Aone, Proper ((⊆)++>(⊆)) (@RingUnits A Ae Amult Aone)).
Proof. intro. intros. intros ?? E x [?[y[??]]]. split. now rewrite <-E.
  exists y. split. now rewrite <-E. assumption.
Qed.
Hint Extern 0 (Find_Proper_Signature (@RingUnits) 0 _) => eexact RingUnits_proper : typeclass_instances.

Lemma RingUnits_subset `{Equiv A} `{Mult A} `{One A} (R:Subset A) : RingUnits R ⊆ R. Proof. firstorder. Qed.
Hint Extern 0 (@SubsetOf _ (@RingUnits _ _ _ _ ?R) ?R) => eapply @RingUnits_subset : typeclass_instances. 

