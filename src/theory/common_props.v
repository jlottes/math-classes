Require Import abstract_algebra theory.sub_strong_setoids.

Local Ltac subproper := red; intros; intros ?? ? ? [??]; split; apply _.

Lemma NonZero_proper : Find_Proper_Signature (@NonZero) 0 (∀ A Aue Azero, Proper ((⊆)++>(⊆)) (@NonZero A Aue Azero)). Proof. subproper. Qed.
Lemma NonNeg_proper  : Find_Proper_Signature (@NonNeg ) 0 (∀ A Ale Azero, Proper ((⊆)++>(⊆)) (@NonNeg  A Ale Azero)). Proof. subproper. Qed.
Lemma Pos_proper     : Find_Proper_Signature (@Pos    ) 0 (∀ A Alt Azero, Proper ((⊆)++>(⊆)) (@Pos     A Alt Azero)). Proof. subproper. Qed.
Lemma NonPos_proper  : Find_Proper_Signature (@NonPos ) 0 (∀ A Ale Azero, Proper ((⊆)++>(⊆)) (@NonPos  A Ale Azero)). Proof. subproper. Qed.
Lemma Neg_proper     : Find_Proper_Signature (@Neg    ) 0 (∀ A Alt Azero, Proper ((⊆)++>(⊆)) (@Neg     A Alt Azero)). Proof. subproper. Qed.

Hint Extern 0 (Find_Proper_Signature (@NonZero) 0 _) => eexact NonZero_proper : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@NonNeg ) 0 _) => eexact NonNeg_proper  : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@Pos    ) 0 _) => eexact Pos_proper     : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@NonPos ) 0 _) => eexact NonPos_proper  : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@Neg    ) 0 _) => eexact Neg_proper     : typeclass_instances.

Lemma NonZero_subset `{UnEq A} `{Zero A} (R:Subset A) : R ₀ ⊆ R. Proof. firstorder. Qed.
Lemma NonNeg_subset  `{Le A}   `{Zero A} (R:Subset A) : R⁺  ⊆ R. Proof. firstorder. Qed.
Lemma Pos_subset     `{Lt A}   `{Zero A} (R:Subset A) : R₊  ⊆ R. Proof. firstorder. Qed.
Lemma NonPos_subset  `{Le A}   `{Zero A} (R:Subset A) : R⁻  ⊆ R. Proof. firstorder. Qed.
Lemma Neg_subset     `{Lt A}   `{Zero A} (R:Subset A) : R₋  ⊆ R. Proof. firstorder. Qed.

Hint Extern 0 (?R ₀ ⊆ ?R) => eapply @NonZero_subset : typeclass_instances. 

Lemma NonZero_element `{UnEq A} `{Zero A} R `{x ∊ R} `{PropHolds (x ≠ 0)} : x ∊ R ₀. Proof. now split. Qed.
Lemma NonNeg_element  `{Le A}   `{Zero A} R `{x ∊ R} `{PropHolds (0 ≤ x)} : x ∊ R⁺ . Proof. now split. Qed.
Lemma Pos_element     `{Lt A}   `{Zero A} R `{x ∊ R} `{PropHolds (0 < x)} : x ∊ R₊ . Proof. now split. Qed.
Lemma NonPos_element  `{Le A}   `{Zero A} R `{x ∊ R} `{PropHolds (x ≤ 0)} : x ∊ R⁻ . Proof. now split. Qed.
Lemma Neg_element     `{Lt A}   `{Zero A} R `{x ∊ R} `{PropHolds (x < 0)} : x ∊ R₋ . Proof. now split. Qed.

Hint Extern 0 (?x ∊ ?R ₀) => eapply @NonZero_element : typeclass_instances.

Lemma NonZero_subsetoid `{UnEqualitySetoid A} `{Zero A} R `{!SubSetoid R} : SubSetoid (R ₀).
Proof. split; try apply _. intros ?? E [??]. split; now rewrite <-E. Qed.
Hint Extern 0 (@SubSetoid _ _ (@NonZero _ _ _ _)) => eapply @NonZero_subsetoid : typeclass_instances. 

Lemma Every_SubReflexive     `(R:relation A) `{!Reflexive R}    : SubReflexive    R (Every A). Proof. firstorder. Qed.
Lemma Every_SubIrreflexive   `(R:relation A) `{!Irreflexive R}  : SubIrreflexive  R (Every A). Proof. firstorder. Qed.
Lemma Every_SubSymmetric     `(R:relation A) `{!Symmetric R}    : SubSymmetric    R (Every A). Proof. firstorder. Qed.
Lemma Every_SubTransitive    `(R:relation A) `{!Transitive R}   : SubTransitive   R (Every A). Proof. firstorder. Qed.
Lemma Every_SubCoTransitive  `(R:relation A) `{!CoTransitive R} : SubCoTransitive R (Every A). Proof. firstorder. Qed.
Lemma Every_SubAntiSymmetric `(R:relation A) `{Equiv A} `{!AntiSymmetric (=) R} : SubAntiSymmetric R (Every A). Proof. firstorder. Qed.

Hint Extern 2 (SubReflexive     ?R (Every _)) => eexact (Every_SubReflexive     R) : typeclass_instances.
Hint Extern 2 (SubIrreflexive   ?R (Every _)) => eexact (Every_SubIrreflexive   R) : typeclass_instances.
Hint Extern 2 (SubSymmetric     ?R (Every _)) => eexact (Every_SubSymmetric     R) : typeclass_instances.
Hint Extern 2 (SubTransitive    ?R (Every _)) => eexact (Every_SubTransitive    R) : typeclass_instances.
Hint Extern 2 (SubCoTransitive  ?R (Every _)) => eexact (Every_SubCoTransitive  R) : typeclass_instances.
Hint Extern 2 (SubAntiSymmetric ?R (Every _)) => eexact (Every_SubAntiSymmetric R) : typeclass_instances.

Lemma Every_SubEquivalence   `(R:relation A) `{!Equivalence R}   : SubEquivalence   R (Every A). Proof. split; apply _. Qed.
Hint Extern 2 (SubEquivalence ?R (Every _)) => eexact (Every_SubEquivalence R) : typeclass_instances.


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

Lemma SubCoTransitive_proper : Find_Proper_Signature (@SubCoTransitive) 0
  (∀ A, Proper (relation_equivalence==>(⊆)-->impl) (@SubCoTransitive A)).
Proof. intro. intros R1 R2 ER S1 S2 ES ? x ? y ? E z ?. unfold flip in *.
  apply ER in E. destruct (subcotransitivity E z); [left|right]; now apply ER.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SubCoTransitive) 0 _) => eexact SubCoTransitive_proper : typeclass_instances.

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

Lemma Trichotomy_proper : Find_Proper_Signature (@Trichotomy) 0
  (∀ A Ae, Proper (subrelation++>(⊆)-->impl) (@Trichotomy A Ae)).
Proof. red. intros. intros R1 R2 ER S1 S2 ES P x ? y ?. unfold flip in *.
  destruct (trichotomy R1 x y) as [?|[?|?]]; [left|right;left|right;right];
  trivial; now apply ER.
Qed.
Hint Extern 0 (Find_Proper_Signature (@Trichotomy) 0 _) => eexact Trichotomy_proper : typeclass_instances.

Section cancellation.

  Lemma right_cancel_from_left `{SubSetoid (S:=R)} `{!Closed (R ==> R ==> R) op} `{!Commutative op R}
   `{z ∊ R} `{!LeftCancellation op z R} : RightCancellation op z R.
  Proof. intros x ? y ? E.
    apply (left_cancellation op z R); trivial.
    rewrite_on R -> (commutativity z x).
    now rewrite_on R -> (commutativity z y).
  Qed.

  Context `{SubStrongSetoid (S:=R)}.

  Lemma strong_right_cancel_from_left `{!Closed (R ==> R ==> R) op} `{!Commutative op R}
    `{z ∊ R} `{!StrongLeftCancellation op z R} : StrongRightCancellation op z R.
  Proof. intros x ? y ? E.
    rewrite 2!(commutativity _ z).
    now apply (strong_left_cancellation op _ R).
  Qed.

  Global Instance strong_left_cancellation_cancel `{!StrongLeftCancellation op z R} : LeftCancellation op z R | 20.
  Proof.
    intros x ? y ?. rewrite <-!tight_apart. intro E. contradict E.
    now apply (strong_left_cancellation op _ R).
  Qed.

  Global Instance strong_right_cancellation_cancel `{!StrongRightCancellation op z R} : RightCancellation op z R | 20.
  Proof.
    intros x ? y ?. rewrite <-!tight_apart. intros E. contradict E.
    now apply (strong_right_cancellation op _ R).
  Qed.

End cancellation.

Lemma ZeroProduct_proper : Find_Proper_Signature (@ZeroProduct) 0
  (∀ A Ae Amult Azero, Proper ((⊆)-->impl) (@ZeroProduct A Ae Amult Azero)).
Proof. intro. intros. intros ?? ES P x ? y ?. unfold flip in ES.
  exact (zero_product x y).
Qed.
Hint Extern 0 (Find_Proper_Signature (@ZeroProduct) 0 _) => eexact ZeroProduct_proper : typeclass_instances.

Instance ZeroProduct_no_zero_divisors `{UnEqualitySetoid A} `{Mult A} `{Zero A} `{!ZeroProduct R} : NoZeroDivisors R.
Proof. intros x [[? xn0][y[[? yn0][E|E]]]];
  pose proof (uneq_ne _ _ xn0); pose proof (uneq_ne _ _ yn0).
  destruct (zero_product x y E); contradiction.
  destruct (zero_product y x E); contradiction.
Qed.

Lemma ZeroDivisor_proper: Find_Proper_Signature (@ZeroDivisor) 0
  (∀ A Aue Ae Azero Amult, Proper ((⊆)++>eq==>impl) (@ZeroDivisor A Aue Ae Azero Amult)).
Proof. red. intros. intros ?? ES ?? Ex [?[y[??]]]. rewrite <-Ex.
  split. now rewrite <-ES. exists y. intuition; now rewrite <-ES.
Qed.
Hint Extern 0 (Find_Proper_Signature (@ZeroDivisor) 0 _) => eexact ZeroDivisor_proper : typeclass_instances.

Lemma NoZeroDivisors_proper: Find_Proper_Signature (@NoZeroDivisors) 0
  (∀ A Aue Ae Azero Amult, Proper ((⊆)-->impl) (@NoZeroDivisors A Aue Ae Azero Amult)).
Proof. red. intros. intros ?? E P x. pose proof (P x) as Px.
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

