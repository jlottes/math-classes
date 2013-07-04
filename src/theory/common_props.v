Require Import abstract_algebra theory.setoids.

Hint Extern 0 (Equiv (elt_type (?X ₀))) => exact (_ : Equiv X) : typeclass_instances.

Local Hint Extern 20 (?x ∊ ?T) => match goal with
  | sub : SubsetOf _ ?T |- _ => eapply (subset (SubsetOf:=sub) x)
end : typeclass_instances.

Local Ltac subproper := red; intros; intros ?? ? ? [??]; split; apply _.

Lemma NonZero_proper : Find_Proper_Signature (@NonZero) 0 (∀ A Aue Azero, Proper (SubsetOf++>SubsetOf) (@NonZero A Aue Azero)). Proof. subproper. Qed.
Lemma NonNeg_proper  : Find_Proper_Signature (@NonNeg ) 0 (∀ A Ale Azero, Proper (SubsetOf++>SubsetOf) (@NonNeg  A Ale Azero)). Proof. subproper. Qed.
Lemma Pos_proper     : Find_Proper_Signature (@Pos    ) 0 (∀ A Alt Azero, Proper (SubsetOf++>SubsetOf) (@Pos     A Alt Azero)). Proof. subproper. Qed.
Lemma NonPos_proper  : Find_Proper_Signature (@NonPos ) 0 (∀ A Ale Azero, Proper (SubsetOf++>SubsetOf) (@NonPos  A Ale Azero)). Proof. subproper. Qed.
Lemma Neg_proper     : Find_Proper_Signature (@Neg    ) 0 (∀ A Alt Azero, Proper (SubsetOf++>SubsetOf) (@Neg     A Alt Azero)). Proof. subproper. Qed.

Hint Extern 0 (Find_Proper_Signature (@NonZero) 0 _) => eexact NonZero_proper : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@NonNeg ) 0 _) => eexact NonNeg_proper  : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@Pos    ) 0 _) => eexact Pos_proper     : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@NonPos ) 0 _) => eexact NonPos_proper  : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@Neg    ) 0 _) => eexact Neg_proper     : typeclass_instances.

Lemma NonZero_subset `{UnEq} `{Zero _} R : SubsetOf (R ₀) R. Proof. firstorder. Qed.
Lemma NonNeg_subset  `{Le}   `{Zero _} R : SubsetOf R⁺  R. Proof. firstorder. Qed.
Lemma Pos_subset     `{Lt}   `{Zero _} R : SubsetOf R₊  R. Proof. firstorder. Qed.
Lemma NonPos_subset  `{Le}   `{Zero _} R : SubsetOf R⁻  R. Proof. firstorder. Qed.
Lemma Neg_subset     `{Lt}   `{Zero _} R : SubsetOf R₋  R. Proof. firstorder. Qed.

Hint Extern 0 (SubsetOf (?R ₀) ?R) => eapply @NonZero_subset : typeclass_instances. 
Hint Extern 0 (SubsetOf ?R⁺  ?R) => eapply @NonNeg_subset  : typeclass_instances. 
Hint Extern 0 (SubsetOf ?R₊  ?R) => eapply @Pos_subset     : typeclass_instances. 
Hint Extern 0 (SubsetOf ?R⁻  ?R) => eapply @NonPos_subset  : typeclass_instances. 
Hint Extern 0 (SubsetOf ?R₋  ?R) => eapply @Neg_subset     : typeclass_instances. 

Lemma NonZero_setoid `{UnEq} `{Zero _} `{Setoid _ (S:=R)} : Setoid (R ₀). Proof. now rewrite (_:SubsetOf (R ₀) R). Qed.
Lemma NonNeg_setoid  `{Le}   `{Zero _} `{Setoid _ (S:=R)} : Setoid R⁺.    Proof. now rewrite (_:SubsetOf R⁺  R). Qed.
Lemma NonPos_setoid  `{Le}   `{Zero _} `{Setoid _ (S:=R)} : Setoid R⁻.    Proof. now rewrite (_:SubsetOf R⁻  R). Qed.
Lemma Pos_setoid     `{Lt}   `{Zero _} `{Setoid _ (S:=R)} : Setoid R₊.    Proof. now rewrite (_:SubsetOf R₊  R). Qed.
Lemma Neg_setoid     `{Lt}   `{Zero _} `{Setoid _ (S:=R)} : Setoid R₋.    Proof. now rewrite (_:SubsetOf R₋  R). Qed.

Hint Extern 2 (Setoid (_ ₀)) => eapply @NonZero_setoid : typeclass_instances. 
Hint Extern 2 (Setoid _⁺   ) => eapply @NonNeg_setoid  : typeclass_instances. 
Hint Extern 2 (Setoid _₊   ) => eapply @Pos_setoid     : typeclass_instances. 
Hint Extern 2 (Setoid _⁻   ) => eapply @NonPos_setoid  : typeclass_instances. 
Hint Extern 2 (Setoid _₋   ) => eapply @Neg_setoid     : typeclass_instances. 

Lemma NonZero_element `{UnEq} `{Zero _} R `{x ∊ R} `{PropHolds (x ≠ 0)} : x ∊ R ₀. Proof. now split. Qed.
Lemma NonNeg_element  `{Le}   `{Zero _} R `{x ∊ R} `{PropHolds (0 ≤ x)} : x ∊ R⁺ . Proof. now split. Qed.
Lemma Pos_element     `{Lt}   `{Zero _} R `{x ∊ R} `{PropHolds (0 < x)} : x ∊ R₊ . Proof. now split. Qed.
Lemma NonPos_element  `{Le}   `{Zero _} R `{x ∊ R} `{PropHolds (x ≤ 0)} : x ∊ R⁻ . Proof. now split. Qed.
Lemma Neg_element     `{Lt}   `{Zero _} R `{x ∊ R} `{PropHolds (x < 0)} : x ∊ R₋ . Proof. now split. Qed.

Hint Extern 19 (?x ∊ ?R) => match goal with
  | sub : x ∊ R ₀ |- _ => eapply (NonZero_subset R x sub)
  | sub : x ∊ R⁺  |- _ => eapply (NonNeg_subset  R x sub)
  | sub : x ∊ R₊  |- _ => eapply (Pos_subset     R x sub)
  | sub : x ∊ R⁻  |- _ => eapply (NonPos_subset  R x sub)
  | sub : x ∊ R₋  |- _ => eapply (Neg_subset     R x sub)
end : typeclass_instances.

(* Check fun `{Le A} `{Zero A} R `{x ∊ R ⁻} => _ : x ∊ R. *)

Hint Extern 5 (0 ∊ ?R⁺) => split; [apply _ | subreflexivity] : typeclass_instances.
Hint Extern 5 (0 ∊ ?R⁻) => split; [apply _ | subreflexivity] : typeclass_instances.
Hint Extern 5 (1 ∊ ?R ₀) => eapply @NonZero_element : typeclass_instances.
Hint Extern 5 (1 ∊ ?R⁺) => eapply @NonNeg_element : typeclass_instances.
Hint Extern 5 (1 ∊ ?R₊) => eapply @Pos_element : typeclass_instances.
Hint Extern 5 (2 ∊ ?R ₀) => eapply @NonZero_element : typeclass_instances.

Lemma NonZero_subsetoid `{Equiv} `{UnEq _} `{Zero _} R `{!InequalitySetoid R} `{0 ∊ R} : R ₀ ⊆ R.
Proof. split; try apply _. intros ?? E [??]. unfold_sigs. split. apply _. now rewrite_on R <- E. Qed.
Hint Extern 5 (SubSetoid (?R ₀) _) => eapply (NonZero_subsetoid R) : typeclass_instances. 

Lemma zero_or_nonzero `{Setoid (S:=R)} `{UnEq _} `{Zero _} `{!DenialInequality R} `{!SubDecision R R (=)} `{0 ∊ R}
  x `{x ∊ R} : x = 0 ∨ x ∊ R ₀.
Proof. destruct (decide_sub (=) x 0). now left. right. split. apply _. now rewrite (denial_inequality _ _). Qed.

(* When the following properties hold, they hold also on subsets. *)
Local Ltac solve := red; intros; intros S1 S2 ES R1 R2 ER P ?; intros; unfold flip in *; apply ER; apply P; try apply _.
Lemma Associative_proper      : Find_Proper_Signature (@Associative)       0 (∀ A f              , Proper (SubsetOf-->(=)==>impl) (@Associative       A f              )). Proof. solve. Qed.
Lemma Commutative_proper      : Find_Proper_Signature (@Commutative)       0 (∀ A B f            , Proper (SubsetOf-->(=)==>impl) (@Commutative       A B f            )). Proof. solve. Qed.
Lemma LeftIdentity_proper     : Find_Proper_Signature (@LeftIdentity)      0 (∀ A B op x         , Proper (SubsetOf-->(=)==>impl) (@LeftIdentity      A B op x         )). Proof. solve. Qed.
Lemma RightIdentity_proper    : Find_Proper_Signature (@RightIdentity)     0 (∀ A B op x         , Proper (SubsetOf-->(=)==>impl) (@RightIdentity     A B op x         )). Proof. solve. Qed.
Lemma LeftAbsorb_proper       : Find_Proper_Signature (@LeftAbsorb)        0 (∀ A B op x         , Proper (SubsetOf-->(=)==>impl) (@LeftAbsorb        A B op x         )). Proof. solve. Qed.
Lemma RightAbsorb_proper      : Find_Proper_Signature (@RightAbsorb)       0 (∀ A B op x         , Proper (SubsetOf-->(=)==>impl) (@RightAbsorb       A B op x         )). Proof. solve. Qed.
Lemma LeftInverse_proper      : Find_Proper_Signature (@LeftInverse)       0 (∀ A B C op inv unit, Proper (SubsetOf-->(=)==>impl) (@LeftInverse       A B C op inv unit)). Proof. solve. Qed.
Lemma RightInverse_proper     : Find_Proper_Signature (@RightInverse)      0 (∀ A B C op inv unit, Proper (SubsetOf-->(=)==>impl) (@RightInverse      A B C op inv unit)). Proof. solve. Qed.
Lemma Involutive_proper       : Find_Proper_Signature (@Involutive)        0 (∀ A f              , Proper (SubsetOf-->(=)==>impl) (@Involutive        A f              )). Proof. solve. Qed.
Lemma LeftDistribute_proper   : Find_Proper_Signature (@LeftDistribute)    0 (∀ A f g            , Proper (SubsetOf-->(=)==>impl) (@LeftDistribute    A f g            )). Proof. solve. Qed.
Lemma RightDistribute_proper  : Find_Proper_Signature (@RightDistribute)   0 (∀ A f g            , Proper (SubsetOf-->(=)==>impl) (@RightDistribute   A f g            )). Proof. solve. Qed.
Lemma LeftCancellation_proper : Find_Proper_Signature (@LeftCancellation)  0 (∀ A op z           , Proper (SubsetOf-->(=)==>impl) (@LeftCancellation  A op z           )). Proof. solve. now apply ER. Qed.
Lemma RightCancellation_proper: Find_Proper_Signature (@RightCancellation) 0 (∀ A op z           , Proper (SubsetOf-->(=)==>impl) (@RightCancellation A op z           )). Proof. solve. now apply ER. Qed.

Lemma Absorption_proper : Find_Proper_Signature (@Absorption) 0
  (∀ A B C op1 op2, Proper (SubsetOf-->SubsetOf-->(=)==>impl) (@Absorption A B C op1 op2)).
Proof. red; intros; intros S1 S2 ES T1 T2 ET R1 R2 ER P ?; intros; unfold flip in *; apply ER; apply P; try apply _. Qed.

Hint Extern 0 (Find_Proper_Signature (@Associative      ) 0 _) => eexact Associative_proper      : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@Commutative      ) 0 _) => eexact Commutative_proper      : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@LeftIdentity     ) 0 _) => eexact LeftIdentity_proper     : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@RightIdentity    ) 0 _) => eexact RightIdentity_proper    : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@Absorption       ) 0 _) => eexact Absorption_proper       : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@LeftAbsorb       ) 0 _) => eexact LeftAbsorb_proper       : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@RightAbsorb      ) 0 _) => eexact RightAbsorb_proper      : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@LeftInverse      ) 0 _) => eexact LeftInverse_proper      : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@RightInverse     ) 0 _) => eexact RightInverse_proper     : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@Involutive       ) 0 _) => eexact Involutive_proper       : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@LeftDistribute   ) 0 _) => eexact LeftDistribute_proper   : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@RightDistribute  ) 0 _) => eexact RightDistribute_proper  : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@LeftCancellation ) 0 _) => eexact LeftCancellation_proper : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@RightCancellation) 0 _) => eexact RightCancellation_proper: typeclass_instances.

Local Existing Instance closed_range.
Local Existing Instance closed_binary.

(* We can also replace the equivalence relation by a weaker one. *)
Local Ltac solve2 := red; intros; intros R1 R2 ER P ?; intros; apply (ER _ _ _ _); apply P; apply _.
Lemma Associative_proper2    : Find_Proper_Signature (@Associative)     1 (∀ A f S               `{!Closed (S ⇀ S ⇀ S) f}                             , Proper ((SubRelation S)++>impl) (@Associative     A f S            )). Proof. solve2. Qed.
Lemma Commutative_proper2    : Find_Proper_Signature (@Commutative)     1 (∀ A B f S T           `{!Closed (S ⇀ S ⇀ T) f}                             , Proper ((SubRelation T)++>impl) (@Commutative     A B f S          )). Proof. solve2. Qed.
Lemma LeftIdentity_proper2   : Find_Proper_Signature (@LeftIdentity)    1 (∀ A op S `{x∊S}       `{!Closed (S ⇀ S ⇀ S) op}                            , Proper ((SubRelation S)++>impl) (@LeftIdentity    A A op x S       )). Proof. solve2. Qed.
Lemma RightIdentity_proper2  : Find_Proper_Signature (@RightIdentity)   1 (∀ A op S `{x∊S}       `{!Closed (S ⇀ S ⇀ S) op}                            , Proper ((SubRelation S)++>impl) (@RightIdentity   A A op x S       )). Proof. solve2. Qed.
Lemma Absorption_proper2     : Find_Proper_Signature (@Absorption)      1 (∀ A B C op1 op2 S T U `{!Closed (S ⇀ U ⇀ S) op1} `{!Closed (S ⇀ T ⇀ U) op2}, Proper ((SubRelation S)++>impl) (@Absorption      A B C op1 op2 S T)). Proof. solve2. Qed.
Lemma LeftAbsorb_proper2     : Find_Proper_Signature (@LeftAbsorb)      1 (∀ A B op S `{x∊T}     `{!Closed (T ⇀ S ⇀ T) op}                            , Proper ((SubRelation T)++>impl) (@LeftAbsorb      A B op x S       )). Proof. solve2. Qed.
Lemma RightAbsorb_proper2    : Find_Proper_Signature (@RightAbsorb)     1 (∀ A B op S `{x∊T}     `{!Closed (S ⇀ T ⇀ T) op}                            , Proper ((SubRelation T)++>impl) (@RightAbsorb     A B op x S       )). Proof. solve2. Qed.
Lemma LeftInverse_proper2    : Find_Proper_Signature (@LeftInverse)     1 (∀ A C op inv S `{u∊U} `{!Closed (S ⇀ S ⇀ U) op} `{!Closed (S ⇀ S) inv}     , Proper ((SubRelation U)++>impl) (@LeftInverse     A A C op inv u S )). Proof. solve2. Qed.
Lemma RightInverse_proper2   : Find_Proper_Signature (@RightInverse)    1 (∀ A C op inv S `{u∊U} `{!Closed (S ⇀ S ⇀ U) op} `{!Closed (S ⇀ S) inv}     , Proper ((SubRelation U)++>impl) (@RightInverse    A A C op inv u S )). Proof. solve2. Qed.
Lemma Involutive_proper2     : Find_Proper_Signature (@Involutive)      1 (∀ A f S               `{!Closed (S ⇀ S) f}                                 , Proper ((SubRelation S)++>impl) (@Involutive      A f S            )). Proof. solve2. Qed.
Lemma LeftDistribute_proper2 : Find_Proper_Signature (@LeftDistribute)  1 (∀ A f g S             `{!Closed (S ⇀ S ⇀ S) f} `{!Closed (S ⇀ S ⇀ S) g}    , Proper ((SubRelation S)++>impl) (@LeftDistribute  A f g S          )). Proof. solve2. Qed.
Lemma RightDistribute_proper2: Find_Proper_Signature (@RightDistribute) 1 (∀ A f g S             `{!Closed (S ⇀ S ⇀ S) f} `{!Closed (S ⇀ S ⇀ S) g}    , Proper ((SubRelation S)++>impl) (@RightDistribute A f g S          )). Proof. solve2. Qed.

Hint Extern 0 (Find_Proper_Signature (@Associative    ) 1 _) => eexact Associative_proper2     : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@Commutative    ) 1 _) => eexact Commutative_proper2     : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@LeftIdentity   ) 1 _) => eexact LeftIdentity_proper2    : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@RightIdentity  ) 1 _) => eexact RightIdentity_proper2   : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@Absorption     ) 1 _) => eexact Absorption_proper2      : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@LeftAbsorb     ) 1 _) => eexact LeftAbsorb_proper2      : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@RightAbsorb    ) 1 _) => eexact RightAbsorb_proper2     : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@LeftInverse    ) 1 _) => eexact LeftInverse_proper2     : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@RightInverse   ) 1 _) => eexact RightInverse_proper2    : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@Involutive     ) 1 _) => eexact Involutive_proper2      : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@LeftDistribute ) 1 _) => eexact LeftDistribute_proper2  : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@RightDistribute) 1 _) => eexact RightDistribute_proper2 : typeclass_instances.


Lemma TotalRelation_proper : Find_Proper_Signature (@TotalRelation) 0
  (∀ A, Proper (SubsetOf-->subrelation++>impl) (@TotalRelation A)).
Proof. intro. intros S1 S2 ES R1 R2 ER P x ? y ?. unfold flip in *.
  destruct (total R1 x y); [ left | right ]; now apply ER.
Qed.
Hint Extern 0 (Find_Proper_Signature (@TotalRelation) 0 _) => eexact TotalRelation_proper : typeclass_instances.

Lemma Trichotomy_proper : Find_Proper_Signature (@Trichotomy) 0
  (∀ A Ae, Proper (SubsetOf-->subrelation++>impl) (@Trichotomy A Ae)).
Proof. red. intros. intros S1 S2 ES R1 R2 ER P x ? y ?. unfold flip in *.
  destruct (trichotomy R1 x y) as [?|[?|?]]; [left|right;left|right;right];
  trivial; now apply ER.
Qed.
Hint Extern 0 (Find_Proper_Signature (@Trichotomy) 0 _) => eexact Trichotomy_proper : typeclass_instances.

Lemma unary_idempotency `{S:Subset} (f:S ⇀ S) `{Equiv S} `{!SubReflexive S (=)} `{!UnaryIdempotent S f} x `{x ∊ S} : f (f x) = f x.
Proof. now destruct (idempotency (S:=S ⇀ S) (∘) (f) _ _ (_ : Proper (S,=) x)). Qed.

Lemma unary_idempotent_morphism `{S:Subset} (f:S ⇀ S) `{Setoid _ (S:=S)} `{!UnaryIdempotent S f} : Morphism (S ⇒ S) f.
Proof. change (f = f). transitivity (f ∘ f); trivial. now symmetry. Qed.

Lemma UnaryIdempotent_proper : Find_Proper_Signature (@UnaryIdempotent) 0
  (∀ `{Setoid (S:=X)}, Proper ((@equiv (X ⇀ X) _) ==> impl) (UnaryIdempotent X)).
Proof. red; intros. intros f g E ?. do 2 red. now rewrite <- E. Qed.
Hint Extern 0 (Find_Proper_Signature (@UnaryIdempotent) 0 _) => eexact UnaryIdempotent_proper : typeclass_instances.

Lemma UnaryIdempotent_proper2 : Find_Proper_Signature (@UnaryIdempotent) 1
  (∀ A, Proper ((=)==>(=)==>eq==>impl) (@UnaryIdempotent A)).
Proof. red; intros. intros S1 S2 ES R1 R2 ER f g Ef P x y [[elx ely] E].
  rewrite <- Ef; clear dependent g.
  rewrite <-ES in elx, ely. apply ER in E.
  destruct (P _ _ (S1 $ E)).
  unfold compose. split. now rewrite <-ES. now apply ER.
Qed.
Hint Extern 0 (Find_Proper_Signature (@UnaryIdempotent) 1 _) => eexact UnaryIdempotent_proper2 : typeclass_instances.

Lemma BinaryIdempotent_proper : Find_Proper_Signature (@BinaryIdempotent) 0
  (∀ A op, Proper (SubsetOf-->subrelation++>impl) (@BinaryIdempotent A op)).
Proof. red; intros. intros S1 S2 ES R1 R2 ER P x el. unfold flip in *. red.
  rewrite ES in el. apply ER. now apply P.
Qed.
Hint Extern 0 (Find_Proper_Signature (@BinaryIdempotent) 0 _) => eexact BinaryIdempotent_proper : typeclass_instances.


Lemma right_id_from_left `{LeftIdentity A A op e (T:=M)} `{e ∊ M} `{!Setoid M}
  `{!Closed (M ⇀ M ⇀ M) op} `{!Commutative op M} : RightIdentity op e M.
Proof. intros x ?. rewrite_on M -> (commutativity op x e). exact (left_identity op x). Qed.

Lemma right_inv_from_left `{LeftInverse A A B op f e (T:=G)} `{e ∊ U} `{!Setoid U} 
  `{!Closed (G ⇀ G ⇀ U) op} `{!Commutative op G} `{!Closed (G ⇀ G) f} : RightInverse op f e G.
Proof. intros x ?. rewrite_on U -> (commutativity op x (f x)). exact (left_inverse op x). Qed.

Lemma right_absorb_from_left `{LeftAbsorb A A op e (T:=M)} `{e ∊ M} `{!Setoid M}
  `{!Closed (M ⇀ M ⇀ M) op} `{!Commutative op M} : RightAbsorb op e M.
Proof. intros x ?. rewrite_on M -> (commutativity op x e). exact (left_absorb op x). Qed.

Lemma right_distr_from_left `{LeftDistribute A f g (S:=R)} `{!Setoid R} 
  `{!Closed (R ⇀ R ⇀ R) f} `{!Morphism (R ⇒ R ⇒ R) g} `{!Commutative f R} : RightDistribute f g R.
Proof. intros x ? y ? z ?. rewrite 3!(R $ commutativity f _ z). exact (distribute_l _ _ _). Qed.

Lemma right_cancel_from_left `{Equiv} `{!Setoid R} `{!Closed (R ⇀ R ⇀ R) op} `{!Commutative op R}
 `{z ∊ R} `{!LeftCancellation op z R} : RightCancellation op z R.
Proof. intros x ? y ? E.
  apply (left_cancellation op z R); trivial.
  rewrite_on R -> (commutativity op z x).
  now rewrite_on R -> (commutativity op z y).
Qed.

Lemma ZeroProduct_proper : Find_Proper_Signature (@ZeroProduct) 0
  (∀ A Ae Amult Azero, Proper (SubsetOf-->impl) (@ZeroProduct A Ae Amult Azero)).
Proof. intro. intros. intros ?? ES P x ? y ?. unfold flip in ES.
  exact (zero_product x y).
Qed.
Hint Extern 0 (Find_Proper_Signature (@ZeroProduct) 0 _) => eexact ZeroProduct_proper : typeclass_instances.

Instance ZeroProduct_no_zero_divisors `{InequalitySetoid A (S:=R)} `{Mult A} `{Zero A} `{0 ∊ R} `{!ZeroProduct R} : NoZeroDivisors R.
Proof. intros x [[? xn0][y[[? yn0][E|E]]]];
  pose proof (uneq_ne _ _ xn0); pose proof (uneq_ne _ _ yn0);
  destruct (zero_product _ _ E); contradiction.
Qed.

Lemma ZeroDivisor_proper: Find_Proper_Signature (@ZeroDivisor) 0
  (∀ A Aue Ae Azero Amult, Proper (SubsetOf++>eq==>impl) (@ZeroDivisor A Aue Ae Azero Amult)).
Proof. red. intros. intros R1 R2 ES ?? Ex [?[y[??]]]. rewrite <-Ex.
  split. now rewrite <-ES. assert (y ∊ R2 ₀) by now rewrite <- ES. now exists_sub y.
Qed.
Hint Extern 0 (Find_Proper_Signature (@ZeroDivisor) 0 _) => eexact ZeroDivisor_proper : typeclass_instances.

Lemma NoZeroDivisors_proper: Find_Proper_Signature (@NoZeroDivisors) 0
  (∀ A Aue Ae Azero Amult, Proper (SubsetOf-->impl) (@NoZeroDivisors A Aue Ae Azero Amult)).
Proof. red. intros. intros ?? E P x. pose proof (P x) as Px.
  contradict Px. unfold flip in E. now rewrite <-E.
Qed.
Hint Extern 0 (Find_Proper_Signature (@NoZeroDivisors) 0 _) => eexact NoZeroDivisors_proper : typeclass_instances.

Lemma RingUnits_proper : Find_Proper_Signature (@RingUnits) 0
  (∀ A Ae Amult Aone, Proper (SubsetOf++>SubsetOf) (@RingUnits A Ae Amult Aone)).
Proof. intro. intros. intros ?? E x [?[y[??]]]. split. now rewrite <-E.
  exists y. split. now rewrite <-E. assumption.
Qed.
Hint Extern 0 (Find_Proper_Signature (@RingUnits) 0 _) => eexact RingUnits_proper : typeclass_instances.

Lemma RingUnits_subset `{Equiv} `{Mult _} `{One _} R : SubsetOf (RingUnits R) R. Proof. firstorder. Qed.
Hint Extern 2 (SubsetOf (RingUnits ?R) ?R) => eapply @RingUnits_subset : typeclass_instances. 
