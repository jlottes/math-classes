Require Import abstract_algebra interfaces.orders.
Require Export subset.

Lemma empty_setoid `{Equiv A} : Setoid (@bottom (@Subset A) _). Proof. firstorder. Qed.
Hint Extern 2 (Setoid ⊥) => eapply @empty_setoid : typeclass_instances.
Lemma empty_subsetoid `{Setoid (S:=X)} : ⊥ ⊆ X. Proof. firstorder. Qed.
Hint Extern 2 (⊥ ⊆ _) => eapply @empty_subsetoid : typeclass_instances.

Lemma equiv_proper : Find_Proper_Signature (@equiv) 0
  (∀ A Ae S `{@Setoid A Ae S}, Proper ((S,=)==>(S,=)==>impl) (=)).
Proof. red. intros. change (Proper ((S,=)==>(S,=)==>impl) (=)).
  intros x1 x2 Ex y1 y2 Ey P. unfold_sigs. subtransitivity y1. now subtransitivity x1. Qed.
Hint Extern 0 (Find_Proper_Signature (@equiv) 0 _) => eexact equiv_proper : typeclass_instances.

Lemma uneq_proper_fp : Find_Proper_Signature (@uneq) 0
  (∀ `{InequalitySetoid (S:=X)}, Proper ((X,=)==>(X,=)==>impl) (≠)).
Proof. red. intros. exact uneq_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@uneq) 0 _) => eexact uneq_proper_fp : typeclass_instances.

Instance default_uneq `{Equiv} : UnEq _ | 20 := (λ x y, ¬ x = y).
Typeclasses Opaque default_uneq.

Lemma default_uneq_denial `{Equiv} S : DenialInequality S.
Proof. easy. Qed.
Hint Extern 2 (@DenialInequality _ _ (@default_uneq _ _) _) => eapply @default_uneq_denial : typeclass_instances.

Instance: ∀ `{Equiv} `{UnEq _} S `{!Setoid S} `{!DenialInequality S}, InequalitySetoid S.
Proof. intros. split; try apply _; [ intros ?? E1 ?? E2; unfold_sigs; unfold impl | intros ???? ..];
  setoid_rewrite (denial_inequality _ _); try tauto.
  intro P. contradict P. now rewrite_on S -> E1, E2.
Qed.

Instance: ∀ `{Equiv} `{UnEq _} S `{!Setoid S} `{!DenialInequality S} `{!SubDecision S S (=)}, TightApart S.
Proof. intros. intros x ? y ?. rewrite (denial_inequality _ _).
  split. unfold SubDecision in *|-. apply stable. tauto.
Qed.

Lemma Setoid_proper : Find_Proper_Signature (@Setoid) 0
  (∀ A, Proper ((=)==>SubsetOf-->impl) (@Setoid A)).
Proof. red. intros. intros ?? Ee ?? ES. exact (SubEquivalence_proper _ _ _ ES _ _ Ee). Qed.
Hint Extern 0 (Find_Proper_Signature (@Setoid) 0 _) => eexact Setoid_proper : typeclass_instances.

Local Hint Extern 20 (?x ∊ ?T) => match goal with
  | sub : SubsetOf _ ?T |- _ => eapply (subset (SubsetOf:=sub) x)
end : typeclass_instances.

Lemma InequalitySetoid_proper : Find_Proper_Signature (@InequalitySetoid) 0
  (∀ A, Proper ((=)==>(=)==>SubsetOf-->impl) (@InequalitySetoid A)).
Proof. red. intros. intros ?? Ee ?? Eu S1 S2 ES ?. unfold flip in ES. split.
+ rewrite <- Ee, ES. apply _.
+ intros ?? E1 ?? E2 E. unfold_sigs. apply Ee in E1. apply Ee in E2. apply Eu in E.
  apply Eu. exact (uneq_proper _ _ (S1 $ E1) _ _ (S1 $ E2) E).
+ intros ???? E1 E2. apply Eu in E1. apply Ee in E2. exact (uneq_ne _ _ E1 E2).
+ intros ???? E1 E2. apply Ee in E1. apply Eu in E2. exact (equiv_nue _ _ E1 E2).
Qed.
Hint Extern 0 (Find_Proper_Signature (@InequalitySetoid) 0 _) => eexact InequalitySetoid_proper : typeclass_instances.

Lemma subsetoid_alt {A} S T `{Equiv A} `{!Setoid T}
  : Proper ((T,=) ==> impl) (∊ S) → SubsetOf S T →  S ⊆ T.
Proof. intros. split; try apply _. rewrite (_:SubsetOf S T). apply _. Qed.

Lemma subsetoid_subset_subrel `{Equiv} : subrelation (⊆) SubsetOf.
Proof. firstorder. Qed.

Hint Extern 2 (subrelation (⊆) SubsetOf) => eapply @subsetoid_subset_subrel : typeclass_instances.
Hint Extern 2 (Find_Proper_Subrelation (⊆) SubsetOf) => eapply @subsetoid_subset_subrel : typeclass_instances.

Hint Extern 19 (?x ∊ ?T) => match goal with
  | sub : SubSetoid _ ?T |- _ => eapply (subset (SubsetOf:=subsetoid_subset (SubSetoid:=sub)) x)
end : typeclass_instances.

Lemma element_proper2 : Find_Proper_Signature (@Element) 1
  (∀ `{Equiv} `{X ⊆ Y}, Proper ((Y,=)==>impl) (∊ X)).
Proof. red. intros. exact subsetoid_regular. Qed.
Hint Extern 0 (Find_Proper_Signature (@Element) 1 _) => eexact element_proper2 : typeclass_instances.

Lemma subsetoid_proper : Find_Proper_Signature (@SubSetoid) 0
  (∀ A, Proper ((=)==>(=)==>(=)==>impl) (@SubSetoid A)).
Proof. red. intros. intros e1 e2 E1 ?? E2 X Y E3 S. split.
+ rewrite <- E1, <- E2. exact subsetoid_a.
+ rewrite <- E1, <- E3. exact subsetoid_b.
+ intros a b [[ela elb] E4]. rewrite <- E3 in ela,elb. rewrite <- E2.
  assert (@equiv _ e1 a b) as E' by now apply E1. intro. now rewrite <- (X $ E').
+ rewrite <- E2, <- E3. exact subsetoid_subset.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SubSetoid) 0 _) => eexact subsetoid_proper : typeclass_instances.

Lemma subsetoid_from_subsetof `(X:Subset) `{Setoid _ (S:=X)} S T `{S ⊆ X} `{T ⊆ X}
  : SubsetOf S T → S ⊆ T.
Proof. split; try apply _. Qed.


Hint Extern 0 (?S ∊ Setoid) => red : typeclass_instances.

Lemma Setoid_subsetoid `{Equiv} : Setoid ⊆ (every Subset).
Proof. apply subsetoid_alt; try apply _.
  intros S1 S2 [_ ES]. change (Setoid S1 -> Setoid S2). intro. now rewrite <- ES.
Qed.
Hint Extern 2 ((Setoid) ⊆ (every Subset)) => eapply @Setoid_subsetoid : typeclass_instances.
Hint Extern 2 (Setoid Setoid) => eapply (subsetoid_a (T:=every _)) : typeclass_instances.

Lemma SubSetoid_trans `{Equiv} : Transitive SubSetoid.
Proof. intros S1 S2 S3 P1 P2. apply subsetoid_alt. apply subsetoid_b.
  intros x y E ?. unfold_sigs. assert (y∊S2). rewrite_on S3 <- E. apply _. now rewrite_on S2 <- E.
  transitivity S2; apply _.
Qed.
Hint Extern 0 (Transitive SubSetoid) => eapply @SubSetoid_trans : typeclass_instances.
Hint Extern 2 (SubTransitive    _ SubSetoid) => eapply @every_SubTransitive  : typeclass_instances.

Lemma SubSetoid_antisym `{Equiv} : AntiSymmetric (=) SubSetoid.
Proof. intros S1 S2 P1 P2. apply (antisymmetry SubsetOf); apply _. Qed.
Hint Extern 0 (AntiSymmetric _ SubSetoid) => eexact SubSetoid_antisym : typeclass_instances.
Hint Extern 2 (SubAntiSymmetric _ SubSetoid) => eapply @every_SubAntiSymmetric  : typeclass_instances.

Lemma Setoid_partialorder `{Equiv} : PartialOrder (Ale:=SubSetoid) Setoid.
Proof. split; unfold le; try apply _. firstorder. Qed.
Hint Extern 2 (PartialOrder Setoid) => eapply @Setoid_partialorder : typeclass_instances.

(*
Hint Extern 5 (SubReflexive     _ SubSetoid) => eapply @po_refl    : typeclass_instances.
Hint Extern 5 (SubTransitive    _ SubSetoid) => eapply @po_trans   : typeclass_instances.
Hint Extern 5 (SubAntiSymmetric _ SubSetoid) => eapply @po_antisym : typeclass_instances.
*)
(* The underscores above will already need to be resolved by the time these hints are consulted *)

Hint Extern 31 (@Subset Subset) => eexact (every _) : typeclass_instances.
Hint Extern 30 (@Subset Subset) => eexact Setoid : typeclass_instances.
(* We can extend this list later with other structures *)

Hint Extern 5 (SubsetOf _ Setoid) => intros ?; unfold Element; intro; exact _ : typeclass_instances.

Lemma SubSetoid_refl `{Equiv} C `{sub:!SubsetOf C Setoid} : SubReflexive C SubSetoid.
Proof. rewrite sub. eapply @po_refl. apply _. Qed.
Hint Extern 5 (SubReflexive _ SubSetoid) => eapply @SubSetoid_refl : typeclass_instances.


Lemma subsetoid_refl `{Setoid (S:=X)} : X ⊆ X.  Proof. subreflexivity. Qed.
Hint Extern 5 (SubSetoid ?X ?X) => eapply @subsetoid_refl : typeclass_instances.
Hint Extern 2 (Proper (⊆) _) => red : typeclass_instances.
Hint Extern 2 (ProperProxy (⊆) _) => red : typeclass_instances.
Hint Extern 2 (Find_Proper_Proper (⊆) _) => red : typeclass_instances.

Lemma subset_singleton_element `{Setoid (S:=X)} x `{x ∊ X} : x ∊ {{x}}.
Proof. assert (x=x) by subreflexivity. firstorder. Qed.
Hint Extern 2 (?x ∊ {{?x}}) => eapply @subset_singleton_element: typeclass_instances.

Lemma subset_singleton_subsetoid `{Setoid (S:=X)} x `{x ∊ X} : {{x}} ⊆ X.
Proof. apply subsetoid_alt; [ apply _ | | firstorder ].
  intros y z E [? E2]. split. now rewrite <- E. unfold_sigs. now subtransitivity y.
Qed.
Hint Extern 2 ((subset_singleton ?X _) ⊆ ?X) => eapply @subset_singleton_subsetoid : typeclass_instances.

Lemma subset_singleton_setoid `{Setoid (S:=X)} x `{x ∊ X} : Setoid {{x}}.
Proof subsetoid_a.
Hint Extern 2 (Setoid {{_}}) => eapply @subset_singleton_setoid : typeclass_instances.


Lemma subsetoid_eq_singleton `{Equiv} S `{S ⊆ X} x `{x ∊ X} :
  S = {{x | X }} ↔ (∃ y, y ∊ S) ∧ ∀ `{y ∊ S}, y = x.
Proof. pose proof subsetoid_b. split.
+ intro E. split. exists x. rewrite E. apply _. intros ? el. rewrite E in el. now destruct el.
+ intros [[z E] P]. intro y. split. intro. split. apply _. now apply P.
  intros [? el]. now rewrite_on X -> el, <- ( P z _ ).
Qed.

Lemma projected_setoid `{X:Subset} `{Equiv X} `{Setoid (S:=Y)} (f : X ⇀ Y) `{!Closed (X ⇀ Y) f}
  (eq_correct : ∀ `{x ∊ X} `{y ∊ X}, x = y ↔ f x = f y) : Setoid X.
Proof. pose proof @closed_range.
  split; red; [ intros ?? | intros ???? | intros ?? y ? ?? ]; rewrite ?(eq_correct _ _ _ _);
  intros. easy. subsymmetry. subtransitivity (f y).
Qed.

(* symmetry and transitivity of extensional equality *)

Lemma ext_equiv_symmetric
  `(X:Subset) `{Equiv X} `{!SubSymmetric X (=)}
  `(Y:Subset) `{Equiv Y} `{!SubSymmetric Y (=)}
 : Symmetric (@equiv (X ⇀ Y) _).
Proof. intros f g E x y E2. symmetry. apply E. now symmetry. Qed.
Hint Extern 2 (Symmetric ext_equiv) => eapply @ext_equiv_symmetric : typeclass_instances.
Hint Extern 2 (Symmetric (@equiv _ ext_equiv)) => eapply @ext_equiv_symmetric : typeclass_instances.
Hint Extern 2 (Find_Proper_Symmetric ext_equiv) => eapply @ext_equiv_symmetric : typeclass_instances.
Hint Extern 2 (Find_Proper_Symmetric (@equiv _ ext_equiv)) => eapply @ext_equiv_symmetric : typeclass_instances.

Lemma ext_equiv_subsymmetric
  `(X:Subset) `{Equiv X} `{!SubSymmetric X (=)}
  `(Y:Subset) `{Equiv Y} `{!SubSymmetric Y (=)}
 : SubSymmetric (X ⇀ Y) (@equiv (X ⇀ Y) _).
Proof every_SubSymmetric _.
Hint Extern 2 (SubSymmetric _ (@equiv _ ext_equiv)) => eapply @ext_equiv_subsymmetric : typeclass_instances.

Lemma ext_equiv_transitive
  `(X:Subset) `{Equiv X} `{!SubReflexive X (=)} `{!SubTransitive X (=)}
  `(Y:Subset) `{Equiv Y} `{!SubTransitive Y (=)}
 : Transitive (@equiv (X ⇀ Y) _).
Proof. intros f g h E1 E2 x y E3. transitivity (g x). unfold_sigs. apply E1. now red_sig. now apply E2. Qed.
Hint Extern 2 (Transitive ext_equiv) => eapply @ext_equiv_transitive : typeclass_instances.
Hint Extern 2 (Transitive (@equiv _ ext_equiv)) => eapply @ext_equiv_transitive : typeclass_instances.

Lemma ext_equiv_subtransitive
  `(X:Subset) `{Equiv X} `{!SubReflexive X (=)} `{!SubTransitive X (=)}
  `(Y:Subset) `{Equiv Y} `{!SubTransitive Y (=)}
 : SubTransitive (X ⇀ Y) (@equiv (X ⇀ Y) _).
Proof every_SubTransitive _.
Hint Extern 2 (SubTransitive _ (@equiv _ ext_equiv)) => eapply @ext_equiv_subtransitive : typeclass_instances.

Lemma ext_equiv_subrelation
  `(X1:Subset) {ex1:Equiv X1} (X2:Subset) {ex2:Equiv X2} `{!SubsetOf X1 X2} {Rx:SubRelation X1 ex1 ex2}
  `(Y1:Subset) {ey1:Equiv Y1} (Y2:Subset) {ey2:Equiv Y2} `{!SubsetOf Y1 Y2} {Ry:SubRelation Y1 ey1 ey2}
 : subrelation (@ext_equiv _ X2 _ Y1 ex2 ey1) (@ext_equiv _ X1 _ Y2 ex1 ey2).
Proof. intros f g E ?? [[??]Ex]. pose proof (E _ _ (X2 $ Rx _ _ _ _ Ex)).
  unfold_sigs. red_sig. now apply Ry.
Qed.
Hint Extern 2 (subrelation ext_equiv ext_equiv) => eapply @ext_equiv_subrelation : typeclass_instances.
Hint Extern 2 (SubRelation _ ext_equiv ext_equiv) => eapply @every_SubRelation : typeclass_instances.

Lemma morphism_subset
  `(X1:Subset) {ex1:Equiv X1} (X2:Subset) {ex2:Equiv X2} `{!SubsetOf X1 X2} {Rx:SubRelation X1 ex1 ex2}
  `(Y1:Subset) {ey1:Equiv Y1} (Y2:Subset) {ey2:Equiv Y2} `{!SubsetOf Y1 Y2} {Ry:SubRelation Y1 ey1 ey2}
 : SubsetOf (@morphism _ _ X2 Y1 ex2 ey1) (@morphism _ _ X1 Y2 ex1 ey2).
Proof λ f m, @ext_equiv_subrelation _ X1 ex1 X2 ex2 _ _ _ Y1 ey1 Y2 ey2 _ _ f f m.
Hint Extern 3 (SubsetOf (_ ⇒ _) (_ ⇒ _)) => eapply @morphism_subset : typeclass_instances.

(* we get binary and higher for free *)
Section ext_equiv_binary.
  Context `{Setoid (S:=X)} `{Setoid (S:=Y)} `{Setoid (S:=Z)}.

  Let s : Symmetric (@equiv (X ⇀ Y ⇀ Z) _) := _.
  Let t : Transitive (@equiv (X ⇀ Y ⇀ Z) _) := _.
End ext_equiv_binary.

Lemma ext_equiv_binary_sig `{X:Subset} `{Equiv X} `{Setoid (S:=Y)} `{Z:Subset} `{Equiv Z}
  {f g : X ⇀ Y ⇀ Z} : f = g ↔ ((X,=) ==> (Y,=) ==> (Z,=))%signature f g.
Proof. split.
+ intro E. intros x1 x2 Ex. now destruct (E x1 x2 Ex).
+ intro E. intros x1 x2 Ex. split. split.
  * intros y1 ?. now destruct (E _ _ Ex _ _ (_:Proper (Y,=) y1)).
  * intros y2 ?. now destruct (E _ _ Ex _ _ (_:Proper (Y,=) y2)).
  * intros y1 y2 Ey. now apply E.
Qed.

Lemma ext_equiv_binary_applied `{Setoid (S:=X)} `{Setoid (S:=Y)} `{Z:Subset} `{Equiv Z}
  {f g : X ⇀ Y ⇀ Z} (E:f = g) x `{x ∊ X} y `{y ∊ Y} : f x y = g x y.
Proof. rewrite ext_equiv_binary_sig in E.
  now destruct (E _ _ (_:Proper (X,=) x) _ _ (_:Proper (Y,=) y)).
Qed.

Lemma compose_proper : Find_Proper_Signature (@compose) 0
  (∀ `{Equiv A} `{Equiv B} `{Equiv C} {X:@Subset A} {Y:@Subset B} {Z:@Subset C},
   Proper ((@equiv (Y ⇀ Z) _) ==> (@equiv (X ⇀ Y) _) ==> (@equiv (X ⇀ Z) _)) compose).
Proof. red; intros. intros ?? Eg ?? Ef ???. now apply Eg, Ef. Qed.
Hint Extern 0 (Find_Proper_Signature (@compose) 0 _) => eexact compose_proper : typeclass_instances.

Lemma uncurry_proper : Find_Proper_Signature (@uncurry) 0
  (∀ `{Equiv A} `{Equiv B} `{Equiv C} {X:@Subset A} {Y:@Subset B} {Z:@Subset C},
   Proper ((@equiv (X ⇀ Y ⇀ Z) _) ==> (@equiv (X * Y ⇀ Z) _)) uncurry).
Proof. red; intros. intros ?? Ef [??][??][[[??][??]][??]].
  unfold uncurry. apply Ef; now red_sig.
Qed.
Hint Extern 0 (Find_Proper_Signature (@uncurry) 0 _) => eexact uncurry_proper : typeclass_instances.

Lemma curry_proper : Find_Proper_Signature (@curry) 0
  (∀ `{Equiv A} `{Equiv B} `{Equiv C} {X:@Subset A} {Y:@Subset B} {Z:@Subset C} `{!Setoid Y},
   Proper ((@equiv (X * Y ⇀ Z) _) ==> (@equiv (X ⇀ Y ⇀ Z) _)) curry).
Proof. red; intros. intros f g Ef. rewrite ext_equiv_binary_sig.
  intros ?? Ex ?? Ey. unfold curry. apply Ef. unfold_sigs. repeat (split; trivial; try apply _).
Qed.
Hint Extern 0 (Find_Proper_Signature (@curry) 0 _) => eexact curry_proper : typeclass_instances.


Lemma Morphism_proper : Find_Proper_Signature (@Morphism) 0
  (∀ A, Proper (SubsetOf ++> eq ==> impl) (@Morphism A)).
Proof element_proper.
Hint Extern 0 (Find_Proper_Signature (@Morphism) 0 _) => eexact Morphism_proper : typeclass_instances.


Lemma morphism_closed_subset `{Setoid (S:=X)} `{Y:Subset} `{Equiv Y}
  : SubsetOf (X ⇒ Y) (X ⇀ Y).
Proof. intros f m x ?. now destruct (m x x (_ : Proper (X,=) x)). Qed.
Hint Extern 10 (SubsetOf (?X ⇒ ?Y) (?X ⇀ ?Y)) => eapply @morphism_closed_subset : typeclass_instances.

Lemma binary_morphism_closed_subset `{Setoid (S:=X)} `{Setoid (S:=Y)} `{Z:Subset} `{Equiv Z}
  : SubsetOf (X ⇒ Y ⇒ Z) (X ⇀ Y ⇀ Z).
Proof. transitivity (X ⇀ Y ⇒ Z). apply _.
  intros f m. now rewrite <- (_ : SubsetOf (Y ⇒ Z) (Y ⇀ Z)).
Qed.
Hint Extern 9 (SubsetOf (?X ⇒ ?Y ⇒ ?Z) (?X ⇀ ?Y ⇀ ?Z)) => eapply @binary_morphism_closed_subset : typeclass_instances.

Instance morphism_closed `{Setoid (S:=X)} `{Y:Subset} `{Equiv Y} f {m:Morphism (X ⇒ Y) f} : Closed (X ⇀ Y) f | 10.
Proof. now rewrite <- (_ : SubsetOf (X ⇒ Y) (X ⇀ Y)). Qed.

Instance binary_morphism_closed `{Setoid (S:=X)} `{Setoid (S:=Y)} `{Z:Subset} `{Equiv Z}
  f {m:Morphism (X ⇒ Y ⇒ Z) f} : Closed (X ⇀ Y ⇀ Z) f | 9.
Proof. now rewrite <- (_ : SubsetOf (X ⇒ Y ⇒ Z) (X ⇀ Y ⇀ Z)). Qed.

Instance submorphism_1 `{Setoid (S:=X)} `{Y:Subset} `{Equiv Y} `{Z:Subset} `{Equiv Z}
  f {m:Morphism (X ⇒ Y ⇒ Z) f} x `{x ∊ X} : Morphism (Y ⇒ Z) (f x) | 10.
Proof. now destruct (m x x (_:Proper (X,=) x)). Qed.

Lemma submorphism_2 `{X:Subset} `{Equiv X} `{Setoid (S:=Y)} `{Z:Subset} `{Equiv Z}
  f {m:Morphism (X ⇒ Y ⇒ Z) f} y `{y ∊ Y} : Morphism (X ⇒ Z) (λ x, f x y).
Proof. intros ?? Ex. apply (m _ _ Ex). now red_sig. Qed.
Hint Extern 5 (Morphism _ (λ x, ?f x _)) => eapply @submorphism_2 : typeclass_instances.

Instance morphism_proper `{X:Subset} `{Equiv X} `{Y:Subset} `{Equiv Y}
  f {m:Morphism (X ⇒ Y) f} : Proper ((X,=) ==> (Y,=)) f.
Proof m.

Instance binary_morphism_proper `{X:Subset} `{Equiv X} `{Setoid (S:=Y)} `{Z:Subset} `{Equiv Z}
  f {m:Morphism (X ⇒ Y ⇒ Z) f} : Proper ((X,=) ==> (Y,=) ==> (Z,=)) f.
Proof. intros ?? Ex ?? Ey. destruct (m _ _ Ex) as [[??] E]. now apply E. Qed.

Lemma binary_morphism_proper_back `{Setoid (S:=X)} `{Setoid (S:=Y)} `{Z:Subset} `{Equiv Z}
  f : Proper ((X,=) ==> (Y,=) ==> (Z,=)) f → Morphism (X ⇒ Y ⇒ Z) f.
Proof. intros P x1 x2 Ex. split. unfold_sigs. split; apply P; now red_sig. now apply P. Qed.

Lemma binary_morphism_ext_equiv `{Setoid (S:=X)} `{Setoid (S:=Y)} `{Z:Subset} `{Equiv Z}
  (f : X ⇀ Y ⇀ Z) : Morphism (X ⇒ Y ⇒ Z) f ↔ f = f.
Proof. split.
+ intro. rewrite ext_equiv_binary_sig. exact (binary_morphism_proper f).
+ intro. apply binary_morphism_proper_back. red. now rewrite <- ext_equiv_binary_sig.
Qed.

Lemma extensionally_equal `{Setoid (S:=X)} `{Setoid (S:=Y)} (f g : X ⇒ Y) `{x ∊ X} `{y ∊ X}
  : f = g → x = y → f x = g y.
Proof. intros Ef Ex. apply Ef. exact (X $ Ex). Qed.

Lemma extensionality `{Setoid (S:=X)} `{Setoid (S:=Y)} f {m:Morphism (X ⇒ Y) f} `{x ∊ X} `{y ∊ X}
  : x = y → f x = f y.
Proof. now apply extensionally_equal. Qed.

Hint Extern 0 (?f ∊ Morphism ?S) => eexact (_ : Morphism S f) : typeclass_instances.

Lemma morphism_setoid `(X:Subset) `{Equiv X} `{!Setoid X} `(Y:Subset) `{Equiv Y} `{!Setoid Y}
  : @Setoid (X ⇒ Y) _ (X ⇒ Y).
Proof. split.
+ now intros f ?.
+ exact (every_SubSymmetric _).
+ exact (every_SubTransitive _).
Qed.
Hint Extern 2 (Setoid (?X ⇒ ?Y)) => eapply (morphism_setoid X Y) : typeclass_instances.
Hint Extern 30 (@Subset (elt_type (?X ⇒ ?Y))) => eapply ((X ⇒ Y) : Subset) : typeclass_instances.
Hint Extern 30 (@Subset (elt_type (?X ⇀ ?Y))) => eapply ((X ⇒ Y) : Subset) : typeclass_instances.
Hint Extern 2 (@SubEquivalence (elt_type (?X ⇒ ?Y)) _ (@equiv _ ext_equiv)) => eapply (morphism_setoid X Y) : typeclass_instances.
Hint Extern 2 (@SubReflexive (elt_type (?X ⇒ ?Y)) _ (@equiv _ ext_equiv)) => eapply @subequiv_reflexive : typeclass_instances.
Hint Extern 2 (@Setoid (_ → _) (@ext_equiv _ ?X _ ?Y _ _) _) => eapply (morphism_setoid X Y) : typeclass_instances.

Lemma binary_extensionality `{Setoid (S:=X)} `{Setoid (S:=Y)} `{Setoid (S:=Z)}
 (f:X ⇀ Y ⇀ Z) `{!Morphism (X ⇒ Y ⇒ Z) f} `{x ∊ X} `{y ∊ X} `{a ∊ Y} `{b ∊ Y}
 : x = y → a = b → f x a = f y b.
Proof. intros ??. apply (extensionally_equal _ _); [ apply extensionally_equal|..]; trivial. Qed.

Lemma id_morphism `{X:Subset} `{Equiv X} : Morphism (X ⇒ X) id.  Proof. firstorder. Qed.
Hint Extern 2 (Morphism (?X ⇒ ?X) id) => eapply (@id_morphism _ X) : typeclass_instances.

Lemma id_morphism2
 `(X1:Subset) {ex1:Equiv X1} (X2:Subset) {ex2:Equiv X2} `{!SubsetOf X1 X2} {Rx:SubRelation X1 ex1 ex2}
 : Morphism (@morphism _ _ X1 X2 ex1 ex2) id.
Proof. rewrite <- (_ : SubsetOf (@morphism _ _ X1 X1 ex1 ex1) (@morphism _ _ X1 X2 ex1 ex2)). apply _. Qed.
Hint Extern 5 (Morphism _ id) => eapply @id_morphism2 : typeclass_instances.

Lemma const_morphism `(X:Subset) `{Equiv X} `{Setoid (S:=Y)} c `{c ∊ Y}
  : Morphism (X ⇒ Y) (λ _, c).
Proof. intros _ _ _. now red_sig. Qed.
Hint Extern 5 (Morphism _ (λ _, ?c)) => eapply @const_morphism : typeclass_instances.

Lemma compose_morphism `{X:Subset} `{Y:Subset} `{Z:Subset} (f:X ⇀ Y) (g:Y ⇀ Z) `{Equiv X} `{Equiv Y} `{Equiv Z}
  {mf:Morphism (X ⇒ Y) f} {mg:Morphism (Y ⇒ Z) g} : Morphism (X ⇒ Z) (g ∘ f).
Proof. intros ?? Ex. apply mg. now apply mf. Qed.
Hint Extern 4 (Morphism _ (_ ∘ _)) => class_apply @compose_morphism : typeclass_instances.

Lemma uncurry_closed `{X:Subset} `{Y:Subset} `{Z:Subset} f {cf:Closed (X ⇀ Y ⇀ Z) f} : Closed (X * Y ⇀ Z) (uncurry f).
Proof. intros [??][??]. unfold uncurry. now apply cf. Qed.
Hint Extern 8 (Closed _ (uncurry _)) => class_apply @uncurry_closed : typeclass_instances.

Lemma uncurry_morphism `{X:Subset} `{Y:Subset} `{Z:Subset} (f:X ⇀ Y ⇀ Z) `{Equiv X} `{Equiv Y} `{Equiv Z}
  {mf:Morphism (X ⇒ Y ⇒ Z) f} : Morphism (X * Y ⇒ Z) (uncurry f).
Proof. intros [??][??] [[[??][??]][??]]. unfold uncurry. apply mf; now red_sig. Qed.
Hint Extern 4 (Morphism _ (uncurry _)) => class_apply @uncurry_morphism : typeclass_instances.

Lemma curry_closed `{X:Subset} `{Y:Subset} `{Z:Subset} f {cf:Closed (X * Y ⇀ Z) f} : Closed (X ⇀ Y ⇀ Z) (curry f).
Proof. intros ????. unfold curry. apply cf. now split. Qed.
Hint Extern 8 (Closed _ (curry _)) => class_apply @curry_closed : typeclass_instances.

Lemma curry_morphism `{Setoid (S:=X)} `{Setoid (S:=Y)} `{Z:Subset} (f:X * Y ⇀ Z) `{Equiv Z}
  {mf:Morphism (X * Y ⇒ Z) f} : Morphism (X ⇒ Y ⇒ Z) (curry f).
Proof. apply binary_morphism_proper_back. intros ??[[??]?] ??[[??]?].
  unfold curry. apply mf. repeat (split; trivial; try apply _). Qed.
Hint Extern 4 (Morphism _ (curry _)) => class_apply @curry_morphism : typeclass_instances.


Lemma Closed_proper2 : Find_Proper_Signature (@Closed) 1
  (∀ A B `{Equiv A} `{Equiv B} {X:@Subset A} {Y:@Subset B} `{!SubReflexive X (=)},
    Proper ((@equiv (X ⇀ Y) _) ==> impl) (Closed (X ⇀ Y))).
Proof. red; intros. intros f g E ?. intros x ?.
  destruct (E x x) as [[??]_]. now red_sig. assumption.
Qed.
Hint Extern 0 (Find_Proper_Signature (@Closed) 1 _) => eexact Closed_proper2 : typeclass_instances.

Lemma Morphism_proper2 : Find_Proper_Signature (@Morphism) 1
  (∀ `{Setoid (S:=X)} `{Setoid (S:=Y)},
     Proper ((@equiv (X ⇀ Y) _) ==> impl) (Morphism (X ⇒ Y))).
Proof. red. intros. intros f g E ?.
  change (g=g). transitivity f; [symmetry|]; trivial.
Qed.
Hint Extern 0 (Find_Proper_Signature (@Morphism) 1 _) => eexact Morphism_proper2 : typeclass_instances.

Hint Extern 7 (_ ∊ _) =>
  match goal with
  | |- ?f ?x ∊ ?Y =>
    match type of f with
    | elt_type (_ ⇀ _) =>
      let A := type of x in
      let S := fresh "S" in evar (S:@Subset A);
      let D := eval unfold S in S in clear S;
      let e' := fresh "e" in evar (e':Equiv D);
      let e := eval unfold e' in e' in clear e';
      let m := fresh "m" in assert (Morphism (@morphism _ _ D Y e _) f) as m by
        solve [ typeclasses eauto | apply _ ];
      eapply (morphism_closed f (m:=m))
    end
  | |- ?f ?x ?y ∊ ?Z =>
    match type of f with
    | elt_type (_ ⇀ _ ⇀ _) =>
      let A := type of x in
      let B := type of y in
      let S := fresh "S" in evar (S:@Subset A);
      let D1 := eval unfold S in S in clear S;
      let S := fresh "S" in evar (S:@Subset B);
      let D2 := eval unfold S in S in clear S;
      let e' := fresh "e" in evar (e':Equiv D1);
      let e1 := eval unfold e' in e' in clear e';
      let e' := fresh "e" in evar (e':Equiv D2);
      let e2 := eval unfold e' in e' in clear e';
      let m := fresh "m" in assert (Morphism (@morphism _ _ D1 (@morphism _ _ D2 Z e2 _) e1 _) f) as m by
        solve [ typeclasses eauto | apply _ ];
      eapply (binary_morphism_closed f (m:=m))
    end
  end : typeclass_instances.

Section images.
  Context `{Setoid (S:=X)} `{Setoid (S:=Y)} (f:X ⇀ Y) `{!Morphism (X ⇒ Y) f}.

  Instance image_element {S} `{!SubsetOf S X} x `{x ∊ S} : f x ∊ f⁺¹(S).
  Proof. split. apply _. now exists_sub x. Qed.

  Instance subsetof_image {S} `{!SubsetOf S X} : SubsetOf f⁺¹(S) Y. Proof. firstorder. Qed.
  Instance subsetof_inv_image `{!SubsetOf T Y} : SubsetOf f⁻¹(T) X. Proof. now intros ?[??]. Qed.

  Instance subsetoid_image {S} `{!SubsetOf S X} : f⁺¹(S) ⊆ Y.
  Proof with try apply _. apply subsetoid_alt... intros y1 y2 E [_ [x [? E2]]]. unfold_sigs.
    split... exists_sub x. subtransitivity y1.
  Qed.

  Instance subsetoid_inv_image `{T ⊆ Y} : f⁻¹(T) ⊆ X.
  Proof with try apply _. apply subsetoid_alt... intros x1 x2 E [_?]. unfold_sigs.
    split... assert (f x2 = f x1) as E2. now rewrite_on X -> E. now rewrite_on Y -> E2.
  Qed.

  Lemma setoid_image     S `{!SubsetOf S X} : Setoid f⁺¹(S). Proof subsetoid_a.
  Lemma setoid_inv_image T `{T ⊆ Y}         : Setoid f⁻¹(T). Proof subsetoid_a.

  Lemma image_empty : f⁺¹(⊥) = ⊥. Proof. firstorder. Qed.

  Lemma image_inhabited S `{!SubsetOf S X} `{!Inhabited S} : Inhabited f⁺¹(S).
  Proof. destruct (inhabited S) as [x ?]. exists (f x). apply _. Qed.

  Lemma image_eq_singleton S `{!SubsetOf S X} y `{y ∊ Y}
    : f⁺¹(S) = {{y}} ↔ (∃ x, x ∊ S) ∧ ∀ `{x ∊ S}, f x = y.
  Proof. rewrite (subsetoid_eq_singleton f⁺¹(S) y). split.
  + intros [[y' [? [x [? E]]]] P]. split. now exists x. intros x' ?. apply (P (f x') _).
  + intros [[x ?] P]. split. exists (f x). apply _. intros y' [? [x' [? E]]]. rewrite_on Y <- E. exact (P x' _).
  Qed.

  Lemma inv_image_eq_singleton T `{T ⊆ Y} x `{x ∊ X}
    : f⁻¹(T) = {{x}} ↔ f x ∊ T ∧ ∀ `{x' ∊ X}, f x' ∊ T → x' = x.
  Proof. split.
  + intros E. split. cut (x ∊ f⁻¹(T)). firstorder. rewrite E. apply _.
    intros x' ? ?. assert (x' ∊ f⁻¹(T)) as el by now split. rewrite E in el. now destruct el.
  + intros [? P] x'. split. intros [??]. pose proof (P x' _ _). now split.
    intros [? E]. split. apply _. now rewrite_on X -> E.
  Qed.

  Lemma subimage_image {S} `{!SubsetOf S X} {T} `{!SubsetOf T S} :
    (@image _ S _ (@image _ X _ Y _ f S) _ f T) = f⁺¹(T).
  Proof. intro y. split.
  + intros [[??]?]. now split.
  + intros [?[x[? E]]]. split. split. apply _. now exists_sub x. now exists_sub x.
  Qed.

  Lemma image_dom_range_proper X2 Y2 `{Y ⊆ Y2} S `{!SubsetOf S X}
    : f⁺¹(S) = (image (X:=X2) (Y:=Y2) f S).
  Proof. intro y. split.
  + intros [?[x[? E]]]. split. apply _. now exists_sub x.
  + intros [?[x[? E]]]. split. rewrite <-(_ $ E). apply _. now exists_sub x.
  Qed.

End images.

Hint Extern 2 (?f ?x ∊ ?f⁺¹(_)) => eapply @image_element : typeclass_instances.
Hint Extern 2 (SubsetOf ?f⁺¹(_) ?Y) => eapply (subsetof_image (Y:=Y) f) : typeclass_instances.
Hint Extern 2 (SubsetOf ?f⁻¹(_) ?X) => eapply (subsetof_inv_image (X:=X) f) : typeclass_instances.
Hint Extern 2 (Setoid ?f⁺¹(_)) => eapply (setoid_image f) : typeclass_instances.
Hint Extern 2 (Setoid ?f⁻¹(_)) => eapply (setoid_inv_image f) : typeclass_instances.
Hint Extern 5 (?f⁺¹(_) ⊆ _) => eapply (subsetoid_image f) : typeclass_instances.
Hint Extern 5 (?f⁻¹(_) ⊆ _) => eapply (subsetoid_inv_image f) : typeclass_instances.
Hint Extern 2 (Inhabited ?f⁺¹(_)) => eapply @image_inhabited : typeclass_instances.

Lemma image_proper: Find_Proper_Signature (@image) 0
  (∀ A X B Y Be f, Proper (SubsetOf ++> SubsetOf) (@image A X B Y Be f)).
Proof. red. intros. intros S1 S2 ES y [?[x[? Ex]]]. split. apply _. now exists_sub x. Qed.
Hint Extern 0 (Find_Proper_Signature (@image) 0 _) => eexact image_proper : typeclass_instances.

Lemma image_proper2: Find_Proper_Signature (@image) 1
  (∀ `{Setoid (S:=X)} `{Setoid (S:=Y)},
    Proper ((@equiv (X ⇀ Y) _)
      ==> (restrict_rel (λ S, SubsetOf S X) (=))
      ==> (=)) (@image _ X _ Y _)).
Proof. red. intros. intros f g Ef S1 S2 [[e1 e2] ES] y. red in e1,e2.
  split; intros [?[x[? Ex]]]; (split; [apply _ |]);
  assert (x ∊ X) by first [ now apply e1 | now apply e2 ];
  destruct (Ef x x (_ $ subreflexivity x)) as [[??] E].
  assert (x ∊ S2) by now apply ES. exists_sub x. subtransitivity (f x). subsymmetry.
  assert (x ∊ S1) by now apply ES. exists_sub x. subtransitivity (g x).
Qed.
Hint Extern 0 (Find_Proper_Signature (@image) 1 _) => eexact image_proper2 : typeclass_instances.

Lemma inv_image_proper: Find_Proper_Signature (@inv_image) 0
  (∀ A X B Y f, Proper (SubsetOf ++> SubsetOf) (@inv_image A X B Y f)).
Proof. red. intros. intros S1 S2 ES x [??]. split; apply _.  Qed.
Hint Extern 0 (Find_Proper_Signature (@inv_image) 0 _) => eexact inv_image_proper : typeclass_instances.

Lemma inv_image_proper2: Find_Proper_Signature (@inv_image) 1
  (∀ `{Setoid (S:=X)} `{Setoid (S:=Y)},
    Proper ((@equiv (X ⇀ Y) _) ==> ((⊆ Y),=) ==> (=)) (@inv_image _ X _ Y)).
Proof. red. intros. intros f g Ef S1 S2 [[e1 e2]ES] x. red in e1,e2.
  split; intros [??]; (split; [apply _ |]); apply ES.
  now rewrite <-(Ef x x (_ $ subreflexivity x)).
  now rewrite ->(Ef x x (_ $ subreflexivity x)).
Qed.
Hint Extern 0 (Find_Proper_Signature (@inv_image) 1 _) => eexact inv_image_proper2 : typeclass_instances.


Lemma image_id `{Setoid (S:=X)} S `{!SubSetoid S X} {Y} : @image _ Y _ X _ id S = S.
Proof. split. intros [?[?[? E]]]. now rewrite <-(X $ E).
       intro. split. apply _. now exists_sub x.
Qed.

Lemma compose_image `{Setoid (S:=X)} `{Setoid (S:=Y)} `{Setoid (S:=Z)}
  (f:X ⇀ Y) `{!Morphism (X ⇒ Y) f}
  (g:Y ⇀ Z) `{!Morphism (Y ⇒ Z) g} S `{!S ⊆ X}
  : (g ∘ f)⁺¹(S) = g⁺¹(f⁺¹(S)).
Proof. unfold compose. intro z. split.
+ intros [?[x[? E]]]. split. apply _. now exists_sub (f x).
+ intros [?[y[[?[x [? E2]]] E1]]]. split. apply _. exists_sub x.
  subtransitivity (g y). now rewrite (_ $ E2).
Qed.

Lemma restrict_morphism_image `{Setoid (S:=X)} `{Setoid (S:=Y)}
  (f:X ⇀ Y) `{!Morphism (X ⇒ Y) f} S `{!S ⊆ X}
  : Morphism (S ⇒ f⁺¹(S)) f.
Proof. intros ?? E. unfold_sigs. red_sig. now rewrite (X $ E). Qed.
Hint Extern 5 (Morphism (?S ⇒ ?f⁺¹(?S)) ?f) => eapply @restrict_morphism_image : typeclass_instances.
