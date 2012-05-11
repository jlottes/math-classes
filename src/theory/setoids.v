Require Import abstract_algebra interfaces.orders.
Require Export theory.subset.

Lemma equiv_proper : Find_Proper_Signature (@equiv) 0
  (∀ A Ae S `{@Setoid A Ae S}, Proper ((S,=)==>(S,=)==>impl) (=)).
Proof. red. intros. change (Proper ((S,=)==>(S,=)==>impl) (=)).
  intros x1 x2 Ex y1 y2 Ey P. unfold_sigs. subtransitivity y1. subtransitivity x1. subsymmetry. Qed.
Hint Extern 0 (Find_Proper_Signature (@equiv) 0 _) => eexact equiv_proper : typeclass_instances.

Lemma unequiv_proper : Find_Proper_Signature (@uneq) 0
  (∀ `{UnEqualitySetoid (S:=X)}, Proper ((X,=)==>(X,=)==>impl) (≠)).
Proof. red. intros. exact uneq_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@uneq) 0 _) => eexact unequiv_proper : typeclass_instances.

Instance default_uneq `{Equiv} : UnEq _ | 20 := (λ x y, ¬ x = y).
Typeclasses Opaque default_uneq.

Instance default_uneq_standard `{Equiv} S : StandardUnEq S.
Proof. red. reflexivity. Qed.

Instance: ∀ `{Equiv A} `{UnEq A} S `{!Setoid S} `{!StandardUnEq S}, UnEqualitySetoid S.
Proof. intros. split; try apply _; [ intros ?? E1 ?? E2; unfold_sigs; unfold impl | intros ???? ..];
  setoid_rewrite (standard_uneq _ _); try tauto.
  intro P. contradict P. now rewrite_on S -> E1, E2.
Qed.

Instance: ∀ `{Equiv A} `{UnEq A} S `{!Setoid S} `{!StandardUnEq S} `{!SubDecision S S (=)}, TightApart S.
Proof. intros. intros x ? y ?. rewrite (standard_uneq _ _).
  split. unfold SubDecision in *|-. apply stable. tauto.
Qed.

Lemma Setoid_proper : Find_Proper_Signature (@Setoid) 0
  (∀ A, Proper ((=)==>(⊆)-->impl) (@Setoid A)).
Proof. red. intros. intros ?? Ee ?? ES. exact (SubEquivalence_proper _ _ _ ES _ _ Ee). Qed.
Hint Extern 0 (Find_Proper_Signature (@Setoid) 0 _) => eexact Setoid_proper : typeclass_instances.

Lemma UnEqualitySetoid_proper : Find_Proper_Signature (@UnEqualitySetoid) 0
  (∀ A, Proper ((=)==>(=)==>(⊆)-->impl) (@UnEqualitySetoid A)).
Proof. red. intros. intros ?? Ee ?? Eu S1 S2 ES ?. unfold flip in ES. split.
+ rewrite <- Ee, ES. apply _.
+ intros ?? E1 ?? E2 E. unfold_sigs. apply Ee in E1. apply Ee in E2. apply Eu in E.
  pose proof  _ : Proper ((S1,=)==>(S1,=)==>impl) (≠) as p.
  apply Eu. exact (p _ _ (S1 $ E1) _ _ (S1 $ E2) E).
+ intros ???? E1 E2. apply Eu in E1. apply Ee in E2. exact (uneq_ne _ _ E1 E2).
+ intros ???? E1 E2. apply Ee in E1. apply Eu in E2. exact (equiv_nue _ _ E1 E2).
Qed.
Hint Extern 0 (Find_Proper_Signature (@UnEqualitySetoid) 0 _) => eexact UnEqualitySetoid_proper : typeclass_instances.


Lemma subsetoid_a `{Equiv} {S T} {sub:SubSetoid S T} : Setoid S.
Proof. rewrite (_:S⊆T). apply subsetoid_b. Qed.

Hint Extern 19 (?x ∊ ?T) => match goal with
  | sub : SubSetoid _ ?T |- _ => eapply (subset (SubsetOf:=regular_subset_sub (RegularSubset:=subsetoid_regular (SubSetoid:=sub))) x)
end : typeclass_instances.

Lemma element_proper2 : Find_Proper_Signature (@Element) 1
  (∀ `{Equiv} S T `{!RegularSubset S T}, Proper ((T,=)==>impl) (∊ S)).
Proof. red. intros. exact regular_subset_reg. Qed.
Hint Extern 0 (Find_Proper_Signature (@Element) 1 _) => eexact element_proper2 : typeclass_instances.

Lemma subsetoid_singleton `{Equiv} {S} `{!Setoid S} x `{x ∊ S} : SubSetoid {{x}} S.
Proof. split. apply _. split. apply _.
  intros y z E. unfold_sigs.
  intros [_ ?]. split. apply _. subtransitivity y; now subsymmetry.
Qed.
Hint Extern 2 (SubSetoid (@subset_singleton _ _ ?S _) ?S) => eapply @subsetoid_singleton : typeclass_instances.

Lemma singleton_setoid `{Equiv} {S} `{!Setoid S} x `{x ∊ S} : Setoid {{x}}.
Proof subsetoid_a.
Hint Extern 2 (Setoid {{_}}) => eapply @singleton_setoid : typeclass_instances.

Lemma subsetoid_eq_singleton `{Ae:Equiv A} S X `{!SubSetoid S X} x `{x ∊ X} :
  S = {{x | X }} ↔ (∃ y, y ∊ S) ∧ ∀ `{y ∊ S}, y = x.
Proof. pose proof subsetoid_b. split.
+ intro E. split. exists x. rewrite E. apply _. intros ? el. rewrite E in el. now destruct el.
+ intros [[z E] P]. intro y. split. intro. split. apply _. now apply P.
  intros [? el]. now rewrite_on X -> el, <- ( P z _ ).
Qed.

Lemma regularsubset_proper : Find_Proper_Signature (@RegularSubset) 0
  (∀ A, Proper (subrelation-->(=)==>(=)==>impl) (@RegularSubset A)).
Proof. red. intros. intros e1 e2 Ee S1 S2 ES T1 T2 ET [? P].
  split. now rewrite <-ES, <-ET.
  intros x y E ?. unfold_sigs. rewrite <-ES.
  assert ((T1,e1)%signature x y) as E'.
    split. rewrite ET. split; apply _.
    apply Ee. exact E.
  apply (P _ _ E'). now rewrite ES.
Qed.
Hint Extern 0 (Find_Proper_Signature (@RegularSubset) 0 _) => eexact regularsubset_proper : typeclass_instances.

Lemma subsetoid_proper : Find_Proper_Signature (@SubSetoid) 0
  (∀ A, Proper ((=)==>(=)==>(=)==>impl) (@SubSetoid A)).
Proof. red. intros. intros ?? E1 ?? E2 ?? E3 [??].
  split; now rewrite <- E1, <- ?E2, <- E3.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SubSetoid) 0 _) => eexact subsetoid_proper : typeclass_instances.

Lemma Setoid_element `{Equiv A} S `{!Setoid S} : S ∊ Setoid. Proof. trivial. Qed.
Hint Extern 2 (_ ∊ Setoid) => eapply @Setoid_element : typeclass_instances.

Lemma Setoid_subsetoid `{Equiv A} : SubSetoid Setoid (every (Subset A)).
Proof with try apply _. split... split...
  intros S1 S2 ES. unfold_sigs. change (Setoid S1 -> Setoid S2). intro. now rewrite <- ES.
Qed.
Hint Extern 2 (SubSetoid (Setoid) (every (Subset _))) => eapply @Setoid_subsetoid : typeclass_instances.

Lemma Setoid_setoid `{Equiv} : Setoid Setoid.
Proof subsetoid_a (T:=every _).
Hint Extern 2 (Setoid Setoid) => eapply @Setoid_setoid : typeclass_instances.

Lemma Setoid_partialorder `{Equiv} : PartialOrder (Ale:=SubSetoid) Setoid.
Proof. split; [apply _ |..]; unfold le.
+ intros ?? E1 ?? E2 ?. unfold_sigs. now rewrite <- E1, <- E2.
+ firstorder.
+ intros S1 _ S2 _ S3 _ P1 P2. split. apply subsetoid_b. split. transitivity S2; apply _.
  intros x y E ?. unfold_sigs. assert (y∊S2). rewrite_on S3 <- E. apply _. now rewrite_on S2 <- E.
+ intros S1 _ S2 _ P1 P2. exact (subset_sub_sub_eq _ _).
Qed.
Hint Extern 2 (PartialOrder Setoid) => eapply @Setoid_partialorder : typeclass_instances.

Hint Extern 5 (SubReflexive     _ SubSetoid) => eapply @po_refl    : typeclass_instances.
Hint Extern 5 (SubTransitive    _ SubSetoid) => eapply @po_trans   : typeclass_instances.
Hint Extern 5 (SubAntiSymmetric _ SubSetoid) => eapply @po_antisym : typeclass_instances.
(* The underscores above will already need to be resolved by the time these hints are consulted *)

Hint Extern 31 (Subset (Subset _)) => eexact (every _) : typeclass_instances.
Hint Extern 30 (Subset (Subset _)) => eexact Setoid : typeclass_instances.
(* We can extend this list later with other structures *)

Hint Extern 5 (SubSetoid ?X ?X) => subreflexivity : typeclass_instances.

Local Existing Instance setoidmor_a.
Local Existing Instance setoidmor_b.
Local Existing Instance binary_setoidmor_a.
Local Existing Instance binary_setoidmor_b.
Local Existing Instance binary_setoidmor_c.

Instance morphism_closed `{mor:Setoid_Morphism (S:=X) (T:=Y) (f:=f)} : Closed (X==>Y) f | 10.
Proof. intros x ?. now destruct (setoidmor_proper f _ _ (_:Proper (X,=) x)). Qed.

Section binary_morphisms.
  Context `{Equiv A} `{Equiv B} `{Equiv C} {S:Subset A} {T:Subset B} {U:Subset C}.

  Context (f : S ⇀ T ⇀ U) `{!Setoid_Binary_Morphism S T U f}.

  Lemma binary_morphism_closed : Closed (S ==> T ==> U) f.
  Proof. intros x ? y ?. now destruct (binary_sm_proper f _ _ (_:Proper (S,=) x) _ _ (_:Proper (T,=) y)). Qed.

  Global Instance submorphism_binary_1 x `{x ∊ S} : Setoid_Morphism T U (f x) | 10 := {}.

  Instance submorphism_binary_2 y `{y ∊ T} : Setoid_Morphism S U (λ x, f x y).
  Proof. split; try apply _. intros ?? E. unfold_sigs. red_sig. now rewrite_on S -> E. Qed.
End binary_morphisms.
Hint Extern 5 (Setoid_Morphism _ _ (λ x, ?f x _)) => eapply @submorphism_binary_2 : typeclass_instances.

(* Check fun `{Setoid_Binary_Morphism (S:=X) (f:=f)} => _ : Proper ((X,=)==>_==>_) f. *)

Lemma id_morphism `{Equiv} `{!Setoid X} `{!Setoid Y} `{X ⊆ Y}: Setoid_Morphism X Y id.
Proof. split. apply _. apply _. intros ?? ?. unfold_sigs. red_sig. assumption. Qed.
Hint Extern 5 (Setoid_Morphism _ _ id) => eapply @id_morphism : typeclass_instances.

(* Check fun `{SubSetoid (S:=X) (T:=Y)} => _ : Setoid_Morphism X Y id. *)

Lemma morphism_setoid `{Setoid (S:=X)} `{Setoid (S:=Y)} : Setoid (A:=X ⇀ Y) (Setoid_Morphism X Y).
Proof with try apply _. split.
+ intros f fmor. red in fmor. exact (setoidmor_proper f).
+ intros f _ g _ P x y E. symmetry. symmetry in E. exact (P _ _ E).
+ intros f _ g _ h _ P1 P2 x y E. transitivity (g x).
  unfold_sigs. exact (P1 _ _ (_:Proper (X,=) x)).
  exact (P2 _ _ E).
Qed.
Hint Extern 30 (Subset (?X ⇀ ?Y)) => eapply (Setoid_Morphism X Y) : typeclass_instances.

Lemma compose_setoid_morphism {A B C} `{Equiv A} `{Equiv B} `{Equiv C} {S:Subset A} {T:Subset B} {U:Subset C}
  (f:S ⇀ T) (g:T ⇀ U) `{!Setoid_Morphism S T f} `{!Setoid_Morphism T U g} : Setoid_Morphism S U (g ∘ f).
Proof. split; try apply _. intros ?? E. unfold_sigs. unfold compose. red_sig. now rewrite_on S -> E. Qed.
Hint Extern 4 (Setoid_Morphism _ _ (_ ∘ _)) => eapply @compose_setoid_morphism : typeclass_instances.

Lemma setoid_morphism_proper : Find_Proper_Signature (@Setoid_Morphism) 0
  (∀ A B, Proper ((=)==>(=)==>(⊆)-->(=)==>eq==>impl) (@Setoid_Morphism A B)).
Proof. red. intros. intros Se1 Se2 Ees Te1 Te2 Eet S1 S2 ES T1 T2 ET f g E mor. unfold flip in ES.
  split.
  + rewrite    ES, <- Ees. apply _.
  + rewrite <- ET, <- Eet. apply _.
  + rewrite <- E. intros x1 x2 Ex. destruct_subset_eq T1 T2. unfold_sigs. red_sig.
    apply Eet. assert ((S1,Se1)%signature x1 x2) as Ex'. red_sig. now apply Ees.
    now destruct (setoidmor_proper f (Setoid_Morphism:=mor) _ _ Ex').
Qed.
Hint Extern 0 (Find_Proper_Signature (@Setoid_Morphism) 0 _) => eexact setoid_morphism_proper : typeclass_instances.

Lemma setoid_morphism_proper2 : Find_Proper_Signature (@Setoid_Morphism) 1
  (∀ A B Ae Be S, Proper ((Setoid,⊆)++>eq==>impl) (@Setoid_Morphism A B Ae Be S)).
Proof. red. intros. intros T1 T2 ET f g E mor. unfold_sigs. red in el,el0. rewrite <- E. split; try apply _.
  intros ?? E1. unfold_sigs. red_sig. now rewrite_on S -> E1.
Qed.
Hint Extern 0 (Find_Proper_Signature (@Setoid_Morphism) 1 _) => eexact setoid_morphism_proper2 : typeclass_instances.

Lemma setoid_binary_morphism_proper : Find_Proper_Signature (@Setoid_Binary_Morphism) 0
  (∀ A B C, Proper ((=)==>(=)==>(=)==>(⊆)-->(⊆)-->(=)==>eq==>impl) (@Setoid_Binary_Morphism A B C)).
Proof. red. intros. intros Se1 Se2 Ees Te1 Te2 Eet Ue1 Ue2 Eeu S1 S2 ES T1 T2 ET U1 U2 EU f g E mor. unfold flip in ES, ET.
  split.
  + rewrite    ES, <- Ees. apply _.
  + rewrite    ET, <- Eet. apply _.
  + rewrite <- EU, <- Eeu. apply _.
  + rewrite <- E. intros x1 x2 Ex y1 y2 Ey. destruct_subset_eq U1 U2. unfold_sigs. red_sig. apply Eeu.
    assert ((S1,Se1)%signature x1 x2) as Ex'. red_sig. now apply Ees.
    assert ((T1,Te1)%signature y1 y2) as Ey'. red_sig. now apply Eet.
    now destruct (binary_sm_proper f (Setoid_Binary_Morphism:=mor) _ _ Ex' _ _ Ey').
Qed.
Hint Extern 0 (Find_Proper_Signature (@Setoid_Binary_Morphism) 0 _) => eexact setoid_binary_morphism_proper : typeclass_instances.

Lemma setoid_binary_morphism_proper2 : Find_Proper_Signature (@Setoid_Binary_Morphism) 1
  (∀ A B C Ae Be Ce S T, Proper ((Setoid,⊆)==>eq==>impl) (@Setoid_Binary_Morphism A B C Ae Be Ce S T)).
Proof. red. intros. intros T1 T2 ET f g E mor. unfold_sigs. red in el,el0. rewrite <- E. split; try apply _.
  intros ?? E1 ?? E2. unfold_sigs. red_sig. rewrite_on S -> E1. now rewrite_on T -> E2.
Qed.
Hint Extern 0 (Find_Proper_Signature (@Setoid_Binary_Morphism) 1 _) => eexact setoid_binary_morphism_proper : typeclass_instances.

Section images.
  Context {A B} `{Equiv A} `{Equiv B} {X:Subset A} {Y:Subset B} (f:X ⇀ Y) `{!Setoid_Morphism X Y f}.

  Instance image_element (S:Subset A) `{!S ⊆ X} x `{!x ∊ S} : f x ∊ f⁺¹(S).
  Proof. split. apply _. exists_sub x. subreflexivity. Qed.

  Instance subsetof_image     (S:Subset A) `{!S ⊆ X} : f⁺¹(S) ⊆ Y. Proof. firstorder. Qed.
  Instance subsetof_inv_image (T:Subset B) `{!T ⊆ Y} : f⁻¹(T) ⊆ X. Proof. now intros ?[??]. Qed.

  Instance subsetoid_image (S:Subset A) `{!S ⊆ X} : SubSetoid f⁺¹(S) Y.
  Proof with try apply _. split... split... intros y1 y2 E [_ [x [? E2]]]. unfold_sigs.
    split... exists_sub x. subtransitivity y1.
  Qed.

  Instance subsetoid_inv_image (T:Subset B) `{!SubSetoid T Y} : SubSetoid f⁻¹(T) X.
  Proof with try apply _. split... split... intros x1 x2 E [_?]. unfold_sigs.
    split... assert (f x2 = f x1) as E2. rewrite_on X -> E. subreflexivity. now rewrite_on Y -> E2.
  Qed.

  Lemma setoid_image     (S:Subset A) `{!S ⊆ X}         : Setoid f⁺¹(S). Proof subsetoid_a.
  Lemma setoid_inv_image (T:Subset B) `{!SubSetoid T Y} : Setoid f⁻¹(T). Proof subsetoid_a.
 
  Lemma image_eq_singleton (S:Subset A) `{!S ⊆ X} y `{y ∊ Y}
    : f⁺¹(S) = {{y}} ↔ (∃ x, x ∊ S) ∧ ∀ `{x ∊ S}, f x = y.
  Proof. rewrite (subsetoid_eq_singleton f⁺¹(S) Y y). split.
  + intros [[y' [? [x [? E]]]] P]. split. now exists x. intros x' ?. apply (P (f x') _).
  + intros [[x ?] P]. split. exists (f x). apply _. intros y' [? [x' [? E]]]. rewrite_on Y <- E. exact (P x' _).
  Qed.

  Lemma inv_image_eq_singleton (T:Subset B) `{!SubSetoid T Y} x `{x ∊ X}
    : f⁻¹(T) = {{x}} ↔ f x ∊ T ∧ ∀ `{x' ∊ X}, f x' ∊ T → x' = x.
  Proof. split.
  + intros E. split. cut (x ∊ f⁻¹(T)). firstorder. rewrite E. apply _.
    intros x' ? ?. assert (x' ∊ f⁻¹(T)) as el by now split. rewrite E in el. now destruct el.
  + intros [? P] x'. split. intros [??]. pose proof (P x' _ _). now split.
    intros [? E]. split. apply _. now rewrite_on X -> E.
  Qed.

End images.

Hint Extern 2 (?f ?x ∊ ?f⁺¹(_)) => eapply (image_element f x) : typeclass_instances.
Hint Extern 2 (?f⁺¹(_) ⊆ ?Y) => eapply (subsetof_image (Y:=Y) f) : typeclass_instances.
Hint Extern 2 (?f⁻¹(_) ⊆ ?X) => eapply (subsetof_inv_image (X:=X) f) : typeclass_instances.
Hint Extern 2 (Setoid ?f⁺¹(_)) => eapply (setoid_image f) : typeclass_instances.
Hint Extern 2 (Setoid ?f⁻¹(_)) => eapply (setoid_inv_image f) : typeclass_instances.
Hint Extern 5 (SubSetoid ?f⁺¹(_) _) => eapply (subsetoid_image f) : typeclass_instances.
Hint Extern 5 (SubSetoid ?f⁻¹(_) _) => eapply (subsetoid_inv_image f) : typeclass_instances.

Lemma image_proper: Find_Proper_Signature (@image) 0
  (∀ A B Be X Y f, Proper ((⊆) ++> (⊆)) (@image A B Be X Y f)).
Proof. red. intros. intros S1 S2 ES y [?[x[? Ex]]]. split. apply _. now exists_sub x. Qed.

Lemma inv_image_proper: Find_Proper_Signature (@inv_image) 0
  (∀ A B Ae X Y f, Proper ((⊆) ++> (⊆)) (@inv_image A B Ae X Y f)).
Proof. red. intros. intros S1 S2 ES x [??]. split; apply _.  Qed.
Hint Extern 0 (Find_Proper_Signature (@inv_image) 0 _) => eexact inv_image_proper : typeclass_instances.


