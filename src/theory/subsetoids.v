Require Import
  abstract_algebra.
Require Export theory.setoids theory.subset.

Lemma element_proper2 : Find_Proper_Signature (@Element) 1
  (∀ A S `{!Equiv A} `{!SubSetoid S}, Proper ((=)==>impl) (∊ S)).
Proof. intros ????. exact subset_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@Element) 1 _) => eexact element_proper2 : typeclass_instances.

Instance subsetoid_every `{Setoid A} : SubSetoid (Every A).
Proof. split; try apply _. intros ????. apply _. Qed.

Instance subsetoid_singleton `{Setoid A} (x:A) : SubSetoid {{x}}.
Proof. split; try apply _. intros y z E. change (y = x -> z = x). intro. now rewrite <-E. Qed.

Lemma subsetoid_eq_singleton `{Ae:Equiv A} S `{!SubSetoid S} x :
  S = {{x}} ↔ (∃ y, y ∊ S) ∧ ∀ `{y ∊ S}, y = x.
Proof. split.
+ intro E. split. exists x. rewrite E. apply _. intros ? el. now rewrite E in el.
+ intros [[z E] P]. intro y. split. intro. change (y=x). now apply P.
  intro el. change (y=x) in el. rewrite el. now rewrite <- ( P z _ ).
Qed.

Lemma subsetoid_proper : Find_Proper_Signature (@SubSetoid) 0
  (∀ A (Ae:Equiv A), Proper ((=) ==> impl) (@SubSetoid A Ae)).
Proof. intros ?? ?? E ?. split; try apply _. intros ?? E2 ?. now rewrite <-E, <-E2, E. Qed.
Hint Extern 0 (Find_Proper_Signature (@SubSetoid) 0 _) => eexact subsetoid_proper : typeclass_instances.

Lemma subsetoid_refl_eq_fp `{SubSetoid (S:=X)} : Find_Proper_Proper (SubSetoid,=) X.
Proof. apply restrict_rel_refl; apply _. Qed.

Lemma subsetoid_refl_sub_fp `{SubSetoid (S:=X)} : Find_Proper_Proper (SubSetoid,⊆) X.
Proof. apply restrict_rel_refl; apply _. Qed.

Hint Extern 0 (@Find_Proper_Proper (Subset _) (@restrict_rel _ (@SubSetoid _ _) (@equiv _ (subset_equiv _))) _)
  => eapply @subsetoid_refl_eq_fp : typeclass_instances.

Hint Extern 0 (@Find_Proper_Proper (Subset _) (@restrict_rel _ (@SubSetoid _ _) (@SubsetOf _)) _)
  => eapply @subsetoid_refl_sub_fp : typeclass_instances.

Lemma find_subsetoid1   `{SubSetoid (S:=X)} : SubSetoid X.          Proof. tauto. Qed.
Lemma find_subsetoid_ms `{SubSetoid_Morphism (S:=X)} : SubSetoid X. Proof subsetoidmor_s _.
Lemma find_subsetoid_mt `{SubSetoid_Morphism (T:=X)} : SubSetoid X. Proof subsetoidmor_t _.
Lemma find_subsetoid_bms `{SubSetoid_Binary_Morphism (S:=X)} : SubSetoid X. Proof subsetoidmor_binary_s _.
Lemma find_subsetoid_bmt `{SubSetoid_Binary_Morphism (T:=X)} : SubSetoid X. Proof subsetoidmor_binary_t _.
Lemma find_subsetoid_bmu `{SubSetoid_Binary_Morphism (U:=X)} : SubSetoid X. Proof subsetoidmor_binary_u _.

Ltac find_subsetoid X :=
  let aux1 X :=
    first [ match goal with _ : SubSetoid X |- _ => idtac end
          | match goal with _ : SubSetoid_Morphism _ X _ |- _ => pose proof (find_subsetoid_ms  (X:=X))
                          | _ : SubSetoid_Morphism _ _ X |- _ => pose proof (find_subsetoid_mt  (X:=X))
                          | _ : SubSetoid_Binary_Morphism _ X _ _ |- _ => pose proof (find_subsetoid_bms  (X:=X))
                          | _ : SubSetoid_Binary_Morphism _ _ X _ |- _ => pose proof (find_subsetoid_bmt  (X:=X))
                          | _ : SubSetoid_Binary_Morphism _ _ _ X |- _ => pose proof (find_subsetoid_bmu  (X:=X)) end
          ]
  in let aux2 X :=
    match goal with E: X = ?Y |- _ => aux1 Y; assert (SubSetoid X) by now rewrite E
                  | E: ?Y = X |- _ => aux1 Y; assert (SubSetoid X) by now rewrite <-E
    end
  in let aux3 X :=
    first [ pose proof (find_subsetoid1    (X:=X))
          | pose proof (find_subsetoid_ms  (X:=X))
          | pose proof (find_subsetoid_mt  (X:=X))
          | pose proof (find_subsetoid_bms (X:=X))
          | pose proof (find_subsetoid_bmt (X:=X))
          | pose proof (find_subsetoid_bmu (X:=X))
          ]
  in first [ aux1 X | aux2 X | aux3 X ].
Tactic Notation "find_subsetoids" constr(X) constr(Y) := find_subsetoid X; find_subsetoid Y.
Tactic Notation "find_subsetoids" constr(X) constr(Y) constr(Z) := find_subsetoid X; find_subsetoid Y; find_subsetoid Z.

Lemma subsetoid_refl_eq `{SubSetoid (S:=X)} : Proper (SubSetoid,=)%signature X.
Proof. apply restrict_rel_refl; apply _. Qed.

Lemma subsetoid_refl_sub `{SubSetoid (S:=X)} : Proper (SubSetoid,⊆)%signature X.
Proof. apply restrict_rel_refl; apply _. Qed.

Lemma subsetoid_refl_eq2  `{SubSetoid_Morphism (S:=X)} : Proper (SubSetoid,=)%signature X. Proof. find_subsetoid X. exact subsetoid_refl_eq. Qed.
Lemma subsetoid_refl_sub2 `{SubSetoid_Morphism (S:=X)} : Proper (SubSetoid,⊆)%signature X. Proof. find_subsetoid X. exact subsetoid_refl_sub. Qed.
Lemma subsetoid_refl_eq3  `{SubSetoid_Morphism (T:=X)} : Proper (SubSetoid,=)%signature X. Proof. find_subsetoid X. exact subsetoid_refl_eq. Qed.
Lemma subsetoid_refl_sub3 `{SubSetoid_Morphism (T:=X)} : Proper (SubSetoid,⊆)%signature X. Proof. find_subsetoid X. exact subsetoid_refl_sub. Qed.

Hint Extern 0 (@Proper (Subset _) (@restrict_rel _ (@SubSetoid _ _) (@equiv _ (subset_equiv _)) ) _ ) => eapply @subsetoid_refl_eq   : typeclass_instances.
Hint Extern 1 (@Proper (Subset _) (@restrict_rel _ (@SubSetoid _ _) (@equiv _ (subset_equiv _)) ) _ ) => eapply @subsetoid_refl_eq2  : typeclass_instances.
Hint Extern 1 (@Proper (Subset _) (@restrict_rel _ (@SubSetoid _ _) (@equiv _ (subset_equiv _)) ) _ ) => eapply @subsetoid_refl_eq3  : typeclass_instances.
Hint Extern 0 (@Proper (Subset _) (@restrict_rel _ (@SubSetoid _ _) (@SubsetOf _) )               _ ) => eapply @subsetoid_refl_sub  : typeclass_instances.
Hint Extern 1 (@Proper (Subset _) (@restrict_rel _ (@SubSetoid _ _) (@SubsetOf _) )               _ ) => eapply @subsetoid_refl_sub2 : typeclass_instances.
Hint Extern 1 (@Proper (Subset _) (@restrict_rel _ (@SubSetoid _ _) (@SubsetOf _) )               _ ) => eapply @subsetoid_refl_sub3 : typeclass_instances.

Lemma id_submorphism `{Equiv A} (S T:Subset A) `{!S ⊆ T} `{!SubSetoid S} `{!SubSetoid T}
  : SubSetoid_Morphism id S T.
Proof with try apply _. split... intros ?? E. unfold_sigs. red_sig. now unfold id. Qed.
Hint Extern 0 (SubSetoid_Morphism id _ _) => eapply @id_submorphism : typeclass_instances.

Section images.
  Context {A B} {Ae:Equiv A} {Be:Equiv B} (f:A → B) `{!SubSetoid_Morphism f X Y}.

  Existing Instance subsetoidmor_s.
  Existing Instance subsetoidmor_t.

  Instance image_element (S:Subset A) `{!S ⊆ X} x `{!x ∊ S} : f x ∊ f⁺¹(S).
  Proof. exists x. now split. Qed.

  Lemma subsetof_image (S:Subset A) `{!S ⊆ X} : f⁺¹(S) ⊆ Y.
  Proof. intros y [x[? E]]. rewrite <-E. apply _. Qed.

  Lemma subsetof_inv_image `{!Domain f X} `{!CoDomain f Y} (T:Subset B) `{!T ⊆ Y} : f⁻¹(T) ⊆ X.
  Proof. now intros ?[??]. Qed.

  Instance subsetoid_image (S:Subset A) `{!S ⊆ X} : SubSetoid f⁺¹(S).
  Proof with try apply _. split... intros ?? E [y [??]]. exists y.
    split... now rewrite <-E.
  Qed.

  Lemma subsetoid_inv_image (T:Subset B) `{!SubSetoid T} `{!T ⊆ Y} : SubSetoid f⁻¹(T).
  Proof. split; try apply _. intros x x' E [??].
    assert (x' ∊ X) by now rewrite <-E. split. assumption.
    now rewrite_on X <- E.
  Qed.

  Lemma image_eq_singleton (S:Subset A) `{!S ⊆ X} y : f⁺¹(S) = {{y}} ↔ (∃ x, x ∊ S) ∧ ∀ `{x ∊ S}, f x = y.
  Proof. rewrite (subsetoid_eq_singleton f⁺¹(S) y). split.
  + intros [[y' [x' [? E]]] P]. split. now exists x'. intros x ?. apply (P (f x) _).
  + intros [[x ?] P]. split. exists (f x). apply _. intros y' [x' [? E]]. rewrite <- E. exact (P x' _).
  Qed.

  Lemma inv_image_eq_singleton (T:Subset B) `{!SubSetoid T} `{!T ⊆ Y} x
    : f⁻¹(T) = {{x}} ↔ (x ∊ X ∧ f x ∊ T) ∧ ∀ `{x' ∊ X}, f x' ∊ T → x' = x.
  Proof. split.
  + intro E. split. change (x ∊ f⁻¹(T)). rewrite E. apply _.
    intros x' ? ?. assert (x' ∊ f⁻¹(T)) as el by now split. now rewrite E in el.
  + intros [[??] P x']. split. intros [??]. exact (P x' _ _).
    intro E. change (x'=x) in E. assert (x' ∊ X) by now rewrite E.
    split. apply _. now rewrite_on X -> E.
  Qed.

End images.

Hint Extern 0 (@Element _  (@image _ _ _ ?f _) (?f ?x)) => eapply (image_element f _ x) : typeclass_instances.
Hint Extern 1 (@SubsetOf _ (@image _ _ _ ?f _) ?Y) => eapply (subsetof_image f (Y:=Y)) : typeclass_instances.
Hint Extern 1 (@SubsetOf _ (@inv_image _ _ ?f ?X ?dom _) ?X) => eapply (subsetof_inv_image f (Domain0:=dom)) : typeclass_instances.
Hint Extern 0 (@SubSetoid _ ?Be (@image _ _ ?Be ?f _) ) => eapply (subsetoid_image f) : typeclass_instances.
Hint Extern 0 (@SubSetoid _ _ (@inv_image _ _ _ _ _ _) ) => eapply @subsetoid_inv_image : typeclass_instances.

Lemma image_proper_fp: Find_Proper_Signature (@image) 0
  (∀ A B Be f, Proper ((⊆) ++> (⊆)) (@image A B Be f)).
Proof. intro. intros. intros T1 T2 E ? [y [??]]. exists y. split. apply _. assumption. Qed.
Hint Extern 0 (Find_Proper_Signature (@image) 0 _) => eexact image_proper_fp : typeclass_instances.

Lemma inv_image_proper_fp: Find_Proper_Signature (@inv_image) 0
  (∀ A B f D dom, Proper ((⊆) ++> (⊆)) (@inv_image A B f D dom)).
Proof. intro. intros. intros S1 S2 E ? [H1 H2]. split; apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@inv_image) 0 _) => eexact inv_image_proper_fp : typeclass_instances.

Lemma compose_subsetoid_morphism `{Equiv A} `{Equiv B} `{Equiv C} (S:Subset A) (T:Subset B) (U:Subset C)
  (f : A → B) (g : B → C) :
  SubSetoid_Morphism f S T → SubSetoid_Morphism g T U → SubSetoid_Morphism (g ∘ f) S U.
Proof. intros ? ?. find_subsetoids S T U.
  split; try apply _.
  intros ?? E. unfold_sigs. unfold compose. red_sig.
  now rewrite_on S <- E.
Qed.
Hint Extern 4 (SubSetoid_Morphism (_ ∘ _)) => class_apply @compose_subsetoid_morphism : typeclass_instances.

Lemma to_subsetoid_rel `{SubSetoid (S:=X)} `{!SubSetoid Y} {R:relation _} (E:R X Y)
  : (SubSetoid,R)%signature X Y.
Proof. split. split; assumption. exact E. Qed.

Ltac rewrite_subsetoid_init E :=
  match type of E with ?R ?x ?y => find_subsetoids x y end.

Tactic Notation "rewrite_subsetoid"      constr(E) := rewrite_subsetoid_init E; rewrite   (to_subsetoid_rel E).
Tactic Notation "rewrite_subsetoid" "<-" constr(E) := rewrite_subsetoid_init E; rewrite <-(to_subsetoid_rel E).

Lemma submorphism_proper: Find_Proper_Signature (@SubSetoid_Morphism) 0
  (∀ A Ae B Be f, Proper ((SubSetoid,⊆)-->(SubSetoid,⊆)++>impl) (@SubSetoid_Morphism A Ae B Be f)).
Proof. intros ?????.
  intros S1 S2 [[??]ES] T1 T2 [[??]ET] ?. split; try apply _.
  intros ?? E. unfold_sigs. red_sig. now rewrite_on S2 ->E.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SubSetoid_Morphism) 0 _) => eexact submorphism_proper : typeclass_instances.

Lemma submorphism_proper2: Find_Proper_Signature (@SubSetoid_Morphism) 1
  (∀ A Ae B Be f, Proper ((=)==>(=)==>impl) (@SubSetoid_Morphism A Ae B Be f)).
Proof. intros ?????.
  intros S1 S2 ES T1 T2 ET ?. find_subsetoids S2 T2.
  rewrite_subsetoid <-ES. now rewrite_subsetoid <-ET.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SubSetoid_Morphism) 1 _) => eexact submorphism_proper2 : typeclass_instances.

Lemma submorphism_binary_proper: Find_Proper_Signature (@SubSetoid_Binary_Morphism) 0
  (∀ A Ae B Be C Ce f, Proper ((SubSetoid,⊆)-->(SubSetoid,⊆)-->(SubSetoid,⊆)++>impl)
                              (@SubSetoid_Binary_Morphism A Ae B Be C Ce f) ).
Proof. intros ?? ?? ?? ?.
  intros S1 S2 [[??]ES] T1 T2 [[??]ET] U1 U2 [[??]EU] ?. split; try apply _.
  intros ?? E1 ?? E2. unfold_sigs. red_sig. rewrite_on S1 ->E1. now rewrite_on T1 ->E2.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SubSetoid_Binary_Morphism) 0 _) => eexact submorphism_binary_proper : typeclass_instances.

Lemma submorphism_binary_proper2: Find_Proper_Signature (@SubSetoid_Binary_Morphism) 1
  (∀ A Ae B Be C Ce f, Proper ((=)==>(=)==>(=)==>impl)
                              (@SubSetoid_Binary_Morphism A Ae B Be C Ce f) ).
Proof. intros ?? ?? ?? ?.
  intros S1 S2 ES T1 T2 ET U1 U2 EU ?. find_subsetoids S2 T2 U2.
  rewrite_subsetoid <-ES. rewrite_subsetoid <-ET. now rewrite_subsetoid <-EU.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SubSetoid_Binary_Morphism) 1 _) => eexact submorphism_binary_proper2 : typeclass_instances.

Section binary_morphisms.
  Context `{Equiv A} `{Equiv B} `{Equiv C}.

  Context (f : A → B → C) {S:Subset A} {T:Subset B} {U:Subset C} `{!SubSetoid_Binary_Morphism f S T U}.

  Existing Instance subsetoidmor_binary_s.
  Existing Instance subsetoidmor_binary_t.
  Existing Instance subsetoidmor_binary_u.

  (* making these global causes loops *)
 
  Instance submorphism_binary_1 x `{!x ∊ S} : SubSetoid_Morphism (f x) T U.
  Proof. split; try apply _. red. apply _. Qed.

  Instance submorphism_binary_2 y `{!y ∊ T} : SubSetoid_Morphism (λ x, f x y) S U.
  Proof. split; try apply _.
    intros ?? E. unfold_sigs. red_sig. now rewrite_on S -> E.
  Qed.
End binary_morphisms.


Section relation_extension.

  Context `{Setoid A} (S:Subset A) (R: relation A) .

  Definition equiv_ext : relation A := λ x y, (S,R)%signature x y ∨ x = y.

  Instance equiv_ext_sub : subrelation (=) equiv_ext.
  Proof. intros ?? E. now right. Qed.

  Context `{!SubSetoid S} `{!SubEquivalence R S} `{!Proper ((S,=)==>(S,=)==>impl) R}.

  Lemma equiv_ext_correct x `{!x ∊ S} y `{!y ∊ S} : equiv_ext x y ↔ R x y.
  Proof. unfold equiv_ext. split. intros [[??]|E]. tauto. rewrite_on S ->E.
    apply (subreflexivity y). unfold restrict_rel. tauto. Qed.

  Instance equiv_ext_equivalence : Equivalence equiv_ext.
  Proof. unfold equiv_ext. split.
  + intro. right. reflexivity.
  + intros x y [E|?]. unfold_sigs. left. red_sig. now apply (subsymmetry x y). right. now symmetry.
  + intros x y z [E1|E1]. unfold_sigs. intros [E2|E2]. unfold_sigs.
      left. red_sig. apply (subtransitivity x y z); tauto.
      left. assert (z ∊ S) by now rewrite <-E2. red_sig. rewrite_on S <-E2. exact E1.
      intros [E2|E2]. unfold_sigs. assert (x ∊ S) by now rewrite E1. left. red_sig. rewrite_on S ->E1. exact E2.
      right. auto_trans.
  Qed.

  Instance equiv_ext_subsetoid : SubSetoid (Ae:=equiv_ext) S.
  Proof. split. red. apply _. intros ?? [?|E] ?. now unfold_sigs. now rewrite <-E. Qed.

End relation_extension.
Hint Extern 0 (@subrelation _ (@equiv _ ?Ae) (@equiv_ext _ ?Ae _ _)) => eapply @equiv_ext_sub : typeclass_instances.
Hint Extern 0 (@SubSetoid _ (@equiv_ext _ _ ?S _) ?S) => eapply @equiv_ext_subsetoid : typeclass_instances.
