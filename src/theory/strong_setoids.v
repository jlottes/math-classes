Require Import
  abstract_algebra theory.products.
Require Export
  theory.setoids.

Section contents.
Context `{S:Subset} `{StrongSetoid _ (S:=S)}.

Global Instance: Setoid S.
Proof. split; red; intros x ?; [| intros y ? ..]; [| | intros z ?]; rewrite <- ?(tight_apart _ _).
+ exact (subirreflexivity (≠) _).
+ intro E. contradict E. subsymmetry.
+ intros E1 E2 E3. destruct (subcotransitivity E3 y); contradiction.
Qed.

Instance: Proper ((S,=) ==> (S,=) ==> impl) (≠).
Proof.
  assert (∀ `{x₁ ∊ S} `{y ∊ S} `{x₂ ∊ S}, x₁ ≠ y → x₁ = x₂ → x₂ ≠ y) as P1.
   intros ?? ?? ?? E Ex.
   destruct (subcotransitivity E x₂); trivial.
   apply (tight_apart _ _) in Ex. now destruct Ex.
  intros x₁ x₂ Ex y₁ y₂ Ey E. unfold_sigs. apply P1 with x₁; trivial.
  subsymmetry. apply P1 with y₁; trivial. subsymmetry.
Qed.

Global Instance: InequalitySetoid S.
Proof. split; try apply _; intros ?? ??; rewrite <- ?(tight_apart _ _); tauto. Qed.

Global Instance: ∀ `{x ∊ S} `{y ∊ S}, Stable (x = y).
Proof. intros. unfold Stable, DN. rewrite <- (tight_apart _ _). tauto. Qed.
End contents.

Local Hint Extern 20 (?x ∊ ?T) => match goal with
  | sub : SubsetOf _ ?T |- _ => eapply (subset (SubsetOf:=sub) x)
end : typeclass_instances.


Lemma denial_inequality_proper : Find_Proper_Signature (@DenialInequality) 0
  (∀ A, Proper ((=)==>(=)==>SubsetOf-->impl) (@DenialInequality A)).
Proof. red. intros. intros e1 e2 Ee u1 u2 Eu S1 S2 ES P. unfold flip in ES.
  intros x ? y ?. split; intro Q.
    apply Eu in Q. apply (P _ _ _ _) in Q. contradict Q. now apply Ee.
    apply Eu. apply (P _ _ _ _). contradict Q. now apply Ee.
Qed.
Hint Extern 0 (Find_Proper_Signature (@DenialInequality) 0 _) => eexact denial_inequality_proper : typeclass_instances.

Lemma tight_apart_proper : Find_Proper_Signature (@TightApart) 0
  (∀ A, Proper ((=)==>(=)==>SubsetOf-->impl) (@TightApart A)).
Proof. red. intros. intros e1 e2 Ee u1 u2 Eu S1 S2 ES P. unfold flip in ES.
  intros x ? y ?. split; intro Q.
    apply Ee. apply (tight_apart _ _). contradict Q. now apply Eu.
    intro E. apply Eu in E. generalize E. apply (tight_apart _ _). now apply Ee.
Qed.
Hint Extern 0 (Find_Proper_Signature (@TightApart) 0 _) => eexact tight_apart_proper : typeclass_instances.

Lemma strong_setoid_proper : Find_Proper_Signature (@StrongSetoid) 0
  (∀ A, Proper ((=)==>(=)==>SubsetOf-->impl) (@StrongSetoid A)).
Proof. red. intros. intros e1 e2 Ee u1 u2 Eu S1 S2 ES P. unfold flip in ES.
  split; unfold uneq; rewrite <- ?Ee, <- Eu, ES. apply strongsetoid_apart. apply _.
Qed.
Hint Extern 0 (Find_Proper_Signature (@StrongSetoid) 0 _) => eexact strong_setoid_proper : typeclass_instances.

(* In case we have a decidable setoid, we can construct a strong setoid. Again
  we do not make this an instance as it will cause loops *)
Section dec_setoid.
  Context `{UnEq} {S} `{Setoid _ (S:=S)} `{!DenialInequality S} `{!SubDecision S S (=)}.

  Instance dec_strong_setoid: StrongSetoid S.
  Proof. split; [ split; red | red ]; intros x ?; [| intros y ? ..]; rewrite -> ?(denial_inequality _ _).
  + intro E. now contradict E.
  + intro E. contradict E. subsymmetry.
  + intros E1 z ?. rewrite -> ?(denial_inequality _ _).
    destruct (decide_sub (=) x z) as [E2|?]; [|tauto]. right. contradict E1. subtransitivity z.
  + split. apply stable. tauto.
  Qed.
End dec_setoid.

Lemma strong_ext_equiv_2 `{X:Subset} `{Y:Subset} `{Z:Subset} (f g:X ⇀ Y ⇀ Z) `{UnEq X} `{UnEq Y} `{UnEq Z}
  : strong_ext_equiv (uncurry f) (uncurry g)
  ↔ ∀ `{x₁ ∊ X} `{x₂ ∊ X} `{y₁ ∊ Y} `{y₂ ∊ Y}, f x₁ y₁ ≠ g x₂ y₂ → x₁ ≠ x₂ ∨ y₁ ≠ y₂.
Proof. unfold strong_ext_equiv, uncurry. split.
+ intros P a ? b ? c ? d ? E. destruct (P (a,c) _ (b,d) _ E); tauto.
+ intros P [??][??][??][??] E. do 2 red. destruct (P _ _ _ _ _ _ _ _ E); tauto.
Qed.

Lemma strong_ext_equiv_proper : Find_Proper_Signature (@strong_ext_equiv) 0
  (∀ `{StrongSetoid (S:=X)} `{StrongSetoid (S:=Y)},
     Proper ((restrict_rel (X ⇀ Y) (@equiv (X ⇀ Y) _))
         ==> (restrict_rel (X ⇀ Y) (@equiv (X ⇀ Y) _)) ==> impl) strong_ext_equiv).
Proof. red; intros. intros f1 f2 [[cf1 cf2] Ef] g1 g2 [[cg1 cg2] Eg].
  pose proof @closed_range.
  repeat match goal with  H : ?f ∊ X ⇀ Y |- _ => change (Closed (X ⇀ Y) f) in H end.
  intros Es x ? y ? E. apply Es; trivial.
  now rewrite (Ef _ _ (_:Proper(X,=) x)), (Eg _ _ (_:Proper(X,=) y)).
Qed.
Hint Extern 0 (Find_Proper_Signature (@strong_ext_equiv) 0 _) => eexact strong_ext_equiv_proper : typeclass_instances.

Lemma strong_extensionality `{X:Subset} `{Y:Subset} (f:X ⇀ Y) `{UnEq X} `{UnEq Y} {sm: Strong_Morphism X Y f}
  `{x ∊ X} `{y ∊ X} : f x ≠ f y → x ≠ y.
Proof. destruct sm as [? sm]. exact (sm x _ y _). Qed.

Lemma strong_binary_extensionality `{X:Subset} `{Y:Subset} `{Z:Subset} (f:X ⇀ Y ⇀ Z) `{UnEq X} `{UnEq Y} `{UnEq Z}
  {sm: Strong_Binary_Morphism X Y Z f}
  `{x₁ ∊ X} `{x₂ ∊ X} `{y₁ ∊ Y} `{y₂ ∊ Y} : f x₁ y₁ ≠ f x₂ y₂ → x₁ ≠ x₂ ∨ y₁ ≠ y₂.
Proof. destruct sm as [? sm]. rewrite (strong_ext_equiv_2 _ _) in sm. auto. Qed.

Lemma id_strong_injective `{StrongSetoid (S:=X)} `{!StrongSetoid Y} `{!SubsetOf X Y}: StrongInjective X Y id.
Proof. split. intuition. split; try apply _. firstorder. Qed.
Hint Extern 2 (StrongInjective _ _ id) => class_apply @id_strong_injective : typeclass_instances.

Lemma id_strong_morphism `{StrongSetoid (S:=X)} `{!StrongSetoid Y} `{!SubsetOf X Y}: Strong_Morphism X Y id.
Proof strong_injective_mor _.
Hint Extern 2 (Strong_Morphism _ _ id) => class_apply @id_strong_morphism : typeclass_instances.

Lemma strong_morphism_closed `{Strong_Morphism (X:=X) (Y:=Y) (f:=f)} : Closed (X ⇀ Y) f.
Proof. firstorder. Qed.

Lemma strong_binary_morphism_closed `{Strong_Binary_Morphism (X:=X) (Y:=Y) (Z:=Z) (f:=f)} : Closed (X ⇀ Y ⇀ Z) f.
Proof. firstorder. Qed.

Local Existing Instance strong_morphism_closed.
Local Existing Instance strong_binary_morphism_closed.
Local Existing Instance closed_range.
Local Existing Instance closed_binary.

Lemma strong_morphism_morphism
  `{StrongSetoid (S:=X)} `{StrongSetoid (S:=Y)}
  f {sm: Strong_Morphism X Y f} : Morphism (X ⇒ Y) f.
Proof.
  intros x₁ x₂ Ex. unfold_sigs. red_sig.
  rewrite <- (tight_apart _ _). rewrite <- (tight_apart _ _) in Ex.
  contradict Ex. exact (strong_extensionality f Ex).
Qed.

Lemma strong_binary_morphism_morphism
  `{StrongSetoid (S:=X)} `{StrongSetoid (S:=Y)} `{StrongSetoid (S:=Z)}
  f {sm: Strong_Binary_Morphism X Y Z f} : Morphism (X ⇒ Y ⇒ Z) f.
Proof.
  apply binary_morphism_proper_back.
  intros x₁ x₂ Ex y₁ y₂ Ey. unfold_sigs. red_sig.
  rewrite <- (tight_apart _ _). rewrite <- (tight_apart _ _) in Ex. rewrite <- (tight_apart _ _) in Ey.
  intro E. destruct (strong_binary_extensionality f E); contradiction.
Qed.

Hint Extern 8 (Morphism _ _) =>
  match goal with
  | |- Morphism (?X ⇒ ?Y ⇒ ?Z) ?f => first [
    let sm := constr:(_ : Strong_Binary_Morphism X Y Z f) in
    eexact (strong_binary_morphism_morphism f (sm:=sm))
    | fail 2 ]
  | |- Morphism (?X ⇒ ?Y) ?f =>
    let sm := constr:(_ : Strong_Morphism X Y f) in
    eexact (strong_morphism_morphism f (sm:=sm))
  end : typeclass_instances.

Lemma compose_strong_morphism `{X:Subset} `{Y:Subset} `{Z:Subset}
  (f:X ⇀ Y) (g:Y ⇀ Z) `{UnEq X} `{UnEq Y} `{UnEq Z}
  {mf:Strong_Morphism X Y f} {mg:Strong_Morphism Y Z g}
  : Strong_Morphism X Z (g ∘ f).
Proof. split.
+ intros ??. unfold compose. apply _.
+ intros x ? y ? E. apply (strong_extensionality f).
  now apply (strong_extensionality g).
Qed.
Hint Extern 5 (Strong_Morphism _ _ (_ ∘ _)) => class_apply @compose_strong_morphism : typeclass_instances.

Lemma compose_strong_injective `{X:Subset} `{Y:Subset} `{Z:Subset}
  (f:X ⇀ Y) (g:Y ⇀ Z) `{UnEq X} `{UnEq Y} `{UnEq Z}
  `{!StrongInjective X Y f} `{!StrongInjective Y Z g}
  : StrongInjective X Z (g ∘ f).
Proof. pose proof strong_injective_mor f. pose proof strong_injective_mor g.
  split; try apply _.
  intros x ? y ? E. apply (strong_injective g _ _).
  now apply (strong_injective f _ _).
Qed.
Hint Extern 5 (StrongInjective _ _ (_ ∘ _)) => class_apply @compose_strong_injective : typeclass_instances.



Instance strong_injective_injective `{StrongSetoid (S:=X)} `{StrongSetoid (S:=Y)}
  f {s: StrongInjective X Y f} : Injective X Y f.
Proof.
  pose proof (strong_injective_mor f).
  split; try apply _.
  intros ?? ??. rewrite <-!(tight_apart _ _). intros E1 E2.
  destruct E1. now apply (strong_injective f).
Qed.

(* If a morphism satisfies the binary strong extensionality property, it is
  strongly extensional in both coordinates. *)
Instance strong_setoid_morphism_1 :
  ∀ `{sbm: Strong_Binary_Morphism (X:=X) (Y:=Y) (Z:=Z) (f:=f) } `{Equiv X} `{!StrongSetoid X} `{x ∊ X},
    Strong_Morphism Y Z (f x) | 10.
Proof. intros. split. intros ??. apply _. intros y₁ ? y₂ ? E.
  destruct (strong_binary_extensionality f E); trivial.
  now destruct (subirreflexivity (≠) x).
Qed.

Lemma strong_setoid_morphism_2 :
  ∀ `{sbm: Strong_Binary_Morphism (X:=X) (Y:=Y) (Z:=Z) (f:=f) } `{Equiv Y} `{!StrongSetoid Y} `{y ∊ Y},
    Strong_Morphism X Z (λ x, f x y).
Proof. intros. split. intros ??. apply _. intros x₁ ? x₂ ? E.
  destruct (strong_binary_extensionality f E); trivial.
  now destruct (subirreflexivity (≠) y).
Qed.
Hint Extern 5 (Strong_Morphism _ _ (λ x, ?f x _)) => eapply @strong_setoid_morphism_2 : typeclass_instances.

(* Conversely, if a morphism is strongly extensional in both coordinates, it
  satisfies the binary strong extensionality property. We don't make this an
  instance in order to avoid loops. *)
Lemma strong_binary_morphism_both_coordinates
  `{X:Subset} `{Y:Subset} `{Z:Subset} (f : X ⇀ Y ⇀ Z)
  `{UnEq X} `{UnEq Y} `{StrongSetoid _ (S:=Z)} :
    (∀ x, x ∊ X → Strong_Morphism Y Z (f x))
  → (∀ y, y ∊ Y → Strong_Morphism X Z (λ x, f x y))
  → Strong_Binary_Morphism X Y Z f.
Proof. intros. split. intros x ? y ?. apply _.
  rewrite strong_ext_equiv_2. intros x₁ ? x₂ ? y₁ ? y₂ ? E.
  destruct (subcotransitivity E (f x₂ y₁)).
   left. now apply (strong_extensionality (λ x, f x y₁)).
  right. now apply (strong_extensionality (f x₂)).
Qed.

Lemma strong_binary_morphism_commutative
  `{X:Subset} `{Z:Subset} (f : X ⇀ X ⇀ Z)
  `{UnEq X} `{StrongSetoid _ (S:=Z)} :
  Commutative f X → (∀ x, x ∊ X → Strong_Morphism X Z (f x))
  → Strong_Binary_Morphism X X Z f.
Proof. intros. apply (strong_binary_morphism_both_coordinates f). apply _.
  intros y ?. split. intros ??; apply _. intros x₁ ? x₂ ?.
  rewrite 2!(Z $ commutativity f _ y). now apply (strong_extensionality (f y)).
Qed.

Lemma strong_morphism_proper : Find_Proper_Signature (@Strong_Morphism) 0
  (∀ `{StrongSetoid (S:=X)} `{StrongSetoid (S:=Y)},
     Proper ((@equiv (X ⇀ Y) _) ==> impl) (Strong_Morphism X Y)).
Proof. red. intros. intros f g E [??].
  assert (Closed (X ⇀ Y) g) by (rewrite <- E; apply _).
  split. apply _. now rewrite <- ( X ⇀ Y $ E).
Qed.
Hint Extern 0 (Find_Proper_Signature (@Strong_Morphism) 0 _) => eexact strong_morphism_proper : typeclass_instances.

Lemma strong_binary_morphism_proper : Find_Proper_Signature (@Strong_Binary_Morphism) 0
  (∀ `{StrongSetoid (S:=X)} `{StrongSetoid (S:=Y)} `{StrongSetoid (S:=Z)},
     Proper ((@equiv (X ⇀ Y ⇀ Z) _) ==> impl) (Strong_Binary_Morphism X Y Z)).
Proof. red. intros. intros f g E sbm.
  assert (Closed (X ⇀ Y ⇀ Z) g) by (rewrite <- E; apply _).
  split. apply _.
  assert (uncurry f = uncurry g) as E2. rewrite <- ( X ⇀ Y ⇀ Z $ E). subreflexivity.
  rewrite <- ( X * Y ⇀ Z $ E2). now destruct sbm.
Qed.
Hint Extern 0 (Find_Proper_Signature (@Strong_Binary_Morphism) 0 _) => eexact strong_binary_morphism_proper : typeclass_instances.


Lemma strong_morphism_proper2 : Find_Proper_Signature (@Strong_Morphism) 1
  (∀ A B Aue Bue, Proper (SubsetOf-->SubsetOf++>eq==>impl) (@Strong_Morphism A B Aue Bue)).
Proof. red. intros. intros S1 S2 ES T1 T2 ET f g Ef ?. unfold flip in ES. rewrite <- Ef.
  split. rewrite <- (_ : SubsetOf (S1 ⇀ T1) (S2 ⇀ T2)). apply _.
  intros ?? ?? E. exact (strong_extensionality f E).
Qed.
Hint Extern 0 (Find_Proper_Signature (@Strong_Morphism) 1 _) => eexact strong_morphism_proper2 : typeclass_instances.

Lemma strong_binary_morphism_proper2 : Find_Proper_Signature (@Strong_Binary_Morphism) 1
  (∀ A B C Aue Bue Cue, Proper (SubsetOf-->SubsetOf-->SubsetOf++>eq==>impl) (@Strong_Binary_Morphism A B C Aue Bue Cue)).
Proof. red. intros. intros S1 S2 ES T1 T2 ET U1 U2 EU f g Ef ?. unfold flip in ES, ET. rewrite <- Ef.
  split. rewrite <- (_ : SubsetOf (S1 ⇀ T1 ⇀ U1) (S2 ⇀ T2 ⇀ U2)). apply _.
  rewrite strong_ext_equiv_2. intros ?? ?? ?? ?? E. exact (strong_binary_extensionality f E).
Qed.
Hint Extern 0 (Find_Proper_Signature (@Strong_Binary_Morphism) 1 _) => eexact strong_binary_morphism_proper2 : typeclass_instances.

Lemma strong_injective_proper : Find_Proper_Signature (@StrongInjective) 0
  (∀ `{StrongSetoid (S:=X)} `{StrongSetoid (S:=Y)},
     Proper ((@equiv (X ⇀ Y) _) ==> impl) (StrongInjective X Y)).
Proof. red. intros. intros f g E ?. pose proof strong_injective_mor f.
  assert (Strong_Morphism X Y g) by (rewrite <- E; apply _).
  split; try apply _. intros x ? y ? E2.
  rewrite <-(E x x), <-(E y y); try now red_sig.
  now apply (strong_injective f _ _).
Qed.
Hint Extern 0 (Find_Proper_Signature (@StrongInjective) 0 _) => eexact strong_injective_proper : typeclass_instances.


Section dec_setoid_morphisms.
  Context `{StrongSetoid (S:=X)} `{!DenialInequality X} `{StrongSetoid (S:=Y)}.

  Instance dec_strong_morphism (f : X ⇀ Y) `{!Morphism (X ⇒ Y) f} : Strong_Morphism X Y f.
  Proof. split. now apply morphism_closed.
    intros x ? y ? E. rewrite (denial_inequality _ _). contradict E. apply (equiv_nue _ _).
    now rewrite_on X -> E.
  Qed.

  Context `{!DenialInequality Y}.

  Instance dec_strong_injective (f : X ⇀ Y) `{!Injective X Y f} : StrongInjective X Y f.
  Proof. pose proof injective_mor f.
    split; try apply _.
    intros x ? y ?. rewrite ?(denial_inequality _ _). intro E. contradict E.
    exact (injective f x y E).
  Qed.

  Context `{StrongSetoid (S:=Z)}.

  Instance dec_strong_binary_morphism (f : X ⇀ Y ⇀ Z) `{!Morphism (X ⇒ Y ⇒ Z) f}
    : Strong_Binary_Morphism X Y Z f.
  Proof. split. now apply binary_morphism_closed. rewrite strong_ext_equiv_2.
    intros x₁ ? x₂ ? y₁ ? y₂ ? E1.
    case (subcotransitivity E1 (f x₂ y₁)); rewrite ?(denial_inequality _ _); intro E2;
    [ left | right ]; intro E3; destruct (uneq_ne _ _ E2).
    now rewrite_on X -> E3. now rewrite_on Y -> E3.
  Qed.

End dec_setoid_morphisms.

Section strong_cancellation.

  Context `{StrongSetoid (S:=R)} `{!Closed (R ⇀ R ⇀ R) op}.

  Lemma strong_right_cancel_from_left `{!Commutative op R}
    `{z ∊ R} `{!StrongLeftCancellation op z R} : StrongRightCancellation op z R.
  Proof. intros x ? y ? E.
    rewrite_on R -> (commutativity op x z), (commutativity op y z).
    now apply (strong_left_cancellation op _ R).
  Qed.

  Global Instance strong_left_cancellation_cancel `{z ∊ R} `{!StrongLeftCancellation op z R} : LeftCancellation op z R | 20.
  Proof.
    intros x ? y ?. rewrite <-!(tight_apart _ _). intro E. contradict E.
    now apply (strong_left_cancellation op _ R).
  Qed.

  Global Instance strong_right_cancellation_cancel `{z ∊ R} `{!StrongRightCancellation op z R} : RightCancellation op z R | 20.
  Proof.
    intros x ? y ?. rewrite <-!(tight_apart _ _). intros E. contradict E.
    now apply (strong_right_cancellation op _ R).
  Qed.

End strong_cancellation.
