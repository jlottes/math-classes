Require Import
  abstract_algebra.
Require Export
  theory.setoids.

Section contents.
Context {A S} `{StrongSetoid A (S:=S)}.

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

Global Instance: UnEqualitySetoid S.
Proof. split; try apply _; intros ?? ??; rewrite <- ?(tight_apart _ _); tauto. Qed.

Global Instance: ∀ `{x ∊ S} `{y ∊ S}, Stable (x = y).
Proof. intros. unfold Stable, DN. rewrite <- (tight_apart _ _). tauto. Qed.
End contents.

Lemma tight_apart_proper : Find_Proper_Signature (@TightApart) 0
  (∀ A, Proper ((=)==>(=)==>(⊆)-->impl) (@TightApart A)).
Proof. red. intros. intros e1 e2 Ee u1 u2 Eu S1 S2 ES P. unfold flip in ES.
  intros x ? y ?. split; intro Q.
    apply Ee. apply (tight_apart _ _). contradict Q. now apply Eu.
    intro E. apply Eu in E. generalize E. apply (tight_apart _ _). now apply Ee.
Qed.
Hint Extern 0 (Find_Proper_Signature (@TightApart) 0 _) => eexact tight_apart_proper : typeclass_instances.

Lemma strong_setoid_proper : Find_Proper_Signature (@StrongSetoid) 0
  (∀ A, Proper ((=)==>(=)==>(⊆)-->impl) (@StrongSetoid A)).
Proof. red. intros. intros e1 e2 Ee u1 u2 Eu S1 S2 ES P. unfold flip in ES.
  split; unfold uneq; rewrite <- ?Ee, <- Eu, ES; apply _.
Qed.
Hint Extern 0 (Find_Proper_Signature (@StrongSetoid) 0 _) => eexact strong_setoid_proper : typeclass_instances.

(* In case we have a decidable setoid, we can construct a strong setoid. Again
  we do not make this an instance as it will cause loops *)
Section dec_setoid.
  Context `{UnEq A} {S} `{Setoid A (S:=S)} `{!StandardUnEq S} `{!SubDecision S S (=)}.

  Instance dec_strong_setoid: StrongSetoid S.
  Proof. split; [ split; red | red ]; intros x ?; [| intros y ? ..]; rewrite -> ?(standard_uneq _ _).
  + intro E. contradict E. subreflexivity.
  + intro E. contradict E. subsymmetry.
  + intros E1 z ?. rewrite -> ?(standard_uneq _ _).
    destruct (decide_sub (=) x z) as [E2|?]; [|tauto]. right. contradict E1. subtransitivity z.
  + split. apply stable. tauto.
  Qed.
End dec_setoid.

(*
Hint Extern 19 (StrongSetoid ?S) => match goal with
  | mor : StrongSetoid_Morphism S _ ?f |- _ => eexact (strong_setoidmor_a f (StrongSetoid_Morphism:=mor))
  | mor : StrongSetoid_Morphism _ S ?f |- _ => eexact (strong_setoidmor_b f (StrongSetoid_Morphism:=mor))
  | mor : StrongSetoid_Binary_Morphism S _ _ ?f  |- _ => eexact (strong_binary_setoidmor_a f (StrongSetoid_Binary_Morphism:=mor))
  | mor : StrongSetoid_Binary_Morphism _ S _ ?f  |- _ => eexact (strong_binary_setoidmor_b f (StrongSetoid_Binary_Morphism:=mor))
  | mor : StrongSetoid_Binary_Morphism _ _ S ?f  |- _ => eexact (strong_binary_setoidmor_c f (StrongSetoid_Binary_Morphism:=mor))
end : typeclass_instances.

Hint Extern 10 (?f _ _ ∊ ?S) => match goal with
  | mor : StrongSetoid_Binary_Morphism _ _ S f |- _ => eapply (strong_binary_setoidmor_closed f (StrongSetoid_Binary_Morphism:=mor))
end : typeclass_instances.

Hint Extern 11 (?f _ ∊ ?S) => match goal with
  | mor : StrongSetoid_Morphism _ S f |- _ => eapply (strong_setoidmor_closed f (StrongSetoid_Morphism:=mor))
end : typeclass_instances.
*)
(* Check fun `{StrongSetoid_Morphism (S:=X) (T:=Y) (f:=f)} `{x ∊ X} => _ : f x ∊ Y. *)

Local Existing Instance strong_setoidmor_a.
Local Existing Instance strong_setoidmor_b.
Local Existing Instance strong_binary_setoidmor_a.
Local Existing Instance strong_binary_setoidmor_b.
Local Existing Instance strong_binary_setoidmor_c.

Instance strong_setoidmor_setoidmor `{sm: StrongSetoid_Morphism (S:=X) (T:=Y) (f:=f)} : Setoid_Morphism X Y f.
Proof. pose proof strong_setoidmor_closed f. split; try apply _.
  intros x₁ x₂ Ex. unfold_sigs. red_sig.
  rewrite <- (tight_apart _ _). rewrite <- (tight_apart _ _) in Ex.
  contradict Ex. exact (strong_extensionality f _ _ Ex).
Qed.

(*
Hint Extern 11 (Proper ((?S,=)==>_) ?f) => match goal with
  | mor : StrongSetoid_Morphism S _ f |- _ => eapply (setoidmor_proper f (Setoid_Morphism:=strong_setoidmor_setoidmor (sm:=mor)))
end : typeclass_instances.
*)
(* Check fun `{StrongSetoid_Morphism (S:=X) (T:=Y) (f:=f)} => _ : Proper ((X,=)==>_) f. *)

Lemma strong_binary_setoidmor_binary_setoidmor `{sbm: StrongSetoid_Binary_Morphism (S:=X) (T:=Y) (U:=Z) (f:=f)}
  : Setoid_Binary_Morphism X Y Z f.
Proof. pose proof strong_binary_setoidmor_closed f. split; try apply _.
  intros x₁ x₂ Ex y₁ y₂ Ey. unfold_sigs. red_sig.
  rewrite <- (tight_apart _ _). rewrite <- (tight_apart _ _) in Ex. rewrite <- (tight_apart _ _) in Ey.
  intro E. destruct (strong_binary_extensionality f x₁ y₁ x₂ y₂ E); contradiction.
Qed.

(* If a morphism satisfies the binary strong extensionality property, it is
  strongly extensional in both coordinates. *)
Instance strong_setoid_morphism_1 :
  ∀ `{sbm: StrongSetoid_Binary_Morphism (S:=X) (T:=Y) (U:=Z) (f:=f) } `{x ∊ X},
    StrongSetoid_Morphism Y Z (f x) | 10.
Proof. intros. pose proof strong_binary_setoidmor_closed f. split; try apply _. intros ??; apply _.
  intros y₁ ? y₂ ? E.
  destruct (strong_binary_extensionality f _ _ _ _ E); trivial.
  now destruct (subirreflexivity (≠) x).
Qed.

Lemma strong_setoid_morphism_2 :
  ∀ `{sbm: StrongSetoid_Binary_Morphism (S:=X) (T:=Y) (U:=Z) (f:=f)} `{y ∊ Y},
    StrongSetoid_Morphism X Z (λ x, f x y).
Proof. intros. split; try apply _. intros ??; apply _.
  intros x₁ ? x₂ ? E.
  destruct (strong_binary_extensionality f _ _ _ _ E); trivial.
  now destruct (subirreflexivity (≠) y).
Qed.
Hint Extern 5 (StrongSetoid_Morphism _ _ (λ x, ?f x _)) => eapply @strong_setoid_morphism_2 : typeclass_instances.

(* Conversely, if a morphism is strongly extensional in both coordinates, it
  satisfies the binary strong extensionality property. We don't make this an
  instance in order to avoid loops. *)
Lemma strong_binary_setoid_morphism_both_coordinates
  `{StrongSetoid (S:=X)} `{StrongSetoid (S:=Y)} `{StrongSetoid (S:=Z)}
  `{sm1: ∀ `{z ∊ X}, StrongSetoid_Morphism Y Z (f z)}
  `{sm2: ∀ `{z ∊ Y}, StrongSetoid_Morphism X Z (λ x, f x z)}
  : StrongSetoid_Binary_Morphism X Y Z f.
Proof. assert (Closed (X ==> Y ==> Z) f). intros x ? y ?. apply _.
  split; try apply _. 
  intros x₁ ? y₁ ? x₂ ? y₂ ? E.
  destruct (subcotransitivity E (f x₂ y₁)).
   left. now apply (strong_extensionality (λ x, f x y₁)).
  right. now apply (strong_extensionality (f x₂)).
Qed.

Lemma strong_binary_setoid_morphism_commutative
  `{StrongSetoid A (S:=X)} `{StrongSetoid B (S:=Y)} {f : A → A → B}
  `{!Commutative f X} `{sm1: ∀ `{z ∊ X}, StrongSetoid_Morphism X Y (f z)}
  : StrongSetoid_Binary_Morphism X X Y f.
Proof. assert (Closed (X ==> X ==> Y) f). intros x ? y ?. apply _.
  assert (∀ z, z ∊ X → StrongSetoid_Morphism X Y (λ x, f x z)).
    split; try apply _.
    intros x ?. apply _.
    intros x ? y ?. rewrite_on Y -> (commutativity f x z), (commutativity f y z).
    now apply (strong_extensionality (f z)).
  apply strong_binary_setoid_morphism_both_coordinates.
Qed.

Lemma strong_morphism_proper : Find_Proper_Signature (@StrongSetoid_Morphism) 0
  (∀ A B Ae Be Aue Bue, Proper ((⊆)-->(=)==>eq==>impl) (@StrongSetoid_Morphism A B Ae Be Aue Bue)).
Proof. red. intros. intros S1 S2 ES T1 T2 ET f g Ef ?. unfold flip in ES. rewrite <- Ef.
  split. rewrite ES. apply _. rewrite <- ET. apply _. intros ??. rewrite <- ET. apply _.
  intros ?? ?? E. exact (strong_extensionality f _ _ E).
Qed.
Hint Extern 0 (Find_Proper_Signature (@StrongSetoid_Morphism) 0 _) => eexact strong_morphism_proper : typeclass_instances.

Lemma strong_binary_morphism_proper : Find_Proper_Signature (@StrongSetoid_Binary_Morphism) 0
  (∀ A B C Ae Be Ce Aue Bue Cue, Proper ((⊆)-->(⊆)-->(=)==>eq==>impl) (@StrongSetoid_Binary_Morphism A B C Ae Be Ce Aue Bue Cue)).
Proof. red. intros. intros S1 S2 ES T1 T2 ET U1 U2 EU f g Ef ?. unfold flip in ES, ET. rewrite <- Ef.
  split. rewrite ES. apply _. rewrite ET. apply _. rewrite <- EU. apply _. intros ?? ??. rewrite <- EU. apply _.
  intros ?? ?? ?? ?? E. exact (strong_binary_extensionality f _ _ _ _ E).
Qed.
Hint Extern 0 (Find_Proper_Signature (@StrongSetoid_Binary_Morphism) 0 _) => eexact strong_binary_morphism_proper : typeclass_instances.

Section dec_setoid_morphisms.
  Context `{StrongSetoid (S:=X)} `{!StandardUnEq X} `{StrongSetoid (S:=Y)}.

  Instance dec_strong_morphism (f : X ⇀ Y) `{!Setoid_Morphism X Y f} : StrongSetoid_Morphism X Y f.
  Proof.
    split; try apply _.
    intros x ? y ? E. rewrite (standard_uneq _ _). contradict E. apply (equiv_nue _ _).
    now rewrite_on X -> E.
  Qed.

  Context `{!StandardUnEq Y}.

  Instance dec_strong_injective (f : X ⇀ Y) `{!Injective X Y f} : StrongInjective X Y f.
  Proof. pose proof injective_mor f.
    split; try apply _.
    intros x ? y ?. rewrite ?(standard_uneq _ _). intro E. contradict E.
    exact (injective f x y E).
  Qed.

  Context `{StrongSetoid (S:=Z)}.

  Instance dec_strong_binary_morphism (f : X ⇀ Y ⇀ Z)
    `{sbm: !Setoid_Binary_Morphism X Y Z f} : StrongSetoid_Binary_Morphism X Y Z f.
  Proof. split; try apply _. apply (binary_morphism_closed f).
    intros x₁ ? y₁ ? x₂ ? y₂ ? E1.
    case (subcotransitivity E1 (f x₂ y₁)); rewrite ?(standard_uneq _ _); intro E2;
    [ left | right ]; intro E3; destruct (uneq_ne _ _ E2).
    now rewrite_on X -> E3. now rewrite_on Y -> E3.
  Qed.

End dec_setoid_morphisms.

Section strong_cancellation.

  Context `{StrongSetoid (S:=R)} `{!Closed (R==>R==>R) op}.

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
