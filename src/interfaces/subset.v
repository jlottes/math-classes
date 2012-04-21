Require Import canonical_names restrict_rel.

Class Subset A := set_comp : A → Prop.
Class Element `{S:Subset A} x := element : S x.
Notation "x ∊ S" := (Element (A:=_) (S:=S) x) (at level 70) : mc_scope.
Notation "(∊ S )" := (Element (S:=S)) (only parsing) : mc_scope.

Instance subset_equiv T: Equiv (Subset T) := λ A B, ∀ x, x ∊ A ↔ x ∊ B.

Class SubsetOf `(S:Subset A) (T:Subset A) := subset x `{!x ∊ S} :> x ∊ T.
Notation "S ⊆ T" := (SubsetOf S T) (at level 70) : mc_scope.
Notation "(⊆)" := (SubsetOf) (only parsing) : mc_scope.
Hint Extern 2 (?x ⊆ ?x) => reflexivity : typeclass_instances.
Hint Extern 2 (?x ⊆ ?y) => auto_trans : typeclass_instances.
Notation " ( S ,⊆) " := (restrict_rel S (⊆)) : signature_scope.

Definition Every A : Subset A := λ _, True.
Lemma every_element {A} x : x ∊ (Every A). Proof I.
Hint Extern 0 (@Element ?A (Every ?A) _) => eapply @every_element : typeclass_instances.

(** [ x ∊ {{y}} ] is convertible to [ x = y ]. *)
Instance subset_singleton `{Equiv A}: Singleton A (Subset A) := flip equiv.
Lemma subset_singleton_element `{Ae: Equiv A} `{!Equivalence Ae} (x:A) : x ∊ {{x}}.
Proof. change (x=x). reflexivity. Qed.
Hint Extern 0 (@Element _ (@singleton _ (Subset _) (@subset_singleton _ _) ?x) ?x) => eapply @subset_singleton_element : typeclass_instances.

(** Define the [Prop]

        [Closed (S ==> T ==> ... ==> U) f]
 
    to mean
     
        [x ∊ S → y ∊ T → ... → f x y ... ∊ U.]
*)

(* Closed is just another name for Element *)
Class Closed {A} (S:Subset A) f := closed_prf : f ∊ S.
Definition closed {A B} (S:Subset A) (T:Subset B) : Subset (A → B) := λ f, ∀ x, x ∊ S → (f x) ∊ T.

Delimit Scope closed_sig_scope with closed_sig.

Arguments Closed {A}%type (S)%closed_sig _.
Arguments closed {A B}%type (S T)%closed_sig _.

Module ClosedNotations.

  Notation " S ==> T " := (@closed _ _ (S%closed_sig) (T%closed_sig))
    (right associativity, at level 55) : closed_sig_scope.

End ClosedNotations.

Export ClosedNotations.

(** SubProper instances effectively declare Closed instances *)
Class SubProper {A} (R : relation A) (m : A) : Prop := subproper_prf :> Proper R m.
Arguments SubProper {A}%type R%signature m.

