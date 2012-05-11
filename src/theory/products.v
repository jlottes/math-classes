Require Import
  abstract_algebra theory.subset.

Definition prod_equiv `{Equiv A} `{Equiv B} : Equiv (A * B) :=
  λ p q, let (a,b) := p in let (c,d) := q in a = c ∧ b = d.
(* Avoid eager application *)
Hint Extern 10 (Equiv (_ * _)) => eapply @prod_equiv : typeclass_instances.

Definition prod_subset {A B} (S:Subset A) (T:Subset B) : Subset (A*B) := λ p, let (a,b) := p in a ∊ S ∧ b ∊ T.
Infix "*" := prod_subset : subset_scope.

Lemma prod_el {A B} S T (x:A) `{x ∊ S} (y:B) `{y ∊ T} : pair x y ∊ S * T.
Proof. firstorder. Qed.
Hint Extern 5 (pair _ _ ∊ _ * _) => eapply @prod_el : typeclass_instances.

Instance prod_setoid `{Setoid (S:=X)} `{Setoid (S:=Y)} : Setoid (X * Y).
Proof. split.
+ intros [??][??]. now split.
+ intros [??][??][??] [??] [??]. split; subsymmetry.
+ intros [??][??][x y][??][??][??] [??][??]. split. subtransitivity x. subtransitivity y.
Qed.

Lemma pair_proper: Find_Proper_Signature (@pair) 0
  (∀ `{Setoid (S:=X)} `{Setoid (S:=Y)}, Proper ((X,=) ==> (Y,=) ==> (X * Y,=)) pair).
Proof. red. intros. intros ?? E1 ?? E2. unfold_sigs. red_sig. now split. Qed.
Hint Extern 0 (Find_Proper_Signature (@pair) 0 _) => eexact pair_proper : typeclass_instances.

Section product.
  Context `{Setoid A (S:=X)} `{Setoid B (S:=Y)}.

  Global Instance: Setoid_Morphism (X * Y) X fst.
  Proof. split; try apply _. intros [??][??] [[[??][??]][??]]. now red_sig. Qed.

  Global Instance: Setoid_Morphism (X * Y) Y snd.
  Proof. split; try apply _. intros [??][??] [[[??][??]][??]]. now red_sig. Qed.
 
  Global Program Instance prod_dec `(A_dec : ∀ x y : A, Decision (x = y)) `(B_dec : ∀ x y : B, Decision (x = y))
    : ∀ x y : A * B, Decision (x = y) := λ x y,
    match A_dec (fst x) (fst y) with
    | left _ => match B_dec (snd x) (snd y) with left _ => left _ | right _ => right _ end
    | right _ => right _
    end.
  Solve Obligations using (program_simpl; firstorder).

  Context `{!SubDecision X X (=)} `{!SubDecision Y Y (=)}.
  Global Instance prod_sub_dec : SubDecision (X*Y) (X*Y) (=) | 20.
  Proof. intros [a b] [??] [c d] [??].
    destruct (decide_sub (=) a c); [|right; now intros [??]].
    destruct (decide_sub (=) b d); [left; split |right; intros [??]]; easy.
  Defined.

End product.

(*
Definition prod_fst_equiv X A `{Equiv X} : relation (X * A) := λ x y, fst x = fst y.

Section product_fst.
  Context `{Setoid X}.

  Global Instance: Equivalence (prod_fst_equiv X A).
  Proof. unfold prod_fst_equiv. firstorder auto. Qed.
End product_fst.

Section dep_product.
  Context (I : Type) (c : I → Type) `{∀ i, Equiv (c i)} `{∀ i, Setoid (c i)}.

  Let dep_prod: Type := ∀ i, c i.

  Instance dep_prod_equiv: Equiv dep_prod := λ x y, ∀ i, x i = y i.

  Global Instance: Setoid dep_prod.
  Proof.
   constructor.
     repeat intro. reflexivity.
    intros ?? E ?. symmetry. apply E.
   intros ? y ??? i. transitivity (y i); firstorder.
  Qed.

  (*
  Global Instance dep_prod_morphism i : Setoid_Morphism (λ c: dep_prod, c i).
  Proof. firstorder auto. Qed.
  *)
End dep_product.
*)
