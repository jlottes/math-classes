Require Import
  abstract_algebra theory.subset.

Lemma prod_el `{X:Subset} `{Y:Subset} x `{x ∊ X} y `{y ∊ Y} : (x, y) ∊ X * Y.
Proof. firstorder. Qed.
Hint Extern 5 ((_, _) ∊ _ * _) => eapply @prod_el : typeclass_instances.

Lemma prod_setoid `{Setoid (S:=X)} `{Setoid (S:=Y)} : Setoid (X * Y).
Proof. split.
+ intros [??][??]. now split.
+ intros [??][??][??] [??] [??]. split; subsymmetry.
+ intros [??][??][x y][??][??][??] [??][??]. split. subtransitivity x. subtransitivity y.
Qed.
Hint Extern 5 (Setoid (_ * _)) => eapply @prod_setoid : typeclass_instances.

Lemma prod_strongsetoid `{StrongSetoid (S:=X)} `{StrongSetoid (S:=Y)} : StrongSetoid (X * Y).
Proof. split. split.
+ intros [??][??] [E|E]; contradict E; apply (subirreflexivity _ _).
+ intros [??][??][??][??] [E|E]; do 2 red; subsymmetry in E; tauto.
+ intros [a b][??][c d][??] [E|E] [x y][??].
  destruct (subcotransitivity E x); [left | right]; do 2 red; tauto.
  destruct (subcotransitivity E y); [left | right]; do 2 red; tauto.
+ intros [??][??][??][??]. unfold equiv, uneq, prod_equiv, prod_uneq.
  rewrite <-2!(tight_apart _ _). tauto.
Qed.

Lemma pair_proper: Find_Proper_Signature (@pair) 0
  (∀ `{Setoid (S:=X)} `{Setoid (S:=Y)}, Proper ((X,=) ==> (Y,=) ==> (X * Y,=)) pair).
Proof. red. intros. intros ?? E1 ?? E2. unfold_sigs. red_sig. now split. Qed.
Hint Extern 0 (Find_Proper_Signature (@pair) 0 _) => eexact pair_proper : typeclass_instances.

Lemma fst_closed `{X:Subset} `{Y:Subset} : Closed (X * Y ⇀ X) fst.
Proof. intros [??]. firstorder. Qed.

Lemma snd_closed `{X:Subset} `{Y:Subset} : Closed (X * Y ⇀ Y) snd.
Proof. intros [??]. firstorder. Qed.

Lemma fst_morphism `{X:Subset} `{Y:Subset} `{Equiv X} `{Equiv Y} : Morphism (X * Y ⇒ X) fst.
Proof. intros [??][??] [[[??][??]][??]]. now red_sig. Qed.
Hint Extern 2 (Morphism _ fst) => class_apply @fst_morphism : typeclass_instances.

Lemma snd_morphism `{X:Subset} `{Y:Subset} `{Equiv X} `{Equiv Y} : Morphism (X * Y ⇒ Y) snd.
Proof. intros [??][??] [[[??][??]][??]]. now red_sig. Qed.
Hint Extern 2 (Morphism _ snd) => class_apply @snd_morphism : typeclass_instances.

Hint Extern 2 (fst ?p ∊ ?X) =>
  let A := type of (snd p) in
  let S := fresh "S" in evar (S:@Subset A);
  let Y := eval unfold S in S in clear S;
  let el := fresh "el" in assert (p ∊ X * Y) as el by typeclasses eauto;
  eapply (@fst_closed _ X _ Y p el)
: typeclass_instances.

Hint Extern 2 (snd ?p ∊ ?Y) =>
  let A := type of (fst p) in
  let S := fresh "S" in evar (S:@Subset A);
  let X := eval unfold S in S in clear S;
  let el := fresh "el" in assert (p ∊ X * Y) as el by typeclasses eauto;
  eapply (@snd_closed _ X _ Y p el)
: typeclass_instances.


Section product.
  Context `{Setoid A (S:=X)} `{Setoid B (S:=Y)}.

  Program Instance prod_dec `(A_dec : ∀ x y : A, Decision (x = y)) `(B_dec : ∀ x y : B, Decision (x = y))
    : ∀ x y : A * B, Decision (x = y) := λ x y,
    match A_dec (fst x) (fst y) with
    | left _ => match B_dec (snd x) (snd y) with left _ => left _ | right _ => right _ end
    | right _ => right _
    end.
  Solve Obligations using (program_simpl; firstorder).

  Context `{!SubDecision X X (=)} `{!SubDecision Y Y (=)}.
  Instance prod_sub_dec : SubDecision (X*Y) (X*Y) (=).
  Proof. intros [a b] [??] [c d] [??].
    destruct (decide_sub (=) a c); [|right; now intros [??]].
    destruct (decide_sub (=) b d); [left; split |right; intros [??]]; easy.
  Defined.

End product.
Hint Extern 2 (Decision (@equiv _ prod_equiv _ _)) => eapply @prod_dec : typeclass_instances.


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
