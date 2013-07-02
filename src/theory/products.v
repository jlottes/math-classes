Require Import
  abstract_algebra theory.setoids.

Lemma prod_el `{X:Subset} `{Y:Subset} x `{x ∊ X} y `{y ∊ Y} : (x, y) ∊ X * Y.
Proof. firstorder. Qed.
Hint Extern 5 ((_, _) ∊ _ * _) => eapply @prod_el : typeclass_instances.

Lemma prod_subsetof {A B} `{@SubsetOf A X1 X2} `{@SubsetOf B Y1 Y2} : SubsetOf (X1*Y1) (X2*Y2).
Proof. intros [x y]. firstorder. Qed.
Hint Extern 5 (SubsetOf (_ * _) (_ * _)) => eapply @prod_subsetof : typeclass_instances.

Lemma prod_setoid `{Setoid (S:=X)} `{Setoid (S:=Y)} : Setoid (X * Y).
Proof. split.
+ intros [??][??]. now split.
+ intros [??][??][??] [??] [??]. split; subsymmetry.
+ intros [??][??][x y][??][??][??] [??][??]. split. subtransitivity x. subtransitivity y.
Qed.
Hint Extern 5 (Setoid (_ * _)) => eapply @prod_setoid : typeclass_instances.

Lemma prod_subsetoid `{@SubSetoid A Ae X1 X2} `{@SubSetoid B Be Y1 Y2} : X1*Y1 ⊆ X2*Y2.
Proof. pose proof subsetoid_b : Setoid X2. pose proof subsetoid_b : Setoid Y2.
  split; try apply _.
  intros [??][??] [[[??][??]][E1 E2]] [??].
  split. 
    now apply (subsetoid_regular _ _ (X2 $ E1)).
    now apply (subsetoid_regular _ _ (Y2 $ E2)).
Qed.
Hint Extern 5 (_ * _ ⊆ _ * _) => eapply @prod_subsetoid : typeclass_instances.

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
Hint Extern 5 (StrongSetoid (_ * _)) => eapply @prod_strongsetoid : typeclass_instances.

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

Lemma prod_equal_components `{X:Subset} `{Y:Subset} `{Equiv X} `{Equiv Y}
 (x y : X * Y) : fst x = fst y → snd x = snd y → x = y.
Proof. destruct x,y. firstorder. Qed.

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

Lemma prod_inhabited `{X:Subset} `{Y:Subset} `{!Inhabited X} `{!Inhabited Y} : Inhabited (X*Y).
Proof. destruct (inhabited X) as [x ?]. destruct (inhabited Y) as [y ?]. exists (x,y). apply _. Qed.
Hint Extern 2 (Inhabited (_ * _)) => eapply @prod_inhabited : typeclass_instances.

Definition prod_map `{X1:Subset} `{X2:Subset} `{Y1:Subset} `{Y2:Subset}
  (f:X1⇀X2) (g:Y1⇀Y2) : X1*Y1 ⇀ X2*Y2 := λ x, (f (fst x), g (snd x)).

Section prod_map.
  Context `{Setoid (S:=X1)} `{Setoid (S:=X2)}.
  Context `{Setoid (S:=Y1)} `{Setoid (S:=Y2)}.

  Context (f:X1⇀X2) (g:Y1⇀Y2).

  Lemma prod_map_image U V : (prod_map f g)⁺¹(U*V) = (f⁺¹(U) * g⁺¹(V))%subset .
  Proof. unfold prod_map. intros [x y]. split.
    intros [[??][[x' y'][[??][??]]]]. firstorder.
    intros [ [? [x' [??]]] [? [y' [??]]] ]. split. apply _.
      exists_sub (x',y'). now split.
  Qed.

  Context `{!Morphism (X1 ⇒ X2) f} `{!Morphism (Y1 ⇒ Y2) g}.

  Lemma prod_map_image_el U V `{!SubsetOf U X1} `{!SubsetOf V Y1} x `{x ∊ U} y `{y ∊ V}
    : (f x, g y) ∊ (prod_map f g)⁺¹(U*V).
  Proof. rewrite (prod_map_image U V). apply _. Qed.

  Instance prod_map_mor : Morphism (X1*Y1 ⇒ X2*Y2) (prod_map f g).
  Proof. intros [??][??][[[??][??]][E1 E2]]. unfold prod_map. simpl.
    red_sig. now rewrite (_ $ E1), (_ $ E2).
  Qed.

  Lemma prod_map_image_subsetoid U V `{!U ⊆ X1} `{!V ⊆ Y1} : (prod_map f g)⁺¹(U*V) ⊆ X2*Y2.
  Proof. rewrite (prod_map_image U V). apply _. Qed.
End prod_map.
Hint Extern 2 (Morphism _ (prod_map _ _)) => eapply @prod_map_mor : typeclass_instances.
Hint Extern 2 ((prod_map _ _)⁺¹(_ * _) ⊆ _ * _) => eapply @prod_map_image_subsetoid : typeclass_instances.
Hint Extern 2 ((?f _, ?g _) ∊ (prod_map ?f ?g)⁺¹(_ * _)) => eapply @prod_map_image_el : typeclass_instances.

Definition prod_diag `(x:A) := (x,x).
Lemma prod_diag_mor `{Setoid (S:=X)} : Morphism (X ⇒ X*X) prod_diag.
Proof. intros ??[[??]?]. unfold prod_diag. red_sig. now split. Qed.
Hint Extern 2 (Morphism _ prod_diag) => eapply @prod_diag_mor : typeclass_instances.
Hint Extern 2 (prod_diag _ ∊ ?X * ?X) =>
  eapply (morphism_closed prod_diag (m:=prod_diag_mor (X:=X))) : typeclass_instances.

Definition prod_swap {A B} (p:A*B) := let (x,y) := p in (y,x).
Lemma prod_swap_mor `{Setoid (S:=X)} `{Setoid (S:=Y)} : Morphism (X*Y ⇒ Y*X) prod_swap.
Proof. intros [??][??][[[??][??]][??]]. unfold prod_swap. red_sig. now split. Qed.
Hint Extern 2 (Morphism _ prod_swap) => eapply @prod_swap_mor : typeclass_instances.
Hint Extern 2 (prod_swap _ ∊ ?Y * ?X) =>
  eapply (morphism_closed prod_swap (m:=prod_swap_mor (X:=X) (Y:=Y))) : typeclass_instances.

Definition prod_assoc_r {A B C} (p:(A*B)*C) := let (p',z) := p in let (x,y) := p' in (x,(y,z)).
Lemma prod_assoc_r_mor `{Setoid (S:=X)} `{Setoid (S:=Y)} `{Setoid (S:=Z)}
  : Morphism ((X*Y)*Z ⇒ X*(Y*Z)) prod_assoc_r.
Proof. intros [[??]?][[??]?] [[ [[??]?] [[??]?] ] [[??]?]].
  unfold prod_assoc_r. red_sig. now repeat split.
Qed.
Hint Extern 2 (Morphism _ prod_assoc_r) => eapply @prod_assoc_r_mor : typeclass_instances.
Hint Extern 2 (prod_assoc_r _ ∊ ?X * (?Y * ?Z)) =>
  eapply (morphism_closed prod_assoc_r (m:=prod_assoc_r_mor (X:=X) (Y:=Y) (Z:=Z))) : typeclass_instances.

Definition prod_assoc_l {A B C} (p:A*(B*C)) := let (x,p') := p in let (y,z) := p' in ((x,y),z).
Lemma prod_assoc_l_mor `{Setoid (S:=X)} `{Setoid (S:=Y)} `{Setoid (S:=Z)}
  : Morphism (X*(Y*Z) ⇒ (X*Y)*Z) prod_assoc_l.
Proof. intros [?[??]][?[??]] [[ [?[??]] [?[??]] ] [?[??]]].
  unfold prod_assoc_l. red_sig. now repeat split.
Qed.
Hint Extern 2 (Morphism _ prod_assoc_l) => eapply @prod_assoc_l_mor : typeclass_instances.
Hint Extern 2 (prod_assoc_l _ ∊ (?X * ?Y) * ?Z) =>
  eapply (morphism_closed prod_assoc_l (m:=prod_assoc_l_mor (X:=X) (Y:=Y) (Z:=Z))) : typeclass_instances.

Section proj_image.
  Context `{Setoid (S:=X)} `{Setoid (S:=Y)}.

  Lemma prod_diag_image U `{U ⊆ X} : image (X:=X) (Y:=X*X) prod_diag U ⊆ (U*U)%subset .
  Proof. apply (subsetoid_from_subsetof (X*X) _ _).
    intros [??] [[??][?[?[E1 E2]]]]. split. now rewrite <-(X $ E1). now rewrite <-(X $ E2).
  Qed.

  Notation π₁ := (fst:X*Y⇀X).
  Notation π₂ := (snd:X*Y⇀Y).

  Context U `{U ⊆ X*Y}.

  Lemma fst_snd_image : U ⊆ π₁⁺¹(U)*π₂⁺¹(U).
  Proof. apply (subsetoid_from_subsetof (X*Y) _ _). intros [a b] ?.
    destruct (_ : (a,b) ∊ X*Y).
    split; (split; [ apply _ | now exists_sub (a,b) ]).
  Qed.

  Lemma fst_image_inhabited `{!Inhabited U} : Inhabited π₁⁺¹(U).
  Proof. destruct (inhabited U) as [[x y]?].
    destruct (_ : (x,y) ∊ (X*Y)%subset ).
    exists x. split; trivial. now exists_sub (x,y).
  Qed.

  Lemma snd_image_inhabited `{!Inhabited U} : Inhabited π₂⁺¹(U).
  Proof. destruct (inhabited U) as [[x y]?].
    destruct (_ : (x,y) ∊ (X*Y)%subset ).
    exists y. split; trivial. now exists_sub (x,y).
  Qed.
End proj_image.
Hint Extern 2 (prod_diag⁺¹(?U) ⊆ ?U * ?U) => eapply @prod_diag_image : typeclass_instances.
Hint Extern 2 (?U ⊆ fst⁺¹(?U)*snd⁺¹(?U)) => eapply @fst_snd_image : typeclass_instances.
Hint Extern 2 (Inhabited fst⁺¹(?U)) => eapply @fst_image_inhabited : typeclass_instances.
Hint Extern 2 (Inhabited snd⁺¹(?U)) => eapply @snd_image_inhabited : typeclass_instances.

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
