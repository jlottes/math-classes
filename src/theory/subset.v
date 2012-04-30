Require Import abstract_algebra.

Instance subset_equivalence A: Equivalence (@equiv (Subset A) _).
Proof. split.
+ intros ??. tauto.
+ intros ?? E ?. split; intro; now apply E.
+ intros ??? E1 E2 ?. split; intro. now apply E2, E1. now apply E1, E2.
Qed.

Instance subsetof_preorder T: PreOrder (@SubsetOf T).
Proof. split.
+ intros ??. tauto.
+ intros ??? E1 E2. firstorder.
Qed.

Lemma subset_sub_sub_eq {T} (A B:Subset T) `{!A ⊆ B} `{!B ⊆ A} : A = B.
Proof. intro. intuition. Qed.

Instance subsetof_antisym T: AntiSymmetric (=) (@SubsetOf T) := subset_sub_sub_eq.

Instance: ∀ A, subrelation (=) (@SubsetOf A). Proof. firstorder. Qed.
Instance: ∀ A, Find_Proper_PrePartialOrder (=) (@SubsetOf A).
Proof. intro. split; try apply _; red; apply _. Qed.
Instance: ∀ A, Find_Proper_Reflexive (@equiv (Subset A) _).
Proof. intros ? S. change (S = S). reflexivity. Qed.
Instance: ∀ A, Find_Proper_Reflexive (@SubsetOf A).
Proof. intros ? S. change (S ⊆ S). reflexivity. Qed.

Lemma subset_eq_sub_sub {T} (A B:Subset T) : A = B → A ⊆ B ∧ B ⊆ A.
Proof. firstorder. Qed.

Ltac destruct_subset_eq A B := 
  match goal with E:A = B |- _ => destruct (subset_eq_sub_sub _ _ E)
                | E:B = A |- _ => destruct (subset_eq_sub_sub _ _ E)
  end.

Lemma subsetof_proper : Find_Proper_Signature (@SubsetOf) 0
  (∀ A, Proper ((⊆) --> (⊆) ++> impl) (@SubsetOf A)).
Proof. intros ? ?? ? ?? ? ?. firstorder. Qed.
Hint Extern 0 (Find_Proper_Signature (@SubsetOf) 0 _) => eexact subsetof_proper : typeclass_instances.

Lemma element_proper : Find_Proper_Signature (@Element) 0
  (∀ A, Proper ((⊆) ++> eq ==> impl) (@Element A)).
Proof. intros ? ?? S ?? E. rewrite E. unfold impl. apply S. Qed.
Hint Extern 0 (Find_Proper_Signature (@Element) 0 _) => eexact element_proper : typeclass_instances.
      
(* Closed is just another name for Element *)
Lemma Closed_proper : Find_Proper_Signature (@Closed) 0
  (∀ A, Proper ((⊆) ++> eq ==> impl) (@Element A)).
Proof element_proper.
Hint Extern 0 (Find_Proper_Signature (@Closed) 0 _) => eexact Closed_proper : typeclass_instances.

(* closed functions are elements of the following subset of the function space *)
Lemma closed_proper : Find_Proper_Signature (@closed) 0
  (∀ A B, Proper ((⊆) --> (⊆) ++> (⊆)) (@closed A B)).
Proof. intros ?? ??? ???. firstorder. Qed.
Hint Extern 0 (Find_Proper_Signature (@closed) 0 _) => eexact closed_proper : typeclass_instances.

Instance closed_range `(S:Subset) `(T:Subset) f `{C:!Closed (S ==> T) f} `{D:x ∊ S} : f x ∊ T.
Proof C x D.

(* This covers all arities, but with large proof terms. *)
(*
Instance closed_partial `(S:Subset) `(T:Subset) `(U:Subset) f
   `{C:!Closed (S ==> T ==> U) f} `{D:x ∊ S} : Closed (T ==> U) (f x) | 10.
Proof C x D.
*)

Instance closed_binary `(S:Subset) `(T:Subset) `(U:Subset)
  f `{C:!Closed (S ==> T ==> U) f} `{Dx:x ∊ S} `{Dy:y ∊ T} : f x y ∊ U | 5.
Proof C x Dx y Dy.

Lemma id_closed {A} (S T:Subset A) {sub: S ⊆ T} : Closed (S ==> T) id.
Proof. intros ? I. apply sub. exact I. Qed.
Hint Extern 0 (@Closed _ _ id) => eapply @id_closed : typeclass_instances.

Section restrict_rel_subset.
  Context `(S:Subset A) (R:relation A).

  Instance restrict_rel_subset_refl `{!Reflexive R} `{x ∊ S} : Proper (S, R) x.
  Proof. apply restrict_rel_refl. apply _. assumption. Qed.

  Instance restrict_rel_subset_refl_pp `{!Reflexive R} `{x ∊ S} : ProperProxy (S, R)%signature x.
  Proof @restrict_rel_subset_refl _ x _.

  Instance restrict_rel_subset_refl_fp {refl:Find_Proper_Reflexive R} `{x ∊ S} : Find_Proper_Proper (S, R) x.
  Proof @restrict_rel_subset_refl refl x _.

  Definition to_restrict_rel `{x ∊ S} `{y ∊ S} (E:R x y) : (S, R)%signature x y.
  Proof. split. split; assumption. exact E. Defined.

  Definition from_restrict_rel x y (E: (S,R)%signature x y) : R x y.
  Proof. unfold restrict_rel in E. tauto. Qed.
End restrict_rel_subset.
Arguments restrict_rel_subset_refl {A} S {R _} x {_}.
Arguments to_restrict_rel {A} S {R} {x _} {y _} E.
Arguments from_restrict_rel {A} S R x y E.

Hint Extern 0 (@Proper _ (@restrict_rel _ _ _) _) => eapply @restrict_rel_subset_refl : typeclass_instances.
Hint Extern 0 (@ProperProxy _ (@restrict_rel _ _ _) _) => eapply @restrict_rel_subset_refl_pp : typeclass_instances.
Hint Extern 0 (@Find_Proper_Proper _ (@restrict_rel _ _ _) _) => eapply @restrict_rel_subset_refl_fp : typeclass_instances.

Ltac unfold_sigs :=
  repeat match goal with E : (?S, ?R)%signature ?x ?y |- _ =>
    let el0 := fresh "el" in let el1 := fresh "el" in
    destruct E as [[el0 el1] E]; try (change (x ∊ S) in el0; change (y ∊ S) in el1)
  end.
Ltac red_sig :=
  match goal with |- (?S, ?R)%signature ?x ?y =>
    split; [split; [ try (change (x ∊ S); try apply _)
                   | try (change (y ∊ S); try apply _)
                   ]
           | idtac ]
  end.

Instance: ∀ `{Equiv A} (S1 S2 : Subset A) (R:relation A),
  S1 ⊆ S2 → subrelation (S1,R)%signature (S2,R)%signature.
Proof. intros. intros ???. unfold_sigs. now red_sig. Qed.

Lemma restrict_subset_sub_fp `{Equiv A} (S1 S2 : Subset A) (R:relation A) :
  S1 ⊆ S2 → Find_Proper_Subrelation (S1,R)%signature (S2,R)%signature.
Proof. intro. red. apply _. Qed.
Hint Extern 0 (@Find_Proper_Subrelation  _ (@restrict_rel _ _ ?R) (@restrict_rel _ _ ?R)) => eapply @restrict_subset_sub_fp : typeclass_instances.


Tactic Notation "rewrite_on" constr(S) "->" constr(E) := rewrite   (to_restrict_rel S E).
Tactic Notation "rewrite_on" constr(S) "<-" constr(E) := rewrite <-(to_restrict_rel S E).

Tactic Notation "rewrite_on" constr(S) "->" constr(E)
  "at" ne_int_or_var_list(o) := rewrite   (to_restrict_rel S E) at o.
Tactic Notation "rewrite_on" constr(S) "<-" constr(E)
  "at" ne_int_or_var_list(o) := rewrite <-(to_restrict_rel S E) at o.

Tactic Notation "rewrite_on" constr(S) "->" constr(E)
  "in" ident(H) := rewrite   (to_restrict_rel S E) in H.
Tactic Notation "rewrite_on" constr(S) "<-" constr(E)
  "in" ident(H) := rewrite <-(to_restrict_rel S E) in H.

Instance subproper_closed1
  `{R:relation A} `{R':relation B}
  `{!Reflexive R}
   (f:A → B)
   (S:Subset A) (S':Subset B)
  `{!SubProper ((S,R) ==> (S',R')) f}
 : Closed (S ==> S') f.
Proof. intros x ?. now destruct (subproper_prf x x (restrict_rel_subset_refl S x)). Qed.

Instance subproper_closed2
  `{R1:relation A} `{R2:relation B} `{R3:relation C}
  `{!Reflexive R1} `{!Reflexive R2} 
   (f:A → B → C)
   (S1:Subset A) (S2:Subset B) (S3:Subset C)
  `{!SubProper ((S1,R1) ==> (S2,R2) ==> (S3,R3)) f}
 : Closed (S1 ==> S2 ==> S3) f.
Proof. intros x ? y ?.
  now destruct (subproper_prf x x (restrict_rel_subset_refl S1 x)
                              y y (restrict_rel_subset_refl S2 y)).
Qed.

Class SubDecision `(R : A → B → Prop) (S:Subset A) (T:Subset B)
  := decide_sub `{x ∊ S} `{y ∊ T} : Decision (R x y).
Arguments decide_sub {A B} R {S T _} x {_} y {_}.

Instance: ∀ `(R : A → B → Prop) `{∀ x y, Decision (R x y)} (S:Subset A) (T:Subset B),
  SubDecision R S T.
Proof. intros. exact (λ x _ y _, decide_rel R x y). Defined.
