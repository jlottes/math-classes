Require Import abstract_algebra interfaces.orders.

Ltac subreflexivity    := first [ apply (subreflexivity _) | apply subreflexivity]; trivial.
Ltac subsymmetry       := first [ apply (subsymmetry _ _)  | apply subsymmetry   ]; trivial.
Ltac subtransitivity y := apply (subtransitivity _ y _); trivial.

Tactic Notation "subsymmetry" "in" hyp(H) := apply (subsymmetry _ _) in H.

(* add subreflexivity, subsymmetry to the easy tactic (and thereby now) *)
Ltac easy ::=
  let rec use_hyp H :=
    match type of H with
    | _ /\ _ => exact H || destruct_hyp H
    | _ => try solve [inversion H]
    end
  with do_intro := let H := fresh in intro H; use_hyp H
  with destruct_hyp H := case H; clear H; do_intro; do_intro in
  let rec use_hyps :=
    match goal with
    | H : _ /\ _ |- _ => exact H || (destruct_hyp H; use_hyps)
    | H : _ |- _ => solve [inversion H]
    | _ => idtac
    end in
  let rec do_atom :=
    solve [ reflexivity | symmetry; trivial
          | subreflexivity | subsymmetry ] ||
    contradiction ||
    (split; do_atom)
  with do_ccl := trivial with eq_true; repeat do_intro; do_atom in
  (use_hyps; do_ccl) || fail "Cannot solve this goal".

Hint Extern 20 (?x ∊ ?T) => match goal with
  | sub : _ ⊆ ?T |- _ => eapply (subset (SubsetOf:=sub) x)
end : typeclass_instances.

Lemma subset_every `(S:Subset A) : S ⊆ every A. Proof λ _ _, I.
Hint Extern 2 (_ ⊆ every _) => eapply @subset_every : typeclass_instances.

Lemma subset_singleton_element `{Setoid (S:=X)} x `{x ∊ X} : x ∊ {{x}}.
Proof. assert (x=x) by subreflexivity. firstorder. Qed.
Hint Extern 2 (?x ∊ {{?x}}) => eapply @subset_singleton_element: typeclass_instances.

Lemma subset_singleton_subset `{Setoid (S:=X)} x `{x ∊ X} : {{x}} ⊆ X.
Proof. firstorder. Qed.
Hint Extern 2 ((@subset_singleton _ _ ?X _) ⊆ ?X) => eapply @subset_singleton_subset : typeclass_instances.


Lemma every_SubReflexive     `(R:relation A) `{!Reflexive R}    : SubReflexive    (every A) R. Proof. firstorder. Qed.
Lemma every_SubIrreflexive   `(R:relation A) `{!Irreflexive R}  : SubIrreflexive  (every A) R. Proof. firstorder. Qed.
Lemma every_SubSymmetric     `(R:relation A) `{!Symmetric R}    : SubSymmetric    (every A) R. Proof. firstorder. Qed.
Lemma every_SubTransitive    `(R:relation A) `{!Transitive R}   : SubTransitive   (every A) R. Proof. intros ? _ y _ ? _ ??. now transitivity y. Qed.
(*Lemma every_SubCoTransitive  `(R:relation A) `{!CoTransitive R} : SubCoTransitive R (Every A). Proof. firstorder. Qed*)
Lemma every_SubAntiSymmetric {A} (eq le:relation A) `{!AntiSymmetric eq le} : SubAntiSymmetric (Ae:=eq) (every A) le. Proof. firstorder. Qed.

Hint Extern 2 (SubReflexive     (every _) ?R) => eexact (every_SubReflexive     R) : typeclass_instances.
Hint Extern 2 (SubIrreflexive   (every _) ?R) => eexact (every_SubIrreflexive   R) : typeclass_instances.
Hint Extern 2 (SubSymmetric     (every _) ?R) => eexact (every_SubSymmetric     R) : typeclass_instances.
Hint Extern 2 (SubTransitive    (every _) ?R) => eexact (every_SubTransitive    R) : typeclass_instances.
(*Hint Extern 2 (SubCoTransitive  ?R (Every _)) => eexact (Every_SubCoTransitive  R) : typeclass_instances.*)
Hint Extern 2 (SubAntiSymmetric (every _) ?R) => eapply @every_SubAntiSymmetric : typeclass_instances.

Lemma every_SubEquivalence `(R:relation A) `{!Equivalence R} : SubEquivalence (every A) R. Proof. split; apply _. Qed.
Hint Extern 2 (SubEquivalence (every _) ?R) => eexact (every_SubEquivalence R) : typeclass_instances.

Instance subset_equivalence A: Equivalence (@equiv (Subset A) _).
Proof. split.
+ intros ??. tauto.
+ intros ?? E ?. split; intro; now apply E.
+ intros ??? E1 E2 ?. split; intro. now apply E2, E1. now apply E1, E2.
Qed.

Lemma subset_setoid A: Setoid (every (Subset A)). Proof _ : SubEquivalence _ (=).
Hint Extern 5 (Setoid (every (Subset _))) => eapply @subset_setoid : typeclass_instances.

Instance subsetof_preorder T: PreOrder (@SubsetOf T).
Proof. split.
+ intros ??. tauto.
+ intros ??? E1 E2. firstorder.
Qed.

Lemma subset_sub_sub_eq {T} (A B:Subset T) `{!A ⊆ B} `{!B ⊆ A} : A = B.
Proof. intro. intuition. Qed.

Instance subsetof_antisym T: AntiSymmetric (=) (@SubsetOf T) := subset_sub_sub_eq.

Lemma subset_partialorder A : PartialOrder (Ale:=SubsetOf) (every (Subset A)).
Proof. split; try apply _. firstorder. Qed.

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

Lemma closed_proper : Find_Proper_Signature (@closed) 0
  (∀ A B, Proper ((⊆) --> (⊆) ++> (⊆)) (@closed A B)).
Proof. intros ?? ??? ???. firstorder. Qed.
Hint Extern 0 (Find_Proper_Signature (@closed) 0 _) => eexact closed_proper : typeclass_instances.

Instance closed_range `(S:Subset) `(T:Subset) f `{C:!Closed (S ==> T) f} `{D:x ∊ S} : f x ∊ T | 10.
Proof C x D.

(* This covers all arities, but with large proof terms. *)
(*
Instance closed_partial `(S:Subset) `(T:Subset) `(U:Subset) f
   `{C:!Closed (S ==> T ==> U) f} `{D:x ∊ S} : Closed (T ==> U) (f x) | 10.
Proof C x D.
*)

Instance closed_binary `(S:Subset) `(T:Subset) `(U:Subset)
  f `{C:!Closed (S ==> T ==> U) f} `{Dx:x ∊ S} `{Dy:y ∊ T} : f x y ∊ U | 9.
Proof C x Dx y Dy.

Lemma id_closed {A} (S T:Subset A) {sub: S ⊆ T} : Closed (S ==> T) id.
Proof. intros ? I. apply sub. exact I. Qed.
Hint Extern 0 (@Closed _ _ id) => eapply @id_closed : typeclass_instances.

Ltac unfold_sigs :=
  repeat match goal with E : (?S, ?R)%signature ?x ?y |- _ =>
    let el0 := fresh "el" in let el1 := fresh "el" in
    destruct E as [[el0 el1] E]
  end.
Ltac red_sig :=
  match goal with |- (?S, ?R)%signature ?x ?y =>
    split; [split; try apply _ | idtac ]
  end.


Section restrict_rel_subset.
  Context `(S:Subset A) (R:relation A).

  Instance restrict_rel_subset_refl `{!SubReflexive S R} `{x ∊ S} : Proper (S, R) x.
  Proof. split; [firstorder | subreflexivity]. Qed.

  Instance restrict_rel_subset_refl_pp `{!SubReflexive S R} `{x ∊ S} : ProperProxy (S, R)%signature x.
  Proof @restrict_rel_subset_refl _ x _.

  Instance restrict_rel_subset_refl_fp `{!SubReflexive S R} `{x ∊ S} : Find_Proper_Proper (S, R) x.
  Proof @restrict_rel_subset_refl _ x _.

  Instance restrict_rel_subset_sym `{!SubSymmetric S R} : Symmetric (S,R)%signature.
  Proof. intros. intros ?? E. unfold_sigs. red_sig. subsymmetry. Qed.

  Instance restrict_rel_subset_sym_fp `{!SubSymmetric S R} : Find_Proper_Symmetric (S,R)%signature.
  Proof restrict_rel_subset_sym.

  Instance restrict_rel_subset_trans `{!SubTransitive S R} : Transitive (S,R)%signature.
  Proof. intros. intros ? y ? ??. unfold_sigs. red_sig. subtransitivity y. Qed.

  Definition to_restrict_rel `{x ∊ S} `{y ∊ S} (E:R x y) : (S, R)%signature x y.
  Proof. split. split; assumption. exact E. Defined.

  Definition from_restrict_rel x y (E: (S,R)%signature x y) : R x y.
  Proof. unfold restrict_rel in E. tauto. Qed.
End restrict_rel_subset.
Arguments to_restrict_rel {A} S {R} {x _} {y _} E.
Arguments from_restrict_rel {A} S R x y E.

Hint Extern 0 (@Proper _ (@restrict_rel _ _ _) _) => eapply @restrict_rel_subset_refl : typeclass_instances.
Hint Extern 0 (@ProperProxy _ (@restrict_rel _ _ _) _) => eapply @restrict_rel_subset_refl_pp : typeclass_instances.
Hint Extern 0 (@Find_Proper_Proper _ (@restrict_rel _ _ _) _) => eapply @restrict_rel_subset_refl_fp : typeclass_instances.
Hint Extern 5 (Symmetric (_,_)%signature) => eapply @restrict_rel_subset_sym : typeclass_instances.
Hint Extern 0 (Find_Proper_Symmetric (_,_)%signature) => eapply @restrict_rel_subset_sym_fp : typeclass_instances.
Hint Extern 5 (Transitive (_,_)%signature) => eapply @restrict_rel_subset_trans : typeclass_instances.

Instance: ∀ (S1 S2 : Subset A) (R:relation A),
  S1 ⊆ S2 → subrelation (S1,R)%signature (S2,R)%signature.
Proof. intros. intros ???. unfold_sigs. now red_sig. Qed.

Lemma restrict_subset_sub_fp {A} (S1 S2 : Subset A) (R:relation A) :
  S1 ⊆ S2 → Find_Proper_Subrelation (S1,R)%signature (S2,R)%signature.
Proof. intro. red. apply _. Qed.
Hint Extern 0 (@Find_Proper_Subrelation  _ (@restrict_rel _ _ ?R) (@restrict_rel _ _ ?R)) => eapply @restrict_subset_sub_fp : typeclass_instances.

Notation "S $ E" := (to_restrict_rel S E) (at level 75, no associativity, only parsing).

Tactic Notation "rewrite_on" constr(S) "->" constr(E) := rewrite -> (to_restrict_rel S E).
Tactic Notation "rewrite_on" constr(S) "<-" constr(E) := rewrite <- (to_restrict_rel S E).

Tactic Notation "rewrite_on" constr(S) "->" constr(E) ","  constr(E2) := rewrite -> (to_restrict_rel S E), -> (to_restrict_rel S E2).
Tactic Notation "rewrite_on" constr(S) "->" constr(E) "," "<-" constr(E2) := rewrite -> (to_restrict_rel S E), <- (to_restrict_rel S E2).
Tactic Notation "rewrite_on" constr(S) "<-" constr(E) ","  constr(E2) := rewrite <- (to_restrict_rel S E), -> (to_restrict_rel S E2).
Tactic Notation "rewrite_on" constr(S) "<-" constr(E) "," "<-" constr(E2) := rewrite <- (to_restrict_rel S E), <- (to_restrict_rel S E2).

Tactic Notation "rewrite_on" constr(S) "->" constr(E) ","      constr(E2) ","      constr(E3) := rewrite -> (to_restrict_rel S E), -> (to_restrict_rel S E2), -> (to_restrict_rel S E3).
Tactic Notation "rewrite_on" constr(S) "->" constr(E) ","      constr(E2) "," "<-" constr(E3) := rewrite -> (to_restrict_rel S E), -> (to_restrict_rel S E2), <- (to_restrict_rel S E3).
Tactic Notation "rewrite_on" constr(S) "->" constr(E) "," "<-" constr(E2) ","      constr(E3) := rewrite -> (to_restrict_rel S E), <- (to_restrict_rel S E2), -> (to_restrict_rel S E3).
Tactic Notation "rewrite_on" constr(S) "->" constr(E) "," "<-" constr(E2) "," "<-" constr(E3) := rewrite -> (to_restrict_rel S E), <- (to_restrict_rel S E2), <- (to_restrict_rel S E3).
Tactic Notation "rewrite_on" constr(S) "<-" constr(E) ","      constr(E2) ","      constr(E3) := rewrite <- (to_restrict_rel S E), -> (to_restrict_rel S E2), -> (to_restrict_rel S E3).
Tactic Notation "rewrite_on" constr(S) "<-" constr(E) ","      constr(E2) "," "<-" constr(E3) := rewrite <- (to_restrict_rel S E), -> (to_restrict_rel S E2), <- (to_restrict_rel S E3).
Tactic Notation "rewrite_on" constr(S) "<-" constr(E) "," "<-" constr(E2) ","      constr(E3) := rewrite <- (to_restrict_rel S E), <- (to_restrict_rel S E2), -> (to_restrict_rel S E3).
Tactic Notation "rewrite_on" constr(S) "<-" constr(E) "," "<-" constr(E2) "," "<-" constr(E3) := rewrite <- (to_restrict_rel S E), <- (to_restrict_rel S E2), <- (to_restrict_rel S E3).

Tactic Notation "rewrite_on" constr(S) "->" constr(E)
  "at" ne_int_or_var_list(o) := rewrite   (to_restrict_rel S E) at o.
Tactic Notation "rewrite_on" constr(S) "<-" constr(E)
  "at" ne_int_or_var_list(o) := rewrite <-(to_restrict_rel S E) at o.

Tactic Notation "rewrite_on" constr(S) "->" constr(E)
  "in" ident(H) := rewrite   (to_restrict_rel S E) in H.
Tactic Notation "rewrite_on" constr(S) "<-" constr(E)
  "in" ident(H) := rewrite <-(to_restrict_rel S E) in H.

Class SubDecision {A B} (S:Subset A) (T:Subset B) (R : A → B → Prop)
  := decide_sub `{x ∊ S} `{y ∊ T} : Decision (R x y).
Arguments decide_sub {A B S T} R {_} x {_} y {_}.

Instance: ∀ `(R : A → B → Prop) `{∀ x y, Decision (R x y)} S T, SubDecision S T R.
Proof. intros. exact (λ x _ y _, decide_rel R x y). Defined.

Instance: ∀ `(R : A → B → Prop) S T `{!SubDecision S T R}, (∀ `{x ∊ S} `{y ∊ T}, Stable (R x y)).
Proof. intros. pose proof decide_sub R x y. apply _. Qed.

Ltac exists_sub x :=
  let S := match goal with |- ex (fun x => ex (fun (y:x ∊ ?S) => _)) => S end
  in exists x; exists (_:x ∊ S).

Lemma SubReflexive_proper : Find_Proper_Signature (@SubReflexive) 0 (∀ A, Proper ((⊆)-->subrelation++>impl) (@SubReflexive A)).
Proof. red; intros; intros S1 S2 ES R1 R2 ER P ?; intros; unfold flip in *; apply ER; apply P; apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@SubReflexive) 0 _) => eexact SubReflexive_proper : typeclass_instances.

Lemma SubIrreflexive_proper : Find_Proper_Signature (@SubIrreflexive) 0
  (∀ A, Proper ((⊆)-->subrelation-->impl) (@SubIrreflexive A)).
Proof. red. intros. intros S1 S2 ES R1 R2 ER P ?. intros. unfold flip in *.
  pose proof (subirreflexivity R1 x) as Q. contradict Q. now apply ER.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SubIrreflexive) 0 _) => eexact SubIrreflexive_proper : typeclass_instances.

Lemma SubSymmetric_proper : Find_Proper_Signature (@SubSymmetric) 0
  (∀ A, Proper ((⊆)-->(=)==>impl) (@SubSymmetric A)).
Proof. intro. intros S1 S2 ES R1 R2 ER P ?. intros. unfold flip in *. apply ER. apply P; try apply _. now apply ER. Qed.
Hint Extern 0 (Find_Proper_Signature (@SubSymmetric) 0 _) => eexact SubSymmetric_proper : typeclass_instances.

Lemma SubTransitive_proper : Find_Proper_Signature (@SubTransitive) 0
  (∀ A, Proper ((⊆)-->(=)==>impl) (@SubTransitive A)).
Proof. intro. intros S1 S2 ES R1 R2 ER P x ? y ? z ? ??. unfold flip in *. apply ER.
  subtransitivity y; now apply ER.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SubTransitive) 0 _) => eexact SubTransitive_proper : typeclass_instances.

Lemma SubCoTransitive_proper : Find_Proper_Signature (@SubCoTransitive) 0
  (∀ A, Proper ((⊆)-->(=)==>impl) (@SubCoTransitive A)).
Proof. intro. intros S1 S2 ES R1 R2 ER ? x ? y ? E z ?. unfold flip in *.
  apply ER in E. destruct (subcotransitivity E z); [left|right]; now apply ER.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SubCoTransitive) 0 _) => eexact SubCoTransitive_proper : typeclass_instances.

Lemma SubEquivalence_proper : Find_Proper_Signature (@SubEquivalence) 0
  (∀ A, Proper ((⊆)-->(=)==>impl) (@SubEquivalence A)).
Proof. intro. intros S1 S2 ES R1 R2 ER ?. unfold flip in *.
  split; try rewrite <- ER, ES; apply _.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SubEquivalence) 0 _) => eexact SubEquivalence_proper : typeclass_instances.

Lemma SubApartness_proper : Find_Proper_Signature (@SubApartness) 0
  (∀ A, Proper ((⊆)-->(=)==>impl) (@SubApartness A)).
Proof. intro. intros S1 S2 ES R1 R2 ER ?. unfold flip in *.
  split; try rewrite <- ER, ES; apply _.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SubApartness) 0 _) => eexact SubApartness_proper : typeclass_instances.

Lemma SubAntiSymmetric_proper : Find_Proper_Signature (@SubAntiSymmetric) 0
  (∀ A, Proper (subrelation++>(⊆)-->subrelation-->impl) (@SubAntiSymmetric A)).
Proof. red. intros. intros e1 e2 Ee S1 S2 ES R1 R2 ER ?. unfold flip in *.
  intros x ? y ? ??. apply Ee. apply (subantisymmetry R1 x y); now apply ER.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SubAntiSymmetric) 0 _) => eexact SubAntiSymmetric_proper : typeclass_instances.
