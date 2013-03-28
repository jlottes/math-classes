Require Import abstract_algebra interfaces.orders.

Definition subset_empty        {A} : Bottom (@Subset A) := λ x, False.
Definition subset_intersection {A} : Meet (@Subset A) := λ S T x, x ∊ S ∧ x ∊ T.
Definition subset_union        {A} : Join (@Subset A) := λ S T x, x ∊ S ∨ x ∊ T.
Hint Extern 2 (Bottom Subset) => eapply @subset_empty : typeclass_instances.
Hint Extern 2 (Meet Subset) => eapply @subset_intersection : typeclass_instances.
Hint Extern 2 (Join Subset) => eapply @subset_union : typeclass_instances.
Hint Extern 10 (Top Subset) => eapply @every : typeclass_instances.
Hint Extern 10 (Meet (_ → Prop)) => eapply @subset_intersection : typeclass_instances.
Hint Extern 10 (Join (_ → Prop)) => eapply @subset_union : typeclass_instances.

Hint Extern 2 (_ ∊ _ ⊓ _) => split; trivial; apply _ : typeclass_instances.
Hint Extern 2 (_ ∊ _ ⊔ _) => first [ left; trivial; apply _
                                   | right; trivial; apply _ ] : typeclass_instances.


Ltac subreflexivity    := first [ apply (subreflexivity _) | rapply (subreflexivity)]; trivial.
Ltac subsymmetry       := first [ apply (subsymmetry _ _)  | rapply (subsymmetry)   ]; trivial.
Ltac subtransitivity y := apply (subtransitivity _ y _); trivial.

Tactic Notation "subsymmetry" "in" hyp(H) :=  apply (subsymmetry _ _) in H.

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

(*
Hint Extern 20 (?x ∊ ?T) => match goal with
  | sub : _ ⊆ ?T |- _ => eapply (subset (SubsetOf:=sub) x)
end : typeclass_instances.
*)

Hint Extern 2 (SubsetOf ?S (every _)) => eexact (λ `{x ∊ S}, I) : typeclass_instances.



Lemma every_SubReflexive     `(R:relation A) `{!Reflexive R}   {S} : SubReflexive    S R. Proof. firstorder. Qed.
Lemma every_SubIrreflexive   `(R:relation A) `{!Irreflexive R} {S} : SubIrreflexive  S R. Proof. firstorder. Qed.
Lemma every_SubSymmetric     `(R:relation A) `{!Symmetric R}   {S} : SubSymmetric    S R. Proof. firstorder. Qed.
Lemma every_SubTransitive    `(R:relation A) `{!Transitive R}  {S} : SubTransitive   S R. Proof. intros ? _ y _ ? _ ??. now transitivity y. Qed.
(*Lemma every_SubCoTransitive  `(R:relation A) `{!CoTransitive R} : SubCoTransitive R (Every A). Proof. firstorder. Qed*)
Lemma every_SubAntiSymmetric {A} (eq le:relation A) `{!AntiSymmetric eq le} {S} : SubAntiSymmetric (Ae:=eq) S le. Proof. firstorder. Qed.
Lemma every_SubRelation `{@subrelation A R1 R2} {S} : SubRelation S R1 R2. Proof. firstorder. Qed.

Hint Extern 2 (SubReflexive     (every _) ?R) => eapply @every_SubReflexive   : typeclass_instances.
Hint Extern 2 (SubIrreflexive   (every _) ?R) => eapply @every_SubIrreflexive : typeclass_instances.
Hint Extern 2 (SubSymmetric     (every _) ?R) => eapply @every_SubSymmetric   : typeclass_instances.
Hint Extern 2 (SubTransitive    (every _) ?R) => eapply @every_SubTransitive  : typeclass_instances.
(*Hint Extern 2 (SubCoTransitive  ?R (Every _)) => eexact (Every_SubCoTransitive  R) : typeclass_instances.*)
Hint Extern 2 (SubAntiSymmetric (every _) ?R) => eapply @every_SubAntiSymmetric : typeclass_instances.

Lemma every_SubEquivalence `(R:relation A) `{!Equivalence R} {S} : SubEquivalence S R. Proof. split; firstorder. Qed.
Hint Extern 2 (SubEquivalence (every _) _) => eapply @every_SubEquivalence : typeclass_instances.

Lemma SubRelation_reflexive `{S:Subset} R : SubRelation S R R. Proof. firstorder. Qed.
Hint Extern 2 (SubRelation _ ?R ?R) => eapply @SubRelation_reflexive : typeclass_instances.

Instance subset_equivalence A: Equivalence (@equiv (@Subset A) _).
Proof. split.
+ intros ??. tauto.
+ intros ?? E ?. split; intro; now apply E.
+ intros ??? E1 E2 ?. split; intro. now apply E2, E1. now apply E1, E2.
Qed.

Hint Extern 5 (Setoid (every Subset)) => eapply @every_SubEquivalence : typeclass_instances.

Instance subsetof_preorder T: PreOrder (@SubsetOf T).
Proof. firstorder. Qed.

Instance subsetof_antisym T: AntiSymmetric (=) (@SubsetOf T).
Proof. firstorder. Qed.

Hint Extern 2 (SubsetOf ?x ?x) => reflexivity : typeclass_instances.
Hint Extern 20 (SubsetOf ?X ?Y) => match goal with
    E : X = Y |- _ => intro; apply E
  | E : Y = X |- _ => intro; apply E
end : typeclass_instances.

Lemma subset_partialorder A : PartialOrder (Ale:=@SubsetOf A) (every Subset).
Proof. split; try apply _. firstorder. Qed.
Hint Extern 2 (PartialOrder (every Subset)) => eapply @subset_partialorder : typeclass_instances.

Lemma subset_lattice_order {A} : LatticeOrder (Ale:=SubsetOf) (every (@Subset A)).
Proof. split; (split; [ apply _ | intros ????; apply _ | firstorder..]). Qed.
Hint Extern 2 (LatticeOrder (every Subset)) => eapply @subset_lattice_order : typeclass_instances.
Hint Extern 2 (MeetSemiLatticeOrder (every Subset)) => eapply @lattice_order_meet : typeclass_instances.
Hint Extern 2 (JoinSemiLatticeOrder (every Subset)) => eapply @lattice_order_join : typeclass_instances.

Lemma subset_bounded_meet_semilattice {A} : BoundedMeetSemiLattice (every (@Subset A)).  Proof. firstorder. Qed.
Lemma subset_bounded_join_semilattice {A} : BoundedJoinSemiLattice (every (@Subset A)).  Proof. firstorder. Qed.
Hint Extern 2 (BoundedMeetSemiLattice (every Subset)) => eapply @subset_bounded_meet_semilattice : typeclass_instances.
Hint Extern 2 (BoundedJoinSemiLattice (every Subset)) => eapply @subset_bounded_meet_semilattice : typeclass_instances.

Lemma subset_dist_lattice {A} : DistributiveLattice (every (@Subset A)). Proof. firstorder. Qed.
Hint Extern 2 (DistributiveLattice (every Subset)) => eapply @subset_dist_lattice : typeclass_instances.

Hint Extern 2 (SubsetOf (?X ⊓ ?Y) ?X) => apply (meet_lb_l (L:=every Subset) _ _) : typeclass_instances.
Hint Extern 2 (SubsetOf (?X ⊓ ?Y) ?Y) => apply (meet_lb_r (L:=every Subset) _ _) : typeclass_instances.
Hint Extern 2 (SubsetOf ?X (?X ⊔ ?Y)) => apply (join_ub_l (L:=every Subset) _ _) : typeclass_instances.
Hint Extern 2 (SubsetOf ?Y (?X ⊔ ?Y)) => apply (join_ub_r (L:=every Subset) _ _) : typeclass_instances.

Instance: ∀ A, subrelation (=) (@SubsetOf A). Proof. firstorder. Qed.
Instance: ∀ A, Find_Proper_PrePartialOrder (=) (@SubsetOf A).
Proof. intro. split; try apply _; red; apply _. Qed.
Instance: ∀ A, Find_Proper_Reflexive (@equiv (@Subset A) _).
Proof. intros ? S. now change (S = S). Qed.
Instance: ∀ A, Find_Proper_Reflexive (@SubsetOf A).
Proof. intros ? S. exact (_ : SubsetOf S S). Qed.

Lemma subsetof_proper : Find_Proper_Signature (@SubsetOf) 0
  (∀ A, Proper (SubsetOf --> SubsetOf ++> impl) (@SubsetOf A)).
Proof. intros ? ?? ? ?? ? ?. firstorder. Qed.
Hint Extern 0 (Find_Proper_Signature (@SubsetOf) 0 _) => eexact subsetof_proper : typeclass_instances.

Lemma element_proper : Find_Proper_Signature (@Element) 0
  (∀ A, Proper (SubsetOf ++> eq ==> impl) (@Element A)).
Proof. intros ? ?? S ?? E. rewrite E. unfold impl. apply S. Qed.
Hint Extern 0 (Find_Proper_Signature (@Element) 0 _) => eexact element_proper : typeclass_instances.

(* Closed is just another name for Element *)
Lemma Closed_proper : Find_Proper_Signature (@Closed) 0
  (∀ A, Proper (SubsetOf ++> eq ==> impl) (@Closed A)).
Proof element_proper.
Hint Extern 0 (Find_Proper_Signature (@Closed) 0 _) => eexact Closed_proper : typeclass_instances.

Lemma closed_fun_subset {A B} `{@SubsetOf A X1 X2} `{@SubsetOf B Y1 Y2} : SubsetOf (X2 ⇀ Y1) (X1 ⇀ Y2).
Proof. firstorder. Qed.
Hint Extern 3 (SubsetOf (_ ⇀ _) (_ ⇀ _)) => eapply @closed_fun_subset : typeclass_instances.

Lemma closed_fun_proper : Find_Proper_Signature (@closed_fun) 0
  (∀ A B, Proper (SubsetOf --> SubsetOf ++> SubsetOf) (@closed_fun A B)).
Proof. red; intros. intros ??? ???. unfold flip in *. apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@closed_fun) 0 _) => eexact closed_fun_proper : typeclass_instances.

Lemma closed_range `(S:Subset) `(T:Subset) f `{C:!Closed (S ⇀ T) f} `{D:x ∊ S} : f x ∊ T.
Proof C x D.

Lemma closed_binary `(S:Subset) `(T:Subset) `(U:Subset)
  f `{C:!Closed (S ⇀ T ⇀ U) f} `{Dx:x ∊ S} `{Dy:y ∊ T} : f x y ∊ U.
Proof C x Dx y Dy.

Lemma id_closed `(S:Subset) T {sub: SubsetOf S T} : Closed (S ⇀ T) id.
Proof. intros ? I. apply sub. exact I. Qed.
Hint Extern 0 (@Closed _ _ id) => eapply @id_closed : typeclass_instances.
Hint Extern 1 (id ?x ∊ ?X) => change (x ∊ X); apply _ : typeclass_instances.

Ltac unfold_sigs :=
  repeat match goal with E : (restrict_rel ?S ?R) ?x ?y |- _ =>
    let el0 := fresh "el" in let el1 := fresh "el" in
    destruct E as [[el0 el1] E]
  end.
Ltac red_sig :=
  match goal with |- (restrict_rel ?S ?R) ?x ?y =>
    split; [split; try apply _ | idtac ]
  end.


Section restrict_rel_subset.
  Context `(S:@Subset A) (R:relation A).

  Instance restrict_rel_subset_refl `{!SubReflexive S R} `{x ∊ S} : Proper (restrict_rel S R) x.
  Proof. split; [firstorder | subreflexivity]. Qed.

  Instance restrict_rel_subset_sym `{!SubSymmetric S R} : Symmetric (restrict_rel S R).
  Proof. intros. intros ?? E. unfold_sigs. red_sig. subsymmetry. Qed.

  Instance restrict_rel_subset_trans `{!SubTransitive S R} : Transitive (restrict_rel S R).
  Proof. intros. intros ? y ? ??. unfold_sigs. red_sig. subtransitivity y. Qed.

  Instance restrict_rel_subset_per `{!SubEquivalence S R} : RelationClasses.PER (restrict_rel S R) := {}.

  Definition to_restrict_rel `{x ∊ S} `{y ∊ S} (E:R x y) : (restrict_rel S R) x y.
  Proof. split. split; assumption. exact E. Defined.

  Definition from_restrict_rel x y (E: (restrict_rel S R) x y) : R x y.
  Proof. unfold restrict_rel in E. tauto. Qed.
End restrict_rel_subset.
Arguments to_restrict_rel {A} S {R} {x _} {y _} E.
Arguments from_restrict_rel {A} S R x y E.

Hint Extern 0 (@Proper _ (@restrict_rel _ _ _) _) => eapply @restrict_rel_subset_refl : typeclass_instances.
Hint Extern 0 (@ProperProxy _ (@restrict_rel _ _ _) _) => eapply @restrict_rel_subset_refl : typeclass_instances.
Hint Extern 0 (@Find_Proper_Proper _ (@restrict_rel _ _ _) _) => eapply @restrict_rel_subset_refl : typeclass_instances.
Hint Extern 5 (Symmetric (restrict_rel _ _)) => eapply @restrict_rel_subset_sym : typeclass_instances.
Hint Extern 0 (Find_Proper_Symmetric (restrict_rel _ _)) => eapply @restrict_rel_subset_sym : typeclass_instances.
Hint Extern 5 (Transitive (restrict_rel _ _)) => eapply @restrict_rel_subset_trans : typeclass_instances.
Hint Extern 3 (RelationClasses.PER (restrict_rel _ _)) => eapply @restrict_rel_subset_per : typeclass_instances.

Local Hint Extern 20 (?x ∊ ?T) => match goal with
  | sub : SubsetOf _ ?T |- _ => eapply (subset (SubsetOf:=sub) x)
end : typeclass_instances.

Lemma restrict_rel_subset_subrel `(S1:Subset) S2 R `{!SubsetOf S1 S2}
  : subrelation (restrict_rel S1 R) (restrict_rel S2 R).
Proof. intros. intros ???. unfold_sigs. split; [split; apply (subset (S:=S1))|];trivial. Qed.
Hint Extern 4 (subrelation  (restrict_rel _ ?R) (restrict_rel _ ?R)) => eapply @restrict_rel_subset_subrel : typeclass_instances.
Hint Extern 4 (Find_Proper_Subrelation  (restrict_rel _ ?R) (restrict_rel _ ?R)) => eapply @restrict_rel_subset_subrel : typeclass_instances.

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

Tactic Notation "mc_replace" constr(x) "with" constr(y) "on" constr(S) "by" tactic(tac) :=
  let E := fresh "E" in assert (x = y) as E by tac; rewrite_on S -> E; clear E.

Tactic Notation "mc_replace" constr(x) "with" constr(y) "on" constr(S) "in" hyp(H) "by" tactic(tac) :=
  let E := fresh "E" in assert (x = y) as E by tac; rewrite (S $ E) in H; clear E.

Class StrongSubDecision `(S:Subset) `(T:Subset) (R:_ → _ → Prop)
  := decide_sub_strong x y : {x ∊ S → y ∊ T → R x y} + {x ∊ S → y ∊ T → ¬ R x y}.
Arguments decide_sub_strong {_ S _ T} R {_} x y.

Ltac destruct_dec_sub_strong E :=
  match goal with |- context [ decide_sub_strong ?R ?x ?y ] =>
    let E1 := fresh "Edec" in destruct (decide_sub_strong R x y) as [E1|E1];
      pose proof E1 _ _ as E; clear E1
  end.

Class SubDecision `(S:Subset) `(T:Subset) R
  := decide_sub `{x ∊ S} `{y ∊ T} : Decision (R x y).
Arguments decide_sub {_ _ _ _} R {_} x {_} y {_}.

Instance: ∀ `(R : A → B → Prop) `{∀ x y, Decision (R x y)} S T, StrongSubDecision S T R.
Proof. intros. intros x y. destruct (decide_rel R x y) as [E|E]; [left|right]; intuition. Defined.

Instance: ∀ {A B} `{@StrongSubDecision A X B Y R}, SubDecision X Y R | 5.
Proof. intros. intros x ? y ?. destruct (decide_sub_strong R x y) as [E|E]; [left|right]; intuition. Defined.

Instance: ∀ `(R : A → B → Prop) `{∀ x y, Decision (R x y)} S T, SubDecision S T R.
Proof. intros. exact (λ x _ y _, decide_rel R x y). Defined.

Instance: ∀ `(R : A → B → Prop) S T `{!SubDecision S T R}, (∀ `{x ∊ S} `{y ∊ T}, Stable (R x y)).
Proof. intros. pose proof decide_sub R x y. apply _. Qed.

Ltac exists_sub x :=
  exists x;
  let S := match goal with |- ex (fun (y:x ∊ ?S) => _) => S end
  in exists (_:x ∊ S).

Tactic Notation "exists_sub" constr(x) := exists_sub x.
Tactic Notation "exists_sub" constr(x) constr(y) := exists_sub x; exists_sub y.
Tactic Notation "exists_sub" constr(x) constr(y) constr (z) := exists_sub x; exists_sub y z.
Tactic Notation "exists_sub" constr(x) constr(y) constr (z) constr(w)
  := exists_sub x; exists_sub y z w.
Tactic Notation "exists_sub" constr(x) constr(y) constr (z) constr(w) constr(u)
  := exists_sub x; exists_sub y z w u.
Tactic Notation "exists_sub" constr(x) constr(y) constr (z) constr(w) constr(u)
  constr(v) := exists_sub x; exists_sub y z w u v.


Lemma SubReflexive_proper : Find_Proper_Signature (@SubReflexive) 0 (∀ A, Proper (SubsetOf-->subrelation++>impl) (@SubReflexive A)).
Proof. red; intros; intros S1 S2 ES R1 R2 ER P ?; intros; unfold flip in *; apply ER; apply P; apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@SubReflexive) 0 _) => eexact SubReflexive_proper : typeclass_instances.

Lemma SubIrreflexive_proper : Find_Proper_Signature (@SubIrreflexive) 0
  (∀ A, Proper (SubsetOf-->subrelation-->impl) (@SubIrreflexive A)).
Proof. red. intros. intros S1 S2 ES R1 R2 ER P ?. intros. unfold flip in *.
  pose proof (subirreflexivity R1 x) as Q. contradict Q. now apply ER.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SubIrreflexive) 0 _) => eexact SubIrreflexive_proper : typeclass_instances.

Lemma SubSymmetric_proper : Find_Proper_Signature (@SubSymmetric) 0
  (∀ A, Proper (SubsetOf-->(=)==>impl) (@SubSymmetric A)).
Proof. intro. intros S1 S2 ES R1 R2 ER P ?. intros. unfold flip in *. apply ER. apply P; try apply _. now apply ER. Qed.
Hint Extern 0 (Find_Proper_Signature (@SubSymmetric) 0 _) => eexact SubSymmetric_proper : typeclass_instances.

Lemma SubTransitive_proper : Find_Proper_Signature (@SubTransitive) 0
  (∀ A, Proper (SubsetOf-->(=)==>impl) (@SubTransitive A)).
Proof. intro. intros S1 S2 ES R1 R2 ER P x ? y ? z ? ??. unfold flip in *. apply ER.
  subtransitivity y; now apply ER.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SubTransitive) 0 _) => eexact SubTransitive_proper : typeclass_instances.

Lemma SubCoTransitive_proper : Find_Proper_Signature (@SubCoTransitive) 0
  (∀ A, Proper (SubsetOf-->(=)==>impl) (@SubCoTransitive A)).
Proof. intro. intros S1 S2 ES R1 R2 ER ? x ? y ? E z ?. unfold flip in *.
  apply ER in E. destruct (subcotransitivity E z); [left|right]; now apply ER.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SubCoTransitive) 0 _) => eexact SubCoTransitive_proper : typeclass_instances.

Lemma SubEquivalence_proper : Find_Proper_Signature (@SubEquivalence) 0
  (∀ A, Proper (SubsetOf-->(=)==>impl) (@SubEquivalence A)).
Proof. intro. intros S1 S2 ES R1 R2 ER ?. unfold flip in *.
  split; try rewrite <- ER, ES; apply _.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SubEquivalence) 0 _) => eexact SubEquivalence_proper : typeclass_instances.

Lemma SubApartness_proper : Find_Proper_Signature (@SubApartness) 0
  (∀ A, Proper (SubsetOf-->(=)==>impl) (@SubApartness A)).
Proof. intro. intros S1 S2 ES R1 R2 ER ?. unfold flip in *.
  split; try rewrite <- ER, ES; apply _.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SubApartness) 0 _) => eexact SubApartness_proper : typeclass_instances.

Lemma SubAntiSymmetric_proper : Find_Proper_Signature (@SubAntiSymmetric) 0
  (∀ A, Proper (subrelation++>SubsetOf-->subrelation-->impl) (@SubAntiSymmetric A)).
Proof. red. intros. intros e1 e2 Ee S1 S2 ES R1 R2 ER ?. unfold flip in *.
  intros x ? y ? ??. apply Ee. apply (subantisymmetry R1 x y); now apply ER.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SubAntiSymmetric) 0 _) => eexact SubAntiSymmetric_proper : typeclass_instances.
