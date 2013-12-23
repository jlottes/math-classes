Require Import abstract_algebra interfaces.orders.

Hint Extern 2 (_ ∊ _ ⊓ _) => split; trivial; apply _ : typeclass_instances.
Hint Extern 2 (_ ∊ _ ⊔ _) => first [ left; trivial; apply _
                                   | right; trivial; apply _ ] : typeclass_instances.

Lemma empty_subset `(S:set) : Subset ⊥ S. Proof. firstorder. Qed.
Hint Extern 2 (Subset ⊥ _) => eapply @empty_subset : typeclass_instances.

Ltac subreflexivity    := first [ apply (reflexivity _) | rapply (reflexivity) | apply reflexivity; apply _ | reflexivity ]; trivial.
Ltac subsymmetry       := first [ apply (symmetry _ _)  | rapply (symmetry)    | symmetry ]; trivial.
Ltac subtransitivity y := apply (transitivity _ y _); trivial.

Tactic Notation "subsymmetry" "in" hyp(H) :=  apply (symmetry _ _) in H.

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


Hint Extern 2 (Subset ?S (every _)) => eexact (λ `{x ∊ S}, I) : typeclass_instances.



Lemma every_Reflexive     `(R:relation A) `{!ReflexiveT   R} {S} : Reflexive    S R. Proof. firstorder. Qed.
Lemma every_Irreflexive   `(R:relation A) `{!IrreflexiveT R} {S} : Irreflexive  S R. Proof. firstorder. Qed.
Lemma every_Symmetric     `(R:relation A) `{!SymmetricT   R} {S} : Symmetric    S R. Proof. firstorder. Qed.
Lemma every_Transitive    `(R:relation A) `{!TransitiveT  R} {S} : Transitive   S R. Proof. intros ? _ y _ ? _ ??. now transitivity y. Qed.
(*Lemma every_SubCoTransitive  `(R:relation A) `{!CoTransitive R} : SubCoTransitive R (Every A). Proof. firstorder. Qed*)
Lemma every_AntiSymmetric {A} (eq le:relation A) `{!AntiSymmetricT eq le} {S} : AntiSymmetric (Ae:=eq) S le. Proof. firstorder. Qed.
Lemma every_SubRelation `{@subrelation A R1 R2} {S} : SubRelation S R1 R2. Proof. firstorder. Qed.

Hint Extern 2 (Reflexive     (every _) ?R) => eapply @every_Reflexive   : typeclass_instances.
Hint Extern 2 (Irreflexive   (every _) ?R) => eapply @every_Irreflexive : typeclass_instances.
Hint Extern 2 (Symmetric     (every _) ?R) => eapply @every_Symmetric   : typeclass_instances.
Hint Extern 2 (Transitive    (every _) ?R) => eapply @every_Transitive  : typeclass_instances.
(*Hint Extern 2 (SubCoTransitive  ?R (Every _)) => eexact (Every_SubCoTransitive  R) : typeclass_instances.*)
Hint Extern 2 (AntiSymmetric (every _) ?R) => eapply @every_AntiSymmetric : typeclass_instances.

Lemma every_Equivalence `(R:relation A) `{!EquivalenceT R} {S} : Equivalence S R.
Proof. split; [apply every_Reflexive | apply every_Symmetric|apply every_Transitive]; apply _. Qed.
Hint Extern 2 (Equivalence (every _) _) => eapply @every_Equivalence : typeclass_instances.

Lemma SubRelation_reflexive `{S:set} R : SubRelation S R R. Proof. firstorder. Qed.
Hint Extern 2 (SubRelation _ ?R ?R) => eapply @SubRelation_reflexive : typeclass_instances.

Instance set_equivalence A: EquivalenceT (@equiv (@set A) _).
Proof. firstorder. Qed.

Notation Sets := (every set).

Hint Extern 2 (Equivalence _ (@equiv _ set_equiv)) => eapply @every_Equivalence : typeclass_instances.
Hint Extern 2 (Setoid (Ae:=set_equiv) _) => eapply @every_Equivalence : typeclass_instances.
(*Hint Extern 5 (Setoid Sets) => eapply @every_Equivalence : typeclass_instances.*)

Instance subset_preorder T: PreOrder (@Subset T).
Proof. firstorder. Qed.

Instance subset_antisym T: AntiSymmetricT (=) (@Subset T).
Proof. firstorder. Qed.

Hint Extern 2 (Reflexive  _ Subset) => eapply @every_Reflexive  : typeclass_instances.
Hint Extern 2 (Transitive _ Subset) => eapply @every_Transitive : typeclass_instances.
Hint Extern 2 (AntiSymmetric _ Subset) => eapply @every_AntiSymmetric : typeclass_instances.

Hint Extern 2 (Subset ?x ?x) => reflexivity : typeclass_instances.
(*Hint Extern 20 (Subset ?X ?Y) => match goal with
    E : X = Y |- _ => intro; apply E
  | E : Y = X |- _ => intro; apply E
end : typeclass_instances.*)

Hint Extern 2 (_ ∊ (λ S, Subset S ?X)) => red : typeclass_instances.
Hint Extern 2 (_ ∊ Subset _) => red : typeclass_instances.

Lemma subset_partialorder A : PartialOrder (Ale:=@Subset A) Sets.
Proof. split; try apply _. firstorder. Qed.
Hint Extern 2 (PartialOrder Sets) => eapply @subset_partialorder : typeclass_instances.

Lemma subset_lattice_order {A} : LatticeOrder (Ale:=@Subset A) Sets.
Proof. split; (split; [ apply _ | intros ????; apply _ | firstorder..]). Qed.
Hint Extern 2 (LatticeOrder Sets) => eapply @subset_lattice_order : typeclass_instances.
Hint Extern 2 (MeetSemiLatticeOrder Sets) => eapply @lattice_order_meet : typeclass_instances.
Hint Extern 2 (JoinSemiLatticeOrder Sets) => eapply @lattice_order_join : typeclass_instances.

Lemma subset_bounded_meet_semilattice {A} : BoundedMeetSemiLattice (every (@set A)).  Proof. firstorder. Qed.
Lemma subset_bounded_join_semilattice {A} : BoundedJoinSemiLattice (every (@set A)).  Proof. firstorder. Qed.
Hint Extern 2 (BoundedMeetSemiLattice Sets) => eapply @subset_bounded_meet_semilattice : typeclass_instances.
Hint Extern 2 (BoundedJoinSemiLattice Sets) => eapply @subset_bounded_join_semilattice : typeclass_instances.

Instance subset_dist_lattice {A} : DistributiveLattice (every (@set A)). Proof. firstorder. Qed.
(*Hint Extern 2 (DistributiveLattice Sets) => eapply @subset_dist_lattice : typeclass_instances.*)

Hint Extern 2 (Subset (?X ⊓ ?Y) ?X) => apply (meet_lb_l (L:=Sets) _ _) : typeclass_instances.
Hint Extern 2 (Subset (?X ⊓ ?Y) ?Y) => apply (meet_lb_r (L:=Sets) _ _) : typeclass_instances.
Hint Extern 2 (Subset ?X (?X ⊔ ?Y)) => apply (join_ub_l (L:=Sets) _ _) : typeclass_instances.
Hint Extern 2 (Subset ?Y (?X ⊔ ?Y)) => apply (join_ub_r (L:=Sets) _ _) : typeclass_instances.

Instance: ∀ A, subrelation (=) (@Subset A). Proof. firstorder. Qed.
Instance: ∀ A, Find_Proper_PrePartialOrder (=) (@Subset A).
Proof. intro. split; try apply _; red; apply _. Qed.
Hint Extern 2 (Find_Proper_Reflexive (@equiv _ set_equiv)) => eapply @Equivalence_Reflexive : typeclass_instances.
Instance: ∀ A, Find_Proper_Reflexive (@Subset A).
Proof. intros ? S. exact (_ : Subset S S). Qed.

Hint Extern 2 (@Find_Proper_PrePartialOrder _ (restrict_rel _ _) (restrict_rel _ Subset)) => eapply @restrict_ppo_fp : typeclass_instances.

Lemma subset_proper : Find_Proper_Signature (@Subset) 0
  (∀ A, Proper (Subset --> Subset ++> impl) (@Subset A)).
Proof. intros ? ?? ? ?? ? ?. firstorder. Qed.
Hint Extern 0 (Find_Proper_Signature (@Subset) 0 _) => eexact subset_proper : typeclass_instances.

Lemma element_proper : Find_Proper_Signature (@Element) 0
  (∀ A, Proper (Subset ++> eq ==> impl) (@Element A)).
Proof. intros ? ?? S ?? E. rewrite E. unfold impl. apply S. Qed.
Hint Extern 0 (Find_Proper_Signature (@Element) 0 _) => eexact element_proper : typeclass_instances.

Lemma inhabited_proper : Find_Proper_Signature (@Inhabited) 0
  (∀ A, Proper (Subset ++> impl) (@Inhabited A)).
Proof. intros ? ?? E [x ?]. exists x. now apply E. Qed.
Hint Extern 0 (Find_Proper_Signature (@Inhabited) 0 _) => eexact inhabited_proper : typeclass_instances.
Hint Extern 2 (_ ∊ Inhabited) => red : typeclass_instances.

Hint Extern 10 (Inhabited ?S) =>
  match goal with H : ?x ∊ ?S |- _ => exists x; exact H end : typeclass_instances.


(* Closed is just another name for Element *)
Lemma Closed_proper : Find_Proper_Signature (@Closed) 0
  (∀ A, Proper (Subset ++> eq ==> impl) (@Closed A)).
Proof element_proper.
Hint Extern 0 (Find_Proper_Signature (@Closed) 0 _) => eexact Closed_proper : typeclass_instances.

Lemma closed_fun_subset {A B} `{@Subset A X1 X2} `{@Subset B Y1 Y2} : Subset (X2 ⇀ Y1) (X1 ⇀ Y2).
Proof. firstorder. Qed.
Hint Extern 3 (Subset (_ ⇀ _) (_ ⇀ _)) => eapply @closed_fun_subset : typeclass_instances.

Lemma closed_fun_proper : Find_Proper_Signature (@closed_fun) 0
  (∀ A B, Proper (Subset --> Subset ++> Subset) (@closed_fun A B)).
Proof. red; intros. intros ??? ???. unfold flip in *. apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@closed_fun) 0 _) => eexact closed_fun_proper : typeclass_instances.

Lemma closed_range `(X:set) `(Y:set) f `{C:!Closed (X ⇀ Y) f} `{D:x ∊ X} : f x ∊ Y.
Proof C x D.

Lemma closed_binary `(X:set) `(Y:set) `(Z:set)
  f `{C:!Closed (X ⇀ Y ⇀ Z) f} `{Dx:x ∊ X} `{Dy:y ∊ Y} : f x y ∊ Z.
Proof C x Dx y Dy.

Lemma id_closed `(S:set) T {sub: Subset S T} : Closed (S ⇀ T) id.
Proof. intros ? el. apply sub. exact el. Qed.
Hint Extern 0 (@Closed _ _ id) => eapply @id_closed : typeclass_instances.
Hint Extern 1 (id ?x ∊ ?X) => change (x ∊ X) : typeclass_instances.

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
  Context `(S:@set A) (R:relation A).

  Instance restrict_rel_subset_refl `{!Reflexive S R} `{x ∊ S} : Proper (restrict_rel S R) x.
  Proof. split; [firstorder | subreflexivity]. Qed.

  Instance restrict_rel_subset_sym `{!Symmetric S R} : SymmetricT (restrict_rel S R).
  Proof. intros. intros ?? E. unfold_sigs. red_sig. subsymmetry. Qed.

  Instance restrict_rel_subset_trans `{!Transitive S R} : TransitiveT (restrict_rel S R).
  Proof. intros. intros ? y ? ??. unfold_sigs. red_sig. subtransitivity y. Qed.

  Instance restrict_rel_subset_per `{!Equivalence S R} : RelationClasses.PER (restrict_rel S R) := {}.

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
Hint Extern 5 (@Proper _ (@restrict_rel _ _ _) _) => eapply @to_restrict_rel : typeclass_instances.
Hint Extern 5 (@ProperProxy _ (@restrict_rel _ _ _) _) => eapply @to_restrict_rel : typeclass_instances.
Hint Extern 5 (@Find_Proper_Proper _ (@restrict_rel _ _ _) _) => eapply @to_restrict_rel : typeclass_instances.
Hint Extern 5 (SymmetricT (restrict_rel _ _)) => eapply @restrict_rel_subset_sym : typeclass_instances.
Hint Extern 0 (Find_Proper_Symmetric (restrict_rel _ _)) => eapply @restrict_rel_subset_sym : typeclass_instances.
Hint Extern 5 (TransitiveT (restrict_rel _ _)) => eapply @restrict_rel_subset_trans : typeclass_instances.
Hint Extern 3 (RelationClasses.PER (restrict_rel _ _)) => eapply @restrict_rel_subset_per : typeclass_instances.

Local Hint Extern 20 (?x ∊ ?T) => match goal with
  | sub : Subset _ ?T |- _ => eapply (subset (Subset:=sub) x)
end : typeclass_instances.

Lemma restrict_rel_subset_subrel `(S:set) T R `{!Subset S T}
  : subrelation (restrict_rel S R) (restrict_rel T R).
Proof. intros. intros ???. unfold_sigs. split; [split; apply (subset (S:=S))|];trivial. Qed.
Hint Extern 4 (subrelation  (restrict_rel _ ?R) (restrict_rel _ ?R)) => eapply @restrict_rel_subset_subrel : typeclass_instances.
Hint Extern 4 (Find_Proper_Subrelation  (restrict_rel _ ?R) (restrict_rel _ ?R)) => eapply @restrict_rel_subset_subrel : typeclass_instances.

Lemma to_eq {A x y} : @equiv A eq x y → x ≡ y. Proof id.

Tactic Notation "eq_replace" constr(x) "with" constr(y) :=
  let E := fresh "E" in cut (x = y); [ intro E; rewrite ->(to_eq E); clear E |].

Tactic Notation "eq_replace" constr(x) "with" constr(y) "by" tactic(tac) :=
  let E := fresh "E" in assert (x = y) as E by tac; rewrite ->(to_eq E); clear E.

Tactic Notation "eq_replace" constr(x) "with" constr(y) "in" hyp(H) "by" tactic(tac) :=
  let E := fresh "E" in assert (x = y) as E by tac; rewrite ->(to_eq E) in H; clear E.

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

Tactic Notation "mc_replace" constr(x) "with" constr(y) "on" constr(S) :=
  let E := fresh "E" in cut (x = y); [ intro E; rewrite_on S -> E; clear E |].

Tactic Notation "mc_replace" constr(x) "with" constr(y) "on" constr(S) "by" tactic(tac) :=
  let E := fresh "E" in assert (x = y) as E by tac; rewrite_on S -> E; clear E.

Tactic Notation "mc_replace" constr(x) "with" constr(y) "on" constr(S) "in" hyp(H) "by" tactic(tac) :=
  let E := fresh "E" in assert (x = y) as E by tac; rewrite (S $ E) in H; clear E.

Ltac destruct_dec_sub_strong E :=
  match goal with |- context [ decide_sub_strong ?R ?x ?y ] =>
    let E1 := fresh "Edec" in destruct (decide_sub_strong R x y) as [E1|E1];
      pose proof E1 _ _ as E; clear E1
  end.

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


Lemma Reflexive_proper : Find_Proper_Signature (@Reflexive) 0 (∀ A, Proper (Subset-->subrelation++>impl) (@Reflexive A)).
Proof. red; intros; intros S1 S2 ES R1 R2 ER P ?; intros; unfold flip in *; apply ER; apply P; apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@Reflexive) 0 _) => eexact Reflexive_proper : typeclass_instances.

Lemma Irreflexive_proper : Find_Proper_Signature (@Irreflexive) 0
  (∀ A, Proper (Subset-->subrelation-->impl) (@Irreflexive A)).
Proof. red. intros. intros S1 S2 ES R1 R2 ER P ?. intros. unfold flip in *.
  pose proof (irreflexivity R1 x) as Q. contradict Q. now apply ER.
Qed.
Hint Extern 0 (Find_Proper_Signature (@Irreflexive) 0 _) => eexact Irreflexive_proper : typeclass_instances.

Lemma Symmetric_proper : Find_Proper_Signature (@Symmetric) 0
  (∀ A, Proper (Subset-->(=)==>impl) (@Symmetric A)).
Proof. intro. intros S1 S2 ES R1 R2 ER P ?. intros. unfold flip in *. apply ER. apply P; try apply _. now apply ER. Qed.
Hint Extern 0 (Find_Proper_Signature (@Symmetric) 0 _) => eexact Symmetric_proper : typeclass_instances.

Lemma Transitive_proper : Find_Proper_Signature (@Transitive) 0
  (∀ A, Proper (Subset-->(=)==>impl) (@Transitive A)).
Proof. intro. intros S1 S2 ES R1 R2 ER P x ? y ? z ? ??. unfold flip in *. apply ER.
  subtransitivity y; now apply ER.
Qed.
Hint Extern 0 (Find_Proper_Signature (@Transitive) 0 _) => eexact Transitive_proper : typeclass_instances.

Lemma CoTransitive_proper : Find_Proper_Signature (@CoTransitive) 0
  (∀ A, Proper (Subset-->(=)==>impl) (@CoTransitive A)).
Proof. intro. intros S1 S2 ES R1 R2 ER ? x ? y ? E z ?. unfold flip in *.
  apply ER in E. destruct (cotransitivity E z); [left|right]; now apply ER.
Qed.
Hint Extern 0 (Find_Proper_Signature (@CoTransitive) 0 _) => eexact CoTransitive_proper : typeclass_instances.

Lemma Equivalence_proper : Find_Proper_Signature (@Equivalence) 0
  (∀ A, Proper (Subset-->(=)==>impl) (@Equivalence A)).
Proof. intro. intros S1 S2 ES R1 R2 ER ?. unfold flip in *.
  split; try rewrite <- ER, ES; apply _.
Qed.
Hint Extern 0 (Find_Proper_Signature (@Equivalence) 0 _) => eexact Equivalence_proper : typeclass_instances.

Lemma Apartness_proper : Find_Proper_Signature (@Apartness) 0
  (∀ A, Proper (Subset-->(=)==>impl) (@Apartness A)).
Proof. intro. intros S1 S2 ES R1 R2 ER ?. unfold flip in *.
  split; try rewrite <- ER, ES; apply _.
Qed.
Hint Extern 0 (Find_Proper_Signature (@Apartness) 0 _) => eexact Apartness_proper : typeclass_instances.

Lemma AntiSymmetric_proper : Find_Proper_Signature (@AntiSymmetric) 0
  (∀ A, Proper (subrelation++>Subset-->subrelation-->impl) (@AntiSymmetric A)).
Proof. red. intros. intros e1 e2 Ee S1 S2 ES R1 R2 ER ?. unfold flip in *.
  intros x ? y ? ??. apply Ee. apply (antisymmetry R1 x y); now apply ER.
Qed.
Hint Extern 0 (Find_Proper_Signature (@AntiSymmetric) 0 _) => eexact AntiSymmetric_proper : typeclass_instances.
