Require Import
  List
  abstract_algebra interfaces.orders interfaces.metric_spaces
  theory.setoids theory.lattices theory.powerset orders.lattices orders.minmax
  orders.affinely_extended_field
  metric.metric_spaces metric.maps
  stdlib_field_dec.

Local Notation AQ := TheAERationals.A.
Local Notation Q := the_ae_rationals.
Local Notation "Q∞" := (aff_ext Q).
Local Notation Qfull := (aff_ext_full Q).

Lemma union_of_balls_subsetoid1 `{MetricSpace (X:=X)} ε `{ε ∊ Qfull} S {ES: S ⊆ X} (l:list {x|x ∊ S})
  : union_of_balls (X:=X) ε l ⊆ X.
Proof. induction l. simpl. apply _. destruct a as [x ?]. simpl.
  assert (x ∊ X) by now apply ES.
  apply (join_lub (Ale:=SubSetoid) (L:=(⊆ X)) _ _ _); unfold le; apply _.
Qed.
Hint Extern 2 (@union_of_balls _ ?X _ _ _ _ ⊆ ?X) => eapply @union_of_balls_subsetoid1 : typeclass_instances.

Lemma totally_bounded_proper: Find_Proper_Signature (@TotallyBounded) 0
  (∀ A (Ae:Equiv A) (b:Ball A) (X:set), Proper ((=)==>impl) (TotallyBounded (X:=X))).
Proof. red; intros. intros U V E ?. pose proof totally_bounded_msp (X:=X).
  assert (V ⊆ X) by (rewrite <-E; apply _).
  split; try apply _.
  set (f := λ (y:{x | x ∊ U}), match y with exist x el => exist _ x (proj1 (E x) el) end).
  intros ε ?.
  destruct (totally_bounded_def (X:=X) U ε) as [l P].
  exists (map f l).
  assert (∀ (l' : list { x | x ∊ U }),
    union_of_balls (X:=X) ε l' = union_of_balls (X:=X) ε (map f l')) as E'.
    intros l'. induction l'. now simpl. destruct a as [x ?]. simpl.
    now rewrite (Sets $ IHl').
  now rewrite <- (E' l), <-E.
Qed.
Hint Extern 0 (Find_Proper_Signature (@TotallyBounded) 0 _) => eexact totally_bounded_proper : typeclass_instances.

Section totally_bounded.
  Context `{MetricSpace (X:=X)}.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.

  Instance empty_totally_bounded : TotallyBounded ⊥.
  Proof. split; try apply _. intros ??. exists ([] : list {x : X | x ∊ ⊥}). simpl. apply _. Qed.

  Lemma union_of_balls_empty_or_not U `{U ⊆ X} (l:list {x | x ∊ U}) ε `{ε ∊ Q∞} :
    union_of_balls ε l = ⊥ ∨ Inhabited (union_of_balls ε l).
  Proof. induction l. simpl. now left. destruct a as [x ?]. simpl.
    destruct IHl as [E|?].
      destruct (nonneg_or_neg (R:=Q∞) ε).
        right. exists x. right. apply _.
      left. rewrite (Sets $ E),(Sets $ B_neg_empty ε x). exact (join_bottom_l _).
    right. destruct (inhabited (union_of_balls ε l)) as [y ?].
    exists y. now left.
  Qed.

  Lemma totally_bounded_empty_or_not U `{!TotallyBounded U} : U = ⊥ ∨ Inhabited U.
  Proof.
    destruct (totally_bounded_def U 1) as [[|[x ?]] P]; [left|right].
    simpl in P. apply (subset_antisym); apply _. now exists x.
  Qed.

  Lemma totally_bounded U `{!TotallyBounded U}
    ε `{ε ∊ Q∞₊} : ∃ l : list {x : A | x ∊ U}, U ⊆ union_of_balls ε l .
  Proof. pose proof (_ : U ⊆ X).
    destruct (ae_decompose_pos ε) as [E|?].
      destruct (totally_bounded_empty_or_not U) as [EU|?].
        exists ([]:list {x | x ∊ U}). simpl. rewrite EU. apply _.
      destruct (inhabited U) as [x ?]. exists ([exist _ x (_ : x ∊ U)]). simpl.
      rewrite (Sets $ join_bottom_l _). rewrite (_ $ E). now rewrite (B_infty _).
    exact (totally_bounded_def U ε).
  Qed.

  Lemma union_of_balls_map ε `{ε ∊ Qfull} {U} (l : list { x | x ∊ U }) V `{U ⊆ V} `{V ⊆ X}
   : ∃ (l' : list { x | x ∊ V }), union_of_balls ε l = union_of_balls ε l' .
  Proof. assert (U ⊆ X) by now transitivity V. induction l.
  + now exists ([] : list { x | x ∊ V }).
  + destruct a as [x ?], IHl as [l' E].
    exists ( (exist _ x (_ : x ∊ V)) :: l' ). simpl. now rewrite (Sets $ E).
  Qed.

  Lemma union_of_balls_union ε `{ε ∊ Qfull} {U} `{U ⊆ X}
      (l1 : list { x | x ∊ U }) (l2 : list { x | x ∊ U })
   : ∃ (l : list { x | x ∊ U }),
       union_of_balls ε l = union_of_balls ε l1 ⊔ union_of_balls ε l2 .
  Proof. induction l1.
  + exists l2. subsymmetry. exact (join_bottom_l _).
  + destruct IHl1 as [l E]. exists (a::l). destruct a as [x ?]. simpl. rewrite (Sets $ E).
    pose proof (_ : DistributiveLattice (every (@set A))).
    rewrite <-(associativity (S:=Sets) (⊔) _ _ _).
    rewrite (Sets $ commutativity (S:=Sets) (⊔) (union_of_balls ε l2) _).
    exact (associativity (S:=Sets) (⊔) _ _ _).
  Qed.

  Lemma totally_bounded_union U V `{!TotallyBounded U} `{!TotallyBounded V}
    : TotallyBounded (U ⊔ V) .
  Proof. split; try apply _. intros ε ?.
    destruct (totally_bounded U ε) as [l1' E1].
    destruct (totally_bounded V ε) as [l2' E2].
    destruct (union_of_balls_map ε l1' (U ⊔ V)) as [l1 E]. rewrite E in E1. clear dependent l1'.
    destruct (union_of_balls_map ε l2' (U ⊔ V)) as [l2 E]. rewrite E in E2. clear dependent l2'.
    destruct (union_of_balls_union ε l1 l2) as [l E].
    exists l. rewrite E. now apply (join_le_compat _ _ _ _).
  Qed.

  Instance point_totally_bounded x `{x ∊ X} : TotallyBounded (B 0 x).
  Proof. split; try apply _. intros ε ?.
    exists [ exist _ x (_ : x ∊ B 0 x) ]. simpl. rewrite (join_bottom_l _).
    apply (B_weaken_le _ _ _). now destruct (_ : ε ∊ Q⁺).
  Qed.

  Instance singleton_totally_bounded x `{x ∊ X} : TotallyBounded {{x}}.
  Proof. rewrite (singleton_is_ball x). apply _. Qed.

  Lemma totally_bounded_closure U `{!TotallyBounded U}
    : TotallyBounded (closure U).
  Proof. split; try apply _. intros ε ?.
    destruct (totally_bounded U (ε/2)) as [l E].
    destruct (union_of_balls_map ε l (closure U)) as [l' E'].
    exists l'. rewrite <-E'. clear dependent l'.
    apply (subsetoid_from_subset X _ _).
    intros y [? P]. destruct (P (ε/2) _) as [s[els ?]].
    rewrite E in els. revert els. clear E. induction l.
    * simpl. intros [].
    * destruct a as [x ?]. simpl. intros [?|[??]].
        left. tauto.
      right. split; trivial. red.
      pose proof (_ : U ⊆ X).
      rewrite <-(_ $ ae_in_halves ε).
      apply (ball_triangle _ _ _ s _); trivial; subsymmetry.
  Qed.

  Lemma totally_bounded_closure_back U `{U ⊆ X}
    : TotallyBounded (closure U) → TotallyBounded U.
  Proof. intro. split; try apply _. intros ε ?.
    destruct (totally_bounded (closure U) (ε/2)) as [l E].
    cut (∀ l  : list {x | x ∊ closure U},
         ∃ l' : list {x | x ∊ U},
         ∀ y, y ∊ union_of_balls (ε/2) l → y ∊ union_of_balls ε l').
      intro P. destruct (P l) as [l' P']. exists l'.
      apply (subsetoid_from_subset X _ _).
      intros y ely. rewrite (_ : U ⊆ closure U) in ely.
      rewrite E in ely. now apply P'.
    clear dependent l. intro l. induction l.
    * exists ([]: list {x | x ∊ U}). intros y [].
    * destruct a as [x [? Px]], IHl as [l' P]. simpl.
      destruct (Px (ε/2) _) as [s[??]].
      exists ( (exist _ s (_ : s ∊ U)) :: l' ). simpl.
      intros y [?|[??]]. left. now apply P.
      right. split; trivial. red.
      pose proof (_ : U ⊆ X).
      rewrite <-(_ $ ae_in_halves ε).
      apply (ball_triangle _ _ _ x _); trivial; subsymmetry.
  Qed.

  Lemma union_of_balls_located `{!LocatedPoints X} U `{U ⊆ X}
    x `{x ∊ X} p `{p ∊ Q⁺} q `{q ∊ Q₊} :
    p < q → ∀ (l : list { x | x ∊ U }),
        (∃ y (_ : y ∊ U), ball q x y)
      ∨ (∀ y, y ∊ union_of_balls ((q-p)/2) l → ¬ ball p x y).
  Proof. intros Ep.
    assert (q-p ∊ Q₊) by now rewrite (flip_pos_minus _ _).
    set (r := (q-p)/2). assert (r ∊ Q₊). subst r. apply _.
    intro l. induction l. right. intros ? [].
    destruct IHl as [?|P]. now left.
    destruct a as [x' ?]. simpl.
    destruct (located_points x x' (p+(q-p)/2) q) as [?|P'].
    * rewrite <-(flip_pos_minus _ _).
      mc_replace (q-(p+(q-p)/2)) with ((q-p)/2) on Q by decfield Q.
      apply _.
    * left. now exists_sub x'.
    * right. intros y [?|[??]]. now apply P. contradict P'.
      apply (ball_triangle _ _ _ y _); trivial. subsymmetry.
  Qed.

  Lemma totally_bounded_located `{!LocatedPoints X} U `{!TotallyBounded U} `{U ⊆ X} : Located U.
  Proof. split; try apply _. intros x ? p ? q ? Ep.
    assert (q-p ∊ Q₊) by now rewrite (flip_pos_minus _ _).
    destruct (totally_bounded U ((q-p)/2)) as [l E].
    destruct (union_of_balls_located U x p q Ep l) as [?|P]. now left. 
    right. intros. apply P. now apply E.
  Qed.

  Lemma located_totally_bounded_aux1 U `{!Located U} ε `{ε ∊ Q₊} 
     (l : list {x | x ∊ X}) : ∃ l' : list {x | x ∊ U},
         ∀ y, y ∊ U → y ∊ union_of_balls (ε/3) l → y ∊ union_of_balls ε l' .
  Proof.
    induction l. exists ([]:list {x | x ∊ U}). simpl. intros ?? [].
    destruct a as [x ?]. simpl. destruct IHl as [l' IHl].
    pose proof (_ : U ⊆ X).
    destruct (located U x (ε/3) (2*ε/3)) as [[y'[??]]|P].
    * apply (flip_pos_minus _ _).
      mc_replace (2*ε/3-ε/3) with (ε/3) on Q by setring Q. apply _.
    * exists (exist _ y' (_ : y' ∊ U) :: l'). simpl.
      intros y ? [?|[??]]; [left|right]. now apply IHl.
      split; [| apply _]. red. subsymmetry.
      mc_replace ε with (ε/3+2*ε/3) on Q by decfield Q.
      apply (ball_triangle _ _ _ x _); trivial. subsymmetry.
    * exists l'. intros y ? [?|[??]]. now apply IHl.
      cut False. intros []. now apply (P y _).
  Qed.

  Lemma located_totally_bounded_aux2 U `{!Located U} ε `{ε ∊ Q₊} 
      (l:list {x | x ∊ X}) : U ⊆ union_of_balls (ε/3) l
   → ∃ l' : list {x | x ∊ U}, U ⊆ union_of_balls ε l'.
  Proof. intro. destruct (located_totally_bounded_aux1 U ε l) as [l' P].
    exists l'. apply (subsetoid_from_subset _ _ _). intros y ?. apply (P y _ _).
  Qed.

  Lemma located_totally_bounded U `{!Located U} V `{!TotallyBounded V} `{U ⊆ V}
    : TotallyBounded U.
  Proof. split; try apply _. intros ε ?.
    destruct (totally_bounded V (ε/3)) as [l1 ?].
    destruct (union_of_balls_map (ε/3) l1 X) as [l2 E].
    apply (located_totally_bounded_aux2 _ _ l2).
    rewrite <-E. now transitivity V.
  Qed.

  Instance union_of_balls_bounded `{!FinitePoints X} U `{U ⊆ X} (l:list {x | x ∊ U})
    ε `{ε ∊ Q} : Bounded (union_of_balls ε l).
  Proof. induction l. simpl. apply _. destruct a as [x ?]. simpl.
    destruct (nonneg_or_neg ε).
      destruct (union_of_balls_empty_or_not _ l ε) as [E|?].
        cut (union_of_balls ε l ⊔ B ε x = B ε x). intro E'. rewrite E'. apply _.
        rewrite (Sets $ E). exact (join_bottom_l _).
      apply _.
    cut (union_of_balls ε l ⊔ B ε x = union_of_balls ε l). intro E. now rewrite E.
    rewrite (Sets $ B_neg_empty ε x). exact (join_bottom_r _).
  Qed.

  Lemma totally_bounded_bounded `{!FinitePoints X} U `{!TotallyBounded U} : Bounded U.
  Proof. destruct (totally_bounded U 1) as [l E]. rewrite E. apply _. Qed.

  Lemma union_of_balls_subspace U `{U ⊆ X} V `{V ⊆ X} W `{W ⊆ U} `{W ⊆ V} ε `{ε ∊ Q₊} y `{y ∊ W}
    (l : list {x | x ∊ W}) : y ∊ union_of_balls (X:=U) ε l → y ∊ union_of_balls (X:=V) ε l .
  Proof. induction l. now simpl. destruct a as [x ?]. simpl.
    intros [?|[??]]; [left; tauto |right]. split; trivial. apply _.
  Qed.

  Lemma totally_bounded_subspace U `{U ⊆ X} V `{V ⊆ X} W `{W ⊆ U} `{W ⊆ V}
    : TotallyBounded (X:=U) W → TotallyBounded (X:=V) W.
  Proof. assert (MetricSpace V) by exact sub_metric_space.
    intros. split; try apply _. intros ε ?.
    destruct (totally_bounded_def (X:=U) W ε) as [l P]. exists l.
    apply (subsetoid_from_subset V _ _). intros y ?.
    apply (union_of_balls_subspace U V W _ _ _). now apply P.
  Qed.

End totally_bounded.

Hint Extern 2 (Bounded (union_of_balls _ _)) => eapply @union_of_balls_bounded : typeclass_instances.

Hint Extern 2 (TotallyBounded ⊥) => eapply @empty_totally_bounded : typeclass_instances.
Hint Extern 2 (TotallyBounded (B 0 _)) => eapply @point_totally_bounded : typeclass_instances.
Hint Extern 2 (TotallyBounded {{_}}) => eapply @singleton_totally_bounded : typeclass_instances.
Hint Extern 2 (TotallyBounded (_ ⊔ _)) => eapply @totally_bounded_union : typeclass_instances.
Hint Extern 5 (TotallyBounded (X:=?X) (closure (X:=?X) _)) => eapply @totally_bounded_closure : typeclass_instances.

Section locally_totally_bounded.

  Context `{MetricSpace (X:=X)}.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.

  Lemma locally_totally_bounded `{!LocallyTotallyBounded X}
    U `{!Bounded U} `{!Inhabited U}
    ε `{ε ∊ Q∞₊} : ∃ (l : list { x | x ∊ X }), U ⊆ union_of_balls ε l .
  Proof. destruct (ae_decompose_pos ε) as [E|?].
      destruct (inhabited U) as [x ?]. pose proof (_ : U ⊆ X).
      exists [(exist _ x (_ : x ∊ X))]. simpl.
      rewrite (Sets $ join_bottom_l _). rewrite (_ $ E). now rewrite (B_infty _).
    exact (locally_totally_bounded_def U ε).
  Qed.

  Lemma totally_bounded_locally U : TotallyBounded U → LocallyTotallyBounded U.
  Proof. intro P. apply (totally_bounded_subspace X U U) in P.
    intros V ?? ε ?. destruct (totally_bounded_def (X:=U) U ε) as [l E].
    exists l. transitivity U; apply _.
  Qed.

  Lemma locally_totally_bounded_located `{!FinitePoints X} `{!LocatedPoints X}
    Y `{Y ⊆ X} `{!Inhabited Y} : LocallyTotallyBounded Y → Located Y.
  Proof. intro. split; try apply _. intros x ? p ? q ? E.
    destruct (inhabited Y) as [y₀ ?].
    destruct (finite_points x y₀) as [M [??]].
    destruct (le_or_lt M q).
      left. exists_sub y₀. apply ball_weaken_le with M; trivial; apply _.
    assert (MetricSpace Y) by exact sub_metric_space.
    assert (q-p ∊ Q₊) by now apply (flip_pos_minus _ _).
    destruct (locally_totally_bounded_def (B (X:=Y) (M+M) y₀) ((q-p)/2)) as [l El].
    destruct (union_of_balls_located Y x p q E l) as [?|P]. now left.
    right. intros y ? Bxy. cut (y ∊ B (X:=Y) (M + M) y₀).
      intro. apply (P y); trivial.
      apply (union_of_balls_subspace Y _ _ _ _). now apply El.
    split; trivial. red.
    apply (ball_triangle _ _ _ x _).
    now apply (symmetry (S:=X) (R:=ball M) _ _).
    apply ball_weaken_le with p; trivial; try apply _.
    apply (lt_le _ _). subtransitivity q.
  Qed.

  Lemma located_locally_totally_bounded `{!LocallyTotallyBounded X} `{!LocatedPoints X}
    Y `{Y ⊆ X} `{!Located Y} : LocallyTotallyBounded Y.
  Proof. assert (MetricSpace Y) by exact sub_metric_space.
    intros U ?? ε ?.
    assert (U ⊆ X). transitivity Y; apply _.
    assert (Bounded (X:=X) U). split; try apply _. exact (bounded (X:=Y) U).
    destruct (locally_totally_bounded U (ε/3)) as [l ?].
    destruct (located_totally_bounded_aux1 (X:=X) Y ε l) as [l' P].
    exists l'. apply (subsetoid_from_subset _ _ _). intros y ?.
    pose proof (_ : U ⊆ Y).
    apply (union_of_balls_subspace (X:=X) X _ _ _ _).
    apply (P _ _ _).
  Qed.

  (** Total boundedness of balls implies local total boundedness. *)
  Lemma locally_totally_bounded_by_ball :
    (∀ q `{q ∊ Q₊} x `{x ∊ X} ε `{ε ∊ Q₊}, ε < q →
     ∃ l : list { y | y ∊ X }, B q x ⊆ union_of_balls ε l)
    → LocallyTotallyBounded X.
  Proof. intros P U ?? ε ?.
    pose proof (_ : U ⊆ X). destruct (inhabited U) as [x ?].
    destruct (bounded U) as [d[? P']].
    destruct (le_or_lt d ε) as [?|E].
      exists ([exist _ x (_ : x ∊ X)]). simpl.
      rewrite (Sets $ join_bottom_l _).
      apply (subsetoid_from_subset _ _ _). intros y ?.
      split. 2: apply _. red.
      apply ball_weaken_le with d; trivial; try apply _. now apply P'.
    assert (d ∊ Q₊). split. apply _. red. subtransitivity ε. apply (_ : ε ∊ Q₊).
    destruct (P d _ x _ ε _ E) as [l ?]. exists l.
    transitivity (B d x); trivial.
    apply (subsetoid_from_subset _ _ _).
    intros y ?. pose proof (P' x _ y _). apply _.
  Qed.

  Lemma locally_totally_bounded_by_ball_alt :
    (∀ q `{q ∊ Q₊} x `{x ∊ X}, TotallyBounded (B q x))
    → LocallyTotallyBounded X.
  Proof. intros P. apply locally_totally_bounded_by_ball.
    intros q ? x ? ε ? _. pose proof (P q _ x _).
    destruct (totally_bounded (B q x) ε) as [l ?].
    destruct (union_of_balls_map ε l X) as [l' E].
    exists l'. now rewrite <-E.
  Qed.

  Context `{!LocallyTotallyBounded X}.

  Lemma locally_totally_bounded_alt
    U `{!Bounded U} `{!Inhabited U} `{!Located U} : TotallyBounded U.
  Proof.
    split; try apply _. intros ε ?.
    destruct (locally_totally_bounded U (ε/3)) as [l ?].
    now apply (located_totally_bounded_aux2 U ε l).
  Qed.

  Lemma locally_totally_bounded_iff `{!FinitePoints X} `{!LocatedPoints X}
    U : TotallyBounded U ↔ Bounded U ∧ (U = ⊥ ∨ Inhabited U) ∧ Located U .
  Proof. split.
  + intuition.
      exact (totally_bounded_bounded _).
      exact (totally_bounded_empty_or_not _).
      exact (totally_bounded_located _).
  + intros [? [[E|?] ?]]. rewrite E. apply _.
    exact (locally_totally_bounded_alt _).
  Qed.

  Lemma ball_totally_bounded `{!LocatedPoints X} `{!PrelengthSpace X}
    q `{q ∊ Q} x `{x ∊ X} : TotallyBounded (B q x).
  Proof. destruct (nonneg_or_neg q) as [?|?].
  + apply locally_totally_bounded_alt; apply _.
  + split; try apply _. intros ε ?.
    exists ([]:list {y|y ∊ B q x}). simpl.
    apply (subsetoid_from_subset _ _ _). intros ? [Bx ?].
    destruct (neg_not_nonneg q). exact (ball_nonneg _ _ _ Bx).
  Qed.
End locally_totally_bounded.


Section maps.
  Context `{X:set} `{Equiv X} `{Ball X}.
  Context `{Y:set} `{Equiv Y} `{Ball Y}.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact Y : typeclass_instances.

  Existing Instance uniform_cont_X.
  Existing Instance uniform_cont_Y.

  Lemma ufm_cont_union_of_balls_image `{!MetricSpace X} `{!MetricSpace Y}
    U `{U ⊆ X} (f:X ⇀ Y) `{!Morphism (X ⇒ Y) f}
    ε `{ε ∊ Q∞₊} δ `{δ ∊ Q∞₊} (Cf:∀ `{x ∊ X} `{y ∊ X}, ball δ x y → ball ε (f x) (f y))
    (l : list { x | x ∊ U }) : ∃ l' : list {x | x ∊ f⁺¹(U)},
           f⁺¹(union_of_balls δ l) ⊆ union_of_balls ε l'.
  Proof.
    induction l. exists ([]: list {x | x ∊ f⁺¹(U)}). simpl.
      rewrite (preserves_bottom (L:=(⊆ X)) (K:=(⊆ Y)) (image f)). apply _.
    destruct a as [x ?]. destruct IHl as [l' ?].
    exists (exist _ (f x) (_ : f x ∊ f⁺¹(U)) :: l'). simpl.
    rewrite (preserves_join (L:=(⊆ X)) (K:=(⊆ Y)) (image f) _ _).
    apply (join_lub (L:=(⊆ Y)) _ _ _); unfold le.
      transitivity (union_of_balls ε l'); trivial.
      apply (join_ub_l (L:=(⊆ Y)) _ _).
    transitivity (B ε (f x)); [| apply (join_ub_r (L:=(⊆ Y)) _ _) ].
    apply (subsetoid_from_subset _ _ _). intros ? [?[x' [[??] E]]].
    rewrite <- (_ $ E). split; [|apply _]. red. now apply (Cf _ _ _ _).
  Qed.

  Lemma ufm_cont_totally_bounded_image f `{!UniformlyContinuous X Y f}
    U `{!TotallyBounded (X:=X) U} : TotallyBounded f⁺¹(U).
  Proof. split; try apply _. intros ε ?.
    pose proof (_ : U ⊆ X).
    destruct (uniform_continuity f ε) as [δ[el Cf]].
    destruct (totally_bounded U δ) as [l ?].
    destruct (ufm_cont_union_of_balls_image U f ε δ Cf l) as [l' ?]. exists l'.
    transitivity (f⁺¹(union_of_balls δ l)); trivial.
    apply (image_order_preserving f _ _).
  Qed.

  Lemma ufm_cont_locally_totally_bounded_image `{!LocallyTotallyBounded X} `{!FinitePoints Y}
    f `{!UniformlyContinuous X Y f}
    U `{!Bounded (X:=X) U} `{!Inhabited U} : Bounded f⁺¹(U).
  Proof.
    destruct (uniform_continuity f 1) as [δ[el Cf]].
    destruct (locally_totally_bounded U δ) as [l ?].
    destruct (ufm_cont_union_of_balls_image X f 1 δ Cf l) as [l' ?].
    cut (f⁺¹(U) ⊆ union_of_balls 1 l'). intro E'. rewrite E'. apply _.
    transitivity f⁺¹(union_of_balls δ l); trivial.
    apply (image_order_preserving f _ _).
  Qed.

End maps.

Section completion.
  Context `{Completion (X:=X) (X':=X')} `{!LocallyTotallyBounded X}.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact X' : typeclass_instances.

  Notation f := (to_completion X X').

  Lemma locally_totally_bounded_completion : LocallyTotallyBounded X'.
  Proof. intros U ?? ε ?.
    cut (∀ l : list {x | x ∊ X}, ∃ l' : list {x' | x' ∊ X'},
           ∀ y', y' ∊ X' → ∀ y, y ∊ union_of_balls (ε/2) l → ball (ε/2) y' (f y)
               → y' ∊ union_of_balls ε l' ).
      intro P. 
      destruct (bounded U) as [d [eld BU]].
      destruct (inhabited U) as [x' ?].
      pose proof (_ : U ⊆ X').
      destruct (dense_image f X x' (ε/2)) as [x [??]].
      destruct (locally_totally_bounded (B (d + ε) x) (ε/2)) as [l E].
      destruct (P l) as [l' P']. exists l'.
      apply (subsetoid_from_subset _ _ _). intros y' ?.
      destruct (dense_image f X y' (ε/2)) as [y [??]].
      apply (P' y' _ y); trivial. apply E. split. 2: apply _. red.
      apply (isometric f _ _ _).
      apply ball_weaken_le with (ε/2 + d + ε/2); trivial; try apply _.
        2: apply (eq_le _ _); decfield Q.
      apply (ball_triangle _ _ _ y' _); trivial.
      apply (ball_triangle _ _ _ x' _). subsymmetry.
      now apply BU.
    induction l.
    + exists ([] : list {x' | x' ∊ X'}). simpl. intros ??? [].
    + destruct a as [x ?], IHl as [l' P].
      exists (exist _ (f x) (_ : f x ∊ X') :: l'). simpl.
      intros y' ? y [?|[??]] ?; [left|right]. now apply P with y.
      split. 2: apply _. red.
      apply ball_weaken_le with (ε/2+ε/2); trivial; try apply _.
        2: apply (eq_le _ _); decfield Q.
      apply (ball_triangle _ _ _ (f y) _). 2: subsymmetry.
      now apply (isometric f _ _ _).
  Qed.
End completion.

