Require Import
  List
  abstract_algebra interfaces.orders interfaces.metric_spaces
  theory.setoids theory.lattices theory.powerset orders.lattices orders.minmax
  orders.affinely_extended_field
  metric.metric_spaces metric.maps
  stdlib_field.

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

Lemma located `{X:Subset} `{Equiv X} `{Ball X} S `{!Located (X:=X) S}
  x `{x ∊ X} p `{p ∊ Q∞} q `{q ∊ Q∞}
  : p < q → (∃ `{y ∊ S}, ball q x y) ∨ (∀ `{y ∊ S}, ¬ ball p x y).
Proof.
  destruct (_ : Located (X:=X) S) as [?? _].
  destruct (decide_sub (le) 0 p) as [Ep|Ep].
  + intro E. assert (p ∊ Q∞⁺) by now split.
    assert (q ∊ Q∞₊). split. apply _. now apply (le_lt_trans _ p _).
    destruct (ae_decompose_nonneg p) as [Ep'|?].
      rewrite (_ $ Ep') in E. contradict E.
      destruct (ae_decompose_pos q) as [Eq|?].
        intro E. rewrite (_ $ Eq) in E. now destruct (subirreflexivity (S:=Q∞) (<) infty).
        apply (lt_flip _ _). exact (ae_inf_sub _).
    destruct (ae_decompose_pos q) as [Eq|?].
    * destruct (located_def (X:=X) x p (p+1)) as [[y [? P]]|?].
      - rewrite <-(flip_pos_minus _ _). mc_replace (p+1-p) with 1 on Q by subring Q. apply _.
      - left. exists_sub y. rewrite (_ $ Eq). exact (msp_ball_inf _ _).
      - now right.
    * exact (located_def (X:=X) x p q E).
  + intro. right. intros. intro Bp. now destruct (msp_nonneg _ _ _ Bp).
Qed.

Lemma located_proper: Find_Proper_Signature (@Located) 0
  (∀ A (Ae:Equiv A) (b:Ball A) (X:Subset), Proper ((=)==>impl) (Located (X:=X))).
Proof. red; intros. intros U V E ?. pose proof located_msp (X:=X).
  assert (V ⊆ X) by (rewrite <-E; apply _).
  split; try apply _.
  intros x ? p ? q ? Ep.
  destruct (located_def (X:=X) x p q Ep) as [[y[el P]]|P]; [left|right].
    rewrite E in el. now exists_sub y.
    intros y el. rewrite <-E in el. now apply P.
Qed.
Hint Extern 0 (Find_Proper_Signature (@Located) 0 _) => eexact located_proper : typeclass_instances.

Lemma totally_bounded_proper: Find_Proper_Signature (@TotallyBounded) 0
  (∀ A (Ae:Equiv A) (b:Ball A) (X:Subset), Proper ((=)==>impl) (TotallyBounded (X:=X))).
Proof. red; intros. intros U V E ?. pose proof totally_bounded_msp (X:=X).
  assert (V ⊆ X) by (rewrite <-E; apply _).
  split; try apply _.
  set (f := λ (y:{x | x ∊ U}), match y with exist x el => exist _ x (proj1 (E x) el) end).
  intros ε ?.
  destruct (totally_bounded (X:=X) U ε) as [l P].
  exists (map f l).
  assert (∀ (l' : list { x | x ∊ U }),
    union_of_balls (X:=X) ε l' = union_of_balls (X:=X) ε (map f l')) as E'.
    intros l'. induction l'. now simpl. destruct a as [x ?]. simpl.
    now rewrite (every Subset $ IHl').
  now rewrite <- (E' l), <-E.
Qed.
Hint Extern 0 (Find_Proper_Signature (@TotallyBounded) 0 _) => eexact totally_bounded_proper : typeclass_instances.

Section contents.
  Context `{MetricSpace (X:=X)}.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.

  Lemma totally_bounded_empty_or_not U `{!TotallyBounded U} : U = ⊥ ∨ Inhabited U.
  Proof.
    destruct (totally_bounded U 1) as [[|[x ?]] P]; [left|right].
    simpl in P. apply (subsetof_antisym); apply _. now exists x.
  Qed.

  Lemma totally_bounded_located `{!LocatedPoints X} U `{!TotallyBounded U} `{U ⊆ X} : Located U.
  Proof. split; try apply _. intros x ? p ? q ? Ep.
    assert (q-p ∊ Q₊) by now rewrite (flip_pos_minus _ _).
    set (r := (q-p)/2). assert (r ∊ Q₊). subst r. apply _.
    cut (∀ (l : list { x | x ∊ U }),
        (∃ y, y ∊ U ∧ ball q x y) ∨ (∀ y, y ∊ union_of_balls r l → ¬ ball p x y) ).
    + intro P.
      destruct (totally_bounded U r) as [l E].
      destruct (P l) as [[y[??]]|P']; [left|right].
        now exists_sub y.
        intros. apply P'. now rewrite <-E.
    + intro l. induction l. right. intros ? [].
      destruct IHl as [?|P]. now left.
      destruct a as [x' ?]. simpl.
      destruct (located_points x x' (p+(q-p)/2) q) as [?|P'].
      * rewrite <-(flip_pos_minus _ _).
        mc_replace (q-(p+(q-p)/2)) with ((q-p)/2) on Q by subfield Q.
        apply _.
      * left. exists x'. now split.
      * right. intros y [?|[??]]. now apply P. contradict P'.
        apply (ball_triangle _ _ _ y _); trivial. subsymmetry.
  Qed.

  Lemma located_totally_bounded U `{!Located U} V `{!TotallyBounded V} `{U ⊆ V}
    : TotallyBounded U.
  Proof. split; try apply _. intros ε ?.
    cut (∀ (l:list {x | x ∊ V}), ∃ l' : list {x | x ∊ U},
      ∀ y, y ∊ U → y ∊ union_of_balls (ε/3) l → y ∊ union_of_balls ε l').
    + intro P. destruct (totally_bounded V (ε/3)) as [l ?].
      destruct (P l) as [l' P']. exists l'.
      apply (subsetoid_from_subsetof X _ _). intros y ?. apply (P' y _).
      apply (_ :  V ⊆ union_of_balls (ε / 3) l). now apply (_ : U ⊆ V).
    + intros l. induction l. exists ([]:list {x | x ∊ U}). simpl. intros ?? [].
      destruct a as [x ?]. simpl. destruct IHl as [l' IHl].
      pose proof totally_bounded_subsetoid.
      destruct (located U x (ε/3) (2*ε/3)) as [[y'[??]]|P].
      * apply (flip_pos_minus _ _).
        mc_replace (2*ε/3-ε/3) with (ε/3) on Q by subring Q. apply _.
      * exists (exist _ y' (_ : y' ∊ U) :: l'). simpl.
        intros y ? [?|[??]]; [left|right]. now apply IHl.
        split; [| apply _]. red. subsymmetry.
        mc_replace ε with (ε/3+2*ε/3) on Q by subfield Q.
        apply (ball_triangle _ _ _ x _); trivial. subsymmetry.
      * exists l'. intros y ? [?|[??]]. now apply IHl.
        cut False. intros []. now apply (P y _).
  Qed.

  Lemma totally_bounded_bounded `{!FinitePoints X} U `{!TotallyBounded U} : Bounded U.
  Proof.
    cut (∀ (l : list { x | x ∊ U }), Bounded (union_of_balls 1 l)).
    + intro P. destruct (totally_bounded U 1) as [l E].
      rewrite E. now apply P.
    + intro l. induction l. simpl. apply _. destruct a as [x ?].
      pose proof (_ : U ⊆ X). pose proof _ : x ∊ X.
      destruct l as [|[y ?]]. simpl.
      rewrite (join_bottom_l (L:=every Subset) _). apply (ball_bounded _ _).
      simpl. simpl in IHl. split; try apply _. pose proof _ : y ∊ X.
      destruct (bounded (union_of_balls 1 l ⊔ B 1 y)) as [d[? P]].
      destruct (finite_points y x) as [q[? ?]].
      pose proof _ : union_of_balls 1 l ⊔ B 1 y ⊆ X.
      assert (∀ y' x', y' ∊ union_of_balls 1 l ⊔ B 1 y -> x' ∊ B 1 x -> ball (d+q+1) y' x') as P'.
        intros ?? el [??].
        apply (ball_triangle _ _ _ x _); trivial.
        apply (ball_triangle _ _ _ y _); trivial. exact (P _ _ _ _).
      assert (d+q+1 ≤ d+q+2) as Er.
        rewrite <-(flip_nonneg_minus _ _).
        mc_replace (d+q+2-(d+q+1)) with 1 on Q by subring Q. apply _.
      exists_sub (d+q+2). intros x' [?|?] y' [?|?].
      * rewrite <-(_ $ associativity (+) _ _ _).
        rewrite <-(_ $ nonneg_plus_le_compat_r d (q+2)). now apply P.
      * destruct (_: y' ∊ B 1 x) as [_ ?]. rewrite <-(_ $ Er). now apply P'.
      * destruct (_: x' ∊ B 1 x) as [_ ?]. rewrite <-(_ $ Er). subsymmetry. now apply P'.
      * destruct (_: x' ∊ B 1 x). destruct (_: y' ∊ B 1 x).
        rewrite <-(_ $ nonneg_plus_le_compat_l _ _).
        apply (ball_triangle _ _ _ x _); trivial. subsymmetry.
  Qed.

  Lemma locally_totally_bounded `{!LocallyTotallyBounded X}
    q `{q ∊ Q} x `{x ∊ X} : TotallyBounded (B q x).
  Proof. destruct (trichotomy (<) q 0) as [?|[E|?]]; [split; try apply _; intros ε ? .. |].
  + exists ([]:list {y|y ∊ B q x}). simpl.
    apply (subsetoid_from_subsetof _ _ _). intros ? [Bx ?].
    assert (q ∊ Q₋) by now split. destruct (neg_not_nonneg q).
    exact (ball_nonneg _ _ _ Bx).
  + assert (q ∊ Q⁺). rewrite (_ $ E). apply _.
    exists [exist _ x (_ : x ∊ B q x)]. simpl.
    rewrite (join_bottom_l (L:=every Subset) _).
    apply (B_weaken_le _ _ _).
    rewrite (_ $ E). now destruct (_ : ε ∊ Q⁺).
  + assert (q ∊ Q₊) by now split.
    exact (locally_totally_bounded_def q x).
  Qed.

  Lemma locally_totally_bounded_alt `{!LocallyTotallyBounded X}
    U `{!Bounded U} `{!Inhabited U} : ∃ (V:Subset), U ⊆ V ⊆ X ∧ TotallyBounded V.
  Proof. pose proof (_ : U ⊆ X). destruct (inhabited U) as [x ?].
    destruct (bounded U) as [d[? P]].
    exists (B d x). split; [| apply locally_totally_bounded; apply _ ].
    split; [| apply _]. apply (subsetoid_from_subsetof _ _ _).
    intros y ?. pose proof (P x _ y _). apply _.
  Qed.

End contents.

Section maps.
  Context `{X:Subset} `{Equiv X} `{Ball X}.
  Context `{Y:Subset} `{Equiv Y} `{Ball Y}.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact Y : typeclass_instances.

  Existing Instance uniform_cont_X.
  Existing Instance uniform_cont_Y.

  Lemma ufm_cont_totally_bounded_image f `{!UniformlyContinuous X Y f}
    U `{!TotallyBounded (X:=X) U} : TotallyBounded f⁺¹(U).
  Proof. split; try apply _. intros ε ?.
    pose proof (_ : U ⊆ X).
    destruct (uniform_continuity f ε) as [δ[el Cf]].
    destruct (ae_decompose_pos δ) as [Eδ|?].
      destruct (totally_bounded_empty_or_not U) as [EU|[x ?]].
        exists ([]: list {x | x ∊ f⁺¹(U)}). simpl.
          apply (subsetoid_from_subsetof _ _ _). intros ? [?[?[el' ?]]].
          rewrite EU in el'. destruct el'.
        exists [exist _ (f x) (_ : f x ∊ f⁺¹(U))]. simpl.
          rewrite (join_bottom_l (L:=every Subset) _).
          apply (subsetoid_from_subsetof Y _ _).
          intros y [? [x' [? E]]]. rewrite <-(_ $ E). split; [|apply _]. red.
          apply (Cf _ _ _ _). rewrite (_ $ Eδ). exact (msp_ball_inf _ _).
    cut (∀ (l : list { x | x ∊ U }), ∃ l' : list {x | x ∊ f⁺¹(U)},
           f⁺¹(union_of_balls δ l) ⊆ union_of_balls ε l').
    + intro P.
      destruct (totally_bounded U δ) as [l ?].
      destruct (P l) as [l' ?]. exists l'.
      transitivity (f⁺¹(union_of_balls δ l)); trivial.
      apply (image_order_preserving f _ _).
    + intro l. induction l.
      * simpl. exists ([]: list {x | x ∊ f⁺¹(U)}). simpl.
        rewrite (preserves_bottom (L:=(⊆ X)) (K:=(⊆ Y)) (image f)). apply _.
      * destruct a as [x ?]. destruct IHl as [l' ?].
        exists (exist _ (f x) (_ : f x ∊ f⁺¹(U)) :: l'). simpl.
        rewrite (preserves_join (L:=(⊆ X)) (K:=(⊆ Y)) (image f) _ _).
        apply (join_lub (L:=(⊆ Y)) _ _ _); unfold le.
          transitivity (union_of_balls ε l'); trivial.
          apply (join_ub_l (L:=(⊆ Y)) _ _).
        transitivity (B ε (f x)); [| apply (join_ub_r (L:=(⊆ Y)) _ _) ].
        apply (subsetoid_from_subsetof _ _ _). intros ? [?[x' [[??] E]]].
          rewrite <- (_ $ E). split; [|apply _]. red. now apply (Cf _ _ _ _).
  Qed.

  Lemma ufm_cont_bounded_image `{!LocallyTotallyBounded X} `{!FinitePoints Y}
    f `{!UniformlyContinuous X Y f} : StronglyUniformlyContinuous X Y f.
  Proof. split. apply _. intros U ??.
    destruct (locally_totally_bounded_alt U) as [V [[??]?]].
    rewrite (image_order_preserving f U V).
    apply totally_bounded_bounded.
    now apply ufm_cont_totally_bounded_image.
  Qed.

End maps.
Hint Extern 30 (StronglyUniformlyContinuous _ _ _) => eapply @ufm_cont_bounded_image : typeclass_instances.
