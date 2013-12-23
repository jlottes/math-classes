Require Import
  List
  abstract_algebra interfaces.metric_spaces interfaces.orders
  theory.setoids theory.products metric.metric_spaces
  metric.totally_bounded metric.maps_continuous
  orders.affinely_extended_field the_ae_rationals
  orders.lattices orders.minmax
  stdlib_field_dec.

Local Notation AQ := TheAERationals.A.
Local Notation Q := the_ae_rationals.
Local Notation "Q∞" := (aff_ext Q).
Local Notation Qfull := (aff_ext_full Q).

Definition prod_sup_ball `{X:set} `{Y:set} `{Ball X} `{Ball Y} : Ball (X * Y)
  := λ ε x y, ball ε (fst x) (fst y) ∧ ball ε (snd x) (snd y).
Hint Extern 4 (Ball (elt_type (prod_set ?X ?Y))) => eexact (prod_sup_ball (X:=X) (Y:=Y)) : typeclass_instances.
Hint Extern 4 (Ball (elt_type ?X * elt_type ?Y)) => eexact (prod_sup_ball (X:=X) (Y:=Y)) : typeclass_instances.

Hint Extern 2 (@AmbientSpace (?A * ?B)) =>
  exact ((_:AmbientSpace)*(_:AmbientSpace))%set : typeclass_instances.

Section contents.
  Context `{MetricSpace (X:=X)} `{MetricSpace (X:=Y)}.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact Y : typeclass_instances.

  Instance prod_msp : MetricSpace (X * Y).
  Proof. split; unfold ball, prod_sup_ball. apply _.
  + intros a b E1 x1 x2 Ex y1 y2 Ey [??]. unfold_sigs.
    split; now rewrite <- (_ $ E1), <-(X*Y $ Ex), <-(X*Y $ Ey).
  + intros ?????? [E?]. exact (msp_nonneg _ _ _ E).
  + split; exact (msp_ball_inf _ _).
  + now split.
  + split; subsymmetry; firstorder.
  + intros. apply prod_equal_components; now apply (ball_separated _ _).
  + intros. split.
      now apply (ball_triangle _ _ _ (fst y) _).
      now apply (ball_triangle _ _ _ (snd y) _).
  + intros ?????? P. split; apply (ball_closed _ _ _); intros; now apply P.
  Qed.

  Instance prod_finite_points `{!FinitePoints X} `{!FinitePoints Y} : FinitePoints (X*Y).
  Proof. intros [a b][??][x y][??].
    destruct (finite_points a x) as [q[??]].
    destruct (finite_points b y) as [r[??]].
    exists_sub (q ⊔ r). split; simpl.
    now rewrite <-(Qfull $ join_ub_l q r).
    now rewrite <-(Qfull $ join_ub_r q r).
  Qed.

  Instance prod_located_points `{!LocatedPoints X} `{!LocatedPoints Y} : LocatedPoints (X*Y).
  Proof. intros [a b][??][x y][??] p ? q ? E.
    destruct (located_points a x _ _ E); [| right; firstorder].
    destruct (located_points b y _ _ E); [| right; firstorder].
    left; now split.
  Qed.

  Instance prod_prelength `{!PrelengthSpace X} `{!PrelengthSpace Y} : PrelengthSpace (X*Y).
  Proof. intros [a b][??][x y][??] ε ? δ₁ ? δ₂ ? E [B1 B2]. simpl in B1,B2.
    destruct (prelength_msp a x _ _ _ E B1) as [z1[?[??]]].
    destruct (prelength_msp b y _ _ _ E B2) as [z2[?[??]]].
    exists_sub (z1,z2). now (split; split).
  Qed.

  Instance prod_metric_inequality `{UnEq X} `{!MetricInequality X} `{UnEq Y} `{!MetricInequality Y}
    `{!LocatedPoints X} `{!LocatedPoints Y} : MetricInequality (X*Y).
  Proof. intros [a b] [? ?] [c d] [? ?]. split.
  + intros [E|E]; rewrite (metric_inequality _ _) in E; destruct E as [q[? P]]; exists_sub q;
    intros [??]; now destruct P.
  + intros [q[? P]].
    assert (q/2<q) as E. apply (flip_pos_minus _ _).
      mc_replace (q-q/2) with (q/2) on Q by decfield Q. apply _.
    destruct (located_points a c (q/2) q E).
    destruct (located_points b d (q/2) q E).
    destruct P. now split.
    right. rewrite (metric_inequality _ _). now exists_sub (q/2).
    left.  rewrite (metric_inequality _ _). now exists_sub (q/2).
  Qed.

  Instance fst_ufm_cont : UniformlyContinuous (X*Y) X fst.
  Proof. split; try apply _. intros q ?. exists_sub q. now intros ???? [??]. Qed.

  Instance snd_ufm_cont : UniformlyContinuous (X*Y) Y snd.
  Proof. split; try apply _. intros q ?. exists_sub q. now intros ???? [??]. Qed.

  Notation π₁ := (fst:X*Y⇀X).
  Notation π₂ := (snd:X*Y⇀Y).

  Section projections.
    Context U `{U ⊆ X*Y}.

    Lemma fst_bounded `{!Bounded U} : Bounded π₁⁺¹(U).
    Proof. split; try apply _. destruct (bounded U) as [d[eld P]].
      exists_sub d. intros x [?[[xa xb][? Ex]]] y [?[[ya yb][? Ey]]]. simpl in Ex,Ey.
      destruct (_ : (xa, xb) ∊ X*Y ).
      destruct (_ : (ya, yb) ∊ X*Y ).
      rewrite <-(_ $ Ex), <-(_ $ Ey).
      now destruct (P (xa,xb) _ (ya,yb) _).
    Qed.

    Lemma snd_bounded `{!Bounded U} : Bounded π₂⁺¹(U).
    Proof. split; try apply _. destruct (bounded U) as [d[eld P]].
      exists_sub d. intros x [?[[xa xb][? Ex]]] y [?[[ya yb][? Ey]]]. simpl in Ex,Ey.
      destruct (_ : (xa, xb) ∊ X*Y ).
      destruct (_ : (ya, yb) ∊ X*Y ).
      rewrite <-(_ $ Ex), <-(_ $ Ey).
      now destruct (P (xa,xb) _ (ya,yb) _).
    Qed.

  End projections.
  Existing Instance fst_bounded.
  Existing Instance snd_bounded.

  Instance prod_bounded U V : Bounded (X:=X) U → Bounded (X:=Y) V → Bounded (U*V).
  Proof. intros ??. split; try apply _.
    pose proof (_ : U ⊆ X).
    pose proof (_ : V ⊆ Y).
    destruct (bounded U) as [d1 [eld1 B1]].
    destruct (bounded V) as [d2 [eld2 B2]].
    exists_sub (join d1 d2).
    intros [x1 x2][??][y1 y2][??].
    split; simpl.
    rewrite <- (Qfull $ join_ub_l _ _). now apply B1.
    rewrite <- (Qfull $ join_ub_r _ _). now apply B2.
  Qed.

  Lemma prod_open U V : Open (X:=X) U → Open (X:=Y) V → Open (U*V).
  Proof. intros ??. split; try apply _.
    pose proof _ : U ⊆ X. pose proof _ : V ⊆ Y. pose proof _ : U*V ⊆ X*Y.
    apply subset_antisym. apply _.
    intros [x y] [??].
    destruct (open U x) as [p[? OU]].
    destruct (open V y) as [q[? OV]].
    ae_rat_set_min r p q Ep Er. split. apply _. exists_sub r.
    intros [a b] [[??][Ba Bb]]. simpl in Ba,Bb. split.
      rewrite <-OU. split; [| apply _]. red. now rewrite <-(Q∞ $ Ep).
      rewrite <-OV. split; [| apply _]. red. now rewrite <-(Q∞ $ Er).
  Qed.

  Instance prod_complement_l U V `{U ⊆ X} `{V ⊆ Y} : (∼U)*Y ⊆ ∼(U*V)%set.
  Proof. apply (subsetoid_from_subset (X*Y) _ _).
    intros [x y][[? P]?]. split. apply _. intros [u v][??].
    destruct (P u _) as [q[? B]]. exists_sub q. intros [??]. now destruct B.
  Qed. 

  Instance prod_complement_r U V `{U ⊆ X} `{V ⊆ Y} : X*(∼V) ⊆ ∼(U*V)%set.
  Proof. apply (subsetoid_from_subset (X*Y) _ _).
    intros [x y][?[? P]]. split. apply _. intros [u v][??].
    destruct (P v _) as [q[? B]]. exists_sub q. intros [??]. now destruct B.
  Qed. 

  Instance prod_metric_complement_stable U V `{U ⊆ X} `{V ⊆ Y}
    `{!MetricComplementStable U} `{!MetricComplementStable V}
    : MetricComplementStable (U*V).
  Proof. intros [x y]. split.
  + intros [[??][q[? P]]]. split.
    * rewrite <-(metric_complement_stable U). split. apply _. exists_sub q.
      intros s ?. assert ((s,y) ∊ ∼(U * V)%set).
        apply (_ : ∼U * Y ⊆ ∼(U * V)%set). apply _.
      intro B. destruct (P (s,y) _). now split.
    * rewrite <-(metric_complement_stable V). split. apply _. exists_sub q.
      intros s ?. assert ((x,s) ∊ ∼(U * V)%set).
        apply (_ : X * ∼V ⊆ ∼(U * V)%set). apply _.
      intro B. destruct (P (x,s) _). now split.
  + intros [??].
    assert (x ∊ -∼U) by now rewrite (metric_complement_stable U).
    assert (y ∊ -∼V) by now rewrite (metric_complement_stable V).
    destruct (_ : x ∊ -∼U) as [?[qx[? Px]]].
    destruct (_ : y ∊ -∼V) as [?[qy[? Py]]].
    ae_rat_set_min q qx qy Ex Ey.
    split. apply _. exists_sub (q/2).
    intros [a b] [[??] P] [B1 B2]. simpl in B1,B2.
    assert (a ∊ U). rewrite <-(metric_complement_stable U).
      split; try apply _. exists_sub (q/2). intros s ??.
      destruct (Px s _). assert (s ∊ X) by now apply (_ : ∼U ⊆ X).
      rewrite <-(Qfull $ Ex). rewrite <-(Qfull $ ae_in_halves q).
      now apply (ball_triangle _ _ _ a _).
    assert (b ∊ V). rewrite <-(metric_complement_stable V).
      split; try apply _. exists_sub (q/2). intros s ??.
      destruct (Py s _). assert (s ∊ Y) by now apply (_ : ∼V ⊆ Y).
      rewrite <-(Qfull $ Ey). rewrite <-(Qfull $ ae_in_halves q).
      now apply (ball_triangle _ _ _ b _).
    now destruct (P (a,b) _) as [?[?[]]].
  Qed.

  Instance prod_set_apart_complement U₁ U₂ V₁ V₂ `{U₁ ⊆ X} `{U₂ ⊆ Y} `{V₁ ⊆ X} `{V₂ ⊆ Y}
    `{!MetricComplementStable V₁} `{!MetricComplementStable V₂}
    `{!SetApart U₁ (∼V₁)} `{!SetApart U₂ (∼V₂)}
  : SetApart (U₁ * U₂) (∼(V₁ * V₂)%set).
  Proof.
    destruct (set_apart U₁ (∼V₁)) as [q1[? P1]].
    destruct (set_apart U₂ (∼V₂)) as [q2[? P2]].
    ae_rat_set_min q q1 q2 E1 E2.
    exists_sub (q/2). intros [a b] [??] [va vb] [[??] P] [B1 B2]. simpl in B1,B2. simpl in *.
    assert (va ∊ V₁). rewrite <-(metric_complement_stable V₁).
      split; try apply _. exists_sub (q/2). intros s ??.
      destruct (P1 a _ s _). assert (s ∊ X) by now apply (_ : ∼V₁ ⊆ X).
      assert (a ∊ X) by now apply (_ : U₁ ⊆ X).
      apply (ball_weaken_le) with (q/2+q/2); try apply _.
        now apply (ball_triangle _ _ _ va _).
        apply (transitivity (S:=Qfull) _ q _); trivial.
        apply (eq_le _ _). exact (ae_in_halves q).
    assert (vb ∊ V₂). rewrite <-(metric_complement_stable V₂).
      split; try apply _. exists_sub (q/2). intros s ??.
      destruct (P2 b _ s _). assert (s ∊ Y) by now apply (_ : ∼V₂ ⊆ Y).
      assert (b ∊ Y) by now apply (_ : U₂ ⊆ Y).
      apply (ball_weaken_le) with (q/2+q/2); try apply _.
        now apply (ball_triangle _ _ _ vb _).
        apply (transitivity (S:=Qfull) _ q _); trivial.
        apply (eq_le _ _). exact (ae_in_halves q).
    destruct (P (va,vb) _) as [?[?[]]].
    apply (reflexivity (S:=X*Y) _).
  Qed.

  Instance prod_set_contained U₁ U₂ V₁ V₂ `{U₁ ⊆ X} `{U₂ ⊆ Y} `{V₁ ⊆ X} `{V₂ ⊆ Y}
    `{!SetContained U₁ V₁} `{!SetContained U₂ V₂}
  : SetContained (U₁ * U₂) (V₁ * V₂).
  Proof.
    destruct (set_contained U₁ V₁) as [q1[? P1]].
    destruct (set_contained U₂ V₂) as [q2[? P2]].
    ae_rat_set_min q q1 q2 E1 E2.
    exists_sub q. intros [a b][??] [ua ub][??] [??]. simpl in *.
    split. apply (P1 a _ ua _). now rewrite <-(Qfull $ E1).
           apply (P2 b _ ub _). now rewrite <-(Qfull $ E2).
  Qed.

  Lemma prod_well_contained U₁ U₂ V₁ V₂
    `{!WellContained (X:=X) U₁ V₁} `{!WellContained (X:=Y) U₂ V₂}
  : U₁ * U₂ ⊂⊂ V₁ * V₂ .
  Proof. apply (well_contained_alt _ _); apply _. Qed.

  Section projections_wc.
    Context D₁ D₂ `{D₁ ⊆ X} `{D₂ ⊆ Y} U `{U ⊂⊂ D₁*D₂}.

    Lemma fst_wc : π₁⁺¹(U) ⊂⊂ D₁.
    Proof. apply (well_contained_alt _ _); try apply _.
      destruct (set_contained U (D₁*D₂)) as [q[elq P]].
      exists_sub q. intros x ? u [?[[ua ub][? Eu]]] ?. simpl in Eu.
      assert ((ua, ub) ∊ D₁*D₂) as E by now apply (_ : U ⊂⊂ D₁*D₂). destruct E.
      apply (P (x, ub) _ (ua,ub) _). split; simpl. 2:easy. now rewrite (_ $ Eu).
    Qed.

    Lemma snd_wc : π₂⁺¹(U) ⊂⊂ D₂.
    Proof. apply (well_contained_alt _ _); try apply _.
      destruct (set_contained U (D₁*D₂)) as [q[elq P]].
      exists_sub q. intros x ? u [?[[ua ub][? Eu]]] ?. simpl in Eu.
      assert ((ua, ub) ∊ D₁*D₂) as E by now apply (_ : U ⊂⊂ D₁*D₂). destruct E.
      apply (P (ua, x) _ (ua,ub) _). split; simpl. easy. now rewrite (_ $ Eu).
    Qed.

  End projections_wc.

  Lemma prod_join_distr_l U `{U ⊆ X} V₁ `{V₁ ⊆ Y} V₂ `{V₂ ⊆ Y} :
    ( U * (V₁ ⊔ V₂) = U * V₁ ⊔ U * V₂  )%set.
  Proof. apply subset_antisym.
    intros [??][?[?|?]]; [left|right]; now split.
    intros [??][[??]|[??]]; split; trivial; apply _.
  Qed.

  Lemma prod_join_distr_r U₁ `{U₁ ⊆ X} U₂ `{U₂ ⊆ X} V `{V ⊆ Y} :
    ( (U₁ ⊔ U₂) * V = U₁ * V ⊔ U₂ * V  )%set.
  Proof. apply subset_antisym.
    intros [??][[?|?]?]; [left|right]; now split.
    intros [??][[??]|[??]]; split; trivial; apply _.
  Qed.

  Lemma B_prod ε `{ε ∊ Qfull} x `{x ∊ X} y `{y ∊ Y} :
    B ε (x, y) = (B ε x * B ε y)%set .
  Proof. apply subset_antisym.
    intros [a b][[??][??]]. simpl in *. split; now split.
    intros [a b][[??][??]]. simpl in *. split; [|apply _]. now split.
  Qed.

  Lemma union_of_balls_product ε `{ε ∊ Qfull} {U} `{U ⊆ X} {V} `{V ⊆ Y}
      (l₁ : list { x | x ∊ U }) (l₂ : list { y | y ∊ V })
   : ∃ (l : list { x | x ∊ U*V }),
       union_of_balls ε l = (union_of_balls ε l₁ * union_of_balls ε l₂)%set .
  Proof.
    cut (∀ x, x ∊ U → ∃ l : list {x | x ∊ U * V},
           union_of_balls ε l = (B ε x * union_of_balls ε l₂)%set).
    * intro P. induction l₁.
      + exists ([]:list { x | x ∊ U*V }). simpl.
        apply subset_antisym. intros [??][]. intros [??][[]?].
      + destruct IHl₁ as [l E]. destruct a as [x ?]. simpl.
        destruct (P x _) as [lx Ex].
        destruct (union_of_balls_union (X:=X*Y) ε l lx) as [l' E'].
        exists l'. rewrite E'. rewrite (Sets $ E), (Sets $ Ex).
        symmetry. exact (prod_join_distr_r _ _ _).
    * intros x ?. induction l₂.
      + exists ([]:list { x | x ∊ U*V }). simpl.
        apply subset_antisym. intros [??][]. intros [??][?[]].
      + destruct IHl₂ as [l E]. destruct a as [y ?]. simpl.
        exists (exist _ (x,y) (_ : (x,y) ∊ U * V) :: l). simpl.
        now rewrite (Sets $ prod_join_distr_l _ _ _), (Sets $ E), (Sets $ B_prod _ _ _).
  Qed.

  Lemma totally_bounded_product U V `{!TotallyBounded (X:=X) U} `{!TotallyBounded (X:=Y) V}
    : TotallyBounded (U * V) .
  Proof. split; try apply _. intros ε ?.
    destruct (totally_bounded U ε) as [l1 E1].
    destruct (totally_bounded V ε) as [l2 E2].
    destruct (union_of_balls_product ε l1 l2) as [l E].
    exists l. rewrite E. apply _.
  Qed.

  Lemma locally_totally_bounded_product `{!LocallyTotallyBounded X} `{!LocallyTotallyBounded Y}
    : LocallyTotallyBounded (X * Y) .
  Proof. intros U ?? ε ?.
    destruct (locally_totally_bounded π₁⁺¹(U) ε) as [l1 E1].
    destruct (locally_totally_bounded π₂⁺¹(U) ε) as [l2 E2].
    destruct (union_of_balls_product ε l1 l2) as [l E].
    exists l. transitivity (π₁⁺¹(U) * π₂⁺¹(U))%set. apply _.
    rewrite E. apply _.
  Qed.

End contents.
Hint Extern 2 (MetricSpace (_ * _)) => eapply @prod_msp : typeclass_instances.
Hint Extern 2 (FinitePoints (_ * _)) => eapply @prod_finite_points : typeclass_instances.
Hint Extern 2 (LocatedPoints (_ * _)) => eapply @prod_located_points : typeclass_instances.
Hint Extern 2 (PrelengthSpace (_ * _)) => eapply @prod_prelength : typeclass_instances.
Hint Extern 2 (MetricInequality (_ * _)) => eapply @prod_metric_inequality : typeclass_instances.
Hint Extern 2 (UniformlyContinuous _ _ fst) => eapply @fst_ufm_cont : typeclass_instances.
Hint Extern 2 (UniformlyContinuous _ _ snd) => eapply @snd_ufm_cont : typeclass_instances.
Hint Extern 5 (Bounded fst⁺¹(_)) => eapply @fst_bounded : typeclass_instances.
Hint Extern 5 (Bounded snd⁺¹(_)) => eapply @snd_bounded : typeclass_instances.
Hint Extern 5 (Bounded (_ * _)) => eapply @prod_bounded : typeclass_instances.
Hint Extern 5 (Open (_ * _)) => eapply @prod_open : typeclass_instances.
Hint Extern 4 (MetricComplementStable (_ * _)) => eapply @prod_metric_complement_stable : typeclass_instances.
Hint Extern 4 (SetApart (_ * _) (∼(_ * _)%set)) => eapply @prod_set_apart_complement : typeclass_instances.
Hint Extern 4 (SetContained (_ * _) (_ * _)) => eapply @prod_set_contained : typeclass_instances.
Hint Extern 3 (_ * _ ⊂⊂ _ * _) => eapply @prod_well_contained : typeclass_instances.
Hint Extern 3 (TotallyBounded (_ * _)) => eapply @totally_bounded_product : typeclass_instances.
Hint Extern 3 (LocallyTotallyBounded (_ * _)) => eapply @locally_totally_bounded_product : typeclass_instances.

Section uncurry.
  Context `{MetricSpace (X:=X)} `{MetricSpace (X:=Y)} `{MetricSpace (X:=Z)}.

  Context f `{!Morphism (X ⇒ Y ⇒ Z) f} `{!UniformlyContinuous (X*Y) Z (uncurry f)}.

  Instance ufm_cont_binary_1 y `{y ∊ Y} : UniformlyContinuous X Z (λ x, f x y).
  Proof.
    split; try apply _. intros ε ?.
    destruct (uniform_continuity (uncurry f) ε) as [δ[elδ C]].
    exists_sub δ. intros x1 ? x2 ? B.
    apply (C (x1,y) _ (x2,y) _). now (split; simpl).
  Qed.

  Instance ufm_cont_binary_2 x `{x ∊ X} : UniformlyContinuous Y Z (f x).
  Proof.
    split; try apply _. intros ε ?.
    destruct (uniform_continuity (uncurry f) ε) as [δ[elδ C]].
    exists_sub δ. intros y1 ? y2 ? B.
    apply (C (x,y1) _ (x,y2) _). now (split; simpl).
  Qed.
End uncurry.
Hint Extern 5 (UniformlyContinuous _ _ (λ x, ?f x ?y)) => eapply @ufm_cont_binary_1 : typeclass_instances.
Hint Extern 10 (UniformlyContinuous _ _ (?f ?x)) => eapply @ufm_cont_binary_2 : typeclass_instances.


Lemma prod_map_ufm_cont
  `{UniformlyContinuous (X:=X₁) (Y:=Y₁) (f:=f)}
  `{UniformlyContinuous (X:=X₂) (Y:=Y₂) (f:=g)}
 : UniformlyContinuous (X₁*X₂) (Y₁*Y₂) (prod_map f g).
Proof.
  destruct ( _ : (X₁ ==> Y₁)%set f ) as [?? _ _].
  destruct ( _ : (X₂ ==> Y₂)%set g ) as [?? _ _].
  split; try apply _.
  intros ε ?.
  destruct (uniform_continuity f ε) as [δ₁[? Cf]].
  destruct (uniform_continuity g ε) as [δ₂[? Cg]].
  ae_rat_set_min δ δ₁ δ₂ E1 E2.
  exists_sub δ.
  intros [x₁ x₂][??][y₁ y₂][??] [B1 B2]. simpl in B1,B2.
  split; unfold prod_map; simpl.
  apply (Cf _ _ _ _). now rewrite <-(Qfull $ E1).
  apply (Cg _ _ _ _). now rewrite <-(Qfull $ E2).
Qed.
Hint Extern 2 (UniformlyContinuous _ _ (prod_map _ _)) => eapply @prod_map_ufm_cont : typeclass_instances.


Lemma prod_diag_iso `{MetricSpace (X:=X)}
  : Isometry X (X*X) prod_diag.
Proof. split; try apply _. intros ε ? ????. unfold prod_diag.
  split. intro. now split. now intros [??].
Qed.
Hint Extern 2 (Isometry _ _ prod_diag) => eapply @prod_diag_iso : typeclass_instances.

Lemma prod_swap_iso `{MetricSpace (X:=X)} `{MetricSpace (X:=Y)}
  : Isometry (X*Y) (Y*X) prod_swap.
Proof. split; try apply _. intros ε ? [??][??][??][??]. unfold prod_swap.
  split; intros [??]; now split.
Qed.
Hint Extern 2 (Isometry _ _ prod_swap) => eapply @prod_swap_iso : typeclass_instances.

Lemma prod_assoc_r_iso `{MetricSpace (X:=X)} `{MetricSpace (X:=Y)} `{MetricSpace (X:=Z)}
  : Isometry (X*Y*Z) (X*(Y*Z)) prod_assoc_r.
Proof. split; try apply _. intros ε ? [[??]?][[??]?][[??]?][[??]?]. unfold prod_assoc_r.
  split; [ intros [[??]?] | intros [?[??]] ]; split; trivial; now split.
Qed.
Hint Extern 2 (Isometry _ _ prod_assoc_r) => eapply @prod_assoc_r_iso : typeclass_instances.

Lemma prod_assoc_l_iso `{MetricSpace (X:=X)} `{MetricSpace (X:=Y)} `{MetricSpace (X:=Z)}
  : Isometry (X*(Y*Z)) (X*Y*Z) prod_assoc_l.
Proof. split; try apply _. intros ε ? [?[??]][?[??]][?[??]][?[??]]. unfold prod_assoc_l.
  split; [ intros [?[??]] | intros [[??]?] ]; split; trivial; now split.
Qed.
Hint Extern 2 (Isometry _ _ prod_assoc_l) => eapply @prod_assoc_l_iso : typeclass_instances.

Section prod_map_dense.
  Context `{MetricSpace (X:=X₁)} `{MetricSpace (X:=X₂)}.
  Context `{MetricSpace (X:=Y₁)} `{MetricSpace (X:=Y₂)}.
  Hint Extern 0 AmbientSpace => eexact X₁ : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact Y₁ : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact X₂ : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact Y₂ : typeclass_instances.

  Context (f:X₁ ⇀ Y₁) (g:X₂ ⇀ Y₂) `{!Morphism (X₁ ⇒ Y₁) f} `{!Morphism (X₂ ⇒ Y₂) g}.

  Lemma prod_map_dense `{!Dense f⁺¹(X₁)} `{!Dense g⁺¹(X₂)} : Dense (prod_map f g)⁺¹(X₁ * X₂).
  Proof.
    split; try apply _. split. now intros [??]. intro. split. apply _. intros ε ?.
    destruct (dense f⁺¹(X₁) (fst x) ε) as [x' [[?[a [? Ea]]] Ba]]. rewrite <-(_ $ Ea) in Ba.
    destruct (dense g⁺¹(X₂) (snd x) ε) as [y' [[?[b [? Eb]]] Bb]]. rewrite <-(_ $ Eb) in Bb.
    exists_sub (f a, g b). now split.
  Qed.
End prod_map_dense.
Hint Extern 2 (Dense (prod_map _ _)⁺¹(_ * _)) => eapply @prod_map_dense : typeclass_instances.

Section prod_diag_continuous.
  Context `{MetricSpace (X:=X)} `{!LocallyTotallyBounded X}.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.

  Lemma prod_diag_continuous `{R ⊆ X} `{D ⊆ R} `{!Open D} `{!Open R}
  : Continuous D (R*R) prod_diag.
  Proof.
    cut (Continuous R (R*R) prod_diag).
      intro. apply restrict_continuous; apply _.
    assert (∀ x, x ∊ R → x ∊ X) by (intros; apply _).
    pose proof sub_metric_space (X:=X*X) : MetricSpace (R*R).
    apply continuity_alt. apply _. intros U ?.
    assert (∀ x, x ∊ U → x ∊ R) by (intros; now apply (_ :  U ⊂⊂ R)).
    split. split; try apply _. exact (sub_metric_space).
      rewrite <-(_ : Subset (R ⇒ R*R) (U ⇒ R*R)); apply _ .
      intros q ?. exists_sub q. intros x ? y ? ?. unfold prod_diag. now split.
    cut (image (X:=R) (Y:=R*R) prod_diag U ⊂⊂ R*R). intro. split; apply _.
    rewrite (Inhabited $ (_ : image (X:=R) (Y:=R*R) prod_diag U ⊆ (U*U)%set)). apply _.
  Qed.
End prod_diag_continuous.
Hint Extern 2 (Continuous _ _ prod_diag) => eapply @prod_diag_continuous : typeclass_instances.

Section prod_map_continuous.
  Context `{Cf:Continuous (X:=X₁) (Y:=Y₁) (D:=D₁) (R:=R₁) (f:=f)}.
  Context `{Cg:Continuous (X:=X₂) (Y:=Y₂) (D:=D₂) (R:=R₂) (f:=g)}.
  Hint Extern 0 AmbientSpace => eexact X₁ : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact Y₁ : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact X₂ : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact Y₂ : typeclass_instances.

  Instance: MetricSpace X₁.  Proof. now destruct Cf. Qed.
  Instance: MetricSpace Y₁.  Proof. now destruct Cf. Qed.
  Instance: MetricSpace X₂.  Proof. now destruct Cg. Qed.
  Instance: MetricSpace Y₂.  Proof. now destruct Cg. Qed.

  Instance: LocallyTotallyBounded X₁.  Proof. now destruct Cf. Qed.
  Instance: LocallyTotallyBounded Y₁.  Proof. now destruct Cf. Qed.
  Instance: LocallyTotallyBounded X₂.  Proof. now destruct Cg. Qed.
  Instance: LocallyTotallyBounded Y₂.  Proof. now destruct Cg. Qed.

  Instance: MetricSpace (R₁*R₂) (Aball := _:Ball (Y₁*Y₂)).
  Proof. apply (sub_metric_space (X:=Y₁*Y₂)). Qed.

  Section patch.
    Context U `{U ⊂⊂ D₁*D₂}.
    Notation U₁ := ((fst:X₁*X₂⇀X₁)⁺¹(U)).
    Notation U₂ := ((snd:X₁*X₂⇀X₂)⁺¹(U)).

    Instance: U₁ ⊂⊂ D₁ := fst_wc D₁ D₂ U.
    Instance: U₂ ⊂⊂ D₂ := snd_wc D₁ D₂ U.
    Instance: U₁ ⊆ X₁ := bounded_subsetoid.
    Instance: U₂ ⊆ X₂ := bounded_subsetoid.

    Instance: UniformlyContinuous U₁ R₁ f := continuity_ufm _.
    Instance: UniformlyContinuous U₂ R₂ g := continuity_ufm _.
    Instance: f⁺¹(U₁) ⊂⊂ R₁ := continuity_wc_range _.
    Instance: g⁺¹(U₂) ⊂⊂ R₂ := continuity_wc_range _.

    Instance: MetricSpace (U₁*U₂) (Aball := _:Ball (X₁*X₂)).
    Proof. apply (sub_metric_space (X:=X₁*X₂)). Qed.

    Instance prod_map_patch_ufm_cont
      : UniformlyContinuous U (Ae:=_:Equiv(X₁*X₂)) (Aball:=_:Ball(X₁*X₂))
                              (R₁*R₂) (Aball0:=_:Ball(Y₁*Y₂))
                              (prod_map f g).
    Proof.
      apply (@restrict_uniformly_continuous _ (U₁*U₂) _ (_:Ball(X₁*X₂))
        _ (R₁*R₂) _ (_:Ball(Y₁*Y₂)) (R₁*R₂) _ _ (prod_map f g)).
      exact (@prod_map_ufm_cont _ U₁ _ R₁ _ _ _ _ f _
                                _ U₂ _ R₂ _ _ _ _ g _).
      apply _.
    Qed.

    Instance: (prod_map f g)⁺¹(U) ⊆ Y₁*Y₂.
    Proof. transitivity (R₁*R₂)%set; apply _. Qed.

    Hint Extern 2 (_ ∊ X₁) => apply (_ : D₁ ⊆ X₁) : typeclass_instances.
    Hint Extern 2 (_ ∊ Y₁) => apply (_ : R₁ ⊆ Y₁) : typeclass_instances.
    Hint Extern 2 (_ ∊ X₂) => apply (_ : D₂ ⊆ X₂) : typeclass_instances.
    Hint Extern 2 (_ ∊ Y₂) => apply (_ : R₂ ⊆ Y₂) : typeclass_instances.

    Instance prod_map_patch_subsetoid : (prod_map f g)⁺¹(U) ⊆ f⁺¹(U₁) * g⁺¹(U₂).
    Proof. apply (subsetoid_from_subset (Y₁*Y₂) _ _).
      intros [y1 y2] [[??][[x1 x2][?[E1 E2]]]].
      assert ((x1,x2) ∊ (D₁ * D₂)%set) as E by now apply (_:U ⊂⊂ D₁ * D₂). destruct E.
      split.
      split. apply _. assert (x1 ∊ U₁). split. apply _. now exists_sub (x1,x2). now exists_sub x1.
      split. apply _. assert (x2 ∊ U₂). split. apply _. now exists_sub (x1,x2). now exists_sub x2.
    Qed.

    Instance prod_map_patch_bounded : Bounded (prod_map f g)⁺¹(U).
    Proof. rewrite prod_map_patch_subsetoid. apply _. Qed.

    Instance prod_map_patch_contained : SetContained (prod_map f g)⁺¹(U) (R₁ * R₂).
    Proof. rewrite prod_map_patch_subsetoid. apply _. Qed.
  End patch.

  Lemma prod_map_cont : Continuous (D₁*D₂) (R₁*R₂) (prod_map f g).
  Proof. apply (continuity_alt _). intros U ?.
    split. exact (prod_map_patch_ufm_cont U).
    split. exact (prod_map_patch_bounded U).
           exact (prod_map_patch_contained U).
  Qed.
End prod_map_continuous.
Hint Extern 2 (Continuous _ _ (prod_map _ _)) => eapply @prod_map_cont : typeclass_instances.
