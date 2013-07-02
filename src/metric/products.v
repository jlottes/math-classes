Require Import
  abstract_algebra interfaces.metric_spaces interfaces.orders
  theory.setoids theory.products metric.metric_spaces metric.maps
  orders.affinely_extended_field the_ae_rationals
  orders.lattices orders.minmax
  stdlib_field.

Local Notation AQ := TheAERationals.A.
Local Notation Q := the_ae_rationals.
Local Notation "Q∞" := (aff_ext Q).
Local Notation Qfull := (aff_ext_full Q).

Definition prod_sup_ball `{X:Subset} `{Y:Subset} `{Ball X} `{Ball Y} : Ball (X * Y)
  := λ ε x y, ball ε (fst x) (fst y) ∧ ball ε (snd x) (snd y).
Hint Extern 4 (Ball (elt_type (prod_subset ?X ?Y))) => eexact (prod_sup_ball (X:=X) (Y:=Y)) : typeclass_instances.
Hint Extern 4 (Ball (elt_type ?X * elt_type ?Y)) => eexact (prod_sup_ball (X:=X) (Y:=Y)) : typeclass_instances.

Hint Extern 2 (@AmbientSpace (?A * ?B)) =>
  exact ((_:AmbientSpace)*(_:AmbientSpace))%subset : typeclass_instances.

Section contents.
  Context `{MetricSpace (X:=X)} `{MetricSpace (X:=Y)}.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact Y : typeclass_instances.
  (*Hint Extern 0 AmbientSpace => eexact (X*Y)%subset : typeclass_instances.*)

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
      mc_replace (q-q/2) with (q/2) on Q by subfield Q. apply _.
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
      destruct (_ : (xa, xb) ∊ (X*Y)%subset ).
      destruct (_ : (ya, yb) ∊ (X*Y)%subset ).
      rewrite <-(_ $ Ex), <-(_ $ Ey).
      now destruct (P (xa,xb) _ (ya,yb) _).
    Qed.

    Lemma snd_bounded `{!Bounded U} : Bounded π₂⁺¹(U).
    Proof. split; try apply _. destruct (bounded U) as [d[eld P]].
      exists_sub d. intros x [?[[xa xb][? Ex]]] y [?[[ya yb][? Ey]]]. simpl in Ex,Ey.
      destruct (_ : (xa, xb) ∊ (X*Y)%subset ).
      destruct (_ : (ya, yb) ∊ (X*Y)%subset ).
      rewrite <-(_ $ Ex), <-(_ $ Ey).
      now destruct (P (xa,xb) _ (ya,yb) _).
    Qed.

  End projections.
  Existing Instance fst_bounded.
  Existing Instance snd_bounded.

  Instance fst_str_ufm_cont : StronglyUniformlyContinuous (X*Y) X fst := {}.
  Instance snd_str_ufm_cont : StronglyUniformlyContinuous (X*Y) Y snd := {}.

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
    apply subsetof_antisym. apply _.
    intros [x y] [??].
    destruct (open U x) as [p[? OU]].
    destruct (open V y) as [q[? OV]].
    ae_rat_set_min r p q Ep Er. split. apply _. exists_sub r.
    intros [a b] [[??][Ba Bb]]. simpl in Ba,Bb. split.
      rewrite <-OU. split; [| apply _]. red. now rewrite <-(Q∞ $ Ep).
      rewrite <-OV. split; [| apply _]. red. now rewrite <-(Q∞ $ Er).
  Qed.

  Instance prod_complement_l U V `{U ⊆ X} `{V ⊆ Y} : (∼U)*Y ⊆ ∼(U*V)%subset.
  Proof. apply (subsetoid_from_subsetof (X*Y) _ _).
    intros [x y][[? P]?]. split. apply _. intros [u v][??].
    destruct (P u _) as [q[? B]]. exists_sub q. intros [??]. now destruct B.
  Qed. 

  Instance prod_complement_r U V `{U ⊆ X} `{V ⊆ Y} : X*(∼V) ⊆ ∼(U*V)%subset.
  Proof. apply (subsetoid_from_subsetof (X*Y) _ _).
    intros [x y][?[? P]]. split. apply _. intros [u v][??].
    destruct (P v _) as [q[? B]]. exists_sub q. intros [??]. now destruct B.
  Qed. 

  Instance prod_metric_complement_stable U V `{U ⊆ X} `{V ⊆ Y}
    `{!MetricComplementStable U} `{!MetricComplementStable V}
    : MetricComplementStable (U*V).
  Proof. intros [x y]. split.
  + intros [[??][q[? P]]]. split.
    * rewrite <-(metric_complement_stable U). split. apply _. exists_sub q.
      intros s ?. assert ((s,y) ∊ ∼(U * V)%subset).
        apply (_ : ∼U * Y ⊆ ∼(U * V)%subset). apply _.
      intro B. destruct (P (s,y) _). now split.
    * rewrite <-(metric_complement_stable V). split. apply _. exists_sub q.
      intros s ?. assert ((x,s) ∊ ∼(U * V)%subset).
        apply (_ : X * ∼V ⊆ ∼(U * V)%subset). apply _.
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
  : SetApart (U₁ * U₂) (∼(V₁ * V₂)%subset).
  Proof.
    destruct (set_apart U₁ (∼V₁)) as [q1[? P1]].
    destruct (set_apart U₂ (∼V₂)) as [q2[? P2]].
    ae_rat_set_min q q1 q2 E1 E2.
    exists_sub (q/2). intros [a b] [??] [va vb] [[??] P] [B1 B2]. simpl in B1,B2.
    assert (va ∊ V₁). rewrite <-(metric_complement_stable V₁).
      split; try apply _. exists_sub (q/2). intros s ??.
      destruct (P1 a _ s _). assert (s ∊ X) by now apply (_ : ∼V₁ ⊆ X).
      assert (a ∊ X) by now apply (_ : U₁ ⊆ X).
      apply (ball_weaken_le) with (q/2+q/2); try apply _.
        now apply (ball_triangle _ _ _ va _).
        apply (subtransitivity (S:=Qfull) _ q _); trivial.
        apply (eq_le _ _). exact (ae_in_halves q).
    assert (vb ∊ V₂). rewrite <-(metric_complement_stable V₂).
      split; try apply _. exists_sub (q/2). intros s ??.
      destruct (P2 b _ s _). assert (s ∊ Y) by now apply (_ : ∼V₂ ⊆ Y).
      assert (b ∊ Y) by now apply (_ : U₂ ⊆ Y).
      apply (ball_weaken_le) with (q/2+q/2); try apply _.
        now apply (ball_triangle _ _ _ vb _).
        apply (subtransitivity (S:=Qfull) _ q _); trivial.
        apply (eq_le _ _). exact (ae_in_halves q).
    destruct (P (va,vb) _) as [?[?[]]].
    apply (subreflexivity (S:=X*Y) _).
  Qed.

  Lemma prod_well_contained U₁ U₂ V₁ V₂
    `{!MetricComplementStable (X:=X) V₁} `{!MetricComplementStable (X:=Y) V₂}
    `{U₁ ⊂⊂ V₁} `{U₂ ⊂⊂ V₂} : U₁ * U₂ ⊂⊂ V₁ * V₂ .
  Proof. apply (well_contained_stable _ _); apply _. Qed.

  Section projections_wc.
    Context D₁ D₂ `{D₁ ⊆ X} `{D₂ ⊆ Y}
           `{!MetricComplementStable (X:=X) D₁}
           `{!MetricComplementStable (X:=Y) D₂}.
    Context U `{U ⊂⊂ D₁*D₂}.

    Lemma fst_wc : π₁⁺¹(U) ⊂⊂ D₁.
    Proof. apply (well_contained_stable _ _); try apply _.
      destruct (set_apart U (∼(D₁*D₂)%subset)) as [q[? P]].
      exists_sub q. intros u [?[[ua ub][? Eu]]] v ? B. simpl in Eu.
      assert ((ua, ub) ∊ D₁*D₂) as E by now apply (_ : U ⊂⊂ D₁*D₂). destruct E.
      rewrite <-(_ : ∼D₁ * Y ⊆ ∼(D₁ * D₂)%subset ) in P.
      destruct (P (ua,ub) _ (v,ub) _). split; [|easy]. simpl.
      assert (v ∊ X) by now apply (_ : ∼D₁ ⊆ X).
      now rewrite (_ $ Eu).
    Qed.

    Lemma snd_wc : π₂⁺¹(U) ⊂⊂ D₂.
    Proof. apply (well_contained_stable _ _); try apply _.
      destruct (set_apart U (∼(D₁*D₂)%subset)) as [q[? P]].
      exists_sub q. intros u [?[[ua ub][? Eu]]] v ? B. simpl in Eu.
      assert ((ua, ub) ∊ D₁*D₂) as E by now apply (_ : U ⊂⊂ D₁*D₂). destruct E.
      rewrite <-(_ : X * ∼D₂ ⊆ ∼(D₁ * D₂)%subset ) in P.
      destruct (P (ua,ub) _ (ua,v) _). split; [easy|]. simpl.
      assert (v ∊ Y) by now apply (_ : ∼D₂ ⊆ Y).
      now rewrite (_ $ Eu).
    Qed.
  End projections_wc.

End contents.
Hint Extern 2 (MetricSpace (_ * _)) => eapply @prod_msp : typeclass_instances.
Hint Extern 2 (FinitePoints (_ * _)) => eapply @prod_finite_points : typeclass_instances.
Hint Extern 2 (LocatedPoints (_ * _)) => eapply @prod_located_points : typeclass_instances.
Hint Extern 2 (PrelengthSpace (_ * _)) => eapply @prod_prelength : typeclass_instances.
Hint Extern 2 (MetricInequality (_ * _)) => eapply @prod_metric_inequality : typeclass_instances.
Hint Extern 2 (UniformlyContinuous _ _ fst) => eapply @fst_ufm_cont : typeclass_instances.
Hint Extern 2 (UniformlyContinuous _ _ snd) => eapply @snd_ufm_cont : typeclass_instances.
Hint Extern 2 (StronglyUniformlyContinuous _ _ fst) => eapply @fst_str_ufm_cont : typeclass_instances.
Hint Extern 2 (StronglyUniformlyContinuous _ _ snd) => eapply @snd_str_ufm_cont : typeclass_instances.
Hint Extern 5 (Bounded (_ * _)) => eapply @prod_bounded : typeclass_instances.
Hint Extern 5 (Open (_ * _)) => eapply @prod_open : typeclass_instances.
Hint Extern 4 (MetricComplementStable (_ * _)) => eapply @prod_metric_complement_stable : typeclass_instances.
Hint Extern 4 (SetApart (_ * _) (∼(_ * _)%subset)) => eapply @prod_set_apart_complement : typeclass_instances.
Hint Extern 3 (_ * _ ⊂⊂ _ * _) => eapply @prod_well_contained : typeclass_instances.

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
  destruct ( _ : (X₁ ==> Y₁)%subset f ) as [?? _ _].
  destruct ( _ : (X₂ ==> Y₂)%subset g ) as [?? _ _].
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
  Context `{MetricSpace (X:=X)}.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.

  Lemma prod_diag_continuous `{R ⊆ X} `{D ⊆ R}
    `{!MetricComplementStable D} `{!MetricComplementStable R}
  : Continuous D (R*R) prod_diag.
  Proof.
    cut (Continuous R (R*R) prod_diag).
      intro. apply restrict_continuous; apply _.
    assert (∀ x, x ∊ R → x ∊ X) by (intros; apply _).
    pose proof sub_metric_space (X:=X*X) : MetricSpace (R*R).
    apply continuity_alt. apply _. intros U ?.
    assert (∀ x, x ∊ U → x ∊ R) by (intros; now apply (_ :  U ⊂⊂ R)).
    split. split; try apply _. exact (sub_metric_space).
      rewrite <-(_ : SubsetOf (R ⇒ R*R) (U ⇒ R*R)); apply _ .
      intros q ?. exists_sub q. intros x ? y ? ?. unfold prod_diag. now split.
    cut (image (X:=R) (Y:=R*R) prod_diag U ⊂⊂ R*R). intro. split; apply _.
    rewrite (Inhabited $ (_ : image (X:=R) (Y:=R*R) prod_diag U ⊆ (U*U)%subset)). apply _.
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

  Instance: MetricSpace (R₁*R₂) (Aball := _:Ball (Y₁*Y₂)).
  Proof. apply (sub_metric_space (X:=Y₁*Y₂)). Qed.

  Section patch.
    Context U `{U ⊂⊂ D₁*D₂}.
    Notation U₁ := ((fst:X₁*X₂⇀X₁)⁺¹(U)).
    Notation U₂ := ((snd:X₁*X₂⇀X₂)⁺¹(U)).

    Instance: U₁ ⊂⊂ D₁ := fst_wc D₁ D₂ U.
    Instance: U₂ ⊂⊂ D₂ := snd_wc D₁ D₂ U.

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
    Proof. transitivity (R₁*R₂)%subset; apply _. Qed.

    Hint Extern 2 (_ ∊ X₁) => apply (_ : D₁ ⊆ X₁) : typeclass_instances.
    Hint Extern 2 (_ ∊ Y₁) => apply (_ : R₁ ⊆ Y₁) : typeclass_instances.
    Hint Extern 2 (_ ∊ X₂) => apply (_ : D₂ ⊆ X₂) : typeclass_instances.
    Hint Extern 2 (_ ∊ Y₂) => apply (_ : R₂ ⊆ Y₂) : typeclass_instances.

    Instance prod_map_patch_subsetoid : (prod_map f g)⁺¹(U) ⊆ f⁺¹(U₁) * g⁺¹(U₂).
    Proof. apply (subsetoid_from_subsetof (Y₁*Y₂) _ _).
      intros [y1 y2] [[??][[x1 x2][?[E1 E2]]]].
      assert ((x1,x2) ∊ (D₁ * D₂)%subset) as E by now apply (_:U ⊂⊂ D₁ * D₂). destruct E.
      split.
      split. apply _. assert (x1 ∊ U₁). split. apply _. now exists_sub (x1,x2). now exists_sub x1.
      split. apply _. assert (x2 ∊ U₂). split. apply _. now exists_sub (x1,x2). now exists_sub x2.
    Qed.

    Instance prod_map_patch_bounded : Bounded (prod_map f g)⁺¹(U).
    Proof. rewrite prod_map_patch_subsetoid. apply _. Qed.

    Instance prod_map_patch_apart : SetApart (prod_map f g)⁺¹(U) (∼(R₁ * R₂)%subset).
    Proof. rewrite prod_map_patch_subsetoid. apply _. Qed.
  End patch.

  Lemma prod_map_cont : Continuous (D₁*D₂) (R₁*R₂) (prod_map f g).
  Proof. apply (continuity_alt _). intros U ?.
    split. exact (prod_map_patch_ufm_cont U).
    split. exact (prod_map_patch_bounded U).
           exact (prod_map_patch_apart U).
  Qed.
End prod_map_continuous.
Hint Extern 2 (Continuous _ _ (prod_map _ _)) => eapply @prod_map_cont : typeclass_instances.
