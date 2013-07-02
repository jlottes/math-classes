Require Import
  abstract_algebra interfaces.orders interfaces.rationals interfaces.metric_spaces
  theory.setoids theory.jections theory.rings theory.rationals theory.powerset
  orders.rings orders.lattices orders.minmax
  orders.affinely_extended_field stdlib_field
  metric.metric_spaces.

Local Notation AQ := TheAERationals.A.
Local Notation Q := the_ae_rationals.
Local Notation "Q∞" := (aff_ext Q).
Local Notation Qfull := (aff_ext_full Q).

(* f = g → UniformlyContinuous X Y f ↔ UniformlyContinuous X Y g *)
Lemma uniformly_continuous_proper: Find_Proper_Signature (@UniformlyContinuous) 0
  (∀ A1 (Ae1:Equiv A1) (Aball1:Ball A1) (X:@Subset A1)
     A2 (Ae2:Equiv A2) (Aball2:Ball A2) (Y:@Subset A2),
     Proper ((=) ==> impl) (UniformlyContinuous X Y)).
Proof. red; intros. intros f g E ?.
  destruct (_ : UniformlyContinuous X Y f) as [?? _ _ _].
  assert (Morphism (X ⇒ Y) g) by (rewrite <- E; apply _).
  split; try apply _.
  intros ε ?. destruct (uniform_continuity_def X Y ε) as [δ[el Cf]]. exists_sub δ.
  intros. rewrite <-(E x x), <-(E y y); try now red_sig. now apply Cf.
Qed.
Hint Extern 0 (Find_Proper_Signature (@UniformlyContinuous) 0 _) => eexact uniformly_continuous_proper : typeclass_instances.

Lemma ufm_continuous_dom_ran_proper
  {A} `{Equiv A} `{Ball A} (X:@Subset A)
  {B} `{Equiv B} `{Ball B} (Y:@Subset B)
  f `{!UniformlyContinuous X Y f}
  X' Y' : X = X' → Y = Y' → UniformlyContinuous X' Y' f.
Proof. intros EX EY.
  destruct (_ : UniformlyContinuous X Y f) as [?? _ _ _].
  assert (X' ⊆ X) by (rewrite <-EX; apply _).
  assert (Y' ⊆ Y) by (rewrite <-EY; apply _).
  split. exact sub_metric_space. exact sub_metric_space.
  assert (Y ⊆ Y') by (rewrite <-EY; apply _).
  rewrite <-(_ : SubsetOf (X ⇒ Y) (X' ⇒ Y')). apply _.
  intros ε ?. destruct (uniform_continuity_def X Y ε) as [δ [el P]].
  exists_sub δ. intros x ? y ?.
  assert (x ∊ X) by (rewrite EX; apply _).
  assert (y ∊ X) by (rewrite EX; apply _).
  now apply P.
Qed.

(* f = g → Isometry X Y f ↔ Isometry X Y g *)
Lemma isometry_proper: Find_Proper_Signature (@Isometry) 0
  (∀ A1 (Ae1:Equiv A1) (Aball1:Ball A1) (X:@Subset A1)
     A2 (Ae2:Equiv A2) (Aball2:Ball A2) (Y:@Subset A2),
   Proper ((=) ==> impl) (Isometry X Y)).
Proof. red; intros. intros f g E ?.
  destruct (_ : Isometry X Y f) as [?? _ _].
  assert (Morphism (X ⇒ Y) g) by (rewrite <- E; apply _).
  split; try apply _.
  intros. rewrite <-(E x x), <-(E y y); try now red_sig. now apply (isometric_def X Y).
Qed.
Hint Extern 0 (Find_Proper_Signature (@Isometry) 0 _) => eexact isometry_proper : typeclass_instances.

(* f = g → StronglyUniformlyContinuous X Y f ↔ StronglyUniformlyContinuous X Y g *)
Lemma strongly_uniformly_continuous_proper: Find_Proper_Signature (@StronglyUniformlyContinuous) 0
  (∀ A1 (Ae1:Equiv A1) (Aball1:Ball A1) (X:@Subset A1)
     A2 (Ae2:Equiv A2) (Aball2:Ball A2) (Y:@Subset A2),
     Proper ((=) ==> impl) (StronglyUniformlyContinuous X Y)).
Proof. red; intros. intros f g E ?.
  destruct (_ : UniformlyContinuous X Y f) as [?? _ _ _].
  assert (UniformlyContinuous X Y g) by (rewrite <- E; apply _).
  split; try apply _.
  intros U ??. rewrite <-E. now apply (strongly_ufm_cont _ _).
Qed.
Hint Extern 0 (Find_Proper_Signature (@StronglyUniformlyContinuous) 0 _) => eexact strongly_uniformly_continuous_proper : typeclass_instances.

Section maps.
  Context `{X:Subset} `{Equiv X} `{Ball X}.
  Context `{Y:Subset} `{Equiv Y} `{Ball Y}.

  Existing Instance uniform_cont_X.
  Existing Instance uniform_cont_Y.
  Existing Instance isometry_X.
  Existing Instance isometry_Y.

  Lemma uniform_continuity f `{!UniformlyContinuous X Y f} ε `{ε ∊ Q∞₊} :  ∃ `{δ ∊ Q∞₊},
    ∀ `{x ∊ X} `{y ∊ X}, ball δ x y → ball ε (f x) (f y).
  Proof.
   destruct (ae_decompose_pos ε) as [E|?].
   + exists_sub ∞. intros. rewrite (_ $ E). exact (msp_ball_inf _ _).
   + destruct (uniform_continuity_def X Y ε) as [δ[? P]]. now exists_sub δ.
  Qed.

  Lemma isometric f `{!Isometry X Y f} ε `{ε ∊ Qfull} x `{x ∊ X} y `{y ∊ X}
    : ball ε x y ↔ ball ε (f x) (f y).
  Proof.
    split; intro E'; pose proof (msp_nonneg _ _ _ E');
      ( destruct (ae_decompose_nonneg ε) as [E|?];
        [ rewrite (_ $ E); exact (msp_ball_inf _ _) |]);
    apply (ball_closed _ _ _); intros;
     apply (isometric_def X Y _ _ _); apply (ball_weaken_plus _ _ _); trivial; apply _.
  Qed.

  Lemma isometry_uniformly_continuous f `{!Isometry X Y f} : UniformlyContinuous X Y f.
  Proof. split; try apply _.
    intros ε ?. exists_sub ε. intros. now rewrite <-(isometric f _ _ _).
  Qed.

  Lemma isometry_strongly_uniformly_continuous f `{!Isometry X Y f} : StronglyUniformlyContinuous X Y f.
  Proof. split. now apply isometry_uniformly_continuous.
    destruct (_ : Isometry X Y f) as [?? _ _].
    intros U [_ ?[d[? P]]] [x ?].
    split; try apply _. exists_sub d.
    intros ? [? [x1 [? Ex1]]] ? [? [x2 [? Ex2]]].
    rewrite <- (_ $ Ex1), <- (_ $ Ex2), <- (isometric f _ _ _). now apply P.
  Qed.

  Instance restrict_uniformly_continuous `{Y' ⊆ Y} `{!MetricSpace Y}
      f `{!UniformlyContinuous X Y' f} (X':Subset) `{X' ⊆ X} : UniformlyContinuous X' Y f.
  Proof.
    split; trivial.
    + exact sub_metric_space.
    + rewrite <-(_ : SubsetOf (X ⇒ Y') (X' ⇒ Y)). apply _.
    + intros. pose proof (sub_metric_space : MetricSpace Y').
        destruct (uniform_continuity_def X Y' ε) as [δ[? P]]. exists_sub δ.
      intros. now apply (P _ _ _ _).
  Qed.

  Lemma restrict_ufm_cont_image f `{!UniformlyContinuous X Y f} S `{!S ⊆ X}
    : UniformlyContinuous S f⁺¹(S) f.
  Proof.
    split; try exact sub_metric_space. apply _.
    now destruct (restrict_uniformly_continuous f S).
  Qed.

  Lemma restrict_str_uniformly_continuous
     f `{!StronglyUniformlyContinuous X Y f} (X':Subset) `{X' ⊆ X} : StronglyUniformlyContinuous X' Y f.
  Proof. pose proof restrict_uniformly_continuous f X'.
    split. apply _.
    intros U [???] ?. split; try apply _.  apply subsetoid_image; apply _.
    assert (Bounded (X:=X) U). split; trivial; try apply _. now transitivity X'.
    now destruct (strongly_ufm_cont _ _ U).
  Qed.

  Lemma restrict_str_ufm_cont_image f `{!StronglyUniformlyContinuous X Y f} S `{!S ⊆ X}
    : StronglyUniformlyContinuous S f⁺¹(S) f.
  Proof. split. exact (restrict_ufm_cont_image f S).
    pose proof restrict_str_uniformly_continuous f S.
    intros U ??.
    assert (U ⊆ X). transitivity S; apply _.
    rewrite (subimage_image _).
    split. exact sub_metric_space. exact (image_order_preserving _ _ _).
    now destruct (strongly_ufm_cont S Y U).
  Qed.

End maps.

Hint Extern 20 (UniformlyContinuous _ _ _) => eapply @isometry_uniformly_continuous : typeclass_instances.
Hint Extern 20 (StronglyUniformlyContinuous _ _ _) => eapply @isometry_strongly_uniformly_continuous : typeclass_instances.
Hint Extern 5 (UniformlyContinuous ?S ?f⁺¹(?S) ?f) => eapply @restrict_ufm_cont_image : typeclass_instances.
Hint Extern 5 (StronglyUniformlyContinuous ?S ?f⁺¹(?S) ?f) => eapply @restrict_str_ufm_cont_image : typeclass_instances.

Lemma id_isometry `{MetricSpace (X:=X)} `{Y ⊆ X} : Isometry Y X (id:Y ⇀ X).
Proof. split; try apply _. exact sub_metric_space. tauto. Qed.
Hint Extern 2 (Isometry _ _ id) => eapply @id_isometry : typeclass_instances.

Lemma id_uniformly_cont `{MetricSpace (X:=X)} `{Y ⊆ X} : UniformlyContinuous Y X id.
Proof _.
Hint Extern 2 (UniformlyContinuous _ _ id) => eapply @id_uniformly_cont : typeclass_instances.

Lemma id_str_uniformly_cont `{MetricSpace (X:=X)} `{Y ⊆ X} : StronglyUniformlyContinuous Y X id.
Proof _.
Hint Extern 2 (StronglyUniformlyContinuous _ _ id) => eapply @id_str_uniformly_cont : typeclass_instances.

Lemma const_uniformly_cont `{MetricSpace (X:=X)} `{MetricSpace (X:=Y)} c `{c ∊ Y}
  : UniformlyContinuous X Y (λ _, c).
Proof. split; try apply _. intros ??. exists_sub ∞. now intros. Qed.
Hint Extern 5 (UniformlyContinuous _ _ (λ _, ?c)) => eapply @const_uniformly_cont : typeclass_instances.

Lemma const_str_uniformly_cont `{MetricSpace (X:=X)} `{MetricSpace (X:=Y)} c `{c ∊ Y}
  : StronglyUniformlyContinuous X Y (λ _, c).
Proof. split; try apply _. intros ???. split; try apply _.
  exists_sub 0. intros ? [?[?[? E1]]] ? [?[?[? E2]]].
  now rewrite <-(_ $ E1), <-(_ $ E2).
Qed.
Hint Extern 5 (StronglyUniformlyContinuous _ _ (λ _, ?c)) => eapply @const_str_uniformly_cont : typeclass_instances.


Section more_maps.
  Context `{X:Subset} `{Equiv X} `{Ball X}.
  Context `{Y:Subset} `{Equiv Y} `{Ball Y}.
  Context `{Z:Subset} `{Equiv Z} `{Ball Z}.

  Existing Instance uniform_cont_X.
  Existing Instance uniform_cont_Y.
  Existing Instance isometry_X.
  Existing Instance isometry_Y.

  Open Scope mc_fun_scope.

  Lemma compose_isometry f g `{!Isometry X Y f} `{!Isometry Y Z g}
  : Isometry X Z (g ∘ f).
  Proof.
    split; try apply _. unfold compose. intros.
    transitivity (ball ε (f x) (f y)); exact (isometric _ _ _ _).
  Qed.

  Lemma invert_isometry f `{!Isometry X Y f} `{!Inverse f} `{!Bijective X Y f}
  : Isometry Y X f⁻¹.
  Proof.
    split; try apply _. intros.
    rewrite <-(Y $ surjective_applied f x) at 1.
    rewrite <-(Y $ surjective_applied f y) at 1.
    symmetry. exact (isometric f _ _ _).
  Qed.

  Instance compose_uniformly_cont
    f g `{!UniformlyContinuous X Y f} `{!UniformlyContinuous Y Z g}
  : UniformlyContinuous X Z (g ∘ f).
  Proof.
    split; try apply _. unfold compose. intros ε ?.
    destruct (uniform_continuity g ε) as [δ₁[? P1]].
    destruct (uniform_continuity f δ₁) as [δ₂[? P2]].
    exists_sub δ₂. intros. apply (P1 _ _ _ _). now apply P2.
  Qed.

  Lemma compose_str_uniformly_cont
    f g `{!StronglyUniformlyContinuous X Y f} `{!StronglyUniformlyContinuous Y Z g}
  : StronglyUniformlyContinuous X Z (g ∘ f).
  Proof.
    split; try apply _. intros U ??.
    rewrite (compose_image _ _ _).
    pose proof (strongly_ufm_cont X Y U).
    apply (strongly_ufm_cont Y Z _).
  Qed.

  Lemma isometry_injective f `{!Isometry X Y f} : Injective X Y f.
  Proof.
    split; try apply _. intros x ? y ?.
    rewrite <-2!(ball_separated _ _). intro.
    now rewrite (isometric f _ _ _).
  Qed.

  Instance uniformly_cont_subsetoid `{!Setoid X} `{!Setoid Y} : X ==> Y ⊆ X ⇒ Y.
  Proof. apply subsetoid_alt. apply _. intros f g E P. red in P.
    red. unfold_sigs. now rewrite <-E.
    now intros ? [??? _].
  Qed.

  Lemma isometry_subsetoid `{!Setoid X} `{!Setoid Y} : Isometry X Y ⊆ X ==> Y.
  Proof. apply subsetoid_alt. apply _. intros f g E P. red in P.
    red. unfold_sigs. now rewrite <-E.
    intros f P. red in P. red. apply _.
  Qed.

  Context `{UnEq X} `{UnEq Y} `{!MetricInequality X} `{!MetricInequality Y}.

  Instance uniformly_cont_strong_mor f `{!UniformlyContinuous X Y f} : Strong_Morphism X Y f.
  Proof. split. apply _. intros x ? y ?. rewrite !(metric_inequality _ _).
    intros [q[? E]].
    destruct (uniform_continuity f q) as [r[? Cf]].
    destruct (ae_decompose_pos r) as [Er|?].
      contradict E. apply (Cf _ _ _ _). rewrite (_ $ Er). exact (msp_ball_inf _ _).
    exists_sub r. contradict E. now apply (Cf _ _ _ _).
  Qed.

  Lemma isometry_str_injective f `{!Isometry X Y f} : StrongInjective X Y f.
  Proof. split; [| apply _]. intros x ? y ?. rewrite !(metric_inequality _ _).
    intros [q[? E]]. exists_sub q. now rewrite <-(isometric f _ _ _).
  Qed.

End more_maps.

Hint Extern 4 (Isometry _ _ (_ ∘ _)) =>  eapply @compose_isometry : typeclass_instances.
Hint Extern 4 (Isometry _ _ (inverse _)) => eapply @invert_isometry : typeclass_instances.
Hint Extern 4 (UniformlyContinuous _ _ (_ ∘ _)) => eapply @compose_uniformly_cont : typeclass_instances.
Hint Extern 4 (StronglyUniformlyContinuous _ _ (_ ∘ _)) => eapply @compose_str_uniformly_cont : typeclass_instances.
(*
Hint Extern 10 (Strong_Morphism _ _ _) => eapply @uniformly_cont_strong_mor : typeclass_instances.
Hint Extern 20 (Injective _ _ _) => eapply @isometry_injective : typeclass_instances.
Hint Extern 20 (StrongInjective _ _ _) => eapply @isometry_str_injective : typeclass_instances.
*)

Hint Extern 2 (_ ==> _ ⊆ _ ⇒ _) => eapply @uniformly_cont_subsetoid : typeclass_instances.
Hint Extern 2 (Setoid (?X ==> ?Y)) => eapply (subsetoid_a (T:=(X ⇒ Y))) : typeclass_instances.
Hint Extern 2 (Isometry _ _ ⊆ _ ==> _) => eapply @isometry_subsetoid : typeclass_instances.
Hint Extern 2 (Setoid (Isometry ?X ?Y)) => eapply (subsetoid_a (T:=(UniformlyContinuous X Y))) : typeclass_instances.
Hint Extern 2 (Isometry ?X ?Y ⊆ ?X ⇒ ?Y) => transitivity (UniformlyContinuous X Y) : typeclass_instances.

Hint Extern 0 (_ ∊ _ --> _) => red : typeclass_instances.
Hint Extern 0 (_ ∊ _ ==> _) => red : typeclass_instances.
Hint Extern 0 (_ ∊ Isometry _ _) => red : typeclass_instances.

Lemma dense_compose_iso
  `{MetricSpace (X:=X)} `{MetricSpace (X:=Y)} `{MetricSpace (X:=Z)}
  (f:X ⇀ Y) `{!Morphism (X ⇒ Y) f} g `{!Isometry Y Z g}
 `{!Dense (X:=Y) (f)⁺¹(X)} `{!Dense (X:=Z) (g)⁺¹(Y)} : Dense (X:=Z) (g ∘ f)⁺¹(X) .
Proof. split. apply _. apply _. intro z. split. now intros [? _]. intro. split. apply _. intros ε ?.
  destruct (dense_image g Y z (ε/2)) as [y[ely ?]].
  destruct (dense_image f X y (ε/2)) as [x[elx ?]].
  exists_sub ((g ∘ f) x). rewrite <-(Qfull $ ae_in_halves ε). unfold compose.
  apply (ball_triangle _ _ _ (g y) _); trivial.
  now rewrite <-(isometric g _ _ _).
Qed.
Hint Extern 5 (Dense (_ ∘ _)⁺¹(_)) => eapply @dense_compose_iso : typeclass_instances.

Section uniform_continuity_closure.
  Context `{X:Subset} `{Equiv X} `{Ball X}.
  Context `{Y:Subset} `{Equiv Y} `{Ball Y}.

  Existing Instance uniform_cont_X.
  Existing Instance uniform_cont_Y.

  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact Y : typeclass_instances.

  Lemma uniformly_continuous_closure f `{!UniformlyContinuous X Y f} 
    D `{D ⊆ X} R : ClosedFun (D ⇀ R) f → ClosedFun ( closure D ⇀ closure R ) f.
  Proof. intros P x [? Q]. split. apply _. intros ε ?.
    destruct (uniform_continuity f ε) as [δ[? C]].
    destruct (Q δ _) as [y[? ?]].
    assert (f y ∊ R) by now apply P.
    exists_sub (f y).
    now apply (C _ _ _ _).
  Qed.
End uniform_continuity_closure.

Section continuity_alt.
  Context `{MetricSpace (X:=X)} `{D ⊆ X} `{!MetricComplementStable (X:=X) D}.
  Context `{MetricSpace (X:=Y)} `{R ⊆ Y} `{!MetricComplementStable (X:=Y) R}.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact Y : typeclass_instances.


  Lemma continuity_alt (f:D ⇀ R) `{!Morphism (D ⇒ R) f}
    : (∀ `{U ⊂⊂ D}, UniformlyContinuous U R f ∧ Bounded f⁺¹(U) ∧ SetApart f⁺¹(U) (∼R))
     → Continuous D R f.
  Proof. intro P. split; try apply _; intros U ?. now destruct (P U _).
    split; try apply _; try apply (P U _).
  Qed.
End continuity_alt.

Lemma strongly_uniformly_continuous_continuous
  `{MetricSpace (X:=X)} `{D ⊆ X} `{!MetricComplementStable (X:=X) D}
  `{MetricSpace (X:=Y)}
  f `{!StronglyUniformlyContinuous D Y f} : Continuous (X:=X) (Y:=Y) D Y f.
Proof. apply (continuity_alt f). intros U ?.
  pose proof (restrict_str_uniformly_continuous f U).
  assert (Bounded (X:=D) U). split; [ exact sub_metric_space | apply _ | exact (bounded U)].
  pose proof (strongly_ufm_cont _ _ U).
  split; [| split]; apply _.
Qed.
Hint Extern 20 (Continuous _ _ _) => eapply @strongly_uniformly_continuous_continuous : typeclass_instances.

(* f = g → Continuous D R f ↔ Continuous D R g *)
Lemma continuous_proper: Find_Proper_Signature (@Continuous) 0
  (∀ A1 (Ae1:Equiv A1) (Aball1:Ball A1) (X:@Subset A1) D
     A2 (Ae2:Equiv A2) (Aball2:Ball A2) (Y:@Subset A2) R,
     Proper ((=)==> impl) (Continuous (X:=X) (Y:=Y) D R)).
Proof. red; intros. intros f g Ef ?.
  destruct (_ : Continuous (X:=X) (Y:=Y) D R f) as [?? ?? _ _ _ _ _].
  assert (Morphism (D ⇒ R) g) by (rewrite <-Ef; apply _).
  split; try apply _; intros U ?.
  rewrite <-(ext_equiv_subrelation U D R R _ _ Ef). now apply (continuity_ufm (X:=X) (Y:=Y)).
  rewrite <-Ef. now apply (continuity_wc_range (X:=X) (Y:=Y)).
Qed.
Hint Extern 0 (Find_Proper_Signature (@Continuous) 0 _) => eexact continuous_proper : typeclass_instances.

Lemma continuous_dom_ran_proper `{MetricSpace (X:=X)} `{MetricSpace (X:=Y)}
  D R f `{!Continuous (X:=X) (Y:=Y) D R f} D' R'
  : D = D' → R = R' → Continuous (X:=X) (Y:=Y) D' R' f.
Proof. intros ED ER.
  assert (D' ⊆ X) by (rewrite <-ED; apply _).
  assert (R' ⊆ Y) by (rewrite <-ER; apply _).
  assert (MetricComplementStable (X:=X) D') by (rewrite <-ED; apply _).
  assert (MetricComplementStable (X:=Y) R') by (rewrite <-ER; apply _).
  assert (D' ⊆ D) by (rewrite <-ED; apply _).
  assert (R ⊆ R') by (rewrite <-ER; apply _).
  apply continuity_alt.
  rewrite <-(_ : SubsetOf (D ⇒ R) (D' ⇒ R')). apply _.
  intros U ?. assert (WellContained (X:=X) U D) by (rewrite ED; apply _).
  pose proof (continuity_ufm (X:=X) (Y:=Y) U).
  pose proof (continuity_wc_range (X:=X) (Y:=Y) U).
  intuition.
  + apply (ufm_continuous_dom_ran_proper U R); trivial. reflexivity.
  + rewrite <-(image_dom_range_proper f D' R' U). apply _.
  + rewrite <-(image_dom_range_proper f D' R' U). rewrite <-ER. apply _.
Qed.

Section id_continuous.
  Context `{MetricSpace (X:=X)}.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.

  Lemma id_continuous `{R ⊆ X} `{D ⊆ R}
    `{!MetricComplementStable D} `{!MetricComplementStable R}
  : Continuous D R id.
  Proof. assert (D ⊆ X) by (transitivity R; apply _).
    split; try apply _; intros U ?;
    assert (U ⊆ R) by (transitivity D; apply _);
    pose proof sub_metric_space : MetricSpace R.
    apply _. rewrite (image_id _).
    now rewrite <-((⊆ X) $ (_ : D ⊆ R)).
  Qed.
End id_continuous.
Hint Extern 2 (Continuous _ _ id) => eapply @id_continuous : typeclass_instances.

Section continuous_subsetoid.
  Context
    `{X:Subset} `{Equiv X} `{Ball X}
    `{Y:Subset} `{Equiv Y} `{Ball Y}.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact Y : typeclass_instances.

  Instance continuous_subsetoid (D:@Subset X) (R:@Subset Y) `{!Setoid D} `{!Setoid R} : D --> R ⊆ D ⇒ R.
  Proof. apply subsetoid_alt. apply _. intros f g E P. red in P.
    red. unfold_sigs. now rewrite <-E.
    now intros ? [??? _].
  Qed.
End continuous_subsetoid.
Hint Extern 2 (_ --> _ ⊆ _ ⇒ _) => eapply @continuous_subsetoid : typeclass_instances.
Hint Extern 2 (Setoid (?X --> ?Y)) => eapply (subsetoid_a (T:=(X ⇒ Y))) : typeclass_instances.

Section compose_continuous.
  Context
    `{X:Subset} `{Equiv X} `{Ball X}
    `{Y:Subset} `{Equiv Y} `{Ball Y}
    `{Z:Subset} `{Equiv Z} `{Ball Z}.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact Y : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact Z : typeclass_instances.

  Lemma compose_continuous
    D₁ R₁ D₂ R₂ (f:D₁ ⇀ R₁) (g:D₂ ⇀ R₂)
    `{!Continuous (X:=X) (Y:=Y) D₁ R₁ f}
    `{!Continuous (X:=Y) (Y:=Z) D₂ R₂ g}
    `{R₁ ⊆ D₂}
    : Continuous D₁ R₂ (g ∘ f).
  Proof.
    pose proof cont_X : MetricSpace X.
    pose proof cont_Y : MetricSpace Y.
    pose proof cont_Y : MetricSpace Z.
    assert (Morphism (D₁ ⇒ D₂) f).
      rewrite <-(_:SubsetOf (D₁ ⇒ R₁) (D₁ ⇒ D₂)). apply _.
    pose proof _ : Morphism (D₁ ⇒ R₂) (g ∘ (f:D₁ ⇀ D₂)).
    apply (continuity_alt _). intros U ?.
    pose proof (continuity_ufm U). pose proof (continuity_wc_range U).
    assert (f⁺¹(U) ⊂⊂ D₂) by (rewrite <-((⊆ Y) $ (_ : R₁ ⊆ D₂)); apply _).
    pose proof (continuity_ufm f⁺¹(U)). pose proof (continuity_wc_range f⁺¹(U)).
    split.
    + apply (compose_uniformly_cont (X:=U) (Y:=f⁺¹(U)) (Z:=R₂) (f:D₁ ⇀ D₂)); trivial.
      eapply (@restrict_ufm_cont_image _ U); apply _.
    + cut ((g ∘ f)⁺¹(U) ⊂⊂ R₂). intuition; apply _.
      rewrite (compose_image); trivial; try apply _.
      rewrite <-(image_dom_range_proper f U D₂ U). apply _.
      rewrite <-(_:SubsetOf (D₁ ⇒ R₁) (U ⇒ D₂)). apply _.
  Qed.
End compose_continuous.
Hint Extern 2 (Continuous ?X ?Z (@compose _ ?X _ ?Y _ ?Z ?g ?f))
  => eapply (compose_continuous (X:=_:AmbientSpace) (Y:=_:AmbientSpace) (Z:=_:AmbientSpace)
               X Y Y Z f g) : typeclass_instances.

Section cont_strong_mor.
  Context `{Cf:Continuous (X:=X) (Y:=Y) (D:=D) (R:=R) (f:=f)}.
  Context `{UnEq X} `{!MetricInequality X}.
  Context `{UnEq Y} `{!MetricInequality Y}.
  Context `{!FinitePoints X}.

  Instance: MetricSpace X.  Proof. now destruct Cf. Qed.
  Instance: MetricSpace Y.  Proof. now destruct Cf. Qed.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact Y : typeclass_instances.

  Hint Extern 5 (_ ∊ X) => apply (_ : D ⊆ X) : typeclass_instances.
  Hint Extern 5 (_ ∊ Y) => apply (_ : R ⊆ Y) : typeclass_instances.

  Lemma cont_strong_mor : Strong_Morphism D R f.
  Proof. split. apply _. intros x ? y ? E.
    pose proof _ : B 0 x ⊔ B 0 y ⊂⊂ D .
    assert (∀ z, z ∊ B 0 x ⊔ B 0 y → z ∊ D). intros. now apply (_ : B 0 x ⊔ B 0 y ⊂⊂ D).
    assert (MetricInequality (B 0 x ⊔ B 0 y)). intros x' ? y' ?. exact (metric_inequality (X:=X) _ _).
    assert (MetricInequality R). intros x' ? y' ?. exact (metric_inequality (X:=Y) _ _).
    pose proof (continuity_ufm (B 0 x ⊔ B 0 y)).
    pose proof uniformly_cont_strong_mor (X:=B 0 x ⊔ B 0 y) (Y:=R) f as sm.
    apply (strong_morphism_proper (Strong_Morphism := sm)); trivial; apply _.
  Qed.

End cont_strong_mor.
Arguments cont_strong_mor {_ X _ _ _ Y _ _ D R} f {Cf _ _ _ _ _}.

Section continuous_misc.
  Context `{Cf:Continuous (X:=X) (Y:=Y) (D:=D) (R:=R) (f:=f)}.
  Instance: MetricSpace X.  Proof. now destruct Cf. Qed.
  Instance: MetricSpace Y.  Proof. now destruct Cf. Qed.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact Y : typeclass_instances.

  Hint Extern 5 (_ ∊ X) => apply (_ : D ⊆ X) : typeclass_instances.
  Hint Extern 5 (_ ∊ Y) => apply (_ : R ⊆ Y) : typeclass_instances.

  Lemma pointwise_continuity x `{x ∊ D} ε `{ε ∊ Q∞₊} :  ∃ `{δ ∊ Q₊},
    ∀ `{y ∊ D}, ball δ x y → ball ε (f x) (f y).
  Proof. destruct (ball_well_contained_stable (X:=X) D x) as [q[??]].
    pose proof (continuity_ufm (B q x)).
    destruct (uniform_continuity (f:B q x ⇀ R) ε) as [δ[? C]].
    ae_rat_set_min r q δ E1 E2. pose proof (ae_pos_finite_bound r _ E1).
    exists_sub r. intros y ? By.
    assert (y ∊ B q x). split; [| apply _]. red.
      apply (ball_weaken_le) with r; trivial; try apply _.
    apply (C _ _ _ _).
      apply (ball_weaken_le) with r; trivial; try apply _.
  Qed.

  Context D' `{D' ⊆ D} `{!MetricComplementStable (X:=X) D'}.

  Instance: D' ⊆ X. Proof. transitivity D; apply _. Qed.

  Lemma restrict_continuous : Continuous D' R f.
  Proof. apply continuity_alt.
    rewrite <- (_ : SubsetOf (D ⇒ R) (D' ⇒ R)). apply _.
    intros U P.
    rewrite ((⊆ X) $ (_ : D' ⊆ D)) in P.
    pose proof (continuity_ufm U). pose proof (continuity_wc_range U).
    repeat (split; [apply _ |]). apply _.
  Qed.

End continuous_misc.
Arguments pointwise_continuity {_ X _ _ _ Y _ _ D R} f {_} x {_} ε {_}.

Hint Extern 30 (@Subset (elt_type (?X ⇀ ?Y))) => eapply ((UniformlyContinuous X Y) : Subset) : typeclass_instances.
Hint Extern 30 (@Subset (elt_type (?X ⇀ ?Y))) => eapply ((Continuous X Y) : Subset) : typeclass_instances.

Definition sup_ball `{X:Subset} `{Y:Subset} `{Ball Y} : Ball (X ⇀ Y)
  := λ ε f g, ε ∊ Q∞⁺ ∧ ∀ `{x ∊ X}, ball ε (f x) (g x).
Hint Extern 4 (Ball (elt_type (?X ⇀ ?Y))) => eexact (sup_ball (X:=X) (Y:=Y)) : typeclass_instances.
Hint Extern 4 (Ball (elt_type (?X ⇒ ?Y))) => eexact (sup_ball (X:=X) (Y:=Y)) : typeclass_instances.
Hint Extern 8 (Ball (_ -> _)) => eapply @sup_ball : typeclass_instances.

Hint Extern 4 (Ball (elt_type (?X --> ?Y))) => eexact (sup_ball (X:=X) (Y:=Y)) : typeclass_instances.
Hint Extern 4 (Equiv (elt_type (?X --> ?Y))) => eapply (@ext_equiv _ X _ Y) : typeclass_instances.
Hint Extern 4 (Ball (elt_type (?X ==> ?Y))) => eexact (sup_ball (X:=X) (Y:=Y)) : typeclass_instances.
Hint Extern 4 (Equiv (elt_type (?X ==> ?Y))) => eapply (@ext_equiv _ X _ Y) : typeclass_instances.
Hint Extern 4 (Ball (elt_type (Isometry ?X ?Y))) => eexact (sup_ball (X:=X) (Y:=Y)) : typeclass_instances.
Hint Extern 4 (Equiv (elt_type (Isometry ?X ?Y))) => eapply (@ext_equiv _ X _ Y) : typeclass_instances.


Section fun_space.
  Context `{Setoid (S:=X)} `{Y:Subset} `{Ball Y} `{Equiv Y} `{!MetricSpace Y}.

  Ltac mor_prem_tac :=
    repeat match goal with H : ?f ∊ ?X ⇒ ?Y |- _ => change (Morphism (X ⇒ Y) f) in H end.

  Instance fun_msp : MetricSpace (A:=X ⇀ Y) (X ⇒ Y).
  Proof. split; unfold ball, sup_ball. apply _.
  + intros a b E1 f1 f2 Ef g1 g2 Eg [? P]. unfold_sigs. mor_prem_tac.
    split. now rewrite <- (_ $ E1).
    intros x ?. rewrite <- (_ $ E1), <-(Ef x x), <-(Eg x x); try now red_sig. exact (P _ _).
  + intuition.
  + intros. split. apply _. intros. mor_prem_tac. exact (msp_ball_inf _ _).
  + intros. intros f ?. mor_prem_tac. split. apply _. now intros.
  + intros. intros f ? g ? [_ P]. mor_prem_tac. split. apply _. intros. subsymmetry. now apply P.
  + intros f ? g ? [_ P] x y [[??] E]. mor_prem_tac. red_sig. rewrite (X $ E).
    rewrite <-(ball_separated _ _). exact (P _ _).
  + intros a ? b ? f ? g ? h ? [_ P] [_ Q]. split. apply _. intros x ?. mor_prem_tac.
    apply (ball_triangle _ _ _ (g x) _). exact (P _ _). exact (Q _ _).
  + intros a ? f ? g ? P. split. apply _. intros x ?. mor_prem_tac.
    apply (ball_closed _ _ _). intros d ?. destruct (P d _) as [_ Q]. exact (Q _ _).
  Qed.

  Context `{Ball X}.

  Instance ufm_fun_msp : MetricSpace (A:=X ⇀ Y) (X ==> Y).
  Proof sub_metric_space (X:=(X ⇒ Y)).

  Instance iso_fun_msp : MetricSpace (A:=X ⇀ Y) (Isometry X Y).
  Proof sub_metric_space (X:=(X ⇒ Y)).

End fun_space.

Hint Extern 2 (MetricSpace (?X ⇒ ?Y)) => eapply @fun_msp : typeclass_instances.
Hint Extern 2 (MetricSpace (?X ==> ?Y)) => eapply @ufm_fun_msp : typeclass_instances.
Hint Extern 2 (MetricSpace (Isometry ?X ?Y)) => eapply @iso_fun_msp : typeclass_instances.

Lemma lift_compose_isometry_l `{MetricSpace (X:=X)} `{MetricSpace (X:=Y)} `{MetricSpace (X:=Z)}
  (f:Y ⇀ Z) `{!Isometry Y Z f} : Isometry (X==>Y) (X==>Z) (f ∘).
Proof. split; try apply _.
+ intros g h [[u1 u2]E]. red in u1,u2. red_sig. intros ?? E2.
  unfold_sigs. red_sig. unfold compose. now rewrite (E _ _ (X $ E2)).
+ intros q ? g u1 h u2. red in u1,u2. unfold compose.
  split; (intros [_ P]; split; [apply _|]); intros.
  rewrite <-(isometric f _ _ _). now apply P.
  rewrite   (isometric f _ _ _). now apply P.
Qed.
Hint Extern 2 (Isometry _ _ (_ ∘)) => eapply @lift_compose_isometry_l : typeclass_instances.

Lemma lift_compose_isometry_r `{MetricSpace (X:=X)} `{MetricSpace (X:=Y)} `{MetricSpace (X:=Z)}
  (f:X ⇀ Y) `{!Inverse f} `{!Surjective X Y f} `{!UniformlyContinuous X Y f}
: Isometry (Y==>Z) (X==>Z) (∘ f).
Proof. split. apply _. apply _.
+ intros g h [[u1 u2]E]. red in u1,u2. red_sig. intros ?? E2.
  unfold_sigs. red_sig. unfold compose.
  rewrite (_ $ E2). apply E. now red_sig.
+ intros q ? g u1 h u2. red in u1,u2. unfold compose.
  split; (intros [_ P]; split; [apply _|]); intros.
  exact (P _ _). rewrite <- (_ $ surjective_applied f x). exact (P _ _).
Qed.
Hint Extern 2 (Isometry _ _ (∘ _)) => eapply @lift_compose_isometry_r : typeclass_instances.
