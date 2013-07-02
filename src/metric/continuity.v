Require Import
  abstract_algebra interfaces.orders interfaces.metric_spaces
  theory.setoids theory.products theory.lattices theory.powerset orders.lattices orders.minmax
  orders.affinely_extended_field
  metric.metric_spaces metric.maps metric.products cauchy_completion metric.uniform_continuity
  stdlib_field.

Local Notation AQ := TheAERationals.A.
Local Notation Q := the_ae_rationals.
Local Notation "Q∞" := (aff_ext Q).
Local Notation Qfull := (aff_ext_full Q).

Section extended_domain.
  Context `{MetricSpace (X:=X)} `{MetricSpace (X:=X')}.
  Context g `{!Isometry X X' g}.

  Hint Extern 0 AmbientSpace => eexact X  : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact X' : typeclass_instances.

  Lemma ext_domain_ambient : (-(closure g⁺¹(∼ X))) = X'.
  Proof. now rewrite complement_ambient, (image_empty g), closure_empty, metric_complement_empty. Qed.

  Context D `{D ⊆ X} `{!MetricComplementStable D}.

  Notation D' := (-(closure g⁺¹(∼ D))) .

  Hint Extern 5 (_ ∊ X) => apply (_ : ∼D ⊆ X) : typeclass_instances.
  Hint Extern 5 (_ ∊ X') => apply (_ : ∼D' ⊆ X') : typeclass_instances.

  Instance: Open D := metric_complement_stable_open _.

  Instance ext_domain_contains_image_comp : g⁺¹(∼D) ⊆ ∼D'.
  Proof. transitivity (closure g⁺¹(∼ D)); apply _. Qed.

  (*Instance : g⁺¹(∼D) ⊆ ∼g⁺¹(D).
  Proof. apply (subsetoid_from_subsetof X' _ _).
    intros x' [?[x[[? P]E]]]. split. apply _.
    intros y' [?[y[? E2]]].
    destruct (P y _) as [q[??]]. exists_sub q.
    now rewrite <-(_ $ E), <-(_ $ E2), <-(isometric g _ _ _).
  Qed.*)

  Instance ext_domain_contains_image : g⁺¹(D) ⊆ D'.
  Proof.
    apply (subsetoid_from_subsetof X' _ _).
    intros x' [?[x [? Ex]]]. pose proof _ : D ⊆ X. rewrite <-(X' $ Ex). clear dependent x'.
    split. apply _.
    destruct (open D x) as [q[? Bx]]. exists_sub (q/2).
    intros s [? P].
    destruct (ae_decompose_pos q) as [Eq|?].
      destruct (P ∞ _) as [s'[[?[x'[??]]] _]].
      assert (x' ∊ D). rewrite <- Bx. split; [| apply _]. red.
        rewrite (_ $ Eq). exact (msp_ball_inf _ _).
      destruct (complement_contradiction D x').
    destruct (P (q/2) _) as [? [[?[s'[? Es']]] Bs']].
    rewrite <-(_ $ Es') in Bs'. intro Bs.
    pose proof ball_triangle _ _ _ _ _ Bs Bs' as Bxs.
    mc_replace (q/2+q/2) with q on Q in Bxs by subfield Q.
    rewrite <-(isometric g _ _ _) in Bxs.
    assert (s' ∊ D). rewrite <- Bx. apply _.
    exact (complement_contradiction D s').
  Qed.

  Lemma ext_domain_exact_image x `{x ∊ X} `{g x ∊ D'} : x ∊ D.
  Proof. rewrite <-(metric_complement_stable D). split. apply _.
    destruct (open D' (g x) ) as [q[? Bx]].
    exists_sub q. intros s ? Bxs.
    rewrite (isometric g _ _ _) in Bxs.
    assert (g s ∊ D'). rewrite <-Bx. apply _.
    assert (g s ∊ closure g⁺¹(∼ D)). split. apply _. intros. now exists_sub (g s).
    exact (metric_complement_contradiction (closure g⁺¹(∼ D)) (g s)).
  Qed.

  Instance ext_domain_dense_image `{!Dense (X:=X') g⁺¹(X)} : Dense (X:=D') g⁺¹(D).
  Proof. split. exact sub_metric_space. apply _. intro x. split. now intros [??].
    intros ?. split. apply _. intros ε ?.
    destruct (open D' x) as [q[? Bx]].
    ae_rat_set_min a ε q E1 E2.
    assert (x ∊ X') by now apply (_ : D' ⊆ X').
    destruct (dense_image g X x a) as [x'[? Bx']].
    assert (g x' ∊ D'). rewrite <-Bx, <-(Q∞ $ E2). apply _.
    pose proof ext_domain_exact_image x'.
    exists_sub (g x'). now rewrite <-(Q∞ $ E1).
  Qed.
End extended_domain.

Section subdomain.
  Context `{MetricSpace (X:=X)}.

  Hint Extern 0 AmbientSpace => eexact X  : typeclass_instances.

  Context D `{D ⊆ X} `{!MetricComplementStable D}.

  Context  `{MetricSpace (X:=X')} g `{!Isometry X X' g} `{!Dense (X:=X') g⁺¹(X)}.
  Hint Extern 0 AmbientSpace => eexact X' : typeclass_instances.

  Notation D' := (-(closure g⁺¹(∼ D))) .

  Existing Instance ext_domain_dense_image.

  Hint Extern 5 (_ ∊ X) => apply (_ : ∼D ⊆ X) : typeclass_instances.
  Hint Extern 5 (_ ∊ X') => apply (_ : D' ⊆ X') : typeclass_instances.
  Hint Extern 6 (_ ∊ X') => apply (_ : ∼D' ⊆ X') : typeclass_instances.

  Definition shrink q : Subset := X ⊓ (λ y, ∀ z `{z ∊ ∼D'}, ¬ ball q (g y) z).

  Instance shrink_subsetoid q `{q ∊ Q₊} : shrink q ⊆ D.
  Proof. apply subsetoid_alt. apply _.
  + intros ?? E [_ P]. unfold_sigs. split. apply _. intros z ?.
      rewrite <-(X $ E). exact (P z _).
  + intros x [? P]. red in P. rewrite <-(metric_complement_stable D).
    split. trivial. exists_sub q.
    intros z ?. pose proof ext_domain_contains_image_comp g D.
    rewrite (isometric g _ _ _). apply P. apply _.
  Qed.

  Instance shrink_subsetoid2 q `{q ∊ Q₊} : shrink q ⊆ X.
  Proof. transitivity D; apply _. Qed.

  Definition cont_subdom x r q := B r x ⊓ shrink q.

  Instance cont_subdom_subsetoid x `{x ∊ X} r `{r ∊ Q⁺} q `{q ∊ Q₊} : cont_subdom x r q ⊆ X.
  Proof. unfold cont_subdom. apply _. Qed.

  Instance cont_subdom_wc x `{x ∊ D} r `{r ∊ Q⁺} q `{q ∊ Q₊} `{x ∊ shrink q}
    : cont_subdom x r q ⊂⊂ D.
  Proof. apply (well_contained_stable _ _).
  + unfold cont_subdom. rewrite (_ : B r x ⊓ shrink q ⊆ B r x). apply _.
  + exists x. split; apply _.
  + exists_sub q. intros ? [_ [? P]] z ?. red in P.
    pose proof ext_domain_contains_image_comp g D.
    rewrite (isometric g _ _ _). apply P. apply _.
  Qed.

  Instance cont_subdom_im_wc x `{x ∊ D} r `{r ∊ Q⁺} q `{q ∊ Q₊} `{x ∊ shrink q}
    : g⁺¹(cont_subdom x r q) ⊂⊂ D'.
  Proof. apply (well_contained_stable _ _).
  + eapply @strongly_ufm_cont; apply _.
  + apply _.
  + exists_sub q. intros u' [?[u [[?[? P]] E]]] z ?.
    rewrite <-(_ $ E). now apply P.
  Qed.

  Lemma proj_subdom_aux U' `{U' ⊆ D'} q `{q ∊ Q₊} x' `{x' ∊ U'} s `{s ∊ D}
    : set_separated q U' (∼D') → ball (q / 2) x' (g s) → s ∊ shrink (q / 2).
  Proof. intros HS ?. split. apply _. intros z ??.
      destruct (HS x' _ z _).
      mc_replace q with (q/2+q/2) on Q by subfield Q.
      apply (ball_triangle _ _ _ (g s) _); trivial.
  Qed.

  Lemma proj_subdom U' `{U' ⊂⊂ D'} : ∃ U, U ⊂⊂ D ∧ closure g⁺¹(U) ⊂⊂ D' ∧ g⁻¹(U') ⊆ U ∧ U' ⊆ closure g⁺¹(U).
  Proof. pose proof _ : U' ⊆ D'.
    destruct (inhabited U') as [x' ?].
    destruct (bounded U') as [d [? HB]].
    destruct (set_apart_finite U' (∼D')) as [q [? HS]].
    destruct (dense g⁺¹(D) (X:=D') x' (q/2)) as [s' [[?[s[? Es]]] Bxs]].
      rewrite <-(X' $ Es) in Bxs. clear dependent s'.
    assert (s ∊ shrink (q / 2)) by now apply (proj_subdom_aux U' q x' _).
    exists (cont_subdom s (q/2+d+q/2) (q/2)). intuition.
    + apply _.
    + apply (well_contained_closure _ _).
    + apply (subsetoid_from_subsetof X _ _). intros u [??]. split.
      split; trivial. red. rewrite (isometric g _ _ _). subsymmetry.
        apply (ball_triangle _ _ _ x' _); trivial.
        rewrite (_ $ commutativity (+) _ _). apply (ball_weaken_plus); try apply _.
        now apply HB.
      split; trivial. intros z ? B. destruct (HS (g u) _ z _).
        mc_replace q with (q/2+q/2) on Q by subfield Q.
        apply (ball_weaken_plus); try apply _. trivial.
    + apply (subsetoid_from_subsetof X' _ _).
      intros y' ?. split. apply _. intros ε ?.
      ae_rat_set_min p ε (q/2) Ea Eb.  pose proof (ae_pos_finite_bound _ _ Eb).
      destruct (dense g⁺¹(D) (X:=D') y' p) as [t' [[?[t[? Et]]] Byt]].
        rewrite <-(X' $ Et) in Byt. clear dependent t'.
      cut (t ∊ cont_subdom s (q/2+d+q/2) (q/2)). intro. exists_sub (g t). now rewrite <-(_ $ Ea).
      split.
      * split; [red | apply _].
        rewrite (isometric g _ _ _).
        apply (ball_triangle _ _ _ y' _).
        apply (ball_triangle _ _ _ x' _); [subsymmetry|].
        now apply HB. now rewrite <-(_ $ Eb).
      * apply (proj_subdom_aux U' q y' _). trivial. now rewrite <-(_ $ Eb).
  Qed.

  Lemma proj_subdom_point x' `{x' ∊ D'} : ∃ U, U ⊂⊂ D ∧ closure g⁺¹(U) ⊂⊂ D'
     ∧ (∀ x, x ∊ X → g x = x' → x ∊ U) ∧ x' ∊ closure g⁺¹(U).
  Proof.
    cut (∃ U', U' ⊂⊂ D' ∧ x' ∊ U').
      intros [U' [??]]. destruct (proj_subdom U') as [U [?[?[??]]]].
      exists U. split.  apply _. split. apply _. split.
        intros x ? E. apply (_ : g⁻¹(U') ⊆ U). split. apply _. now rewrite (X' $ E).
        apply _.
    assert (x' ∊ -∼D') as E by now rewrite (metric_complement_stable D').
    destruct E as [? [q [? P]]].
    exists (B 0 x'). split; [| apply _].
    assert (∀ y', y' ∊ B 0 x' → (X',=)%signature x' y') as E.
      intros y' [E ?]. red in E. rewrite (ball_separated x' y') in E. now red_sig.
    apply well_contained_alt; try apply _.
    * apply (subsetoid_from_subsetof X' _ _). intros y' ?. now rewrite <-(E y' _).
    * exists_sub q. intros y' ? z ?. rewrite <-(E y' _). now apply P.
  Qed.

  Context U `{U ⊂⊂ D}.
  Notation U' := (closure g⁺¹(U)).
  Notation g' := (g: U ⇀ U').

  Hint Extern 10 (MetricSpace _) => eapply @sub_metric_space : typeclass_instances.

  Instance restrict_g_iso: Isometry U U' g'.
  Proof. split; try apply _.
  + rewrite <-(_ : SubsetOf (U ⇒ g⁺¹(U)) (U ⇒ U')). apply _.
  + intros. pose proof _ : U ⊆ X. exact (isometric g _ _ _).
  Qed.

  Lemma restrict_g_image : g'⁺¹(U) = g⁺¹(U).
  Proof.
    rewrite <-(image_dom_range_proper (Y:=g⁺¹(U)) g U U' U).
    apply (subimage_image _).
  Qed.

  Instance restrict_g_dense: Dense (X:=U') g'⁺¹(U).
  Proof. rewrite restrict_g_image.
    split; try apply _. intros y.
    pose proof _ : U' ⊆ X'. split.
    + intros [??]. split. apply _. trivial.
    + intro el. split. apply _. now destruct el.
  Qed.

End subdomain.

Section continuous_extension.
  Context `{MetricSpace (X:=X)} `{MetricSpace (X:=X')}.
  Context `{MetricSpace (X:=Y)} `{CompleteMetricSpace (X:=Y')}.
  Context g `{!Isometry X X' g} `{!Dense (X:=X') g⁺¹(X)}.
  Context h `{!Isometry Y Y' h}.

  Hint Extern 0 AmbientSpace => eexact X  : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact X' : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact Y : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact Y' : typeclass_instances.

  Context D `{D ⊆ X} `{!MetricComplementStable D}.
  Context R `{R ⊆ Y} `{!MetricComplementStable R}.
  Notation D' := (-(closure (X:=X') g⁺¹(∼D))) .
  Notation R' := (-(closure (X:=Y') h⁺¹(∼R))) .
  Instance: Setoid D' := subsetoid_a.
  Instance: Setoid R' := subsetoid_a.

  Hint Extern 10 (MetricSpace _) => eapply @sub_metric_space : typeclass_instances.

  Section subdomain.
    Context f `{!Continuous D R f}.

    Context U `{U ⊂⊂ D}.
    Notation U' := (closure (X:=X') g⁺¹(U)).
    Notation g' := (g: U ⇀ U').

    Notation V := f⁺¹(U).
    Notation V' := (closure (X:=Y') h⁺¹(V)).
    Notation h' := (h: V ⇀ V').

    Existing Instance restrict_g_iso.
    Existing Instance restrict_g_dense.

    Instance: UniformlyContinuous U R f := continuity_ufm _.
    Instance: f⁺¹(U) ⊂⊂ R := continuity_wc_range _.

    Instance : Limit V' := subspace_limit _.
    Instance : CompleteMetricSpace V' := complete_subspace _.

    Definition sub_ext := ufm_cont_extension g' h' (M:=U==>V) id f.
    Hint Unfold sub_ext : typeclass_instances.

    Instance: UniformlyContinuous U V f.
    Proof.
      pose proof restrict_ufm_cont_image (f:U⇀R) U.
      split; try apply _. exact (uniform_continuity_def U V).
    Qed.

    Lemma sub_ext_cont : UniformlyContinuous U' V' sub_ext.
    Proof ufm_cont_ext_cont g' h' (M:=U==>V) id f.
    Hint Extern 0 (UniformlyContinuous U' V' sub_ext) => eexact sub_ext_cont : typeclass_instances.

    Lemma sub_ext_mor : Morphism (U' ⇒ V') sub_ext.
    Proof uniform_cont_mor U' V'.

    Lemma sub_ext_extends x `{x ∊ U} : sub_ext (g x) = h (f x).
    Proof. now destruct ( ufm_cont_ext_extends_2 g' h' (M:=U==>V) id f x x (_: Proper (U,=) x) ). Qed. 

    Instance sub_range_wc : V' ⊂⊂ R' .
    Proof. apply (well_contained_stable _ _).
    + apply closure_bounded. apply (strongly_ufm_cont Y Y'); apply _.
    + apply _.
    + apply set_apart_closure_l; try apply _.
      destruct (set_apart V (∼R)) as [q[? P]].
      exists_sub (q/3).
      intros u' [? [u[? Eu]]] v' ? Bu'v'.
      assert (u ∊ Y) by now apply (_ : V ⊆ Y).
      assert (v' ∊ Y') by now apply (_ : ∼R' ⊆ Y').
      cut (v' ∊ R'). intro. exact (complement_contradiction R' v').
      split. apply _. exists_sub (q/3).
      intros s' [? P'] ?.
      destruct (P' (q/3) _) as [t'[[?[t[? Et]]]?]].
      assert (t ∊ Y) by now apply (_ : ∼R ⊆ Y).
      destruct (ae_decompose_pos q) as [Eq|?].
        destruct (P u _ t _).
        apply (ball_weaken_le) with ∞; try apply _.
        exact (msp_ball_inf _ _). apply (eq_le (P:=Qfull) _ _). subsymmetry.
      destruct (P u _ t _).
      apply (ball_weaken_le) with (q/3+q/3+q/3); try apply _.
      rewrite (isometric h _ _ _), (Y' $ Eu), (Y' $ Et).
      apply (ball_triangle _ _ _ s' _); trivial.
      apply (ball_triangle _ _ _ v' _); trivial.
      apply (eq_le _ _). subfield Q.
    Qed.

    Instance sub_range_sub : V' ⊆ R' := _.

  End subdomain.

  Hint Extern 5 (UniformlyContinuous _ _ (sub_ext _ _)) => eapply @sub_ext_cont : typeclass_instances.
  Existing Instance sub_ext_mor.
  Existing Instance sub_range_sub.

  Hint Extern 5 (sub_ext ?f ?U _ ∊ R') => apply (_ : closure h⁺¹(f⁺¹(U)) ⊆ R');
    apply (morphism_closed (X:=closure (X:=X') g⁺¹(U)) _ _ _) : typeclass_instances.
  Hint Extern 5 (_ ∊ X') => apply (_ : D' ⊆ X') : typeclass_instances.
  Hint Extern 5 (_ ∊ Y') => apply (_ : R' ⊆ Y') : typeclass_instances.
  Hint Extern 5 (_ ∊ X) => apply (_ : D ⊆ X) : typeclass_instances.

  Lemma subext_proper_aux U `{U ⊆ X} x' `{x' ∊ closure g⁺¹(U)}
    d `{d ∊ Q} : (∀ x, x ∊ U → ∀ y, y ∊ U → ball d x y) → (∀ x `{x ∊ U}, ball d (g x) x').
  Proof. intro B. assert (x' ∊ X') by now apply (_ : closure g⁺¹(U) ⊆ X').
    intros y ?. apply (ball_closed _ _ _). intros ε ?.
    destruct (dense g⁺¹(U) (X:=closure g⁺¹(U)) x' ε) as [z' [[?[z[? E]]]Bxz]].
    rewrite <-(_ $ E) in Bxz. clear dependent z'.
    apply (ball_triangle _ _ _ (g z) _); [| subsymmetry].
    rewrite <-(isometric g _ _ _). now apply B.
  Qed.

  Hint Extern 2 (_ _ ∊ R) => apply (morphism_closed (X:=D)); apply _ : typeclass_instances.

  Hint Extern 2 (Setoid (closure (X:=X') g⁺¹(_))) => apply subsetoid_a : typeclass_instances.

  Section subext_proper.
    Context f `{!Continuous D R f}.
    Context U1 `{U1 ⊂⊂ D} U2 `{U2 ⊂⊂ D}.
    Notation U1' := (closure (X:=X') g⁺¹(U1)).
    Notation U2' := (closure (X:=X') g⁺¹(U2)).
    
    Notation U := (@join _ subset_union U1 U2).

    Notation U' := (closure (X:=X') g⁺¹(U1) ⊓ closure (X:=X') g⁺¹(U2)).
    Instance : Setoid U' := subsetoid_a.

    Instance: UniformlyContinuous U1 R f := continuity_ufm _.
    Instance: UniformlyContinuous U2 R f := continuity_ufm _.
    Instance: f⁺¹(U1) ⊂⊂ R := continuity_wc_range _.
    Instance: f⁺¹(U2) ⊂⊂ R := continuity_wc_range _.

    Hint Extern 5 (_ ∊ D) => apply (_ : U1 ⊆ D) : typeclass_instances.
    Hint Extern 5 (_ ∊ D) => apply (_ : U2 ⊆ D) : typeclass_instances.

    Instance subext_union_bounded `{!Inhabited U'} : Bounded U.
      destruct (inhabited U') as [x[??]].
      assert (x ∊ X') by now  apply (_ :  U1' ⊆ X').
      destruct (bounded U1) as [d1 [eld1 B1]].
      destruct (bounded U2) as [d2 [eld2 B2]].
      pose proof subext_proper_aux U1 x d1 B1 as P1.
      pose proof subext_proper_aux U2 x d2 B2 as P2.
      split; try apply _. exists_sub (d1+d2).
      intros y1 [?|?] y2 [?|?].
      apply (ball_weaken_plus _ _ _). now apply B1. apply _.
      rewrite (isometric g _ _ _). apply (ball_triangle _ _ _ x _). now apply P1. subsymmetry. now apply P2.
      subsymmetry. rewrite (isometric g _ _ _). apply (ball_triangle _ _ _ x _). now apply P1. subsymmetry. now apply P2.
      rewrite (_ $ commutativity (+) _ _). apply (ball_weaken_plus _ _ _). now apply B2. apply _.
    Qed.

    Instance subext_union_wc `{!Inhabited U'} : U ⊂⊂ D.
    Proof well_contained_union _ _ _.

    Instance: Inhabited U' → UniformlyContinuous U R f := λ _, continuity_ufm _.
    Instance: Inhabited U' → f⁺¹(U) ⊂⊂ R := λ _, continuity_wc_range _.

    Lemma subext_proper : (sub_ext f U1 : U' ⇀ Y') = (sub_ext f U2 : U' ⇀ Y').
    Proof. intros y x [[[??][??]]E]. unfold_sigs. red_sig.
      subtransitivity (sub_ext f U1 x). now destruct ((_ : Morphism _ (sub_ext f U1)) _ _ (U1' $ E)).
      clear dependent y.
      assert (x ∊ X') by now  apply (_ :  U1' ⊆ X').
      assert (Inhabited U') by (exists x; apply _).
      apply (equal_by_ball_closed _ _). intros ε ?.
      destruct (uniform_continuity (sub_ext f U1) (ε/3)) as [δ₁ [el1 C1]].
      destruct (uniform_continuity (sub_ext f U2) (ε/3)) as [δ₂ [el2 C2]].
      destruct (uniform_continuity (f : U ⇀ R) (ε/3)) as [δ [el3 Cf]].
      mc_replace ε with (ε/3+ε/3+ε/3) on Q by subfield Q.
      pose proof _ : δ/2 ∊ Q∞₊.
      ae_rat_set_min a δ₁ (δ/2) Ea1 Ea2.
      ae_rat_set_min b δ₂ (δ/2) Eb1 Eb2.
      destruct (dense g⁺¹(U1) (X:=U1') x a) as [y' [[?[y[? E]]]Bxy]]. rewrite <-(_ $ E) in Bxy. clear dependent y'.
      destruct (dense g⁺¹(U2) (X:=U2') x b) as [z' [[?[z[? E]]]Bxz]]. rewrite <-(_ $ E) in Bxz. clear dependent z'.
      apply (ball_triangle _ _ _ (h (f z)) _).
      apply (ball_triangle _ _ _ (h (f y)) _).
      * rewrite <-(Y' $ sub_ext_extends f U1 y). apply (C1 _ _ _ _). now rewrite <-(Qfull $ Ea1).
      * rewrite <-(isometric h _ _ _). apply (Cf _ _ _ _).
        apply (ball_weaken_le) with (δ/2 + δ/2); try apply _.
        rewrite (isometric g _ _ _). apply (ball_triangle _ _ _ x _). subsymmetry.
        now rewrite <-(Qfull $ Ea2). now rewrite <-(Qfull $ Eb2).
        apply (eq_le (P:=Qfull) _ _). exact (ae_in_halves _).
      * rewrite <-(Y' $ sub_ext_extends f U2 z). apply (C2 _ _ _ _). subsymmetry. now rewrite <-(Qfull $ Eb1).
    Qed.

    Lemma subext_proper_point x `{x ∊ U1'} `{x ∊ U2'} : sub_ext f U1 x = sub_ext f U2 x.
    Proof. now destruct ( subext_proper _ _ (_ : Proper (U',=) x) ). Qed.
  End subext_proper.

  Section def.
    Context f `{!Continuous D R f}.

    Notation C := (CauchyNets Y').

    Definition cont_ext_net : D' ⇀ C := λ x, net (λ _ y,
      y ∊ R' ∧ ∀ `{U ⊂⊂ D}, x ∊ closure g⁺¹(U) → y = sub_ext f U x
    ).

    Notation S := cont_ext_net.

    Instance: ∀ x `{x ∊ D'} q, S x q ⊆ R'.
    Proof with intuition. intros. apply subsetoid_alt. apply subsetoid_a.
    + intros y1 y2 Ey [? P]... split... now rewrite <-Ey.
      pose proof (_ : R' ⊆ Y'). rewrite <-Ey. now apply P.
    + now intros ?[??].
    Qed.

    Instance: ∀ x `{x ∊ D'} q, S x q ⊆ Y'.
    Proof. intros. transitivity R'; apply _. Qed.

    Instance: ∀ x `{x ∊ D'} q, Setoid (S x q).
    Proof. intros. exact (subsetoid_a (T:=R')). Qed.

    Lemma cont_ext_net_proper_1 x `{x ∊ D'} p q : ∀ `{y ∊ S x p}, y ∊ S x q.
    Proof. tauto. Qed.

    Lemma cont_ext_net_proper_2 x₁ `{x₁ ∊ D'} x₂ `{x₂ ∊ D'} : x₁ = x₂  →
      S x₁ = S x₂.
    Proof. intro E.
      intros q₁ ? q₂ ? y₁ [? P₁].
      intros           y₂ [? P₂].
      destruct (proj_subdom_point D g x₁) as [U[?[?[??]]]].
      assert (x₂ ∊ closure g⁺¹(U)) by now rewrite <-(D' $ E).
      rewrite (Y' $ P₁ U _ _), (Y' $ P₂ U _ _).
      destruct ( sub_ext_mor f U _ _ (closure g⁺¹(U) $ E) ) as [_ E'].
      now rewrite (Y' $ E').
    Qed.

    Instance: ∀ x `{x ∊ D'}, S x ∊ C.
    Proof. intros. split. apply _.
    + intros ?? E. unfold_sigs. red_sig.
      split; apply cont_ext_net_proper_1; trivial; try apply _.
    + intros q ?.
      destruct (proj_subdom_point D g x) as [U[?[?[??]]]].
      exists (sub_ext f U x). split. apply _.
      intros U2 ? ?. now apply subext_proper_point.
    + now apply cont_ext_net_proper_2.
    Qed.

    Instance cont_ext_net_mor : Morphism (D' ⇒ C) S.
    Proof. intros ???. unfold_sigs. red_sig. now apply cont_ext_net_proper_2. Qed.

  End def.

  Definition continuous_extension : (D --> R) ⇀ (D' --> R') := λ f, limit ∘ (cont_ext_net f).

  Section continuity.
    Context f `{!Continuous D R f}.

    Notation f' := (continuous_extension f).

    Existing Instance cont_ext_net_mor.

    Section patch.
      Context U `{U ⊂⊂ D}.
      Notation U' := (closure (X:=X') g⁺¹(U)).
      Context `{U' ⊂⊂ D'}.

      Hint Extern 5 (_ ∊ D') => apply (_ : U' ⊆ D') : typeclass_instances.
 
      Lemma cont_ext_patch : (f' : U' ⇀ Y') = (sub_ext f U : U' ⇀ Y').
      Proof. intros ?? E. unfold_sigs. unfold continuous_extension. red_sig.
        unfold compose. apply limit_const.
        apply (morphism_closed _ (m:=cont_ext_net_mor f) _ _). apply _.
        intros q ?. split. apply _.
        intros U2 ? ?. subsymmetry in E.
        assert (y ∊ closure g⁺¹(U2)) by now rewrite (_ $ E).
        now destruct (subext_proper f U U2 _ _ (U' ⊓ closure (X:=X') g⁺¹(U2) $ E)).
      Qed.
    End patch.

    Instance cont_ext_mor: Morphism (D' ⇒ R') f'.
    Proof. intros x y E. unfold_sigs.
      destruct (proj_subdom_point D g x) as [U[?[?[??]]]].
      assert (y ∊ closure g⁺¹(U)) by now rewrite <-(D' $ E).
      assert (∀ z, z ∊ closure g⁺¹(U) -> f' z ∊ R').
        intros. rewrite (cont_ext_patch U _ _ (_ : Proper (closure g⁺¹(U),=) z)). apply _.
      red_sig.
      rewrite (cont_ext_patch U _ _ (closure g⁺¹(U) $ E)).
      now rewrite (cont_ext_patch U _ _ (_ : Proper (closure g⁺¹(U),=) y)).
    Qed.

    Hint Extern 2 (f' _ ∊ R') => apply (morphism_closed _ (m:=cont_ext_mor)) : typeclass_instances.

    Lemma cont_ext_cont: Continuous D' R' f'.
    Proof. apply continuity_alt. apply _.
      intros U' ?. pose proof _ : U' ⊆ D'.
      destruct (proj_subdom D g U') as [U[?[?[??]]]]. pose proof _ : U ⊆ D.
      pose proof continuity_ufm (f:=f) U. pose proof continuity_wc_range (f:=f) U.
      split.
    + split; try apply _. rewrite <-(_ : SubsetOf (D' ⇒ R') (U' ⇒ R')). apply _.
      intros ε ?.
      destruct (uniform_continuity (sub_ext f U) ε) as [δ[el P]].
      exists_sub δ. intros x ? y ? ?.
      rewrite (cont_ext_patch U _ _ (_ : Proper (closure g⁺¹(U),=) x)).
      rewrite (cont_ext_patch U _ _ (_ : Proper (closure g⁺¹(U),=) y)).
      now apply (P x _ y _).
    + cut (f'⁺¹(U') ⊂⊂ R'). intuition; apply _.
      cut (f'⁺¹(U') ⊆ closure h⁺¹(f⁺¹(U))). intro E.
        rewrite (Inhabited $ E). exact (sub_range_wc f U).
      apply (subsetoid_from_subsetof Y'). transitivity R'; apply _. apply _.
      intros y [?[x[? E]]]. rewrite <-(_ $ E). clear dependent y.
      rewrite (cont_ext_patch U _ _ (_ : Proper (closure g⁺¹(U),=) x)).
      apply (morphism_closed _ (m:=sub_ext_mor f U) _ _).
    Qed.

    Lemma cont_ext_extends : f' ∘ (g:D⇀D') = h ∘ f.
    Proof. intros x y E. unfold compose. unfold_sigs.
      pose proof ext_domain_contains_image g D.
      pose proof ext_domain_contains_image h R.
      red_sig.
      destruct (proj_subdom_point D g (g x)) as [U[?[?[P ?]]]]; pose proof _ : U ⊆ D.
      assert (g x = g y) as E2 by now rewrite (X $ E).
      assert (g y ∊ closure g⁺¹(U)) by now rewrite <-(_ $ E2).
      rewrite (cont_ext_patch U _ _ (closure g⁺¹(U) $ E2)).
      assert (y ∊ U). apply (P _ _). subsymmetry.
      exact (sub_ext_extends f U y).
    Qed.

  End continuity.

End continuous_extension.

Hint Extern 2 (Morphism _ (continuous_extension _ _ _ _ _)) => eapply @cont_ext_mor : typeclass_instances.
Hint Extern 2 (Continuous _ _ (continuous_extension _ _ _ _ _)) => eapply @cont_ext_cont : typeclass_instances.

Section continuous_equal_on_dense.
  Context `{MetricSpace (X:=X)} `{MetricSpace (X:=Y)}.

  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact Y : typeclass_instances.

  Context {D R} f `{!Continuous (X:=X) (Y:=Y) D R f}.
  Context g `{!Continuous D R g}.

  Context C `{!Dense (X:=D) C}.

  Hint Extern 5 (_ ∊ X) => apply (_ : D ⊆ X) : typeclass_instances.
  Hint Extern 6 (_ ∊ X) => apply (_ : ∼D ⊆ X) : typeclass_instances.

  Instance: C ⊆ X.    Proof. transitivity D; apply _. Qed.
  Hint Extern 6 (_ ∊ D) => apply (_ : C ⊆ D) : typeclass_instances.

  Section patch.
    Context x `{x ∊ D}.

    Let finite_ball : ∃ `{q ∊ Q₊}, ∀ s, s ∊ ∼D → ¬ball q x s.
    Proof.
      pose proof _ : x ∊ D as E. rewrite <-(metric_complement_stable D) in E.
      destruct E as [?[q[? P]]]. (* x is distance q from the boundary *)
      destruct (ae_decompose_pos q) as [Eq|?].
        exists_sub 1. intros s ?. destruct (P s _).
        rewrite (_ $ Eq). exact (msp_ball_inf _ _).
      now exists_sub q.
    Qed.

    Lemma cont_patch : ∃ U, U ⊂⊂ D ∧ x ∊ U ∧ Dense (X:=U) (C ⊓ U).
    Proof.
      destruct finite_ball as [q[? P]]. (* x is distance q from the boundary *)
      assert (x ∊ (B (q / 2) x)°).
        split. apply _. exists_sub (q/2). apply _.
      assert ((B (q / 2) x)° ⊂⊂ D).
        apply (well_contained_stable _ _).
          rewrite (_ : (B (q / 2) x)° ⊆ (B (q / 2) x)). apply _.
          exists x. apply _.
          rewrite (_ : (B (q / 2) x)° ⊆ (B (q / 2) x)).
          exists_sub (q/2). intros y [??] z ??.
          destruct (P z _). mc_replace q with (q/2+q/2) on Q by subfield Q.
          now apply (ball_triangle _ _ _ y _ ).
      exists (interior (B (q/2) x) ). do 3 (split; trivial).
      * exact sub_metric_space.
      * apply (subsetoid_from_subsetof X _ _). firstorder.
      * intro y. split. firstorder. intro. split; trivial.
        pose proof _ : y ∊ (B (q / 2) x)° as E. destruct E as [?[r[? S]]].
        assert (y ∊ D) by now apply ( _ : (B (q / 2) x)° ⊆ D).
        intros ε ?. pose proof _ : r/2 ∊ Q∞₊ . ae_rat_set_min a ε (r/2) E1 E2.
        destruct (dense (X:=D) C y a) as [s[??]].
        assert (s ∊ (B (q / 2) x)°). split.
            apply S. split; [|apply _]. red.
            apply (ball_weaken_le) with (r/2+r/2); try apply _.
              apply (ball_weaken_plus); try apply _.
              now rewrite <-(Qfull $ E2).
            apply (eq_le (P:=Qfull) _ _). exact (ae_in_halves _).
          exists_sub (r/2). transitivity (B r y); trivial.
          intros z [??]. split; [| apply _]. red.
          apply (ball_weaken_le) with (r/2+r/2); try apply _.
            apply (ball_triangle _ _ _ s _ ); trivial. now rewrite <-(Qfull $ E2).
          apply (eq_le (P:=Qfull) _ _). exact (ae_in_halves _).
        exists_sub s. now rewrite <-(Qfull $ E1).
    Qed.
  End patch.

  Hint Extern 10 (MetricSpace _) => eapply @sub_metric_space : typeclass_instances.


  Lemma cont_equal_on_dense : (f:C ⇀ R) = (g:C ⇀ R) ↔ f = g.
  Proof. split.
  + intros E x y Ex. unfold_sigs. red_sig.
    rewrite <- ( (_ : Morphism _ g) _ _ (D $ Ex) ). clear dependent y.
    destruct (cont_patch x) as [U[?[??]]].
    pose proof (continuity_ufm (f:=f) U).
    pose proof (continuity_ufm (f:=g) U).
    cut ((f:U ⇀ R) = (g:U ⇀ R)). intros EU. apply EU. now red_sig.
    apply (ufm_cont_equal_on_dense (f:U ⇀ R) (g:U ⇀ R) (C ⊓ U)).
    intros y1 y2 [[[??][??]]Ey]. red_sig. apply E. now red_sig.
  + intros E x y Ex. unfold_sigs. red_sig. apply E. now red_sig.
  Qed.

End continuous_equal_on_dense.

Section continuous_equal_on_dense_image.
  Context `{Continuous (X:=X) (Y:=Y) (D:=D) (R:=R) (f:=f)}.
  Context g `{!Continuous (X:=X) (Y:=Y) D R g}.

  Instance: MetricSpace X.   Proof. now destruct (_ : (D --> R)%subset f ). Qed.
  Instance: MetricSpace Y.   Proof. now destruct (_ : (D --> R)%subset f ). Qed.

  Context `{Setoid (S:=C)} (k:C ⇀ D) `{!Morphism (C ⇒ D) k} `{!Dense (X:=D) k⁺¹(C)}.

  Lemma cont_equal_on_dense_image : f ∘ k = g ∘ k ↔ f = g.
  Proof. transitivity ((f:k⁺¹(C) ⇀ R) = (g:k⁺¹(C) ⇀ R)) .
  + unfold compose. split.
    * intros Ef ?? [[[?[x' [? E2]]][??]]E]. red_sig.
      rewrite <-(D $ E), <-(D $ E2).
      now destruct (Ef _ _ (_ : Proper (C,=) x')).
    * intros Ef ?? E. unfold_sigs. red_sig.
      assert (k x = k y) as E' by now rewrite <-(C $ E).
      now destruct (Ef _ _ (k⁺¹(C) $ E')).
  + exact (cont_equal_on_dense f g _).
  Qed.

  Lemma cont_equal_on_dense_image_applied : (∀ `{x ∊ C}, f (k x) = g (k x)) → f = g.
  Proof. intro P.
    apply cont_equal_on_dense_image.
    intros ?? E. unfold_sigs. red_sig. unfold compose.
    rewrite <-(C $ E). exact (P _ _).
  Qed.

End continuous_equal_on_dense_image.

Arguments cont_equal_on_dense_image {_ _ _ _ _ _ _ _ _ _} f {_} g {_} {_ _ C _} k {_ _}.
Arguments cont_equal_on_dense_image_applied {_ _ _ _ _ _ _ _ _ _} f {_} g {_} {_ _ C _} k {_ _} _ _ _ _.
