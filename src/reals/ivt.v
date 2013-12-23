Require Import
  abstract_algebra interfaces.orders interfaces.metric_spaces
  interfaces.archimedean_fields interfaces.reals
  theory.setoids theory.products theory.fields theory.lattices
  orders.maps orders.fields orders.lattices orders.abs orders.reals
  metric.metric_spaces metric.maps metric.products metric.archimedean_fields
  cauchy_completion metric.complete metric.distance
  metric.real_families
  metric.bisection
  reals.intervals
  stdlib_ring stdlib_field.

Local Open Scope grp_scope.
Local Open Scope mc_abs_scope.

Section monotonic_root.
  Context `{Reals (R:=R)}.
  Hint Extern 0 TheReals => eexact R : typeclass_instances.
  Add Ring R : (stdlib_ring_theory R).
  Add Field R' : (stdlib_field_theory R).

  Context (f:R ⇀ R) `{!StrictlyOrderPreserving R R f}.

  Instance: Morphism (R ⇒ R) f.
  Proof. now destruct (_ : StrictOrder_Morphism R R f). Qed.

  Notation C := (RealCauchyFamilies R).

  Definition monotonic_root_family := real_family (λ ε x,
    x ∊ R ∧ (f (x - ε) ≤ 0 ≤ f (x + ε))).

  Notation S := monotonic_root_family.

  Instance: ∀ ε `{ε ∊ R₊}, S ε ⊆ R.
  Proof. intros. apply subsetoid_alt. apply _.
  + intros x y E [??]; unfold_sigs; (split; [ apply _ |]). now rewrite <-(R $ E).
  + now intros ? [??].
  Qed.

  Let mon_root_family_proper_1_aux
    ε₁ `{ε₁ ∊ R₊} ε₂ `{ε₂ ∊ R₊} : ε₁ = ε₂ → Subset (S ε₁) (S ε₂).
  Proof. intros E x [??]; (split; [ apply _ |]). now rewrite <-(R $ E). Qed.

  Lemma mon_root_family_proper_1
    ε₁ `{ε₁ ∊ R₊} ε₂ `{ε₂ ∊ R₊} : ε₁ = ε₂ → S ε₁ = S ε₂.
  Proof. intro E. apply antisymmetry_t with Subset; try apply _;
    apply (mon_root_family_proper_1_aux _ _); trivial; subsymmetry.
  Qed.

  Existing Instance full_pseudo_order_reflecting .

  Lemma mon_root_family_proper_2 : S = S.
  Proof.
    intros ε₁ ? ε₂ ? x₁ [? [Pl₁ Pr₁]].
    intros           x₂ [? [Pl₂ Pr₂]].
    change (|x₁ - x₂| ≤ ε₁ + ε₂). apply (abs_le_iff _ _). split.
    + apply (flip_le_minus_r _ _ _).
      mc_replace (- (ε₁ + ε₂) + x₂) with (x₂ -  ε₂ - ε₁) on R by setring R.
      apply (flip_le_minus_l _ _ _).
      apply (order_reflecting f _ _). subtransitivity 0.
    + apply (flip_le_minus_l _ _ _).
      mc_replace (ε₁ + ε₂ + x₂) with (x₂ + ε₂ + ε₁) on R by setring R.
      apply (flip_le_minus_l _ _ _).
      apply (order_reflecting f _ _). subtransitivity 0.
  Qed.

  Context a `{a ∊ R} b `{b ∊ R} (E:f a ≤ 0 ≤ f b).

  Let Eab : a ≤ b.
  Proof. apply (order_reflecting f _ _). now subtransitivity 0. Qed.

  Instance: b-a ∊ R⁺.
  Proof. now apply (flip_nonneg_minus _ _). Qed. 

  Section bisection.
    
    Let invar x δ := f x ≤ 0 ≤ f (x+δ). 

    Let bisect x `{x ∊ R} δ `{δ ∊ R₊} : invar x δ → ∃ `{x' ∊ R}, invar x' (2*δ/3) .
    Proof. intros [E1 E2].
      assert (x+δ/3 < x+2*δ/3) as Ex.
        apply (flip_pos_minus _ _).
        mc_replace (x + 2 * δ / 3 - (x + δ / 3)) with (δ/3) on R by setring R. apply _.
      apply (strictly_order_preserving f _ _) in Ex.
      destruct ( cotransitivity (x:=f (x+δ/3)) (y:=f (x+2*δ/3)) Ex 0 ) as [El|Er].
      + exists_sub (x+ δ/3). split. now apply (lt_le _ _).
        now mc_replace (x + δ/3 + (2*δ/3)) with (x + δ) on R by setfield R.
      + exists_sub x. split; trivial. now apply (lt_le _ _).
    Qed.

    Instance mon_root_family_inh ε `{ε ∊ R₊} : Inhabited (S ε).
    Proof.
      assert (invar a (b-a)) as P0. red.
        now mc_replace (a+(b-a)) with b on R by setring R.
      destruct (bisection R R invar bisect ε _ _ P0) as [x[?[δ[?[[Pl Pr]Eδ]]]]].
      rewrite (_ $ commutativity (.*.) _ _) in Eδ.
      apply (mult_inv_lt_cancel_l _ _ _) in Eδ.
      exists (x+δ/2). split. apply _. split.
      * subtransitivity (f x). apply (lt_le _ _).
        apply (strictly_order_preserving f _ _).
        apply (flip_lt_minus_l _ _ _).
        now apply (strictly_order_preserving (x+) _ _).
      * subtransitivity (f (x+δ)). apply (lt_le _ _).
        apply (strictly_order_preserving f _ _).
        rewrite <-(_ $ associativity (+) _ _ _).
        apply (strictly_order_preserving (x+) _ _).
        rewrite (_ $ commutativity (+) _ _).
        apply (flip_lt_minus_l _ _ _).
        now mc_replace (δ-δ/2) with (δ/2) on R by setfield R.
    Qed.
  End bisection.

  Existing Instance mon_root_family_inh.

  Instance: S ∊ C.
  Proof. split; try apply _.
  + intros ?? E'. unfold_sigs. red_sig.
    now apply mon_root_family_proper_1.
  + now apply mon_root_family_proper_2.
  Qed.

  Notation lim := (real_family_limit (R:=R) R).

  Definition monotonic_root := lim S.
  Notation x := monotonic_root.

  Instance monotonic_root_el : x ∊ R := _ : lim S ∊ R.

  Context `{!Ball R} `{!ArchimedeanField_Metric R}.
  Context `{!UniformlyContinuous R R f}.

  Lemma monotonic_root_eq : f x = 0.
  Proof. apply (eq_closed_alt _ _). intros ε ?. rewrite 2!(_ $ plus_0_l _).
    apply (abs_le_iff _ _).
    destruct (uniform_continuity_dist f ε) as [δ [elδ Cf]].
    destruct (inhabited (S (δ/4))) as [y ?].
    destruct (_ : y ∊ S (δ/4)) as [? [P1 P2]].
    assert (distance x y ≤ δ/4) as Exy.
      rewrite (_ $ metric_dist_sym _ _).
      exact (real_family_limit_spec S (δ/4) _ y _).
    assert (distance (y+δ/2) (y-δ/2) ≤ δ) as Ef.
      unfold distance, reals_distance.
      mc_replace ((y+δ/2)-(y-δ/2)) with δ on R by setfield R.
      now rewrite (_ $ abs_of_nonneg δ).
    apply (Cf _ _ _ _) in Ef.
    setoid_rewrite (abs_le_iff _ _) in Ef. destruct Ef as [_ Ef].
    subtransitivity (f (y + δ/2) - f (y - δ/2)). apply (lt_le _ _).
    apply (abs_lt_iff _ _).
    mc_replace (- (f (y + δ/2) - f (y - δ/2)) ) with (f (y - δ/2) - f (y + δ/2)) on R by setring R.
    mc_replace (f x) with (f x - 0) on R by setring R.
    assert (δ/4 < δ/2).
      rewrite <-(mult_inv_lt_cancel_both _ _ _ _).
      apply (flip_pos_minus _ _).
      mc_replace (4*δ-δ*2) with (2*δ) on R by setring R. apply _.
    apply (plus_lt_compat_2 _ _ _ _ _ _).
    + cut (-(δ/2) < x - y < δ/2). intros [??].
        split; apply (strictly_order_preserving f _ _);
        apply (strictly_order_reflecting (+ -y) _ _).
        now mc_replace (y-δ/2 - y) with (-(δ / 2)) on R by setring R.
        now mc_replace (y+δ/2 - y) with (  δ / 2 ) on R by setring R.
      apply (abs_lt_iff _ _). now apply (le_lt_trans _ (δ/4) _).
    + split; apply (flip_lt_negate _ _).
        apply (le_lt_trans _ (f (y + δ/4)) _); trivial.
        apply (strictly_order_preserving f _ _).
        now apply (strictly_order_preserving (y +) _ _).
      apply (lt_le_trans _ (f (y - δ/4)) _); trivial.
      apply (strictly_order_preserving f _ _).
      apply (strictly_order_preserving (y +) _ _).
      now apply (flip_lt_negate _ _).
  Qed.

End monotonic_root.


Local Notation "{[ a , b ]}" := (interval a b).

Section monotonic_root_interval.
  Context `{Reals (R:=R)} `{!Ball R} `{!ArchimedeanField_Metric R}.
  Hint Extern 0 TheReals => eexact R : typeclass_instances.
  Instance: FullLatticeOrder R := _.
  Add Ring R3 : (stdlib_ring_theory R).

  Context a `{a ∊ R} b `{b ∊ R} `{b-a ∊ R⁺}.

  Context (f:{[a, b]} ⇀ R) `{!StrictlyOrderPreserving {[a,b]} R f}.
  Context `{!UniformlyContinuous {[a,b]} R f}.

  Let Eab : a ≤ b.   Proof. now apply (flip_nonneg_minus _ _). Qed.

  Instance interval_strictly_increasing_increasing : OrderPreserving {[a,b]} R f.
  Proof. split. split; try apply _. rewrite (_ : Subset {[a,b]} R). apply _. intros x ? y ? E.
    apply (le_closed_alt _ _). intros ε ?.
    destruct (uniform_continuity_dist f ε) as [δ[? Cf]].
    destruct (_ : δ ∊ R₊) as [_ Eδ]. red in Eδ.
    pose proof _ : {[a,b]} ⊆ R.
    destruct (cotransitivity Eδ (y-x)) as [E'|E'].
      apply (plus_le_compat_r _ _ _). apply (lt_le _ _).
      apply (strictly_order_preserving (S:={[a,b]}) f _ _).
      apply (flip_pos_minus _ _). split; trivial; apply _.
    cut (|f x - f y|  ≤ ε). rewrite (abs_le_iff _ _). intros [_ ?].
      rewrite (_ $ commutativity (+) _ _).
      now apply (flip_le_minus_l _ _ _).
    apply (Cf _ _ _ _).
    rewrite (_ $ metric_dist_sym (X:={[a,b]}) _ _).
    setoid_rewrite (abs_le_iff _ _). split. 2: now apply (lt_le _ _).
    subtransitivity 0. apply (_ : -δ ∊ R⁻).
      apply (flip_le_minus_r _ _ _). now rewrite (_ $ plus_0_l _).
  Qed.

  Instance : FullPseudoOrder {[a,b]}.
  Proof. rewrite (_ : Subset {[a,b]} R). apply _. Qed.

  Instance : OrderReflecting {[a,b]} R f := full_pseudo_order_reflecting.

  Instance: ∀ x, x ∊ {[a,b]} → f x ∊ {[f a, f b]}.
  Proof. intros x ?. split. apply _.
    split; apply (order_preserving (S:={[a,b]}) f _ _);
    now destruct (_ : x ∊ {[a, b]}) as [_ [??]].
  Qed.

  Instance: Morphism ({[a,b]} ⇒ {[f a, f b]}) f.
  Proof. intros x y E. unfold_sigs. red_sig. now rewrite ({[a,b]} $ E). Qed.

  Definition monotonic_ext : R ⇀ R := λ x,
    ( (x-a) ⊓ 0 ) + f (clamp a b x) + ( 0 ⊔ (x-b) ).
  Notation g := monotonic_ext.

  Instance: ∀ x, x ∊ R → g x ∊ R .
  Proof. intros x ?. unfold g. apply _. Qed.
  Instance: Morphism (R ⇒ R) g.
  Proof. intros ?? E. unfold_sigs. red_sig. unfold g. now rewrite (R $ E). Qed.

  Lemma monotonic_ext_extends : (g : {[a,b]} ⇀ R) = f.
  Proof. intros x y E. unfold_sigs. pose proof _ : {[a,b]} ⊆ R. red_sig.
    rewrite <-({[a,b]} $ E). clear dependent E. unfold g.
    cut (x - a ⊓ 0 = 0 ∧ 0 ⊔ (x - b) = 0). intros [E1 E2].
      rewrite (R $ E1), (R $ E2).
      rewrite (clamp_in_range _ _ _ _ (_:Proper ({[a,b]},=) x)). unfold id.
      rewrite (_ $ plus_0_l _). exact (plus_0_r _).
    split.
    + apply (meet_r _ _). cut (x - a ∊ R⁺). now intros [??].
      rewrite (flip_nonneg_minus _ _). now destruct (_ : x ∊ {[a,b]}) as [?[??]].
    + apply (join_l _ _). cut (x - b ∊ R⁻). now intros [??].
      rewrite (flip_nonpos_minus _ _). now destruct (_ : x ∊ {[a,b]}) as [?[??]].
  Qed.


  Let meet_minus_0_r x `{x ∊ R} y `{y ∊ R} : y ≤ x → (x - y) ⊓ 0 = 0 .
  Proof. intro. apply (meet_r _ _). cut (x - y ∊ R⁺). now intros [??].
    now rewrite (flip_nonneg_minus _ _).
  Qed.

  Let join_0_minus_l x `{x ∊ R} y `{y ∊ R} : x ≤ y → 0 ⊔ (x - y) = 0 .
  Proof. intro. apply (join_l _ _). cut (x - y ∊ R⁻). now intros [??].
    now rewrite (flip_nonpos_minus _ _).
  Qed.

  Let aux1  x `{x ∊ R} y `{y ∊ R} : x < y → x < a → g x < g y.
  Proof. intros E Eax. apply (plus_lt_le_compat _ _ _ _). apply (plus_lt_le_compat _ _ _ _).
  * assert (x-a < 0) as Eax'. rewrite <-(flip_neg_minus _ _) in Eax. now destruct Eax.
    rewrite (_ $ meet_l _ _ (lt_le _ _ Eax')).
    apply (meet_lt _ _ _); trivial. now pose proof (strictly_order_preserving (+ -a) x y E).
  * apply (order_preserving (S:={[a,b]}) f _ _).
    unfold clamp. rewrite (_ $ join_l a x (lt_le _ _ Eax)), (_ $  meet_l a b Eab).
    apply (meet_glb _ _ _); trivial. exact (join_ub_l _ _).
  * cut (0 ⊔ (x - b) = 0). intro E'. rewrite (_ $ E'). now apply (join_ub_l _ _).
    apply (join_0_minus_l _ _). subtransitivity a. now apply (lt_le _ _).
  Qed.

  Let aux2  x `{x ∊ R} y `{y ∊ R} : x < y → b < y → g x < g y.
  Proof. intros E Eby. apply (plus_le_lt_compat _ _ _ _). apply (plus_le_compat _ _ _ _).
  * subtransitivity 0. now apply (meet_lb_r _ _). apply (eq_le _ _). subsymmetry.
    apply (meet_minus_0_r _ _). subtransitivity b. now apply (lt_le _ _).
  * apply (order_preserving (S:={[a,b]}) f _ _).
    unfold clamp. subtransitivity b. now apply (meet_lb_r _ _).
    apply (meet_glb _ _ _). 2:easy.
    subtransitivity y. now apply (lt_le _ _).
    apply (eq_le _ _). subsymmetry. apply (join_r _ _).
    subtransitivity b. now apply (lt_le _ _).
  * assert (0 < y-b ) as Eyb'. rewrite <-(flip_pos_minus _ _) in Eby. now destruct Eby.
    rewrite (_ $ join_r _ _ (lt_le _ _ Eyb')).
    apply (join_lt _ _ _); trivial. now pose proof (strictly_order_preserving (+ -b) _ _ E).
  Qed.

  Instance monotonic_ext_mono : StrictlyOrderPreserving R R g.
  Proof. split. split; apply _. intros x ? y ? E.
    destruct (cotransitivity E a) as [Eax|Eya]. now apply aux1.
    destruct (cotransitivity E b) as [Ebx|Eyb]. 2: now apply aux2.
    destruct (cotransitivity Ebx a) as [Eax|Eab']. now apply aux1.
    unfold g.
    apply (plus_lt_le_compat _ _ _ _). apply (plus_le_lt_compat _ _ _ _).
    * rewrite (_ $ meet_minus_0_r _ _ (lt_le _ _ Eya)). apply (meet_lb_r _ _).
    * apply (strictly_order_preserving (S:={[a,b]}) f _ _).
      unfold clamp.
      rewrite (_ $ join_r _ _ (lt_le _ _ Eya)).
      apply (le_lt_trans _ (a ⊔ x) _).
      apply (eq_le _ _). apply (meet_l _ _).
      apply (join_lub _ _ _); trivial. now apply (lt_le _ _).
      apply (meet_lt _ _ _); apply (join_lt _ _ _); trivial.
    * rewrite (_ $ join_0_minus_l x b (lt_le _ _ Ebx)). apply (join_ub_l _ _).
  Qed.

  Instance: OrderReflecting R R g := full_pseudo_order_reflecting.

  Instance: UniformlyContinuous R R g.
  Proof _ : UniformlyContinuous R R (
    uncurry (+) ∘ prod_map
        (uncurry (+) ∘ prod_map ((⊓ 0) ∘ (+ -a)) (f ∘ clamp a b) ∘ prod_diag)
        ((0 ⊔) ∘ (+ -b))
     ∘ prod_diag).

  Definition interval_monotonic_inverse : {[f a, f b]} ⇀ {[a, b]} := λ y, monotonic_root ((+ -y) ∘ g).
  Notation h := interval_monotonic_inverse.

  Section with_point.
    Context y `{y ∊ {[f a, f b]} }.

    Instance: y ∊ R.
    Proof. now apply (_ : {[f a, f b]} ⊆ R). Qed.

    Let Eg : g a - y ≤ 0 ≤ g b - y .
    Proof.
      split; apply (order_reflecting (+ y) _ _); rewrite (_ $ plus_0_l _).
      * subtransitivity (g a). apply (eq_le _ _). setring R.
        rewrite (monotonic_ext_extends _ _ (_ : Proper ({[a,b]},=) a)).
        now destruct (_:y ∊ {[f a, f b]}) as [?[??]].
      * subtransitivity (g b). 2: apply (eq_le _ _); setring R.
        rewrite (monotonic_ext_extends _ _ (_ : Proper ({[a,b]},=) b)).
        now destruct (_:y ∊ {[f a, f b]}) as [?[??]].
    Qed.

    Instance: h y ∊ R.
    Proof. apply (monotonic_root_el _ a b). exact Eg. Qed.

    Let aux : g (h y) = y.
    Proof. apply (equal_by_zero_sum _ _).
      change (((+ -y) ∘ g) (h y) = 0).
      eapply (monotonic_root_eq _ a b). exact Eg. apply _. apply _.
    Qed.

    Instance interval_monotonic_inverse_el: h y ∊ {[a, b]}.
    Proof. split. apply _. pose proof (plus_negate_r y) as E.
      split; apply (order_reflecting g _ _); rewrite (R $ aux);
      apply (order_reflecting (+ -y) _ _); rewrite (R $ E); now destruct Eg.
    Qed.

    Lemma interval_monotonic_inverse_applied : f (h y) = y.
    Proof. now rewrite <-(monotonic_ext_extends _ _ (_ : Proper ({[a,b]},=) (h y))). Qed.
  End with_point.

  Existing Instance interval_monotonic_inverse_el.

  Instance interval_monotonic_inverse_mor : Morphism ({[f a, f b]} ⇒ {[a, b]}) h.
  Proof. intros x y E. unfold_sigs. red_sig.
    pose proof _ : {[a, b]} ⊆ R.
    pose proof _ : {[f a, f b]} ⊆ R.
    pose proof _ : h x ∊ {[a, b]}.
    pose proof _ : h y ∊ {[a, b]}.
    apply (antisymmetry (S:=R) le _ _); apply (order_reflecting (S:={[a,b]}) f _ _);
    rewrite 2!(R $ interval_monotonic_inverse_applied _); now rewrite (_ $ E).
  Qed.

  Instance interval_monotonic_surjective : Surjective {[a,b]} {[f a, f b]} f (inv:=h).
  Proof. split; unfold inverse; try apply _.
    intros x y E. unfold_sigs. red_sig. unfold compose.
    pose proof _ : {[f a, f b]} ⊆ R. subtransitivity x.
    now apply interval_monotonic_inverse_applied.
  Qed.

  Instance interval_monotonic_inverse_reflecting : StrictlyOrderReflecting {[f a, f b]} {[a, b]} h.
  Proof. split. split; try apply _. rewrite (_ : Subset {[f a, f b]} R). apply _. intros x ? y ? E.
    pose proof _ : {[a, b]} ⊆ R.
    pose proof _ : {[f a, f b]} ⊆ R.
    rewrite <-(R $ interval_monotonic_inverse_applied x), <-(R $ interval_monotonic_inverse_applied y).
    now apply (strictly_order_preserving (S:={[a,b]}) f _ _).
  Qed.

End monotonic_root_interval.

Section monotonic.
  Context `{Reals (R:=R)} `{!Ball R} `{!ArchimedeanField_Metric R}.
  Hint Extern 0 TheReals => eexact R : typeclass_instances.
  Instance: FullLatticeOrder R := _.
  Add Ring R4 : (stdlib_ring_theory R).

  Context X `{!X ⊆ R} Y `{!Y ⊆ R}.
  Context {D C} (f:D ⇀ C) `{!Continuous (X:=X) (Y:=Y) D C f}.
  Context `{!StrictlyOrderPreserving D C f}.

  Instance: MetricSpace X := sub_metric_space.
  Instance: MetricSpace Y := sub_metric_space.

  Hint Extern 2 (Distance X) => eexact (reals_distance (R:=R)) : typeclass_instances.
  Hint Extern 2 (Distance Y) => eexact (reals_distance (R:=R)) : typeclass_instances.
  Hint Extern 2 (MetricDistance X) => eapply (@subspace_distance_correct _ R) : typeclass_instances.
  Hint Extern 2 (MetricDistance Y) => eapply (@subspace_distance_correct _ R) : typeclass_instances.

  Instance: D ⊆ R.  Proof. transitivity X; apply _. Qed.
  Instance: C ⊆ R.  Proof. transitivity Y; apply _. Qed.

  Instance: FullPseudoOrder D.  Proof. rewrite (_ : Subset D R). apply _. Qed.
  Instance: FullPseudoOrder C.  Proof. rewrite (_ : Subset C R). apply _. Qed.
  Instance: OrderReflecting D C f := full_pseudo_order_reflecting.
  Instance: Injective D C f.
  Proof. split; try apply _. intros x ? y ? E.
    apply (antisymmetry le _ _); apply (order_reflecting f _ _); now rewrite (_ $ E).
  Qed.

  Section interval.
    Context a `{a ∊ D} b `{b ∊ D} `{b-a ∊ R⁺} `{!Subset {[a, b]} D}.

    Instance: {[a, b]} ⊆ D.
    Proof. apply (subsetoid_alt _ _); trivial.
    + intros ?? E ?. unfold_sigs. pose proof _ : D ⊆ R . now rewrite <-(R $ E).
    Qed.

    Instance: {[a, b]} ⊆ X.  Proof. transitivity D; apply _. Qed.

    Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.

    Instance interval_wc: {[a, b]} ⊂⊂ D.
    Proof. pose proof (_ : D ⊆ R). apply (well_contained_alt (X:=X) _ _); try apply _.
    + split; try apply _. now destruct (_ : Bounded (X:=R) {[a, b]}).
    + destruct (open_dist (R:=R) (X:=X) D a) as [q[elq ?]].
      destruct (open_dist (R:=R) (X:=X) D b) as [r[elr ?]].
      apply (set_contained_by_dist (R:=R) (X:=X) _ _ (q ⊓ r)).
      intros x ? u [?[Eu1 Eu2]]. assert (x ∊ R). apply _.
      setoid_rewrite (abs_le_iff _ _). intros [??].
      assert (x-b ≤ r). subtransitivity (q ⊓ r). subtransitivity (x-u).
        apply (order_preserving (x +) _ _). now apply (flip_le_negate _ _).
        exact (meet_lb_r _ _).
      assert (-q ≤ x-a). subtransitivity (-(q ⊓ r)). 2: subtransitivity (x-u).
        apply (flip_le_negate _ _). exact (meet_lb_l _ _).
        apply (order_preserving (x +) _ _). now apply (flip_le_negate _ _).
      destruct ( cotransitivity (pos_plus_lt_compat_r a q) x ) as [Eax|?].
      assert (b-r < b) as Eb. apply (flip_lt_minus_l _ _ _).
        exact (pos_plus_lt_compat_r _ _).
      destruct ( cotransitivity Eb x ) as [Ebx|?].
      * apply (_ : closed_ball r b ⊆ D). split. apply _.
        setoid_rewrite (_ $ abs_minus_swap _ _). rewrite (abs_le_iff _ _).
        split; trivial. apply (flip_le_minus_r _ _ _).
        rewrite (R $ commutativity (+) _ _). now apply (lt_le _ _).
      * apply (_ : Subset {[a, b]} D). split. apply _. split; apply (lt_le _ _); trivial.
      * apply (_ : closed_ball q a ⊆ D). split. apply _.
        setoid_rewrite (_ $ abs_minus_swap _ _). rewrite (abs_le_iff _ _).
        split; trivial. apply (flip_le_minus_l _ _ _).
        rewrite (R $ commutativity (+) _ _). now apply (lt_le _ _).
    Qed.
  End interval.

  Context (bracket : ∀ y, y ∊ C → ∃ `{a ∊ D} `{b ∊ D}, Subset {[a, b]} D ∧ y ∊ {[f a, f b]}).

  Let P y := D ⊓ (λ x, f x = y).

  Instance: ∀ y `{y ∊ C}, P y ⊆ R.
  Proof. intros. unfold P. apply subsetoid_alt. apply _.
  + intros x1 x2 E [??]. unfold_sigs.
    assert (x2 ∊ D). now rewrite <-(R $ E).
    split; trivial. red. now rewrite <-(D $ E).
  + intros ? [??]. now apply (_ : D ⊆ R).
  Qed.

  Instance: ∀ y `{y ∊ C}, Inhabited (P y).
  Proof. intros. unfold P.
    destruct (bracket y _) as [a[?[b[?[??]]]]].
    pose proof (_ : D ⊆ R).
    assert (b-a ∊ R⁺). 
      apply (flip_nonneg_minus _ _). apply (order_reflecting (S:=D) f _ _).
      subtransitivity y; now destruct (_ : y ∊ {[f a, f b]}) as [?[??]].
    pose proof interval_wc a b.
    pose proof continuity_ufm (X:=X) (Y:=Y) (D:=D) (R:=C) (f:=f) {[a,b]}.
    assert (UniformlyContinuous {[a,b]} R f).
      apply (restrict_uniformly_continuous (X:={[a,b]}) _ _).
    assert (StrictlyOrderPreserving {[a,b]} R f).
      split. split; try apply _. rewrite (_ : Subset {[a,b]} R). apply _.
      intros x1 ? x2 ? ?. apply (strictly_order_preserving (S:=D) f); trivial; apply _.
    exists (interval_monotonic_inverse a b f y). split.
      apply (_ : Subset {[a,b]} D). apply interval_monotonic_inverse_el; apply _.
      red. apply interval_monotonic_inverse_applied; apply _.
  Qed.

  Let unique y₁ `{y₁ ∊ C} y₂ `{y₂ ∊ C} x₁ `{x₁ ∊ P y₁} x₂ `{x₂ ∊ P y₂}
    : y₁ = y₂ → x₁ = x₂.
  Proof. intro.
    destruct (_ : x₁ ∊ P y₁) as [? E1]; red in E1.
    destruct (_ : x₂ ∊ P y₂) as [? E2]; red in E2.
    apply (injective f _ _).
    subtransitivity y₁.
    subtransitivity y₂.
    subsymmetry.
  Qed.

  Instance: ∀ y `{y ∊ C}, Singleton (P y) R.
  Proof. intros. split; try apply _. intros. now apply (unique y y _ _). Qed.

  Definition monotonic_inverse : C ⇀ D := λ y, metric_description (X:=R) (P y).
  Notation g := monotonic_inverse.

  Instance: ∀ y `{y ∊ C}, g y ∊ P y.
  Proof. intros. apply (metric_description_spec _). Qed.

  Instance: ∀ y `{y ∊ C}, g y ∊ D.
  Proof. intros. now destruct (_ : g y ∊ P y). Qed.
 
  Instance monotonic_inverse_mor : Morphism (C ⇒ D) g.
  Proof. intros ?? E. unfold_sigs. red_sig. now apply (unique x y _ _). Qed.

  Lemma monotonic_inverse_applied y `{y ∊ C} : f (g y) = y.
  Proof. now destruct (_ : g y ∊ P y). Qed.

  Lemma monotonic_inverse_unique x `{x ∊ D} y `{y ∊ C} : f x = y → x = g y.
  Proof. intro. assert (x ∊ P y) by now split. now apply (unique y y _ _). Qed.

  Instance monotonic_surjective : Surjective D C f (inv:=g).
  Proof. split; unfold inverse; try apply _.
    intros x y E. unfold_sigs. red_sig. unfold compose.
    pose proof _ : C ⊆ R. subtransitivity x.
    now apply monotonic_inverse_applied.
  Qed.

  Instance monotonic_inverse_reflecting : StrictlyOrderReflecting C D g.
  Proof. split. split; try apply _.
    intros x ? y ? ?.
    rewrite <-( C $ monotonic_inverse_applied x ), <-( C $ monotonic_inverse_applied y ).
    now apply (strictly_order_preserving (S:=D) f _ _).
  Qed.

End monotonic.
