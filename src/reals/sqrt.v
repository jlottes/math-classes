Require Import
  abstract_algebra interfaces.orders interfaces.metric_spaces
  interfaces.archimedean_fields interfaces.reals
  theory.setoids theory.products theory.fields theory.lattices
  orders.maps orders.fields orders.lattices lattice_ordered_rings orders.abs orders.reals
  metric.metric_spaces metric.totally_bounded metric.maps_continuous
   metric.products metric.archimedean_fields
  cauchy_completion metric.complete metric.distance
  reals.intervals reals.ivt
  metric.bisection
  stdlib_ring stdlib_field.

Local Open Scope grp_scope.
Local Open Scope mc_abs_scope.

Local Notation "{[ a , b ]}" := (interval a b).

Section contents.
  Context `{Reals (R:=R) (U:=UR)}.
  Hint Extern 0 TheReals => eexact R : typeclass_instances.
  Add Ring R : (stdlib_ring_theory R).

  Instance: FullLatticeOrder R := _.
  Instance: SemiRingLatticeOrder R := _.
  Instance: LatticeAbs R := _.

  Section Rplus.
    Context `{!Ball R} `{!ArchimedeanField_Metric R}.

    Instance: Located (X:=R) R⁺.
    Proof. apply located_by_dist. apply _. intros x ?. exists_sub ((-x) ⊔ 0). split.
    + intros s ?. apply (join_lub _ _ _). 2: apply (_ : distance s x ∊ R⁺).
      unfold distance, reals_distance. rewrite (_ $ abs_def _).
      apply (join_le_compat_r _ _ _).
      rewrite (_ $ commutativity (+) _ _).
      exact (nonneg_plus_le_compat_r _ _).
    + intros p ? Ep.
      exists_sub (0 ⊔ x).
      unfold distance, reals_distance.
      rewrite (_ $ plus_join_distr_r _ _ _), (_ $ plus_negate_r _), (_ $ plus_0_l _).
      rewrite (_ $ abs_of_nonneg (- x ⊔ 0) ).
      now apply (lt_le _ _).
    Qed.

    Instance R_nonneg_ltb : LocallyTotallyBounded R⁺ .
    Proof. apply located_locally_totally_bounded; apply _. Qed.
  End Rplus.

  Existing Instance R_nonneg_ltb.

  Definition square : R ⇀ R := (uncurry (.*.) : R*R ⇀ R) ∘ (prod_diag : R ⇀ R*R).
  Notation "x ²" := (square x) (at level 1, format "x ²").

  Hint Unfold square : typeclass_instances.

  Instance square_mor : Morphism (R ⇒ R) square := _.

  Section square_cont.
    Hint Extern 0 AmbientSpace => eexact R : typeclass_instances.
    Instance square_cont `{!Ball R} `{!ArchimedeanField_Metric R}
      : Continuous (X:=R) (Y:=R) R R square := _.
  End square_cont.
  Existing Instance square_cont.

  Instance: ∀ x, x ∊ R → x² ∊ R⁺.
  Proof λ x _, _ : x*x ∊ R⁺ .

  Instance: Morphism (R⁺ ⇒ R⁺) square.
  Proof. intros ?? E. unfold_sigs. red_sig. now rewrite (R $ E). Qed.

  (*Hint Extern 0 AmbientSpace => eexact R⁺ : typeclass_instances.*)

  Section square_nonneg_cont.
    Context `{!Ball R} `{!ArchimedeanField_Metric R}.

    Instance: MetricSpace R⁺ := sub_metric_space.

    Instance square_nonneg_cont : Continuous (X:=R⁺) (Y:=R⁺) R⁺ R⁺ square.
    Proof.
      apply (continuity_alt (X:=R⁺) (Y:=R⁺)). apply _.
      intros U ?. assert (U ⊆ R). transitivity R⁺; apply _.
      assert (WellContained (X:=R) U R).
        apply (well_contained_alt); try apply _.
        split; try apply _. exact (bounded (X:=R⁺) U).
      pose proof (continuity_ufm (X:=R) (Y:=R) (f:=square) U).
      pose proof (continuity_wc_range (X:=R) (Y:=R) (f:=square) U).
      intuition.
      * split; [ exact sub_metric_space.. | | exact (uniform_continuity_def U R)].
        rewrite <-(_ : Subset (R⁺ ⇒ R⁺) (U ⇒ R⁺)). apply _.
      * pose proof (image_dom_range_proper (X:=R⁺) (Y:=R⁺) square R R U) as E.
        rewrite E. split; try apply _. rewrite <-E; eapply @subsetoid_image; apply _.
        exact (bounded (X:=R) _).
    Qed.
  End square_nonneg_cont.
  Existing Instance square_nonneg_cont.

  Instance: StrictlyOrderPreserving R⁺ R⁺ square .
  Proof. split. split; [| rewrite (_ : R⁺ ⊆ R)..]; apply _.
    intros x ? y ? E.
    destruct (decompose_lt E) as [z[? Ez]].
    apply (compose_lt x² y² (2*x*z + z*z)).
    rewrite (R $ Ez). change ((x+z)*(x+z) = x*x+(2*x*z+z*z)). setring R.
  Qed.

  Let bracket y `{y ∊ R⁺} : ∃ `{a ∊ R⁺} `{b ∊ R⁺}, Subset {[a, b]} R⁺ ∧ y ∊ {[a², b²]}.
  Proof. destruct (cotransitivity lt_1_2 y) as [E|E].
  + exists_sub 0 y. split. intros x [?[??]]. now split.
    split. apply _. change (0*0 ≤ y ≤ y*y). rewrite (_ $ mult_0_r _).
    split. apply (_ : y ∊ R⁺).
    apply (ge_1_mult_le_compat_r _ _ _). now apply (lt_le _ _). easy.
  + exists_sub 0 2. split. intros x [?[??]]. now split.
    split. apply _. change (0*0 ≤ y ≤ 2*2). rewrite (_ $ mult_0_r _).
    split. apply (_ : y ∊ R⁺).
    subtransitivity 2. now apply (lt_le _ _). rewrite (_ $ mult_2_2). exact (le_2_4).
  Qed.

  Definition real_sqrt : R⁺ ⇀ R := monotonic_inverse (square : R⁺ ⇀ R⁺).
  Notation "√" := real_sqrt.

  Instance real_sqrt_mor: Morphism (R⁺ ⇒ R⁺) √.
  Proof. unfold real_sqrt.
    apply (monotonic_inverse_mor R⁺ R⁺); trivial; try apply _.
  Qed.

  Lemma real_sqrt_eq x `{x ∊ R⁺} : √x * √x = x.
  Proof. change ((√x)² = x).
    apply (monotonic_inverse_applied R⁺ R⁺); trivial; try apply _.
  Qed.

  Lemma real_sqrt_unique x `{x ∊ R⁺} y `{y ∊ R} : x * x = y → x = √y.
  Proof. replace (x*x) with (square x) by reflexivity. intro E.
    assert (y ∊ R⁺). rewrite <-(_ $ E). apply _.
    apply (monotonic_inverse_unique R⁺ R⁺); trivial; try apply _.
  Qed.

End contents.
