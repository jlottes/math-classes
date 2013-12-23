Require Import
  abstract_algebra interfaces.orders interfaces.metric_spaces
  interfaces.archimedean_fields interfaces.reals
  theory.setoids theory.products theory.fields theory.lattices
  orders.maps orders.fields orders.lattices orders.abs orders.reals
  metric.metric_spaces metric.totally_bounded metric.archimedean_fields
  cauchy_completion metric.distance
  stdlib_ring stdlib_field.

Local Open Scope mc_abs_scope.

Definition interval `{R:@TheReals AR} `{Le AR} a b : set := (R:set) ⊓ (λ x, a ≤ x ≤ b) .
Local Notation "{[ a , b ]}" := (interval a b).

Section interval.
  Context `{Reals (R:=R)} `{!Ball R} `{!ArchimedeanField_Metric R}.
  Hint Extern 0 TheReals => eexact R : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact R : typeclass_instances.
  Add Field R : (stdlib_field_theory R).

  Instance: FullLatticeOrder R := _.
  Instance: SemiRingLatticeOrder R := _.
  Instance: LatticeAbs R := _.

  Context a `{a ∊ R} b `{b ∊ R}.

  Lemma interval_is_ball : {[a, b]} = closed_ball ((b-a)/2) ((a+b)/2).
  Proof. cut (∀ x `{x ∊ R}, a ≤ x ≤ b ↔ |(a+b)/2-x| ≤ (b-a)/2).
      intro P. intros x. split; intros [??]; split; trivial; now apply (P x _).
    intros x ?. rewrite (R $ abs_minus_swap _ _), (abs_le_iff _ _).
    cut (  (a ≤ x ↔ - ((b - a) / 2) ≤ x - (a + b) / 2 )
         ∧ (x ≤ b ↔ x - (a + b) / 2 ≤ (b - a) / 2) ). tauto.
    split.
    + rewrite (order_embedding (+ -((a+b)/2)) a x).
      now mc_replace (a-(a+b)/2) with (-((b-a)/2)) on R by setfield R.
    + rewrite (order_embedding (+ -((a+b)/2)) x b).
      now mc_replace (b-(a+b)/2) with ((b-a)/2) on R by setfield R.
  Qed.

  Instance interval_subsetoid : {[a, b]} ⊆ R  .   Proof. rewrite interval_is_ball. apply _. Qed.
  Instance interval_closed : Closed {[a, b]}  .   Proof. rewrite interval_is_ball. apply _. Qed.
  Instance interval_bounded : Bounded {[a, b]}.   Proof. rewrite interval_is_ball. apply _. Qed.

  Instance interval_setoid : Setoid {[a, b]} := _ .

  Instance interval_limit : Limit {[a, b]} := subspace_limit _.
  Instance interval_complete : CompleteMetricSpace {[a, b]} := complete_subspace _.
  Instance interval_msp : MetricSpace {[a, b]} := _.

  Context `{b-a ∊ R⁺}.

  Let Eab : a ≤ b.   Proof. now apply (flip_nonneg_minus _ _). Qed.

  Instance interval_left_el : a ∊ {[a, b]}.  Proof. split. apply _. now split. Qed.
  Instance interval_right_el: b ∊ {[a, b]}.  Proof. split. apply _. now split. Qed.

  Instance interval_inhabited : Inhabited {[a, b]}.
  Proof. exists a. apply _. Qed.

  Instance interval_wc_R : {[a,b]} ⊂⊂ R.
  Proof. apply (well_contained_alt _ _); apply _. Qed.

  Instance interval_located : Located {[a, b]}.   Proof. rewrite interval_is_ball. apply _. Qed.
  Instance interval_totally_bounded : TotallyBounded {[a, b]}.  Proof locally_totally_bounded_alt _.
  Instance interval_locally_totally_bounded : LocallyTotallyBounded {[a, b]}.  Proof totally_bounded_locally _ _.

End interval.

Hint Extern 2 (Setoid (interval (R:=?R) _ _)) => eapply (@interval_setoid _ R) : typeclass_instances.
Hint Extern 2 (interval (R:=?R) _ _ ⊆ ?R) => eapply (@interval_subsetoid _ R) : typeclass_instances.
Hint Extern 2 (Closed (interval (R:=?R) _ _)) => eapply (@interval_closed _ R) : typeclass_instances.
Hint Extern 2 (Bounded (interval (R:=?R) _ _)) => eapply (@interval_bounded _ R) : typeclass_instances.
Hint Extern 2 (Inhabited (interval (R:=?R) _ _)) => eapply (@interval_inhabited _ R) : typeclass_instances.
Hint Extern 2 (Located (interval (R:=?R) _ _)) => eapply (@interval_located _ R) : typeclass_instances.
Hint Extern 2 (TotallyBounded (interval (R:=?R) _ _)) => eapply (@interval_totally_bounded _ R) : typeclass_instances.
Hint Extern 2 (LocallyTotallyBounded (interval (R:=?R) _ _)) => eapply (@interval_locally_totally_bounded _ R) : typeclass_instances.
Hint Extern 2 (?a ∊ interval (R:=?R) ?a _) => eapply (@interval_left_el _ R) : typeclass_instances.
Hint Extern 2 (?b ∊ interval (R:=?R) _ ?b) => eapply (@interval_right_el _ R) : typeclass_instances.
Hint Extern 2 (interval (R:=?R) _ _ ⊂⊂ ?R) => eapply (@interval_wc_R _ R) : typeclass_instances.
Hint Extern 2 (Limit (interval (R:=?R) ?a ?b)) => eexact (interval_limit (R:=R) a b) : typeclass_instances.
Hint Extern 2 (CompleteMetricSpace (interval (R:=?R) _ _)) => eapply (@interval_complete _ R) : typeclass_instances.
Hint Extern 2 (MetricSpace (interval (R:=?R) _ _)) => eapply (@interval_msp _ R) : typeclass_instances.
Hint Extern 2 (Distance (interval (R:=?R) _ _)) => eexact (reals_distance (R:=R)) : typeclass_instances.
Hint Extern 2 (MetricDistance (interval (R:=?R) _ _)) => eapply (@subspace_distance_correct _ R) : typeclass_instances.

Section clamp.
  Context `{Reals (R:=R)} `{!Ball R} `{!ArchimedeanField_Metric R}.
  Hint Extern 0 TheReals => eexact R : typeclass_instances.
  Instance: FullLatticeOrder R := _.

  Context a `{a ∊ R} b `{b ∊ R} `{b-a ∊ R⁺}.

  Definition clamp : R ⇀ {[a, b]} := λ x, a ⊔ x ⊓ b.

  Let Eab : a ≤ b.   Proof. now apply (flip_nonneg_minus _ _). Qed.

  Instance: ∀ x, x ∊ R → clamp x ∊ {[a,b]}.
  Proof. intros x ?. unfold clamp. split. apply _. split.
  + apply (meet_glb _ _ _); trivial. exact (join_ub_l _ _).
  + exact (meet_lb_r _ _).
  Qed.
  Instance clamp_mor: Morphism (R ⇒ {[a,b]}) clamp.
  Proof. intros ?? E. unfold_sigs. red_sig. unfold clamp. now rewrite (_ $ E). Qed.

  Instance clamp_cont: UniformlyContinuous R {[a,b]} clamp.
  Proof.
    assert (UniformlyContinuous R R clamp) by exact (_ : UniformlyContinuous R R ((⊓ b) ∘ (a ⊔))).
    split; try apply _. apply (uniform_continuity_def R R).
  Qed.

  Lemma clamp_in_range : (clamp : {[a,b]} ⇀ {[a,b]}) = id.
  Proof. intros x y [[[? [E1 E2]] ?] ?]. red_sig.
    pose proof _ : {[a,b]} ⊆ R. subtransitivity x. unfold clamp.
    rewrite (R $ join_r _ _ E1). exact (meet_l _ _ E2).
  Qed.

End clamp.

Hint Extern 2 (Morphism _ (clamp (R:=?R) _ _)) => eapply (@clamp_mor _ R) : typeclass_instances.
Hint Extern 2 (UniformlyContinuous _ _ (clamp (R:=?R) _ _)) => eapply (@clamp_cont _ R) : typeclass_instances.



