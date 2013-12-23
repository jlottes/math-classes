Require Import
  abstract_algebra interfaces.orders interfaces.metric_spaces interfaces.rationals interfaces.reals
  theory.setoids
  orders.fields orders.affinely_extended_field orders.abs
  metric.metric_spaces metric.maps_continuous metric.prelength metric.rationals
  metric.cauchy_completion
  the_integers interfaces.integers interfaces.additional_operations
  nonneg_integers_naturals orders.naturals
  theory.rings
  orders.archimedean_fields orders.integers orders.lattices
  theory.rationals theory.reals orders.reals
  metric.bisection
  stdlib_field stdlib_field_dec misc.quote.

Local Notation AQ := TheAERationals.A.
Local Notation Q := the_ae_rationals.
Local Notation "Q∞" := (aff_ext Q).
Local Notation Qfull := (aff_ext_full Q).

Class Distance `{R:TheReals} `(X:set) := distance : X ⇀ X ⇀ R.
Class SetDistance `{R:@TheReals AR} `(X:@set A) := set_distance : every (@set A) ⇀ X ⇀ R.

Section ifc.
  Context `{R:TheReals} `{Reals _ (R:=R)}.
  Context `{MetricSpace (X:=X)} `{d:!Distance X} `{sd:!SetDistance X}.

  Class MetricDistance : Prop :=
  { metric_dist_real x `{x ∊ X} y `{y ∊ X} : distance x y ∊ R
  ; metric_dist_spec x `{x ∊ X} y `{y ∊ X} q `{q ∊ Q}
    : ball q x y ↔ distance x y ≤ rationals_to_field Q R q
  }.

  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.
  Class MetricSetDistance : Prop :=
  { metric_set_dist_real S `{!Inhabited S} `{!Located S} x `{x ∊ X} : set_distance S x ∊ R
  ; metric_set_dist_spec S `{!Inhabited S} `{!Located S} x `{x ∊ X} q `{q ∊ Q}
    : (∀ `{ε ∊ Q₊}, ∃ `{y ∊ S}, ball (q+ε) x y) ↔ set_distance S x ≤ rationals_to_field Q R q
  }.
End ifc.
Arguments MetricDistance    {_ R _ _ _ _ _ _ _ _} X {_ _} .
Arguments MetricSetDistance {_ R _ _ _ _ _ _ _ _} X {_ _ _} .

Hint Extern 2 (distance (R:=?R) _ _ ∊ ?R) => eapply (@metric_dist_real _ R) : typeclass_instances.
Hint Extern 2 (set_distance (R:=?R) _ _ ∊ ?R) => eapply (@metric_set_dist_real _ R) : typeclass_instances.


Local Open Scope mc_abs_scope.
Section reals.
  Context `{Reals (R:=R)}.
  Context `{!Ball R} `{!ArchimedeanField_Metric R}.
  Context `{!Meet R} `{!Join R} `{!FullLatticeOrder R} `{!Abs R} `{!LatticeAbs R}.

  Hint Extern 0 TheReals => eexact R : typeclass_instances.

  Instance reals_distance : Distance R := λ x y, |x - y|.

  Instance reals_metric_distance: MetricDistance R.
  Proof. split; unfold distance, reals_distance.
  + intros. apply _.
  + intros ??????. exact (arch_field_ball_abs _ _ _).
  Qed.
End reals.

Hint Extern 2 (Distance (R:=?R) ?R) => eapply @reals_distance : typeclass_instances.
Hint Extern 2 (MetricDistance ?R (d:=reals_distance)) => eapply @reals_metric_distance : typeclass_instances.

(*
Section reals_test.
  Context `{Reals (R:=R)}.
  Hint Extern 0 TheReals => eexact R : typeclass_instances.

  Check _ : MetricDistance R.
End reals_test.
*)

(*Hint Extern 2 (Morphism _ (distance (R:=?R))) => eapply (@metric_dist_mor _ R) : typeclass_instances.*)

Section metric_from_distance.
  Context `{Reals (R:=R)}.
  Hint Extern 0 TheReals => eexact R : typeclass_instances.

  Context `{Setoid (S:=X)} `{!Distance X}.
  Notation d := distance.
  Notation "#" := (rationals_to_field Q R).

  Instance ball_from_distance : Ball X := 
    alt_Build_MetricSpace_ball (λ q x y, d x y ≤ #q).

  Context `{!Morphism (X ⇒ X ⇒ R) d}.
  Context (sep : ∀ `{x ∊ X} `{y ∊ X}, d x y = 0 ↔ x = y).
  Context (sym : ∀ `{x ∊ X} `{y ∊ X}, d x y = d y x).
  Context (tri : ∀ `{x ∊ X} `{y ∊ X} `{z ∊ X}, d x z ≤ d x y + d y z).

  Instance: ∀ `{x ∊ X} `{y ∊ X}, d x y ∊ R⁺.
  Proof. intros. split. apply _. red.
    apply (order_reflecting (2 *.) _ _).
    rewrite (_ $ mult_0_r _), (_ $ mult_2_plus_l _).
    rewrite (_ $ sym x _ y _) at 2.
    subtransitivity (d x x).
      apply (eq_le _ _). subsymmetry. now apply (sep _ _ _ _).
    exact (tri _ _ _ _ _ _).
  Qed.

  Instance msp_from_distance: MetricSpace X.
  Proof. apply alt_Build_MetricSpace.
  + intros ?? E1 ?? E2 ?? E3 ?; unfold_sigs.
    now rewrite <-(Q $ E1), <-(_ $ E2), <-(_ $ E3).
  + intros ε ? ??. subtransitivity 0.
      apply (eq_le _ _). now apply (sep _ _ _ _).
    apply (_ : # ε ∊ R⁺).
  + intros ?? ?? ??. rewrite (_ $ sym _ _ _ _) at 1. tauto.
  + intros x ? y ? E1. rewrite (_ $ preserves_0) in E1.
    apply (sep _ _ _ _). apply antisymmetry with le; try apply _; trivial.
    apply (_ : d x y ∊ R⁺).
  + intros ?? ?? x ? y ? z ? ??. subtransitivity (d x y + d y z).
      exact (tri _ _ _ _ _ _).
    rewrite (_ $ preserves_plus _ _).
    now apply (plus_le_compat _ _ _ _).
  + intros ?? ?? ?? P. apply (le_closed _ _).
    intros δ ?. rewrite <-(_ $ preserves_plus (f:=#) _ _).
    now apply P.
  Qed.

  Instance msp_from_distance_correct: MetricDistance X.
  Proof. split. intros x ? y ?. apply _.
    intros x ? y ? q ?. unfold ball, ball_from_distance, alt_Build_MetricSpace_ball.
    rewrite <-(rationals_to_field_unique Q id _ _ (_:Proper (Q,=) q)). unfold id.
    split. intros [E|?]; [|intuition].
      destruct (ae_inf_not_el). now rewrite <-(_ $ E).
    intros E. right. intuition. apply (reflects_nonneg #). apply _. split. apply _. red.
      subtransitivity (d x y). apply (_ : d x y ∊ R⁺).
  Qed.

End metric_from_distance.

Section uniqueness.
  Context `{Reals (R:=R)}.
  Hint Extern 0 TheReals => eexact R : typeclass_instances.

  Context `{MetricSpace (X:=X)}.

  Notation "#" := (rationals_to_field Q R).

  Existing Instance closed_binary.
  Let distance_unique_aux (d₁ d₂ : X ⇀ X ⇀ R)
    `{!ClosedFun (X ⇀ X ⇀ R) d₁} `{!ClosedFun (X ⇀ X ⇀ R) d₂}
    : (∀ `{x ∊ X} `{y ∊ X} `{q ∊ Q}, ball q x y ↔ d₁ x y ≤ #q)
    → (∀ `{x ∊ X} `{y ∊ X} `{q ∊ Q}, ball q x y ↔ d₂ x y ≤ #q)
    → (∀ `{x ∊ X} `{x' ∊ X} `{y ∊ X} `{y' ∊ X}, x = x' → y = y' → d₁ x y ≤ d₂ x' y').
  Proof. intros P1 P2 x ? x' ? y ? y' ? Ex Ey.
    rewrite (le_iff_not_lt_flip _ _). intro E.
    destruct (archimedean_rationals_dense _ _ E) as [q[?[E1 E2]]].
    revert E2. setoid_rewrite <-(le_iff_not_lt_flip _ _).
    apply (P1 _ _ _ _ _ _). rewrite (X $ Ex), (X $ Ey). apply (P2 _ _ _ _ _ _).
    now apply (lt_le _ _).
  Qed.

  Lemma distance_unique (d₁ d₂ : X ⇀ X ⇀ R)
    `{!ClosedFun (X ⇀ X ⇀ R) d₁} `{!ClosedFun (X ⇀ X ⇀ R) d₂}
    : (∀ `{x ∊ X} `{y ∊ X} `{q ∊ Q}, ball q x y ↔ d₁ x y ≤ #q)
    → (∀ `{x ∊ X} `{y ∊ X} `{q ∊ Q}, ball q x y ↔ d₂ x y ≤ #q)
    → d₁ = d₂ .
  Proof. intros P1 P2. rewrite ext_equiv_binary_sig. intros x x' Ex y y' Ey.
    unfold_sigs. red_sig.
    apply (antisymmetry le _ _).
    apply (distance_unique_aux _ _ P1 P2); trivial.
    apply (distance_unique_aux _ _ P2 P1); trivial; subsymmetry.
  Qed.

End uniqueness.


Section props.
  Context `{Reals (R:=R)}.
  Hint Extern 0 TheReals => eexact R : typeclass_instances.
  Add Ring R : (stdlib_ring_theory R).

  Context `{MetricSpace (X:=X)} {dist:Distance X} `{!MetricDistance X}.
  Notation d := distance.
  Notation "#" := (rationals_to_field Q R).

  Instance metric_dist_nonneg x `{x ∊ X} y `{y ∊ X} : d x y ∊ R⁺.
  Proof. split. apply _. red.
    rewrite (le_iff_not_lt_flip _ _). intro E.
    destruct (archimedean_rationals_dense _ _ E) as [q[?[E1 E2]]].
    revert E2. setoid_rewrite <-(le_iff_not_lt_flip _ _).
    cut (q ∊ Q⁺). intro. apply (_ : #q ∊ R⁺).
    apply (ball_nonneg q x y).
    rewrite (metric_dist_spec _ _ _). now apply (lt_le _ _).
  Qed.

  Instance metric_dist_mor : Morphism (X ⇒ X ⇒ R) d.
  Proof.
    assert (ClosedFun (X ⇀ X ⇀ R) d). intros ????. apply _.
    apply binary_morphism_proper_back. apply ext_equiv_binary_sig.
    apply (distance_unique _ _); apply metric_dist_spec.
  Qed.

  Lemma metric_dist_sep x `{x ∊ X} y `{y ∊ X} : d x y = 0 ↔ x = y.
  Proof.
    assert (d x y = 0 ↔ d x y ≤ # 0) as P.
      rewrite (_ $ preserves_0). split.
        exact (eq_le _ _).
        intro. apply antisymmetry with le; try apply _; trivial. apply (_ : d x y ∊ R⁺).
    rewrite P, <-(metric_dist_spec _ _ _).
    exact (ball_separated _ _).
  Qed.

  Lemma metric_dist_refl x `{x ∊ X} : d x x = 0.
  Proof. now apply metric_dist_sep. Qed.

  Lemma metric_dist_sym x `{x ∊ X} y `{y ∊ X} : d x y = d y x.
  Proof.
    cut (∀ x `{x ∊ X} y `{y ∊ X}, d x y ≤ d y x). intro P.
      apply antisymmetry with le; try apply _; now apply P.
    clear dependent x. clear dependent y. intros x ? y ?.
    rewrite (le_iff_not_lt_flip _ _). intro E.
    destruct (archimedean_rationals_dense _ _ E) as [q[?[E1 E2]]].
    revert E2. setoid_rewrite <-(le_iff_not_lt_flip _ _).
    rewrite <-(metric_dist_spec _ _ _).
    subsymmetry.
    rewrite (metric_dist_spec _ _ _). now apply (lt_le _ _).
  Qed.

  Lemma metric_dist_tri x `{x ∊ X} y `{y ∊ X} z `{z ∊ X} : d x z ≤ d x y + d y z .
  Proof.
    rewrite (le_iff_not_lt_flip _ _). intro E.
    destruct (archimedean_rationals_dense _ _ E) as [q[?[E1 E2]]].
    revert E2. setoid_rewrite <-(le_iff_not_lt_flip _ _).
    rewrite <-(metric_dist_spec _ _ _).
    destruct (split_sum_bound_r _ _ _ E1) as [r[?[s[?[Eq [E3 E4]]]]]].
    rewrite (_ $ Eq).
    apply (ball_triangle _ _ _ y _); rewrite (metric_dist_spec _ _ _); now apply (lt_le _ _).
  Qed.

  Lemma metric_dist_finite : FinitePoints X.
  Proof. intros x ? y ?.
    destruct (finite_points (d x y) 0) as [q[? E]].
    exists_sub q.
    rewrite (metric_dist_spec _ _ _).
    rewrite (arch_field_ball _ _ _) in E. destruct E as [_ E].
    now rewrite (_ $ negate_0), (_ $ plus_0_r _) in E.
  Qed.

  Lemma metric_dist_located : LocatedPoints X.
  Proof. intros x ? y ? p ? q ? E.
    apply (strictly_order_preserving # _ _) in E.
    rewrite !(metric_dist_spec _ _ _).
    destruct (cotransitivity E (d x y)) as [E2|E2].
    + right. rewrite (le_iff_not_lt_flip _ _). tauto.
    + left. now apply (lt_le _ _).
  Qed.

  Let cont_aux a `{a ∊ X} b `{b ∊ X} x `{x ∊ X} y `{y ∊ X} q `{q ∊ Q⁺} r `{r ∊ Q⁺}
    : ball q a x → ball r b y → ball (q+r) (d a b) (d x y).
  Proof. intros E1 E2.
    rewrite (metric_dist_spec _ _ _) in E1.
    rewrite (metric_dist_spec _ _ _) in E2.
    rewrite (arch_field_ball _ _ _). rewrite (_ $ preserves_plus _ _).
    split.
    + rewrite (flip_le_minus_r _ _ _), (_ $ commutativity (+) _ _), (flip_le_minus_l _ _ _).
      subtransitivity (d x a + d a y). exact (metric_dist_tri _ _ _).
      subtransitivity (#q + (d a b + #r)).
      apply (plus_le_compat _ _ _ _). now rewrite (_ $ metric_dist_sym _ _).
      subtransitivity (d a b + d b y). exact (metric_dist_tri _ _ _).
      now apply (order_preserving (d a b +) _ _).
      apply (eq_le _ _). setring R.
    + rewrite (flip_le_minus_l _ _ _), <-(_ $ associativity (+) _ _ _), (_ $ commutativity (+) _ (d x y)).
      subtransitivity (d a x + d x b). exact (metric_dist_tri _ _ _).
      apply (plus_le_compat _ _ _ _). exact E1.
      subtransitivity (d x y + d y b). exact (metric_dist_tri _ _ _).
      apply (order_preserving (d x y +) _ _).
      now rewrite (_ $ metric_dist_sym _ _).
  Qed.

  Instance metric_dist_ufm_cont : UniformlyContinuous (X*X) R (uncurry d).
  Proof. split; try apply _. intros ε ?. exists_sub (ε/2).
    intros [a b][??][x y][??][E1 E2]. unfold uncurry. simpl in *.
    mc_replace ε with (ε/2+ε/2) on Q by decfield Q.
    now apply (cont_aux _ _ _ _ _ _).
  Qed.

  Instance subspace_distance_correct S `{S ⊆ X} : MetricDistance (R:=R) (d:=dist) S.
  Proof. split.
  + intros ????. apply _.
  + intros x ? y ?. exact (metric_dist_spec x y).
  Qed.

End props.

Hint Extern 2 (Morphism _ (distance (R:=?R))) => eapply (@metric_dist_mor _ R) : typeclass_instances.
Hint Extern 2 (distance (R:=?R) _ _ ∊ ?R⁺) => eapply (@metric_dist_nonneg _ R) : typeclass_instances.

Hint Extern 2 (Equiv (elt_type (Inhabited ⊓ Located))) => eapply set_equiv : typeclass_instances.

Section set_distance_props.
  Context `{Reals (R:=R)}.
  Hint Extern 0 TheReals => eexact R : typeclass_instances.

  Context `{MetricSpace (X:=X)} {sdist:SetDistance X} `{!MetricSetDistance X}.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.
  Notation d := set_distance.
  Notation "#" := (rationals_to_field Q R).

  Instance metric_set_dist_nonneg S `{!Inhabited S} `{!Located S} x `{x ∊ X} : d S x ∊ R⁺.
  Proof. split. apply _. red.
    rewrite (le_iff_not_lt_flip _ _). intro E.
    destruct (archimedean_rationals_dense _ _ E) as [q[?[E1 E2]]].
    revert E2. setoid_rewrite <-(le_iff_not_lt_flip _ _).
    rewrite <-(_ $ preserves_0 (f:=#)). apply (order_preserving # _ _).
    apply (le_closed_alt _ _). intros ε ?. cut (q+ε ∊ Q⁺). intro E'. apply E'.
    apply (lt_le _ _) in E1. rewrite <-(metric_set_dist_spec _ _ _) in E1.
    destruct (E1 ε _) as [y[??]]. pose proof (_ : S ⊆ X). now apply (ball_nonneg _ x y).
  Qed.

  Lemma metric_set_dist_proper
    S T `{!Inhabited S} `{!Located S} `{!Inhabited T} `{!Located T} `{S ⊆ T}
    x `{x ∊ X} y `{y ∊ X} : x = y → d T x ≤ d S y.
  Proof. rewrite (le_iff_not_lt_flip _ _). intros Ex E.
    destruct (archimedean_rationals_dense _ _ E) as [q[?[E1 E2]]].
    revert E2. apply (le_iff_not_lt_flip _ _).
    apply (metric_set_dist_spec _ _ _). intros ε ?.
    apply (lt_le _ _) in E1. rewrite <-(metric_set_dist_spec _ _ _) in E1.
    destruct (E1 ε _) as [z[? E2]]. assert (z ∊ X). apply (_ : S ⊆ X). apply _. 
    rewrite <-(X $ Ex) in E2. now exists_sub z.
  Qed.

  Instance metric_set_dist_bimor : Morphism (Inhabited ⊓ Located ⇒ X ⇒ R) d.
  Proof. apply binary_morphism_proper_back.
    intros S T [[[elS1 elS2] [elT1 elT2]]ES] x y Ex. red in elS1,elS2,elT1,elT2.
    unfold_sigs. red_sig.
    apply (antisymmetry le _ _); 
    apply (metric_set_dist_proper); trivial; try apply _; try subsymmetry;
    rewrite ES; apply _.
  Qed.

  Context {dist:Distance X} `{!MetricDistance X}.
  Lemma metric_set_dist_lb S `{!Located S} s `{s ∊ S} x `{x ∊ X}
    : d S x ≤ distance s x.
  Proof. pose proof (_ : S ⊆ X).
    apply (le_iff_not_lt_flip _ _). intro E.
    destruct (archimedean_rationals_dense _ _ E) as [q[?[E1 E2]]].
    revert E2. setoid_rewrite <-(le_iff_not_lt_flip _ _).
    apply (metric_set_dist_spec _ _ _). intros ε ?. exists_sub s.
    subsymmetry. apply (metric_dist_spec _ _ _).
    subtransitivity (#q). now apply (lt_le _ _).
    apply (order_preserving # _ _).
    exact (nonneg_plus_le_compat_r _ _).
  Qed.

  Lemma metric_set_dist_plus S `{!Inhabited S} `{!Located S} x `{x ∊ X} ε `{ε ∊ R₊}
    : ∃ s `{s ∊ S}, distance s x ≤ d S x + ε .
  Proof.
    destruct (archimedean_rationals_dense (d S x) (d S x + ε) (pos_plus_lt_compat_r _ _))
      as [q[?[E1 E2]]].
    apply (lt_le _ _) in E1.
    rewrite <-(metric_set_dist_spec _ _ _) in E1.
    apply (flip_pos_minus _ _) in E2.
    destruct (archimedean_rationals_dense_pos (d S x + ε - #q)) as [p[??]].
    destruct (E1 p _) as [s[??]].
    exists_sub s. pose proof (_ : S ⊆ X). subtransitivity (#(q+p)).
    now apply (metric_dist_spec _ _ _).
    preserves_simplify #. rewrite (_ $ commutativity (+) (#q) _).
    apply (flip_le_minus_r _ _ _). now apply (lt_le _ _).
  Qed.

  Lemma metric_set_dist_alt S `{!Inhabited S} `{!Located S} x `{x ∊ X} r `{r ∊ R}
    : d S x < r → ∃ s `{s ∊ S}, distance s x ≤ r .
  Proof. intro E. destruct (decompose_lt E) as [ε[? E']].
    destruct (metric_set_dist_plus S x ε) as [s [??]].
    exists_sub s. pose proof (_ : S ⊆ X). now rewrite (_ $ E').
  Qed.
End set_distance_props.

Hint Extern 2 (Morphism _ (set_distance (R:=?R))) => eapply (@metric_set_dist_bimor _ R) : typeclass_instances.
Hint Extern 2 (set_distance (R:=?R) _ _ ∊ ?R⁺) => eapply (@metric_set_dist_nonneg _ R) : typeclass_instances.

Section set_distance_more_props.
  Context `{Reals (R:=R) (U:=UR)}.
  Hint Extern 0 TheReals => eexact R : typeclass_instances.
  Notation "#" := (rationals_to_field Q R).

  Notation d := distance.
  Context `{MetricSpace (X:=X)} `{!Distance X} `{!MetricDistance X}.

  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.

  Definition metric_set_dist_spec_alt S x r : Prop :=
       (∀ `{s ∊ S}, r ≤ distance s x)
     ∧ (∀ `{p ∊ R}, r < p → ∃ `{s ∊ S}, distance s x ≤ p) .

  Lemma located_by_dist S `{S ⊆ X} :
    (∀ `{x ∊ X}, ∃ `{r ∊ R}, metric_set_dist_spec_alt S x r) → Located S.
  Proof. intro P. split; try apply _. intros x ? p ? q ? E.
    destruct (P x _) as [r[?[P1 P2]]].
    destruct (cotransitivity (strictly_order_preserving # _ _ E) r) as [E'|E'].
      right. intros s ??. generalize (P1 s _). apply (lt_not_le_flip _ _).
      apply (le_lt_trans _ (#p) _); trivial.
      apply (metric_dist_spec _ _ _). subsymmetry.
    left. destruct (P2 (#q) _ E') as [s[??]]. exists_sub s.
    subsymmetry. now apply (metric_dist_spec _ _ _).
  Qed.

  Context {sd:SetDistance X} `{!MetricSetDistance X}.
  Lemma located_by_dist_fun S `{S ⊆ X}
    (f : X ⇀ R) `{!Morphism (X ⇒ R) f} :
    (∀ `{x ∊ X}, metric_set_dist_spec_alt S x (f x))
    → Located S ∧ (set_distance (X:=X) S : X ⇀ R) = f.
  Proof. intro P.
    assert (Located S). apply (located_by_dist _).
      intros x ?. exists_sub (f x). exact (P _ _).
    intuition. intros ?? E. unfold_sigs.
    destruct (P x _) as [P1 P2].
    assert (Inhabited S).
      destruct (P2 (f x + 1) _ (pos_plus_lt_compat_r _ _)) as [s[??]]. apply _.
    red_sig. rewrite <-(X $ E). clear dependent y.
    apply (antisymmetry le _ _); apply (le_closed_alt _ _); intros ε ?.
    + destruct (P2 (f x + ε) _ (pos_plus_lt_compat_r _ _)) as [s[? E]].
      subtransitivity (d s x).
      apply (metric_set_dist_lb S _ _).
    + destruct (metric_set_dist_plus S x ε) as [s[??]].
      subtransitivity (d s x).
      now apply P1.
  Qed.

End set_distance_more_props.

Section set_distance_existence.
  Context `{Reals (R:=R)}.
  Hint Extern 0 TheReals => eexact R : typeclass_instances.
  Add Ring R' : (stdlib_ring_theory R).

  Context `{MetricSpace (X:=X)}.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.

  Notation C := (CauchyFamilies Q⁺).

  Definition default_set_distance_family : Sets ⇀ X ⇀ C := λ V x, family (λ ε q,
    q ∊ Q⁺ ∧ (∀ `{c ∊ Q₊}, ∃ `{y ∊ V}, ball (q+ε+c) x y) ∧ ∀ `{y ∊ V} `{r ∊ Q₊}, ball r x y → q-ε ≤ r).

  Notation S := default_set_distance_family.

  Instance: ∀ V `{V ⊆ X} x `{x ∊ X} ε `{ε ∊ Q∞₊}, S V x ε ⊆ Q⁺.
  Proof. intros. apply subsetoid_alt. apply _.
  + intros p q E [? [P1 P2]]. unfold_sigs. split. apply _. split.
      intros c ?. destruct (P1 c _) as [y[??]]. exists_sub y. now rewrite <-(Qfull $ E).
    intros y ? r ??. rewrite <-(Qfull $ E). now apply (P2 y _ _ _).
  + now intros q [? _].
  Qed.

  Instance: ∀ V `{V ⊆ X} x `{x ∊ X} ε `{ε ∊ Q∞₊}, Setoid (S V x ε).
  Proof. intros. exact (subsetoid_a (T:=Q⁺)). Qed.

  Let set_dist_family_proper_1_aux V `{V ⊆ X} x `{x ∊ X}
    ε₁ `{ε₁ ∊ Q∞₊} ε₂ `{ε₂ ∊ Q∞₊} : ε₁ = ε₂ → Subset (S V x ε₁) (S V x ε₂).
  Proof. intros E q [?[P1 P2]]. split. apply _. split.
      intros c ?. destruct (P1 c _) as [y[??]]. exists_sub y. now rewrite <-(Qfull $ E).
    intros y ? r ??. rewrite <-(Qfull $ E). now apply (P2 y _ _ _).
  Qed.
 
  Lemma set_dist_family_proper_1 V `{V ⊆ X} x `{x ∊ X}
    ε₁ `{ε₁ ∊ Q∞₊} ε₂ `{ε₂ ∊ Q∞₊} : ε₁ = ε₂ → S V x ε₁ = S V x ε₂.
  Proof. intro E. apply antisymmetry_t with Subset; try apply _;
    apply (set_dist_family_proper_1_aux _ _ _ _); trivial; subsymmetry.
  Qed.

  Lemma set_dist_family_proper_2 V₁ `{V₁ ⊆ X} V₂ `{V₂ ⊆ X} x₁ `{x₁ ∊ X} x₂ `{x₂ ∊ X}
    : V₁ = V₂ → x₁ = x₂ → S V₁ x₁ = S V₂ x₂ .
  Proof. intros EV Ex.
    intros ε₁ ? ε₂ ? q₁ [? [B₁ P₁]].
    intros           q₂ [? [B₂ P₂]].
    rewrite (the_ae_rationals_ball _ _ _), (abs_le_iff _ _). split.
    * mc_replace (q₁ - q₂) with (-(q₂ - q₁)) on Q by setring Q.
      apply (flip_le_negate _ _).
      apply (flip_le_minus_l _ _ _).
      mc_replace (ε₁ + ε₂ + q₁) with (q₁ + ε₁ + ε₂) on Q by setring Q.
      apply (flip_le_minus_l _ _ _).
      apply (le_closed_alt _ _). intros c ?.
      destruct (B₁ c _) as [y[??]].
      assert (y ∊ V₂) by now rewrite <-EV.
      apply (P₂ y _ _ _). now rewrite <-(X $ Ex).
    * apply (flip_le_minus_l _ _ _).
      mc_replace (ε₁ + ε₂ + q₂) with (q₂ + ε₂ + ε₁) on Q by setring Q.
      apply (flip_le_minus_l _ _ _).
      apply (le_closed_alt _ _). intros c ?.
      destruct (B₂ c _) as [y[??]].
      assert (y ∊ V₁) by now rewrite EV.
      apply (P₁ y _ _ _). now rewrite (X $ Ex).
  Qed.

  Context `{!FinitePoints X}.

  Section with_pts.
    
    Context V `{!Inhabited V} `{!Located V} x `{x ∊ X}.

    Let sub : V ⊆ X := _.

    Let invar q δ := (∀ `{ε ∊ Q₊}, ∃ `{y ∊ V}, ball (q+δ+ε) x y)
                   ∧ (∀ `{y ∊ V} `{p ∊ Q⁺}, p<q → ¬ ball p x y).

    Let bisect q `{q ∊ Q⁺} δ `{δ ∊ Q₊} : invar q δ → ∃ `{q' ∊ Q⁺}, invar q' (2*δ/3) .
    Proof. intros [P1 P2].
      destruct (located V x (q+δ/3) (q+2*δ/3)) as [[y'[??]]|P3].
      * apply (flip_pos_minus _ _).
        mc_replace (q + 2*δ/3 - (q + δ/3) ) with (δ/3) on Q by setring Q. apply _.
      * exists_sub q. split; trivial. intros ??. exists_sub y'.
        apply (ball_weaken_plus _ _ _); trivial; apply _.
      * exists_sub (q+δ/3). split.
          intros ε ?. destruct (P1 ε _) as [y[??]]. exists_sub y.
          now mc_replace (q + δ/3 + 2*δ/3) with (q + δ) on Q by decfield Q.
        intros y ? p ? E ?. apply (P3 y _).
        apply ball_weaken_le with p; trivial; try apply _. now apply (lt_le _ _).
    Qed.

    Let invar0 : ∃ `{M ∊ Q⁺}, invar 0 M.
    Proof.
      destruct (inhabited V) as [y ?].
      destruct (finite_points x y) as [M [? Bxy]].
      exists_sub M. split.
        intros ??. exists_sub y. rewrite (Q $ plus_0_l M).
        apply (ball_weaken_plus _ _ _); trivial; apply _.
      intros y' ? p ??. destruct (nonneg_not_neg p). split; trivial; apply _.
    Qed.

    Instance set_dist_family_inh ε `{ε ∊ Q₊} : Inhabited (S V x ε).
    Proof.
      destruct invar0 as [M[elM P0]].
      destruct (bisection Q Q⁺ invar bisect ε 0 M P0) as [q[?[δ[?[[P1 P2] E]]]]].
      rewrite (_ $ commutativity (.*.) _ _) in E.
      apply (mult_inv_lt_cancel_l _ _ _) in E.
      apply (flip_pos_minus _ _) in E.
      exists (q+δ/2). split. apply _. split.
      * intros c ?. destruct (P1 (ε - δ/2 + c) _) as [y[??]]. exists_sub y.
        now mc_replace (q + δ/2 + ε + c) with (q + δ + (ε - δ/2 + c)) on Q by decfield Q.
      * intros y' ? r ??. apply (le_iff_not_lt_flip  _ _). intro.
        apply (P2 y' _ r _); trivial.
        subtransitivity (q+δ/2-ε).
        apply (flip_pos_minus _ _).
        now mc_replace (q - (q + δ/2 - ε)) with (ε-δ/2) on Q by decfield Q.
    Qed.
  End with_pts.

  Existing Instance set_dist_family_inh.

  Instance: ∀ V `{!Inhabited V} `{!Located V} x `{x ∊ X}, S V x ∊ C.
  Proof. intros V ?? x ?. pose proof (_ : V ⊆ X). split. exact (sub_metric_space).
  + intros ?? E. unfold_sigs. red_sig.
    apply set_dist_family_proper_1; trivial; apply _.
  + intros ε ?. destruct (ae_decompose_pos ε) as [Eε | ?]; [| apply _].
    exists (0:Q). do 3 red. intuition.
    * destruct (inhabited V) as [y ?]. exists_sub y.
      apply (ball_weaken_le) with infty; try apply _. exact (msp_ball_inf _ _).
      apply (eq_le _ _). apply (transitivity (S:=Qfull) _ ε _); subsymmetry.
      rewrite (_ $ ae_plus_0_l _). rewrite (_ $ Eε). exact (ae_inf_plus_fin _).
    * apply (transitivity (S:=Qfull) _ 0 _); [| now destruct (_ : r ∊ Q⁺)].
      rewrite (Qfull $ ae_plus_0_l _), (Qfull $ Eε). now destruct (_ : -∞ ∊ Q∞⁻).
  + now apply set_dist_family_proper_2.
  Qed.

  Instance set_dist_family_mor : Morphism (Inhabited ⊓ Located ⇒ X ⇒ C) S.
  Proof. apply binary_morphism_proper_back.
    intros ?? [[[el1 el2][el3 el4]]E1] ?? E2. red in el1,el2,el3,el4. unfold_sigs. red_sig.
    apply set_dist_family_proper_2; trivial; apply _.
  Qed.

  Instance: MetricSpace Q⁺ := sub_metric_space.

  Notation "#" := (rationals_to_field Q R).

  Definition default_set_distance (V:set) :=
    map_limit (Y:=R⁺) (# : Q⁺ ⇀ R⁺) ∘ (S V : X ⇀ C).
  Notation d := default_set_distance.

  Hint Unfold d : typeclass_instances.

  Section spec.
    Context V `{!Inhabited V} `{!Located V}.

    Let sub : V ⊆ X := _.

    Instance: Morphism (X ⇒ C) (S V).
    Proof. apply (morphism_closed (X:=Inhabited ⊓ Located) _ _ _). Qed.

    Instance: Morphism (X ⇒ R⁺) (d V) := _.

    Hint Extern 2 (d _ _ ∊ R) => apply (_ : Subset R⁺ R) : typeclass_instances.

    Context x `{x ∊ X} q `{q ∊ Q}.

    Instance set_default_distance_closed : d V x ∊ R := _.

    Lemma set_default_distance_spec1 : (∀ `{ε ∊ Q₊}, ∃ `{y ∊ V}, ball (q+ε) x y) → d V x ≤ #q .
    Proof. intros P.
      apply (le_closed _ _). intros ε ?. subtransitivity (#(q+ε)). 2: now preserves_simplify #.
      destruct (P ε _) as [y[? Bxy]]. clear P. revert Bxy.
      set (q' := q+ε). assert (q' ∊ Q). subst q'. apply _. intro Bxy.
      pose proof (ball_nonneg _ _ _ Bxy).
      assert (q' ∊ Q⁻ → d V x ≤ # q'). intro.
        pose proof (nonneg_nonpos_0 q') as E.
        rewrite (_ $ E) in Bxy. rewrite (ball_separated _ _) in Bxy.
        rewrite (_ $ Bxy), (_ $ E).
        apply (eq_le _ _). unfold d, compose.
        apply (map_limit_const (X:=Q⁺) (X':=R⁺) (Y:=R⁺) # _ _).
        intros q'' ?. split. apply _. split. intros ??. now exists_sub y.
        intros y' ? r ? _. rewrite (_ $ plus_0_l _). apply (lt_le _ _).
        subtransitivity (0:Q). apply (_ : -q'' ∊ Q₋). apply (_ : r ∊ Q₊).
      destruct (pos_or_nonpos q'). 2:tauto.
      apply (le_iff_not_lt_flip _ _). intro E.
      destruct (archimedean_rationals_dense (#q') (d V x)) as [p[? Ep]]; trivial.
      assert (p-q' ∊ Q₊). apply (flip_pos_minus _ _). now apply (strictly_order_reflecting # _ _).
      destruct (inhabited (S V x ((p-q')/2))) as [r Hr].
      pose proof map_limit_spec (X:=Q⁺) (X':=R⁺) (Y:=R⁺) # (S V x) ((p-q')/2) r as Er.
      change (ball ((p-q')/2) (#r) (d V x)) in Er.
      destruct Hr as [? [P1 P2]].
      pose proof (P2 y _ q'  _ Bxy) as Er2. 
      apply (le_iff_not_lt_flip _ _) in Er2. destruct Er2.
      apply (flip_lt_minus_r _ _ _).
      rewrite (arch_field_ball _ _ _) in Er.
      destruct Er as [Er _]. destruct Ep as [_ Ep].
      mc_replace (q'+(p-q')/2) with (-((p-q')/2)+p) on Q by decfield Q.
      apply (strictly_order_reflecting # _ _).
      rewrite (_ $ preserves_plus _ _), (_ $ preserves_negate _).
      mc_replace (#r) with (#r - d V x + d V x) on R by setring R.
      now apply (plus_le_lt_compat _ _ _ _).
    Qed.

    Lemma set_default_distance_spec2 : d V x ≤ #q → (∀ `{ε ∊ Q₊}, ∃ `{y ∊ V}, ball (q+ε) x y).
    Proof. intros E ε ?. assert (q ∊ Q⁺). apply (reflects_nonneg #). apply _.
        split. apply _. red. subtransitivity (d V x). apply (_ : d V x ∊ R⁺).
      destruct (archimedean_rationals_dense (d V x) (#(q+ε))) as [p[? Ep]].
        apply (le_lt_trans _ (#q) _); trivial.
        apply (strictly_order_preserving # _ _). exact (pos_plus_lt_compat_r _ _).
      assert (q + ε - p ∊ Q₊). apply (flip_pos_minus _ _). now apply (strictly_order_reflecting # _ _).
      destruct (inhabited (S V x ((q+ε-p)/2))) as [r Hr].
      pose proof map_limit_spec (X:=Q⁺) (X':=R⁺) (Y:=R⁺) # (S V x) ((q+ε-p)/2) r as Er.
      change (ball ((q+ε-p)/2) (#r) (d V x)) in Er.
      destruct Hr as [? [P _]].
      cut ((r + (q + ε - p) / 2) < q+ε). intro E'.
        destruct (decompose_lt E') as [c[? Ec]].
        destruct (P c _) as [y[??]]. exists_sub y. now rewrite (_ $ Ec).
      rewrite (arch_field_ball _ _ _) in Er.
      destruct Er as [_ Er], Ep as [Ep1 Ep2].
      apply (flip_lt_minus_r _ _ _).
      mc_replace (q + ε - (q + ε - p) / 2) with ((q+ε-p)/2+p) on Q by decfield Q.
      apply (strictly_order_reflecting # _ _).
      rewrite (_ $ preserves_plus _ _).
      mc_replace (#r) with (#r - d V x + d V x) on R by setring R.
      now apply (plus_le_lt_compat _ _ _ _).
    Qed.
  End spec.

  Instance default_set_distance_correct : MetricSetDistance (R:=R) X (sd:=d).
  Proof. split. apply set_default_distance_closed.
    intros. split. now apply set_default_distance_spec1.
    now apply set_default_distance_spec2.
  Qed.
End set_distance_existence.

Hint Extern 5 (SetDistance (R:=?R) ?X) => eexact (default_set_distance (R:=R) (X:=X)) : typeclass_instances.
Hint Extern 2 (MetricSetDistance _ (sd:=default_set_distance)) => eapply @default_set_distance_correct : typeclass_instances.

Section default_distance.
  Context `{Reals (R:=R)}.
  Hint Extern 0 TheReals => eexact R : typeclass_instances.
  Notation "#" := (rationals_to_field Q R).

  Context `{MetricSpace (X:=X)}.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.

  Definition default_distance : X ⇀ X ⇀ R := λ x, set_distance {{x}}.
  Notation d := default_distance.

  Context `{!FinitePoints X} `{!LocatedPoints X}.

  Instance default_distance_correct : MetricDistance (R:=R) X (d:=d).
  Proof. split; unfold distance, d. intros ????. apply _. intros x ? y ? q ?.
    rewrite <-(metric_set_dist_spec _ _ _). split.
  + intros ? ε ?. exists_sub x. apply (ball_weaken_plus _ _ _). subsymmetry. apply _.
  + intros P. apply (ball_closed _ _ _). intros ε ?.
    destruct (P ε _) as [x'[[? E] ?]]. rewrite <-(_ $ E). subsymmetry.
  Qed.
End default_distance.

Hint Extern 2 (MetricDistance _ (d:=default_distance)) => eapply @default_distance_correct : typeclass_instances.


Definition closed_ball `{R:@TheReals A} `{Le A} `{X:AmbientSpace} `{!Distance X}
  : R ⇀ X ⇀ Sets := λ r x y, y ∊ X ∧ distance (X:=X) x y ≤ r .

Section closed_ball.
  Context `{Reals (R:=R)}.
  Hint Extern 0 TheReals => eexact R : typeclass_instances.
  Notation "#" := (rationals_to_field Q R).

  Notation d := distance.
  Context `{MetricSpace (X:=X)} `{!Distance X} `{!MetricDistance X}.

  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.

  Instance closed_ball_subsetoid r `{r ∊ R} x `{x ∊ X} : closed_ball r x ⊆ X .
  Proof. apply subsetoid_alt. apply _.
  + intros ?? E. unfold_sigs. intros [??]. split. apply _. now rewrite <-(_ $ E).
  + now intros ? [??].
  Qed.

  Instance closed_ball_mor : Morphism (R ⇒ X ⇒ (⊆ X)) closed_ball.
  Proof. apply binary_morphism_proper_back. intros r t Er x y Ex.
    unfold_sigs. red_sig. intros z. split; intros [??]; split; trivial.
    now rewrite <-(_ $ Er), <-(_ $ Ex).
    now rewrite   (_ $ Er),   (_ $ Ex).
  Qed.

  Instance closed_ball_inhabited r `{r ∊ R⁺} x `{x ∊ X} : Inhabited (closed_ball r x).
  Proof. exists x. split. apply _. rewrite (_ $ metric_dist_refl _). apply (_ : r ∊ R⁺). Qed.

  Instance closed_ball_order_preserving x `{x ∊ X} : OrderPreserving (Ble:=(⊆)) R (⊆ X) (λ r, closed_ball r x).
  Proof. split. split; try apply _.
    intros r ? s ? E. apply (subsetoid_from_subset X _ _). intros y [??].
    split; trivial. subtransitivity r.
  Qed.

  Lemma closed_ball_weaken_le r `{r ∊ R} x `{x ∊ X} s `{s ∊ R}
    : r ≤ s → closed_ball r x ⊆ closed_ball s x.
  Proof. intro E. now apply (order_preserving (Ble:=(⊆)) (T:=(⊆ X)) (λ r, closed_ball r x) _ _). Qed.

  Lemma closed_ball_rational r `{r ∊ Q} x `{x ∊ X} : closed_ball (#r) x = B r x.
  Proof. intros y; split; intros [??]; split; trivial. red.
    now rewrite (metric_dist_spec _ _ _). now rewrite <-(metric_dist_spec _ _ _).
  Qed.
 
  Lemma singleton_is_closed_ball x `{x ∊ X} : {{x}} = closed_ball 0 x.
  Proof. transitivity (B 0 x). exact (singleton_is_ball _).
    transitivity (closed_ball (#0) x). symmetry. exact (closed_ball_rational _ _).
    now destruct (binary_morphism_proper closed_ball _ _ (R $ preserves_0 (f:=#)) _ _ (_ : Proper (X,=) x)).
  Qed.
End closed_ball.

Hint Extern 2 (closed_ball (X:=?X) _ _ ⊆ ?X) => eapply @closed_ball_subsetoid : typeclass_instances.
Hint Extern 2 (Morphism _ closed_ball) => eapply @closed_ball_mor : typeclass_instances.
Hint Extern 2 (Inhabited (closed_ball _ _)) => eapply @closed_ball_inhabited : typeclass_instances.
Hint Extern 2 (OrderPreserving _ _ (λ r, closed_ball r _)) => eapply @closed_ball_order_preserving : typeclass_instances.

Lemma closed_ball_proper: Find_Proper_Signature (@closed_ball) 0
  (∀ `{Reals (R:=R)} `{MetricSpace (X:=X)} `{!Distance (R:=R) X} `{!MetricDistance (R:=R) X},
   Proper ((R,=)==>(X,=)==>(=)) (closed_ball (R:=R) (X:=X)) ).
Proof. red; intros. intros r s E1 x y E2.
  now destruct (binary_morphism_proper closed_ball (m:=closed_ball_mor (R:=R) (X:=X)) _ _ E1 _ _ E2).
Qed.
Hint Extern 0 (Find_Proper_Signature (@closed_ball) 0 _) => eexact closed_ball_proper : typeclass_instances.

Lemma closed_ball_proper2: Find_Proper_Signature (@closed_ball) 1
  (∀ `{Reals (R:=R)} `{MetricSpace (X:=X)} `{!Distance (R:=R) X} `{!MetricDistance (R:=R) X},
   Proper ((R,≤)++>(X,=)==>(⊆)) (closed_ball (R:=R) (X:=X)) ).
Proof. red; intros. intros r s E1 x y E2. unfold_sigs. rewrite <-(_ $ E2).
  now apply (closed_ball_weaken_le _ _ _).
Qed.
Hint Extern 0 (Find_Proper_Signature (@closed_ball) 1 _) => eexact closed_ball_proper2 : typeclass_instances.

Section metric.
  Context `{Reals (R:=R) (U:=UR)}.
  Hint Extern 0 TheReals => eexact R : typeclass_instances.
  Notation "#" := (rationals_to_field Q R).

  Notation d := distance.
  Context `{MetricSpace (X:=X)} `{!Distance X} `{!MetricDistance X}.

  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.

  Lemma closure_dist (S:set) `{S ⊆ X} : closure S = λ x, x ∊ X ∧
    ∀ `{ε ∊ R₊}, ∃ `{s ∊ S}, d x s ≤ ε.
  Proof. intros x. split; intros [? P]; split; trivial; intros ε ?.
  + destruct (archimedean_rationals_dense_pos ε) as [q[elq E]].
    destruct (P q _) as [s[??]]. exists_sub s.
    subtransitivity (#q). now rewrite <-(metric_dist_spec _ _ _). now apply (lt_le _ _).
  + destruct (ae_decompose_pos ε) as [Eε | ?].
      destruct (P 1 _) as [s[??]]. exists_sub s.
      rewrite (_ $ Eε). exact (msp_ball_inf _ _).
    destruct (P (#ε) _) as [s[??]]. exists_sub s.
    now rewrite (metric_dist_spec _ _ _).
  Qed.

  Lemma dense_dist (S:set) `{!Dense S} x `{x ∊ X} ε `{ε ∊ R₊} : ∃ `{s ∊ S}, d x s ≤ ε.
  Proof. pose proof (_ : x ∊ X) as el. rewrite <-dense_def in el.
    rewrite (closure_dist S) in el.
    destruct el as [_ P]. now apply P.
  Qed.

  Lemma interior_dist (S:set) `{S ⊆ X} : S° = λ x, x ∊ S ∧ ∃ `{r ∊ R₊}, Subset (closed_ball r x) S.
  Proof. intros x. split; intros [?[r[??]]]; split; trivial.
  + destruct (ae_decompose_pos r) as [Er | ?].
      exists_sub 1. transitivity X. apply _. rewrite <-(B_infty x). now rewrite <-(_ $ Er).
    exists_sub (#r). now rewrite (closed_ball_rational _ _).
  + destruct (archimedean_rationals_dense_pos r) as [q[elq E]]. exists_sub q.
    rewrite <-(closed_ball_rational _ _).
    now rewrite (R $ E).
  Qed.

  Lemma open_dist (S:set) `{!Open S} x `{x ∊ S} : ∃ `{r ∊ R₊}, closed_ball r x ⊆ S.
  Proof. pose proof (_ : S ⊆ X).
    pose proof (_ : x ∊ S) as el. rewrite <-open_def, (interior_dist S) in el.
    destruct el as [_ [r [??]]]. exists_sub r. now apply (subsetoid_from_subset X _ _).
  Qed.

  Lemma bounded_dist (S:set) `{!Bounded S} : ∃ d `{d ∊ R⁺}, ∀ `{x ∊ S} `{y ∊ S}, distance x y ≤ d.
  Proof. pose proof (_ : S ⊆ X). destruct (bounded S) as [q[elq P]].
    exists_sub (#q). intros x ? y ?. rewrite <-(metric_dist_spec _ _ _). now apply P.
  Qed.

  Lemma closed_by_dist (S:set) `{S ⊆ X} :
    (∀ `{x ∊ X}, (∀ `{ε ∊ R₊}, ∃ `{s ∊ S}, d x s ≤ ε) → x ∊ S) → Closed S.
  Proof. intro P. split; try apply _. apply subset_antisym. 2: apply _.
    rewrite (closure_dist S). intros x [??]. now apply P.
  Qed.

  Lemma open_by_dist (S:set) `{S ⊆ X} :
    (∀ `{s ∊ S}, ∃ `{r ∊ R₊}, ∀ `{x ∊ X}, d s x ≤ r → x ∊ S) → Open S.
  Proof. intro P. split; try apply _. apply subset_antisym. apply _.
    rewrite (interior_dist S). intros s ?. split. apply _.
    destruct (P s _) as [r[elr P']]. exists_sub r. intros x [??]. now apply P'.
  Qed.

  Lemma bounded_by_dist (S:set) `{S ⊆ X} d `{d ∊ R⁺} :
    (∀ `{x ∊ S} `{y ∊ S}, distance x y ≤ d) → Bounded S.
  Proof. intros P. split; try apply _.
    destruct (archimedean_rationals_bound_nonneg (F:=R) d) as [q[elq E]].
    exists_sub q. intros x ? y ?. rewrite (metric_dist_spec _ _ _).
    subtransitivity d. now apply P. now apply (lt_le _ _).
  Qed.

  Lemma set_contained_dist (U V:set) `{U ⊆ X} `{V ⊆ X} `{!SetContained U V} : ∃ r `{r ∊ R₊},
    ∀ x `{x ∊ X} u `{u ∊ U}, d x u ≤ r → x ∊ V.
  Proof. destruct (set_contained_finite U V) as [q[elq P]]. exists_sub (#q). intros x ? u ?.
    rewrite <-(metric_dist_spec _ _ _). now apply P.
  Qed.

  Lemma set_contained_by_dist (U V:set) `{U ⊆ X} `{V ⊆ X} r `{r ∊ R₊} :
    (∀ x `{x ∊ X} u `{u ∊ U}, d x u ≤ r → x ∊ V) → SetContained U V.
  Proof. intros P. destruct (archimedean_rationals_dense_pos r) as [q[elq E]]. exists_sub q.
    intros x ? u ?. rewrite (metric_dist_spec _ _ _). intro. apply (P _ _ _ _).
    subtransitivity (#q). now apply (lt_le _ _).
  Qed.

  Add Field R3 : (stdlib_field_theory R).

  Lemma prelength_dist `{!PrelengthSpace X}
     x `{x ∊ X} y `{y ∊ X} δ₁ `{δ₁ ∊ R⁺} δ₂ `{δ₂ ∊ R⁺} :
               d x y < δ₁ + δ₂ → ∃ `{z ∊ X}, d x z ≤ δ₁ ∧ d z y ≤ δ₂ .
  Proof. intro E.
    destruct (decompose_lt E) as [ε [? Eε]].
    assert (ε/2 < ε) as Eh. apply (flip_pos_minus _ _).
      mc_replace (ε - ε/2) with (ε/2) on R by setfield R. apply _.
    destruct (cotransitivity Eh δ₁) as [E1|?] .
      destruct (cotransitivity Eh δ₂) as [E2|?] .
        destruct (archimedean_rationals_dense (δ₁ - ε/2) δ₁) as [q₁[??]].
          apply (flip_lt_minus_l _ _ _). exact (pos_plus_lt_compat_r _ _).
        destruct (archimedean_rationals_dense (δ₂ - ε/2) δ₂) as [q₂[??]].
          apply (flip_lt_minus_l _ _ _). exact (pos_plus_lt_compat_r _ _).
        assert (q₁ ∊ Q₊). apply (reflects_pos #). apply _. split. apply _. red.
          subtransitivity (δ₁ - ε/2). apply (flip_pos_minus _ _) in E1. apply E1. easy.
        assert (q₂ ∊ Q₊). apply (reflects_pos #). apply _. split. apply _. red.
          subtransitivity (δ₂ - ε/2). apply (flip_pos_minus _ _) in E2. apply E2. easy.
        destruct (archimedean_rationals_dense (d x y) (#(q₁+q₂))) as [p[??]].
          mc_replace (d x y) with (d x y + ε - ε) on R by setfield R.
          rewrite <-(_ $ Eε).
          mc_replace (δ₁ + δ₂ - ε) with ((δ₁-ε/2) + (δ₂-ε/2)) on R by setfield R.
          preserves_simplify #.
          now apply (plus_lt_compat _ _ _ _).
        destruct (prelength x y p q₁ q₂) as [z[?[??]]].
          now apply (strictly_order_reflecting # _ _).
          apply (metric_dist_spec _ _ _). now apply (lt_le _ _).
        exists_sub z. split.
        subtransitivity (#q₁). now apply (metric_dist_spec _ _ _). now apply (lt_le _ _).
        subtransitivity (#q₂). now apply (metric_dist_spec _ _ _). now apply (lt_le _ _).
      exists_sub y. split.
        apply (order_reflecting (+ε) _ _). rewrite <-(_ $ Eε).
        apply (order_preserving (δ₁ +) _ _). now apply (lt_le _ _).
      rewrite (_ $ metric_dist_refl _). apply (_ : δ₂ ∊ R⁺).
    exists_sub x. split.
      rewrite (_ $ metric_dist_refl _). apply (_ : δ₁ ∊ R⁺).
    apply (order_reflecting (+ε) _ _). rewrite <-(_ $ Eε).
    rewrite (_ $ commutativity (+) δ₁ _).
    apply (order_preserving (δ₂ +) _ _). now apply (lt_le _ _).
  Qed.
End metric.

Section closed_ball_more.
  Context `{Reals (R:=R)}.
  Hint Extern 0 TheReals => eexact R : typeclass_instances.
  Instance: FullLatticeOrder R := _.
  Instance: SemiRingLatticeOrder R := _.
  Instance: LatticeAbs R := _.

  Notation d := distance.
  Context `{MetricSpace (X:=X)} {dist:Distance X} `{!MetricDistance X}.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.

  Lemma closed_ball_closed r `{r ∊ R} x `{x ∊ X} : Closed (closed_ball r x).
  Proof. apply closed_by_dist. apply _. intros y ? P. split; trivial.
    apply (le_closed_alt _ _). intros ε ?.
    destruct (P ε _) as [s[[??]?]].
    subtransitivity (d x s + d s y). exact (metric_dist_tri _ _ _).
    apply (plus_le_compat _ _ _ _); trivial.
    now rewrite (_ $ metric_dist_sym _ _).
  Qed.

  Lemma closed_ball_bounded r `{r ∊ R} x `{x ∊ X} : Bounded (closed_ball r x).
  Proof. apply bounded_by_dist with (r+r ⊔ 0); try apply _.
    intros y [??] z [??].
    apply (join_le_compat_r _ _ _) .
    subtransitivity (d y x + d x z). exact (metric_dist_tri _ _ _).
    apply (plus_le_compat _ _ _ _); trivial.
    now rewrite (_ $ metric_dist_sym _ _).
  Qed.

  Context `{!PrelengthSpace X}.

  Let located_aux {sd:SetDistance X} `{!MetricSetDistance X}
    r `{r ∊ R⁺} x `{x ∊ X} : Located (closed_ball r x) ∧ 
      set_distance (closed_ball r x) = (⊔ 0) ∘ (+ -r) ∘ (d x : X ⇀ R) .
  Proof. apply located_by_dist_fun; try apply _. intros y ?. split.
  + intros s [??]. unfold compose. apply (join_lub _ _ _).
      2: apply (_ : d s y ∊ R⁺).
    apply (flip_le_minus_l _ _ _).
    subtransitivity (d x s + d s y). exact (metric_dist_tri _ _ _).
    rewrite (_ $ commutativity (+) _ (d s y)).
    now apply (order_preserving (d s y +) _ _).
  + intros p ?. unfold compose. intro E.
    assert (p ∊ R₊). split. apply _. red.
      apply (le_lt_trans _ (d x y - r ⊔ 0) _); trivial. exact (join_ub_r _ _).
    destruct (prelength_dist x y r p) as [s[?[??]]].
      rewrite (_ $ commutativity (+) _ p).
      apply (flip_lt_minus_l _ _ _).
      apply (le_lt_trans _ (d x y - r ⊔ 0) _); trivial. exact (join_ub_l _ _).
    assert (s ∊ closed_ball r x) by now split.
    now exists_sub s.
  Qed.

  Instance: FinitePoints X := metric_dist_finite.

  Lemma closed_ball_located r `{r ∊ R⁺} x `{x ∊ X} : Located (closed_ball r x) .
  Proof. now destruct (located_aux r x). Qed.

  Lemma closed_ball_distance {sd:SetDistance X} `{!MetricSetDistance X}
    r `{r ∊ R⁺} x `{x ∊ X} y `{y ∊ X}
    : set_distance (closed_ball r x) y = d x y - r ⊔ 0 .
  Proof. destruct (located_aux r x) as [? E]. now destruct (E _ _ (_ : Proper (X,=) y)). Qed.

End closed_ball_more.

Hint Extern 2 (Closed (closed_ball _ _)) => eapply @closed_ball_closed : typeclass_instances.
Hint Extern 2 (Bounded (closed_ball _ _)) => eapply @closed_ball_bounded : typeclass_instances.
Hint Extern 5 (Located (closed_ball _ _)) => eapply @closed_ball_located : typeclass_instances.

Section maps.
  Context `{Reals (R:=R)}.
  Hint Extern 0 TheReals => eexact R : typeclass_instances.
  Notation "#" := (rationals_to_field Q R).

  Notation d := distance.
  Context `{MetricSpace (X:=X)} `{!Distance X} `{!MetricDistance X}.
  Context `{MetricSpace (X:=Y)} `{!Distance Y} `{!MetricDistance Y}.

  Lemma uniform_continuity_dist f `{!UniformlyContinuous X Y f}
    ε `{ε ∊ R₊} : ∃ `{δ ∊ R₊},
    ∀ `{x ∊ X} `{y ∊ X}, d x y ≤ δ → d (f x) (f y) ≤ ε.
  Proof. destruct (archimedean_rationals_dense_pos ε) as [q[elq E]].
    destruct (uniform_continuity_finite f q) as [δ[elδ Cf]].
    exists_sub (#δ). intros x ? y ?.
    rewrite <-(metric_dist_spec _ _ _). intro.
    subtransitivity (#q). rewrite <-(metric_dist_spec _ _ _). now apply Cf.
    now apply (lt_le _ _).
  Qed.

  Lemma uniformly_continuous_by_dist (f:X ⇀ Y) `{!Morphism (X ⇒ Y) f}
    : (∀ ε `{ε ∊ R₊}, ∃ `{δ ∊ R₊}, ∀ `{x ∊ X} `{y ∊ X}, d x y ≤ δ → d (f x) (f y) ≤ ε)
    → UniformlyContinuous X Y f.
  Proof. intro P. split; try apply _. intros ε ?.
    destruct (P (#ε) _) as [δ[elδ Cf]].
    destruct (archimedean_rationals_dense_pos δ) as [q[elq E]].
    exists_sub q. intros x ? y ?.
    rewrite 2!(metric_dist_spec _ _ _).
    intro. apply (Cf x _ y _).
    subtransitivity (#q). now apply (lt_le _ _).
  Qed.

  Lemma isometric_dist f `{!Isometry X Y f} x `{x ∊ X} y `{y ∊ X}
    : d (f x) (f y) = d x y.
  Proof. apply antisymmetry with le; try apply _;
    rewrite (le_iff_not_lt_flip _ _); intro E;
    destruct (archimedean_rationals_dense _ _ E) as [q[?[E1 E2]]];
    revert E2; setoid_rewrite <-(le_iff_not_lt_flip _ _);
    rewrite <-(metric_dist_spec _ _ _);
    apply (isometric f _ _ _);
    rewrite (metric_dist_spec _ _ _);
    now apply (lt_le _ _).
  Qed.

  Lemma isometry_by_dist (f:X ⇀ Y) `{!Morphism (X ⇒ Y) f}
    : (∀ `{x ∊ X} `{y ∊ X}, d (f x) (f y) = d x y) → Isometry X Y f.
  Proof. intro P. split; try apply _. intros ε ? x ? y ?.
    rewrite 2!(metric_dist_spec _ _ _).
    now rewrite (_ $ P x _ y _).
  Qed.

  Lemma pointwise_continuity_dist {D:set} {C:set} f `{!Continuous (X:=X) (Y:=Y) D C f}
    x `{x ∊ D} ε `{ε ∊ R₊} :  ∃ `{δ ∊ R₊}, ∀ `{y ∊ D}, d x y ≤ δ → d (f x) (f y) ≤ ε.
  Proof.
    pose proof (_ : D ⊆ X). pose proof (_ : C ⊆ Y).
    destruct (archimedean_rationals_dense_pos ε) as [q[elq E]].
    destruct (pointwise_continuity (X:=X) (Y:=Y) f x q) as [δ[elδ Cf]].
    exists_sub (#δ). intros y ?.
    rewrite <-(metric_dist_spec _ _ _). intro.
    subtransitivity (#q). rewrite <-(metric_dist_spec _ _ _). now apply Cf.
    now apply (lt_le _ _).
  Qed.
End maps.

