Require Import
  abstract_algebra interfaces.orders interfaces.metric_spaces interfaces.rationals interfaces.reals
  theory.setoids
  orders.fields orders.affinely_extended_field orders.abs
  metric.metric_spaces metric.maps_continuous metric.prelength metric.cauchy_completion metric.distance
  theory.rings
  orders.archimedean_fields
  theory.rationals theory.reals orders.reals
  stdlib_field stdlib_field_dec misc.quote.

Local Notation AQ := TheAERationals.A.
Local Notation Q := the_ae_rationals.
Local Notation "Q∞" := (aff_ext Q).
Local Notation Qfull := (aff_ext_full Q).


(** Richman's regular family of subsets *)

Inductive RealFamily `{R:@TheReals AR} `{Zero AR} `{Lt AR}
  `(X:@set A) `{Equiv X} := real_family : (R₊ ⇀ (⊆ X)) → RealFamily X.
Arguments real_family {_ _ _ _ _ X _} _.
Definition real_family_to_fun `{R:@TheReals AR} `{Zero AR} `{Lt AR}
  `{X:@set A} `{Equiv X} (x : RealFamily X)
  := match x with real_family f => (f:AR→@set A) end.
Coercion real_family_to_fun : RealFamily >-> Funclass.

Section Cauchy.
  Context `{R:@TheReals AR} `{Reals _ (R:=R)}.
  Context `{X:set} `{Equiv X} `{!Distance X}.

  Class RealCauchy (S:RealFamily X) : Prop :=
  { real_cauchy_family_mor : Morphism (R₊ ⇒ (⊆ X)) S
  ; real_cauchy_family_inhabited ε `{ε ∊ R₊} : Inhabited (S ε)
  ; real_cauchy_family_def ε₁ `{ε₁ ∊ R₊} ε₂ `{ε₂ ∊ R₊} x `{x ∊ S ε₁} y `{y ∊ S ε₂}
      : distance x y ≤ ε₁ + ε₂
  }.

  Definition RealFamilyLimit (S:RealFamily X) y := ∀ ε `{ε ∊ R₊} x  `{x ∊ S ε}, distance x y ≤ ε.

  Instance real_family_equiv : Equiv (RealFamily X) := λ S T,
    ∀ ε₁ `{ε₁ ∊ R₊} ε₂ `{ε₂ ∊ R₊} x `{x ∊ S ε₁} y `{y ∊ T ε₂},
      distance x y ≤ ε₁ + ε₂.
End Cauchy.

Definition RealCauchyFamilies `{R:@TheReals AR} `{Plus AR} `{Zero AR} `{Equiv AR} `{Lt AR} `{Le AR}
  `(X:set) `{Equiv X} `{!Distance (R:=R) X} := RealCauchy : set.

Hint Extern 10 (@set (RealFamily (R:=?R) ?X)) => eexact (RealCauchyFamilies (R:=R) X) : typeclass_instances.

Hint Extern 2 (Equiv (RealFamily (R:=?R) _)) => eapply (@real_family_equiv _ R) : typeclass_instances.
Hint Extern 2 (Equiv (elt_type (RealCauchyFamilies (R:=?R) _))) => eapply (@real_family_equiv _ R) : typeclass_instances.
Hint Extern 0 (Proper (_ ==> _) (real_family_to_fun (R:=?R) _)) =>
   eapply (real_cauchy_family_mor (R:=R) : Proper ((R₊,=) ==> ((⊆ _),=)) (real_family_to_fun _)) : typeclass_instances.

Local Hint Extern 5 (RealCauchy (R:=?R) (X:=?X) ?S) => eexact (_ : S ∊ (RealCauchyFamilies (R:=R) X)) : typeclass_instances.

Local Hint Extern 5 (?x ∊ ?X) => match goal with
  H : x ∊ ?S ?q |- _ => eapply (_: Subset (S q) X)
end : typeclass_instances.

Definition real_family_to_family
  `{R:@TheReals AR} `{Plus AR} `{Mult AR} `{Zero AR} `{One AR} `{Negate AR} `{Inv AR} `{Equiv AR} `{Lt AR} `{Le AR}
  `(X:@set A) `{Equiv X} `{Ball X} `{!Distance X}
  : RealCauchyFamilies X ⇀ CauchyFamilies X := 
  λ S, family (λ q x, (q = ∞ ∧ x ∊ X) ∨ (q ∊ Q₊ ∧ x ∊ S (rationals_to_field Q R q))).

Definition family_to_real_family
  `{R:@TheReals AR} `{Plus AR} `{Mult AR} `{Zero AR} `{One AR} `{Negate AR} `{Inv AR} `{Equiv AR} `{Lt AR} `{Le AR}
  `(X:@set A) `{Equiv X} `{Ball X} `{!Distance X}
  : CauchyFamilies X ⇀ RealCauchyFamilies X := 
  λ S, real_family (R:=R) (λ ε x, x ∊ X ∧ ∀ `{q ∊ Q}, ε < rationals_to_field Q R q → ball q (cast X (CauchyFamilies X) x) S).

Definition real_family_limit
  `{R:@TheReals AR} `{Plus AR} `{Mult AR} `{Zero AR} `{One AR} `{Negate AR} `{Inv AR} `{Equiv AR} `{Lt AR} `{Le AR}
  `(X:@set A) `{Equiv X} `{Ball X} `{!Distance X} `{!Limit X}
  : RealCauchyFamilies X ⇀ X :=
  limit ∘ (real_family_to_family (R:=R) X).

Section real_family_to_rational.
  Context `{Reals (R:=R)}.
  Hint Extern 0 TheReals => eexact R : typeclass_instances.
  Notation "#" := (rationals_to_field Q R).
  Add Ring R'' : (stdlib_ring_theory R).

  Notation d := distance.
  Context `{MetricSpace (X:=X)} `{!Distance X} `{!MetricDistance X}.

  Notation RC := (RealCauchyFamilies (R:=R) X).
  Notation C := (CauchyFamilies X).

  Instance real_family_subsetoid S `{el: S ∊ RC} ε `{ε ∊ R₊} : S ε ⊆ X.
  Proof. destruct el. change ((S ε) ∊ (⊆ X)). now apply (morphism_closed (X:=R₊)). Qed.

  Lemma real_family_setoid S `{el: S ∊ RC} ε `{ε ∊ R₊} : Setoid (S ε).
  Proof _.

  Notation f := (real_family_to_family (R:=R) X).

  Let aux1 S `{S ∊ RC} q `{q ∊ Q∞₊} : q = ∞ → f S q = X.
  Proof. intro Eq.
    assert (¬q ∊ Q₊). intro. destruct (ae_inf_not_el). rewrite <-(_ $ Eq). apply _.
    split. intros [?|?]; intuition. intro. left. intuition.
  Qed.

  Lemma real_family_to_family_rational S `{S ∊ RC} q `{q ∊ Q₊} : f S q = S (#q).
  Proof.
    assert (¬q = ∞). intro Eq. destruct (ae_inf_not_el). rewrite <-(_ $ Eq). apply _.
    split. intros [?|?]; intuition. intro. right. intuition.
  Qed.
  Notation aux2 := real_family_to_family_rational.

  Instance: ∀ S `{S ∊ RC} q `{q ∊ Q∞₊}, f S q ⊆ X.
  Proof. intros S el q ?. destruct (ae_decompose_pos q) as [Eq|?].
  + rewrite (aux1 S q Eq). apply _.
  + rewrite (aux2 S q). apply _.
  Qed.

  Instance: ∀ S, S ∊ RC → f S ∊ C.
  Proof. intros S el. split. apply _.
  + intros p q E. unfold_sigs. red_sig.
    destruct (ae_decompose_pos q) as [Eq|?].
      assert (p = ∞) as Ep. subtransitivity q.
      now rewrite (aux1 _ _ Ep), (aux1 _ _ Eq).
    assert (p ∊ Q₊) by now rewrite (_ $ E).
    rewrite 2!(aux2 _ _).
    assert (#p = #q) as E' by now rewrite (_ $ E).
    now destruct (real_cauchy_family_mor _ _ (_ $ E')).
  + intros q ?.
    destruct (ae_decompose_pos q) as [Eq|?].
      rewrite (aux1 _ _ Eq).
      destruct (real_cauchy_family_inhabited 1). exists x. now apply (_ : S 1 ⊆ X).
    rewrite (aux2 _ _). exact (real_cauchy_family_inhabited _).
  + intros p ? q ? x elx y ely.
    rewrite (aux2 _ _) in elx. rewrite (aux2 _ _) in ely.
    rewrite (metric_dist_spec _ _ _). preserves_simplify #.
    exact (real_cauchy_family_def _ _ _ _).
  Qed.

  Instance: ClosedFun (RC ⇀ C) f.
  Proof. intros ??. apply _. Qed.

  Instance real_family_to_family_mor : Morphism (RC ⇒ C) f.
  Proof. intros S T E. unfold_sigs. red_sig. revert E.
    unfold equiv, real_family_equiv, family_equiv.
    intros E p ? q ? x elx y ely.
    rewrite (aux2 _ _) in elx. rewrite (aux2 _ _) in ely.
    rewrite (metric_dist_spec _ _ _). preserves_simplify #.
    apply (E _ _ _ _ _ _ _ _).
  Qed.

  Instance real_family_to_family_inj: Injective RC C f.
  Proof. split; [| apply _]. intros S ? T ?.
    unfold equiv, real_family_equiv, family_equiv.
    intros E r ? s ? x elx y ely.
    apply (le_closed _ _). intros a ?.
    set (ε := a/4). assert (ε ∊ Q₊). unfold ε. apply _.
    subtransitivity ( (r+#ε)+(#ε+#ε)+(#ε+s) ).
      destruct (real_cauchy_family_inhabited (S:=S) (#ε)) as [x' elx'].
      destruct (real_cauchy_family_inhabited (S:=T) (#ε)) as [y' ely'].
      subtransitivity (d x x' + d x' y' + d y' y).
      subtransitivity (d x y' + d y' y).
      exact (metric_dist_tri x y' y).
      apply (order_preserving (+ (distance (R:=R) y' y)) (d x y')). apply _.
      exact (metric_dist_tri x x' y').
      apply (plus_le_compat _ _ _ _).
      apply (plus_le_compat _ _ _ _).
      apply (real_cauchy_family_def (S:=S) _ _ _ _).
      rewrite <-(aux2 _ _) in elx'. rewrite <-(aux2 _ _) in ely'.
        subtransitivity (#(ε+ε)). 2: now preserves_simplify #.
        rewrite <-(metric_dist_spec _ _ _). now apply E.
      apply (real_cauchy_family_def (S:=T) _ _ _ _).
    apply (eq_le _ _). cut (a = ε*4). intro E'. rewrite (_ $ E').
      preserves_simplify #. setring R.
    apply (fields.mult_inv_cancel_l _ _ _). now subst ε.
  Qed.

  Instance real_cauchy_families_setoid : Setoid RC.
  Proof. apply (projected_setoid f). intros S ? T ?. split.
  + intro E. rewrite (RC $ E). subreflexivity.
  + apply (injective f _ _).
  Qed.

  Instance real_cauchy_families_ball : Ball RC := projected_ball f.
  Instance real_cauchy_families_msp  : MetricSpace RC := projected_metric_space f.

  Notation g := (family_to_real_family (R:=R) X).

  Instance: ∀ S `{S ∊ C} ε `{ε ∊ R₊}, g S ε ⊆ X.
  Proof. intros S ? ε ?. apply subsetoid_alt. apply _.
  + intros x y E [? P]. unfold_sigs. split; trivial. intros q ? E'. rewrite <-(_ $ E). now apply P.
  + now intros ? [??].
  Qed.
  
  Let aux_proper1a S `{S ∊ C} r `{r ∊ R₊} s `{s ∊ R₊} : r = s → Subset (g S r) (g S s).
  Proof. intros E x [? P]. split; trivial. intros q ??. apply (P q _). now rewrite (_ $ E). Qed.

  Let aux_proper1 S `{S ∊ C} r `{r ∊ R₊} s `{s ∊ R₊} : r = s → g S r = g S s.
  Proof. intro E. apply subset_antisym; apply (aux_proper1a _ _ _); trivial; subsymmetry. Qed.

  Let aux_rel S `{S ∊ C} ε `{ε ∊ R₊} q `{q ∊ Q₊} : #q ≤ ε → S q ⊆ g S ε .
  Proof. intro E. apply (subsetoid_from_subset X _ _). intros x ?. split. apply _.
    intros p ? E2. apply (ball_weaken_le) with q; try apply _.
      subsymmetry. apply (family_const_dist _ _ _).
    apply (order_reflecting # _ _). subtransitivity ε. now apply (lt_le _ _).
  Qed.

  Let aux_proper2 S `{S ∊ C} T `{T ∊ C} : S = T → g S = g T.
  Proof. intros E r ? s ? x [? Px] y [? Py].
    apply (le_closed _ _). intros a ?.
    set (ε := a/2). assert (ε ∊ Q₊). unfold ε. apply _.
    assert (r + s + #a = (r+#ε)+(s+#ε)) as E'.
      cut (a = ε+ε). intro E'. rewrite (_ $ E'). preserves_simplify #. setring R.
      subst ε. decfield Q.
    rewrite (_ $ E'). clear E'.
    destruct (archimedean_rationals_dense r (r+#ε)) as [p[? [Ep1 Ep2]]].
      apply (pos_plus_lt_compat_r _ _).
    destruct (archimedean_rationals_dense s (s+#ε)) as [q[? [Eq1 Eq2]]].
      apply (pos_plus_lt_compat_r _ _).
    subtransitivity (#(p + q)).
      rewrite <-(metric_dist_spec _ _ _).
      apply (isometric (cast X (CauchyFamilies X)) _ _ _).
      apply (ball_triangle _ _ _ S _).
        now apply (Px _ _).
      rewrite (C $ E). subsymmetry. now apply (Py _ _).
    preserves_simplify #. apply (lt_le _ _). now apply (plus_lt_compat _ _ _ _).
  Qed.

  Instance: ∀ S, S ∊ C → g S ∊ RC.
  Proof. intros S ?. split.
  + intros r s ?. unfold_sigs. red_sig. now apply aux_proper1.
  + intros ε ?. destruct (archimedean_rationals_dense_pos ε) as [q[elq E]].
    rewrite <-(aux_rel S ε q (lt_le _ _ E)).
    exact (cauchy_family_inhabited (Cauchy := (_ : S ∊ C)) q).
  + apply (aux_proper2 _ _). subreflexivity.
  Qed.

  Instance family_to_real_family_mor : Morphism (C ⇒ RC) g.
  Proof. intros S T E. unfold_sigs. red_sig. now apply aux_proper2. Qed.

  Hint Extern 0 (Inverse f) => eexact g : typeclass_instances.

  Instance real_family_to_family_bij : Bijective RC C f.
  Proof. split. apply _. split; try apply _. unfold inverse. intros S T E. unfold compose.
    unfold_sigs. red_sig. subtransitivity S. clear dependent T.
    intros p ? q ? x elx y ely. rewrite (aux2 _ _) in elx.
    destruct elx as [? Px].
    apply (isometric (cast X (CauchyFamilies X)) _ _ _).
    apply (ball_triangle _ _ _ S _).
      apply (ball_closed _ _ _). intros δ ?. apply (Px _ _).
      apply (strictly_order_preserving # _ _).
      apply ( pos_plus_lt_compat_r _ _).
    apply (family_const_dist _ _ _).
  Qed.

  Instance real_family_to_family_iso : Isometry RC C f.
  Proof. split; try apply _. tauto. Qed.

  Instance family_to_real_family_iso : Isometry C RC g.
  Proof _ : Isometry C RC (inverse f).

  Instance real_cauchy_families_limit : Limit RC := g ∘ map_limit f.

  Instance real_cauchy_families_cmsp  : CompleteMetricSpace RC.
  Proof. split; unfold limit, real_cauchy_families_limit; try apply _.
    unfold compose. intros SS ? p ? T ?.
    apply (isometric f _ _ _).
    pose proof (jections.surjective_applied f (map_limit f SS)) as E. unfold inverse in E.
    rewrite (C $ E).
    apply (map_limit_spec _ _ _ _).
  Qed.

  Instance real_family_const : Cast X RC := g ∘ (cast X C).

  Instance real_family_const_mor: Morphism (X ⇒ RC) (').
  Proof. unfold cast, real_family_const. apply _. Qed.

  Instance real_family_const_iso: Isometry X RC (').
  Proof. unfold cast, real_family_const. apply _. Qed.

  Instance real_family_const_dense : Dense (X:=RC) (cast X RC)⁺¹(X).
  Proof. unfold cast, real_family_const.
     eapply @dense_compose_iso; try apply _.
       eapply @family_const_dense; apply _.
     cut (g⁺¹(C) = RC). intro E. rewrite E. apply _.
     intros S. split. now intros [??]. intros ?. split; trivial.
     exists_sub (f S). now pose proof (jections.bijective_applied f S).
  Qed.

  Hint Extern 0 (ToCompletion X RC) => eexact real_family_const : typeclass_instances.
  Instance real_cauchy_completion : Completion X RC := {}.

  Existing Instance metric_dist_finite.
  Existing Instance metric_dist_located.

  Instance real_cauchy_fp : FinitePoints RC.
  Proof finite_points_completion (X:=X).

  Instance real_cauchy_lp : LocatedPoints RC.
  Proof located_points_completion (X:=X).

  Instance real_cauchy_distance : Distance RC := default_distance.
  Instance real_cauchy_distance_correct : MetricDistance RC.
  Proof default_distance_correct.

  Lemma real_family_const_dist S `{S ∊ RC} ε `{ε ∊ R₊} s `{s ∊ S ε} : d S (cast X RC s) ≤ ε.
  Proof.
    apply (le_closed _ _). intros a ?.
    set (q := a/2). assert (q ∊ Q₊). unfold q. apply _.
    assert (ε + #a = #q+(#q+ε)) as E'.
      cut (a = q+q). intro E'. rewrite (_ $ E'). preserves_simplify #.
      rewrite (_ $ commutativity (+) _ _). subsymmetry. exact (associativity (+) _ _ _). 
      subst q. decfield Q.
    rewrite (_ $ E'). clear E'.
    destruct (real_cauchy_family_inhabited (#q)) as [y ely].
    subtransitivity (d S (cast X RC y) + d (cast X RC y) (cast X RC s)).
      exact (metric_dist_tri _ _ _).
    apply (plus_le_compat _ _ _ _).
      rewrite <-(metric_dist_spec _ _ _).
      apply (isometric f _ _ _).
      rewrite <-(aux2 S _ _) in ely.
      cut (f (cast X RC y) = cast X C y). intro E. rewrite (_ $ E).
        apply (family_const_dist _ _ _).
      now pose proof (jections.surjective_applied f (cast X C y)).
    rewrite (_ $ isometric_dist (cast X RC) _ _).
    apply (real_cauchy_family_def (S:=S) _ _ _ _).
  Qed.

End real_family_to_rational.

Hint Extern 2 (real_family_to_fun (R:=?R) _ _ ⊆ _) => eapply (@real_family_subsetoid _ R) : typeclass_instances.
Hint Extern 2 (Setoid (real_family_to_fun (R:=?R) _ _)) => eapply (@real_family_setoid _ R) : typeclass_instances.
Hint Extern 2 (Morphism _ (real_family_to_family (R:=?R) _)) => eapply (@real_family_to_family_mor _ R) : typeclass_instances.
Hint Extern 2 (Isometry _ _ (real_family_to_family (R:=?R) _)) => eapply (@real_family_to_family_iso _ R) : typeclass_instances.
Hint Extern 2 (Inverse (real_family_to_family (R:=?R) ?X)) => eexact (family_to_real_family (R:=R) X) : typeclass_instances.
Hint Extern 2 (Bijective _ _ (real_family_to_family (R:=?R) _)) => eapply (@real_family_to_family_bij _ R) : typeclass_instances.

Hint Extern 2 (Morphism _ (family_to_real_family (R:=?R) _)) => eapply (@family_to_real_family_mor _ R) : typeclass_instances.

Hint Extern 2 (Setoid (RealCauchyFamilies (R:=?R) _)) => eapply (@real_cauchy_families_setoid _ R): typeclass_instances.
Hint Extern 2 (Ball (elt_type (RealCauchyFamilies (R:=?R) _))) => eapply (@real_cauchy_families_ball _ R) : typeclass_instances.
Hint Extern 5 (Ball (RealFamily (R:=?R) _)) => eapply (@real_cauchy_families_ball _ R) : typeclass_instances.
Hint Extern 2 (MetricSpace (RealCauchyFamilies (R:=?R) _)) => eapply (@real_cauchy_families_msp _ R) : typeclass_instances.
Hint Extern 2 (Limit (RealCauchyFamilies (R:=?R) _)) => eapply (@real_cauchy_families_limit _ R) : typeclass_instances.
Hint Extern 2 (CompleteMetricSpace (RealCauchyFamilies (R:=?R) _)) => eapply (@real_cauchy_families_cmsp _ R) : typeclass_instances.

Hint Extern 2 (Cast _ (RealCauchyFamilies (R:=?R) _)) => eapply (@real_family_const _ R) : typeclass_instances.
Hint Extern 2 (ToCompletion _ (RealCauchyFamilies (R:=?R) _)) => eapply (@real_family_const _ R) : typeclass_instances.
Hint Extern 2 (Completion _ (RealCauchyFamilies (R:=?R) _)) => eapply (@real_cauchy_completion _ R) : typeclass_instances.
Hint Extern 2 (Morphism _ (cast _ (RealCauchyFamilies (R:=?R) _))) => eapply (@real_family_const_mor _ R) : typeclass_instances.
Hint Extern 2 (Isometry _ _ (cast _ (RealCauchyFamilies (R:=?R) _))) => eapply (@real_family_const_iso _ R) : typeclass_instances.
Hint Extern 2 (Inverse (real_family_limit (R:=?R))) => eapply (@real_family_const _ R) : typeclass_instances.

Hint Extern 2 (Distance (R:=?R) (RealCauchyFamilies (R:=?R) _))  => eapply (@real_cauchy_distance _ R) : typeclass_instances.
Hint Extern 2 (MetricDistance (R:=?R) (RealCauchyFamilies (R:=?R) _))  => eapply (@real_cauchy_distance_correct _ R) : typeclass_instances.

Section real_family_limit.
  Context `{Reals (R:=R)}.
  Hint Extern 0 TheReals => eexact R : typeclass_instances.
  Notation "#" := (rationals_to_field Q R).

  Notation d := distance.
  Context `{CompleteMetricSpace (X:=X)} `{!Distance X} `{!MetricDistance X}.

  Notation RC := (RealCauchyFamilies (R:=R) X).
  Notation C := (CauchyFamilies X).

  Notation f := (real_family_to_family (R:=R) X).
  Notation lim := (real_family_limit (R:=R) X).

  Instance real_family_limit_mor : Morphism (RC ⇒ X) lim.
  Proof. unfold real_family_limit. apply _. Qed.

  Instance real_family_limit_iso : Isometry RC X lim.
  Proof. unfold real_family_limit. apply _. Qed.

  Lemma real_family_limit_const S `{S ∊ RC} x `{x ∊ X} : (∀ `{ε ∊ R₊}, x ∊ S ε) → lim S = x.
  Proof. intro P. apply limit_const; try apply _. intros q ?.
    rewrite (real_family_to_family_rational (R:=R) S _ _). exact (P _ _).
  Qed.

  Lemma real_family_of_limit S `{S ∊ RC} : S = ' (lim S).
  Proof. apply (injective f _ _).
    unfold cast, real_family_const, real_family_limit, compose.
    subtransitivity (cast X C (limit (f S))).
      exact (family_of_limit _).
    subsymmetry. now pose proof (jections.surjective_applied f (cast X C (limit (f S)))).
  Qed.

  Lemma real_family_limit_spec S `{S ∊ RC} : RealFamilyLimit S (lim S).
  Proof. intros ε ? x ?.
    rewrite <-(R $ isometric_dist (cast X RC) _ _).
    rewrite <-(RC $ real_family_of_limit S).
    rewrite (R $ metric_dist_sym _ _).
    apply (real_family_const_dist _ _ _).
  Qed.
End real_family_limit.

Hint Extern 2 (Morphism _ (real_family_limit (R:=?R) _)) => eapply (@real_family_limit_mor _ R) : typeclass_instances.
Hint Extern 2 (Isometry _ _ (real_family_limit (R:=?R) _)) => eapply (@real_family_limit_iso _ R) : typeclass_instances.

