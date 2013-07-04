Require Import
  abstract_algebra interfaces.orders interfaces.rationals interfaces.metric_spaces
  theory.setoids theory.jections theory.fields theory.rationals
  orders.affinely_extended_field stdlib_field metric.metric_spaces metric.maps.

Local Notation AQ := TheAERationals.A.
Local Notation Q := the_ae_rationals.
Local Notation "Q∞" := (aff_ext Q).
Local Notation Qfull := (aff_ext_full Q).

Lemma family_subsetoid `{X:Subset} `{Equiv X} `{Ball X} S `{el: S ∊ CauchyFamilies X} q `{q ∊ Q∞₊}
  : S q ⊆ X.
Proof. destruct el. change ((S q) ∊ (⊆ X)). now apply (morphism_closed (X:=Q∞₊)). Qed.
Hint Extern 2 (family_to_fun _ _ ⊆ _) => eapply @family_subsetoid : typeclass_instances.

Lemma family_setoid `{X:Subset} `{Equiv X} `{Ball X} S `{el: S ∊ CauchyFamilies X} q `{q ∊ Q∞₊}
  : Setoid (S q).
Proof subsetoid_a.
Hint Extern 2 (Setoid (family_to_fun _ _)) => eapply @family_setoid : typeclass_instances.

Local Hint Extern 5 (?x ∊ ?X) => match goal with
  H : x ∊ ?S ?q |- _ => eapply (_: SubsetOf (S q) X)
end : typeclass_instances.

Local Hint Extern 5 (Cauchy ?S) => eexact (_ : S ∊ (CauchyFamilies _)) : typeclass_instances.

Section cauchy_msp.
  Context `{MetricSpace (X:=X)}.
  Local Notation C := (CauchyFamilies X).

  Lemma cauchy_family S `{S ∊ C} p `{p ∊ Q∞₊} q `{q ∊ Q∞₊} x `{x ∊ S p} y `{y ∊ S q} 
    : ball (p+q) x y.
  Proof.
    destruct (ae_decompose_pos p) as [E|?]. rewrite (_ $ E), (_ $ ae_nonneg_plus_inf_l _). exact (msp_ball_inf _ _).
    destruct (ae_decompose_pos q) as [E|?]. rewrite (_ $ E), (_ $ ae_nonneg_plus_inf_r _). exact (msp_ball_inf _ _).
    now apply cauchy_family_def.
  Qed.

  Lemma cauchy_ball_sep S `{S ∊ C} T `{T ∊ C} : cauchy_ball 0 S T ↔ S = T.
  Proof. unfold equiv, family_equiv, cauchy_ball. split.
  + intros P. intros.
    apply (ball_closed _ _ _). intros ε ?.
    destruct (P ε _) as [a[?[b[?[c[?[s[?[t[?[E B]]]]]]]]]]].
    assert ((p + a) + c + (q + b) < p + q + ε) as Er.
      rewrite (_ $ plus_0_l _) in E.
      apply (strictly_order_preserving ((p+q)+) _ _) in E.
      now mc_replace (p + a + c + (q + b)) with (p + q + (a + b + c)) on Q by subring Q.
    rewrite <- (Qfull $ Er). clear Er.
    apply (ball_triangle _ _ _ t _).
    apply (ball_triangle _ _ _ s _).
    now apply (cauchy_family S _ _). assumption. subsymmetry. now apply (cauchy_family T _ _).
  + intros E. intros.
    set (a:=ε/(2*3)). assert (a ∊ Q₊). subst a. apply _.
    destruct (cauchy_family_inhabited (S:=S) a) as [s ?].
    destruct (cauchy_family_inhabited (S:=T) a) as [t ?].
    pose proof (E a _ a _ s _ t _) as B.
    exists_sub a a (a+a) s t. split;trivial. rewrite (_ $ plus_0_l _).
    mc_replace (a + a + (a+a)) with (4*a) on Q by subring Q. apply (flip_pos_minus _ _).
    subst a. mc_replace ((ε - 4 * (ε / (2 * 3)))) with (ε/3) on Q by subfield Q. apply _.
  Qed.

  Instance: ∀ `{ε ∊ Q⁺}, SubReflexive C (cauchy_ball ε).
  Proof. intros q ? S ?. assert (cauchy_ball 0 S S) as B.
    rewrite (cauchy_ball_sep _ _). exact cauchy_family_def. revert B.
    intros P ε ?. destruct (P (q+ε) _) as [a[?[b[?[c[?[s[?[t[?[E B]]]]]]]]]]].
    exists_sub a b c s t. rewrite (_ $ plus_0_l _) in E. intuition.
  Qed.

  Instance: ∀ `{ε ∊ Q⁺}, SubSymmetric C (cauchy_ball ε).
  Proof. intros q ? S ? T ? P. intros ε ?.
    destruct (P ε _) as [a[?[b[?[c[?[s[?[t[?[E B]]]]]]]]]]].
    exists_sub b a c t s. split. now rewrite (_ $ commutativity (+) b _). subsymmetry.
  Qed.

  Lemma cauchy_ball_tri p `{p ∊ Q⁺} q `{q ∊ Q⁺} S `{S ∊ C} T `{T ∊ C} U `{U ∊ C}
      : cauchy_ball p S T → cauchy_ball q T U → cauchy_ball (p + q) S U.
  Proof.
  Proof. intros E1 E2 ε ?.
    destruct (E1 (ε/2) _) as [a [?[b [?[c [?[s [?[t [?[E1' B1]]]]]]]]]]].
    destruct (E2 (ε/2) _) as [a'[?[b'[?[c'[?[t'[?[u [?[E2' B2]]]]]]]]]]].
    exists_sub a b' (b+c+a'+c') s u. split.
    + mc_replace (a + b' + (b + c + a' + c')) with ((a+b+c) + (a'+b'+c')) on Q by subring Q.
      mc_replace (p + q + ε) with ((p + ε/2) + (q + ε/2)) on Q by subfield Q.
      now apply (plus_lt_compat _ _ _ _).
    + apply (ball_triangle _ _ _ t' _); trivial.
      mc_replace (b + c + a') with (c+(b+a')) on Q by subring Q.
      apply (ball_triangle _ _ _ t _); trivial. now apply (cauchy_family T _ _).
  Qed.

  Lemma cauchy_ball_proper_1 S `{S ∊ C} T `{T ∊ C} p `{p ∊ Q⁺} q `{q ∊ Q⁺} : p = q →
    cauchy_ball p S T → cauchy_ball q S T.
  Proof. intros E P ε ?.
    destruct (P ε _) as [a [?[b [?[c [?[s [?[t [?[E1' B1]]]]]]]]]]].
    exists_sub a b c s t. split; trivial. now rewrite <-(Q $ E).
  Qed.

  Instance cauchy_setoid: Setoid C.
  Proof. split.
  + intros x ?. apply (cauchy_ball_sep _ _). subreflexivity.
  + intros x ? y ?. rewrite <-2!(cauchy_ball_sep _ _). intro. subsymmetry.
  + intros x ? y ? z ?. rewrite <-3!(cauchy_ball_sep _ _).
    intros P1 P2. apply cauchy_ball_proper_1 with (0+0); try apply _.
    exact (plus_0_l _). revert P1 P2. apply (cauchy_ball_tri _ _ _ _ _).
  Qed.

  Instance family_ball : Ball C := alt_Build_MetricSpace_ball cauchy_ball.

  Lemma family_ball_def q `{q ∊ Q⁺} S `{S ∊ C} T `{T ∊ C} : ball q S T ↔ cauchy_ball q S T.
  Proof. unfold ball, family_ball, alt_Build_MetricSpace_ball. split.
  + intros [E|[_ P]]. destruct (ae_inf_not_el). rewrite <-(_ $ E). apply _.
    apply cauchy_ball_proper_1 with (rationals_to_field Q Q q); trivial; try apply _.
    subsymmetry. exact (to_rationals_unique id q).
  + intros P. right. intuition.
    apply cauchy_ball_proper_1 with q; trivial; try apply _.
    exact (to_rationals_unique id q).
  Qed.

  Instance cauchy_msp: MetricSpace C.
  Proof. apply alt_Build_MetricSpace; try apply _.
  + intros e1 e2 Ee x1 x2 Ex y1 y2 Ey B. unfold_sigs.
    rewrite <-(cauchy_ball_sep _ _) in Ex.
    rewrite <-(cauchy_ball_sep _ _) in Ey.
    apply (cauchy_ball_proper_1 _ _ (0+e1+0) _).
    subtransitivity e1. subring Q.
    apply (cauchy_ball_tri _ _ _ y1 _); trivial.
    apply (cauchy_ball_tri _ _ _ x1 _); trivial. subsymmetry.
  + intros. now apply cauchy_ball_sep.
  + exact cauchy_ball_tri.
  + intros q ? S ? T ? P ε ?.
    destruct (P (ε/2) _ (ε/2) _) as [a [?[b [?[c [?[s [?[t [?[E B]]]]]]]]]]].
    exists_sub a b c s t. intuition.
    now mc_replace (q + ε) with (q + ε/2 + ε/2) on Q by subfield Q.
  Qed.
End cauchy_msp.

Hint Extern 2 (Setoid (CauchyFamilies _)) => eapply @cauchy_setoid : typeclass_instances.
Hint Extern 2 (Ball (elt_type (CauchyFamilies _))) => eapply @family_ball : typeclass_instances.
Hint Extern 5 (Ball (Family _)) => eapply @family_ball : typeclass_instances.
Hint Extern 2 (MetricSpace (CauchyFamilies _)) => eapply @cauchy_msp : typeclass_instances.

Section cauchy_completion.
  Context `{MetricSpace (X:=X)}.
  Local Notation C := (CauchyFamilies X).

  Instance family_family_limit : Limit C := λ SS, family ( λ q x,
    ∃ `{a ∊ Q∞₊} `{b ∊ Q∞₊}, a + b ≤ q ∧ ∃ `{T ∊ SS a}, x ∊ T b ).

  Local Hint Extern 3 (SubsetOf _ _) => eapply @subsetoid_subset : typeclass_instances.

  Instance: ∀ `{SS ∊ CauchyFamilies C} `{q ∊ Q∞⁺}, limit SS q ⊆ X.
  Proof.
    intros. apply subsetoid_alt; [apply _ |..]; unfold limit, family_to_fun, family_family_limit.
  + intros ?? E P. unfold_sigs.
    destruct P as [a[?[b[?[E'[T [??]]]]]]].
    exists_sub a b. split; trivial. exists_sub T. now rewrite <-(X $ E).
  + intros ? [?[?[b[?[?[T[??]]]]]]]. apply _.
  Qed.

  Instance: ∀ `{SS ∊ CauchyFamilies C}, limit SS ∊ C.
  Proof. split; try apply _; unfold limit.
  + assert (∀ `{a ∊ Q∞₊} `{b ∊ Q∞₊} x, a=b → family_family_limit SS a x → family_family_limit SS b x) as P.
      intros p ? q ? x E [a[?[b[?[E'[T [??]]]]]]].  rewrite (_ $ E) in E'.
      exists_sub a b. intuition. now exists_sub T.
    intros p q E. unfold_sigs. split; [split; red; apply _|].
    split. now apply P. apply P; trivial. subsymmetry.
  + intros q ?.
    destruct (cauchy_family_inhabited (S:=SS) (q/2)) as [S ?]. pose proof _ : S ∊ C.
    destruct (cauchy_family_inhabited (S:=S) (q/2)) as [x ?].
    exists x. exists_sub (q/2) (q/2). split. now rewrite (_ $ ae_in_halves _).
    now exists_sub S.
  + intros p ? q ? x [a[?[b[?[Ex[S [??]]]]]]] y [a'[?[b'[?[Ey[T [??]]]]]]].
    destruct (ae_pos_sum_finite_bound _ _ _ Ex).
    destruct (ae_pos_sum_finite_bound _ _ _ Ey).
    apply (ball_closed _ _ _). intros ε ?.
    pose proof (cauchy_family SS a a' S T) as B. rewrite (family_ball_def _ _ _) in B.
    destruct (B ε _) as [α[?[β[?[γ[?[s[?[t[?[E B']]]]]]]]]]].
    assert (b+α + γ + (β+b') < p+q+ε) as Er.
      apply (lt_le_trans _ ((a+b)+(a'+b')+ε) _).
      mc_replace (b + α + γ + (β + b')) with ((b+b') + (α + β + γ)) on Q by subring Q.
      mc_replace (a + b + (a'+b') + ε) with ((b+b') + (a + a' + ε)) on Q by subring Q.
      now apply (strictly_order_preserving ((b+b')+) _ _).
      apply (order_preserving (+ ε) _ _). now apply (plus_le_compat _ _ _ _).
    rewrite <-(Qfull $ Er). clear Er.
    apply (ball_triangle _ _ _ t _); [| now apply (cauchy_family T _ _)].
    apply (ball_triangle _ _ _ s _); trivial. now apply (cauchy_family S _ _).
  Qed.

  Lemma family_family_limit_correct `{SS ∊ CauchyFamilies C} : FamilyLimit SS (limit SS).
  Proof. pose proof _ : limit SS ∊ C.
    intros p ? S ?. pose proof _ : S ∊ C. rewrite (family_ball_def _ _ _). intros ε ?.
    set (a:=ε/(2*3)). assert (a ∊ Q₊). subst a. apply _.
    destruct (cauchy_family_inhabited (S:=S) a) as [s ?].
    destruct (cauchy_family_inhabited (S:=limit SS) a) as [t Pt].
    exists_sub a a (p+a+a) s t. split. apply (flip_pos_minus _ _).
      mc_replace (p + ε - (a + a + (p + a + a))) with (ε-4*a) on Q by subring Q.
      subst a. mc_replace (ε - 4*(ε/(2*3))) with (ε/3) on Q by subfield Q. apply _.
    apply (ball_closed _ _ _). intros.
    destruct Pt as [q[?[b'[?[E[T[??]]]]]]].
    destruct (ae_pos_sum_finite_bound _ _ _ E).
    pose proof cauchy_family SS p q S T as B. rewrite (family_ball_def _ _ _) in B.
    destruct (B δ _) as [α[?[β[?[γ[?[s'[?[t'[?[E' B']]]]]]]]]]].
    assert (a+α + γ + (β+b') < p+a+a+δ) as Er.
      mc_replace (a+α + γ + (β+b')) with (α+β+γ + b' + a) on Q by subring Q.
      mc_replace (p + a + a + δ) with (p + a + δ + a) on Q by subring Q.
      apply (strictly_order_preserving (+a) _ _). apply (lt_le_trans _ (p + q + δ + b') _).
      now apply (strictly_order_preserving (+b') _ _).
      mc_replace (p + q + δ + b') with (q + b' + p + δ) on Q by subring Q.
      rewrite (_ $ commutativity (+) p a).
      apply (order_preserving (+δ) _ _). now apply (order_preserving (+p) _ _).
    rewrite <-(Qfull $ Er). clear Er.
    apply (ball_triangle _ _ _ t' _); [| now apply (cauchy_family T _ _)].
    apply (ball_triangle _ _ _ s' _); trivial. now apply (cauchy_family S _ _).
  Qed.

  Instance: Morphism (CauchyFamilies C ⇒ C) limit.
  Proof.
    intros SS TT E. unfold_sigs. red_sig.
    rewrite <-(cauchy_ball_sep _ _), <-(family_ball_def _ _ _).
    apply (ball_closed _ _ _). intros ε ?.
    set (a:=ε/(2*2)). assert (a ∊ Q₊). subst a. apply _.
    destruct (cauchy_family_inhabited (S:=SS) a) as [s ?].
    destruct (cauchy_family_inhabited (S:=TT) a) as [t ?].
    assert (a + (a + a) + a = 0 + ε) as E' by (subst a; subfield Q).
    apply ball_weaken_le with (a+(a+a)+a); try apply _; [| now apply (eq_le _ _)].
    apply (ball_triangle _ _ _ t _); [| now apply family_family_limit_correct ].
    apply (ball_triangle _ _ _ s _). subsymmetry. now apply family_family_limit_correct.
    now apply E.
  Qed.

  Instance cauchy_family_cmsp : CompleteMetricSpace C.
  Proof. split; try apply _. intros. apply family_family_limit_correct. Qed.

  Instance family_const : Cast X C := λ x, family (λ _, {{x}}).

  Instance: ∀ `{x ∊ X} q, x ∊ (cast X C x) q.
  Proof. intros. now split. Qed.

  Instance: ∀ `{x ∊ X}, 'x ∊ C.
  Proof. intros. split; [apply _ |..]; unfold cast, family_const, family_to_fun.
  + intros ?? E. split. split; red; apply _. reflexivity.
  + intros. exists x. apply _.
  + intros p ? q ? x' [? E1] x'' [? E2]. now rewrite (_ $ E1), (_ $ E2).
  Qed.

  Instance family_const_mor: Morphism (X ⇒ C) (').
  Proof. intros x y E. unfold_sigs. red_sig.
    unfold cast, family_const, family_to_fun.
    intros p ? q ? x' [? E1] y' [? E2]. now rewrite (_ $ E1), (_ $ E), (_ $ E2).
  Qed.

  Lemma family_const_dist S `{S ∊ C} q `{q ∊ Q∞₊} s `{s ∊ S q} : ball q S (cast X C s).
  Proof. destruct (ae_decompose_pos q) as [E|?]. subsymmetry in E.
    apply ball_weaken_le with infty; try apply _.
      exact (msp_ball_inf _ _). now apply (eq_le _ _).
    rewrite (family_ball_def _ _ _). intros ε ?.
    set (a:=ε/4). assert (a ∊ Q₊). subst a. apply _.
    destruct (cauchy_family_inhabited (S:=S) a) as [s' ?].
    exists_sub a a (q + a) s' s. split.
    + apply (flip_pos_minus _ _).
      mc_replace (q+ε - (a + a +(q+a))) with (ε-3*a) on Q by subring Q. subst a.
      rewrite <-(_ $ mult_1_r ε) at 1. rewrite <-(Q $ field_inv_r 4).
      mc_replace (ε * (4 / 4) - 3 * (ε / 4)) with (ε / 4) on Q by subring Q. apply _.
    + subsymmetry. now apply (cauchy_family S _ _).
  Qed.

  Instance family_const_dense : Dense (X:=C) (cast X C)⁺¹(X).
  Proof. split; try apply _.
    unfold closure. intros S. split. now intros [? _]. intros ?.
    split. apply _. intros. 
    destruct (cauchy_family_inhabited (S:=S) ε) as [s ?]. exists_sub (cast X C s).
    exact (family_const_dist _ _ _).
  Qed.

  Instance family_const_isometry : Isometry X C (').
  Proof. split; try apply _. intros q ? x ? y ?. rewrite (family_ball_def _ _ _).
    unfold cast, family_const. split.
  + intros ? ε ?. exists_sub (ε/3) (ε/3) q x y. split; trivial.
    apply (flip_pos_minus _ _).
    mc_replace (q + ε - (ε / 3 + ε / 3 + q)) with (ε/3) on Q by subfield Q. apply _.
  + intros P. apply (ball_closed _ _ _). intros ε ?.
    destruct (P ε _) as [a[?[b[?[c[?[x'[[? Ex][y'[[? Ey][E B]]]]]]]]]]].
    rewrite (_ $ Ex), (_ $ Ey) in B.
    assert (c < q + ε) as Er.
      subtransitivity (a+b+c). exact (pos_plus_lt_compat_l _ _).
    now rewrite <-(Qfull $ Er).
  Qed.

  Hint Extern 0 (ToCompletion X C) => eexact family_const : typeclass_instances.
  Instance cauchy_completion : Completion X C := {}.

End cauchy_completion.

Hint Extern 2 (Limit (CauchyFamilies _)) => eapply @family_family_limit : typeclass_instances.
Hint Extern 2 (CompleteMetricSpace (CauchyFamilies _)) => eapply @cauchy_family_cmsp : typeclass_instances.
Hint Extern 2 (Cast _ (CauchyFamilies _)) => eapply @family_const : typeclass_instances.
Hint Extern 2 (ToCompletion _ (CauchyFamilies _)) => eapply @family_const : typeclass_instances.
Hint Extern 2 (Completion _ (CauchyFamilies _)) => eapply @cauchy_completion : typeclass_instances.
Hint Extern 2 (Morphism _ (cast _ (CauchyFamilies _))) => eapply @family_const_mor : typeclass_instances.
Hint Extern 2 (Isometry _ _ (cast _ (CauchyFamilies _))) => eapply @family_const_isometry : typeclass_instances.
Hint Extern 2 (Inverse limit) => eapply @family_const : typeclass_instances.

Local Open Scope mc_fun_scope.

Section limit.
  Context `{CompleteMetricSpace (X:=X)}.
  Notation C := (CauchyFamilies X).

  Lemma limit_const S `{S ∊ C} x `{x ∊ X} : (∀ `{q ∊ Q₊}, x ∊ S q) → limit S = x.
  Proof. intro P. apply (ball_separated _ _). apply (ball_closed _ _ _).
    intros. rewrite (_ $ plus_0_l _). subsymmetry.
    apply (complete_msp _ _ _). exact (P _ _).
  Qed.

  Lemma family_of_limit S `{S ∊ C} : S = ' (limit S).
  Proof. apply (equal_by_ball_closed _ _). intros q ?.
    apply (ball_weaken_le (q/2+q/2) _ _); try apply _.
    destruct (cauchy_family_inhabited (S:=S) (q/2)) as [s ?].
    apply (ball_triangle _ _ _ (cast X C s) _).
    exact (family_const_dist _ _ _).
    rewrite <-(isometric (') _ _ _).
    exact (complete_msp _ _ _ _ _).
    apply (eq_le _ _). exact (ae_in_halves _).
  Qed.

  Instance limit_isometry : Isometry C X limit.
  Proof. split; try apply _. intros q ? S ? T ?.
    rewrite (isometric (cast X C) _ _ _).
    now rewrite <-(C $ family_of_limit S), <-(C $ family_of_limit T).
  Qed.

  Instance: Morphism (X ⇒ C) limit⁻¹ := _ : Morphism (X ⇒ C) (').

  Instance limit_bijection : Bijective C X limit.
  Proof. split. apply isometry_injective. apply _. split; try apply _.
    change (limit ∘ (') = id). unfold compose.
    intros ?? E. unfold_sigs. red_sig. subtransitivity x.
    apply (limit_const _ _). intros. exact (_ : x ∊ {{x}}).
  Qed.

End limit.

Hint Extern 2 (Isometry _ _ limit) => eapply @limit_isometry : typeclass_instances.
Hint Extern 5 (Bijective _ _ limit) => eapply @limit_bijection : typeclass_instances.

Section map_limit.
  Context `{MetricSpace (X:=X)} `{CompleteMetricSpace (X:=Y)}.
  Context `{X' ⊆ Y} (g:X ⇀ X') `{!Isometry X X' g}.

  Definition map_family (S : Family X) : Family Y := family (λ q, g⁺¹(S q)).
  Notation T := map_family.

  Instance: ∀ S `{S ∊ CauchyFamilies X} `{q ∊ Q∞₊}, T S q  ⊆ X' := λ S _ q _, _ : g⁺¹(S q) ⊆ X'.
  Instance: ∀ S `{S ∊ CauchyFamilies X} `{q ∊ Q∞₊}, T S q  ⊆ Y. Proof. transitivity X'; apply _. Qed. 
  Instance: ∀ S `{S ∊ CauchyFamilies X} `{q ∊ Q∞₊}, Setoid (T S q) := λ _ _ _ _, subsetoid_a.

  Lemma map_family_proper S1 `{S1 ∊ CauchyFamilies X} S2 `{S2 ∊ CauchyFamilies X}
    : S1 = S2 → T S1 = T S2.
  Proof. 
    intros E p ? q ? cx [?[x [? Ex]]] cy [?[y [? Ey]]].
    rewrite <-(Y $ Ex), <-(Y $ Ey), <-(isometric g _ _ _).
    now apply E.
  Qed.

  Instance: ∀ S `{S ∊ CauchyFamilies X}, T S ∊ CauchyFamilies Y.
  Proof. intros. split. apply _.
  + intros p q E. unfold_sigs. red_sig. change (g⁺¹(S p) = g⁺¹(S q)).
    assert (S p = S q) as E'. now rewrite (Q∞₊ $ E). now rewrite E'.
  + intros q ?. destruct (cauchy_family_inhabited (S:=S) q) as [x ?]. exists (g x).
    change (g x ∊ g⁺¹(S q)) . apply _.
  + change (T S = T S). apply (map_family_proper _ _). subreflexivity.
  Qed.

  Instance: Morphism (CauchyFamilies X ⇒ CauchyFamilies Y) map_family.
  Proof. intros S1 S2 E. unfold_sigs. red_sig. now apply map_family_proper. Qed.

  Instance: Isometry (CauchyFamilies X) (CauchyFamilies Y) map_family.
  Proof. split; try apply _. intros q ? S1 ? S2 ?.
    rewrite 2!(family_ball_def _ _ _).
    split; intros P ε ?; destruct (P ε _) as [a[?[b[?[c[?[s[els[t[elt[??]]]]]]]]]]];
      exists_sub a b c.
  + assert (g s ∊ T S1 a). change (g s ∊ g⁺¹(S1 a)) . apply _.
    assert (g t ∊ T S2 b). change (g t ∊ g⁺¹(S2 b)) . apply _.
    exists_sub (g s) (g t). split; trivial. now rewrite <-(isometric g _ _ _).
  + destruct els as [?[s'[? Es]]], elt as [?[t'[? Et]]].
    exists_sub s' t'. split; trivial. now rewrite (isometric g _ _ _), (Y $ Es), (Y $ Et).
  Qed.

  Definition map_limit := limit ∘ map_family.

  Hint Unfold map_limit : typeclass_instances.
  Instance map_limit_isometry : Isometry (CauchyFamilies X) Y map_limit := _.

  Lemma map_limit_spec S `{S ∊ CauchyFamilies X} p `{p ∊ Q∞₊} x `{x ∊ S p}
    : ball p (g x) (map_limit S).
  Proof. unfold map_limit, compose.
    assert (g x ∊ T S p). change (g x ∊ g⁺¹(S p)) . apply _.
    destruct (ae_decompose_pos p) as [Ep|?].
      rewrite (_ $ Ep). exact (msp_ball_inf _ _).
    apply complete_msp; trivial; apply _.
  Qed.

  Lemma map_limit_const S `{S ∊ CauchyFamilies X} x `{x ∊ X}
    : (∀ `{q ∊ Q₊}, x ∊ S q) → map_limit S = g x.
  Proof. intro P. unfold map_limit, compose. apply (limit_const _ _).
    intros. change (g x ∊ g⁺¹(S q)) . apply _.
  Qed.

  Hint Extern 0 AmbientSpace => eexact Y : typeclass_instances.

  Context `{!Closed X'}.

  Definition map_limit_closed := map_limit : CauchyFamilies X ⇀ X'.

  Hint Unfold map_limit_closed : typeclass_instances.

  Instance: ∀ S `{S ∊ CauchyFamilies X}, map_limit_closed S ∊ X'.
  Proof. intros. rewrite <-(closed X'). split. apply _.
    intros q ?. destruct (cauchy_family_inhabited (S:=S) q) as [x ?].
    exists_sub (g x). subsymmetry. exact (map_limit_spec _ _ _).
  Qed.

  Instance: Morphism (CauchyFamilies X ⇒ X') map_limit_closed.
  Proof. intros ?? E. unfold_sigs. red_sig. now rewrite (CauchyFamilies X $ E). Qed.

  Instance map_limit_closed_iso `{!Closed (X:=Y) X'} : Isometry (CauchyFamilies X) X' map_limit.
  Proof. split; try apply _. exact sub_metric_space. exact (isometric_def _ _). Qed.

End map_limit.

Hint Extern 2 (Isometry _ _ (map_limit _)) => eapply @map_limit_isometry : typeclass_instances.
Hint Extern 2 (Morphism _ (map_limit _)) => eapply @isometry_mor : typeclass_instances.
Hint Extern 2 (Isometry _ _ (map_limit_closed _)) => eapply @map_limit_closed_iso : typeclass_instances.
Hint Extern 2 (Morphism _ (map_limit_closed _)) => eapply @isometry_mor : typeclass_instances.

Section subspace.
  Context `{CompleteMetricSpace (X:=X)}.
  Hint Extern 0 AmbientSpace => eexact X  : typeclass_instances.

  Context U `{!Closed U}.

  Instance : MetricSpace U := sub_metric_space.

  Instance subspace_limit : Limit U := map_limit_closed (id:U ⇀ U).
  Instance complete_subspace : CompleteMetricSpace U.
  Proof. split; unfold limit,subspace_limit; try apply _.
    intros S ? p ? x ?. exact (map_limit_spec (id:U ⇀ U) S p x).
  Qed.
End subspace.
