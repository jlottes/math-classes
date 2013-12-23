Require Import
  abstract_algebra interfaces.orders interfaces.archimedean_fields interfaces.metric_spaces
  interfaces.rationals the_ae_rationals
  theory.setoids theory.products theory.fields theory.rationals orders.fields orders.rationals
  metric.metric_spaces metric.maps_continuous metric.prelength metric.products
  cauchy_completion metric.complete metric.continuity
  metric.archimedean_fields
  stdlib_field_dec misc.quote.
Require Export
  arch_field_completion_ops.

Local Notation AQ := TheAERationals.A.
Local Notation Q := the_ae_rationals.
Local Notation "Q∞" := (aff_ext Q).
Local Notation Qfull := (aff_ext_full Q).

Local Open Scope grp_scope.

Section contents.
  Context `{ArchimedeanField A1 (F:=F)} `{Ball F} `{!ArchimedeanField_Metric F}.
  Context `{R:@set A2} {Re:Equiv R} {Rue:UnEq R} {Rball:Ball R} {Rlimit:Limit R}.
  Context `{!ToCompletion F R} `{!Completion F R} `{!MetricInequality R}.

  Hint Extern 0 AmbientSpace => eexact F : typeclass_instances.
  Hint Extern 0 AmbientSpace => eexact R : typeclass_instances.

  Hint Extern 0 (Zero   A2) => eexact (Creals_zero   (F:=F) (R:=R)) : typeclass_instances.
  Hint Extern 0 (One    A2) => eexact (Creals_one    (F:=F) (R:=R)) : typeclass_instances.
  Hint Extern 0 (Negate A2) => eexact (Creals_negate (F:=F) (R:=R)) : typeclass_instances.
  Hint Extern 0 (Plus   A2) => eexact (Creals_plus   (F:=F) (R:=R)) : typeclass_instances.
  Hint Extern 0 (Mult   A2) => eexact (Creals_mult   (F:=F) (R:=R)) : typeclass_instances.
  Hint Extern 0 (Inv    A2) => eexact (Creals_inv    (F:=F) (R:=R)) : typeclass_instances.
  Hint Extern 0 (Le     A2) => eexact (Creals_le     (F:=F) (R:=R)) : typeclass_instances.
  Hint Extern 0 (Lt     A2) => eexact (Creals_lt     (F:=F) (R:=R)) : typeclass_instances.
  Hint Extern 0 (Zero   (elt_type R)) => eexact (Creals_zero   (F:=F) (R:=R)) : typeclass_instances.
  Hint Extern 0 (One    (elt_type R)) => eexact (Creals_one    (F:=F) (R:=R)) : typeclass_instances.
  Hint Extern 0 (Negate (elt_type R)) => eexact (Creals_negate (F:=F) (R:=R)) : typeclass_instances.
  Hint Extern 0 (Plus   (elt_type R)) => eexact (Creals_plus   (F:=F) (R:=R)) : typeclass_instances.
  Hint Extern 0 (Mult   (elt_type R)) => eexact (Creals_mult   (F:=F) (R:=R)) : typeclass_instances.
  Hint Extern 0 (Inv    (elt_type R)) => eexact (Creals_inv    (F:=F) (R:=R)) : typeclass_instances.
  Hint Extern 0 (Le     (elt_type R)) => eexact (Creals_le     (F:=F) (R:=R)) : typeclass_instances.
  Hint Extern 0 (Lt     (elt_type R)) => eexact (Creals_lt     (F:=F) (R:=R)) : typeclass_instances.

  Notation "#" := (to_completion F R).

  Context `{!Field R} `{!SemiRing_Morphism F R #}.
  Context `{!Isometry R R (-)}.
  Context `{!UniformlyContinuous (R*R) R (uncurry (+) : R*R ⇀ R)}.
  Context `{!Continuous (R*R) R (uncurry (.*.) : R*R ⇀ R)}.
  Context `{!Continuous (R ₀) (R ₀) (⁻¹)}.

  Instance: FinitePoints R := finite_points_completion.
  Instance: LocatedPoints R := located_points_completion.
  Instance: StrongSetoid R := metric_inequality_strong_setoid.

  Instance: StrongInjective F R #. Proof isometry_str_injective _.
  Instance: Strong_Morphism F R #. Proof strong_injective_mor _.

  Add Ring R : (stdlib_ring_theory R).

  Instance: ∀ `{a ∊ F}, Isometry R R ((#a) +).
  Proof. intros a ?. apply (extend_isometry (((#a) +):R⇀R) #⁺¹(F) ).
    split. exact (sub_metric_space). apply _.
      rewrite <-(_ : Subset (R ⇒ R) (#⁺¹(F) ⇒ R)). apply _.
    intros ε ? x' [?[x[? Ex]]] y' [?[y[? Ey]]].
    rewrite <-(R $ Ex), <-(R $ Ey), <-2!(R $ preserves_plus _ _).
    rewrite <-2!(isometric # _ _ _).
    exact (isometric (a+) _ _ _).
  Qed.

  Instance: ∀ `{a ∊ R}, Isometry R R (a +).
  Proof. split; try apply _. intros ε ? x ? y ?. split.
  + intro B. apply (ball_closed _ _ _). intros δ ?.
    mc_replace (ε + δ) with (δ/2 + ε + δ/2) on Q by decfield Q.
    destruct (uniform_continuity (+x) (δ/2)) as [δ1[el1 C1]].
    destruct (uniform_continuity (+y) (δ/2)) as [δ2[el2 C2]].
    ae_rat_set_min q δ1 δ2 E1 E2.
    destruct (dense_image # F a q) as [b[??]].
    apply (ball_triangle _ _ _ (#b + y) _).
    apply (ball_triangle _ _ _ (#b + x) _).
    apply (C1 _ _ _ _). now rewrite <-(Qfull $ E1).
    now rewrite <-(isometric (#b +) _ _ _).
    apply (C2 _ _ _ _). now rewrite <-(Qfull $ E2).
  + intro B. apply (ball_closed _ _ _). intros δ ?.
    destruct (uniform_continuity (+x) (δ/2)) as [δ1[el1 C1]].
    destruct (uniform_continuity (+y) (δ/2)) as [δ2[el2 C2]].
    ae_rat_set_min q δ1 δ2 E1 E2.
    destruct (dense_image # F a q) as [b[??]].
    mc_replace (ε + δ) with (δ/2 + ε + δ/2) on Q by decfield Q.
    rewrite (isometric (#b +) _ _ _).
    apply (ball_triangle _ _ _ (a + y) _).
    apply (ball_triangle _ _ _ (a + x) _); trivial.
    apply (C1 _ _ _ _). now rewrite <-(Qfull $ E1).
    apply (C2 _ _ _ _). now rewrite <-(Qfull $ E2).
  Qed.

  Instance: ∀ `{a ∊ R}, Isometry R R (+ a).
  Proof. split; try apply _. intros ε ? x ? y ?.
    rewrite 2!(R $ commutativity (+) _ a).
    exact (isometric (a+) _ _ _).
  Qed.

  Notation "%" := (rationals_to_field Q F).

  Existing Instance arch_field_dense.

  Instance : Dense (# ∘ %)⁺¹(Q) := _.

  Notation Q_to_Q_id := (rationals_to_rationals_unique (rationals_to_field Q Q) id).

  Lemma le_closed_aux ε `{ε ∊ Q⁺} q `{q ∊ Q} : (∀ `{δ ∊ Q₊}, -δ-δ - ε ≤ q) → -ε ≤ q.
  Proof. intro P.
    destruct (nonneg_or_neg q).
      apply (transitivity (S:=Q) _ 0 _).
      now destruct (_ : -ε ∊ Q⁻). now destruct (_ : q ∊ Q⁺).
    cut (ball ε q 0).
      rewrite (arch_field_ball _ _ _).
      rewrite (Q_to_Q_id _ _ (_:Proper (Q,=) ε)). unfold id.
      mc_replace (q-0) with q on Q by setring Q. tauto.
    apply (ball_closed _ _ _). intros δ ?.
    rewrite (arch_field_ball _ _ _).
    rewrite (Q_to_Q_id _ _ (_:Proper (Q,=) (ε+δ))). unfold id.
    mc_replace (q-0) with q on Q by setring Q. split.
    mc_replace (-(ε + δ)) with (-(δ/2)-(δ/2)-ε) on Q by decfield Q. exact (P _ _).
    apply (lt_le _ _). apply (transitivity (S:=Q) _ 0 _).
    now destruct (_ : q ∊ Q₋). now destruct (_ : ε+δ ∊ Q₊).
  Qed.

  Instance: Reflexive R (≤).
  Proof.
    intros x ? ε ? q ? B. apply (order_reflecting % _ _). preserves_simplify %.
    rewrite (R $ plus_negate_r x) in B. change (ball ε (#(%q)) (# 0) ) in B.
    rewrite <-(isometric # _ _ _) in B. rewrite (arch_field_ball _ _ _) in B.
    destruct B as [B _]. now rewrite (_ $ negate_0), (_ $ plus_0_r _) in B.
  Qed.

  Instance: Transitive R (≤).
  Proof. intros x ? y ? z ? P1 P2 ε ? q ? B.
    apply (le_closed_aux _ _). intros δ ?.
    destruct (dense_image (# ∘ %) Q (y-x) (δ/2)) as [a[? B1]]. unfold compose in B1.
    destruct (dense_image (# ∘ %) Q (z-y) (δ/2)) as [b[? B2]]. unfold compose in B2.
    subsymmetry in B1. subsymmetry in B2.
    pose proof P1 _ _ _ _ B1 as E1.
    pose proof P2 _ _ _ _ B2 as E2.
    rewrite (isometric (x+) _ _ _) in B1. mc_replace (x+(y-x)) with y on R in B1 by setring R.
    rewrite (isometric (-) _ _ _), (isometric (z+) _ _ _) in B2.
    mc_replace (z-(z-y)) with y on R in B2 by setring R.
    subsymmetry in B2.
    assert (ball δ (z-x) (#(%(a+b))) ) as B3. subsymmetry.
      mc_replace (%(a+b)) with (%a + %b) on F by now preserves_simplify %.
      rewrite (_ $ preserves_plus _ _), (isometric ((x-#(%(b)))+) _ _ _).
      mc_replace (x - # (% b) + (# (% a) + # (% b))) with (x + # (% a)) on R by setring R.
      mc_replace (x - # (% b) + (z - x)) with (z - # (% b)) on R by setring R.
      mc_replace δ with (δ/2+δ/2) on Q by decfield Q.
      now apply (ball_triangle _ _ _ y _).
    pose proof ball_triangle _ _ _ _ _ B B3 as B4.
    rewrite <-(isometric # _ _ _), (arch_field_ball _ _ _) in B4.
    mc_replace (- % (ε + δ)) with (%(-(ε + δ))) on F in B4 by now preserves_simplify %.
    mc_replace (%q - % (a + b)) with (%(q-(a + b))) on F in B4 by now preserves_simplify %.
    mc_replace (- δ - δ - ε) with (- (ε + δ) -δ/2 -δ/2) on Q by decfield Q.
    mc_replace q with ((q-(a+b))+a+b) on Q by setring Q.
    apply (plus_le_compat _ _ _ _); trivial.
    apply (plus_le_compat _ _ _ _); trivial.
    apply (order_reflecting % _ _). now destruct B4.
  Qed.

  Instance: AntiSymmetric R (≤).
  Proof.
    intros x ? y ? P1 P2. apply (equal_by_ball_closed _ _). intros ε ?.
    destruct (dense_image (# ∘ %) Q (y-x) (ε/2)) as [q[? B]]. unfold compose in B.
    rewrite (isometric ((-x)+) _ _ _).
    mc_replace (-x+x) with (0:A2) on R by setring R.
    mc_replace (-x+y) with (y-x) on R by setring R.
    mc_replace ε with (ε/2+ε/2) on Q by decfield Q.
    apply (ball_triangle _ _ _ (#(%q)) _); [| subsymmetry].
    replace (0:A2) with (# 0) by reflexivity. rewrite <-(isometric # _ _ _).
    subsymmetry. rewrite (arch_field_ball _ _ _).
    mc_replace (- % (ε /2)) with (%(-(ε/2))) on F by now preserves_simplify %.
    rewrite (F $ negate_0), (F $ plus_0_r _).
    subsymmetry in B.
    split; apply (order_preserving % _ _).
    exact (P1 _ _ _ _ B).
    apply (flip_le_negate _ _).
    rewrite (isometric (-) _ _ _) in B.
    rewrite <-(R $ preserves_negate _) in B.
    mc_replace (-%q) with (%(-q)) on F in B by now preserves_simplify %.
    mc_replace (-(y-x)) with (x-y) on R in B by setring R.
    exact (P2 _ _ _ _ B).
  Qed.


  Instance: PartialOrder R.
  Proof. split; try apply _.
    intros ?? E1 ?? E2 P ε ? q ? B. unfold_sigs. apply P; try apply _.
    now rewrite (R $ E1), (R $ E2).
  Qed.

  Lemma scale_nonneg a `{a ∊ Q⁺} x `{x ∊ R⁺} : (#(%a))*x ∊ R⁺ .
  Proof. destruct (pos_or_nonpos a).
  + split. apply _. intros  ε ? q ? Bq.
    assert (#(%a) * x - 0 = #(%a) * x) as E by setring R. rewrite (R $ E) in Bq. clear E.
    destruct (_ : x ∊ R⁺ ) as [_ P1]. do 3 red in P1.
    apply (le_closed_aux _ _). intros p ?.
    destruct (pointwise_continuity (uncurry mult) (#(%(a)),x) p) as [δ[? C]].
    ae_rat_set_min r δ (p/a) Er1 Er2.
    destruct (dense_image (# ∘ %) Q x r) as [b[? Bx]].
    unfold compose in Bx. subsymmetry in Bx.
    assert (-b ≤ p/a) as E1.
      rewrite <-(flip_le_negate _ _), (_ $ negate_involutive _). apply (P1 _ _ _ _).
      assert (x-0 = x) as E by setring R. now rewrite <-(Qfull $ Er2), (R $ E).
    assert (ball p (# (% a) * x) (# (% a) * # (% b))) as B3. apply (C (#(%a),#(%b)) _).
      split. simpl. easy. simpl. subsymmetry. now rewrite <-(Qfull $ Er1).
    pose proof ball_triangle _ _ _ _ _ Bq B3 as B4.
    rewrite <-(R $ preserves_mult _ _), <-(isometric # _ _ _) in B4.
    mc_replace (%a * %b) with (%(a*b)) on F in B4 by now preserves_simplify %.
    rewrite <-(isometric % _ _ _), (arch_field_ball _ _ _) in B4.
    rewrite (Q_to_Q_id _ _ (_:Proper (Q,=) (ε+p))) in B4. unfold id in B4.
    destruct (nonneg_or_neg b).
      subtransitivity (q-a*b). subtransitivity (-(ε + p)).
      apply (flip_nonneg_minus _ _). mc_replace (-(ε+p)-(-p-p-ε)) with p on Q by setring Q. apply _.
      now destruct B4.
      apply (flip_nonneg_minus _ _). mc_replace (q-(q-a*b)) with (a*b) on Q by setring Q. apply _.
    mc_replace (-p-p-ε) with (-(ε+p)-p) on Q by setring Q.
    mc_replace (q) with (q-a*b+a*b) on Q by setring Q.
    apply (plus_le_compat _ _ _ _). now destruct B4.
    mc_replace (a*b) with (-((-b)*a)) on Q by setring Q.
    apply (flip_le_negate _ _). now apply (mult_inv_le_cancel_r _ _ _).
  + rewrite (Q $ nonneg_nonpos_0 a).
    mc_replace (%0) with (0:F) on F by now preserves_simplify %.
    change (0*x ∊ R⁺). rewrite (R $ mult_0_l x). apply _.
  Qed.

  Instance Creals_ring_order : SemiRingOrder R.
  Proof. apply from_ring_order.
  + intros z ?. split. split; try apply _. intros x ? y ? P1 ε ? q ? B.
    mc_replace (z+y-(z+x)) with (y-x) on R in B by setring R. now apply P1.
  + intros x ? y ?. split. apply _. intros ε ? q ? Bp.
    mc_replace (x*y-0) with (x*y) on R in Bp by setring R.
    apply (le_closed_aux _ _). intros p ?.
    destruct (pointwise_continuity (uncurry mult) (x,y) p) as [δ[? C]].
    ae_rat_set_min r δ (p/δ) Er1 Er2.
    destruct (dense_image (# ∘ %) Q x r) as [a[? B1]]. unfold compose in B1.
    destruct (dense_image (# ∘ %) Q y r) as [b[? B2]]. unfold compose in B2.
    subsymmetry in B1. subsymmetry in B2.
    subtransitivity (- (ε + p)).
      apply (flip_nonneg_minus _ _). mc_replace (-(ε+p)-(-p-p-ε)) with p on Q by setring Q. apply _.
    destruct (nonneg_or_neg a).
      assert ( ball p (x*y) (#(%a)*y) ) as B3. apply (C (#(%a),y) _).
        split;[|easy]. simpl. now rewrite <-(Qfull $ Er1).
      pose proof ball_triangle _ _ _ _ _ Bp B3 as B4.
      destruct (scale_nonneg a y) as [_ P].
      apply (P _ _ _ _). now mc_replace (#(%a)*y-0) with (#(%a)*y) on R by setring R.
    destruct (nonneg_or_neg b).
      assert ( ball p (x*y) (x*#(%b)) ) as B3. apply (C (x,#(%b)) _).
        split;[easy|]. simpl. now rewrite <-(Qfull $ Er1).
      pose proof ball_triangle _ _ _ _ _ Bp B3 as B4.
      destruct (scale_nonneg b x) as [_ P].
      apply (P _ _ _ _). now mc_replace (#(%b)*x-0) with (x*#(%b)) on R by setring R.
    assert (ball p (x*y) (#(%(a*b)))) as B3.
      mc_replace (%(a*b)) with (%a * %b) on F by now preserves_simplify %.
      rewrite (R $ preserves_mult _ _).
      apply (C (#(%a),#(%b)) _). split; simpl; now rewrite <-(Qfull $ Er1).
    pose proof ball_triangle _ _ _ _ _ Bp B3 as B4.
    rewrite <-(isometric # _ _ _), (arch_field_ball _ _ _) in B4.
    subtransitivity (q-(a*b)).
    apply (order_reflecting % _ _).
      mc_replace (%(-(ε + p))) with (-%(ε + p)) on F by now preserves_simplify %.
      mc_replace (%(q-a*b)) with (%q-%(a*b)) on F by now preserves_simplify %.
      now destruct B4.
    apply (flip_nonneg_minus _ _).
      mc_replace (q-(q-a*b)) with (a*b) on Q by setring Q. apply _.
  Qed.

  Instance: 1 ∊ R⁺ .
  Proof. split. apply _. intros ε ? q ? B1.
    mc_replace (1-0:A2) with (1:A2) on R in B1 by setring R.
    replace (1:R) with (#1) in B1 by reflexivity.
    rewrite <-(isometric # _ _ _), (arch_field_ball _ _ _) in B1.
    apply (order_reflecting % _ _). preserves_simplify %.
    subtransitivity (%q - 1). now destruct B1.
    mc_replace (%q - 1) with (%(q-1)) on F by now preserves_simplify %.
    apply (order_preserving % _ _).
    apply (flip_nonneg_minus _ _).
    mc_replace (q-(q-1)) with (1:Q) on Q by setring Q. apply _.
  Qed.

  Instance Creals_order_embedding : OrderEmbedding Q R (# ∘ %).
  Proof. split.
  + apply preserving_preserves_nonneg. apply _.
    intros a ?. unfold compose. rewrite <-(R $ mult_1_r (#(%a))). exact (scale_nonneg a 1).
  + apply reflecting_reflects_nonneg. intros a ?. unfold compose.
    intros [_ P]. split. apply _. red. rewrite <-(_ $ negate_0). apply (le_closed_aux _ _).
    intros δ ?. mc_replace (- δ - δ - 0) with (-(δ+δ)) on Q by setring Q.
    apply (P (δ+δ) _ a _).
    now mc_replace (#(%a) - 0) with (#(%a)) on R by setring R.
  Qed.

  Lemma Creals_ball_order q `{q ∊ Q⁺} x `{x ∊ R} y `{y ∊ R} : ball q x y ↔ -#(%q) ≤ x-y ≤ #(%q) .
  Proof. rewrite (isometric ((-y)+) _ _ _), (R $ commutativity (+) _ x), (R $ plus_negate_l _). split.
  + intro B1. split; intros ε ? p ? B2.
    * rewrite (isometric ((-#(%q))+) _ _ _) in B2.
      mc_replace (-#(%q)+(x-y--#(%q))) with (x-y) on R in B2 by setring R.
      pose proof ball_triangle _ _ _ _ _ B2 B1 as B3.
      mc_replace (-#(%q)+#(%p)) with (#(-%q+%p)) on R in B3 by now preserves_simplify #.
      replace (0:R) with (#0) in B3 by reflexivity. rewrite <-(isometric # _ _ _) in B3.
      rewrite (arch_field_ball _ _ _) in B3. destruct B3 as [B3 _].
      rewrite (F $ negate_0), (F $ plus_0_r _) in B3.
      mc_replace (-ε) with (-(ε+q) + q) on Q by setring Q.
      mc_replace (p) with ((-q + p)+q) on Q by setring Q.
      apply (plus_le_compat _ _ _ _); [| easy].
      apply (order_reflecting % _ _). preserves_simplify %.
      now mc_replace (-%(ε + q)) with (-(%ε + %q)) on F in B3 by now preserves_simplify %.
    * rewrite (isometric ((x-y-#(%p))+) _ _ _) in B2.
      mc_replace ((x-y-#(%p) + (#(%q)-(x-y)))) with (#(%(q))-#(%p)) on R in B2 by setring R.
      mc_replace (x-y-#(%p)+#(%p)) with (x-y) on R in B2 by setring R. subsymmetry in B2.
      pose proof ball_triangle _ _ _ _ _ B2 B1 as B3.
      mc_replace (#(%q)-#(%p)) with (#(%q-%p)) on R in B3 by now preserves_simplify #.
      replace (0:R) with (#0) in B3 by reflexivity. rewrite <-(isometric # _ _ _) in B3.
      rewrite (arch_field_ball _ _ _) in B3. destruct B3 as [_ B3].
      rewrite (F $ negate_0), (F $ plus_0_r _) in B3.
      apply (flip_le_negate _ _).
      mc_replace (-p) with ((q-p)-q) on Q by setring Q.
      mc_replace (--ε) with ((ε+q)-q) on Q by setring Q.
      apply (plus_le_compat _ _ _ _); [| easy].
      apply (order_reflecting % _ _).
      now mc_replace (%(q-p)) with (%q - %p) on F by now preserves_simplify %.
  + intros [P1 P2]. apply (ball_closed _ _ _). intros ε ?.
    destruct (dense_image (# ∘ %) Q (x-y) (ε/2)) as [p[? B1]]. unfold compose in B1.
    cut (ball (ε/2+q) p 0). intro B2.
      mc_replace (q+ε) with (ε/2+(ε/2+q)) on Q by decfield Q.
      apply (ball_triangle _ _ _ (#(%p)) _); trivial.
      replace (0:R) with (#0) by reflexivity.
      now rewrite <-(isometric # _ _ _), <-(F $ preserves_0 (f:=%)), <-(isometric % _ _ _).
    rewrite (arch_field_ball _ _ _).
    rewrite (Q_to_Q_id _ _ (_:Proper (Q,=) (ε/2+q))). unfold id.
    rewrite (Q $ negate_0), (Q $ plus_0_r _).
    split; [| apply (flip_le_negate _ _)]; apply (order_reflecting (q+) _ _);
      mc_replace (q-(ε/2+q)) with (-(ε/2)) on Q by setring Q.
    * apply (P1 _ _ _ _). rewrite (isometric ((-#(%q))+) _ _ _).
      mc_replace (-#(%q) + (x-y--#(%q))) with (x-y) on R by setring R.
      cut (-#(%q)+#(%(q+p)) = #(%p)). intro E. rewrite (R $ E). subsymmetry.
      rewrite (F $ preserves_plus _ _). preserves_simplify #. setring R.
    * apply (P2 _ _ _ _). rewrite (isometric ((-):R⇀R) _ _ _), (isometric ((#(%q))+) _ _ _).
      mc_replace (#(%q)-(#(%q)-(x-y))) with (x-y) on R by setring R.
      cut (#(%q)-#(%(q-p)) = #(%p)). intro E. rewrite (R $ E). subsymmetry.
      rewrite (F $ preserves_plus _ _), (F $ preserves_negate _).
      preserves_simplify #. setring R.
  Qed.

End contents.
