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

  Notation "%" := (rationals_to_field Q F).
  Notation "#" := (to_completion F R).

  Context `{!Field R} `{!SemiRing_Morphism F R #}.
  Context `{!Isometry R R (-)}.
  Context `{!UniformlyContinuous (R*R) R (uncurry (+) : R*R ⇀ R)}.
  Context `{!Continuous (R*R) R (uncurry (.*.) : R*R ⇀ R)}.
  Context `{!Continuous (R ₀) (R ₀) (⁻¹)}.

  Context `{!SemiRingOrder R}.
  Context `{!OrderEmbedding Q R (# ∘ %)}.
  Context (ball_correct : ∀ q `{q ∊ Q⁺} x `{x ∊ R} y `{y ∊ R}, ball q x y ↔ -#(%q) ≤ x-y ≤ #(%q) ).

  Instance: FinitePoints R := finite_points_completion.
  Instance: LocatedPoints R := located_points_completion.
  Instance: StrongSetoid R := metric_inequality_strong_setoid.

  Instance: StrongInjective F R #. Proof isometry_str_injective _.
  Instance: Strong_Morphism F R #. Proof strong_injective_mor _.

  Add Ring R : (stdlib_ring_theory R).

  Existing Instance arch_field_dense.
  Instance : Dense (# ∘ %)⁺¹(Q) := _.

  Let dense_alt x `{x ∊ R} ε `{ε ∊ Q₊} : ∃ `{q ∊ Q}, #(%(q-ε)) ≤ x ≤ #(%(q+ε)).
  Proof.
    destruct (dense_image (# ∘ %) Q x ε) as [q[? B1]]. unfold compose in B1.
    rewrite (ball_correct _ _ _ _ _ _) in B1. destruct B1.
    exists_sub q. change ( (# ∘ %) (q - ε) ≤ x ≤ (# ∘ %) (q + ε) ).
    preserves_simplify (# ∘ %). unfold compose.
    mc_replace x with (#(%q)+(x-#(%q))) on R by setring R.
    split; apply (plus_le_compat _ _ _ _); trivial; apply (reflexivity (S:=R) _).
  Qed.

  Instance: CoTransitive R (<).
  Proof. intros x ? y ? [q[? E]] z ?.
    set (ε := q/(2+3)). assert (ε ∊ Q₊). unfold ε. apply _.
    destruct (dense_alt (z-x) ε) as [r[? E1]].
    destruct (pos_or_nonpos (r-ε)). left. exists_sub (r-ε).
      apply (order_reflecting (+(-x)) _ _).
      mc_replace (x+#(%(r-ε))-x) with (#(%(r-ε))) on R by setring R.
      now destruct E1.
    destruct (dense_alt (y-z) ε) as [s[? E2]].
    destruct (pos_or_nonpos (s-ε)). right. exists_sub (s-ε).
      apply (order_reflecting (+(-z)) _ _).
      mc_replace (z+#(%(s-ε))-z) with (#(%(s-ε))) on R by setring R.
      now destruct E2.
    assert (z-x ≤ #(%(ε+ε))) as E1'.
      apply (transitivity (S:=R) _ (#(%(r+ε))) _). now destruct E1.
      apply (order_preserving (#∘%) _ _), (order_preserving (+ε) r ε).
      now apply (flip_nonpos_minus _ _). 
    assert (y-z ≤ #(%(ε+ε))) as E2'.
      apply (transitivity (S:=R) _ (#(%(s+ε))) _). now destruct E2.
      apply (order_preserving (#∘%) _ _), (order_preserving (+ε) s ε).
      now apply (flip_nonpos_minus _ _). 
    pose proof plus_le_compat _ _ _ _ E1' E2' as E3.
    mc_replace (z-x+(y-z)) with (y-x) on R in E3 by setring R.
    setoid_rewrite <-(R $ preserves_plus (f:=#∘%) _ _) in E3.
    destruct (pos_not_nonpos ε).
    pose proof _ : 2+3 ∊ Q₊ . pose proof _ : inv (2+3) ∊ Q₊ .
    assert (q=ε*(2+3)) as Eq. unfold ε.
      now rewrite <-(Q $ associativity (.*.) _ _ _), (Q $ field_inv_l _), (Q $ mult_1_r _).
    assert (q-(ε+ε+(ε+ε)) = ε) as E4. rewrite (Q $ Eq). setring Q.
    rewrite <-(Q $ E4). apply (flip_nonpos_minus _ _).
    apply (order_reflecting (#∘%) _ _).
    apply (transitivity (S:=R) _ (y-x) _); [|exact E3].
    apply (order_reflecting (x+) _ _).
    mc_replace (x+(y-x)) with y on R by setring R.
    exact E.
  Qed.

  Instance: PseudoOrder R.
  Proof. split; try apply _.
  + intros x ? y ? [[p[? E1]][q[? E2]]].
    rewrite (_ $ commutativity (+) _ _), <-(flip_le_minus_r _ _ _) in E1.
    rewrite (_ $ commutativity (+) _ _), <-(flip_le_minus_r _ _ _) in E2.
    pose proof (plus_le_compat _ _ _ _ E1 E2) as E.
    mc_replace (y-x+(x-y)) with (0:A2) on R in E by setring R.
    destruct (pos_not_nonpos (p+q)). split. apply _. red.
    apply (order_reflecting (# ∘ %) _ _). unfold compose.
    mc_replace (%(p+q)) with (%p+%q) on F by now preserves_simplify %.
    mc_replace (%0) with (0:F) on F by now preserves_simplify %.
    now rewrite (R $ preserves_plus _ _).
  + intros x ? y ?. rewrite (metric_inequality _ _). split.
    * intros [q[? E]]. 
      destruct (dense_alt (y-x) (q/2)) as [p[? E2]].
      destruct (pos_or_nonpos (p-q/2)). left. exists_sub (p-q/2).
        apply (order_reflecting (+(-x)) _ _).
        mc_replace (x+#(%(p-q/2))-x) with (#(%(p-q/2))) on R by setring R.
        now destruct E2.
      destruct (pos_or_nonpos (-(p+q/2))). right. exists_sub (-(p+q/2)).
        setoid_rewrite (R $ preserves_negate (f:=#∘%) _). unfold compose.
        apply (flip_le_negate _ _). apply (order_reflecting (y+) _ _).
        mc_replace (y - (y - # (% (p + q / 2)))) with (#(%(p+q/2))) on R by setring R.
        now destruct E2.
      destruct E. subsymmetry. apply (ball_correct _ _ _ _ _ _). split.
      - apply (transitivity (S:=R) _ (#(%(p - q / 2))) _); [| now destruct E2].
        setoid_rewrite <-(R $ preserves_negate (f:=#∘%) _).
        apply (order_preserving (#∘%) _ _). apply (flip_nonpos_minus _ _).
        now mc_replace (-q-(p-q/2)) with (-(p+q/2)) on Q by decfield Q.
      - apply (transitivity (S:=R) _ (#(%(p + q / 2))) _); [now destruct E2 |].
        apply (order_preserving (#∘%) _ _). apply (flip_nonpos_minus _ _).
        now mc_replace (p+q/2-q) with (p-q/2) on Q by decfield Q.
    * intros [[q[? E]] | [q[? E]]]; exists_sub (q/2); rewrite (ball_correct _ _ _ _ _ _);
        intros [E2 E3]; destruct (pos_not_nonpos (q/2));
        mc_replace (q/2) with (q-q/2) on Q by decfield Q.
      - apply (flip_nonpos_minus _ _). apply (flip_le_negate _ _).
        apply (order_reflecting (#∘%) _ _). rewrite 2!(R $ preserves_negate (f:=#∘%) _).
        apply (transitivity (S:=R) _ (x-y) _). exact E2.
        unfold compose. apply (order_reflecting ((-x)+) _ _).
        mc_replace (-x+(x-y)) with (-y) on R by setring R.
        mc_replace (-x-#(%q)) with (-(x+#(%q))) on R by setring R.
        apply (flip_le_negate _ _). exact E.
      - apply (flip_nonpos_minus _ _).
        apply (order_reflecting (#∘%) _ _).
        apply (transitivity (S:=R) _ (x-y) _); [| exact E3].
        unfold compose. apply (order_reflecting (y+) _ _).
        mc_replace (y+(x-y)) with x on R by setring R. exact E.
  Qed.

  Instance: PseudoSemiRingOrder R.
  Proof. apply from_pseudo_ring_order; [| apply _ |].
  + intros z ?. split. split; apply _. intros x ? y ? [q[? E]]. exists_sub q.
    rewrite <-(R $ associativity (+) _ _ _). now apply (order_preserving (z+) _ _).
  + intros x [?[p[? E1]]] y [?[q[? E2]]].
    rewrite (R $ plus_0_l _) in E1. rewrite (R $ plus_0_l _) in E2.
    split. apply _. exists_sub (p*q).
    rewrite (R $ plus_0_l _). setoid_rewrite (R $ preserves_mult (f:=#∘%) _ _).
    apply (mult_le_compat _ _ _ _). exact E1. exact E2.
  Qed.

  Instance: FullPseudoSemiRingOrder R.
  Proof. split. apply _. intros x ? y ?. split.
  + intros E1 [q[? E2]]. destruct (pos_not_nonpos q).
    apply (reflects_nonpos (#∘%)). apply _. split. apply _. red. unfold compose.
    apply (order_reflecting (y+) _ _). rewrite (R $ plus_0_r _).
    now apply (transitivity (S:=R) _ x _).
  + intros E ε ? q ? B1. apply (flip_nonneg_minus _ _). rewrite (Q $ negate_involutive _).
    destruct (nonneg_or_neg (q+ε)). trivial.
    destruct E. exists_sub (-(q+ε)).
    change (y+(#∘%)(-(q+ε)) ≤ x). preserves_simplify (#∘%). unfold compose.
    apply (order_reflecting ((-y+#(%q))+) _ _).
    apply (transitivity (S:=R) _ (-#(%ε)) _). apply (eq_le _ _). setring R.
    rewrite (ball_correct _ _ _ _ _ _) in B1.
    apply (transitivity (S:=R) _ (#(%q)-(y-x)) _). destruct B1 as [B1 _]; exact B1.
    apply (eq_le _ _). setring R.
  Qed.

  Let rationals_dense x `{x ∊ R} y `{y ∊ R} : x < y → ∃ `{q ∊ Q}, x < (#∘%)q < y .
  Proof. intros [q[? E]].
    rewrite (R $ commutativity (+) _ _), <-(flip_le_minus_r _ _ _) in E.
    set (ε := q/2/2). assert (ε ∊ Q₊). unfold ε. apply _.
    assert (q = (ε+ε)*2) as Eq. unfold ε. decfield Q.
    destruct (dense_alt ((x+y)/2) ε) as [r[? Er]].
    exists_sub r. split; exists_sub ε.
    + apply (transitivity (S:=R) _ ((x+y)/2 - (#∘%)ε) _ ).
      apply (order_reflecting (+(#∘%)ε) _ _).
      apply (transitivity (S:=R) _ (x+(y-x)/2) _ ).
      rewrite <-(R $ associativity (+) _ _ _).
      apply (order_preserving (x+) _ _).
      rewrite <-(mult_inv_le_cancel_r _ _ _).
      apply (transitivity (S:=R) _ ((#∘%)q) _); [| exact E].
      apply (eq_le _ _). rewrite (Q $ Eq).
      now preserves_simplify (#∘%).
      apply (eq_le _ _).
        cut (x = x*(2/2)). intro E'. rewrite (R $ E') at 1. setring R.
        rewrite (R $ field_inv_r _). setring R.
      rewrite (flip_le_minus_l _ _ _), <-(R $ preserves_plus (f:=#∘%) _ _).
      destruct Er as [_ Er]. exact Er.
    + apply (transitivity (S:=R) _ (((x+y)/2 + (#∘%)ε)+(#∘%)ε) _ ).
      apply (order_preserving (+(#∘%)ε) ((#∘%)r) ((x+y)/2+(#∘%)ε)).
      rewrite <-(flip_le_minus_l _ _ _).
        mc_replace ((# ∘ %) r - (# ∘ %) ε) with ((# ∘ %) (r - ε)) on R by
          now preserves_simplify (# ∘ %). destruct Er as [Er _]. exact Er.
      rewrite <-(R $ associativity (+) _ _ _), (R $ commutativity (+) _ _).
      rewrite <-(flip_le_minus_r _ _ _).
      apply (transitivity (S:=R) _ ((y-x)/2) _).
      rewrite <-(mult_inv_le_cancel_r _ _ _).
      apply (transitivity (S:=R) _ ((#∘%)q) _); [| exact E].
      apply (eq_le _ _). rewrite (Q $ Eq).  now preserves_simplify (#∘%).
      apply (eq_le _ _).
        cut (y = y*(2/2)). intro E'. rewrite (R $ E') at 2. setring R.
        rewrite (R $ field_inv_r _). setring R.
  Qed.

  Instance Creals_arch_field_aux: ArchimedeanField R.
  Proof. split; try apply _.
  + apply (rationals_dense_archimedean (H:=_:Field R)). intros x ? y ? E.
    destruct (rationals_dense x y E) as [q[? E2]]. exists_sub q.
    now rewrite <-( rationals_to_field_unique Q (# ∘ %) _ _ (_ : Proper (Q,=) q) ).
  Qed.

  Instance Creals_arch_field_metric_aux: ArchimedeanField_Metric R.
  Proof. split. apply _.
  + exact msp_nonneg.
  + exact msp_ball_inf.
  + intros ε ? x ? y ?. destruct (nonneg_or_neg ε).
      rewrite <-( rationals_to_field_unique Q (# ∘ %) _ _ (_ : Proper (Q,=) ε) ).
      exact (ball_correct _ _ _ _ _ _).
    split. intro. destruct (neg_not_nonneg ε). now apply (ball_nonneg _ x y).
    intros [??]. destruct (neg_not_nonneg ε). apply (between_nonneg _).
    apply (order_reflecting (rationals_to_field Q R) _ _).
    preserves_simplify (rationals_to_field Q R).
    now apply (transitivity (S:=R) _ (x-y) _).
  Qed.

End contents.
