Require Import
  abstract_algebra interfaces.orders interfaces.metric_spaces
  interfaces.rationals interfaces.archimedean_fields interfaces.reals
  theory.setoids theory.products theory.rings theory.reals
  orders.maps orders.affinely_extended_ring orders.lattices lattice_ordered_rings
  metric.metric_spaces metric.maps metric.products
  uniform_continuity metric.complete
  the_ae_rationals
  stdlib_field_dec misc.quote.

Local Notation Q := the_ae_rationals.
Local Notation "Q∞" := (aff_ext Q).
Local Notation Qfull := (aff_ext_full Q).

Section default_lattice.
  Context `{Reals A (R:=R)}.
  Hint Extern 0 AmbientSpace => eexact R : typeclass_instances.
  Hint Extern 0 TheReals => eexact R : typeclass_instances.

  Add Ring R : (stdlib_ring_theory R).

  Instance reals_min : Meet R := curry (ufm_completion_map (X:=Q*Q) (uncurry (⊓))).
  Instance reals_max : Join R := curry (ufm_completion_map (X:=Q*Q) (uncurry (⊔))).

  Instance reals_min_cont: UniformlyContinuous (R*R) R (uncurry (⊓) : R*R ⇀ R).
  Proof. pose proof _ : UniformlyContinuous (R*R) R (ufm_completion_map (uncurry (⊓) : Q*Q ⇀ Q)).
    cut (@equiv _ (ext_equiv (X:=R*R) (Y:=R)) (ufm_completion_map (uncurry (⊓) : Q*Q ⇀ Q)) (uncurry (⊓))).
      intro E. now rewrite <-E.
    intros ?? E. unfold meet at 2. unfold reals_min.
    unfold_sigs. red_sig. rewrite (R*R $ E).
    destruct y as [??]. now unfold uncurry, curry.
  Qed.

  Instance reals_max_cont: UniformlyContinuous (R*R) R (uncurry (⊔) : R*R ⇀ R).
  Proof. pose proof _ : UniformlyContinuous (R*R) R (ufm_completion_map (uncurry (⊔) : Q*Q ⇀ Q)).
    cut (@equiv _ (ext_equiv (X:=R*R) (Y:=R)) (ufm_completion_map (uncurry (⊔) : Q*Q ⇀ Q)) (uncurry (⊔))).
      intro E. now rewrite <-E.
    intros ?? E. unfold join at 2. unfold reals_max.
    unfold_sigs. red_sig. rewrite (R*R $ E).
    destruct y as [??]. now unfold uncurry, curry.
  Qed.

  Instance: Morphism (R ⇒ R ⇒ R) (⊓). Proof. unfold meet, reals_min. apply _. Qed.
  Instance: ClosedFun (R ⇀ R ⇀ R) (⊓) := binary_morphism_closed _.
  Hint Extern 5 (_ ⊓ _ ∊ R) => eapply (_ : ClosedFun (R ⇀ R ⇀ R) (⊓)) : typeclass_instances.

  Instance: Morphism (R ⇒ R ⇒ R) (⊔). Proof. unfold join, reals_max. apply _. Qed.
  Instance: ClosedFun (R ⇀ R ⇀ R) (⊔) := binary_morphism_closed _.
  Hint Extern 5 (_ ⊔ _ ∊ R) => eapply (_ : ClosedFun (R ⇀ R ⇀ R) (⊔)) : typeclass_instances.

  Notation "#" := (rationals_to_field Q R).
  Notation "%" := (to_completion Q R).
  Existing Instance arch_field_dense.

  Let compl_to_hash x `{x ∊ Q} : %x = # x.
  Proof. now destruct ( rationals_to_field_unique Q (to_reals R Q) _ _ (_ : Proper (Q,=) x) ). Qed.

  Let preserves_meet x `{x ∊ Q} y `{y ∊ Q} : # (x ⊓ y) = # x ⊓ # y.
  Proof. rewrite <-3!(_ $ compl_to_hash _).
    now destruct ( ufm_completion_map_extends (CX:=R*R) (uncurry (⊓) : Q*Q ⇀ Q ) (x,y) (x,y)
      (_:Proper (Q*Q,=) (x,y)) ).
  Qed.

  Let preserves_join x `{x ∊ Q} y `{y ∊ Q} : # (x ⊔ y) = # x ⊔ # y.
  Proof. rewrite <-3!(_ $ compl_to_hash _).
    now destruct ( ufm_completion_map_extends (CX:=R*R) (uncurry (⊔) : Q*Q ⇀ Q ) (x,y) (x,y)
      (_:Proper (Q*Q,=) (x,y)) ).
  Qed.

  Instance: Commutative (⊓) R.
  Proof.
    cut (uncurry (⊓) = uncurry (⊓) ∘ (prod_swap:R*R ⇀ R*R)).
      intros E x ? y ?. now destruct (E (x,y) (x,y) (_:Proper (R*R,=) (x,y)) ).
    apply (ufm_cont_equal_on_dense_image_applied (to_completion (Q*Q) (R*R)) _ _).
    intros [x y][??]. change (%x ⊓ %y = %y ⊓ %x).
    rewrite 2!(_ $ compl_to_hash _).
    now rewrite <-2!(_ $ preserves_meet _ _), (_ $ commutativity _ _ _).
  Qed.

  Lemma reals_max_to_min : ∀ x `{x ∊ R} y `{y ∊ R}, x ⊔ y = -(-x ⊓ -y).
  Proof.
    cut (uncurry (⊔) = negate ∘ uncurry (⊓) ∘ prod_map negate negate).
      intros E x ? y ?. now destruct (E (x,y) (x,y) (_:Proper (R*R,=) (x,y)) ).
    apply (ufm_cont_equal_on_dense_image_applied (to_completion (Q*Q) (R*R)) _ _).
    intros [x y][??]. change (%x ⊔ %y = -(-%x ⊓ -%y)).
    rewrite 2!(_ $ compl_to_hash _).
    rewrite <-2!(_ $ preserves_negate _), <-(_ $ preserves_meet _ _), <-(_ $ preserves_join _ _).
    now rewrite <-(_ $ preserves_negate _), (_ $ negate_meet _ _), 2!(_ $ negate_involutive _).
  Qed.
  Arguments reals_max_to_min x {_} y {_}.

  Lemma reals_min_lb_l x `{x ∊ R} y `{y ∊ R} : x ⊓ y ≤ x .
  Proof.
    apply (order_reflecting (+ -x) _ _). rewrite (_ $ plus_negate_r _).
    apply (le_iff_not_lt_flip _ _). intro E.
    destruct (archimedean_rationals_dense _ _ E) as [q[? [E1 E2]]].
    assert (q ∊ Q₊). apply (reflects_pos #). apply _. split. apply _. trivial.
    set (a := q/2). assert (a ∊ Q₊). unfold a. apply _.
    destruct (uniform_continuity (uncurry (⊓) : R*R ⇀ R) a) as [p[? Cf]].
    ae_rat_set_min r p a Er1 Er2. pose proof (ae_pos_finite_bound r _ Er2).
    destruct (dense_image # Q x r) as [x' [? Ex]].
    destruct (dense_image # Q y r) as [y' [? Ey]].
    assert (ball a (x ⊓ y) (#(x' ⊓ y'))) as E3.
      rewrite (_ $ preserves_meet _ _).
      apply (Cf (x,y) _ (#x',#y') _).
      split; simpl; now rewrite <-(Qfull $ Er1).
    revert E2. apply (le_iff_not_lt_flip _ _).
    mc_replace q with (a+a) on Q by (subst a; decfield Q). preserves_simplify #.
    mc_replace (x ⊓ y - x) with ( (x ⊓ y - # (x' ⊓ y')) + (#(x'⊓ y') - x)) on R by setring R.
    apply (plus_le_compat _ _ _ _).
      rewrite (arch_field_ball _ _ _) in E3. intuition.
    subtransitivity (#x' - x).
      apply (order_preserving (+ -x) (#(x' ⊓ y')) (#(x'))).
      apply (order_preserving # _ _). lattice_order_tac.
    subtransitivity (# r).
      subsymmetry in Ex. rewrite (arch_field_ball _ _ _) in Ex. intuition.
    now apply (order_preserving # _ _).
  Qed.

  Lemma reals_min_slb x `{x ∊ R} y `{y ∊ R} z `{z ∊ R} : x ⊓ y < z → x < z ∨ y < z .
  Proof. intros E.
    destruct (cotransitivity E x) as [E1|?]; [| now left].
    destruct (cotransitivity E y) as [E2|?]; [| now right].
    cut False. tauto.
    apply (strictly_order_preserving (+ -(meet x y)) _ _) in E1. rewrite (_ $ plus_negate_r _) in E1.
    apply (strictly_order_preserving (+ -(meet x y)) _ _) in E2. rewrite (_ $ plus_negate_r _) in E2.
    destruct (archimedean_rationals_dense _ _ E1) as [q1[? [? E1']]].
    destruct (archimedean_rationals_dense _ _ E2) as [q2[? [? E2']]].
    assert (q1 ∊ Q₊). apply (reflects_pos #). apply _. split. apply _. trivial.
    assert (q2 ∊ Q₊). apply (reflects_pos #). apply _. split. apply _. trivial.
    set (a := (meet q1 q2)/2). assert (a ∊ Q₊). unfold a. apply _.
    destruct (uniform_continuity (uncurry (⊓) : R*R ⇀ R) a) as [p[? Cf]].
    ae_rat_set_min r p a Er1 Er2. pose proof (ae_pos_finite_bound r _ Er2).
    destruct (dense_image # Q x r) as [x' [? Ex]].
    destruct (dense_image # Q y r) as [y' [? Ey]].
    assert (ball a (x ⊓ y) (#(x' ⊓ y'))) as E3.
      rewrite (_ $ preserves_meet _ _).
      apply (Cf (x,y) _ (#x',#y') _).
      split; simpl; now rewrite <-(Qfull $ Er1).
    rewrite (arch_field_ball _ _ _) in Ex.
    rewrite (arch_field_ball _ _ _) in Ey.
    subsymmetry in E3. rewrite (arch_field_ball _ _ _) in E3.
    destruct (irreflexivity (<) x'). subtransitivity y'.
    + apply (meet_slb_r _ _). apply (flip_pos_minus _ _).
      apply (reflects_pos #). apply _. split. apply _. red. preserves_simplify #.
      apply (strictly_order_reflecting (y-#y' +) _ _).
      apply (le_lt_trans _ (#a) _).
        rewrite (_ $ plus_0_r _). subtransitivity (#r). intuition.
        now apply (order_preserving # _ _).
      apply (strictly_order_reflecting (+ #(x'⊓y') - (x⊓y)) _ _).
      apply (le_lt_trans _ (#q2) _).
        subtransitivity (#a+#a). apply (order_preserving (#a +) _ _). intuition.
        rewrite <-(_ $ preserves_plus _ _). apply (order_preserving # _ _).
        subst a. subtransitivity (q1 ⊓ q2). apply (eq_le _ _). decfield Q. lattice_order_tac.
      apply (lt_le_trans _  (y - (x ⊓ y)) _); trivial.
      apply (eq_le _ _). setring R.
    + apply (meet_slb_l _ _). apply (flip_pos_minus _ _).
      apply (reflects_pos #). apply _. split. apply _. red. preserves_simplify #.
      apply (strictly_order_reflecting (x-#x' +) _ _).
      apply (le_lt_trans _ (#a) _).
        rewrite (_ $ plus_0_r _). subtransitivity (#r). intuition.
        now apply (order_preserving # _ _).
      apply (strictly_order_reflecting (+ #(x'⊓y') - (x⊓y)) _ _).
      apply (le_lt_trans _ (#q1) _).
        subtransitivity (#a+#a). apply (order_preserving (#a +) _ _). intuition.
        rewrite <-(_ $ preserves_plus _ _). apply (order_preserving # _ _).
        subst a. subtransitivity (q1 ⊓ q2). apply (eq_le _ _). decfield Q. lattice_order_tac.
      apply (lt_le_trans _  (x - (x ⊓ y)) _); trivial.
      apply (eq_le _ _). setring R.
  Qed.

  Instance: FullMeetSemiLatticeOrder R.
  Proof. split; try apply _.
  + exact reals_min_lb_l.
  + intros x ? y ?. rewrite (_ $ commutativity meet _ _). exact (reals_min_lb_l _ _).
  + exact reals_min_slb.
  Qed.

  Instance: FullJoinSemiLatticeOrder R.
  Proof. split; try apply _.
  + intros x ? y ?. rewrite <-(_ $ negate_involutive x) at 1.
    rewrite (_ $ reals_max_to_min _ _). apply (flip_le_negate _ _). lattice_order_tac.
  + intros x ? y ?. rewrite <-(_ $ negate_involutive y) at 1.
    rewrite (_ $ reals_max_to_min _ _). apply (flip_le_negate _ _). lattice_order_tac.
  + intros x ? y ? z ? E.
    rewrite <-(_ $ negate_involutive z), (_ $ reals_max_to_min _ _) in E.
    rewrite (flip_lt_negate _ _) in E.
    destruct (meet_slb _ _ _ E); [left|right]; now apply (flip_lt_negate _ _).
  Qed.

  Instance reals_lattice : FullLatticeOrder R := {} .

End default_lattice.

Hint Extern 2 (Meet (elt_type ?R)) => ensure_reals R; eapply reals_min : typeclass_instances.
Hint Extern 2 (Join (elt_type ?R)) => ensure_reals R; eapply reals_max : typeclass_instances.

Hint Extern 5 (Meet ?A) => let R := reals_of_type A in eapply (reals_min (R:=R)) : typeclass_instances.
Hint Extern 5 (Join ?A) => let R := reals_of_type A in eapply (reals_max (R:=R)) : typeclass_instances.

Hint Extern 2 (FullLatticeOrder (Ameet:=reals_min) (Ajoin:=reals_max) ?R) => eapply @reals_lattice : typeclass_instances. 
Hint Extern 2 (SemiRingLatticeOrder (Ameet:=reals_min) (Ajoin:=reals_max) ?R) => eapply @arch_field_lattice : typeclass_instances. 
Hint Extern 2 (DistributiveLattice (Ameet:=reals_min) (Ajoin:=reals_max) ?R) => eapply @srlatorder_distlat : typeclass_instances. 

(*
Section blah.
  Context `{Reals A (R:=R)}.
  Hint Extern 0 AmbientSpace => eexact R : typeclass_instances.
  Hint Extern 0 TheReals => eexact R : typeclass_instances.

  Check _ : FullLatticeOrder R.
  Check _ : SemiRingLatticeOrder R.
  Check _ : DistributiveLattice R.
  Check _ : Lattice R.
  Check _ : LatticeAbs R.
End blah.
*)
