Require Import
  abstract_algebra interfaces.orders interfaces.rationals interfaces.metric_spaces
  theory.setoids theory.rings theory.rationals orders.lattices orders.abs orders.rationals
  metric.metric_spaces metric.prelength
  orders.affinely_extended_field stdlib_field_dec.

Local Open Scope mc_abs_scope.

Section contents.
  Context `{Rationals (Q:=Q)}.

  (* Use default instances of order and abs *)
  Let b (ε x y : Q) := |x-y| ≤ ε .

  Add Ring Q : (stdlib_ring_theory Q).

  Instance rationals_ball : Ball Q := alt_Build_MetricSpace_ball b.
  Instance rationals_metric: MetricSpace Q.
  Proof. apply (alt_Build_MetricSpace b); unfold b.
  + intros ?? E1 ?? E2 ?? E3. unfold_sigs. intro. now rewrite_on Q <- E1, <-E2, <-E3.
  + intros ε ? x ?. rewrite (Q $ plus_negate_r _), (Q $ abs_0). now destruct (_ : ε ∊ Q⁺).
  + intros ε ? x ? y ? E. now rewrite <- (Q $ abs_negate _), <- (Q $ negate_swap_r _ _).
  + intros x ? y ?. rewrite <- (equal_by_zero_sum _ _), <- (abs_0_iff _), (eq_iff_le _ _).
    destruct (_ : |x - y| ∊ Q⁺). intuition.
  + intros ε₁ ? ε₂ ? x ? y ? z ? E1 E2.
    mc_replace (x-z) with ((x-y)+(y-z)) on Q by setring Q.
    subtransitivity (|x-y| + |y-z|). exact (abs_triangle _ _).
    now apply (plus_le_compat _ _ _ _).
  + intros ε ? x ? y ? P. rewrite (le_iff_not_lt_flip _ _). intro E.
    destruct (decompose_lt E) as [z [? E2]].
    pose proof (P (z/2) _) as P'.
    destruct (le_not_lt_flip _ _ P'). rewrite (Q $ E2).
    apply (strictly_order_preserving (ε +) _ _).
    rewrite <- (mult_inv_lt_cancel_l _ _ _), <- (flip_pos_minus _ _).
    now mc_replace (z*2 - z) with z on Q by setring Q.
  Qed.
End contents.

Hint Extern 2 (Ball TheAERationals.A) => eexact rationals_ball : typeclass_instances.
Hint Extern 2 (Ball (elt_type the_ae_rationals)) => eexact rationals_ball : typeclass_instances.
Hint Extern 2 (MetricSpace the_ae_rationals) => eexact rationals_metric : typeclass_instances.

Hint Extern 20 (Ball ?A) =>
  let H := match A with
           | elt_type ?Q => constr:(_ : Rationals Q)
           | _ => constr:(_ : Rationals (A:=A) _)
           end
  in eapply (rationals_ball (H:=H)) : typeclass_instances.
Hint Extern 20 (MetricSpace ?Q) =>
  let H := constr:(_ : Rationals Q) in eapply (rationals_metric (H:=H)) : typeclass_instances.

Local Notation AQ := TheAERationals.A.
Local Notation Q := the_ae_rationals.
Local Notation "Q∞" := (aff_ext Q).
Local Notation Qfull := (aff_ext_full Q).

Hint Extern 5 (MeetSemiLatticeOrder (Ameet := @minmax.min ?A ?l ?X ?d) _) =>
  eapply (lattice_order_meet (Ameet:=@minmax.min A l X d) (Ajoin:=@minmax.max A l X d)) : typeclass_instances.
Hint Extern 5 (JoinSemiLatticeOrder (Ajoin := @minmax.max ?A ?l ?X ?d) _) => 
  eapply (lattice_order_join (Ameet:=@minmax.min A l X d) (Ajoin:=@minmax.max A l X d)) : typeclass_instances.

Section ball_def.
  Context `{Rationals (Q:=Q')}.
  Instance latabs1: LatticeAbs Q' := _.
  Instance : FullLatticeOrder Q' := dec_full_lattice_order.
  Instance : ∀ `{q ∊ Q'}, |q| ∊ Q' := λ q _, _.

  Context `{Le _} `{Lt _} `{!FullPseudoSemiRingOrder Q'}.
  Context `{Join _} `{!JoinSemiLatticeOrder Q'}.
  Context (f:Q ⇀ Q') `{!SemiRing_Morphism Q Q' f}.

  Existing Instance rationals.morphism_order_embedding.
  Instance : FullJoinSemiLatticeOrder Q' := dec_full_join_semilattice_order.

  Lemma rationals_ball_def `{Abs _} `{!LatticeAbs Q'} ε `{ε ∊ Q} x `{x ∊ Q'} y `{y ∊ Q'} :
    ball ε x y ↔ |x-y| ≤ f ε.
  Proof. unfold ball, rationals_ball, alt_Build_MetricSpace_ball. split.
  + intros [E|[? E]]. destruct (ae_inf_not_el). now rewrite <- (_ $ E).
    revert E.
       match goal with |- @abs _ ?a1 _ ≤ _ -> @abs _ ?a2 _ ≤ _ => set (abs1:=a1) end.
       pose proof preserves_abs (a1:=abs1) (LatticeAbs0:=latabs1) (id:Q' ⇀ Q') as E'.
       subst abs1. unfold id in E'. rewrite (Q' $ E' _ _).
    rewrite (Q' $ to_rationals_unique f _).
    exact (order_preserving (id:Q' ⇀ Q') _ _).
  + intros E. right. split.
    * apply (reflects_nonneg f); trivial. split. apply _. red.
      match type of E with ?a ≤ f ε => subtransitivity a; now destruct (_ : a ∊ Q'⁺) end.
    *
    revert E. match goal with |- @abs _ ?a2 _ ≤ _ -> @abs _ ?a1 _ ≤ _ =>
      setoid_rewrite (Q' $ preserves_abs (a1:=a1) (LatticeAbs0:=latabs1) (id:Q' ⇀ Q') _)
    end.
    rewrite (Q' $ to_rationals_unique f _).
    apply (order_embedding (id:Q' ⇀ Q') _ _).
  Qed.
End ball_def.

Section the_ae_rationals.
  Lemma the_ae_rationals_ball ε `{ε ∊ Q∞} x `{x ∊ Q} y `{y ∊ Q} : ball ε x y ↔ |x-y| ≤ ε.
  Proof. destruct (ae_decompose_ext ε) as [?|[?[E|E]]].
  + exact (rationals_ball_def id _ _ _).
  + split; intros _; rewrite (_ $ E). exact (ae_inf_ub _). exact (msp_ball_inf _ _).
  + split; intros E2;
      (cut (- ∞ ∊ Q∞⁺); [intro; now destruct (neg_not_nonneg (R:=Q∞) (-infty)) |]);
      rewrite <- (_ $ E).
    exact (msp_nonneg _ _ _ E2).
    split. apply _. red. apply (transitivity (S:=Q∞) _ (|x-y|) _); trivial.
      apply (_ : |x - y| ∊ Q⁺).
  Qed.
End the_ae_rationals.

Local Notation r2r := rationals_to_field.

Lemma rat_to_rat_isometry `{Rationals (Q:=Q1)} `{Rationals (Q:=Q2)} : Isometry Q1 Q2 (r2r Q1 Q2).
Proof.
  pose proof dec_full_lattice_order : FullLatticeOrder Q1.
  pose proof dec_full_lattice_order : FullLatticeOrder Q2.
  split; try apply _. intros.
  rewrite (rationals_ball_def (r2r Q Q1) _ _ _).
  rewrite (rationals_ball_def (r2r Q Q2) _ _ _).
  rewrite (order_embedding (r2r Q1 Q2) _ _).
  pose proof preserves_abs (r2r Q1 Q2) (x-y) as E. rewrite (_ $ E).
  rewrite (_ $ preserves_plus _ _), (_ $ preserves_negate _).
  now rewrite <-(_ $ to_rationals_unique (r2r Q1 Q2 ∘ r2r Q Q1) _).
Qed.
Hint Extern 8 (Isometry _ _ (rationals_to_field _ _)) => eapply @rat_to_rat_isometry : typeclass_instances.

Lemma the_ae_rationals_finite_points : FinitePoints Q.
Proof. intros x ? y ?. exists_sub (|x-y|). now apply (the_ae_rationals_ball _ _ _). Qed.

Lemma the_ae_rationals_located_points : LocatedPoints Q.
Proof. intros x ? y ? p ? q ? E.
  rewrite 2!(the_ae_rationals_ball _ _ _).
  destruct (total (≤) (|x-y|) q); [now left | right].
  apply (lt_not_le_flip _ _).
  now apply (lt_le_trans _ q _).
Qed.

Lemma the_ae_rationals_prelength : PrelengthSpace Q.
Proof. intros x ? y ? ε ? δ₁ ? δ₂ ? E E'.
  rewrite (the_ae_rationals_ball _ _ _) in E'.
  pose proof _ : δ₁ + δ₂ ∊ Q₊ .
  exists_sub ((x*δ₂ + y*δ₁)/(δ₁ + δ₂)).
  rewrite 2!(the_ae_rationals_ball _ _ _). split.
  + mc_replace (x - (x * δ₂ + y * δ₁) / (δ₁ + δ₂)) with ((δ₁/(δ₁ + δ₂))*(x-y)) on Q by decfield Q.
    pose proof _ : δ₁ / (δ₁ + δ₂) ∊ Q₊ .
    rewrite (_ $ abs_mult _ _), (_ $ abs_of_nonneg (δ₁ / (δ₁ + δ₂))).
    mc_replace (δ₁ / (δ₁ + δ₂) * (|x - y|)) with (δ₁ * (|x - y|) / (δ₁ + δ₂)) on Q by setring Q.
    rewrite <-(mult_inv_le_cancel_l _ _ _).
    apply (order_preserving (δ₁ *.) _ _). subtransitivity ε. now apply (lt_le _ _).
  + mc_replace ((x * δ₂ + y * δ₁) / (δ₁ + δ₂) - y) with ((δ₂/(δ₁ + δ₂))*(x-y)) on Q by decfield Q.
    pose proof _ : δ₂ / (δ₁ + δ₂) ∊ Q₊ .
    rewrite (_ $ abs_mult _ _), (_ $ abs_of_nonneg (δ₂ / (δ₁ + δ₂))).
    mc_replace (δ₂ / (δ₁ + δ₂) * (|x - y|)) with (δ₂ * (|x - y|) / (δ₁ + δ₂)) on Q by setring Q.
    rewrite <-(mult_inv_le_cancel_l _ _ _).
    apply (order_preserving (δ₂ *.) _ _). subtransitivity ε. now apply (lt_le _ _).
Qed.

Hint Extern 2 (FinitePoints   the_ae_rationals) => eexact the_ae_rationals_finite_points : typeclass_instances.
Hint Extern 2 (LocatedPoints  the_ae_rationals) => eexact the_ae_rationals_located_points: typeclass_instances.
Hint Extern 2 (PrelengthSpace the_ae_rationals) => eexact the_ae_rationals_prelength     : typeclass_instances.

Lemma rationals_finite_points  `{Rationals (Q:=Q')} : FinitePoints Q'.    Proof isometric_finite_points  (r2r Q Q').
Lemma rationals_located_points `{Rationals (Q:=Q')} : LocatedPoints Q'.   Proof isometric_located_points (r2r Q Q').
Lemma rationals_prelength      `{Rationals (Q:=Q')} : PrelengthSpace Q'.  Proof isometric_prelength      (r2r Q Q').

Hint Extern 20 (FinitePoints ?Q) =>
  let H := constr:(_ : Rationals Q) in eapply (rationals_finite_points (H:=H)) : typeclass_instances.
Hint Extern 20 (LocatedPoints ?Q) =>
  let H := constr:(_ : Rationals Q) in eapply (rationals_located_points (H:=H)) : typeclass_instances.
Hint Extern 20 (PrelengthSpace ?Q) =>
  let H := constr:(_ : Rationals Q) in eapply (rationals_prelength (H:=H)) : typeclass_instances.

