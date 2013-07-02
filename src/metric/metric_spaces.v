Require Import
  abstract_algebra interfaces.orders interfaces.rationals interfaces.metric_spaces
  theory.setoids theory.jections theory.rings theory.rationals theory.powerset
  orders.rings orders.lattices orders.minmax
  orders.affinely_extended_field stdlib_field.

Local Notation AQ := TheAERationals.A.
Local Notation Q := the_ae_rationals.
Local Notation "Q∞" := (aff_ext Q).
Local Notation Qfull := (aff_ext_full Q).


Section another_rationals.
  Context `{Setoid (S:=X)}.
  Context `{Rationals (Q:=Q1)} `{Le _} `{Lt _} `{!FullPseudoSemiRingOrder Q1}.
  Context (b : Q1 → A → @Subset A).

  Context
    (ball_proper : Proper ((Q1⁺,=)==>(X,=)==>(X,=)==>impl) b )
    (refl: ∀ ε `{ε ∊ Q1⁺} , SubReflexive X (b ε) )
    (sym: ∀  ε `{ε ∊ Q1⁺} , SubSymmetric X (b ε) )
    (beq: ∀ x `{x ∊ X} y `{y ∊ X} , b 0 x y → x = y)
    (tri: ∀ ε₁ `{ε₁ ∊ Q1⁺} ε₂ `{ε₂ ∊ Q1⁺} x `{x ∊ X} y `{y ∊ X} z `{z ∊ X},
       b ε₁ x y → b ε₂ y z → b (ε₁ + ε₂) x z)
    (closed: ∀ ε `{ε ∊ Q1⁺} x `{x ∊ X} y `{y ∊ X},
       (∀ `{δ ∊ Q1₊}, b (ε+δ) x y) → b ε x y).

  Instance: Find_Proper_Signature (@b) 0 (Proper ((Q1⁺,=)==>(X,=)==>(X,=)==>impl) b) := ball_proper.

  Instance alt_Build_MetricSpace_ball : Ball X
     := λ ε x y, ε = ∞ ∨ (ε ∊ Q⁺ ∧ b (rationals_to_field Q Q1 ε) x y).

  Instance alt_Build_MetricSpace : MetricSpace X.
  Proof. split; unfold ball, alt_Build_MetricSpace_ball. apply _.
  * intros ?? [[??] E1] ?? E2 ?? E3 [E|[? E]]; [left|right].
    subtransitivity x. subsymmetry.
    assert (y ∊ Q⁺) by now rewrite <-(_ $ E1). split. apply _. revert E.
    apply ball_proper; trivial. red_sig. now rewrite <- (Q $ E1).
  * intros ε ? x ? y ? [E|[? _]]. rewrite (_ $ E). apply _. apply _.
  * intros x ? y ?. now left.
  * intros ε ? x ?. right. split. apply _. apply refl; apply _.
  * intros ε ? x ? y ? [?|[? E]]. now left. right. split. apply _. now apply sym; try apply _.
  * intros x ? y ? [?|[? E]]. destruct (uneq_ne 0 infty); trivial. exact (ae_inf_uneq_r _).
    revert E. rewrite (Q1⁺ $ preserves_0). now apply beq.
  * intros ε₁ ? ε₂ ? x ? y ? z ? [E1|[? E1]] E2.
    destruct (ae_inf_not_el). rewrite <-(_ $ E1). apply _.
    destruct E2 as [E2|[? E2]].
    destruct (ae_inf_not_el). rewrite <-(_ $ E2). apply _.
    right. split. apply _.
    rewrite (Q1⁺ $ preserves_plus _ _). apply tri with y; trivial; apply _.
  * intros ε ? x ? y ? P. right. split. apply _. apply (closed _ _ _ _ _ _). intros δ ?.
    destruct (P (rationals_to_field Q1 Q δ) _) as [E|[_ E]].
    destruct (uneq_ne (ε + rationals_to_field Q1 Q δ) infty); trivial. exact (ae_inf_uneq_r _).
    now rewrite (Q1⁺ $ preserves_plus _ _), (Q1⁺ $ to_rationals_involutive _) in E.
  Qed.
End another_rationals.

Lemma ball_proper0 : Find_Proper_Signature (@ball) 0
  (∀ A (Ae:Equiv A) (b:Ball A) X `{!@MetricSpace A X Ae b}, Proper ((Qfull,=)==>(X,=)==>(X,=)==>impl) ball).
Proof. red. intros. exact msp_ball_proper. Qed.

Section ball.
  Context `{MetricSpace (X:=X)}.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.

  Hint Extern 0 (Find_Proper_Signature (@ball) 0 _) => eexact ball_proper0 : typeclass_instances.
  Hint Extern 5 (SubReflexive _ (ball _)) => class_apply @msp_refl : typeclass_instances.
  Hint Extern 5 (SubSymmetric _ (ball _)) => class_apply @msp_sym : typeclass_instances.

  Instance ball_refl ε `{ε ∊ Q∞⁺} : SubReflexive X (ball ε).
  Proof. destruct (ae_decompose_nonneg ε) as [E|?]; [| apply _].
    intros ??. rewrite (_ $ E). exact (msp_ball_inf _ _).
  Qed.

  Instance ball_sym ε `{ε ∊ Qfull} : SubSymmetric X (ball ε).
  Proof. destruct (ae_decompose_full ε) as [? | [? U]].
    destruct (nonneg_or_neg (R:=Q∞) ε); intros x ? y ? E.
    destruct (ae_decompose_nonneg ε) as [E2|?]. rewrite (_ $ E2). exact (msp_ball_inf _ _).
    subsymmetry.
    destruct (neg_not_nonneg (R:=Q∞) ε). exact (msp_nonneg _ _ _ E).
    intros x ? y ? E. contradict U. cut (ε ∊ Q∞⁺). intro. apply _. exact (msp_nonneg _ _ _ E).
  Qed.

  Lemma ball_separated x `{x ∊ X} y `{y ∊ X} : ball 0 x y ↔ x = y.
  Proof. split. exact (msp_eq _ _). intro E. now rewrite (X $ E). Qed.

  Lemma ball_triangle ε₁ `{ε₁ ∊ Qfull} ε₂ `{ε₂ ∊ Qfull} x `{x ∊ X} y `{y ∊ X} z `{z ∊ X}
        : ball ε₁ x y → ball ε₂ y z → ball (ε₁ + ε₂) x z.
  Proof. intros E1 E2.
    pose proof msp_nonneg _ _ _ E1.
    pose proof msp_nonneg _ _ _ E2.
    destruct (ae_decompose_nonneg ε₁) as [E|?].
    rewrite (_ $ E), (_ $ ae_nonneg_plus_inf_l _). exact (msp_ball_inf _ _).
    destruct (ae_decompose_nonneg ε₂) as [E|?].
    rewrite (_ $ E), (_ $ ae_nonneg_plus_inf_r _). exact (msp_ball_inf _ _).
    now apply (msp_triangle _ _ _ y _).
  Qed.

  Lemma ball_nonneg ε `{ε ∊ Q} x `{x ∊ X} y `{y ∊ X} : ball ε x y → ε ∊ Q⁺.
  Proof. intro E. destruct (msp_nonneg _ _ _ E). now split. Qed.

  Lemma ball_weaken_plus ε `{ε ∊ Qfull} x `{x ∊ X} y `{y ∊ X}
        : ball ε x y → ∀ δ `{δ ∊ Q∞⁺}, ball (ε+δ) x y.
  Proof. intros E δ ?. now apply (ball_triangle _ _ _ y _). Qed.

  Lemma ball_weaken_minus ε `{ε ∊ Q} x `{x ∊ X} y `{y ∊ X}
        : ball ε x y → ∀ δ `{δ ∊ Q} `{δ - ε ∊ Q⁺}, ball δ x y.
  Proof. intros E δ ? ?. rewrite <- (_ $ plus_negate_r_split_alt ε δ).
    exact (ball_weaken_plus _ _ _ E _).
  Qed.

  Lemma ball_weaken_le ε `{ε ∊ Qfull} x `{x ∊ X} y `{y ∊ X}
        : ball ε x y → ∀ δ `{δ ∊ Qfull}, ε ≤ δ → ball δ x y.
  Proof. intros E δ ? E2.
    pose proof msp_nonneg _ _ _ E.
    pose proof ae_le_defined_r _ _ E2.
    destruct (ae_decompose_nonneg ε) as [E1|?].
      rewrite (_ $ E1) in E2.
      rewrite (_ $ ae_inf_le δ E2). exact (msp_ball_inf _ _).
    assert (δ ∊ Q∞⁺). split. apply _.
      apply (subtransitivity (S:=Q∞) _ ε _); trivial. now destruct (_ : ε ∊ Q⁺).
    destruct (ae_decompose_nonneg δ) as [E1|?].
      rewrite (_ $ E1). exact (msp_ball_inf _ _).
    rewrite <- (flip_nonneg_minus _ _) in E2.
    exact (ball_weaken_minus _ _ _ E _).
  Qed.

  Lemma ball_closed ε `{ε ∊ Q} x `{x ∊ X} y `{y ∊ X} :
       (∀ `{δ ∊ Q₊}, ball (ε+δ) x y) → ball ε x y.
  Proof. intro P. cut (ε ∊ Q⁺). intro. apply msp_closed; trivial.
    destruct (nonneg_or_neg ε); trivial.
    cut (ε/2 ∊ Q⁺). now apply (reflects_nonneg (.* inv 2)).
    apply (ball_nonneg _ x y).
    mc_replace (ε/2) with (ε + -ε/2) on Q by subfield Q.
    apply P. apply _.
  Qed.

  Lemma ball_closed_le ε `{ε ∊ Q} x `{x ∊ X} y `{y ∊ X} :
       (∀ `{δ ∊ Q}, ε < δ → ball δ x y) → ball ε x y.
  Proof. intro P. apply ball_closed; trivial.
    intros δ ?. apply P. apply _.
    exact (pos_plus_lt_compat_r _ _).
  Qed.

  Lemma equal_by_ball_closed x `{x ∊ X} y `{y ∊ X} :
       (∀ `{ε ∊ Q₊}, ball ε x y) → x = y.
  Proof. intro P. rewrite <-(ball_separated _ _). apply (ball_closed _ _ _).
    intros. rewrite (_ $ plus_0_l _). now apply P.
  Qed.

  Instance ball_subsetoid ε `{ε ∊ Qfull} x `{x ∊ X} : B ε x ⊆ X.
  Proof. unfold B. apply subsetoid_alt; try apply _. intros ?? E [? E1].
    split; [red |]; now rewrite <-E.
  Qed.

  Instance B_inhabited q `{q ∊ Q∞⁺} x `{x ∊ X} : Inhabited (B q x).
  Proof. exists x. split; [now red | apply _]. Qed.
  
  Instance B_morphism : Morphism (Qfull ⇒ X ⇒ (⊆ X)) B.
  Proof. apply binary_morphism_proper_back. intros ?? Eq ?? Ex. unfold_sigs. red_sig.
    split; intros [Bz ?]; red in Bz; split; try apply _; red.
    now rewrite <-(_ $ Eq), <-(_ $ Ex).
    now rewrite ->(_ $ Eq), ->(_ $ Ex).
  Qed.
  
  Instance B_order_preserving x `{x ∊ X} : OrderPreserving (Ble:=(⊆)) Qfull (⊆ X) (λ ε, B ε x).
  Proof. split. split; try apply _.
    (*rewrite <-(_ : SubsetOf (Qfull ⇒ (⊆ X)) (Q∞ ⇒ (⊆ X))). apply _.*)
    intros p ? q ? E. apply (subsetoid_from_subsetof X _ _). intros y [??].
    split; trivial. now apply (ball_weaken_le p).
  Qed.

  Lemma B_weaken_le ε `{ε ∊ Qfull} x `{x ∊ X} δ `{δ ∊ Qfull} : ε ≤ δ → B ε x ⊆ B δ x.
  Proof. intro E. destruct (ae_decompose_full ε) as [?|U].
     now apply (order_preserving (Ble:=(⊆)) (T:=(⊆ X)) (λ p, B p x)).
     apply (subsetoid_from_subsetof X _ _).
     intros ? [B' ?]. pose proof msp_nonneg _ _ _ B'. contradict U. firstorder.
  Qed.

  Lemma singleton_is_ball x `{x ∊ X} : {{x}} = B 0 x.
  Proof. intro y. unfold subset_singleton.
    change (y ∊ X ∧ y = x ↔ ball 0 x y ∧ y ∊ X). intuition.
    rewrite (ball_separated _ _); subsymmetry.
    rewrite <-(ball_separated _ _); subsymmetry.
  Qed.

End ball.

Lemma ball_proper: Find_Proper_Signature (@ball) 0
  (∀ A (Ae:Equiv A) (b:Ball A) X `{!@MetricSpace A X Ae b}, Proper ((Qfull,≤)++>(X,=)==>(X,=)==>impl) ball).
Proof. red. intros. intros p q [[??]Ep] ?? E1 ?? E2 ?.
  apply (msp_ball_proper _ _ (_:Proper(Qfull,=) q) _ _ E1 _ _ E2).
  unfold_sigs. now apply (ball_weaken_le p).
Qed.
Hint Extern 0 (Find_Proper_Signature (@ball) 0 _) => eexact ball_proper : typeclass_instances.

Lemma ball_proper1 : Find_Proper_Signature (@ball) 1
  (∀ A (Ae:Equiv A) (b:Ball A) X `{!@MetricSpace A X Ae b}, Proper ((Qfull,=)==>(X,=)==>(X,=)==>impl) ball).
Proof ball_proper0.
Hint Extern 0 (Find_Proper_Signature (@ball) 1 _) => eexact ball_proper1 : typeclass_instances.

Lemma B_proper: Find_Proper_Signature (@B) 0
  (∀ A (Ae:Equiv A) (b:Ball A) X `{!@MetricSpace A X Ae b}, Proper ((Qfull,=)==>(X,=)==>(=)) (B (X:=X))).
Proof. red; intros. intros p q Eq ?? Ex.
  now rewrite (binary_morphism_proper _ (m:=B_morphism) _ _ Eq _ _ Ex).
Qed.
Hint Extern 0 (Find_Proper_Signature (@B) 0 _) => eexact B_proper : typeclass_instances.

Lemma B_proper2: Find_Proper_Signature (@B) 1
  (∀ A (Ae:Equiv A) (b:Ball A) X `{!@MetricSpace A X Ae b}, Proper ((Qfull,≤)++>(X,=)==>(⊆)) (B (X:=X))).
Proof. red; intros. intros p q [[??]Eq] ?? Ex.
  rewrite (binary_morphism_proper _ (m:=B_morphism) _ _ (_:Proper (Qfull,=) p) _ _ Ex).
  unfold_sigs. now apply B_weaken_le.
Qed.
Hint Extern 0 (Find_Proper_Signature (@B) 1 _) => eexact B_proper2 : typeclass_instances.

Hint Extern 2 (SubReflexive _ (ball _)) => eapply @ball_refl : typeclass_instances.
Hint Extern 2 (SubSymmetric _ (ball _)) => eapply @ball_sym : typeclass_instances.
Hint Extern 2 (?x ∊ ball _ ?x) => now red : typeclass_instances.
Hint Extern 2 (_ ∊ ball ∞ _) => eapply @msp_ball_inf : typeclass_instances.
Hint Extern 3 (_ ∊ ball _ _) => red; solve [ trivial | subsymmetry ] : typeclass_instances.
Hint Extern 2 (@B _ ?X _ _ _ ⊆ ?X) => eapply @ball_subsetoid : typeclass_instances.
Hint Extern 3 (_ ∊ B _ _) => split : typeclass_instances.
Hint Extern 2 (?x ∊ B (X:=?X) _ ?x) => split; [red; apply (subreflexivity (S:=X) _)|] : typeclass_instances.
Hint Extern 2 (Inhabited (B _ _)) => eapply @B_inhabited : typeclass_instances.
Hint Extern 2 (Morphism _ B) => eapply @B_morphism : typeclass_instances.
Hint Extern 2 (OrderPreserving _ _ (λ ε, B ε ?x)) => eapply @B_order_preserving : typeclass_instances.

Section projected.
  Context `{X:Subset} `{Y:Subset} (f:X ⇀ Y) `{Setoid _ (S:=X)} `{MetricSpace _ (X:=Y)} `{!Injective X Y f}.

  Existing Instance injective_mor.

  Instance projected_ball : Ball X :=  λ ε x y, ball ε (f x) (f y).

  Instance projected_metric_space : MetricSpace X.
  Proof. split; unfold ball, projected_ball. apply _.
  + intros ?? E1 ?? E2 ?? E3 E. unfold_sigs. now rewrite <-(_ $ E1), <-(X $ E2), <-(X $ E3).
  + intros ε ? x ? y ? E. exact (msp_nonneg _ _ _ E).
  + intros x ? y ?. exact (msp_ball_inf _ _).
  + intros ε ? x ?. exact (msp_refl _ _ _).
  + intros ε ? x ? y ?. exact (msp_sym _ _ _ _ _).
  + intros x ? y ? E. apply (injective f _ _). exact (msp_eq _ _ E).
  + intros ε₁ ? ε₂ ? x ? y ? z ? E1 E2. now apply (msp_triangle _ _ _ (f y) _).
  + intros ε ? x ? y ? P. exact (msp_closed _ _ _ P).
  Qed.
End projected.

Lemma sub_metric_space `{MetricSpace (X:=X)} `{Y ⊆ X} : MetricSpace Y.
Proof. pose proof subsetoid_a. exact (projected_metric_space (id:Y ⇀ X)). Qed.

Lemma located_points `{MetricSpace (X:=X)} `{!LocatedPoints X}
  x `{x ∊ X} y `{y ∊ X} p `{p ∊ Qfull} q `{q ∊ Qfull} :
    p < q → ball q x y ∨ ¬ ball p x y .
Proof.
  intro E. destruct (ae_lt_defined _ _ E).
  destruct (decide_sub (le) 0 p) as [?|?].
  + assert (p ∊ Q∞⁺) by now split.
    assert (q ∊ Q∞₊). split. apply _. now apply (le_lt_trans _ p _).
    destruct (ae_decompose_nonneg p) as [Ep|?].
      rewrite (_ $ Ep) in E. contradict E.
      destruct (ae_decompose_pos q) as [Eq|?].
        intro E. rewrite (_ $ Eq) in E. now destruct (subirreflexivity (S:=Q∞) (<) infty).
        apply (lt_flip _ _). exact (ae_inf_sub _).
    destruct (ae_decompose_pos q) as [Eq|?].
    * left. rewrite (_ $ Eq). exact (msp_ball_inf _ _).
    * exact (located_points_def (X:=X) x y p q E).
  + right. intro Bp. now destruct (msp_nonneg _ _ _ Bp).
Qed.

Definition default_metric_uneq `{Ball A} : UnEq A := λ x y, ∃ `{q ∊ Q₊}, ¬ ball q x y  .
Lemma default_metric_inequality `{MetricSpace (X:=X)}
  : MetricInequality (Aue:=default_metric_uneq) X.
Proof. intros ????. reflexivity. Qed.
Hint Extern 2 (MetricInequality (Aue:=default_metric_uneq) _) => eapply @default_metric_inequality : typeclass_instances.

Section metric_inequality.
  Context `{MetricSpace (X:=X)} `{!MetricInequality (Aue:=Aue) X}.

  Instance metric_inequality_setoid : InequalitySetoid X.
  Proof. split. apply _.
  + intros ?? E1 ?? E2. unfold_sigs. red. rewrite !(metric_inequality _ _).
    intros [q[? P]]. exists_sub q. contradict P. now rewrite (_ $ E1), (_ $ E2).
  + intros ????. rewrite (metric_inequality _ _). intros [q[? P]]. contradict P.
    now rewrite (_ $ P).
  + intros ???? E. rewrite (metric_inequality _ _). intros [q[? []]]. now rewrite (_ $ E).
  Qed.

  Context `{!LocatedPoints X}.

  Instance metric_inequality_tight : TightApart X.
  Proof. intros x ? y ?. split.
  + rewrite (metric_inequality _ _).
    intros P. apply (equal_by_ball_closed _ _). intros q ?.
    destruct (located_points (X:=X) x y (q/2) q); trivial.
    rewrite <-(flip_pos_minus _ _). mc_replace (q-q/2) with (q/2) on Q by subfield Q. apply _.
    destruct P. now exists_sub (q/2).
  + exact (equiv_nue _ _).
  Qed.

  Instance metric_inequality_strong_setoid : StrongSetoid X.
  Proof. split; try apply _. split.
  + intros x ?. now apply (equiv_nue _ _).
  + intros x ? y ?. rewrite !(metric_inequality _ _).
    intros [q[? P]]. exists_sub q. contradict P. subsymmetry.
  + intros x ? y ?. rewrite (metric_inequality _ _).
    intros [q[? P]] z ?.
    destruct (located_points (X:=X) x z (q/3) (q/3+q/3)).
    rewrite <-(flip_pos_minus _ _). mc_replace (q/3+q/3-q/3) with (q/3) on Q by subring Q. apply _.
    right. rewrite (metric_inequality _ _). exists_sub (q/3). contradict P.
      mc_replace q with (q/3+q/3+q/3) on Q by subfield Q.
      now apply (ball_triangle _ _ _ z _).
    left. rewrite (metric_inequality _ _). now exists_sub (q/3).
  Qed.
End metric_inequality.  

Section ambient_join_meet.
  Context `{X:AmbientSpace} `{Equiv X} U V `{U ⊆ X} `{V ⊆ X}.

  Instance : Setoid X := subsetoid_b.

  Lemma ambient_union_subsetoid_l     : U ⊆ U ⊔ V. Proof join_ub_l (Ale:=(⊆)) (L:=(⊆ X)) U V.
  Lemma ambient_union_subsetoid_r     : V ⊆ U ⊔ V. Proof join_ub_r (Ale:=(⊆)) (L:=(⊆ X)) U V.
  Lemma ambient_intersect_subsetoid_l : U ⊓ V ⊆ U. Proof meet_lb_l (Ale:=(⊆)) (L:=(⊆ X)) U V.
  Lemma ambient_intersect_subsetoid_r : U ⊓ V ⊆ V. Proof meet_lb_r (Ale:=(⊆)) (L:=(⊆ X)) U V.
End ambient_join_meet.
Hint Extern 2 (?U ⊆ ?U ⊔ _) => eapply @ambient_union_subsetoid_l : typeclass_instances.
Hint Extern 2 (?V ⊆ _ ⊔ ?V) => eapply @ambient_union_subsetoid_r : typeclass_instances.
Hint Extern 2 (?U ⊓ _ ⊆ ?U) => eapply @ambient_intersect_subsetoid_l : typeclass_instances.
Hint Extern 2 (_ ⊓ ?V ⊆ ?V) => eapply @ambient_intersect_subsetoid_r : typeclass_instances.

Lemma closure_subsetoid1 `{MetricSpace (X:=X)} S `{S ⊆ X} : closure (X:=X) S ⊆ X.
Proof. apply subsetoid_alt; [ apply _ | | firstorder].
  intros ?? E [? P]. unfold_sigs. split. apply _.
  intros ε ?. destruct (P ε _) as [s [??]]. exists_sub s. now rewrite <-(_ $ E).
Qed.
Hint Extern 2 (@closure _ ?X _ _ ⊆ ?X) => eapply @closure_subsetoid1 : typeclass_instances.

Lemma closure_subsetoid2 `{MetricSpace (X:=X)} S `{S ⊆ X} : S ⊆ closure (X:=X) S.
Proof. apply (subsetoid_from_subsetof X _ _). intros s ?.
  split. apply _. intros ε ?. now exists_sub s.
Qed.
Hint Extern 2 (?S ⊆ closure ?S) => eapply @closure_subsetoid2 : typeclass_instances.
Hint Extern 2 (?f _ ∊ closure (X:=?X) ?f⁺¹(?S)) => apply (_ : f⁺¹(S) ⊆ closure (X:=X) f⁺¹(S)) : typeclass_instances.

Lemma closure_proper: Find_Proper_Signature (@closure) 0
  (∀ A (Ae:Equiv A) (b:Ball A) X `{!@MetricSpace A X Ae b}, Proper ((=)==>(=)) (closure (X:=X))).
Proof. red; intros. intros S T E ?. unfold closure.
  split; intros [? P]; (split; [apply _|]); intros ε ?;
  destruct (P ε _) as [s[el ?]]; [ rewrite E in el | rewrite <-E in el ];
  now exists_sub s.
Qed.
Hint Extern 0 (Find_Proper_Signature (@closure) 0 _) => eexact closure_proper : typeclass_instances.

Lemma closure_proper2: Find_Proper_Signature (@closure) 1
  (∀ A (Ae:Equiv A) (b:Ball A) X `{!@MetricSpace A X Ae b}, Proper (((⊆ X),⊆)++>(⊆)) (closure (X:=X))).
Proof. red; intros. intros S T [[el1 el2]E]. red in el1,el2.
  apply (subsetoid_from_subsetof X _ _). intros x [? P].
  split. apply _. intros ε ?. destruct (P ε _) as [s[??]]. now exists_sub s.
Qed.
Hint Extern 0 (Find_Proper_Signature (@closure) 1 _) => eexact closure_proper2 : typeclass_instances.

Lemma closure_ambient_proper `(X:Subset) `{Equiv X} `{Ball X} {Y U}
  : X=Y → closure (X:=X) U = closure (X:=Y) U .
Proof. intros E x. split.
+ intros [? P]. split;trivial. now rewrite <-E.
+ intros [? P]. split;trivial. now rewrite   E.
Qed.

Section closure.
  Context `{MetricSpace (X:=X)}.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.

  Lemma closure_order_preserving S T `{T ⊆ X} {E:S ⊆ T} : closure S ⊆ closure T.
  Proof. assert (S ⊆ X) by now transitivity T. rewrite ((⊆ X) $ E).
    pose proof subsetoid_a : Setoid (closure T). apply _.
  Qed.

  Lemma closure_empty : closure ⊥ = ⊥.
  Proof. split; [| intros []]. intros [? P]. destruct (P ∞ _) as [?[[]]]. Qed.

  Lemma closure_ambient : closure X = X.
  Proof. intro x. split. now intros [??]. intro.
    split. apply _. intros. now exists_sub x.
  Qed.

  Lemma closure_inhabited S `{S ⊆ X} `{!Inhabited S} : Inhabited (closure S).
  Proof. destruct (inhabited S) as [x ?]. exists x. now apply (_ : S ⊆ closure S). Qed.

  Lemma closure_idempotent S `{S ⊆ X} : closure (closure S) = closure S.
  Proof. apply (antisymmetry SubsetOf); [| apply _].
    intros x [? P1]. split. apply _. intros ε ?.
    destruct (P1 (ε/2) _) as [s[[? P2] ?]].
    destruct (P2 (ε/2) _) as [t[??]].
    exists_sub t. rewrite <-(_ $ ae_in_halves ε).
    now apply (ball_triangle _ _ _ s _).
  Qed.

  Lemma closure_closed S `{S ⊆ X} : Closed (closure S).
  Proof. split; try apply _. exact (closure_idempotent S). Qed.

  Lemma closure_dense S `{S ⊆ X} : Dense (X:=closure S) S.
  Proof. split; try apply _. exact sub_metric_space. firstorder. Qed.

  Lemma closure_union S `{S ⊆ X} T `{T ⊆ X}: closure S ⊔ closure T ⊆ closure (S ⊔ T).
  Proof. apply (subsetoid_from_subsetof X _ _).
    intros x [[? P]|[? P]]; (split; [apply _ |]); intros ε ?;
    destruct (P ε _) as [s [??]]; now exists_sub s.
  Qed.

  Lemma closure_singleton x `{x ∊ X} : closure {{x}} = {{x}}.
  Proof. apply (antisymmetry SubsetOf); [| apply _]. intros y [? P].
    split. apply _. apply (equal_by_ball_closed _ _). intros ε ?.
    destruct (P ε _) as [s [[? E] ?]]. now rewrite <-(_ $ E).
  Qed.
End closure.

Hint Extern 5 (closure _ ⊆ closure _) => eapply @closure_order_preserving : typeclass_instances.
Hint Extern 2 (Inhabited (closure _)) => eapply @closure_inhabited : typeclass_instances.
Hint Extern 2 (Closed (closure _)) => eapply @closure_closed : typeclass_instances.
Hint Extern 2 (Dense (X:=closure ?S) ?S) => eapply @closure_dense : typeclass_instances.

Lemma interior_subsetoid1 `{MetricSpace (X:=X)} S `{S ⊆ X} : interior (X:=X) S ⊆ X.
Proof. apply subsetoid_alt; [ apply _ | | firstorder].
  intros ?? E [? [q [??]]]. unfold_sigs. split. now rewrite <-(_ $ E).
  exists_sub q. now rewrite <-(_ $ E).
Qed.
Hint Extern 2 (@interior _ ?X _ _ ⊆ ?X) => eapply @interior_subsetoid1 : typeclass_instances.

Lemma interior_subsetoid2 `{MetricSpace (X:=X)} S `{S ⊆ X} : interior (X:=X) S ⊆ S.
Proof. apply (subsetoid_from_subsetof X _ _). firstorder. Qed.
Hint Extern 2 (?S° ⊆ ?S) => eapply @interior_subsetoid2 : typeclass_instances.

Lemma interior_proper: Find_Proper_Signature (@interior) 0
  (∀ A (Ae:Equiv A) (b:Ball A) X `{!@MetricSpace A X Ae b}, Proper ((=)==>(=)) (interior (X:=X))).
Proof. red; intros. intros S T E ?. unfold interior.
  split; intros [?[q[??]]]; (split; [now apply E |] ); exists_sub q.
  now rewrite <-E. now rewrite ->E.
Qed.
Hint Extern 0 (Find_Proper_Signature (@interior) 0 _) => eexact interior_proper : typeclass_instances.



Lemma dense `(S:Subset) `{Dense _ (X:=X) (S:=S)} x `{x ∊ X} ε `{ε ∊ Q∞₊} : ∃ `{s ∊ S}, ball ε x s.
Proof. pose proof (_ : x ∊ X) as el. rewrite <-dense_def in el.
  destruct el as [_ P]. now apply P.
Qed.

Lemma dense_image `{X:Subset} `{Equiv X} `{Y:Subset} `{Equiv Y} `{Ball Y}
  (f:X ⇀ Y) `{!Morphism (X ⇒ Y) f} (S:Subset) `{S ⊆ X} `{!Dense (X:=Y) f⁺¹(S)}
  y `{y ∊ Y} ε `{ε ∊ Q∞₊} : ∃ `{s ∊ S}, ball ε y (f s).
Proof. destruct (_ : Dense (X:=Y) f⁺¹(S)) as [?? _]. pose proof subsetoid_b : Setoid X.
  destruct (dense (X:=Y) f⁺¹(S) y ε) as [y'[[?[x[? Ex]]] B1]].
  exists_sub x. now rewrite (_ $ Ex).
Qed.

Lemma dense_refl `{MetricSpace (X:=X)} : Dense (X:=X) X.
Proof. split; try apply _. exact closure_ambient. Qed.
Hint Extern 5 (@Dense _ ?X _ _ ?X) => eapply @dense_refl : typeclass_instances.

Lemma dense_proper: Find_Proper_Signature (@Dense) 0
  (∀ A (Ae:Equiv A) (b:Ball A) (X:Subset), Proper ((=)==>impl) (Dense (X:=X))).
Proof. red; intros. intros S1 S2 E ?. pose proof dense_msp (X:=X).
  split. apply _. rewrite <-E. apply _.
  intros y. split. now intros [??]. intro. split. apply _.
  intros ε ?. destruct (dense (X:=X) S1 y ε) as [x[??]].
  assert (x ∊ S2). now apply E. now exists_sub x.
Qed.
Hint Extern 0 (Find_Proper_Signature (@Dense) 0 _) => eexact dense_proper : typeclass_instances.

Lemma dense_proper2: Find_Proper_Signature (@Dense) 1
  (∀ A (Ae:Equiv A) (b:Ball A) (X:Subset),
     Proper ((restrict_rel (⊆ X) SubsetOf)++>impl) (Dense (X:=X))).
Proof. red; intros. intros S1 S2 [[e1 e2] E] ?. red in e1,e2.
  pose proof dense_msp (X:=X). split; try apply _.
  intros y. split. now intros [??]. intro. split. apply _.
  intros ε ?. destruct (dense (X:=X) S1 y ε) as [x[??]].
  assert (x ∊ S2). now apply E. now exists_sub x.
Qed.
Hint Extern 0 (Find_Proper_Signature (@Dense) 1 _) => eexact dense_proper2 : typeclass_instances.

Lemma dense_ambient_proper `(X:Subset) `{Equiv X} `{Ball X} {Y U}
  : X=Y → Dense (X:=X) U ↔ Dense (X:=Y) U .
Proof. intro E. split.
+ intros [???]. split. assert (Y ⊆ X). rewrite <-E. apply _. exact sub_metric_space.
  now rewrite <-E. rewrite <-E at 2. rewrite <-dense_def. apply closure_ambient_proper. apply _. now symmetry.
+ intros [???]. split. assert (X ⊆ Y). rewrite   E. apply _. exact (sub_metric_space (X:=Y)).
  now rewrite E. rewrite E at 2. rewrite <-dense_def. apply closure_ambient_proper. apply _. trivial.
Qed.

Lemma dense_id_image `{Y:Subset} `{Dense _ (X:=Y) (S:=X)} : Dense (X:=Y) (image (X:=Y) (Y:=Y) id X).
Proof. destruct (_ : Dense (X:=Y) X) as [?? _]. now rewrite (image_id X). Qed.
Hint Extern 4 (Dense id⁺¹(_)) => eapply @dense_id_image : typeclass_instances.


Lemma closed `(S:Subset) `{Closed _ (X:=X) (S:=S)} : closure (X:=X) S = S.
Proof closed_def.

Section closed.
  Context `{MetricSpace (X:=X)}.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.

  Lemma closed_empty : Closed ⊥.
  Proof. split; try apply _. exact closure_empty. Qed.

  Lemma closed_ambient : Closed X.
  Proof. split; try apply _. exact closure_ambient. Qed.

End closed.

Hint Extern 2 (Closed ⊥) => eapply @closed_empty : typeclass_instances.
Hint Extern 2 (@Closed _ ?X _ _ ?X) => eapply @closed_ambient : typeclass_instances.

Lemma open `(S:Subset) `{Open _ (X:=X) (S:=S)} x `{x ∊ S} : ∃ `{q ∊ Q∞₊}, B q x ⊆ S.
Proof. destruct (_ : Open S) as [?? _].
  pose proof (_ : x ∊ S) as el. rewrite <-open_def in el.
  destruct el as [_ [q [??]]]. exists_sub q. now apply (subsetoid_from_subsetof X _ _).
Qed.

Lemma open_proper: Find_Proper_Signature (@Open) 0
  (∀ A (Ae:Equiv A) (b:Ball A) (X:Subset), Proper ((=)==>impl) (Open (X:=X))).
Proof. red; intros. intros U V E ?. pose proof open_msp (X:=X).
  assert (V ⊆ X) by (rewrite <-E; apply _).
  split; try apply _. apply (subsetof_antisym). apply _.
  intros x el. split. apply _. rewrite <-E in el.
  destruct (open (X:=X) U x) as [q[??]].
  exists_sub q. rewrite <-E; apply _.
Qed.
Hint Extern 0 (Find_Proper_Signature (@Open) 0 _) => eexact open_proper : typeclass_instances.

Section open.
  Context `{MetricSpace (X:=X)}.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.

  Lemma open_empty : Open ⊥.
  Proof. firstorder. Qed.

  Lemma open_ambient : Open X.
  Proof. split; try apply _. split. now intros [??]. intros ?. split. apply _.
    exists_sub ∞. apply _.
  Qed.

  Lemma open_union U V : Open U → Open V → Open (U ⊔ V).
  Proof. intros ??. split; try apply _.
    apply (subsetof_antisym). apply _.
    intros x [?|?].
    destruct (open U x) as [q[??]]. split. apply _. exists_sub q.
      transitivity U; apply _.
    destruct (open V x) as [q[??]]. split. apply _. exists_sub q.
      transitivity V; apply _.
  Qed.

  Lemma open_intersection U V : Open U → Open V → Open (U ⊓ V).
  Proof. intros ??. split; try apply _.
    apply (subsetof_antisym). apply _.
    intros x [??]. pose proof _ : U ⊆ X.
    destruct (open U x) as [a[? Ba]]. destruct (open V x) as [b[? Bb]].
    ae_rat_set_min c a b Ea Eb. split. apply _. exists_sub c.
    apply (meet_glb (Ale:=SubsetOf) (L:=every Subset) U V _); unfold le; intros y [By ?];
    [ rewrite <-Ba | rewrite <-Bb ]; split; trivial; red.
    now rewrite <-(Q∞ $ Ea). now rewrite <-(Q∞ $ Eb).
  Qed.
End open.

Hint Extern 2 (Open ⊥) => eapply @open_empty : typeclass_instances.
Hint Extern 2 (@Open _ ?X _ _ ?X) => eapply @open_ambient : typeclass_instances.
Hint Extern 5 (Open (_ ⊔ _)) => eapply @open_union : typeclass_instances.
Hint Extern 5 (Open (_ ⊓ _)) => eapply @open_intersection : typeclass_instances.

Lemma bounded_proper: Find_Proper_Signature (@Bounded) 0
  (∀ A (Ae:Equiv A) (b:Ball A) (X:Subset), Proper ((⊆)-->impl) (Bounded (X:=X))).
Proof. red; intros. intros U V E ?. unfold flip in E. pose proof bounded_msp (X:=X).
  assert (V ⊆ X) by (rewrite E; apply _).
  split; try apply _.
  destruct (bounded (X:=X) U) as [d [? P]]. exists_sub d. intros. apply P; apply _.
Qed.
Hint Extern 0 (Find_Proper_Signature (@Bounded) 0 _) => eexact bounded_proper : typeclass_instances.

Lemma bounded_proper2: Find_Proper_Signature (@Bounded) 1
  (∀ A (Ae:Equiv A) (b:Ball A) (X:Subset), Proper ((=)==>impl) (Bounded (X:=X))).
Proof. red; intros. intros U V E ?.
  assert (V ⊆ U) as E2. rewrite <-E. pose proof subsetoid_a : Setoid U. apply _.
  now rewrite E2.
Qed.
Hint Extern 0 (Find_Proper_Signature (@Bounded) 1 _) => eexact bounded_proper2 : typeclass_instances.

Section bounded.
  Context `{MetricSpace (X:=X)}.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.

  Lemma empty_bounded : Bounded ⊥.
  Proof. split; try apply _. exists_sub 0. intros ? []. Qed.

  Lemma ball_bounded q `{q ∊ Q⁺} x `{x ∊ X} : Bounded (B q x).
  Proof. split; try apply _. exists_sub (q+q).
    intros y [??] z [??]. apply (ball_triangle _ _ _ x _). subsymmetry. assumption.
  Qed.

  Lemma interior_bounded (U:Subset) `{!Bounded U} : Bounded U°.
  Proof. now rewrite (_ : U° ⊆ U). Qed. 

  Lemma closure_bounded (U:Subset) `{!Bounded U} : Bounded (closure U).
  Proof. split; try apply _.
    destruct (bounded U) as [d[el P]].
    exists_sub d.
    intros x [? P1] y [? P2].
    apply (ball_closed _ _ _). intros ε ?.
    mc_replace (d+ε) with (ε/2+d+ε/2) on Q by subfield Q.
    destruct (P1 (ε/2) _) as [x'[??]].
    destruct (P2 (ε/2) _) as [y'[??]].
    pose proof (_ : U ⊆ X).
    apply (ball_triangle _ _ _ y' _); [| subsymmetry].
    apply (ball_triangle _ _ _ x' _); trivial.
    now apply P.
  Qed.

  Lemma bounded_intersection (U V:Subset) `{!Bounded U} `{!Bounded V} : Bounded (U ⊓ V).
  Proof.
    destruct (bounded U) as [d1 [eld1 P1]].
    destruct (bounded V) as [d2 [eld2 P2]].
    split; try apply _.
    destruct (decide_sub (≤) d1 d2).
    * exists_sub d1. intros x [??] y [??]. now apply P1.
    * exists_sub d2. intros x [??] y [??]. now apply P2.
  Qed.

  Lemma bounded_union `{!FinitePoints X} (U V:Subset)
    `{!Bounded U} `{!Bounded V} `{!Inhabited U} `{!Inhabited V} : Bounded (U ⊔ V).
  Proof.
    destruct (bounded U) as [d1 [eld1 P1]].
    destruct (bounded V) as [d2 [eld2 P2]].
    destruct (inhabited U) as [u ?].
    destruct (inhabited V) as [v ?].
    assert (∀ x, x ∊ U → x ∊ X) by (intros; now apply (_ : U ⊆ X)).
    assert (∀ x, x ∊ V → x ∊ X) by (intros; now apply (_ : V ⊆ X)).
    destruct (finite_points u v) as [q[elq Buv]].
    split; try apply _. exists_sub (d1+q+d2). intros x [?|?] y [?|?].
    apply ball_weaken_le with d1; try apply _. now apply P1.
      apply (flip_nonneg_minus _ _). mc_replace (d1+q+d2-d1) with (q+d2) on Q by subring Q. apply _.
    apply (ball_triangle _ _ _ v _). apply (ball_triangle _ _ _ u _); trivial. now apply P1. now apply P2.
    subsymmetry.
    apply (ball_triangle _ _ _ v _). apply (ball_triangle _ _ _ u _); trivial. now apply P1. now apply P2.
    apply ball_weaken_le with d2; try apply _. now apply P2.
      apply (flip_nonneg_minus _ _). mc_replace (d1+q+d2-d2) with (q+d1) on Q by subring Q. apply _.
  Qed.

End bounded.
Hint Extern 2 (Bounded ⊥) => eapply @empty_bounded : typeclass_instances.
Hint Extern 2 (Bounded (B _ _)) => eapply @ball_bounded : typeclass_instances.
Hint Extern 2 (Bounded _°) => eapply @interior_bounded : typeclass_instances.
Hint Extern 2 (Bounded (closure _)) => eapply @closure_bounded : typeclass_instances.
Hint Extern 2 (Bounded (_ ⊓ _)) => eapply @bounded_intersection : typeclass_instances.
Hint Extern 5 (Bounded (_ ⊔ _)) => eapply @bounded_union : typeclass_instances.

Instance complement_proper `{MetricSpace (X:=X)} : Proper ((=)==>(=)) (@tilde  _ (@complement _ X _)).
Proof. intros S T E ?.
  split; intros [? P]; (split; [ apply _ |]); intros s el; apply E in el; now apply P.
Qed.

Instance metric_complement_proper `{MetricSpace (X:=X)} : Proper ((=)==>(=)) (@negate  _ (@metric_complement _ X _)).
Proof. intros S T E ?.
  split; intros [?[q[? P]]]; (split; [ apply _ |]); exists_sub q;
  intros s el; apply E in el; now apply P.
Qed.

Lemma metric_complement_stable_proper: Find_Proper_Signature (@MetricComplementStable) 0
  (∀ A (Ae:Equiv A) (b:Ball A) X `{!@MetricSpace A X Ae b},
     Proper ((=)==>impl) (MetricComplementStable (X:=X))).
Proof. red; intros. intros S T E ?. red. now rewrite <-E. Qed.
Hint Extern 0 (Find_Proper_Signature (@MetricComplementStable) 0 _) => eexact metric_complement_stable_proper : typeclass_instances.

Lemma set_separated_proper: Find_Proper_Signature (@set_separated) 0
  (∀ A (Ae:Equiv A) (b:Ball A) X `{!@MetricSpace A X Ae b} q,
     Proper ((SubsetOf)-->(SubsetOf)-->impl) (set_separated (X:=X) q)).
Proof. red; intros. intros U1 U2 EU V1 V2 EV P.
  intros u elu v elv. rewrite <-EU in elu. rewrite <-EV in elv. now apply P.
Qed.
Hint Extern 0 (Find_Proper_Signature (@set_separated) 0 _) => eexact set_separated_proper : typeclass_instances.

Lemma set_separated_proper2: Find_Proper_Signature (@set_separated) 1
  (∀ A (Ae:Equiv A) (b:Ball A) X `{!@MetricSpace A X Ae b},
     Proper ((Qfull,≤)-->((⊆ X),=)==>((⊆ X),=)==>impl) (set_separated (X:=X))).
Proof. red; intros. intros ?? Eq U1 U2 [[e1 e2]EU] V1 V2 [[e3 e4] EV] P. red in e1,e2,e3,e4.
  unfold flip in *. unfold_sigs.
  intros u elu v elv. rewrite <-EU in elu. rewrite <-EV in elv. intro.
  apply (P u _ v _).
  assert (u ∊ X) by now apply (_ : U1 ⊆ X).
  assert (v ∊ X) by now apply (_ : V1 ⊆ X).
  now rewrite <-(Qfull $ Eq).
Qed.
Hint Extern 0 (Find_Proper_Signature (@set_separated) 1 _) => eexact set_separated_proper2 : typeclass_instances.

Lemma set_apart_proper: Find_Proper_Signature (@SetApart) 0
  (∀ A (Ae:Equiv A) (b:Ball A) X `{!@MetricSpace A X Ae b},
     Proper ((SubsetOf)-->(SubsetOf)-->impl) (SetApart (X:=X))).
Proof. red; intros. intros ?? E1 ?? E2 [d[? P]] . exists_sub d. now rewrite <-E1, <-E2. Qed.
Hint Extern 0 (Find_Proper_Signature (@SetApart) 0 _) => eexact set_apart_proper : typeclass_instances.

Definition ambient_space_powerset `{X:AmbientSpace} `{Equiv X} := (⊆ X).
Hint Extern 20 (@Subset (@Subset ?A)) =>
  let S := constr:(@ambient_space_powerset A _ _) in 
  let S' := eval unfold ambient_space_powerset in S in
  eexact S'
: typeclass_instances.

Section set_apart.
  Context `{MetricSpace (X:=X)}.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.

  Instance set_separated_sym q `{q ∊ Qfull} : SubSymmetric _ (set_separated (X:=X) q).
  Proof. intros U el1 V el2 P. red in el1,el2. intros u ? v ? E.
    assert (v ∊ X) by now apply (_ : U ⊆ X). subsymmetry in E. revert E. now apply P.
  Qed.

  Instance set_apart_sym : SubSymmetric _ (SetApart (X:=X)).
  Proof. intros U el1 V el2 [q[? P]]. exists_sub q. subsymmetry. Qed.

  Instance set_apart_empty_l (U : Subset) `{U ⊆ X} : SetApart ⊥ U.
  Proof. exists_sub ∞. intros ? []. Qed.

  Instance set_apart_empty_r (U : Subset) `{U ⊆ X} : SetApart U ⊥.
  Proof. exists_sub ∞. intros ? ? ? []. Qed.

  Lemma set_separated_closure_l (U V : Subset) `{U ⊆ X} `{V ⊆ X}
    q `{q ∊ Qfull} p `{p ∊ Qfull} :
    set_separated q U V → p < q → set_separated p (closure U) V.
  Proof. intros P E. destruct (ae_lt_defined _ _ E).
    intros u [? Cu] v ? Buv.
    pose proof (msp_nonneg _ _ _ Buv).
    assert (q ∊ Q∞₊).
      split. apply _. apply (le_lt_trans (P:=Qfull) _ p _); trivial.
      now destruct (_ : p ∊ Q∞⁺).
    assert (v ∊ X) by now apply (_ : V ⊆ X).
    destruct (ae_decompose_pos q) as [Eq|?].
      destruct (Cu ∞ _) as [s[? _]]. assert (s ∊ X) by now apply (_ : U ⊆ X).
      destruct (P s _ v _). rewrite (_ $ Eq). exact (msp_ball_inf _ _).
    assert (p ∊ Q⁺). apply (ae_nonneg_finite_bound _ q). now apply (lt_le (P:=Qfull) _ _).
    assert (q-p ∊ Q₊) by now apply (flip_pos_minus _ _).
    destruct (Cu (q-p) _) as [u'[??]]. assert (u' ∊ X) by now apply (_ : U ⊆ X).
    apply (P u' _ v _).
    mc_replace q with ((q-p)+p) on Q by subring Q.
    apply (ball_triangle _ _ _ u _); trivial. subsymmetry.
  Qed.

  Lemma set_separated_closure_r (U V : Subset) `{U ⊆ X} `{V ⊆ X}
    q `{q ∊ Qfull} p `{p ∊ Qfull} :
    set_separated q U V → p < q → set_separated p U (closure V).
  Proof. intros P E. subsymmetry in P. subsymmetry. now apply (set_separated_closure_l _ _ q p). Qed.

  Instance set_apart_closure_l (U V : Subset) `{U ⊆ X} `{V ⊆ X} `{!SetApart U V} : SetApart (closure U) V.
  Proof. destruct (set_apart U V) as [q[? P]].
    destruct (ae_decompose_pos q) as [Eq|?];
      [ exists_sub 1 | exists_sub (q/2) ];
    apply (set_separated_closure_l _ _ q _); trivial.
    rewrite (_ $ Eq). exact (ae_inf_sub _).
    rewrite <-(flip_pos_minus _ _).
    mc_replace (q-q/2) with (q/2) on Q by subfield Q. apply _.
  Qed.
  
  Context (U V : Subset) `{U ⊆ X} `{V ⊆ X} `{!SetApart U V}.

  Lemma set_apart_closure_r  : SetApart U (closure V).
  Proof. subsymmetry. assert (SetApart V U) by subsymmetry. apply _. Qed.

  Lemma set_apart_finite : ∃ q `{q ∊ Q₊}, set_separated q U V.
  Proof. destruct (set_apart U V) as [q [??]].
    destruct (ae_decompose_pos q) as [Eq|?]; [| now exists_sub q].
    exists_sub 1.
    assert (1 ≤ q) as E by (rewrite (_ $ Eq); exact (ae_inf_ub _)).
    now rewrite (Qfull $ E).
  Qed.

End set_apart.
Hint Extern 2 (SubSymmetric _ (set_separated _)) => eapply @set_separated_sym : typeclass_instances.
Hint Extern 2 (SubSymmetric _ SetApart) => eapply @set_separated_sym : typeclass_instances.
Hint Extern 2 (SetApart ⊥ _) => eapply @set_apart_empty_l : typeclass_instances.
Hint Extern 2 (SetApart _ ⊥) => eapply @set_apart_empty_r : typeclass_instances.
Hint Extern 2 (SetApart (closure _) _) => eapply @set_apart_closure_l : typeclass_instances.
Hint Extern 2 (SetApart _ (closure _)) => eapply @set_apart_closure_r : typeclass_instances.

Section complements.
  Context `{MetricSpace (X:=X)}.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.

  Instance complement_subsetoid (S:Subset) `{S ⊆ X} : ∼S ⊆ X.
  Proof. apply subsetoid_alt; [ apply _ | | firstorder].
    intros ?? E [? P]. unfold_sigs. split. apply _. intros s ?.
    destruct (P s _) as [q [??]]. exists_sub q.
    now rewrite <-(X $ E).
  Qed.

  Instance metric_complement_subsetoid (S:Subset) `{S ⊆ X} : -S ⊆ X.
  Proof. apply subsetoid_alt; [ apply _ | | firstorder].
    intros ?? E [? [q [? P]]]. unfold_sigs. split. apply _.
    exists_sub q. intros s ?. rewrite <-(X $ E). now apply P.
  Qed.

  Instance metric_complement_complement (S:Subset) `{S ⊆ X} : -S ⊆ ∼S.
  Proof. apply (subsetoid_from_subsetof X _ _).
    intros x [?[q[? P]]]. split. apply _. intros s ?. exists_sub q. exact (P _ _).
  Qed.

  Lemma complement_contradiction (S:Subset) `{S ⊆ X} x `{x ∊ S} `{x ∊ ∼S} : False.
  Proof. destruct (_ : x ∊ ∼S) as [? P].
    now destruct (P x _) as [q [? []]].
  Qed.

  Lemma metric_complement_contradiction (S:Subset) `{S ⊆ X} x `{x ∊ S} `{x ∊ -S} : False.
  Proof. pose proof _ : -S ⊆ ∼S. exact (complement_contradiction S x). Qed.

  Lemma complement_flip (S T:Subset) `{T ⊆ X} `{S ⊆ T} : ∼T ⊆ ∼S.
  Proof. assert (S ⊆ X) by now transitivity T.
    apply (subsetoid_from_subsetof X _ _).
    intros x [? P]. split. apply _. intros s ?. apply (P s _).
  Qed.

  Lemma metric_complement_flip (S T:Subset) `{T ⊆ X} `{S ⊆ T} : -T ⊆ -S.
  Proof. assert (S ⊆ X) by now transitivity T.
    apply (subsetoid_from_subsetof X _ _).
    intros x [? [q [? P]]]. split. apply _. exists_sub q. intros s ?. apply (P s _).
  Qed.

  Instance complement_complement (S:Subset) `{S ⊆ X} : S ⊆ ∼∼S.
  Proof.
    apply (subsetoid_from_subsetof X _ _).
    intros s ?. split. apply _.
    intros x [? P]. destruct (P s _) as [q[? Bxs]].
    exists_sub q. contradict Bxs. subsymmetry.
  Qed.

  Instance complement_metric_complement (S:Subset) `{S ⊆ X} : S ⊆ ∼-S.
  Proof.
    apply (subsetoid_from_subsetof X _ _).
    intros s ?. split. apply _. intros s' [?[q [? P]]].
    exists_sub q. intros Bs. subsymmetry in Bs. revert Bs. now apply P.
  Qed.

  Lemma metric_apartness_A4 (S T:Subset) `{S ⊆ X} `{T ⊆ X} : -S ⊆ ∼T → -S ⊆ -T.
  Proof. intro E.
    apply (subsetoid_from_subsetof X _ _).
    intros s [? [q [? P]]]. split. apply _.
    exists_sub (q/2). intros t ? Bst.
    assert (t ∊ X). now rewrite <-(_ : T ⊆ X).
    assert (t ∊ - S). split. apply _.
      exists_sub (q/2). intros s' ? Bts'.
      pose proof _ : q/2 ∊ Q∞₊ .
      assert (s' ∊ X) by now rewrite <-(_ : S ⊆ X).
      pose proof ball_triangle _ _ _ _ _ Bst Bts' as Bss'.
      rewrite (_ $ ae_in_halves _) in Bss'.
      revert Bss'. now apply P.
    destruct (_ : t ∊ ∼ T) as [_ P'].
    now destruct (P' t _) as [q'[?[]]].
  Qed.

  Lemma complement_empty : ∼⊥ = X. Proof. firstorder. Qed.
  Lemma metric_complement_empty : -⊥ = X.
  Proof. apply (antisymmetry SubsetOf). apply _.
    intros ??. split. apply _. exists_sub ∞. intros ? [].
  Qed.

  Lemma complement_ambient : ∼X = ⊥.
  Proof. intro x. split; [| intros []]. intros [? P].
    destruct (P x _) as [?[? P']]. now destruct P'.
  Qed.

  Lemma metric_complement_ambient : -X = ⊥.
  Proof. intro x. split; [| intros []]. intros [?[?[? P]]]. now destruct (P x _). Qed.

  Lemma complement_union (S T:Subset) `{S ⊆ X} `{T ⊆ X} : ∼(S ⊔ T) = ∼S ⊓ ∼T.
  Proof. intro x. split.
  + intros [? P]. split; (split; [apply _|]); intros s ?; exact (P s _).
  + intros [[? P1][_ P2]]. split. apply _.
    intros s [?|?]. now apply P1. now apply P2.
  Qed.

  Lemma metric_complement_union (S T:Subset) `{S ⊆ X} `{T ⊆ X} : -(S ⊔ T) = -S ⊓ -T.
  Proof. intro x. split.
  + intros [? [q [? P]]]. split; (split; [apply _|]); exists_sub q; intros s ?; apply (P _ _).
  + intros [[? [p [? P1]]][_ [q [? P2]]]].
    ae_rat_set_min r p q E1 E2.
    split. apply _. exists_sub r. intros s [?|?];
    assert (s ∊ X) by now apply (_ : S ⊔ T  ⊆ X), _.
    rewrite (Qfull $ E1); now apply P1.
    rewrite (Qfull $ E2); now apply P2.
  Qed.

  Lemma complement_intersection (S T:Subset) `{S ⊆ X} `{T ⊆ X} : ∼S ⊔ ∼T ⊆ ∼(S ⊓ T).
  Proof. apply (subsetoid_from_subsetof X _ _).
    intros x [[? P]|[? P]]; (split; [apply _|]); intros s [??]; now apply P.
  Qed.

  Instance metric_complement_is_stable (S:Subset) `{S ⊆ X} : MetricComplementStable (-S).
  Proof. split.
  + intros [? [q [? P]]]. split. apply _. exists_sub q. intros s ?.
    assert (s ∊ ∼-S) by now apply (_ : S ⊆ ∼-S). now apply P.
  + intros ?. now apply (metric_apartness_A4 _ _ (_ : -S ⊆ ∼∼-S)).
  Qed.

  Lemma metric_complement_open_apart (S:Subset) `{S ⊆ X} x `{x ∊ -S} : ∃ `{q ∊ Q∞₊},
    SetApart (B q x) S.
  Proof.
    destruct (_ : x ∊ - S) as [?[q [? P]]].
    exists_sub (q/2). exists_sub (q/2).
    intros y [By ?]. red in By. intros s ?.
    pose proof P s _ as P'. contradict P'.
    rewrite <-(_ $ ae_in_halves q).
    apply (ball_triangle _ _ _ y _); trivial.
  Qed.

  Lemma metric_complement_open_apart_finite (S:Subset) `{S ⊆ X} x `{x ∊ -S} : ∃ `{q ∊ Q₊},
    SetApart (B q x) S.
  Proof. destruct (metric_complement_open_apart S x) as [q[??]].
    destruct (ae_decompose_pos q) as [E|?]; [| exists_sub q; intuition ].
    exists_sub 1. destruct (_ : x ∊ -S). assert (B 1 x ⊆ B q x) as E2.
    apply (B_order_preserving); try apply _. rewrite (_ $ E). exact (ae_inf_ub _).
    now rewrite E2.
  Qed.

  Instance set_apart_in_metric_complement (U V : Subset) `{U ⊆ X} `{V ⊆ X}
    `{!SetApart U V} : U ⊆ -V.
  Proof. destruct (set_apart U V) as [q [el P]].
    apply (subsetoid_from_subsetof X _ _). intros x ?.
    assert (x ∊ X) by now apply (_ : U ⊆ X).
    split. apply _. exists_sub q. now apply P.
  Qed.

  Instance metric_complement_open (S:Subset) `{S ⊆ X} : Open (-S).
  Proof. split; try apply _. intro x. split. now intros [??].
    intro. split. apply _.
    destruct (metric_complement_open_apart S x) as [q[??]].
    exists_sub q. assert (x ∊ X) by now apply (_:-S ⊆ X). apply _.
  Qed.

  Lemma metric_complement_stable_open (S:Subset) `{S ⊆ X} `{!MetricComplementStable S} : Open S.
  Proof. rewrite <-(metric_complement_stable S). apply _. Qed.

  Lemma ambient_space_stable : MetricComplementStable X.
  Proof. rewrite <-(metric_complement_empty) at 2. apply _. Qed.

  Lemma empty_metric_complement_stable : MetricComplementStable ⊥.
  Proof. rewrite <-(metric_complement_ambient). apply _. Qed.

  Instance set_apart_complement_ambient_l (U : Subset) `{U ⊆ X} : SetApart (∼X) U.
  Proof. rewrite complement_ambient. apply _. Qed.

  Instance set_apart_complement_ambient_r (U : Subset) `{U ⊆ X} : SetApart U (∼X).
  Proof. rewrite complement_ambient. apply _. Qed.

  Context `{!MetricInequality (Aue:=Aue) X}.

  Lemma singleton_is_complement `{!LocatedPoints X}
    x `{x ∊ X} : {{ x }} = ∼((λ y, y ∊ X ∧ PropHolds (y ≠ x)) : Subset).
  Proof. pose proof metric_inequality_strong_setoid.
    intros y. split.
  + intros [? E]. split. apply _. intros z [? E2]. change (z ≠ x) in E2.
    rewrite (metric_inequality _ _) in E2. destruct E2 as [q[? P]].
    exists_sub q. contradict P. rewrite <-(_ $ E). subsymmetry.
  + intros [? P]. split. apply _. rewrite <-(tight_apart _ _). intro.
    destruct (P y) as [q[?[]]]; [now split|easy].
  Qed.
   
  Lemma singleton_metric_complement 
    x `{x ∊ X} : ((λ y, y ∊ X ∧ PropHolds (y ≠ x)) : Subset) = -{{ x }}.
  Proof. intros y. split.
  + intros [? E]. rewrite (metric_inequality _ _) in E. destruct E as [q[? P]].
    split. apply _. exists_sub q. intros s [? E2]. now rewrite (_ $ E2).
  + intros [?[q[? P]]]. split. apply _. red. rewrite (metric_inequality _ _).
    destruct (ae_decompose_pos q) as [Eq|].
      destruct (P x _). rewrite (_ $ Eq). exact (msp_ball_inf _ _). 
    exists_sub q. exact (P x _).
  Qed. 

  Lemma zero_is_complement `{!LocatedPoints X} `{Zero _} `{0 ∊ X} : {{ 0 }} = ∼(X ₀).
  Proof singleton_is_complement 0.

  Lemma nonzero_is_metric_complement `{Zero _} `{0 ∊ X} : X ₀ = -{{ 0 }}.
  Proof singleton_metric_complement 0.

  Instance nonzero_metric_complement_stable `{Zero _} `{0 ∊ X}
    : MetricComplementStable (X ₀).
  Proof. rewrite nonzero_is_metric_complement. apply _. Qed.
    
End complements.
Hint Extern 2 (@tilde _ (@complement _ ?X _) _ ⊆ ?X) => eapply @complement_subsetoid : typeclass_instances.
Hint Extern 2 (@negate _ (@metric_complement _ ?X _) _ ⊆ ?X) => eapply @metric_complement_subsetoid : typeclass_instances.
Hint Extern 2 (- ?S ⊆ ∼ ?S) => eapply @metric_complement_complement : typeclass_instances.
Hint Extern 2 (?S ⊆ ∼∼ ?S) => eapply @complement_complement : typeclass_instances.
Hint Extern 2 (?S ⊆ ∼- ?S) => eapply @complement_metric_complement : typeclass_instances.
Hint Extern 2 (MetricComplementStable (-_)) => eapply @metric_complement_is_stable : typeclass_instances.
Hint Extern 2 (Open (-_)) => eapply @metric_complement_open : typeclass_instances.
Hint Extern 2 (@MetricComplementStable _ ?X _ ?X) => eapply @ambient_space_stable : typeclass_instances.
Hint Extern 2 (MetricComplementStable ⊥) => eapply @empty_metric_complement_stable : typeclass_instances.
Hint Extern 5 (∼ _ ⊆ ∼ _) => eapply @complement_flip : typeclass_instances.
Hint Extern 5 (- _ ⊆ - _) => eapply @metric_complement_flip : typeclass_instances.
Hint Extern 2 (SetApart (X:=?X) (∼ ?X) _) => eapply @set_apart_complement_ambient_l : typeclass_instances.
Hint Extern 2 (SetApart (X:=?X) _ (∼ ?X)) => eapply @set_apart_complement_ambient_r : typeclass_instances.
Hint Extern 2 (MetricComplementStable (_ ₀)) => eapply @nonzero_metric_complement_stable : typeclass_instances.

Section well_contained_alt.
  Context `{MetricSpace (X:=X)}.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.

  Lemma well_contained_alt (U V : Subset) `{V ⊆ X}
    : U ⊆ V → Bounded U → Inhabited U → SetApart U (∼V) → U ⊂⊂ V.
  Proof. intros. split; apply _. Qed.
End well_contained_alt.

Lemma well_contained_proper: Find_Proper_Signature (@WellContained) 0
  (∀ A (Ae:Equiv A) (b:Ball A) (X:Subset), Proper ((=)==>(=)==>impl) (WellContained (X:=X))).
Proof. red; intros. intros U1 U2 EU V1 V2 EV ?. destruct (_ : WellContained (X:=X) U1 V1).
  apply well_contained_alt.
  rewrite <- EV; apply _.
  rewrite <- EU, <- EV; apply _.
  rewrite <- EU; apply _.
  rewrite <- EU; apply _.
  rewrite <- EU, <- EV; apply _.
Qed.
Hint Extern 0 (Find_Proper_Signature (@WellContained) 0 _) => eexact well_contained_proper : typeclass_instances.

Lemma well_contained_proper2: Find_Proper_Signature (@WellContained) 1
  (∀ A (Ae:Equiv A) (b:Ball A) (X:Subset), Proper ((Inhabited,⊆)-->((⊆ X),⊆)++>impl) (WellContained (X:=X))).
Proof. red; intros. intros U1 U2 [[eu1 eu2]EU] V1 V2 [[ev1 ev2]EV] ?. red in eu1,eu2, ev1,ev2.
  destruct (_ : WellContained (X:=X) U1 V1).
  apply (well_contained_alt _ _); trivial.
  transitivity U1; trivial. transitivity V1; trivial.
  rewrite EU; apply _.
  rewrite EU, (complement_flip V1 V2); apply _.
Qed.
Hint Extern 0 (Find_Proper_Signature (@WellContained) 1 _) => eexact well_contained_proper2 : typeclass_instances.

Section well_contained.
  Context `{MetricSpace (X:=X)}.
  Hint Extern 0 AmbientSpace => eexact X : typeclass_instances.

  Lemma well_contained_stable (U V : Subset) `{V ⊆ X} `{!MetricComplementStable V}
    : Bounded (X:=X) U → Inhabited U → SetApart U (∼V) → U ⊂⊂ V.
  Proof. intros. apply (well_contained_alt U V); try apply _.
    rewrite <-(metric_complement_stable V).
    apply (set_apart_in_metric_complement _ _).
  Qed.

  Instance well_contained_trans: Transitive (⊂⊂).
  Proof. intros U V W ??. split; try apply _. transitivity V; apply _.
    rewrite (_ : ∼W ⊆ ∼V). apply _.
  Qed.

  Lemma ball_well_contained_stable (V:Subset) `{V ⊆ X} `{!MetricComplementStable V} x `{x ∊ V}
    : ∃ `{q ∊ Q₊}, B q x ⊂⊂ V.
  Proof. assert (x ∊ -∼V) by now rewrite (metric_complement_stable V).
    destruct (metric_complement_open_apart_finite (∼V) x) as [q[??]].
    exists_sub q. apply (well_contained_stable _ _); apply _.
  Qed.

  Instance point_well_contained_stable (V:Subset) `{V ⊆ X} `{!MetricComplementStable V}
    x `{x ∊ V} : B 0 x ⊂⊂ V.
  Proof. destruct (ball_well_contained_stable V x) as [q[??]].
    assert (x ∊ X) by now apply (_ : V ⊆ X).
    assert (B 0 x ⊆ B q x) as E.
      apply (B_weaken_le _ _ _). apply (lt_le _ _). firstorder.
    now rewrite (Inhabited $ E).
  Qed.

  Lemma singleton_well_contained_stable (V:Subset) `{V ⊆ X} `{!MetricComplementStable V}
    x `{x ∊ V} : subset_singleton X x ⊂⊂ V.
  Proof. assert (x ∊ X) by now apply (_ : V ⊆ X). rewrite (singleton_is_ball x). apply _. Qed.

  Lemma well_contained_closure (U V : Subset) `{!MetricComplementStable V} `{U ⊂⊂ V} : closure U ⊂⊂ V.
  Proof. apply (well_contained_stable _ _); apply _. Qed.

  Lemma well_contained_union (U V W : Subset) `{U ⊂⊂ W} `{V ⊂⊂ W} `{!Bounded (U ⊔ V)} : U ⊔ V ⊂⊂ W.
  Proof. pose proof _ : ∼W ⊆ X.
    apply (well_contained_alt _ _ _ _).
    destruct (inhabited U). exists x. apply _.
    destruct (set_apart U (∼W)) as [a [ela P1]].
    destruct (set_apart V (∼W)) as [b [elb P2]].
    ae_rat_set_min c a b Ea Eb.
    exists_sub c. intros x [?|?] v ?.
    assert (x ∊ X) by now apply (_ : U ⊆ X). rewrite (Qfull $ Ea). now apply P1.
    assert (x ∊ X) by now apply (_ : V ⊆ X). rewrite (Qfull $ Eb). now apply P2.
  Qed.

End well_contained.

Hint Extern 2 (Transitive (⊂⊂)) => eapply @well_contained_trans : typeclass_instances.
Hint Extern 4 (B 0 _ ⊂⊂ _) => eapply @point_well_contained_stable : typeclass_instances.
Hint Extern 4 ({{ _ }} ⊂⊂ _) => eapply @singleton_well_contained_stable : typeclass_instances.
Hint Extern 2 (closure _ ⊂⊂ _) => eapply @well_contained_closure : typeclass_instances.
Hint Extern 2 (_ ⊔ _ ⊂⊂ _) => eapply @well_contained_union : typeclass_instances.
