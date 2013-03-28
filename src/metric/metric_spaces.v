Require Import
  abstract_algebra interfaces.orders interfaces.rationals interfaces.metric_spaces
  theory.setoids theory.jections theory.rings theory.rationals theory.powerset
  orders.rings orders.lattices orders.minmax
  orders.affinely_extended_field stdlib_field.

Local Notation B := TheAERationals.A.
Local Notation Q := the_ae_rationals.
Local Notation "Q∞" := (aff_ext Q).
Local Notation Qfull := (aff_ext_full Q).
Add Field Q : (stdlib_field_theory Q).

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

Lemma ball_proper : Find_Proper_Signature (@ball) 0
  (∀ A (Ae:Equiv A) (b:Ball A) X `{!@MetricSpace A X Ae b}, Proper ((Qfull,=)==>(X,=)==>(X,=)==>impl) ball).
Proof. red. intros. exact msp_ball_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@ball) 0 _) => eexact ball_proper : typeclass_instances.

(* Hint Extern 2 (SubReflexive _ (ball _)) => class_apply @msp_refl : typeclass_instances. *)
(* Hint Extern 2 (SubSymmetric _ (ball _)) => class_apply @msp_sym : typeclass_instances. *)

Section contents.
  Context `{MetricSpace (X:=X)}.

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
        : ball ε x y → ∀ δ `{δ ∊ Q∞}, ε ≤ δ → ball δ x y.
  Proof. intros E δ ? E2.
    pose proof msp_nonneg _ _ _ E.
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

  Lemma ball_subsetoid ε `{ε ∊ Qfull} x `{x ∊ X} : X ⊓ ball ε x ⊆ X.
  Proof. split; try apply _. intros ?? E [? E1].
    split; [| red]; now rewrite <-E.
  Qed.

  (*
  Lemma ball_split_aux ε₁ `{ε₁ ∊ Q₊} ε₂ `{ε₂ ∊ Q₊} x `{x ∊ X} z `{z ∊ X}
  :   (∀ `{ε ∊ Q₊}, ∃ `{y ∊ X}, ball (ε₁ + ε) x y ∧ ball (ε + ε₂) y z)
    → ball (ε₁ + ε₂) x z.
  Proof. intro P. apply (ball_closed _ _ _). intros ε ?.
    mc_replace (ε₁ + ε₂ + ε) with ((ε₁ + ε/2) + (ε/2 + ε₂)) on Q by subfield Q.
    destruct (P (ε/2) _) as [y [? [E1 E2]]].
    apply (ball_triangle _ _ _ y _). exact E1. exact E2.
  Qed.

  Lemma ball_split ε₁ `{ε₁ ∊ Q∞₊} ε₂ `{ε₂ ∊ Q∞₊} x `{x ∊ X} z `{z ∊ X}
  :   (∀ `{ε ∊ Q₊}, ∃ `{y ∊ X}, ball (ε₁ + ε) x y ∧ ball (ε + ε₂) y z)
    → ball (ε₁ + ε₂) x z.
  Proof. intro P.
    destruct (ae_decompose_pos ε₁) as [E|?].
      rewrite (_ $ E), (_ $ ae_nonneg_plus_inf_l _). exact (msp_ball_inf _ _).
    destruct (ae_decompose_pos ε₂) as [E|?].
      rewrite (_ $ E), (_ $ ae_nonneg_plus_inf_r _). exact (msp_ball_inf _ _).
    now apply ball_split_aux.
  Qed.
  *)

End contents.

Hint Extern 2 (SubReflexive _ (ball _)) => class_apply @ball_refl : typeclass_instances.
Hint Extern 2 (SubSymmetric _ (ball _)) => class_apply @ball_sym : typeclass_instances.
Hint Extern 2 (?x ∊ ball _ ?x) => now red : typeclass_instances.
Hint Extern 2 (?X ⊓ ball _ _ ⊆ ?X) => eapply @ball_subsetoid : typeclass_instances.

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

Lemma dense `(S:Subset) `{Dense _ (X:=X) (S:=S)} x `{x ∊ X} ε `{ε ∊ Q∞₊} : ∃ `{s ∊ S}, ball ε x s.
Proof. pose proof (_ : x ∊ X) as el. rewrite <-dense_def in el.
  destruct el as [? P]. now apply P.
Qed.

Lemma dense_refl `(X:Subset) `{MetricSpace _ (X:=X)} : Dense X X.
Proof. split; try apply _. intro x. split. now intros [??]. intro.
  split. apply _. intros. now exists_sub x.
Qed.
Hint Extern 5 (Dense ?X ?X) => eapply @dense_refl : typeclass_instances.

Lemma dense_proper `{MetricSpace (X:=Y)} (X1:Subset) (X2:Subset) `{!X2 ⊆ Y}
  : SubsetOf X1 X2 → Dense Y X1 → Dense Y X2.
Proof. intros E1 E2. split; try apply _.
  intros y. split. now intros [??]. intro. split. apply _.
  intros ε ?. destruct (dense X1 y ε) as [x[??]].
  assert (x ∊ X2). now apply E1. now exists_sub x.
Qed.

Lemma dense_id_image `{Dense (X:=Y) (S:=X)} : Dense Y (image (X:=Y) (Y:=Y) id X).
Proof. destruct (_ : Dense Y X) as [?? _].
  apply (dense_proper X); trivial; rewrite (image_id X); trivial. reflexivity.
Qed.
Hint Extern 4 (Dense _ id⁺¹(_)) => eapply @dense_id_image : typeclass_instances.

Lemma closed_top `{MetricSpace (X:=X)} : ClosedSet X X.
Proof. split; try apply _. now destruct (_ : Dense X X). Qed.
Hint Extern 5 (ClosedSet ?X ?X) => eapply @closed_top : typeclass_instances.

Lemma open_top `{MetricSpace (X:=X)} : Open X X.
Proof. split; try apply _. intros ??. exists_sub ∞. apply _. Qed.
Hint Extern 5 (Open ?X ?X) => eapply @open_top : typeclass_instances.

Lemma open_union `{MetricSpace (X:=X)} (U V:Subset) : Open X U → Open X V → Open X (U ⊔ V).
Proof. intros ??. split; try apply _.
  apply (join_lub (L:=(⊆ X)) _ _ _); unfold le; apply _.
  intros x [?|?].
  destruct (open U x) as [q[??]]. exists_sub q.
    transitivity U; trivial. apply _.
  destruct (open V x) as [q[??]]. exists_sub q.
    transitivity V; trivial. apply _.
Qed.
Hint Extern 5 (Open _ (_ ⊔ _)) => eapply @open_union : typeclass_instances.

Local Ltac set_min δ a b Ea Eb :=
    set (δ := @meet _ (min (X:=Q∞)) a b); assert (δ ∊ Q∞₊) by (subst δ; apply _);
    assert (δ ≤ a) as Ea by (subst δ; exact (meet_lb_l (Ameet:=(min (X:=Q∞))) (L:=Q∞) _ _));
    assert (δ ≤ b) as Eb by (subst δ; exact (meet_lb_r (Ameet:=(min (X:=Q∞))) (L:=Q∞) _ _)).

Lemma open_intersection `{MetricSpace (X:=X)} (U V:Subset) : Open X U → Open X V → Open X (U ⊓ V).
Proof. intros ??. split; try apply _.
  transitivity U; try apply _. exact (meet_lb_l (L:=(⊆ X)) _ _).
  intros x [??]. pose proof _ : U ⊆ X.
  destruct (open U x) as [a[? Ba]]. destruct (open V x) as [b[? Bb]].
  set_min c a b Ea Eb. exists_sub c.
  apply (meet_glb (Ale:=SubsetOf) (L:=every Subset) U V _); unfold le; intros y [? B].
  apply (_ : SubsetOf (X ⊓ ball a x) U). split; trivial. red.
    apply (ball_weaken_le c _ _); trivial; apply _.
  apply (_ : SubsetOf (X ⊓ ball b x) V). split; trivial. red.
    apply (ball_weaken_le c _ _); trivial; apply _.
Qed.
Hint Extern 5 (Open _ (_ ⊓ _)) => eapply @open_intersection : typeclass_instances.

Lemma open_proper: Find_Proper_Signature (@Open) 0
  (∀ A (Ae:Equiv A) (Aball:Ball A) X `{!@MetricSpace A X Ae Aball},
     Proper ((=) ==> impl) (Open X)).
Proof. red; intros. intros U V E ?.
  destruct (_ : Open X U) as [?? _]. split; try apply _.
  now rewrite <-E. intros x el. rewrite <-E in el.
  destruct (open U x) as [q[??]].
  exists_sub q. now rewrite <-E.
Qed.
Hint Extern 0 (Find_Proper_Signature (@Open) 0 _) => eexact open_proper : typeclass_instances.


Lemma uniform_continuity `{X:Subset} `{Y:Subset} (f:X ⇀ Y) `{Equiv X} `{Ball X} `{Equiv Y} `{Ball Y}
  `{!UniformlyContinuous X Y f} ε `{ε ∊ Q∞₊} :  ∃ `{δ ∊ Q∞₊},
    ∀ `{x ∊ X} `{y ∊ X}, ball δ x y → ball ε (f x) (f y).
Proof. destruct (_ : UniformlyContinuous X Y f) as [?? _ _].
 destruct (ae_decompose_pos ε) as [E|?].
 + exists_sub ∞. intros. rewrite (_ $ E). exact (msp_ball_inf _ _).
 + destruct (uniform_continuity_def X Y ε) as [δ[? P]]. now exists_sub δ.
Qed.

Lemma isometric `{X:Subset} `{Y:Subset} (f:X ⇀ Y) `{Equiv X} `{Ball X} `{Equiv Y} `{Ball Y}
  `{!Isometry X Y f} ε `{ε ∊ Qfull} x `{x ∊ X} y `{y ∊ X} : ball ε x y ↔ ball ε (f x) (f y).
Proof. destruct (_ : Isometry X Y f) as [?? _ _].
  split; intro E'; pose proof (msp_nonneg _ _ _ E');
    ( destruct (ae_decompose_nonneg ε) as [E|?];
      [ rewrite (_ $ E); exact (msp_ball_inf _ _) |]);
  apply (ball_closed _ _ _); intros;
   apply (isometric_def X Y _ _ _); apply (ball_weaken_plus _ _ _); trivial; apply _.
Qed.

Lemma isometry_uniformly_continuous `{X:Subset} `{Y:Subset} (f:X ⇀ Y) `{Equiv X} `{Ball X} `{Equiv Y} `{Ball Y}
  {iso:Isometry X Y f} : UniformlyContinuous X Y f.
Proof. destruct (_ : Isometry X Y f) as [?? _ _]. split; try apply _.
  intros ε ?. exists_sub ε. intros. now rewrite <-(isometric f _ _ _).
Qed.
Hint Extern 20 (UniformlyContinuous _ _ _) => eapply @isometry_uniformly_continuous : typeclass_instances.

(* f = g → UniformlyContinuous X Y f ↔ UniformlyContinuous X Y g *)
Lemma uniformly_continuous_proper: Find_Proper_Signature (@UniformlyContinuous) 0
  (∀ A1 (Ae1:Equiv A1) (Aball1:Ball A1) X `{!@MetricSpace A1 X Ae1 Aball1}
     A2 (Ae2:Equiv A2) (Aball2:Ball A2) Y `{!@MetricSpace A2 Y Ae2 Aball2},
     Proper ((@equiv (X ⇀ Y) _) ==> impl) (UniformlyContinuous X Y)).
Proof. red; intros. intros f g E ?.
  destruct (_ : UniformlyContinuous X Y f) as [?? _ _ _].
  assert (Morphism (X ⇒ Y) g) by (rewrite <- E; apply _).
  split; try apply _.
  intros ε ?. destruct (uniform_continuity f ε) as [δ[el Cf]]. exists_sub δ.
  intros. rewrite <-(E x x), <-(E y y); try now red_sig. now apply Cf.
Qed.
Hint Extern 0 (Find_Proper_Signature (@UniformlyContinuous) 0 _) => eexact uniformly_continuous_proper : typeclass_instances.

(* f = g → Isometry X Y f ↔ Isometry X Y g *)
Lemma isometry_proper: Find_Proper_Signature (@Isometry) 0
  (∀ A1 (Ae1:Equiv A1) (Aball1:Ball A1) X `{!@MetricSpace A1 X Ae1 Aball1}
     A2 (Ae2:Equiv A2) (Aball2:Ball A2) Y `{!@MetricSpace A2 Y Ae2 Aball2},
   Proper ((@equiv (X ⇀ Y) _) ==> impl) (Isometry X Y)).
Proof. red; intros. intros f g E ?.
  destruct (_ : Isometry X Y f) as [?? _ _].
  assert (Morphism (X ⇒ Y) g) by (rewrite <- E; apply _).
  split; try apply _.
  intros. rewrite <-(E x x), <-(E y y); try now red_sig. now apply (isometric_def X Y).
Qed.
Hint Extern 0 (Find_Proper_Signature (@Isometry) 0 _) => eexact isometry_proper : typeclass_instances.


Lemma restrict_uniformly_continuous `{X:Subset} `{Y:Subset} (f:X ⇀ Y) `{Equiv X} `{Ball X} `{Equiv Y} `{Ball Y}
  `{!UniformlyContinuous X Y f} (X':Subset) `{X' ⊆ X} : UniformlyContinuous X' Y f.
Proof. 
  destruct (_ : UniformlyContinuous X Y f) as [?? _ _]. split; trivial.
  + exact sub_metric_space.
  + rewrite <-(_ : SubsetOf (X ⇒ Y) (X' ⇒ Y)). apply _.
  + intros. destruct (uniform_continuity f ε) as [δ[? P]]. exists_sub δ.
    intros. now apply (P _ _ _ _).
Qed.


Lemma closure_proper: Find_Proper_Signature (@closure) 0
  (∀ `{MetricSpace (X:=X)}, Proper ((=) ==> (=)) (closure X)).
Proof. red; intros. intros S T E ?. unfold closure.
  split; intros [? P]; (split; [apply _|]); intros ε ?;
  destruct (P ε _) as [s[el ?]]; [ rewrite E in el | rewrite <-E in el ];
  now exists_sub s.
Qed.
Hint Extern 0 (Find_Proper_Signature (@closure) 0 _) => eexact closure_proper : typeclass_instances.

Local Open Scope mc_fun_scope.

Lemma id_isometry `{MetricSpace (X:=X)} `{Y ⊆ X} : Isometry Y X (id:Y ⇀ X).
Proof. split; try apply _. exact sub_metric_space. tauto. Qed.
Hint Extern 2 (Isometry _ _ id) => eapply @id_isometry : typeclass_instances.

Lemma compose_isometry `{MetricSpace (X:=X)} `{MetricSpace (X:=Y)} `{MetricSpace (X:=Z)}
  (f:X ⇀ Y) (g:Y ⇀ Z) {iso1: Isometry X Y f} {iso2: Isometry Y Z g}
: Isometry X Z (g ∘ f).
Proof. split; try apply _. unfold compose. intros.
  transitivity (ball ε (f x) (f y)); exact (isometric _ _ _ _).
Qed.
Hint Extern 4 (Isometry _ _ (_ ∘ _)) =>  eapply @compose_isometry : typeclass_instances.

Lemma invert_isometry `{MetricSpace (X:=X)} `{MetricSpace (X:=Y)}
 (f:X ⇀ Y) `{!Isometry X Y f} `{!Inverse f} `{!Bijective X Y f} :
  Isometry Y X f⁻¹.
Proof. split; try apply _. intros.
  rewrite <-(Y $ surjective_applied f x) at 1.
  rewrite <-(Y $ surjective_applied f y) at 1.
  symmetry. exact (isometric f _ _ _).
Qed.
Hint Extern 4 (Isometry _ _ (inverse _)) => eapply @invert_isometry : typeclass_instances.

Lemma id_uniformly_cont `{MetricSpace (X:=X)} `{Y ⊆ X} : UniformlyContinuous Y X id.
Proof _.
Hint Extern 2 (UniformlyContinuous _ _ id) => eapply @id_uniformly_cont : typeclass_instances.

Lemma compose_uniformly_cont `{MetricSpace (X:=X)} `{MetricSpace (X:=Y)} `{MetricSpace (X:=Z)}
  (f:X ⇀ Y) (g:Y ⇀ Z) {cf: UniformlyContinuous X Y f} {cg: UniformlyContinuous Y Z g}
: UniformlyContinuous X Z (g ∘ f).
Proof. split; try apply _. unfold compose. intros ε ?.
  destruct (uniform_continuity g ε) as [δ₁[? P1]].
  destruct (uniform_continuity f δ₁) as [δ₂[? P2]].
  exists_sub δ₂. intros. apply (P1 _ _ _ _). now apply P2.
Qed.
Hint Extern 4 (UniformlyContinuous _ _ (_ ∘ _)) => eapply @compose_uniformly_cont : typeclass_instances.

Lemma isometry_injective `{MetricSpace (X:=X)} `{MetricSpace (X:=Y)}
 (f:X ⇀ Y) `{!Isometry X Y f} : Injective X Y f.
Proof. split; try apply _. intros x ? y ?.
  rewrite <-2!(ball_separated _ _). intro.
  now rewrite (isometric f _ _ _).
Qed.
Hint Extern 20 (Injective _ _ _) => eapply @isometry_injective : typeclass_instances.

Local Ltac mor_prem_tac :=
    repeat match goal with H : ?f ∊ ?X ⇒ ?Y |- _ => change (Morphism (X ⇒ Y) f) in H end.

Lemma uniformly_cont_subsetoid `{X:Subset} `{Y:Subset} `{Equiv X} `{Ball X} `{Equiv Y} `{Ball Y}
  `{!Setoid X} `{!Setoid Y} : (UniformlyContinuous X Y) ⊆ (X ⇒ Y).
Proof. split. apply _. intros f g E P. red in P.
  destruct (_ : UniformlyContinuous X Y f) as [?? _ _]. red. unfold_sigs. now rewrite <-E.
  now intros ? [??? _].
Qed.
Hint Extern 2 ((UniformlyContinuous _ _) ⊆ (_ ⇒ _)) => eapply @uniformly_cont_subsetoid : typeclass_instances.
Hint Extern 2 (Setoid (UniformlyContinuous ?X ?Y)) => eapply (subsetoid_a (T:=(X ⇒ Y))) : typeclass_instances.

Lemma isometry_subsetoid `{X:Subset} `{Y:Subset} `{Equiv X} `{Ball X} `{Equiv Y} `{Ball Y}
  `{!Setoid X} `{!Setoid Y} : (Isometry X Y) ⊆ (UniformlyContinuous X Y).
Proof. split. apply _. intros f g E P. red in P.
  destruct (_ : Isometry X Y f) as [?? _ _]. red. unfold_sigs. now rewrite <-E.
  intros f P. red in P. red. apply _.
Qed.

Hint Extern 2 ((Isometry _ _) ⊆ (UniformlyContinuous _ _)) => eapply @isometry_subsetoid : typeclass_instances.
Hint Extern 2 (Setoid (Isometry ?X ?Y)) => eapply (subsetoid_a (T:=(UniformlyContinuous X Y))) : typeclass_instances.

(*Hint Extern 0 (Transitive SubSetoid) => eapply @SubSetoid_trans : typeclass_instances.*)

Lemma isometry_subsetoid2 `{X:Subset} `{Y:Subset} `{Equiv X} `{Ball X} `{Equiv Y} `{Ball Y}
  `{!Setoid X} `{!Setoid Y} : (Isometry X Y) ⊆ (X ⇒ Y).
Proof. transitivity (UniformlyContinuous X Y); apply _. Qed.
Hint Extern 2 ((Isometry _ _) ⊆ (_ ⇒ _)) => eapply @isometry_subsetoid2 : typeclass_instances.

Hint Extern 0 (_ ∊ UniformlyContinuous _ _) => red : typeclass_instances.
Hint Extern 0 (_ ∊ Isometry _ _) => red : typeclass_instances.

Hint Extern 30 (@Subset (elt_type (?X ⇀ ?Y))) => eapply ((UniformlyContinuous X Y) : Subset) : typeclass_instances.


Definition sup_ball `{X:Subset} `{Y:Subset} `{Ball Y} : Ball (X ⇀ Y)
  := λ ε f g, ε ∊ Q∞⁺ ∧ ∀ `{x ∊ X}, ball ε (f x) (g x).
Hint Extern 4 (Ball (elt_type (?X ⇀ ?Y))) => eexact (sup_ball (X:=X) (Y:=Y)) : typeclass_instances.
Hint Extern 4 (Ball (elt_type (?X ⇒ ?Y))) => eexact (sup_ball (X:=X) (Y:=Y)) : typeclass_instances.
Hint Extern 8 (Ball (_ -> _)) => eapply @sup_ball : typeclass_instances.

Hint Extern 4 (Ball (elt_type (UniformlyContinuous ?X ?Y))) => eexact (sup_ball (X:=X) (Y:=Y)) : typeclass_instances.
Hint Extern 4 (Equiv (elt_type (UniformlyContinuous ?X ?Y))) => eapply (@ext_equiv _ X _ Y) : typeclass_instances.
Hint Extern 4 (Ball (elt_type (Isometry ?X ?Y))) => eexact (sup_ball (X:=X) (Y:=Y)) : typeclass_instances.
Hint Extern 4 (Equiv (elt_type (Isometry ?X ?Y))) => eapply (@ext_equiv _ X _ Y) : typeclass_instances.


Section fun_space.
  Context `{Setoid (S:=X)} `{Y:Subset} `{Ball Y} `{Equiv Y} `{!MetricSpace Y}.

  Instance fun_msp : MetricSpace (A:=X ⇀ Y) (X ⇒ Y).
  Proof. split; unfold ball, sup_ball. apply _.
  + intros a b E1 f1 f2 Ef g1 g2 Eg [? P]. unfold_sigs. mor_prem_tac.
    split. now rewrite <- (_ $ E1).
    intros x ?. rewrite <- (_ $ E1), <-(Ef x x), <-(Eg x x); try now red_sig. exact (P _ _).
  + intuition.
  + intros. split. apply _. intros. mor_prem_tac. exact (msp_ball_inf _ _).
  + intros. intros f ?. mor_prem_tac. split. apply _. now intros.
  + intros. intros f ? g ? [_ P]. mor_prem_tac. split. apply _. intros. subsymmetry. now apply P.
  + intros f ? g ? [_ P] x y [[??] E]. mor_prem_tac. red_sig. rewrite (X $ E).
    rewrite <-(ball_separated _ _). exact (P _ _).
  + intros a ? b ? f ? g ? h ? [_ P] [_ Q]. split. apply _. intros x ?. mor_prem_tac.
    apply (ball_triangle _ _ _ (g x) _). exact (P _ _). exact (Q _ _).
  + intros a ? f ? g ? P. split. apply _. intros x ?. mor_prem_tac.
    apply (ball_closed _ _ _). intros d ?. destruct (P d _) as [_ Q]. exact (Q _ _).
  Qed.

  Context `{Ball X}.

  Instance ufm_fun_msp : MetricSpace (A:=X ⇀ Y) (UniformlyContinuous X Y).
  Proof sub_metric_space (X:=(X ⇒ Y)).

  Instance iso_fun_msp : MetricSpace (A:=X ⇀ Y) (Isometry X Y).
  Proof sub_metric_space (X:=(X ⇒ Y)).

End fun_space.

Hint Extern 2 (MetricSpace (?X ⇒ ?Y)) => eapply @fun_msp : typeclass_instances.
Hint Extern 2 (MetricSpace (UniformlyContinuous ?X ?Y)) => eapply @ufm_fun_msp : typeclass_instances.
Hint Extern 2 (MetricSpace (Isometry ?X ?Y)) => eapply @iso_fun_msp : typeclass_instances.


Local Infix "==>" := UniformlyContinuous (at level 55, right associativity) : mc_scope.

Lemma lift_compose_isometry_l `{MetricSpace (X:=X)} `{MetricSpace (X:=Y)} `{MetricSpace (X:=Z)}
  (f:Y ⇀ Z) `{!Isometry Y Z f} : Isometry (X==>Y) (X==>Z) (f ∘).
Proof. split; try apply _.
+ intros g h [[u1 u2]E]. red in u1,u2. red_sig. intros ?? E2.
  unfold_sigs. red_sig. unfold compose. now rewrite (E _ _ (X $ E2)).
+ intros q ? g u1 h u2. red in u1,u2. unfold compose.
  split; (intros [_ P]; split; [apply _|]); intros.
  rewrite <-(isometric f _ _ _). now apply P.
  rewrite   (isometric f _ _ _). now apply P.
Qed.
Hint Extern 2 (Isometry _ _ (_ ∘)) => eapply @lift_compose_isometry_l : typeclass_instances.

Lemma lift_compose_isometry_r `{MetricSpace (X:=X)} `{MetricSpace (X:=Y)} `{MetricSpace (X:=Z)}
  (f:X ⇀ Y) `{!Inverse f} `{!Surjective X Y f} `{!UniformlyContinuous X Y f}
: Isometry (Y==>Z) (X==>Z) (∘ f).
Proof. split; try apply _.
+ intros g h [[u1 u2]E]. red in u1,u2. red_sig. intros ?? E2.
  unfold_sigs. red_sig. unfold compose.
  rewrite (_ $ E2). apply E. now red_sig.
+ intros q ? g u1 h u2. red in u1,u2. unfold compose.
  split; (intros [_ P]; split; [apply _|]); intros.
  exact (P _ _). rewrite <- (_ $ surjective_applied f x). exact (P _ _).
Qed.
Hint Extern 2 (Isometry _ _ (∘ _)) => eapply @lift_compose_isometry_r : typeclass_instances.
