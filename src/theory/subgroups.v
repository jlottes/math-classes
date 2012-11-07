Require Import abstract_algebra interfaces.orders theory.setoids.
Require Export quotient theory.groups.

Local Open Scope grp_scope. (* notation for inverse *)
Local Notation e := mon_unit.

Class Normal_SubGroup {A Aop Aunit Ainv Ae} N G :=
  { normal_subgroup_a : @Group A Aop Aunit Ainv Ae N
  ; normal_subgroup_b : Group G
  ; normal_subgroup_sub :>> N ⊆ G
  ; normality n `{n ∊ N} g `{g ∊ G} : g & n & g⁻¹ ∊ N
  }.

Notation "N ◁ G" := (Normal_SubGroup N G) (at level 70) : grp_scope.

Section substructure_tests.
  Context `{Equiv A} `{op: SgOp A}.

  Existing Instance closed_range.
  Existing Instance closed_binary.
  Existing Instance subsetoid_a.

  Lemma subsemigroup {T S} `{T ⊆ S} `{!SemiGroup S} 
    `{!Closed (T ⇀ T ⇀ T) (&)} : SemiGroup T.
  Proof. apply (projected_sg (id:T ⇀ S)). now intros. Qed.

  Lemma subcomsemigroup {T S} `{T ⊆ S} `{!CommutativeSemiGroup S} 
    `{!Closed (T ⇀ T ⇀ T) (&)} : CommutativeSemiGroup T.
  Proof. apply (projected_com_sg (id:T ⇀ S)). now intros. Qed.

  Context `{MonUnit A}.

  Lemma submonoid `{N ⊆ M} `{!Monoid M}
    `{e ∊ N} `{!Closed (N ⇀ N ⇀ N) (&)} : Monoid N.
  Proof. apply (projected_monoid (id:N ⇀ M)); now intros. Qed.

  Lemma subcommonoid `{N ⊆ M} `{!CommutativeMonoid M}
    `{e ∊ N} `{!Closed (N ⇀ N ⇀ N) (&)} : CommutativeMonoid N.
  Proof. apply (projected_com_monoid (id:N ⇀ M)); now intros. Qed.

  Context `{Inv A}.

  Lemma subgroup `{G' ⊆ G} `{!Group G}
    x `{x ∊ G'} `{!Closed (G' ⇀ G' ⇀ G') (&)} `{!Closed (G' ⇀ G') (⁻¹)} : Group G'.
  Proof. assert (e ∊ G') by (rewrite_on G <- (left_inverse (&) x); apply _).
    apply (projected_group (id:G' ⇀ G)); now intros.
  Qed.

  Lemma subgroup_alt `{G' ⊆ G} `{!Group G}
    x `{x ∊ G'} : (∀ `{a ∊ G'} `{b ∊ G'}, a & b⁻¹ ∊ G') → Group G'.
  Proof with try apply _. intro P.
    assert (e ∊ G') by (rewrite_on G <- (right_inverse (&) x); apply _).
    assert (Closed (G' ⇀ G') (⁻¹)). intros b ?. rewrite_on G <-(left_identity (&) b⁻¹)...
    assert (Closed (G' ⇀ G' ⇀ G') (&)). intros a ? b ?. rewrite_on G <-(involutive b)...
    exact (subgroup x).
  Qed.

  Lemma subabgroup `{G' ⊆ G} `{!AbGroup G}
    x `{x ∊ G'} `{!Closed (G' ⇀ G' ⇀ G') (&)} `{!Closed (G' ⇀ G') (⁻¹)} : AbGroup G'.
  Proof. assert (Commutative (&) G') by (rewrite (_:G' ⊆ G); apply _).
    pose proof subgroup x : Group G'. apply abgroup_from_group.
  Qed.

  Lemma subabgroup_alt `{G' ⊆ G} `{!AbGroup G}
    x `{x ∊ G'} : (∀ `{a ∊ G'} `{b ∊ G'}, a & b⁻¹ ∊ G') → AbGroup G'.
  Proof. assert (Commutative (&) G') by (rewrite (_:G' ⊆ G); apply _).
    intro P. pose proof subgroup_alt x P : Group G'. apply abgroup_from_group.
  Qed.

End substructure_tests.

Lemma trivial_subgroup `{Group (G:=G)} : Group {{e}}.
Proof with try apply _. apply (subgroup_alt e). intros a [? Ea] b [? Eb]. split...
  rewrite_on G -> Ea, Eb, (left_identity (&) e⁻¹). exact inv_mon_unit.
Qed.
Hint Extern 5 (Group {{e}}) => eapply @trivial_subgroup : typeclass_instances.

Lemma trivial_subgroup_abelian `{Group (G:=G)} : AbGroup {{e}}.
Proof. assert (Commutative (&) {{e}}). intros a [? Ea] b [? Eb]. now rewrite_on G -> Ea, Eb. exact abgroup_from_group. Qed.
Hint Extern 5 (AbGroup {{e}}) => eapply @trivial_subgroup_abelian : typeclass_instances.

Lemma trivial_subgroup_normal `{Group (G:=G)} : {{e}} ◁ G.
Proof. split; try apply _.
  intros n [? En] g ?. split. apply _.
  now rewrite_on G -> En, (right_identity (&) g), (right_inverse (&) g).
Qed.
Hint Extern 5 ({{e}} ◁ _) => eapply @trivial_subgroup_normal : typeclass_instances.

Lemma absubgroup_abelian `{Group (G:=G')} `{G' ⊆ G} `{!AbGroup G} : AbGroup G'.
Proof. assert (Commutative (&) G') by (rewrite (_:G' ⊆ G); apply _). exact abgroup_from_group. Qed.

Lemma absubgroup_normal `{Group (G:=G')} `{G' ⊆ G} `{!AbGroup G} : G' ◁ G.
Proof. split; try apply _. intros n ? g ?.
  rewrite_on G -> (commutativity (&) g n), <- (associativity (&) n g g⁻¹).
  now rewrite_on G -> (right_inverse (&) g), (right_identity (&) n).
Qed.

Section center.
  Context `{Group (G:=G)}.

  Definition group_center : Subset := λ x, x ∊ G ∧ ∀ `{y ∊ G}, x & y = y & x.
  Notation Z := group_center.

  Instance: Z ⊆ G.
  Proof. split; [ apply _ | | firstorder]. intros x y E [_ C]. unfold_sigs.
    split. assumption. intros z ?. rewrite_on G <-E. now apply C.
  Qed.

  Instance: e ∊ Z.
  Proof. split. apply _. intros y ?. now rewrite_on G -> (left_identity (&) y), (right_identity (&) y). Qed.

  Instance: Closed (Z ⇀ Z ⇀ Z) (&).
  Proof. intros a [? Ca] b [? Cb]. split. apply _. intros y ?.
      rewrite_on G -> (associativity (&) y a b).
      rewrite_on G <- (associativity (&) a b y).
      rewrite_on G -> (Cb y _).
      rewrite_on G -> (associativity (&) a y b).
      now rewrite_on G -> (Ca y _).
  Qed.

  Instance: Closed (Z ⇀ Z) (⁻¹).
  Proof. intros a [? Ca]. split. apply _. intros y ?.
      rewrite_on G <-(involutive y) at 1.
      rewrite_on G <-(inv_sg_op_distr y⁻¹ a).
      rewrite_on G <- (Ca y⁻¹ _).
      rewrite_on G -> (inv_sg_op_distr a y⁻¹).
      now rewrite_on G -> (involutive y).
  Qed.

  Instance group_center_subgroup : Group Z := subgroup e.

  Instance: AbGroup Z.
  Proof. assert (Commutative (&) Z). intros a [? Ca] b [? Cb]. exact (Ca b _). exact abgroup_from_group. Qed.

  Instance : Z ◁ G.
  Proof. split; try apply _. intros n ? g ?. destruct (_:n ∊ Z) as [? Cn].
    rewrite_on G <- (Cn g _), <- (associativity (&) n g g⁻¹), (right_inverse (&) g).
    now rewrite_on G -> (right_identity (&) n).
  Qed.

  Lemma abgroup_is_center : AbGroup G → Z = G.
  Proof. intro. apply (antisymmetry SubsetOf). apply _.
    intros x ?. split. apply _.
    intros y ?. exact (commutativity (&) x y).
  Qed.

End center.

Lemma image_preserves_semigroup `{SemiGroup (S:=H)} `{H ⊆ G} `{!SemiGroup G} `{SemiGroup (S:=G')}
  (f:G ⇀ G') `{!SemiGroup_Morphism G G' f} : SemiGroup f⁺¹(H).
Proof. assert (Closed (f⁺¹(H) ⇀ f⁺¹(H) ⇀ f⁺¹(H)) (&)).
  intros y1 [? [x1[? E1]]] y2 [? [x2[? E2]]]. split. apply _.
  exists_sub (x1 & x2). rewrite (G' $ preserves_sg_op _ _). now rewrite_on G' -> E1, E2.
  apply subsemigroup.
Qed.
Hint Extern 5 (SemiGroup _⁺¹(_)) => class_apply @image_preserves_semigroup : typeclass_instances.

Lemma image_preserves_comsemigroup `{CommutativeSemiGroup (S:=H)} `{H ⊆ G} `{!SemiGroup G} `{SemiGroup (S:=G')}
  (f:G ⇀ G') `{!SemiGroup_Morphism G G' f} : CommutativeSemiGroup f⁺¹(H).
Proof. assert (Commutative (&) f⁺¹(H)).
  intros fx [? [x [? Ex]]] fy [? [y [? Ey]]].
  rewrite_on G' <- Ex, <- Ey, <- (preserves_sg_op x y).
  now rewrite (G $ commutativity (&) x y), (G' $ preserves_sg_op _ _).
  split; apply _.
Qed.
Hint Extern 5 (CommutativeSemiGroup _⁺¹(_)) => class_apply @image_preserves_comsemigroup : typeclass_instances.

Lemma image_preserves_monoid `{Monoid (M:=M)} `{M ⊆ N} `{!Monoid N} `{Monoid (M:=N')}
  (f:N ⇀ N') `{!Monoid_Morphism N N' f} : Monoid f⁺¹(M).
Proof.
  assert (e ∊ f⁺¹(M)). split. apply _. exists_sub (e:N). exact preserves_mon_unit.
  apply submonoid.
Qed.
Hint Extern 5 (Monoid _⁺¹(_)) => class_apply @image_preserves_monoid : typeclass_instances.

Lemma image_preserves_commonoid `{CommutativeMonoid (M:=M)} `{M ⊆ N} `{!Monoid N} `{Monoid (M:=N')}
  (f:N ⇀ N') `{!Monoid_Morphism N N' f} : CommutativeMonoid f⁺¹(M).
Proof. apply commonoid_from_monoid. Qed.
Hint Extern 5 (CommutativeMonoid _⁺¹(_)) => class_apply @image_preserves_commonoid : typeclass_instances.

Lemma image_preserves_group `{Group (G:=H)} `{H ⊆ G} `{!Group G} `{Group (G:=G')}
 (f:G ⇀ G') `{!SemiGroup_Morphism G G' f} : Group f⁺¹(H).
Proof.
  assert (Closed (f⁺¹(H) ⇀ f⁺¹(H)) (⁻¹)).
  intros y1 [? [x1[? E1]]]. split. apply _.
  exists_sub (x1⁻¹). rewrite (G' $ preserves_inverse _). now rewrite_on G' -> E1.
  apply (subgroup e).
Qed.
Hint Extern 5 (Group _⁺¹(_)) => class_apply @image_preserves_group : typeclass_instances.

Lemma image_preserves_abgroup `{AbGroup (G:=H)} `{H ⊆ G} `{!Group G} `{Group (G:=G')}
 (f:G ⇀ G') `{!SemiGroup_Morphism G G' f} : AbGroup f⁺¹(H).
Proof abgroup_from_group.
Hint Extern 5 (AbGroup _⁺¹(_)) => class_apply @image_preserves_abgroup : typeclass_instances.


Lemma inv_image_preserves_semigroup
  `{SemiGroup (S:=G)} `{SemiGroup (S:=K)} `{K ⊆ G'} `{!SemiGroup G'}
  (f:G ⇀ G') `{!SemiGroup_Morphism G G' f} : SemiGroup f⁻¹(K).
Proof. assert (Closed (f⁻¹(K) ⇀ f⁻¹(K) ⇀ f⁻¹(K)) (&)).
  intros y1 [??] y2 [??]. split. apply _.
  rewrite (G' $ preserves_sg_op _ _). apply _.
  apply subsemigroup.
Qed.
Hint Extern 5 (SemiGroup _⁻¹(_)) => class_apply @inv_image_preserves_semigroup : typeclass_instances.

Lemma inv_image_preserves_comsemigroup
  `{CommutativeSemiGroup (S:=G)} `{SemiGroup (S:=K)} `{K ⊆ G'} `{!SemiGroup G'}
  (f:G ⇀ G') `{!SemiGroup_Morphism G G' f} : CommutativeSemiGroup f⁻¹(K).
Proof. assert (Commutative (&) f⁻¹(K)) by (rewrite (_ : f⁻¹(K) ⊆ G); apply _). split; apply _. Qed.
Hint Extern 5 (CommutativeSemiGroup _⁻¹(_)) => class_apply @inv_image_preserves_comsemigroup : typeclass_instances.

Lemma inv_image_preserves_monoid
  `{Monoid (M:=N)} `{Monoid (M:=M')} `{M' ⊆ N'} `{!Monoid N'}
  (f:N ⇀ N') `{!Monoid_Morphism N N' f} : Monoid f⁻¹(M').
Proof.
  assert (e ∊ f⁻¹(M')). split. apply _. rewrite (N' $ preserves_mon_unit). apply _.
  apply submonoid.
Qed.
Hint Extern 5 (Monoid _⁻¹(_)) => class_apply @inv_image_preserves_monoid : typeclass_instances.

Lemma inv_image_preserves_commonoid
  `{CommutativeMonoid (M:=N)} `{Monoid (M:=M')} `{M' ⊆ N'} `{!Monoid N'}
  (f:N ⇀ N') `{!Monoid_Morphism N N' f} : CommutativeMonoid f⁻¹(M').
Proof. assert (Commutative (&) f⁻¹(M')) by (rewrite (_ : f⁻¹(M') ⊆ N); apply _). apply commonoid_from_monoid. Qed.
Hint Extern 5 (CommutativeMonoid _⁻¹(_)) => class_apply @inv_image_preserves_commonoid : typeclass_instances.

Lemma inv_image_preserves_group
  `{Group (G:=G)} `{Group (G:=K)} `{K ⊆ G'} `{!Group G'}
  (f:G ⇀ G') `{!SemiGroup_Morphism G G' f} : Group f⁻¹(K).
Proof. assert (Closed (f⁻¹(K) ⇀ f⁻¹(K)) (⁻¹)).
  intros y1 [??]. split. apply _. rewrite (G' $ preserves_inverse _). apply _.
  apply (subgroup e).
Qed.
Hint Extern 5 (Group _⁻¹(_)) => class_apply @inv_image_preserves_group : typeclass_instances.

Lemma inv_image_preserves_abgroup
  `{AbGroup (G:=G)} `{Group (G:=K)} `{K ⊆ G'} `{!Group G'}
  (f:G ⇀ G') `{!SemiGroup_Morphism G G' f} : AbGroup f⁻¹(K).
Proof absubgroup_abelian.
Hint Extern 5 (AbGroup _⁻¹(_)) => class_apply @inv_image_preserves_abgroup : typeclass_instances.


Lemma inv_image_preserves_normality `{Group (G:=G)} `{Normal_SubGroup (N:=N) (G:=G')}
  (f:G ⇀ G') `{!SemiGroup_Morphism G G' f} : f⁻¹(N) ◁ G.
Proof. pose proof normal_subgroup_a. pose proof normal_subgroup_b.
  split; try apply _. intros n ? g ?.
  destruct (_: n ∊ f⁻¹(N)). split. apply _.
  rewrite 2!(G' $ preserves_sg_op _ _), (G' $ preserves_inverse _).
  exact (normality _ _).
Qed.
Hint Extern 5 (_⁻¹(_) ◁ _) => class_apply @inv_image_preserves_normality : typeclass_instances.


Definition monoid_kern {A B} `{Equiv A} `{Equiv B} `{MonUnit B} {M:@Subset A} {N:@Subset B} (f:M ⇀ N) := f⁻¹( {{e}} ).
Local Notation kern := monoid_kern.

Section kernel.
  Context `{Group (G:=G)} `{Group (G:=G')} (f:G ⇀ G') `{!SemiGroup_Morphism G G' f}.

  Hint Unfold kern : typeclass_instances.

  Instance kern_normal : kern f ◁ G := _.

  Lemma grp_mor_injective : (∀ `{x ∊ G}, f x = e → x = e) ↔ Injective G G' f.
  Proof. split.
  + intro P. split; try apply _. intros x ? y ? E.
    apply (right_cancellation (&) (y⁻¹) G _ _).
    rewrite_on G -> (right_inverse (&) y).
    apply (P _ _).
    rewrite (G' $ preserves_sg_op _ _), (G' $ preserves_inverse _).
    apply (right_cancellation (&) (f y) G' _ _).
    now rewrite_on G' -> E, (right_inverse (&) (f y)), (left_identity (&) (f y)).
  + intros ? x ? ?. apply (injective f _ _). now rewrite_on G' -> preserves_mon_unit.
  Qed.

  Lemma grp_kern_trivial_iff_injective : kern f = {{e}} ↔ Injective G G' f.
  Proof. rewrite <- grp_mor_injective. unfold kern. rewrite (inv_image_eq_singleton _ _ _). split.
  + intros [_ P] x ? ?. apply (P _ _). split. apply _. trivial.
  + intros P. split. rewrite_on G' -> preserves_mon_unit. apply _.
    intros x ? [? ?]. now apply (P _ _).
  Qed.

End kernel.

Hint Extern 5 (kern _ ◁ _) => eapply @kern_normal : typeclass_instances.
Hint Extern 5 (Group (kern _)) => eapply @normal_subgroup_a : typeclass_instances.

Lemma coset_equiv `{Group (G:=H)} `{H ⊆ G} `{!Group G} : SubEquivalence G (λ a b, a & b⁻¹ ∊ H).
Proof. split.
+ intros a ?. rewrite_on G -> (right_inverse (&) a). apply _.
+ intros a ? b ? ?. rewrite_on G <- (involutive b), <- (inv_sg_op_distr a b⁻¹). apply _.
+ intros a ? b ? c ? ??. rewrite_on G <- (right_identity (&) a), <- (left_inverse (&) b).
  rewrite_on G -> (associativity (&) a b⁻¹ b), <- (associativity (&) (a & b⁻¹) b c⁻¹). apply _.
Qed.

Lemma coset_equiv_sub `{Group (G:=H)} `{H ⊆ G} `{!Group G} : SubRelation G (=) (λ a b, a & b⁻¹ ∊ H).
Proof. intros a ? b ? E. rewrite_on G -> E, (right_inverse (&) b). apply _. Qed.
Hint Extern 5 (SubRelation _ (=) (λ a b, a & b⁻¹ ∊ _)) => eapply @coset_equiv_sub : typeclass_instances.

Definition quotient_group_equiv {A} (G N: @Subset A) `{Equiv A} `{SgOp A} `{Inv A} : Equiv (G/N)
  := λ a b, (λ a b, a & b⁻¹ ∊ N) (rep a) (rep b).

Local Existing Instance quotient_group_equiv.

Section quotient_group.

  Context `{Group (G:=G)} N `{N ◁ G}.
  Instance: Group N := normal_subgroup_a.

  Notation "(∼)" := (λ a b, a & b⁻¹ ∊ N).
  Existing Instance coset_equiv.

  Instance: Setoid (G/N) := quotient_setoid.

  Existing Instance normality.

  Instance quotient_group : Group (G/N).
  Proof with try apply _. split... split... split...
  + apply (quotient_binary_morphism (&)).
    intros a b E1 c d E2. unfold_sigs. red_sig.
      rewrite_on G -> (inv_sg_op_distr b d), <- (left_identity (&) b⁻¹), <- (left_inverse (&) a).
      rewrite <- (G $ associativity (&) a⁻¹ _ _), (G $ associativity (&) d⁻¹ _ _).
      rewrite (G $ associativity (&) (a&c) _ _), <- (G $ associativity (&) a c _).
      rewrite (G $ associativity (&) c _ _), (G $ associativity (&) a _ a⁻¹).
      apply _.
  + apply (quotient_morphism (⁻¹)).
    intros a b E1. unfold_sigs. red_sig.
      rewrite_on G -> (involutive b), <- (left_identity (&) (a⁻¹ & b)), <- (left_inverse (&) b).
      rewrite (G $ associativity (&) _ _ _), <- (G $ associativity (&) b⁻¹ _ _).
      rewrite_on G <- (involutive b) at 2 3.
      rewrite_on G <- (inv_sg_op_distr a b⁻¹).
      apply _.
  Qed.

  Instance: SemiGroup_Morphism G (G/N) (').
  Proof. split; try apply _. intros x ? y ?.
    apply (coset_equiv_sub (G:=G)); simpl; try apply _. subreflexivity.
  Qed.

  Instance: Inverse (cast G (G/N)) := rep.
  Instance: Surjective G (G/N) (').
  Proof. split.
  + exact (_ : Proper ((G/N,=)==>(G/N,=)) id).
  + apply _.
  + intros ? el. exact el.
  Qed.

End quotient_group.

Hint Extern 5 (Group (_/_)) => eapply @quotient_group : typeclass_instances.

Section abelian_quotient.
  Context `{Group (G:=H)} `{H ⊆ G} `{!AbGroup G}.

  Instance: H ◁ G := absubgroup_normal.

  Lemma ab_quotient_group : AbGroup (G/H).
  Proof abgroup_from_group.
End abelian_quotient.

Hint Extern 10 (AbGroup (_/_)) => eapply @ab_quotient_group : typeclass_instances.

Section first_iso.
  Context `{Group (G:=G)} `{Group (G:=G')} (f:G ⇀ G') `{!SemiGroup_Morphism G G' f}.

  Notation K := (kern f).
  Notation h := (Quotient_lift_arg f : (G/K) ⇀ f⁺¹(G)).
  Notation ϕ := (cast G (G/K)).
  Notation "(∼)" := (λ a b, a & b⁻¹ ∊ K).
  Existing Instance coset_equiv.

  Instance: K ◁ G := _.
  Instance: Group (G/K) := _.
  Instance: Group f⁺¹(G) := _.

  Instance: SemiGroup_Morphism (G/K) f⁺¹(G) h.
  Proof. split; try apply _.
  + apply (quotient_morphism_arg f).
    intros ?? E. unfold_sigs. red_sig. destruct E as [_ [_ E]].
    apply (right_cancellation (&) (f y)⁻¹ G' _ _).
    now rewrite_on G' -> (right_inverse (&) (f y)), <- (preserves_inverse y), <- (preserves_sg_op x y⁻¹).
  + intros x ? y ?. quotient_destr. exact (preserves_sg_op x y).
  Qed.

  Lemma first_iso : f = (id : f⁺¹(G) ⇀ G') ∘ h ∘ ϕ .
  Proof (_ : Proper ((G,=)==>(G',=)) f).

  Instance: Injective (G/K) f⁺¹(G) h.
  Proof. apply grp_mor_injective. apply _. intros x ? E.
    unfold Quotient_lift_arg in E. quotient_destr. simpl in E.
    change (x & e⁻¹ ∊ K).
    rewrite_on G -> (inv_mon_unit (G:=G)), (right_identity (&) x).
    split. apply _. split. apply _. trivial.
  Qed.

  (* Classically, the injectivity of h implies the existence of an inverse,
     but we have no way of constructing it, constructively *)

  Lemma first_iso2 `{!Inverse h} `{h ∘ (inverse h) = id} `{!Closed (f⁺¹(G) ⇀ G/K) (inverse h)}
  : Bijective (G/K) f⁺¹(G) h.
  Proof. split. apply _. split; try trivial. apply _. Qed.

End first_iso.

