Require Import abstract_algebra substructures theory.setoids.
Require Export theory.groups.

Local Open Scope grp_scope. (* notation for inverse *)
Local Notation e := mon_unit.

Local Existing Instance subsetoid_a.
Local Existing Instance subsetoid_b.
Local Existing Instance subsemigroup_a.
Local Existing Instance subsemigroup_b.
Local Existing Instance submon_a.
Local Existing Instance submon_b.
Local Existing Instance subgroup_a.
Local Existing Instance subgroup_b.

Section substructure_tests.
  Context `{Equiv A} `{op: SgOp A}.

  Lemma subsemigroup {T S} `{!SubSetoid T S} `{!SemiGroup S} 
    `{!Closed (T ==> T ==> T) (&)} : SubSemiGroup T S.
  Proof with try apply _. split... split... rewrite (_:T ⊆ S)... split...
    intros ?? E1 ?? E2. unfold_sigs. red_sig. now rewrite_on S -> E1, E2.
  Qed.

  Context `{MonUnit A}.

  Lemma submonoid {N M} `{!SubSetoid N M} `{!Monoid M}
    `{e ∊ N} `{!Closed (N ==> N ==> N) (&)} : SubMonoid N M.
  Proof with try apply _. pose proof subsemigroup. split... split...
    rewrite (_:N ⊆ M)... rewrite (_:N ⊆ M)...
  Qed.

  Context `{Inv A}.

  Lemma subgroup {G' G} `{!SubSetoid G' G} `{!Group G}
    x `{x ∊ G'} `{!Closed (G' ==> G' ==> G') (&)} `{!Closed (G' ==> G') (⁻¹)} : SubGroup G' G.
  Proof with try apply _. assert (e ∊ G') by (rewrite_on G <- (left_inverse (&) x); apply _).
    pose proof submonoid. split... split...
    + split... intros ?? E1. unfold_sigs. red_sig. now rewrite_on G -> E1.
    + rewrite (_:G' ⊆ G)...
    + rewrite (_:G' ⊆ G)...
  Qed.

  Lemma subgroup_alt {G' G} `{!SubSetoid G' G} `{!Group G}
    x `{x ∊ G'} : (∀ `{a ∊ G'} `{b ∊ G'}, a & b⁻¹ ∊ G') → SubGroup G' G.
  Proof with try apply _. intro P.
    assert (e ∊ G') by (rewrite_on G <- (right_inverse (&) x); apply _).
    assert (Closed (G' ==> G') (⁻¹)). intros b ?. rewrite_on G <-(left_identity (&) b⁻¹)...
    assert (Closed (G' ==> G' ==> G') (&)). intros a ? b ?. rewrite_on G <-(involutive b)...
    exact (subgroup x).
  Qed.
End substructure_tests.

Lemma trivial_subgroup `{Group (G:=G)} : SubGroup {{e}} G.
Proof with try apply _. apply (subgroup_alt e). intros a [? Ea] b [? Eb]. split...
  rewrite_on G -> Ea, Eb, (left_identity (&) e⁻¹). exact inv_mon_unit.
Qed.
Hint Extern 5 (SubGroup {{e}} _) => eapply @trivial_subgroup : typeclass_instances.

Lemma trivial_subgroup_group `{Group (G:=G)} : Group {{e}}.
Proof. pose proof (_:SubGroup {{e}} G). apply _. Qed.
Hint Extern 5 (Group {{e}}) => eapply @trivial_subgroup_group : typeclass_instances.

Lemma trivial_subgroup_abelian `{Group (G:=G)} : AbGroup {{e}}.
Proof. assert (Commutative (&) {{e}}). intros a [? Ea] b [? Eb]. now rewrite_on G -> Ea, Eb. exact abgroup_from_group. Qed.
Hint Extern 5 (AbGroup {{e}}) => eapply @trivial_subgroup_abelian : typeclass_instances.

Lemma trivial_subgroup_normal `{Group (G:=G)} : {{e}} ◁ G.
Proof. split. apply _.
  intros n [? En] g ?. split. apply _.
  now rewrite_on G -> En, (right_identity (&) g), (right_inverse (&) g).
Qed.
Hint Extern 5 ({{e}} ◁ _) => eapply @trivial_subgroup_normal : typeclass_instances.

Lemma absubgroup_abelian `{SubGroup (G:=G) (H:=H)} `{!AbGroup H} : AbGroup G.
Proof. assert (Commutative (&) G) by (rewrite (_:G ⊆ H); apply _). exact abgroup_from_group. Qed.

Lemma absubgroup_normal `{SubGroup (G:=G) (H:=H)} `{!AbGroup H} : G ◁ H.
Proof. split. apply _. intros n ? g ?.
  rewrite_on H -> (commutativity (&) g n), <- (associativity (&) n g g⁻¹).
  now rewrite_on H -> (right_inverse (&) g), (right_identity (&) n).
Qed.

Definition group_center `{Group (G:=G)} : Subset _ := λ x, x ∊ G ∧ ∀ `{y ∊ G}, x & y = y & x.
Arguments group_center {_ _ _ _ _} G {_} _.

Local Notation Z := group_center.

Section center.
  Context `{Group (G:=G)}.

  Instance: SubSetoid (Z G) G.
  Proof. split. apply _. split. firstorder. intros x y E [_ C]. unfold_sigs.
    split. assumption. intros z ?. rewrite_on G <-E. now apply C.
  Qed.

  Instance: e ∊ Z G.
  Proof. split. apply _. intros y ?. now rewrite_on G -> (left_identity (&) y), (right_identity (&) y). Qed.

  Instance: Closed (Z G ==> Z G ==> Z G) (&).
  Proof. intros a [? Ca] b [? Cb]. split. apply _. intros y ?.
      rewrite_on G -> (associativity (&) y a b).
      rewrite_on G <- (associativity (&) a b y).
      rewrite_on G -> (Cb y _).
      rewrite_on G -> (associativity (&) a y b).
      now rewrite_on G -> (Ca y _).
  Qed.

  Instance: Closed (Z G ==> Z G) (⁻¹).
  Proof. intros a [? Ca]. split. apply _. intros y ?.
      rewrite_on G <-(involutive y) at 1.
      rewrite_on G <-(inv_sg_op_distr y⁻¹ a).
      rewrite_on G <- (Ca y⁻¹ _).
      rewrite_on G -> (inv_sg_op_distr a y⁻¹).
      now rewrite_on G -> (involutive y).
  Qed.

  Instance group_center_subgroup : SubGroup (Z G) G.
  Proof subgroup e.

  Instance: AbGroup (Z G).
  Proof. assert (Commutative (&) (Z G)). intros a [? Ca] b [? Cb]. exact (Ca b _). exact abgroup_from_group. Qed.

  Instance : Z G ◁ G.
  Proof. split. apply _. intros n ? g ?. destruct (_:n ∊ Z G) as [? Cn].
    rewrite_on G <- (Cn g _), <- (associativity (&) n g g⁻¹), (right_inverse (&) g).
    now rewrite_on G -> (right_identity (&) n).
  Qed.

  Lemma abgroup_is_center : AbGroup G → Z G = G.
  Proof. intro. assert (G ⊆ (Z G)). intros x ?. split. apply _.
    intros y ?. exact (commutativity (&) x y).
    apply (subset_sub_sub_eq (Z G) G).
  Qed.

End center.

Section image.
  Context `{SubGroup A (G:=H) (H:=G)} `{Group (G:=G')}.
  Context (f:G ⇀ G') `{!SemiGroup_Morphism G G' f}.

  Instance: e ∊ f⁺¹(H).
  Proof. split. apply _. exists_sub (e:A). exact preserves_mon_unit. Qed.

  Lemma image_preserves_subgroup : SubGroup f⁺¹(H) G'.
  Proof. apply (subgroup_alt e).
    intros b1 [? [a1 [? E1]]] b2 [? [a2 [? E2]]]. split. apply _.
    exists_sub (a1 & a2⁻¹).
    rewrite (G' $ preserves_sg_op _ _), (G' $ preserves_inverse _).
    now rewrite_on G' -> E1, E2.
  Qed.
End image.

Section inv_image.
  Context `{Group A (G:=G)} `{SubGroup (G:=K) (H:=G')}.
  Context (f:G ⇀ G') `{!SemiGroup_Morphism G G' f}.

  Instance: e ∊ f⁻¹(K).
  Proof. split. apply _. rewrite_on G' -> preserves_mon_unit. apply _. Qed.

  Lemma inv_image_preserves_subgroup : SubGroup f⁻¹(K) G.
  Proof. apply (subgroup_alt e).
    intros a1 [??] a2 [??]. split. apply _.
    rewrite (G' $ preserves_sg_op _ _), (G' $ preserves_inverse _). apply _.
  Qed.
End inv_image.

Lemma inv_image_preserves_normality `{Group (G:=G)} `{Normal_SubGroup (N:=N) (G:=G')}
  (f:G ⇀ G') `{!SemiGroup_Morphism G G' f} : f⁻¹(N) ◁ G.
Proof. pose proof (inv_image_preserves_subgroup f). split. apply _. intros n ? g ?.
  destruct (_: n ∊ f⁻¹(N)). split. apply _.
  rewrite 2!(G' $ preserves_sg_op _ _), (G' $ preserves_inverse _).
  exact (normality _ _).
Qed.

Definition monoid_kern {A B} `{Equiv A} `{Equiv B} `{MonUnit B} {M:Subset A} {N:Subset B} (f:M ⇀ N) := f⁻¹( {{e}} ).
Local Notation kern := monoid_kern.

Section kernel.
  Context `{Group (G:=G)} `{Group (G:=G')} (f:G ⇀ G') `{!SemiGroup_Morphism G G' f}.

  Instance kern_normal : kern f ◁ G.
  Proof inv_image_preserves_normality (N:={{e}}) f.

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

Lemma coset_equiv `{SubGroup (G:=H) (H:=G)} : SubEquivalence G (λ a b, a & b⁻¹ ∊ H).
Proof. split.
+ intros a ?. rewrite_on G -> (right_inverse (&) a). apply _.
+ intros a ? b ? ?. rewrite_on G <- (involutive b), <- (inv_sg_op_distr a b⁻¹). apply _.
+ intros a ? b ? c ? ??. rewrite_on G <- (right_identity (&) a), <- (left_inverse (&) b).
  rewrite_on G -> (associativity (&) a b⁻¹ b), <- (associativity (&) (a & b⁻¹) b c⁻¹). apply _.
Qed.

Lemma coset_equiv_sub `{SubGroup (G:=H) (H:=G)} : SubRelation G (=) (λ a b, a & b⁻¹ ∊ H).
Proof. intros a ? b ? E. rewrite_on G -> E, (right_inverse (&) b). apply _. Qed.
Hint Extern 5 (SubRelation _ (=) (λ a b, a & b⁻¹ ∊ _)) => eapply @coset_equiv_sub : typeclass_instances.

Section quotient_group.

  Context `{Group (G:=G)} N `{N ◁ G}.

  Notation "(∼)" := (λ a b, a & b⁻¹ ∊ N).

  Instance: Setoid (Ae:=(∼)) G := coset_equiv.

  Existing Instance normality.

  Lemma quotient_group : Group (Ae:=(∼)) G.
  Proof with try apply _. split. split... split...
    + rewrite <- (_:SubRelation G (=) (∼))...
    + split... intros a b E1 c d E2. unfold_sigs. red_sig. unfold equiv in *.
      rewrite_on G -> (inv_sg_op_distr b d), <- (left_identity (&) b⁻¹), <- (left_inverse (&) a).
      rewrite <- (G $ associativity (&) a⁻¹ _ _), (G $ associativity (&) d⁻¹ _ _).
      rewrite (G $ associativity (&) (a&c) _ _), <- (G $ associativity (&) a c _).
      rewrite (G $ associativity (&) c _ _), (G $ associativity (&) a _ a⁻¹).
      apply _.
    + rewrite <- (_:SubRelation G (=) (∼))...
    + rewrite <- (_:SubRelation G (=) (∼))...
    + split... intros a b E1. unfold_sigs. red_sig. unfold equiv in *.
      rewrite_on G -> (involutive b), <- (left_identity (&) (a⁻¹ & b)), <- (left_inverse (&) b).
      rewrite (G $ associativity (&) _ _ _), <- (G $ associativity (&) b⁻¹ _ _).
      rewrite_on G <- (involutive b) at 2 3.
      rewrite_on G <- (inv_sg_op_distr a b⁻¹).
      apply _.
    + rewrite <- (_:SubRelation G (=) (∼))...
    + rewrite <- (_:SubRelation G (=) (∼))...
  Qed.

End quotient_group.

Section abelian_quotient.
  Context `{SubGroup (G:=H) (H:=G)} `{!AbGroup G}.

  Notation "(∼)" := (λ a b, a & b⁻¹ ∊ H).

  Lemma ab_quotient_group : AbGroup (Ae:=(∼)) G.
  Proof. pose proof absubgroup_normal. pose proof quotient_group H.
    assert (Commutative (&) G (Be:=(∼))). rewrite <- (_:SubRelation G (=) (∼)). apply _.
    exact abgroup_from_group.
  Qed.
End abelian_quotient.

Section first_iso.
  Context `{Group (G:=G)} `{Group (G:=G')} (f:G ⇀ G') `{!SemiGroup_Morphism G G' f}.

  Notation K := (kern f).
  Notation "(∼)" := (λ a b, a & b⁻¹ ∊ K).

  Instance: K ◁ G := kern_normal f.
  Instance: Group (Ae:=(∼)) G := quotient_group K.

  Instance: SemiGroup_Morphism (Ae:=(∼)) G G' f.
  Proof. split; try apply _.
  + split; try apply _. intros ?? E. unfold_sigs. red_sig.
    destruct E as [_ [_ E]].
    apply (right_cancellation (&) (f y)⁻¹ G' _ _).
    now rewrite_on G' -> (right_inverse (&) (f y)), <- (preserves_inverse y), <- (preserves_sg_op x y⁻¹).
  + intros. now apply preserves_sg_op.
  Qed.

  Instance: Injective (Ae:=(∼)) G G' f.
  Proof. apply grp_mor_injective. apply _. intros x ? E. unfold equiv.
    rewrite_on G -> (inv_mon_unit (G:=G)), (right_identity (&) x).
    split. apply _. split. apply _. trivial.
  Qed.

End first_iso.
