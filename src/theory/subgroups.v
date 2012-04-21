Require Import abstract_algebra theory.subsetoids.
Require Export theory.groups.

Local Open Scope grp_scope. (* notation for inverse *)
Local Notation e := mon_unit.

Section subsemigroup.
Context `(S:Subset) `{SemiGroup (A:=_) (S:=S)}.

Lemma subsemigroup (T:Subset _) `{!SubSetoid T} {sub:T ⊆ S} :
  Closed (T ==> T ==> T) (&) ↔ SemiGroup T.
Proof with try apply _. split... intro. split... rewrite sub...
  split; try apply _. intros ?? E1 ?? E2. unfold_sigs. red_sig.
  rewrite_on S ->E1. now rewrite_on S ->E2.
Qed.

End subsemigroup.


Section submonoid.
  Context `(M:Subset) `{Monoid (A:=_) (M:=M)}.
  Lemma submonoid (N:Subset _) `{!SubSetoid N} {sub:N ⊆ M} :
    e ∊ N ∧ Closed (N ==> N ==> N) (&) ↔ Monoid N.
  Proof with try apply _. split. intros [??]. split... apply (subsemigroup M N)...
    rewrite sub... rewrite sub...
    intro. split; apply _.
  Qed.
End submonoid.

Section subgroup_test.

  Context `(G:Subset) `{GrpG : Group (A:=_) (G:=G)}.

  Lemma subgroup_test (H:Subset _) `{!SubSetoid H} {sub:H ⊆ G} : 
   (∃ x, x ∊ H) ∧ Closed (H ==> H ==> H) (&) ∧ Closed (H ==> H) (⁻¹) ↔ Group H.
  Proof with try apply _. split.
  + intros [[x ?] [Cop Cinv]].
    assert (e ∊ H). rewrite <-(right_inverse x)...
    split. apply (submonoid G H). split...
    split... intros ?? E. unfold_sigs. red_sig. now rewrite_on G ->E.
    rewrite sub... rewrite sub...
  + intro. split. exists e... split. intros ????... intros ??...
  Qed.

  Lemma subgroup_test_alt (H:Subset A) `{!SubSetoid H} `{!H ⊆ G} : 
   (∃ x, x ∊ H) ∧ (∀ a `{!a ∊ H} b `{!b ∊ H}, a & b⁻¹ ∊ H) ↔ Group H.
  Proof. split.
  + intros [[x ?] C]. apply (subgroup_test H). split. exists x. apply _.
    assert (e ∊ H). rewrite <-(right_inverse x). apply (C x _ x _).
    assert (Closed (H ==> H) (⁻¹)). intros b ?. rewrite <-(left_identity b⁻¹). apply (C e _ b _).
    split. intros a ? b ?. rewrite_on G <-(involutive b). apply _. assumption.
  + intro. split. exists e. apply _. intros ????. apply _.
  Qed.

End subgroup_test.

Lemma trivial_subgroup_sub `{Group (G:=G)} : {{e}} ⊆ G.
Proof. intros ? E. rewrite E. apply _. Qed.
Hint Extern 1 (@SubsetOf _ (@singleton _ _ _ (@mon_unit _ _)) _) => eapply @trivial_subgroup_sub : typeclass_instances.

Lemma trivial_subgroup `{Group (G:=G)} : Group {{e}}.
Proof. apply (subgroup_test_alt G {{e}}). split. exists e. apply _.
  intros a Ea b Eb.
  change (a & b⁻¹ = e). change (a = e) in Ea. change (b = e) in Eb.
  assert (a ∊ G) by (rewrite Ea; apply _).
  assert (b ∊ G) by (rewrite Eb; apply _).
  rewrite_on G ->Ea. rewrite_on G ->Eb.
  rewrite (right_inverse e). reflexivity.
Qed.
Hint Extern 1 (@Group _ _ _ _ _ (@singleton _ _ _ (@mon_unit _ _))) => eapply @trivial_subgroup : typeclass_instances.

Section abelian_subgroup.
  Context {A} (G H: Subset A) {sub: H ⊆ G} `{AbGroup (A:=A) (G:=G)} `{!Group H}.

  Lemma absubgroup_abelian : AbGroup H.
  Proof with try apply _. split... rewrite sub... Qed.
End abelian_subgroup. 

Definition group_center `{Group (G:=G)} : Subset _ := λ x, x ∊ G ∧ ∀ y, y ∊ G → x & y = y & x.
Arguments group_center {_ _ _ _ _} G {_} _.

Local Notation Z := group_center.

Section center.
  Context `{Group (G:=G)}.

  Instance group_center_subset: (Z G) ⊆ G.
  Proof. now intros x [??]. Qed.

  Instance: SubSetoid (Z G).
  Proof. split. apply _. intros x y E [? C]. assert (y ∊ G) by now rewrite <-E.
    split. assumption. intros z ?. rewrite_on G <-E. now apply C.
  Qed.

  Instance group_center_subgroup : AbGroup (Z G).
  Proof. split. apply (subgroup_test G (Z G) (sub:=group_center_subset)).
    split. exists e. split. apply _. intros y ?. now rewrite (left_identity y), (right_identity y).
    split. intros a [? Ca] b [? Cb]. split. apply _. intros y ?.
      rewrite   (associativity y a b).
      rewrite <-(associativity a b y).
      rewrite_on G ->(Cb y _).
      rewrite   (associativity a y b).
      now rewrite_on G ->(Ca y _).
    intros a [? Ca]. split. apply _. intros y ?.
      rewrite_on G <-(involutive y) at 1.
      rewrite      <-(inv_sg_op_distr y⁻¹ a).
      rewrite_on G <-(Ca y⁻¹ _).
      rewrite        (inv_sg_op_distr a y⁻¹).
      rewrite_on G ->(involutive y).
      reflexivity.
    intros a [? Ca] b [? Cb]. exact (Ca b _).
  Qed.

  Lemma abgroup_is_center : AbGroup G → Z G = G.
  Proof. intro. assert (G ⊆ (Z G)). intros x ?. split. apply _.
    intros y ?. exact (commutativity x y).
    apply (subset_sub_sub_eq (Z G) G).
  Qed.

End center.

Section cosets.
  Context {A} (G H: Subset A) `{H ⊆ G} `{Group (A:=A) (G:=G)} `{!Group H}.

  Definition coset_equiv_l a b := a⁻¹ & b ∊ H.
  Definition coset_equiv_r a b := a & b⁻¹ ∊ H.

  Instance coset_l_subequiv: SubEquivalence G coset_equiv_l.
  Proof. unfold coset_equiv_l. split.
  + intros ??. rewrite (left_inverse x). apply _.
  + intros ?????. assert (y⁻¹ & x = (x⁻¹ & y)⁻¹) as E.
      rewrite (inv_sg_op_distr (G:=G) x⁻¹ y).
      now rewrite_on G ->(involutive (S:=G) x).
    rewrite E. apply _.
  + intros ????????. assert (x⁻¹ & z = (x⁻¹ & y) & (y⁻¹ & z)) as E.
      rewrite (associativity (x⁻¹ & y) y⁻¹ z).
      rewrite_on G <-(associativity x⁻¹ y y⁻¹).
      rewrite_on G ->(right_inverse y).
      now rewrite_on G ->(right_identity x⁻¹).
    rewrite E. apply _.
  Qed.

  Global Instance coset_r_subequiv: SubEquivalence G coset_equiv_r.
  Proof. unfold coset_equiv_r. split.
  + intros ??. rewrite (right_inverse x). apply _.
  + intros ?????. assert (y & x⁻¹ = (x & y⁻¹)⁻¹) as E.
      rewrite (inv_sg_op_distr x y⁻¹).
      now rewrite_on G ->(involutive y).
    rewrite E. apply _.
  + intros ????????. assert (x & z⁻¹ = (x & y⁻¹) & (y & z⁻¹)) as E.
      rewrite (associativity (x & y⁻¹) y z⁻¹).
      rewrite_on G <-(associativity x y⁻¹ y).
      rewrite_on G ->(left_inverse y).
      now rewrite_on G ->(right_identity x).
    rewrite E. apply _.
  Qed.

End cosets.

Lemma coset_equiv_r_proper: Find_Proper_Signature (@coset_equiv_r) 0
  (∀ A G H `{!H ⊆ G} `{Group (A:=A) (G:=G)} `{!SubSetoid H},
   Proper ((G,=)==>(G,=)==>impl) (coset_equiv_r H)).
Proof. intro. intros. intros ?? E1 ?? E2 ?. unfold coset_equiv_r in *.
  unfold_sigs. rewrite_on G <-E1. now rewrite_on G <-E2. Qed.
Hint Extern 0 (Find_Proper_Signature (@coset_equiv_r) 0 _) => eexact coset_equiv_r_proper : typeclass_instances.


Section morphisms.
  Context {A} (G  H: Subset A) `{Group (A:=A) (G:=G )}.
  Context {B} (G' K: Subset B) `{Group (A:=B) (G:=G')}.

  Context (f:A → B) `{!Domain f G} `{!SemiGroup_Morphism f G G'}.

  Lemma image_preserves_subgroup `{H ⊆ G } `{!Group H} : Group f⁺¹(H).
  Proof with try apply _. apply (subgroup_test_alt G' f⁺¹(H) ). split.
  + exists (e:B). exists (e:A). split... apply preserves_mon_unit.
  + intros b1 [a1 [? E1]] b2 [a2 [? E2]]. exists (a1 & a2⁻¹). split...
      rewrite preserves_sg_op... rewrite_on G' ->(preserves_inverse a2).
      assert (b1 ∊ G'). rewrite <- E1. apply _.
      assert (b2 ∊ G'). rewrite <- E2. apply _.
      rewrite_on G' ->E1. now rewrite_on G' ->E2.
  Qed.

  Lemma inv_image_preserves_subgroup `{K ⊆ G'}  `{!Group K} : Group f⁻¹(K).
  Proof with try apply _. apply (subgroup_test_alt G f⁻¹(K) ). split.
  + exists (e:A). split... rewrite preserves_mon_unit...
  + intros a1 [? E1] a2 [? E2]. split...
      rewrite (preserves_sg_op a1 a2⁻¹).
      rewrite_on G' ->(preserves_inverse a2). apply _.
  Qed.

End morphisms.

Definition group_kern `{Group (G:=G)} `{Group (G:=G')} f `{!SemiGroup_Morphism f G G'}
  := f⁻¹( {{e}} ).
Local Notation kern := group_kern.

Section kernel.
  Context `{Group (G:=G)} `{Group (G:=G')} f `{!SemiGroup_Morphism f G G'}.

  Instance kern_is_group : Group (kern f).
  Proof. unfold kern. apply (inv_image_preserves_subgroup G G' {{e}}); apply _. Qed.

  Lemma kern_trivial_iff_injective : kern f = {{e}} ↔ Injective f G G'.
  Proof. split.
  + intro K. split; try apply _. intros x ? y ? E.
    assert (x & y⁻¹ ∊ kern f) as E2. split. apply _. change (f (x & y⁻¹) = e).
      rewrite (preserves_sg_op x y⁻¹).
      rewrite_on G' -> (preserves_inverse y).
      rewrite_on G' -> E.
      exact (right_inverse (f y)).
    rewrite K in E2. change (x & y⁻¹ = e) in E2.
    apply (right_cancellation (&) (y⁻¹) G x y).
    now rewrite (right_inverse y).
  + intros ? x. split. intros [? E]. change (f x = e) in E. change (x=e).
    apply (injective f x e). now rewrite preserves_mon_unit.
    intro E. change (x=e) in E. rewrite E. apply _.
  Qed.

  Lemma sg_mor_injective : (∀ `{x ∊ G}, f x = e → x = e) ↔ Injective f G G'.
  Proof. rewrite <- kern_trivial_iff_injective. unfold kern.
    rewrite (inv_image_eq_singleton f {{e}} e). split.
  + intro P. split. split. apply _. exact preserves_mon_unit. exact P.
  + tauto.
  Qed.

End kernel.

Section normal_subgroup.
  Context {A} {Ae:Equiv A} {Gop: SgOp A} {Gunit:MonUnit A} {Ginv:Inv A}.

  Class normal_subgroup (H:Subset A) (G:Subset A) :=
    { normal_subgroup_g : Group G
    ; normal_subgroup_h : Group H
    ; normal_subgroup_sub : H ⊆ G
    ; normal_subgroup_prop g `{!g ∊ G} : (g &)⁺¹(H) = (& g)⁺¹(H)
    }.
End normal_subgroup.

Notation "H ◁ G" := (normal_subgroup H G) (at level 70) : grp_scope.

Section normal_props.
  Context {A} {Ae:Equiv A} {Gop: SgOp A} {Gunit:MonUnit A} {Ginv:Inv A}.
  Lemma normal_cosets (G H:Subset A) {nsub:H ◁ G}
    a {ag:a ∊ G} b {bg:b ∊ G} : a⁻¹ & b ∊ H ↔ a & b⁻¹ ∊ H.
  Proof. destruct nsub as [??? P].
    generalize a ag b bg. clear a ag b bg.
    cut (∀ a : A, a ∊ G → ∀ b : A, b ∊ G → a⁻¹ & b ∊ H -> a & b⁻¹ ∊ H). intro P'.
  + intros a ? b ?. split. apply P'; apply _.
    rewrite_on G <-(involutive a) at 1. intro Q.
    pose proof (P' _ _ _ _ Q). now rewrite_on G <-(involutive b).
  + intros a ? b ?. intro P'. pose proof (P a _) as Pa.
    match type of Pa with ?C = _ => assert (b ∊ C) as Cb end.
      exists (a⁻¹ & b). split. exact P'.
      rewrite associativity; try apply _.
      rewrite_on G ->(right_inverse a).
      now rewrite (left_identity b).
    rewrite Pa in Cb. destruct Cb as [x [? E]].
    rewrite_on G <-E.
    rewrite_on G ->(inv_sg_op_distr x a).
    rewrite (associativity a a⁻¹ x⁻¹).
    rewrite_on G ->(right_inverse a).
    rewrite (left_identity (inv x)).
    apply _.
  Qed.

End normal_props.

Section kernel_normal.
  Context `{Group (G:=G)} `{Group (G:=G')} f `{!SemiGroup_Morphism f G G'}.

  Lemma kernel_normal : kern f ◁ G.
  Proof with try apply _. split... apply (kern_is_group f). unfold kern... intros g ?. split.
  + intros [y[[? E] E2]]. assert (x ∊ G) by (rewrite <- E2; apply _).
    change (f y = e) in E. exists (x & g⁻¹). split. split...
    - change (f (x & g⁻¹) = e). rewrite (preserves_sg_op x g⁻¹).
      rewrite_on G' ->(preserves_inverse g).
      rewrite_on G <- E2. rewrite_on G' ->(preserves_sg_op g y).
      rewrite_on G' ->E. rewrite_on G' ->(right_identity (f g)).
      rewrite_on G' ->(right_inverse (f g)). reflexivity.
    - rewrite <-associativity... rewrite_on G -> (left_inverse g). now rewrite (right_identity x).
  + intros [y[[? E] E2]]. assert (x ∊ G) by (rewrite <- E2; apply _).
    change (f y = e) in E. exists (g⁻¹ & x). split. split...
    - change (f (g⁻¹ & x) = e). rewrite (preserves_sg_op g⁻¹ x).
      rewrite_on G' ->(preserves_inverse g).
      rewrite_on G <- E2. rewrite_on G' ->(preserves_sg_op y g).
      rewrite_on G' ->E. rewrite_on G' ->(left_identity (f g)).
      rewrite_on G' ->(left_inverse (f g)). reflexivity.
    - rewrite associativity... rewrite_on G -> (right_inverse g). now rewrite (left_identity x).
  Qed.
End kernel_normal.    

Section abelian_subgroup_normal.
  Context {A} (G H: Subset A) {sub: H ⊆ G} `{AbGroup (A:=A) (G:=G)} `{!Group H}.

  Lemma absubgroup_normal : H ◁ G.
  Proof with try apply _. split... intros g ?. split;
    intros [y[??]]; exists y; rewrite commutativity; try apply _; tauto.
  Qed.
End abelian_subgroup_normal.

Definition grp_quotient_equiv `{Equiv A} {Gop: SgOp A} {Ginv: Inv A} (G H: Subset A) :=
  equiv_ext G (coset_equiv_r H).

Lemma grp_quotient_equiv_sub `{Ae:Equiv A} {Gop: SgOp A} {Ginv: Inv A} (G H: Subset A)
  : subrelation (=) (grp_quotient_equiv G H).
Proof _ : subrelation (=) (equiv_ext G (coset_equiv_r H)).
Hint Extern 0 (@subrelation _ (@equiv _ ?Ae) (@grp_quotient_equiv _ ?Ae _ _ _ _)) => eapply @grp_quotient_equiv_sub : typeclass_instances.

Lemma grp_quotient_equiv_correct {A} (G H: Subset A) `{!H ⊆ G} `{Group (A:=A) (G:=G)} `{!Group H}
  a `{!a ∊ G} b `{!b ∊ G} : (grp_quotient_equiv G H) a b ↔ a & b⁻¹ ∊ H.
Proof. setoid_rewrite (equiv_ext_correct G (coset_equiv_r H) a b). reflexivity. Qed.

Section quotient_group.
  Context {A} {Ae:Equiv A} {Gop: SgOp A} {Gunit:MonUnit A} {Ginv:Inv A}.
  Context (G H:Subset A) {nsub: H ◁ G}.

  Existing Instance normal_subgroup_g.
  Existing Instance normal_subgroup_h.
  Existing Instance normal_subgroup_sub.

  Local Notation "(∼)" := (grp_quotient_equiv G H).
  
  Local Notation ext_correct := (grp_quotient_equiv_correct G H).

  Instance: SubSetoid (Ae:=(∼)) G := _ : SubSetoid (Ae:=equiv_ext G (coset_equiv_r H)) G.

  Lemma quotient_group : Group (Ae:=(∼)) G.
  Proof with try apply _. split. split... split...
    + rewrite <- (_:subrelation (=) (∼))...
    + split... intros a b E1 c d E2. unfold_sigs. red_sig.
      setoid_rewrite (ext_correct a b) in E1.
      setoid_rewrite (ext_correct c d) in E2.
      setoid_rewrite (ext_correct (a & c) (b & d)).
      rewrite_on G ->(inv_sg_op_distr b d).
      rewrite (associativity (S:=G) (a & c) d⁻¹ b⁻¹).
      rewrite_on G <-(associativity (S:=G) a c d⁻¹).
      pose proof (_:a & (c & d⁻¹) ∊  (a &)⁺¹(H)) as P.
      rewrite (normal_subgroup_prop a) in P.
      destruct P as [x [? Ep]]. rewrite_on G <- Ep.
      rewrite <-(associativity (S:=G) x a b⁻¹). apply _.
    + rewrite <- (_:subrelation (=) (∼))...
    + rewrite <- (_:subrelation (=) (∼))...
    + split... intros a b E1. unfold_sigs. red_sig.
      setoid_rewrite (ext_correct a b) in E1.
      setoid_rewrite (ext_correct a⁻¹ b⁻¹).
      rewrite_on G ->(involutive b).
      now apply (normal_cosets G H).
    + rewrite <- (_:subrelation (=) (∼))...
    + rewrite <- (_:subrelation (=) (∼))...
  Qed.

End quotient_group.

Section abelian_quotient.
  Context {A} (G H: Subset A) {sub: H ⊆ G} `{AbGroup (A:=A) (G:=G)} `{!Group H}.

  Local Notation "(∼)" := (grp_quotient_equiv G H).

  Lemma ab_quotient_group : AbGroup (Ae:=(∼)) G.
  Proof. pose proof (absubgroup_normal G H). split. exact (quotient_group G H).
    rewrite <- (_:subrelation (=) (∼)). apply _.
  Qed.
End abelian_quotient.

Section first_iso.
  Context `{Group (G:=G)} `{Group (G:=G')} f `{!SemiGroup_Morphism f G G'}.

  Local Notation K := (kern f).

  Local Notation "(∼)" := (grp_quotient_equiv G K).

  Local Notation ext_correct := (grp_quotient_equiv_correct G K).

  Existing Instance quotient_group.
  Existing Instance kernel_normal.
  Existing Instance kern_is_group.
  Existing Instance normal_subgroup_sub.

  Instance: SemiGroup_Morphism (Ae:=(∼)) f G G'.
  Proof. split; try apply _.
  + split; try apply _. intros ?? E. unfold_sigs. red_sig.
    setoid_rewrite (ext_correct x y) in E.
    destruct E as [? E]. change ( f (x & y⁻¹) = e ) in E.
    apply (right_cancellation (&) (f y)⁻¹ G' (f x) (f y)).
    rewrite (right_inverse (f y)).
    rewrite (preserves_sg_op x y⁻¹) in E.
    now rewrite_on G' -> (preserves_inverse y) in E.
  + intros. now apply preserves_sg_op.
  Qed.

  Instance: Injective (Ae:=(∼)) f G G'.
  Proof. apply sg_mor_injective. apply _. intros x ? E.
    setoid_rewrite (ext_correct x e).
    rewrite_on G -> (inv_mon_unit (G:=G)).
    rewrite (right_identity x). now split.
  Qed.

End first_iso.
