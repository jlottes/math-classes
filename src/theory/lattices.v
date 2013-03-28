Require Import
  abstract_algebra theory.setoids theory.common_props theory.groups.

Hint Extern 20 (Closed (_ ⇀ _ ⇀ _) (⊔)) => eapply (@sg_op_closed _ join_is_sg_op) : typeclass_instances.
Hint Extern 20 (Closed (_ ⇀ _ ⇀ _) (⊓)) => eapply (@sg_op_closed _ meet_is_sg_op) : typeclass_instances.
Hint Extern 5 (_ ⊔ _ ∊ _) => eapply (@sg_op_closed _ join_is_sg_op) : typeclass_instances. 
Hint Extern 5 (_ ⊓ _ ∊ _) => eapply (@sg_op_closed _ meet_is_sg_op) : typeclass_instances. 

Lemma join_proper_fp : Find_Proper_Signature (@join) 0 (∀ A Ajoin Ae L `{!@SemiGroup A (@join_is_sg_op _ Ajoin) Ae L}, Proper ((L,=)==>(L,=)==>(L,=)) (⊔)). Proof sg_op_proper_fp.
Lemma meet_proper_fp : Find_Proper_Signature (@meet) 0 (∀ A Ameet Ae L `{!@SemiGroup A (@meet_is_sg_op _ Ameet) Ae L}, Proper ((L,=)==>(L,=)==>(L,=)) (⊓)). Proof sg_op_proper_fp.
Hint Extern 0 (Find_Proper_Signature (@join) 0 _) => eexact join_proper_fp : typeclass_instances.
Hint Extern 0 (Find_Proper_Signature (@meet) 0 _) => eexact meet_proper_fp : typeclass_instances.

Instance bounded_sl_is_sl `{BoundedSemiLattice (L:=L)} : SemiLattice L.
Proof. split. apply _. apply bounded_semilattice_idempotent. Qed.

Lemma semilattice_proper: Find_Proper_Signature (@SemiLattice) 0
  (∀ A op Ae, Proper ((=)==>impl) (@SemiLattice A op Ae)).
Proof. structure_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@SemiLattice) 0 _) => eexact semilattice_proper : typeclass_instances.

Lemma bounded_semilattice_proper: Find_Proper_Signature (@BoundedSemiLattice) 0
  (∀ A op unit Ae, Proper ((=)==>impl) (@BoundedSemiLattice A op unit Ae)).
Proof. structure_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@BoundedSemiLattice) 0 _) => eexact bounded_semilattice_proper : typeclass_instances.

Lemma lattice_proper: Find_Proper_Signature (@Lattice) 0
  (∀ A Ajoin Ameet Ae, Proper ((=)==>impl) (@Lattice A Ajoin Ameet Ae)).
Proof. structure_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@Lattice) 0 _) => eexact lattice_proper : typeclass_instances.

Lemma distr_lattice_proper: Find_Proper_Signature (@DistributiveLattice) 0
  (∀ A Ajoin Ameet Ae, Proper ((=)==>impl) (@DistributiveLattice A Ajoin Ameet Ae)).
Proof. structure_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@DistributiveLattice) 0 _) => eexact distr_lattice_proper : typeclass_instances.

Instance bounded_join_sl_mor_is_join_sl_mor `{H : BoundedJoinSemiLattice_Morphism (L:=L) (K:=K) (f:=f)} :
  JoinSemiLattice_Morphism L K f.
Proof. destruct H. split; apply _. Qed.

Instance bounded_meet_sl_mor_is_meet_sl_mor `{H : BoundedMeetSemiLattice_Morphism (L:=L) (K:=K) (f:=f)} :
  MeetSemiLattice_Morphism L K f.
Proof. destruct H. split; apply _. Qed.

Lemma preserves_join `{L:Subset} `{K:Subset} (f:L ⇀ K) `{JoinSemiLattice_Morphism _ _ (L:=L) (K:=K) (f:=f)}
  x `{x ∊ L} y `{y ∊ L} : f (x ⊔ y) = f x ⊔ f y.
Proof preserves_sg_op x y.

Lemma preserves_bottom `{L:Subset} `{K:Subset} (f:L ⇀ K) `{BoundedJoinSemiLattice_Morphism _ _ (L:=L) (K:=K) (f:=f)} :
  f ⊥ = ⊥.
Proof preserves_mon_unit.

Lemma preserves_meet  `{L:Subset} `{K:Subset} (f:L ⇀ K) `{MeetSemiLattice_Morphism _ _ (L:=L) (K:=K) (f:=f)}
 x `{x ∊ L} y `{y ∊ L} : f (x ⊓ y) = f x ⊓ f y.
Proof preserves_sg_op x y.

Lemma preserves_top `{L:Subset} `{K:Subset} (f:L ⇀ K) `{BoundedMeetSemiLattice_Morphism _ _ (L:=L) (K:=K) (f:=f)} :
  f ⊤ = ⊤.
Proof preserves_mon_unit.


Section bounded_join_sl_props.
  Context {A} {L:@Subset A} `{Equiv A} `{Join A} `{Bottom A} `{!BoundedJoinSemiLattice L}.

  Instance join_bottom_l: LeftIdentity (⊔) ⊥ L := _.
  Instance join_bottom_r: RightIdentity (⊔) ⊥ L := _.
End bounded_join_sl_props.
Arguments join_bottom_l {A L _ _ _ _} _ {_}.
Arguments join_bottom_r {A L _ _ _ _} _ {_}.

Section bounded_meet_sl_props.
  Context {A} {L:@Subset A} `{Equiv A} `{Meet A} `{Top A} `{!BoundedMeetSemiLattice L}.

  Instance meet_top_l: LeftIdentity (⊓) ⊤ L := _.
  Instance meet_top_r: RightIdentity (⊓) ⊤ L := _.
End bounded_meet_sl_props.
Arguments meet_top_l {A L _ _ _ _} _ {_}.
Arguments meet_top_r {A L _ _ _ _} _ {_}.


Section distributive_lattice_props.
  Context `{DistributiveLattice (L:=L)}.

  Instance join_meet_distr_r: RightDistribute (⊔) (⊓) L.
  Proof right_distr_from_left.

  Instance meet_join_distr_l: LeftDistribute (⊓) (⊔) L.
  Proof.
    intros x ? y ? z ?.
    rewrite (L $ join_meet_distr_l _ _ _).
    rewrite (L $ distribute_r _ _ _).
    rewrite (L $ idempotency (⊔) x).
    rewrite (L $ commutativity _ y x).
    rewrite (L $ meet_join_absorption _ _).
    rewrite <-(L $ meet_join_absorption x z) at 1.
    rewrite <-(L $ associativity _ _ _ _).
    now rewrite <-(L $ distribute_r _ _ _).
  Qed.

  Lemma meet_join_distr_r: RightDistribute (⊓) (⊔) L.
  Proof right_distr_from_left.

  Lemma distribute_alt x `{x ∊ L} y `{y ∊ L} z `{z ∊ L}
    : (x ⊓ y) ⊔ (x ⊓ z) ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z) ⊓ (y ⊔ z).
  Proof.
    rewrite (L $ distribute_r x y (x ⊓ z)), (L $ join_meet_absorption _ _).
    rewrite (L $ distribute_r _ _ (y ⊓ z)).
    rewrite (L $ distribute_l x y z).
    rewrite (L $ commutativity _ y (x ⊓ z)), <-(L $ associativity _ _ y _).
    rewrite (L $ join_meet_absorption _ _).
    rewrite (L $ distribute_r x z y).
    rewrite (L $ commutativity _ z y).
    rewrite (L $ commutativity _ (x ⊔ y) (x ⊔ z)).
    rewrite (L $ associativity _ _ _ _), <-(L $ associativity _ (x ⊔ z) _ _).
    rewrite (L $ idempotency _ _).
    now rewrite (L $ commutativity _ (x ⊔ z) (x ⊔ y)).
  Qed.
End distributive_lattice_props.
Arguments join_meet_distr_r {_ _ _ _ L _} _ {_} _ {_} _ {_}.
Arguments meet_join_distr_l {_ _ _ _ L _} _ {_} _ {_} _ {_}.
Arguments meet_join_distr_r {_ _ _ _ L _} _ {_} _ {_} _ {_}.

Section lower_bounded_lattice.
  Context `{Lattice (L:=L)} `{Bottom _} `{!BoundedJoinSemiLattice L}.

  Instance meet_bottom_l: LeftAbsorb (⊓) ⊥ L.
  Proof. intros x ?. now rewrite <-(L $ join_bottom_l x), (L $ absorption _ _). Qed.
  Instance meet_bottom_r: RightAbsorb (⊓) ⊥ L.
  Proof right_absorb_from_left.
End lower_bounded_lattice.
Hint Extern 0 (LeftAbsorb (⊓) _ _) => class_apply @meet_bottom_l : typeclass_instances.
Hint Extern 0 (RightAbsorb (⊓) _ _) => class_apply @meet_bottom_r : typeclass_instances.
Arguments meet_bottom_l {_ _ _ _ L _ _ _} _ {_}.
Arguments meet_bottom_r {_ _ _ _ L _ _ _} _ {_}.

Section upper_bounded_lattice.
  Context `{Lattice (L:=L)} `{Top _} `{!BoundedMeetSemiLattice L}.

  Instance join_top_l: LeftAbsorb (⊔) ⊤ L.
  Proof. intros x ?. now rewrite <-(L $ meet_top_l x), (L $ absorption _ _). Qed.
  Instance join_top_r: RightAbsorb (⊔) ⊤ L.
  Proof right_absorb_from_left.
End upper_bounded_lattice.
Hint Extern 0 (LeftAbsorb (⊓) _ _) => class_apply @join_top_l : typeclass_instances.
Hint Extern 0 (RightAbsorb (⊓) _ _) => class_apply @join_top_r : typeclass_instances.
Arguments join_top_l {_ _ _ _ L _ _ _} _ {_}.
Arguments join_top_r {_ _ _ _ L _ _ _} _ {_}.


(*
Section from_another_sl.
  Context `{SemiLattice A} `{Setoid B}
   `{Bop : SgOp B} (f : B → A) `{!Injective f} (op_correct : ∀ x y, f (x & y) = f x & f y).

  Lemma projected_sl: SemiLattice B.
  Proof.
    split. now apply (projected_com_sg f).
    repeat intro; apply (injective f). now rewrite !op_correct, (idempotency (&) _).
  Qed.
End from_another_sl.

Section from_another_bounded_sl.
  Context `{BoundedSemiLattice A} `{Setoid B}
   `{Bop : SgOp B} `{Bunit : MonUnit B} (f : B → A) `{!Injective f}
   (op_correct : ∀ x y, f (x & y) = f x & f y) (unit_correct : f mon_unit = mon_unit).

  Lemma projected_bounded_sl: BoundedSemiLattice B.
  Proof.
    split. now apply (projected_com_monoid f).
    repeat intro; apply (injective f). now rewrite op_correct, (idempotency (&) _).
  Qed.
End from_another_bounded_sl.
*)

Local Existing Instance join_slmor_a.
Local Existing Instance join_slmor_b.
Local Existing Instance meet_slmor_a.
Local Existing Instance meet_slmor_b.
Local Existing Instance bounded_join_slmor_a.
Local Existing Instance bounded_join_slmor_b.
Local Existing Instance bounded_meet_slmor_a.
Local Existing Instance bounded_meet_slmor_b.
Local Existing Instance latticemor_a.
Local Existing Instance latticemor_b.

Lemma join_sl_morphism_alt
  `{Join A} `{SemiLattice A (op:=join_is_sg_op) (L:=L)}
  `{Join B} `{SemiLattice B (op:=join_is_sg_op) (L:=K)}
  (f:L ⇀ K) :
  Morphism (L ⇒ K) f
  → (∀ `{x ∊ L} `{y ∊ L}, f (x ⊔ y) = f x ⊔ f y)
  → JoinSemiLattice_Morphism L K f.
Proof. intros ? P. split; try apply _. split; try apply _. exact P. Qed.

Lemma meet_sl_morphism_alt
  `{Meet A} `{SemiLattice A (op:=meet_is_sg_op) (L:=L)}
  `{Meet B} `{SemiLattice B (op:=meet_is_sg_op) (L:=K)}
  (f:L ⇀ K) :
  Morphism (L ⇒ K) f
  → (∀ `{x ∊ L} `{y ∊ L}, f (x ⊓ y) = f x ⊓ f y)
  → MeetSemiLattice_Morphism L K f.
Proof. intros ? P. split; try apply _. split; try apply _. exact P. Qed.

Lemma bounded_join_sl_morphism_alt
  `{Join A} `{Bottom A} `{BoundedSemiLattice A (op:=join_is_sg_op) (unit:=bottom_is_mon_unit) (L:=L)}
  `{Join B} `{Bottom B} `{BoundedSemiLattice B (op:=join_is_sg_op) (unit:=bottom_is_mon_unit) (L:=K)}
  (f:L ⇀ K) :
  Morphism (L ⇒ K) f
  → (∀ `{x ∊ L} `{y ∊ L}, f (x ⊔ y) = f x ⊔ f y)
  → f ⊥ = ⊥
  → BoundedJoinSemiLattice_Morphism L K f.
Proof. intros ? P1 P2. split; try apply _.
  apply monoid_morphism_alt; try apply _; assumption.
Qed.

Lemma bounded_meet_sl_morphism_alt
  `{Meet A} `{Top A} `{BoundedSemiLattice A (op:=meet_is_sg_op) (unit:=top_is_mon_unit) (L:=L)}
  `{Meet B} `{Top B} `{BoundedSemiLattice B (op:=meet_is_sg_op) (unit:=top_is_mon_unit) (L:=K)}
  (f:L ⇀ K) :
  Morphism (L ⇒ K) f
  → (∀ `{x ∊ L} `{y ∊ L}, f (x ⊓ y) = f x ⊓ f y)
  → f ⊤ = ⊤
  → BoundedMeetSemiLattice_Morphism L K f.
Proof. intros ? P1 P2. split; try apply _.
  apply monoid_morphism_alt; try apply _; assumption.
Qed.


Lemma join_sl_morphism_proper: Find_Proper_Signature (@JoinSemiLattice_Morphism) 0
  (∀ A B Ajoin Bjoin Ae Be L K, Proper ((@equiv (L ⇀ K) _) ==> impl)
   (@JoinSemiLattice_Morphism A B Ajoin Bjoin Ae Be L K)).
Proof. red; intros. intros f g E ?. split; try apply _; rewrite <- E; apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@JoinSemiLattice_Morphism) 0 _) => eexact join_sl_morphism_proper : typeclass_instances.

Lemma meet_sl_morphism_proper: Find_Proper_Signature (@MeetSemiLattice_Morphism) 0
  (∀ A B Ameet Bmeet Ae Be L K, Proper ((@equiv (L ⇀ K) _) ==> impl)
   (@MeetSemiLattice_Morphism A B Ameet Bmeet Ae Be L K)).
Proof. red; intros. intros f g E ?. split; try apply _; rewrite <- E; apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@MeetSemiLattice_Morphism) 0 _) => eexact meet_sl_morphism_proper : typeclass_instances.

Lemma bounded_join_sl_morphism_proper: Find_Proper_Signature (@BoundedJoinSemiLattice_Morphism) 0
  (∀ A B Ajoin Bjoin Abottom Bbottom Ae Be L K, Proper ((@equiv (L ⇀ K) _) ==> impl)
   (@BoundedJoinSemiLattice_Morphism A B Ajoin Bjoin Abottom Bbottom Ae Be L K)).
Proof. red; intros. intros f g E ?. split; try apply _; rewrite <- E; apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@BoundedJoinSemiLattice_Morphism) 0 _) => eexact bounded_join_sl_morphism_proper : typeclass_instances.

Lemma bounded_meet_sl_morphism_proper: Find_Proper_Signature (@BoundedMeetSemiLattice_Morphism) 0
  (∀ A B Ameet Bmeet Atop Btop Ae Be L K, Proper ((@equiv (L ⇀ K) _) ==> impl)
   (@BoundedMeetSemiLattice_Morphism A B Ameet Bmeet Atop Btop Ae Be L K)).
Proof. red; intros. intros f g E ?. split; try apply _; rewrite <- E; apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@BoundedJoinSemiLattice_Morphism) 0 _) => eexact bounded_join_sl_morphism_proper : typeclass_instances.

Lemma lattice_morphism_proper: Find_Proper_Signature (@Lattice_Morphism) 0
  (∀ A B Ajoin Bjoin Ameet Bmeet Ae Be L K, Proper ((@equiv (L ⇀ K) _) ==> impl)
   (@Lattice_Morphism A B Ajoin Bjoin Ameet Bmeet Ae Be L K)).
Proof. red; intros. intros f g E ?. split; try apply _; rewrite <- E; apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@Lattice_Morphism) 0 _) => eexact lattice_morphism_proper : typeclass_instances.

Lemma join_sl_morphism_proper2: Find_Proper_Signature (@JoinSemiLattice_Morphism) 1
  (∀ A B Ajoin Bjoin Ae Be, Proper ((=) ==> (=) ==> eq ==> impl)
   (@JoinSemiLattice_Morphism A B Ajoin Bjoin Ae Be)).
Proof. structure_mor_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@JoinSemiLattice_Morphism) 1 _) => eexact join_sl_morphism_proper2 : typeclass_instances.

Lemma meet_sl_morphism_proper2: Find_Proper_Signature (@MeetSemiLattice_Morphism) 1
  (∀ A B Ameet Bmeet Ae Be, Proper ((=) ==> (=) ==> eq ==> impl)
   (@MeetSemiLattice_Morphism A B Ameet Bmeet Ae Be)).
Proof. structure_mor_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@MeetSemiLattice_Morphism) 1 _) => eexact meet_sl_morphism_proper2 : typeclass_instances.

Lemma bounded_join_sl_morphism_proper2: Find_Proper_Signature (@BoundedJoinSemiLattice_Morphism) 1
  (∀ A B Ajoin Bjoin Abottom Bbottom Ae Be, Proper ((=) ==> (=) ==> eq ==> impl)
   (@BoundedJoinSemiLattice_Morphism A B Ajoin Bjoin Abottom Bbottom Ae Be)).
Proof. structure_mor_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@BoundedJoinSemiLattice_Morphism) 1 _) => eexact bounded_join_sl_morphism_proper2 : typeclass_instances.

Lemma lattice_morphism_proper2: Find_Proper_Signature (@Lattice_Morphism) 1
  (∀ A B Ajoin Bjoin Ameet Bmeet Ae Be, Proper ((=) ==> (=) ==> eq ==> impl)
   (@Lattice_Morphism A B Ajoin Bjoin Ameet Bmeet Ae Be)).
Proof. structure_mor_proper. now rewrite <- ES, <- ET. Qed.
Hint Extern 0 (Find_Proper_Signature (@Lattice_Morphism) 1 _) => eexact lattice_morphism_proper2 : typeclass_instances.


(* The identity morphism; covers also the injection from a sub semilattice *)
Lemma id_join_sl_mor `(L:Subset) K `{!SubsetOf L K} `{Join _} `{Equiv _} `{!JoinSemiLattice L} `{!JoinSemiLattice K} : JoinSemiLattice_Morphism L K id. Proof. split; apply _. Qed.
Lemma id_meet_sl_mor `(L:Subset) K `{!SubsetOf L K} `{Meet _} `{Equiv _} `{!MeetSemiLattice L} `{!MeetSemiLattice K} : MeetSemiLattice_Morphism L K id. Proof. split; apply _. Qed.
Hint Extern 2 (JoinSemiLattice_Morphism _ _ id) => eapply @id_join_sl_mor : typeclass_instances.
Hint Extern 2 (MeetSemiLattice_Morphism _ _ id) => eapply @id_meet_sl_mor : typeclass_instances.

Lemma id_bounded_join_sl_mor `(L:Subset) K `{!SubsetOf L K} `{Join _} `{Bottom _} `{Equiv _} `{!BoundedJoinSemiLattice L} `{!BoundedJoinSemiLattice K} : BoundedJoinSemiLattice_Morphism L K id. Proof. split; apply _. Qed.
Hint Extern 2 (BoundedJoinSemiLattice_Morphism _ _ id) => eapply @id_bounded_join_sl_mor : typeclass_instances.

Lemma id_bounded_meet_sl_mor `(L:Subset) K `{!SubsetOf L K} `{Meet _} `{Top _} `{Equiv _} `{!BoundedMeetSemiLattice L} `{!BoundedMeetSemiLattice K} : BoundedMeetSemiLattice_Morphism L K id. Proof. split; apply _. Qed.
Hint Extern 2 (BoundedMeetSemiLattice_Morphism _ _ id) => eapply @id_bounded_meet_sl_mor : typeclass_instances.

Lemma id_lattice_mor `(L:Subset) K `{!SubsetOf L K} `{Join _} `{Meet _} `{Equiv _} `{!Lattice L} `{!Lattice K} : Lattice_Morphism L K id. Proof. split; apply _. Qed.
Hint Extern 2 (Lattice_Morphism _ _ id) => eapply @id_lattice_mor : typeclass_instances.

Lemma compose_join_sl_morphism
  `{Join A} `{SemiLattice A (op:=join_is_sg_op) (L:=L)}
  `{Join B} `{SemiLattice B (op:=join_is_sg_op) (L:=K)}
  `{Join C} `{SemiLattice C (op:=join_is_sg_op) (L:=M)}
  (f:L ⇀ K) (g:K ⇀ M) `{!JoinSemiLattice_Morphism L K f} `{!JoinSemiLattice_Morphism K M g}
: JoinSemiLattice_Morphism L M (g ∘ f).
Proof. split; apply _. Qed.
Hint Extern 4 (JoinSemiLattice_Morphism _ _ (_ ∘ _)) => class_apply @compose_join_sl_morphism : typeclass_instances.

Lemma compose_meet_sl_morphism
  `{Meet A} `{SemiLattice A (op:=meet_is_sg_op) (L:=L)}
  `{Meet B} `{SemiLattice B (op:=meet_is_sg_op) (L:=K)}
  `{Meet C} `{SemiLattice C (op:=meet_is_sg_op) (L:=M)}
  (f:L ⇀ K) (g:K ⇀ M) `{!MeetSemiLattice_Morphism L K f} `{!MeetSemiLattice_Morphism K M g}
: MeetSemiLattice_Morphism L M (g ∘ f).
Proof. split; apply _. Qed.
Hint Extern 4 (MeetSemiLattice_Morphism _ _ (_ ∘ _)) => class_apply @compose_meet_sl_morphism : typeclass_instances.

Lemma compose_bounded_join_sl_morphism
  `{Join A} `{Bottom A} `{BoundedSemiLattice A (op:=join_is_sg_op) (unit:=bottom_is_mon_unit) (L:=L)}
  `{Join B} `{Bottom B} `{BoundedSemiLattice B (op:=join_is_sg_op) (unit:=bottom_is_mon_unit) (L:=K)}
  `{Join C} `{Bottom C} `{BoundedSemiLattice C (op:=join_is_sg_op) (unit:=bottom_is_mon_unit) (L:=M)}
  (f:L ⇀ K) (g:K ⇀ M) `{!BoundedJoinSemiLattice_Morphism L K f} `{!BoundedJoinSemiLattice_Morphism K M g}
: BoundedJoinSemiLattice_Morphism L M (g ∘ f).
Proof. split; apply _. Qed.
Hint Extern 4 (BoundedJoinSemiLattice_Morphism _ _ (_ ∘ _)) => class_apply @compose_bounded_join_sl_morphism : typeclass_instances.

Lemma compose_bounded_meet_sl_morphism
  `{Meet A} `{Top A} `{BoundedSemiLattice A (op:=meet_is_sg_op) (unit:=top_is_mon_unit) (L:=L)}
  `{Meet B} `{Top B} `{BoundedSemiLattice B (op:=meet_is_sg_op) (unit:=top_is_mon_unit) (L:=K)}
  `{Meet C} `{Top C} `{BoundedSemiLattice C (op:=meet_is_sg_op) (unit:=top_is_mon_unit) (L:=M)}
  (f:L ⇀ K) (g:K ⇀ M) `{!BoundedMeetSemiLattice_Morphism L K f} `{!BoundedMeetSemiLattice_Morphism K M g}
: BoundedMeetSemiLattice_Morphism L M (g ∘ f).
Proof. split; apply _. Qed.
Hint Extern 4 (BoundedMeetSemiLattice_Morphism _ _ (_ ∘ _)) => class_apply @compose_bounded_meet_sl_morphism : typeclass_instances.

Lemma compose_lattice_morphism
  `{Lattice (L:=L)} `{Lattice (L:=K)} `{Lattice (L:=M)}
  (f:L ⇀ K) (g:K ⇀ M) `{!Lattice_Morphism L K f} `{!Lattice_Morphism K M g}
: Lattice_Morphism L M (g ∘ f).
Proof. split; apply _. Qed.
Hint Extern 4 (Lattice_Morphism _ _ (_ ∘ _)) => class_apply @compose_lattice_morphism : typeclass_instances.

Local Open Scope mc_fun_scope.

Lemma invert_join_sl_morphism `{L:Subset} `{K:Subset}
 (f:L ⇀ K) `{JoinSemiLattice_Morphism _ _ (L:=L) (K:=K) (f:=f)} `{!Inverse f} `{!Bijective L K f} :
  JoinSemiLattice_Morphism K L f⁻¹.
Proof. split; apply _. Qed.
Hint Extern 4 (JoinSemiLattice_Morphism _ _ (inverse _)) => eapply @invert_join_sl_morphism : typeclass_instances.

Lemma invert_meet_sl_morphism `{L:Subset} `{K:Subset}
 (f:L ⇀ K) `{MeetSemiLattice_Morphism _ _ (L:=L) (K:=K) (f:=f)} `{!Inverse f} `{!Bijective L K f} :
  MeetSemiLattice_Morphism K L f⁻¹.
Proof. split; apply _. Qed.
Hint Extern 4 (MeetSemiLattice_Morphism _ _ (inverse _)) => eapply @invert_meet_sl_morphism : typeclass_instances.

Lemma invert_bounded_join_sl_morphism `{L:Subset} `{K:Subset}
 (f:L ⇀ K) `{BoundedJoinSemiLattice_Morphism _ _ (L:=L) (K:=K) (f:=f)} `{!Inverse f} `{!Bijective L K f} :
  BoundedJoinSemiLattice_Morphism K L f⁻¹.
Proof. split; apply _. Qed.
Hint Extern 4 (BoundedJoinSemiLattice_Morphism _ _ (inverse _)) => eapply @invert_bounded_join_sl_morphism : typeclass_instances.

Lemma invert_bounded_meet_sl_morphism `{L:Subset} `{K:Subset}
 (f:L ⇀ K) `{BoundedMeetSemiLattice_Morphism _ _ (L:=L) (K:=K) (f:=f)} `{!Inverse f} `{!Bijective L K f} :
  BoundedMeetSemiLattice_Morphism K L f⁻¹.
Proof. split; apply _. Qed.
Hint Extern 4 (BoundedMeetSemiLattice_Morphism _ _ (inverse _)) => eapply @invert_bounded_meet_sl_morphism : typeclass_instances.

Lemma invert_lattice_morphism `{L:Subset} `{K:Subset}
 (f:L ⇀ K) `{Lattice_Morphism _ _ (L:=L) (K:=K) (f:=f)} `{!Inverse f} `{!Bijective L K f} :
  Lattice_Morphism K L f⁻¹.
Proof. split; apply _. Qed.
Hint Extern 4 (Lattice_Morphism _ _ (inverse _)) => eapply @invert_lattice_morphism : typeclass_instances.
