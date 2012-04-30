Require Import
  theory.subsetoids theory.common_props.
Require Import
  abstract_algebra.

Local Open Scope grp_scope. (* notation for inverse *)
Local Notation e := mon_unit.

Lemma sg_op_closed `{SemiGroup (S:=G)} : Closed (G ==> G ==> G) (&). Proof _.
Hint Extern 0 (_ & _ ∊ _) => eapply @sg_op_closed : typeclass_instances. 

Lemma sg_op_proper_fp : Find_Proper_Signature (@sg_op) 0
  (∀ A Ae Sop S `{!@SemiGroup A Ae Sop S}, Proper ((S,=)==>(S,=)==>(S,=)) (&)).
Proof. red. intros. apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@sg_op) 0 _) => eexact sg_op_proper_fp : typeclass_instances.

Instance sg_op_sm1 `{SemiGroup (S:=G)} `{g ∊ G} : SubSetoid_Morphism (g &) G G. Proof submorphism_binary_1 (&) g.
Instance sg_op_sm2 `{SemiGroup (S:=G)} `{g ∊ G} : SubSetoid_Morphism (& g) G G. Proof submorphism_binary_2 (&) g.

Ltac structure_proper :=
  red; intros; intros ?? E ?; split; try apply _; rewrite <- E; apply _.

Lemma semigroup_proper: Find_Proper_Signature (@SemiGroup) 0
  (∀ A Ae Sop, Proper ((=)==>impl) (@SemiGroup A Ae Sop)).
Proof. structure_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@SemiGroup) 0 _) => eexact semigroup_proper : typeclass_instances.

Lemma monoid_proper: Find_Proper_Signature (@Monoid) 0
  (∀ A Ae Mop Munit, Proper ((=)==>impl) (@Monoid A Ae Mop Munit)).
Proof. structure_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@Monoid) 0 _) => eexact monoid_proper : typeclass_instances.

Lemma commonoid_proper: Find_Proper_Signature (@CommutativeMonoid) 0
  (∀ A Ae Mop Munit, Proper ((=)==>impl) (@CommutativeMonoid A Ae Mop Munit)).
Proof. structure_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@CommutativeMonoid) 0 _) => eexact commonoid_proper : typeclass_instances.

Section monoid_props.
Context `{Monoid (M:=M)}.

Lemma monoid_unit_unique_l x `{x ∊ M} `{!LeftIdentity (&) x M} : x = e.
Proof. now rewrite <- (right_identity x), (left_identity e). Qed.

Lemma monoid_unit_unique_r x `{x ∊ M} `{!RightIdentity (&) x M} : x = e.
Proof. now rewrite <- (left_identity x), (right_identity e). Qed.

End monoid_props.

Lemma group_proper: Find_Proper_Signature (@Group) 0
  (∀ A Ae Gop Gunit Ginv, Proper ((=)==>impl) (@Group A Ae Gop Gunit Ginv)).
Proof. structure_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@Group) 0 _) => eexact group_proper : typeclass_instances.

Lemma abgroup_proper: Find_Proper_Signature (@AbGroup) 0
  (∀ A Ae Gop Gunit Ginv, Proper ((=)==>impl) (@AbGroup A Ae Gop Gunit Ginv)).
Proof. structure_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@AbGroup) 0 _) => eexact abgroup_proper : typeclass_instances.

Instance abgroup_is_commonoid `{AbGroup (G:=G)} : CommutativeMonoid G := {}.

Lemma inv_closed `{Group (G:=G)} : Closed (G ==> G) (⁻¹). Proof _.
Hint Extern 1 (_⁻¹ ∊ _) => eapply @inv_closed : typeclass_instances. 

Lemma inv_proper_fp : Find_Proper_Signature (@inv) 0
  (∀ A Ginv Ae Gop Gunit G `{@Group A Ae Gop Gunit Ginv G}, Proper ((G,=)==>(G,=)) (⁻¹)).
Proof. intros ?? ?????. apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@inv) 0 _) => eexact inv_proper_fp : typeclass_instances.

Section group_props.
Context `{GroupG: Group (G:=G)}.

Global Instance inverse_involutive: Involutive (⁻¹) G.
Proof.
  intros x ?.
  rewrite <-(left_identity x) at 2.
  rewrite_on G <-(left_inverse x⁻¹).
  rewrite_on G <-(associativity (x⁻¹)⁻¹ x⁻¹ x).
  rewrite_on G ->(left_inverse x).
  now rewrite (right_identity (x⁻¹)⁻¹).
Qed.

Global Instance: Injective (⁻¹) G G.
Proof.
  split; try apply _.
  intros x ? y ? E.
  rewrite_on G <-(involutive x).
  rewrite_on G <-(involutive y).
  now rewrite_on G ->E.
Qed.

Lemma inv_mon_unit : e⁻¹ = e.
Proof. rewrite <-(left_inverse e) at 2. now rewrite (right_identity e⁻¹). Qed.

Global Instance group_left_cancellation z `{z ∊ G} : LeftCancellation (&) z G.
Proof.
  intros x ? y ? E.
  rewrite <-(left_identity x).
  rewrite_on G <-(left_inverse z).
  rewrite_on G <-(associativity z⁻¹ z x).
  rewrite_on G ->E.
  rewrite_on G ->(associativity z⁻¹ z y).
  rewrite_on G ->(left_inverse z).
  now rewrite (left_identity y).
Qed.

Global Instance group_right_cancellation z `{z ∊ G} : RightCancellation (&) z G.
Proof.
  intros x ? y ? E.
  rewrite <-(right_identity x).
  rewrite_on G <-(right_inverse z).
  rewrite_on G ->(associativity x z z⁻¹).
  rewrite_on G ->E.
  rewrite_on G <-(associativity y z z⁻¹).
  rewrite_on G ->(right_inverse z).
  now rewrite (right_identity y).
Qed.

Lemma inv_sg_op_distr x `{x ∊ G} y `{y ∊ G}: (x & y)⁻¹ = y⁻¹ & x⁻¹.
Proof.
  rewrite <-(left_identity (y⁻¹ & x⁻¹)).
  rewrite_on G <-(left_inverse (x & y)).
  rewrite_on G <-(associativity (x & y)⁻¹ (x & y) (y⁻¹ & x⁻¹)).
  rewrite_on G <-(associativity x y (y⁻¹ & x⁻¹)).
  rewrite_on G ->(associativity y y⁻¹ x⁻¹).
  rewrite_on G ->(right_inverse y).
  rewrite_on G ->(left_identity x⁻¹).
  rewrite_on G ->(right_inverse x).
  now rewrite (right_identity (x & y)⁻¹).
Qed.

End group_props.

Lemma abgroup_from_commonoid `{CommutativeMonoid (A:=A) (M:=G)} `{Inv A}
  : SubSetoid_Morphism (⁻¹) G G
  → LeftInverse (&) (⁻¹) e G
  → AbGroup G.
Proof with try apply _. intros ??. split... split...
  intros x ?. rewrite (commutativity (f:=(&)) x x⁻¹). exact (left_inverse x).
Qed.

Lemma abgroup_inv_distr `{AbGroup (G:=G)} x `{x ∊ G} y `{y ∊ G}: (x & y)⁻¹ = x⁻¹ & y⁻¹.
Proof. rewrite (inv_sg_op_distr x y). apply commutativity; apply _. Qed.

Section groupmor_props.
  Context `{G:Subset A} `{H:Subset B} `{Group (A:=A) (G:=G)} `{Group (A:=B) (G:=H)} {f : A → B} `{!SemiGroup_Morphism f G H}.

  Global Instance: Monoid_Morphism f G H.
  Proof with try apply _. split...
    eapply (right_cancellation (&) (f e))...
    rewrite <-preserves_sg_op...
    rewrite_on G ->(left_identity (e:A)).
    rewrite left_identity...
    reflexivity.
  Qed.

  Lemma preserves_inverse x `{x ∊ G}: f x⁻¹ = (f x)⁻¹.
  Proof with try apply _.
    eapply (left_cancellation (&) (f x))...
    rewrite <-preserves_sg_op...
    rewrite_on G ->(right_inverse x).
    rewrite right_inverse...
    apply preserves_mon_unit.
  Qed.
End groupmor_props.

Ltac structure_mor_proper mor_a mor_b :=
  intro; intros; intros S1 S2 ES T1 T2 ET ?; mor_a; mor_b;
  split; [ now rewrite <-ES | now rewrite <-ET | rewrite <-ES, <-ET; apply _ | ..].

Lemma semigroup_morphism_proper: Find_Proper_Signature (@SemiGroup_Morphism) 0
  (∀ A Ae B Be Sop Top f, Proper ((=) ==> (=) ==> impl) (@SemiGroup_Morphism A Ae B Be Sop Top f)).
Proof. structure_mor_proper ltac:(pose proof sgmor_a) ltac:(pose proof sgmor_b).
  intros x Hx y Hy. rewrite <-ES in Hx. rewrite <-ES in Hy. apply preserves_sg_op; apply _.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SemiGroup_Morphism) 0 _) => eexact semigroup_morphism_proper : typeclass_instances.

Lemma monoid_morphism_proper: Find_Proper_Signature (@Monoid_Morphism) 0
  (∀ A Ae B Be Sunit Tunit Sop Top f,
    Proper ((=) ==> (=) ==> impl) (@Monoid_Morphism A Ae B Be Sunit Tunit Sop Top f)).
Proof. structure_mor_proper ltac:(pose proof monmor_a) ltac:(pose proof monmor_b).
  apply preserves_mon_unit.
Qed.
Hint Extern 0 (Find_Proper_Signature (@Monoid_Morphism) 0 _) => eexact monoid_morphism_proper : typeclass_instances.

Section from_another_sg.
  Context {A} {Ae:Equiv A} {S:Subset A} {Sop:SgOp A} `{!SemiGroup S}.
  Context `{SubSetoid (A:=B) (S:=T)} {Top:SgOp B} `{!SubSetoid_Binary_Morphism (&) T T T}.
  Context (f : B → A) `{!Injective f T S} (op_correct : ∀ `{x ∊ T} `{y ∊ T}, f (x & y) = f x & f y).

  Existing Instance injective_mor.
  Lemma projected_sg: SemiGroup T.
  Proof with try apply _.
    split... intros ??????. apply (injective f)...
    rewrite op_correct...
    rewrite_on S -> (op_correct y _ z _).
    rewrite op_correct...
    rewrite_on S -> (op_correct x _ y _).
    rewrite_on S -> (associativity (f x) (f y) (f z)).
    reflexivity.
  Qed.
End from_another_sg.

(*
Section from_another_com_sg.
  Context `{CommutativeSemiGroup A} `{Setoid B}
   `{Bop : SgOp B} (f : B → A) `{!Injective f} (op_correct : ∀ x y, f (x & y) = f x & f y).

  Lemma projected_com_sg: CommutativeSemiGroup B.
  Proof.
    split. now apply (projected_sg f).
    repeat intro; apply (injective f). now rewrite !op_correct, commutativity.
  Qed.
End from_another_com_sg.
*)

(*
Section from_another_monoid.
  Context `{Monoid (M:=M)}.
  Context `{SubSetoid (A:=B) (S:=N)} {Nunit: MonUnit B} `{!e ∊ N}
          {Nop:SgOp B} `{!SubSetoid_Binary_Morphism (&) N N N}.
  Context (f : B → A) `{!Injective f N M} (op_correct : ∀ x `{!x ∊ N} y `{!y ∊ N}, f (x & y) = f x & f y)
    (unit_correct : f e = e).

  Existing Instance injective_mor.

  Lemma projected_monoid: Monoid N.
  Proof with try apply _.
    split... now apply (projected_sg f).
     intros ??. apply (injective f)... rewrite op_correct, unit_correct, left_identity... reflexivity.
    intros ??. apply (injective f)... rewrite op_correct, unit_correct, right_identity... reflexivity.
  Qed.
End from_another_monoid.
*)

(*
Section from_another_com_monoid.
  Context `{CommutativeMonoid A} `{Setoid B}
   `{Bop : SgOp B} `{Bunit : MonUnit B} (f : B → A) `{!Injective f}
   (op_correct : ∀ x y, f (x & y) = f x & f y) (unit_correct : f mon_unit = mon_unit).

  Lemma projected_com_monoid: CommutativeMonoid B.
  Proof.
    split. now apply (projected_monoid f).
    repeat intro; apply (injective f). now rewrite op_correct, commutativity.
  Qed.
End from_another_com_monoid.

Section from_another_group.
  Context `{Group A} `{Setoid B}
   `{Bop : SgOp B} `{Bunit : MonUnit B} `{Bnegate : Negate B} (f : B → A) `{!Injective f}
   (op_correct : ∀ x y, f (x & y) = f x & f y) (unit_correct : f mon_unit = mon_unit)
   (negate_correct : ∀ x, f (-x) = -f x).

  Instance: Setoid_Morphism f := injective_mor f.
  Instance: Setoid_Morphism Bnegate.
  Proof. split; try apply _. intros ? ? E1. apply (injective f). rewrite 2!negate_correct. now do 2 apply sm_proper. Qed.

  Lemma projected_group: Group B.
  Proof.
    split; try apply _. now apply (projected_monoid f).
     repeat intro; apply (injective f). now rewrite op_correct, negate_correct, unit_correct, left_inverse.
    repeat intro; apply (injective f). now rewrite op_correct, negate_correct, unit_correct, right_inverse.
  Qed.
End from_another_group.

Section from_another_ab_group.
  Context `{AbGroup A} `{Setoid B}
   `{Bop : SgOp B} `{Bunit : MonUnit B} `{Bnegate : Negate B} (f : B → A) `{!Injective f}
   (op_correct : ∀ x y, f (x & y) = f x & f y) (unit_correct : f mon_unit = mon_unit)
   (negate_correct : ∀ x, f (-x) = -f x).

  Lemma projected_ab_group: AbGroup B.
  Proof.
    split; try apply _. now apply (projected_group f).
    repeat intro; apply (injective f). now rewrite op_correct, commutativity.
  Qed.
End from_another_ab_group.

*)
