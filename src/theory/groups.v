Require Import
  abstract_algebra theory.setoids theory.common_props theory.jections.

Local Open Scope grp_scope. (* notation for inverse *)
Local Notation e := mon_unit.

(** Operations are closed and proper *)
Lemma sg_op_closed `{SemiGroup (S:=G)} : Closed (G ⇀ G ⇀ G) (&).
Proof binary_morphism_closed (&).
Hint Extern 20 (Closed (_ ⇀ _ ⇀ _) (&)) => eapply @sg_op_closed : typeclass_instances.
Hint Extern 5 (_ & _ ∊ _) => eapply @sg_op_closed : typeclass_instances. 

Lemma sg_op_proper_fp : Find_Proper_Signature (@sg_op) 0
  (∀ A Sop Ae S `{!@SemiGroup A Sop Ae S}, Proper ((S,=)==>(S,=)==>(S,=)) (&)).
Proof. red. intros. apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@sg_op) 0 _) => eexact sg_op_proper_fp : typeclass_instances.

Lemma inv_closed `{Group (G:=G)} : Closed (G ⇀ G) (⁻¹).
Proof _.
Hint Extern 5 (_⁻¹ ∊ _) => eapply @inv_closed : typeclass_instances. 

Lemma inv_proper_fp : Find_Proper_Signature (@inv) 0
  (∀ A Ginv Ae Gop Gunit G `{@Group A Ae Gop Gunit Ginv G}, Proper ((G,=)==>(G,=)) (⁻¹)).
Proof. red. intros. exact inverse_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@inv) 0 _) => eexact inv_proper_fp : typeclass_instances.


(** Commutative structures are instances of their noncommutative counterparts *)

Instance commonoid_monoid `{cm: CommutativeMonoid (M:=M)} : Monoid M.
Proof. destruct cm. split; try apply _. exact right_id_from_left. Qed.

Lemma commonoid_from_monoid `{Monoid (M:=M)} `{!Commutative (&) M} : CommutativeMonoid M.
Proof. repeat (split; try apply _). Qed.

Instance abgroup_group `{ag: AbGroup (G:=G)} : Group G.
Proof. destruct ag. split; try apply _. exact right_inv_from_left. Qed.

Lemma abgroup_from_group `{Group (G:=G)} `{!Commutative (&) G} : AbGroup G.
Proof. repeat (split; try apply _). Qed.


(** Structure predicates are proper in their subset argument *)

Ltac structure_proper :=
  red; intros; intros ?? E P; destruct P; split; try apply _; 
  try (rewrite <- E; apply _);
  repeat match goal with H : Morphism ?S ?f |- Morphism ?T ?f => rewrite <-(_:SubsetOf S T); apply _ end.

Lemma semigroup_proper: Find_Proper_Signature (@SemiGroup) 0
  (∀ A op Ae, Proper ((=)==>impl) (@SemiGroup A op Ae)).
Proof. structure_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@SemiGroup) 0 _) => eexact semigroup_proper : typeclass_instances.

Lemma comsemigroup_proper: Find_Proper_Signature (@CommutativeSemiGroup) 0
  (∀ A op Ae, Proper ((=)==>impl) (@CommutativeSemiGroup A op Ae)).
Proof. structure_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@CommutativeSemiGroup) 0 _) => eexact comsemigroup_proper : typeclass_instances.

Lemma monoid_proper: Find_Proper_Signature (@Monoid) 0
  (∀ A op unit Ae, Proper ((=)==>impl) (@Monoid A op unit Ae)).
Proof. structure_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@Monoid) 0 _) => eexact monoid_proper : typeclass_instances.

Lemma commonoid_proper: Find_Proper_Signature (@CommutativeMonoid) 0
  (∀ A op unit Ae, Proper ((=)==>impl) (@CommutativeMonoid A op unit Ae)).
Proof. structure_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@CommutativeMonoid) 0 _) => eexact commonoid_proper : typeclass_instances.

Lemma group_proper: Find_Proper_Signature (@Group) 0
  (∀ A op unit Ainv Ae, Proper ((=)==>impl) (@Group A op unit Ainv Ae)).
Proof. structure_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@Group) 0 _) => eexact group_proper : typeclass_instances.

Lemma abgroup_proper: Find_Proper_Signature (@AbGroup) 0
  (∀ A op unit Ainv Ae, Proper ((=)==>impl) (@AbGroup A op unit Ainv Ae)).
Proof. structure_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@AbGroup) 0 _) => eexact abgroup_proper : typeclass_instances.



Section monoid_props.
  Context `{Monoid (M:=M)}.

  Lemma monoid_unit_unique_l x `{x ∊ M} `{!LeftIdentity (&) x M} : x = e.
  Proof. now rewrite_on M <- (right_identity (&) x), (left_identity (&) e). Qed.

  Lemma monoid_unit_unique_r x `{x ∊ M} `{!RightIdentity (&) x M} : x = e.
  Proof. now rewrite_on M <- (left_identity (&) x), (right_identity (&) e). Qed.
End monoid_props.


Section group_props.
Context `{Group (G:=G)}.

Global Instance inverse_involutive: Involutive (⁻¹) G.
Proof.
  intros x ?.
  rewrite_on G <-(left_identity (&) x) at 2.
  rewrite_on G <-(left_inverse (&) x⁻¹). 
  rewrite <- (G $ associativity (&) _ _ _).
  rewrite_on G ->(left_inverse (&) x).
  now rewrite -> (G $ right_identity (&) _).
Qed.

Global Instance: Injective G G (⁻¹).
Proof.
  split; try apply _.
  intros x ? y ? E.
  now rewrite_on G <-(involutive x), <-(involutive y), E.
Qed.

Lemma inv_mon_unit : e⁻¹ = e.
Proof. rewrite_on G <-(left_inverse (&) e) at 2. now rewrite_on G -> (right_identity (&) e⁻¹). Qed.

Global Instance group_left_cancellation z `{z ∊ G} : LeftCancellation (&) z G.
Proof.
  intros x ? y ? E.
  rewrite_on G <-(left_identity (&) x).
  rewrite_on G <-(left_inverse (&) z).
  rewrite <-(G $ associativity (&) _ _ _).
  rewrite_on G ->E.
  rewrite ->(G $ associativity (&) _ _ _).
  rewrite_on G ->(left_inverse (&) z).
  now rewrite_on G -> (left_identity (&) y).
Qed.

Global Instance group_right_cancellation z `{z ∊ G} : RightCancellation (&) z G.
Proof.
  intros x ? y ? E.
  rewrite_on G <-(right_identity (&) x).
  rewrite_on G <-(right_inverse (&) z).
  rewrite ->(G $ associativity (&) _ _ _).
  rewrite_on G ->E.
  rewrite <-(G $ associativity (&) _ _ _).
  rewrite_on G ->(right_inverse (&) z).
  now rewrite_on G -> (right_identity (&) y).
Qed.

Lemma inv_sg_op_distr x `{x ∊ G} y `{y ∊ G}: (x & y)⁻¹ = y⁻¹ & x⁻¹.
Proof.
  rewrite_on G <-(left_identity (&) (y⁻¹ & x⁻¹)).
  rewrite_on G <-(left_inverse (&) (x & y)).
  rewrite <- 2!(G $ associativity (&) _ _ _), ->(G $ associativity (&) y _ _).
  rewrite_on G ->(right_inverse (&) y).
  rewrite_on G ->(left_identity (&) x⁻¹).
  rewrite_on G ->(right_inverse (&) x).
  now rewrite -> (G $ right_identity (&) _).
Qed.

End group_props.

Lemma abgroup_inv_distr `{AbGroup (G:=G)} x `{x ∊ G} y `{y ∊ G}: (x & y)⁻¹ = x⁻¹ & y⁻¹.
Proof. rewrite_on G -> (inv_sg_op_distr x y). exact (commutativity (&) _ _). Qed.

(* The identity morphism; covers also the injection from a sub semigroup *)
Lemma id_semigroup_mor `(S:Subset) T `{!SubsetOf S T} `{SemiGroup _ (S:=S)} `{!SemiGroup T} : SemiGroup_Morphism S T id.
Proof. split; try apply _. now intros. Qed.
Hint Extern 2 (SemiGroup_Morphism _ _ id) => eapply @id_semigroup_mor : typeclass_instances.

Lemma id_monoid_mor `(M:Subset) N `{!SubsetOf M N} `{Monoid _ (M:=M)} `{!Monoid N} : Monoid_Morphism M N id.
Proof. split; try apply _. subreflexivity. Qed.
Hint Extern 2 (Monoid_Morphism _ _ id) => eapply @id_monoid_mor : typeclass_instances.

Lemma compose_semigroup_morphism `(S:Subset) `{SemiGroup _ (S:=S)} `{SemiGroup (S:=T)} `{SemiGroup (S:=U)}
  (f:S ⇀ T) (g:T ⇀ U) `{!SemiGroup_Morphism S T f} `{!SemiGroup_Morphism T U g}: SemiGroup_Morphism S U (g ∘ f).
Proof. split; try apply _.
  intros x ? y ?. unfold compose.
  rewrite_on T -> (preserves_sg_op x y).
  exact (preserves_sg_op _ _).
Qed.
Hint Extern 4 (SemiGroup_Morphism _ _ (_ ∘ _)) => class_apply @compose_semigroup_morphism : typeclass_instances.

Lemma compose_monoid_morphism `{Monoid (M:=M)} `{Monoid (M:=N)} `{Monoid (M:=P)}
  (f:M ⇀ N) (g:N ⇀ P) `{!Monoid_Morphism M N f} `{!Monoid_Morphism N P g}: Monoid_Morphism M P (g ∘ f).
Proof. split; try apply _.
  unfold compose. rewrite -> (N $ preserves_mon_unit).
  exact preserves_mon_unit.
Qed.
Hint Extern 4 (Monoid_Morphism _ _ (_ ∘ _)) => class_apply @compose_monoid_morphism : typeclass_instances.

Lemma invert_semigroup_morphism `{S:Subset} `{T:Subset}
 (f:S ⇀ T) `{SemiGroup_Morphism _ _ (S:=S) (T:=T) (f:=f)} `{!Inverse f} `{!Bijective S T f} :
  SemiGroup_Morphism T S (inverse f).
Proof. pose proof sgmor_a. pose proof sgmor_b. split; try apply _.
  intros x ? y ?. apply (injective f _ _).
  now rewrite (T $ preserves_sg_op _ _), 3!(T $ surjective_applied _ _).
Qed.
Hint Extern 4 (SemiGroup_Morphism _ _ (inverse _)) => eapply @invert_semigroup_morphism : typeclass_instances.

Lemma invert_monoid_morphism `{M:Subset} `{N:Subset}
 (f:M ⇀ N) `{Monoid_Morphism _ _ (M:=M) (N:=N) (f:=f)} `{!Inverse f} `{!Bijective M N f} :
  Monoid_Morphism N M (inverse f).
Proof. pose proof monmor_a. pose proof monmor_b. split; try apply _.
  apply (injective f _ _).
  now rewrite (N $ preserves_mon_unit), (N $ surjective_applied _ _).
Qed.
Hint Extern 4 (Monoid_Morphism _ _ (inverse _)) => eapply @invert_monoid_morphism : typeclass_instances.

Section groupmor_props.
  Context `{Group (G:=G1)} `{Group (G:=G2)} {f : G1 ⇀ G2} `{!SemiGroup_Morphism G1 G2 f}.

  Global Instance: Monoid_Morphism G1 G2 f.
  Proof. split; try apply _.
    apply (right_cancellation (&) (f e) _ _ _).
    now rewrite <- (G2 $ preserves_sg_op _ _), -> (G1 $ left_identity (&) _), -> (G2 $ left_identity (&) _).
  Qed.

  Lemma preserves_inverse x `{x ∊ G1}: f x⁻¹ = (f x)⁻¹.
  Proof.
    apply (left_cancellation (&) (f x) _ _ _).
    rewrite <- (G2 $ preserves_sg_op _ _).
    rewrite_on G1 -> (right_inverse (&) x).
    rewrite_on G2 -> (right_inverse (&) (f x)).
    exact preserves_mon_unit.
  Qed.
End groupmor_props.

Lemma monoid_morphism_alt `{M1:Subset} `{M2:Subset}
  (f:M1 ⇀ M2) `{Monoid _ (M:=M1)} `{Monoid _ (M:=M2)} :
  Morphism (M1 ⇒ M2) f
  → (∀ `{x ∊ M1} `{y ∊ M1}, f (x & y) = f x & f y)
  → f e = e
  → Monoid_Morphism M1 M2 f.
Proof. repeat (split; try apply _; trivial). Qed.

(* f = g → SemiGroup_Morphism S T f ↔ SemiGroup_Morphism S T g *)
Lemma semigroup_morphism_proper: Find_Proper_Signature (@SemiGroup_Morphism) 0
  (∀ A Ae B Be Sop Top S T, Proper ((@equiv (S ⇀ T) _) ==> impl) (@SemiGroup_Morphism A Ae B Be Sop Top S T)).
Proof. red; intros. intros f g E ?.
  pose proof sgmor_a. pose proof sgmor_b.
  assert (Morphism (S ⇒ T) g) by (rewrite <- E; apply _).
  split; try apply _.
  intros x ? y ?.
  rewrite <- (E (x&y) (x&y)), <- (E x x), <- (E y y); try now red_sig.
  exact (preserves_sg_op x y).
Qed.
Hint Extern 0 (Find_Proper_Signature (@SemiGroup_Morphism) 0 _) => eexact semigroup_morphism_proper : typeclass_instances.

(* f = g → Monoid_Morphism M N f ↔ Monoid_Morphism M N g *)
Lemma monoid_morphism_proper: Find_Proper_Signature (@Monoid_Morphism) 0
  (∀ A Ae B Be Sunit Tunit Sop Top S T,
   Proper ((@equiv (S ⇀ T) _) ==> impl) (@Monoid_Morphism A Ae B Be Sunit Tunit Sop Top S T)).
Proof. red; intros. intros f g E ?.
  pose proof monmor_a. pose proof monmor_b.
  assert (SemiGroup_Morphism S T g) by (rewrite <- E; apply _).
  split; try apply _.
  rewrite <- (E e e); try now red_sig.
  exact (preserves_mon_unit).
Qed.
Hint Extern 0 (Find_Proper_Signature (@Monoid_Morphism) 0 _) => eexact monoid_morphism_proper : typeclass_instances.


Ltac structure_mor_proper :=
  red; intros; intros S1 S2 ES T1 T2 ET f g Ef; destruct 1; rewrite <- Ef;
  split; [ rewrite <-ES | rewrite <-ET | try rewrite <-ES, <-ET |..]; try apply _.

Lemma semigroup_morphism_proper2: Find_Proper_Signature (@SemiGroup_Morphism) 1
  (∀ A Ae B Be Sop Top, Proper ((=) ==> (=) ==> eq ==> impl) (@SemiGroup_Morphism A Ae B Be Sop Top)).
Proof. structure_mor_proper. now rewrite <- (_:SubsetOf (S1 ⇒ T1) (S2 ⇒ T2)).
  intros x Hx y Hy. rewrite <-ES in Hx, Hy. eauto.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SemiGroup_Morphism) 1 _) => eexact semigroup_morphism_proper2 : typeclass_instances.

Lemma monoid_morphism_proper2: Find_Proper_Signature (@Monoid_Morphism) 1
  (∀ A Ae B Be Sunit Tunit Sop Top,
    Proper ((=) ==> (=) ==> eq ==> impl) (@Monoid_Morphism A Ae B Be Sunit Tunit Sop Top)).
Proof. now structure_mor_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@Monoid_Morphism) 1 _) => eexact monoid_morphism_proper2 : typeclass_instances. 

Hint Extern 0 (?S ∊ SemiGroup) => red; apply _ : typeclass_instances.
Hint Extern 0 (?S ∊ Monoid)    => red; apply _ : typeclass_instances.

Ltac structure_mor_proper3 EX EY :=
  red; intros; unfold flip; intros X X' EX Y Y' EY f ? Ef ?; rewrite <-Ef; unfold_sigs;
  repeat match goal with H : ?X ∊ ?S |- _ => change (S X) in H end;
  split; trivial.

Lemma semigroup_morphism_proper3: Find_Proper_Signature (@SemiGroup_Morphism) 2
  (∀ A Ae B Be Sop Top, Proper ((SemiGroup,⊆) --> (SemiGroup,⊆) ++> eq ==> impl) (@SemiGroup_Morphism A Ae B Be Sop Top)).
Proof. structure_mor_proper3 EX EY.
  rewrite <- (_ : SubsetOf (X ⇒ Y) (X' ⇒ Y')). apply _.
  intros ?? ??. apply preserves_sg_op; now apply EX.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SemiGroup_Morphism) 2 _) => eexact semigroup_morphism_proper3 : typeclass_instances. 

Lemma monoid_morphism_proper3: Find_Proper_Signature (@Monoid_Morphism) 2
  (∀ A Ae B Be Sunit Tunit Sop Top,
   Proper ((Monoid,⊆) --> (Monoid,⊆) ++> eq ==> impl) (@Monoid_Morphism A Ae B Be Sunit Tunit Sop Top)).
Proof. structure_mor_proper3 EX EY.
  rewrite (SemiGroup $ EX), <-(SemiGroup $ EY). apply _.
  exact preserves_mon_unit.
Qed.
Hint Extern 0 (Find_Proper_Signature (@Monoid_Morphism) 2 _) => eexact monoid_morphism_proper3 : typeclass_instances. 


Local Existing Instance closed_range.
Local Existing Instance closed_binary.
Local Existing Instance injective_mor.

Section from_another_sg.
  Context `{SemiGroup (S:=S1)} `{Setoid B (S:=S2)}
   `{Bop : SgOp B} (f : S2 ⇀ S1) `{!Injective S2 S1 f}
   `{!Closed (S2 ⇀ S2 ⇀ S2) (&)}
    (op_correct : ∀ `{x ∊ S2} `{y ∊ S2}, f (x & y) = f x & f y).

  Instance: Morphism (S2 ⇒ S2 ⇒ S2) (&).
  Proof. apply binary_morphism_proper_back. intros ?? E1 ?? E2. unfold_sigs. red_sig.
    apply (injective f _ _). now rewrite 2!(S1 $ op_correct _ _ _ _), (S2 $ E1), (S2 $ E2).
  Qed.

  Lemma projected_sg: SemiGroup S2.
  Proof.
    split; try apply _.
    repeat intro; apply (injective f _ _).
    now rewrite !(S1 $ op_correct _ _ _ _), (S1 $ associativity (&) _ _ _).
  Qed.
End from_another_sg.

Section from_another_com_sg.
  Context `{CommutativeSemiGroup (S:=S1)} `{Setoid B (S:=S2)}
   `{Bop : SgOp B} (f : S2 ⇀ S1) `{!Injective S2 S1 f}
   `{!Closed (S2 ⇀ S2 ⇀ S2) (&)}
    (op_correct : ∀ `{x ∊ S2} `{y ∊ S2}, f (x & y) = f x & f y).

  Instance: SemiGroup S2 := projected_sg f op_correct.

  Lemma projected_com_sg: CommutativeSemiGroup S2.
  Proof.
    split. apply _.
    repeat intro; apply (injective f _ _).
    now rewrite !(S1 $ op_correct _ _ _ _), (S1 $ commutativity (&) _ _).
  Qed.
End from_another_com_sg.

Section from_another_monoid.
  Context `{Monoid (M:=M1)} `{Setoid B (S:=M2)}
   `{Bop : SgOp B} `{Bunit : MonUnit B} (f : M2 ⇀ M1) `{!Injective M2 M1 f}
   `{!Closed (M2 ⇀ M2 ⇀ M2) (&)} `{e ∊ M2}
    (op_correct : ∀ `{x ∊ M2} `{y ∊ M2}, f (x & y) = f x & f y)
    (unit_correct : f e = e).

  Instance: SemiGroup M2 := projected_sg f op_correct.

  Lemma projected_monoid: Monoid M2.
  Proof.
    split. apply _. apply _.
    repeat intro; apply (injective f _ _).
      now rewrite !(M1 $ op_correct _ _ _ _), (M1 $ unit_correct), (M1 $ left_identity (&) _).
    repeat intro; apply (injective f _ _).
      now rewrite !(M1 $ op_correct _ _ _ _), (M1 $ unit_correct), (M1 $ right_identity (&) _).
  Qed.
End from_another_monoid.

Section from_another_com_monoid.
  Context `{CommutativeMonoid (M:=M1)} `{Setoid B (S:=M2)}
   `{Bop : SgOp B} `{Bunit : MonUnit B} (f : M2 ⇀ M1) `{!Injective M2 M1 f}
   `{!Closed (M2 ⇀ M2 ⇀ M2) (&)} `{e ∊ M2}
    (op_correct : ∀ `{x ∊ M2} `{y ∊ M2}, f (x & y) = f x & f y)
    (unit_correct : f e = e).

  Instance: CommutativeSemiGroup M2 := projected_com_sg f op_correct.
  Instance: Monoid M2 := projected_monoid f op_correct unit_correct.

  Instance projected_com_monoid: CommutativeMonoid M2 := {}.
End from_another_com_monoid.

Section from_another_group.
  Context `{Group (G:=G1)} `{Setoid B (S:=G2)}
   `{Bop : SgOp B} `{Bunit : MonUnit B} `{Binv : Inv B} (f : G2 ⇀ G1) `{!Injective G2 G1 f}
   `{!Closed (G2 ⇀ G2 ⇀ G2) (&)} `{e ∊ G2} `{!Closed (G2 ⇀ G2) (⁻¹)}
    (op_correct : ∀ `{x ∊ G2} `{y ∊ G2}, f (x & y) = f x & f y)
    (unit_correct : f e = e) (inv_correct : ∀ `{x ∊ G2}, f x⁻¹ = (f x)⁻¹).

  Instance: Morphism (G2 ⇒ G2) (⁻¹).
  Proof. intros ?? E1. unfold_sigs. red_sig.
    apply (injective f _ _). now rewrite 2!(G1 $ inv_correct _ _), (G2 $ E1).
  Qed.

  Instance: Monoid G2 := projected_monoid f op_correct unit_correct.

  Lemma projected_group: Group G2.
  Proof.
    split; try apply _.
    repeat intro; apply (injective f _ _). rewrite !(G1 $ op_correct _ _ _ _), 
      (G1 $ unit_correct), (G1 $ inv_correct _ _). exact (left_inverse (&) _).
    repeat intro; apply (injective f _ _). rewrite !(G1 $ op_correct _ _ _ _), 
      (G1 $ unit_correct), (G1 $ inv_correct _ _). exact (right_inverse (&) _).
  Qed.
End from_another_group.

Section from_another_ab_group.
  Context `{AbGroup (G:=G1)} `{Setoid B (S:=G2)}
   `{Bop : SgOp B} `{Bunit : MonUnit B} `{Binv : Inv B} (f : G2 ⇀ G1) `{!Injective G2 G1 f}
   `{!Closed (G2 ⇀ G2 ⇀ G2) (&)} `{e ∊ G2} `{!Closed (G2 ⇀ G2) (⁻¹)}
    (op_correct : ∀ `{x ∊ G2} `{y ∊ G2}, f (x & y) = f x & f y)
    (unit_correct : f e = e) (inv_correct : ∀ `{x ∊ G2}, f x⁻¹ = (f x)⁻¹).

  Instance: CommutativeMonoid G2 := projected_com_monoid f op_correct unit_correct.
  Instance: Group G2 := projected_group f op_correct unit_correct inv_correct.

  Instance projected_ab_group: AbGroup G2 := {}.
End from_another_ab_group.
