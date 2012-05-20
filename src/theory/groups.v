Require Import
  abstract_algebra theory.setoids theory.common_props theory.jections.

Local Open Scope grp_scope. (* notation for inverse *)
Local Notation e := mon_unit.

(* Operations are closed and proper *)
Lemma sg_op_closed `{SemiGroup (S:=G)} : Closed (G ==> G ==> G) (&).
Proof binary_morphism_closed (&).
Hint Extern 20 (Closed (_==>_==>_) (&)) => eapply @sg_op_closed : typeclass_instances.
Hint Extern 5 (_ & _ ∊ _) => eapply @sg_op_closed : typeclass_instances. 

Lemma sg_op_proper_fp : Find_Proper_Signature (@sg_op) 0
  (∀ A Ae Sop S `{!@SemiGroup A Ae Sop S}, Proper ((S,=)==>(S,=)==>(S,=)) (&)).
Proof. red. intros. apply _. Qed.
Hint Extern 0 (Find_Proper_Signature (@sg_op) 0 _) => eexact sg_op_proper_fp : typeclass_instances.

Lemma inv_closed `{Group (G:=G)} : Closed (G ==> G) (⁻¹).
Proof _.
Hint Extern 5 (_⁻¹ ∊ _) => eapply @inv_closed : typeclass_instances. 

Lemma inv_proper_fp : Find_Proper_Signature (@inv) 0
  (∀ A Ginv Ae Gop Gunit G `{@Group A Ae Gop Gunit Ginv G}, Proper ((G,=)==>(G,=)) (⁻¹)).
Proof. red. intros. pose proof inverse_proper. exact (setoidmor_proper (⁻¹)). Qed.
Hint Extern 0 (Find_Proper_Signature (@inv) 0 _) => eexact inv_proper_fp : typeclass_instances.


(* Commutative structures are instances of their noncommutative counterparts *)

Instance commonoid_monoid `{cm: CommutativeMonoid (M:=M)} : Monoid M.
Proof. destruct cm. split; try apply _. exact right_id_from_left. Qed.

Lemma commonoid_from_monoid `{Monoid (M:=M)} `{!Commutative (&) M} : CommutativeMonoid M.
Proof. repeat (split; try apply _). Qed.

Instance abgroup_group `{ag: AbGroup (G:=G)} : Group G.
Proof. destruct ag. split; try apply _. exact right_inv_from_left. Qed.

Lemma abgroup_from_group `{Group (G:=G)} `{!Commutative (&) G} : AbGroup G.
Proof. repeat (split; try apply _). Qed.


(* Structure predicates are proper in their subset argument *)

Ltac structure_proper :=
  red; intros; intros ?? E P; destruct P; split; try apply _; rewrite <- E; apply _.

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
Proof. rewrite_on M <- (right_identity (&) x), (left_identity (&) e). subreflexivity. Qed.

Lemma monoid_unit_unique_r x `{x ∊ M} `{!RightIdentity (&) x M} : x = e.
Proof. rewrite_on M <- (left_identity (&) x), (right_identity (&) e). subreflexivity. Qed.

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
Lemma id_semigroup_mor `(S:Subset A) `{S ⊆ T} `{SemiGroup A (S:=S)} `{!SemiGroup T} : SemiGroup_Morphism S T id.
Proof. split; try apply _. now intros. Qed.
Hint Extern 0 (SemiGroup_Morphism _ _ id) => class_apply @id_semigroup_mor : typeclass_instances.

Lemma id_monoid_mor `(M:Subset A) `{M ⊆ N} `{Monoid A (M:=M)} `{!Monoid N} : Monoid_Morphism M N id.
Proof. split; try apply _. subreflexivity. Qed.
Hint Extern 0 (Monoid_Morphism _ _ id) => class_apply @id_monoid_mor : typeclass_instances.

Lemma compose_semigroup_morphism `(S:Subset A) `{SemiGroup A (S:=S)} `{SemiGroup (S:=T)} `{SemiGroup (S:=U)}
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

Lemma invert_semigroup_morphism {A B} `{S:Subset A} `{T:Subset B}
 (f:S ⇀ T) `{SemiGroup_Morphism A B (S:=S) (T:=T) (f:=f)} `{!Inverse f} `{!Bijective S T f} :
  SemiGroup_Morphism T S (inverse f).
Proof. pose proof sgmor_a. pose proof sgmor_b. split; try apply _.
  intros x ? y ?. apply (injective f _ _).
  now rewrite (T $ preserves_sg_op _ _), 3!(T $ surjective_applied _ _).
Qed.
Hint Extern 4 (SemiGroup_Morphism _ _ (inverse _)) => eapply @invert_semigroup_morphism : typeclass_instances.

Lemma invert_monoid_morphism {A B} `{M:Subset A} `{N:Subset B}
 (f:M ⇀ N) `{Monoid_Morphism A B (M:=M) (N:=N) (f:=f)} `{!Inverse f} `{!Bijective M N f} :
  Monoid_Morphism N M (inverse f).
Proof. pose proof monmor_a. pose proof monmor_b. split; try apply _.
  apply (injective f _ _).
  now rewrite (N $ preserves_mon_unit), (N $ surjective_applied _ _).
Qed.
Hint Extern 4 (Monoid_Morphism _ _ (inverse _)) => eapply @invert_monoid_morphism : typeclass_instances.

Section groupmor_props.
  Context `{G:Subset A} `{H:Subset B} `{Group (A:=A) (G:=G)} `{Group (A:=B) (G:=H)} {f : G ⇀ H} `{!SemiGroup_Morphism G H f}.

  Global Instance: Monoid_Morphism G H f.
  Proof. split; try apply _.
    apply (right_cancellation (&) (f e) H _ _).
    now rewrite <- (H $ preserves_sg_op _ _), -> (G $ left_identity (&) _), -> (H $ left_identity (&) _).
  Qed.

  Lemma preserves_inverse x `{x ∊ G}: f x⁻¹ = (f x)⁻¹.
  Proof.
    apply (left_cancellation (&) (f x) H _ _).
    rewrite <- (H $ preserves_sg_op _ _).
    rewrite_on G -> (right_inverse (&) x).
    rewrite_on H -> (right_inverse (&) (f x)).
    exact preserves_mon_unit.
  Qed.
End groupmor_props.

Ltac structure_mor_proper :=
  red; intros; intros S1 S2 ES T1 T2 ET f g Ef; destruct 1; rewrite <- Ef;
  split; [ rewrite <-ES | rewrite <-ET | rewrite <-ES, <-ET |..]; try apply _.

Lemma semigroup_morphism_proper: Find_Proper_Signature (@SemiGroup_Morphism) 0
  (∀ A Ae B Be Sop Top, Proper ((=) ==> (=) ==> eq ==> impl) (@SemiGroup_Morphism A Ae B Be Sop Top)).
Proof. structure_mor_proper.
  intros x Hx y Hy. rewrite <-ES in Hx, Hy. eauto.
Qed.
Hint Extern 0 (Find_Proper_Signature (@SemiGroup_Morphism) 0 _) => eexact semigroup_morphism_proper : typeclass_instances.

Lemma monoid_morphism_proper: Find_Proper_Signature (@Monoid_Morphism) 0
  (∀ A Ae B Be Sunit Tunit Sop Top,
    Proper ((=) ==> (=) ==> eq ==> impl) (@Monoid_Morphism A Ae B Be Sunit Tunit Sop Top)).
Proof. now structure_mor_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@Monoid_Morphism) 0 _) => eexact monoid_morphism_proper : typeclass_instances. 

