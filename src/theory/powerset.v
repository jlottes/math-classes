Require Import
  abstract_algebra interfaces.orders theory.setoids theory.groups theory.lattices orders.lattices
  theory.jections.

(* We have a notation already for the powerset of X, (⊆ X) *)

Class UniverseSet {A} := universe_set : @set A.
Identity Coercion Id_UniverseSet_set : UniverseSet >-> set.

Instance universe_top `{X:UniverseSet} : Top set := X.

Hint Extern 10 (@set set) => exact (_:UniverseSet) : typeclass_instances.

Hint Extern 2 (_ ∊ (⊆ _)) => red : typeclass_instances.

Lemma powerset_subsetoid `{Setoid (S:=X)} : (⊆ X) ⊆ Setoid.
Proof. apply subsetoid_alt. apply _.
+ intros ?? E P. red. now rewrite <- E.
+ intros ? P. red in P. exact subsetoid_a.
Qed.
Hint Extern 2 ((⊆ _) ⊆ Setoid) => eapply @powerset_subsetoid : typeclass_instances.

Lemma powerset_setoid `{Setoid (S:=X)} : Setoid (⊆ X).
Proof subsetoid_a.
Hint Extern 2 (Setoid (⊆ _)) => eapply @powerset_setoid : typeclass_instances.

Lemma powerset_partial_order `{Setoid (S:=X)} : PartialOrder (Ale:=SubSetoid) (⊆ X).
Proof. rewrite (_ : (⊆ X) ⊆ Setoid). apply _. Qed.
Hint Extern 2 (PartialOrder (⊆ _)) => eapply @powerset_partial_order : typeclass_instances.

Lemma powerset_meet_semi_lattice_order `{Setoid (S:=X)} : MeetSemiLatticeOrder (Ale:=SubSetoid) (⊆ X).
Proof. pose proof @subsetoid_a.
  assert (∀ S T, S ⊆ X → T ⊆ X → S ⊓ T ⊆ S) by ( pose proof @subset;
    intros; apply subsetoid_alt; try apply _; intros ?? E [??]; unfold_sigs; split; now rewrite <-(X $ E)).
  assert (∀ S T, S ⊆ X → T ⊆ X → S ⊓ T ⊆ T) by ( pose proof @subset;
    intros; apply subsetoid_alt; try apply _; intros ?? E [??]; unfold_sigs; split; now rewrite <-(X $ E)).
  split.
  * apply _.
  * intros S s1 T s2. red in s1, s2. red. transitivity S; apply _.
  * intros S s1 T s2. red in s1, s2. red. apply _.
  * intros S s1 T s2. red in s1, s2. red. apply _.
  * intros S s1 T s2 U s3 E1 E2. red in s1, s2, s3, E1, E2. apply subsetoid_alt. apply _.
    - intros ?? [[[??][??]]E]. unfold_sigs.
      assert (x ∊ X) by now apply (_:Subset S X).
      assert (y ∊ X) by now apply (_:Subset S X).
      intro. now rewrite <-(X $ E).
    - apply (meet_glb (L:=Sets) _ _ _); red; apply _.
Qed.
Hint Extern 2 (MeetSemiLatticeOrder (⊆ _)) => eapply @powerset_meet_semi_lattice_order : typeclass_instances.

Lemma powerset_join_semi_lattice_order `{Setoid (S:=X)} : JoinSemiLatticeOrder (Ale:=SubSetoid) (⊆ X).
Proof. pose proof @subsetoid_a.
  assert (∀ S T U, U ⊆ X → S ⊆ U → T ⊆ U → S ⊔ T ⊆ U) as lub.
    intros. apply subsetoid_alt. apply _.
    intros ?? E [?|?]; [left | right]; now rewrite <-E.
    apply (join_lub (L:=Sets) _ _ _); red; apply _.
  assert (∀ S T, S ⊆ X → T ⊆ X → S ⊔ T ⊆ X). intros. apply lub; apply _.
  split.
  * apply _.
  * intros S s1 T s2. red in s1, s2. red. apply _.
  * intros S s1 T s2. red in s1, s2. red. split; try apply _.
      intros ?? E. unfold_sigs. pose proof (_ : S ⊔ T ⊆ X). intro. now rewrite <-(X $ E).
  * intros S s1 T s2. red in s1, s2. red. split; try apply _.
      intros ?? E. unfold_sigs. pose proof (_ : S ⊔ T ⊆ X). intro. now rewrite <-(X $ E).
  * intros S s1 T s2 U s3 E1 E2. red in s1, s2, s3, E1, E2. red. now apply lub.
Qed.
Hint Extern 2 (JoinSemiLatticeOrder (⊆ _)) => eapply @powerset_join_semi_lattice_order : typeclass_instances.


Lemma powerset_lattice_order `{Setoid (S:=X)} : LatticeOrder (Ale:=SubSetoid) (⊆ X).
Proof. split; apply _. Qed.
Hint Extern 2 (LatticeOrder (⊆ _)) => eapply @powerset_lattice_order : typeclass_instances.

Hint Extern 2 (MeetSemiLattice (⊆ ?X)) => eexact (meet_sl_order_meet_sl (Ale:=SubSetoid) (L:=(⊆ X))) : typeclass_instances.
Hint Extern 2 (JoinSemiLattice (⊆ ?X)) => eexact (join_sl_order_join_sl (Ale:=SubSetoid) (L:=(⊆ X))) : typeclass_instances.
Hint Extern 2 (Lattice (⊆ ?X)) => eexact (lattice_order_lattice (Ale:=SubSetoid) (L:=(⊆ X))) : typeclass_instances.

Lemma powerset_bounded_meet_semi_lattice `{Setoid (S:=X)}
  : BoundedSemiLattice (op:=meet_is_sg_op) (unit:=@top_is_mon_unit _ X) (⊆ X).
Proof. pose proof _ : MeetSemiLattice (⊆ X).
  split; [split |]; unfold mon_unit, top_is_mon_unit; [apply _ | red; apply _ | firstorder.. ].
Qed.
Hint Extern 2 (BoundedMeetSemiLattice (⊆ ?X)) => eapply (@powerset_bounded_meet_semi_lattice _ _ X): typeclass_instances.
(* The Top instance needs to be resolved (to X) before this hint is consulted. *)

Lemma powerset_bounded_join_semi_lattice `{Setoid (S:=X)} : BoundedJoinSemiLattice (⊆ X).
Proof. pose proof _ : JoinSemiLattice (⊆ X).
  split; [split |]; unfold mon_unit, bottom_is_mon_unit. apply _.
  + apply subsetoid_alt; [ apply _ | firstorder.. ].
  + intros ? s1 x. red in s1. split.
    intros [el|?]; trivial. now lazy in el.
    intro. now right.
  + firstorder.
Qed.
Hint Extern 2 (BoundedJoinSemiLattice (⊆ ?X)) => eapply (@powerset_bounded_join_semi_lattice _ _ X): typeclass_instances.

Lemma powerset_distr_lattice `{Setoid (S:=X)} : DistributiveLattice (⊆ X).
Proof. split. apply _.  intro. intros. exact (join_meet_distr_l (L:=Sets) _ _ _). Qed.
Hint Extern 2 (DistributiveLattice (⊆ _)) => eapply @powerset_distr_lattice : typeclass_instances.

Lemma union_subsetoid `{Setoid (S:=X)} U V `{U ⊆ X} `{V ⊆ X} : U ⊔ V ⊆ X.
Proof. apply (join_lub (L:=(⊆ X)) _ _ _); unfold le; apply _. Qed.
Hint Extern 5 (_ ⊔ _ ⊆ _) => eapply @union_subsetoid : typeclass_instances.

Lemma intersection_subsetoid `{Setoid (S:=X)} U V `{U ⊆ X} `{V ⊆ X} : U ⊓ V ⊆ X.
Proof. transitivity U; trivial. apply (meet_lb_l (L:=(⊆ X)) _ _). Qed.
Hint Extern 5 (_ ⊓ _ ⊆ _) => eapply @intersection_subsetoid : typeclass_instances.


Section images.
  Context `{Setoid (S:=X)} `{Setoid (S:=Y)} (f:X ⇀ Y) `{!Morphism (X ⇒ Y) f}.

  Hint Extern 0 (Top _) => eexact X : typeclass_instances.
  Hint Extern 0 (Top _) => eexact Y : typeclass_instances.

  Local Hint Extern 2 (CommutativeMonoid (⊆ _)) => eapply @bounded_semilattice_mon : typeclass_instances.
  Local Hint Extern 2 (Monoid (⊆ _)) => eapply @commonoid_monoid : typeclass_instances.

  Instance image_mor : Morphism ((⊆ X) ⇒ (⊆ Y)) (image f).
  Proof. intros S T [[s1 s2] E]. red in s1,s2. red_sig. intro x. split.
    intros [?[y[??]]]. split. apply _. assert (y ∊ T) by now rewrite <-E. now exists_sub y.
    intros [?[y[??]]]. split. apply _. assert (y ∊ S) by now rewrite ->E. now exists_sub y.
  Qed.

  Instance image_bounded_join_slmor : BoundedJoinSemiLattice_Morphism (⊆ X) (⊆ Y) (image f).
  Proof. apply bounded_join_sl_morphism_alt; try apply _.
  + intros S s1 T s2. red in s1,s2. intro y. split.
    intros [?[x[[?|?]?]]]; [left|right]; (split; [apply _| now exists_sub x]).
    intros [[?[x[??]]]|[?[x[??]]]]; (split; [apply _|..]);
      assert (x ∊ S ⊔ T) by first [now left | now right]; now exists_sub x.
  + firstorder.
  Qed.

  Context `{!Injective X Y f}.

  Instance image_meet_slmor : MeetSemiLattice_Morphism (⊆ X) (⊆ Y) (image f).
  Proof. apply meet_sl_morphism_alt; try apply _.
    intros S s1 T s2. red in s1,s2. intro y. split.
    intros [?[x[[??]?]]]. split; (split; [apply _|now exists_sub x]).
    intros [[?[x[??]]] [?[x'[??]]]]. pose proof @subset.
      assert (x = x') as E. apply (injective f _ _). subtransitivity y. subsymmetry.
      assert (x ∊ S ⊓ T). split. apply _. rewrite (X $ E). apply _.
    split. apply _. now exists_sub x.
  Qed.

  Instance image_lattice_mor : Lattice_Morphism (⊆ X) (⊆ Y) (image f).
  Proof. split; try apply _. exact bounded_join_sl_mor_is_join_sl_mor. Qed.

  Context `{!Inverse f} `{!Surjective X Y f}.

  Instance image_bounded_meet_slmor : BoundedMeetSemiLattice_Morphism (⊆ X) (⊆ Y) (image f).
  Proof. apply bounded_meet_sl_morphism_alt; try apply _.
    exact (preserves_meet (image f : (⊆ X) ⇀ (⊆ Y))).
    unfold top. intros y. split. now intros [? _]. intros ?. split. apply _.
    exists_sub (inverse f y). exact (surjective_applied _ _).
  Qed.

End images.

Hint Extern 2 (Morphism _ (image _)) => eapply @image_mor : typeclass_instances.
Hint Extern 2 (BoundedJoinSemiLattice_Morphism _ _ (image _)) => eapply @image_bounded_join_slmor : typeclass_instances.
Hint Extern 2 (JoinSemiLattice_Morphism _ _ (image _)) => eapply @bounded_join_sl_mor_is_join_sl_mor : typeclass_instances.
Hint Extern 2 (MeetSemiLattice_Morphism _ _ (image _)) => eapply @image_meet_slmor : typeclass_instances.
Hint Extern 2 (Lattice_Morphism _ _ (image _)) => eapply @image_lattice_mor : typeclass_instances.
Hint Extern 2 (BoundedMeetSemiLattice_Morphism _ _ (image _)) => eapply @image_bounded_meet_slmor : typeclass_instances.

Lemma image_is_order_preserving `{Setoid (S:=X)} `{Setoid (S:=Y)} (f:X ⇀ Y) `{!Morphism (X ⇒ Y) f} 
  : OrderPreserving (Ale:=(⊆)) (Ble:=(⊆)) (⊆ X) (⊆ Y) (image f).
Proof join_sl_mor_preserving _.
Hint Extern 2 (OrderPreserving _ _ (image _)) => eapply @image_is_order_preserving : typeclass_instances.

Lemma image_order_preserving `{Setoid (S:=X)} `{Setoid (S:=Y)} (f:X ⇀ Y) `{!Morphism (X ⇒ Y) f}
  U V `{V ⊆ X} `{U ⊆ V} : f⁺¹(U) ⊆ f⁺¹(V).
Proof. assert (U ⊆ X) by now transitivity V.
  now apply (order_preserving (Ale:=(⊆)) (Ble:=(⊆)) (S:=(⊆ X)) (T:=(⊆ Y)) (image f) U V).
Qed.
Hint Extern 5 (?f⁺¹(_) ⊆ ?f⁺¹(_)) => eapply @image_order_preserving : typeclass_instances.

Section inv_images.
  Context `{Setoid (S:=X)} `{Setoid (S:=Y)} (f:X ⇀ Y) `{!Morphism (X ⇒ Y) f}.

  Hint Extern 0 (Top _) => eexact X : typeclass_instances.
  Hint Extern 0 (Top _) => eexact Y : typeclass_instances.

  (*Local Hint Extern 2 (CommutativeMonoid (⊆ _)) => eapply @bounded_semilattice_mon : typeclass_instances.
  Local Hint Extern 2 (Monoid (⊆ _)) => eapply @commonoid_monoid : typeclass_instances.*)

  Instance inv_image_mor : Morphism ((⊆ Y) ⇒ (⊆ X)) (inv_image f).
  Proof. intros S T [[s1 s2] E]. red in s1,s2. red_sig. intro x. split.
    intros [??]. split. apply _. now rewrite <-E.
    intros [??]. split. apply _. now rewrite ->E.
  Qed.

  Instance inv_image_bounded_join_slmor : BoundedJoinSemiLattice_Morphism (⊆ Y) (⊆ X) (inv_image f).
  Proof. apply bounded_join_sl_morphism_alt; try apply _.
  + intros S s1 T s2. red in s1,s2. intro x. split.
    intros [?[?|?]]; [left|right]; now split.
    intros [[??]|[??]]; split; trivial; first [ now left | now right ].
  + firstorder.
  Qed.

  Instance inv_image_meet_slmor : MeetSemiLattice_Morphism (⊆ Y) (⊆ X) (inv_image f).
  Proof. apply meet_sl_morphism_alt; try apply _. firstorder. Qed.

  Instance inv_image_bounded_meet_slmor : BoundedMeetSemiLattice_Morphism (⊆ Y) (⊆ X) (inv_image f).
  Proof. apply bounded_meet_sl_morphism_alt; try apply _. firstorder.
    unfold top. intros x. split. now intros [? _]. intros ?. split; apply _.
  Qed.

  Instance inv_image_lattice_mor : Lattice_Morphism (⊆ Y) (⊆ X) (inv_image f).
  Proof. split; try apply _. exact bounded_join_sl_mor_is_join_sl_mor. Qed.

End inv_images.

Hint Extern 2 (Morphism _ (inv_image _)) => eapply @inv_image_mor : typeclass_instances.
Hint Extern 2 (BoundedJoinSemiLattice_Morphism _ _ (inv_image _)) => eapply @inv_image_bounded_join_slmor : typeclass_instances.
Hint Extern 2 (BoundedMeetSemiLattice_Morphism _ _ (inv_image _)) => eapply @inv_image_bounded_meet_slmor : typeclass_instances.
Hint Extern 2 (JoinSemiLattice_Morphism _ _ (inv_image _)) => eapply @bounded_join_sl_mor_is_join_sl_mor : typeclass_instances.
Hint Extern 2 (MeetSemiLattice_Morphism _ _ (inv_image _)) => eapply @inv_image_meet_slmor : typeclass_instances.
Hint Extern 2 (Lattice_Morphism _ _ (inv_image _)) => eapply @inv_image_lattice_mor : typeclass_instances.

Lemma inv_image_is_order_preserving `{Setoid (S:=X)} `{Setoid (S:=Y)} (f:X ⇀ Y) `{!Morphism (X ⇒ Y) f} 
  : OrderPreserving (Ale:=(⊆)) (Ble:=(⊆)) (⊆ Y) (⊆ X) (inv_image f).
Proof join_sl_mor_preserving _.
Hint Extern 2 (OrderPreserving _ _ (inv_image _)) => eapply @inv_image_is_order_preserving : typeclass_instances.

Lemma inv_image_order_preserving `{Setoid (S:=X)} `{Setoid (S:=Y)} (f:X ⇀ Y) `{!Morphism (X ⇒ Y) f}
  U V `{V ⊆ Y} `{U ⊆ V} : f⁻¹(U) ⊆ f⁻¹(V).
Proof. assert (U ⊆ Y) by now transitivity V.
  now apply (order_preserving (Ale:=(⊆)) (Ble:=(⊆)) (S:=(⊆ Y)) (T:=(⊆ X)) (inv_image f) U V).
Qed.
Hint Extern 5 (?f⁻¹(_) ⊆ ?f⁻¹(_)) => eapply @inv_image_order_preserving : typeclass_instances.

