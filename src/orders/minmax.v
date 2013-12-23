Require Import
  abstract_algebra interfaces.orders orders.orders
  orders.lattices theory.setoids theory.products.

Definition sort `{X:set} `{Le _} `{!StrongSubDecision X X (≤)} : X ⇀ X ⇀ X * X
  := λ x y, if decide_sub_strong (≤) x y then (x, y) else (y, x).

Definition min `{Le A} `{X:@set A} `{!StrongSubDecision X X (≤)} : Meet _ := λ x y, fst (sort x y).
Definition max `{Le A} `{X:@set A} `{!StrongSubDecision X X (≤)} : Join _ := λ x y, snd (sort x y).
(* Force the typeclass search to choose the Le instance first,
   before looking for a decision procedure. *)
Hint Extern 5 (Meet ?A) => class_apply (@min A _) : typeclass_instances.
Hint Extern 5 (Join ?A) => class_apply (@max A _) : typeclass_instances.

Section contents.
  Context `{TotalOrder (S:=U)} `{!Subset U X} `{!StrongSubDecision X X (≤)}.

  Instance: Setoid U := po_setoid.
  Instance: ∀ `{x ∊ U}, x ∊ X. Proof. firstorder. Qed.

  Instance sort_morphism : Morphism (U ⇒ U ⇒ U*U) sort.
  Proof. apply binary_morphism_proper_back.
    intros ?? E1 ?? E2. unfold_sigs. unfold sort.
    do 2 case (decide_sub_strong _); simpl;
    intro P; pose proof P _ _ as Ea; clear P;
    intro P; pose proof P _ _ as Eb; clear P; red_sig.
  + firstorder.
  + contradict Ea. now rewrite <-(U $ E1), <-(U $ E2).
  + contradict Eb. now rewrite   (U $ E1),   (U $ E2).
  + firstorder.
  Qed.

  Instance: Closed (U ⇀ U ⇀ U) (⊓). Proof. unfold meet, min. intros ?? ??. apply _. Qed.
  Instance: Closed (U ⇀ U ⇀ U) (⊔). Proof. unfold join, max. intros ?? ??. apply _. Qed.

  Instance minmax_lattice: LatticeOrder U.
  Proof.
    repeat (split; try apply _); unfold join, meet, max, min, sort;
     intros; case (decide_sub_strong _); simpl; intuition; try easy; apply (le_flip _ _);
     intuition.
  Qed.

  Instance: LeftDistribute max min U.
  Proof.
    intros x ? y ? z ?.
    pose proof (_ : x ∊ X). pose proof (_ : y ∊ X). pose proof (_ : z ∊ X).
    unfold min, max, sort.
    repeat case (decide_sub_strong _); simpl; intuition; try easy;
    apply (antisymmetry (≤) _ _); trivial.
    match goal with H : x ≤ z → False |- _ => destruct H end. subtransitivity y.
    subtransitivity y; now apply le_flip.
  Qed.

  Instance minmax_distr_lattice : DistributiveLattice U.
  Proof. repeat (split; try apply _). Qed.
End contents.

Hint Extern 5 (LatticeOrder (Ameet := min) (Ajoin := max) _) => eapply @minmax_lattice : typeclass_instances.
Hint Extern 5 (DistributiveLattice (Ameet := min) (Ajoin := max) _) => eapply @minmax_distr_lattice : typeclass_instances.
Hint Extern 5 (MeetSemiLatticeOrder (Ameet := @min ?A ?l ?X ?d) _) =>
  eapply (lattice_order_meet (Ameet:=@min A l X d) (Ajoin:=@max A l X d)) : typeclass_instances.
Hint Extern 5 (JoinSemiLatticeOrder (Ajoin := @max ?A ?l ?X ?d) _) => 
  eapply (lattice_order_join (Ameet:=@min A l X d) (Ajoin:=@max A l X d)) : typeclass_instances.
