Require Import
  abstract_algebra interfaces.orders orders.orders
  orders.lattices theory.setoids theory.products.

Definition sort `{X:Subset} `{Le _} `{!StrongSubDecision X X (≤)} : X ⇀ X ⇀ X * X
  := λ x y, if decide_sub_strong (≤) x y then (x, y) else (y, x).

Definition min `{Le A} `{X:@Subset A} `{!StrongSubDecision X X (≤)} : Meet _ := λ x y, fst (sort x y).
Definition max `{Le A} `{X:@Subset A} `{!StrongSubDecision X X (≤)} : Join _ := λ x y, snd (sort x y).
(* Force the typeclass search to choose the Le instance first,
   before looking for a decision procedure. *)
Hint Extern 5 (Meet ?A) => class_apply (@min A _) : typeclass_instances.
Hint Extern 5 (Join ?A) => class_apply (@max A _) : typeclass_instances.

Section contents.
  Context `{TotalOrder (S:=X)} `{!StrongSubDecision X X (≤)}.

  Instance: Setoid X := po_setoid.

  Instance sort_morphism : Morphism (X ⇒ X ⇒ X*X) sort.
  Proof. apply binary_morphism_proper_back.
    intros ?? E1 ?? E2. unfold_sigs. unfold sort.
    do 2 case (decide_sub_strong _); simpl;
    intro P; pose proof P _ _ as Ea; clear P;
    intro P; pose proof P _ _ as Eb; clear P; red_sig.
  + firstorder.
  + contradict Ea. now rewrite <-(X $ E1), <-(X $ E2).
  + contradict Eb. now rewrite   (X $ E1),   (X $ E2).
  + firstorder.
  Qed.

  Instance: Closed (X ⇀ X ⇀ X) (⊓). Proof. unfold meet, min. intros ?? ??. apply _. Qed.
  Instance: Closed (X ⇀ X ⇀ X) (⊔). Proof. unfold join, max. intros ?? ??. apply _. Qed.

  Global Instance: LatticeOrder X.
  Proof.
    repeat (split; try apply _); unfold join, meet, max, min, sort;
     intros; case (decide_sub_strong _); simpl; intuition; try easy; now apply le_flip.
  Qed.

  Instance: LeftDistribute max min X.
  Proof.
    intros x ? y ? z ?. unfold min, max, sort.
    repeat case (decide_sub_strong _); simpl; intuition; try easy;
    apply (subantisymmetry (≤) _ _); trivial.
    match goal with H : x ≤ z → False |- _ => destruct H end. subtransitivity y.
    subtransitivity y; now apply le_flip.
  Qed.

  Global Instance: DistributiveLattice X.
  Proof. repeat (split; try apply _). Qed.
End contents.

