Require
  orders.naturals peano_naturals.
Require Import
  abstract_algebra interfaces.additional_operations interfaces.naturals interfaces.orders
  theory.setoids theory.rings theory.cut_minus.

Lemma nat_distance_el `{nd : NatDistance (N:=N)} x `{x ∊ N} y `{y ∊ N} : nat_distance x y ∊ N.
Proof. unfold nat_distance. destruct (nat_distance_sig x y) as [[z p]|[z p]]; tauto. Qed.

Local Existing Instance nat_distance_el.

Section contents.
Context `{Naturals (N:=N)}.

(** NatDistance instances are all equivalent, because their behavior is fully
 determined by the specification. *)
Lemma nat_distance_unique_respectful {a b : NatDistance N} : nat_distance (nd:=a) = nat_distance (nd:= b).
Proof. rewrite ext_equiv_binary_sig.
  intros x1 y1 E x2 y2 F. unfold_sigs. red_sig. unfold nat_distance, nat_distance_sig.
  destruct a as [[z1 p1]|[z1 p1]], b as [[z2 p2]|[z2 p2]];
  destruct (p1 _ _) as [? E1], (p2 _ _) as [? E2]; clear p1; clear p2.
  + apply (left_cancellation (+) x1 N _ _). subtransitivity x2. subtransitivity y2. now rewrite_on N -> E.
  + destruct (naturals.zero_sum z1 z2).
      apply (left_cancellation (+) x1 N _ _).
      rewrite (N $ associativity (+) _ _ _), (N $ E1), (N $ F).
      subtransitivity y1. subtransitivity x1; subsymmetry. exact (plus_0_r _).
    now subtransitivity 0.
  + destruct (naturals.zero_sum z2 z1).
      apply (left_cancellation (+) y1 N _ _).
      rewrite (N $ associativity (+) _ _ _), (N $ E2), <- (N $ F).
      subtransitivity x1. subtransitivity y1. subsymmetry. exact (plus_0_r _).
    now subtransitivity 0.
  + apply (left_cancellation (+) x2 N _ _). subtransitivity x1. subtransitivity y1. now rewrite_on N -> F.
Qed.

Lemma nat_distance_unique {a b: NatDistance N} x `{x ∊ N} y `{y ∊ N} : nat_distance (nd:=a) x y = nat_distance (nd:=b) x y.
Proof ext_equiv_binary_applied nat_distance_unique_respectful _ _.

Lemma nat_distance_proper `{!NatDistance N} : Morphism (N ⇒ N ⇒ N) nat_distance.
Proof. rewrite binary_morphism_ext_equiv. exact nat_distance_unique_respectful. Qed.

End contents.

Hint Extern 0 (Morphism _ nat_distance) => eapply @nat_distance_proper : typeclass_instances.

(** An existing instance of [CutMinus] allows to create an instance of [NatDistance]
 assuming decidability of (≤) on the entire type *)
Program Instance natdistance_cut_minus `{Naturals (N:=N)} `{UnEq _} `{Le _} `{Lt _} `{!StandardUnEq N} `{!FullPseudoSemiRingOrder N}
    `{!CutMinusSpec N cm} `{∀ x y, Decision (x ≤ y)} : NatDistance N :=
  λ x y, if decide_rel (≤) x y then inl (y ∸ x) else inr (x ∸ y).
Next Obligation. split. apply _. rewrite (N $ commutativity (+) _ _). now apply cut_minus_le. Qed.
Next Obligation. split. apply _. rewrite (N $ commutativity (+) _ _). now apply (cut_minus_le _ _), orders.le_flip. Qed.

(** Using the preceding instance we can make an instance for arbitrary models of the naturals
    by translation into [nat] on which we already have a [CutMinus] instance. *)
Local Notation nat := (every nat).
Global Program Instance natdistance_default `{Naturals (N:=N)} : NatDistance N | 10 := λ x y,
  match nat_distance_sig (naturals_to_semiring N nat x) (naturals_to_semiring N nat y) with
  | inl (exist _ n p) => inl (naturals_to_semiring nat N n)
  | inr (exist _ n p) => inr (naturals_to_semiring nat N n)
  end.
Next Obligation. pose proof p _ _ as [? E]. clear dependent p. split. apply _.
  rewrite <- ( N $ naturals.to_semiring_involutive N nat y ), <- E.
  now rewrite (N $ preserves_plus _ _), ( N $ naturals.to_semiring_involutive N nat x ).
Qed.
Next Obligation. pose proof p _ _ as [? E]. clear dependent p. split. apply _.
  rewrite <- ( N $ naturals.to_semiring_involutive N nat x ), <- E.
  now rewrite (N $ preserves_plus _ _), ( N $ naturals.to_semiring_involutive N nat y ).
Qed.

