Require Import
 abstract_algebra.

Class NaturalsToSemiRing `(N:Subset)
  := naturals_to_semiring: ∀ `(R:@Subset B) `{Mult B} `{Plus B} `{One B} `{Zero B}, N ⇀ R.
Arguments naturals_to_semiring {_} N {NaturalsToSemiRing B} R {_ _ _ _} _.
Instance: Params (@naturals_to_semiring) 9.

Class Naturals {A plus mult zero one e} (N:@Subset A) {U: NaturalsToSemiRing N} :=
  { naturals_ring :>> @CommutativeSemiRing A plus mult zero one e N
  ; naturals_to_semiring_mor : ∀ `{CommutativeSemiRing (R:=R)}, SemiRing_Morphism N R (naturals_to_semiring N R)
  ; naturals_initial `{CommutativeSemiRing (R:=R)} (h: N ⇀ R) `{!SemiRing_Morphism N R h} : h = naturals_to_semiring N R
  }.

Hint Extern 2 (SemiRing_Morphism _ _ (naturals_to_semiring _ _)) => class_apply @naturals_to_semiring_mor : typeclass_instances.

(* Specializable operations: *)

Class NatDistance `{Equiv A} `{Plus A} (N:@Subset A)
  := nat_distance_sig x y : {z | x ∊ N → y ∊ N → z ∊ N ∧ x + z = y } 
                          + {z | x ∊ N → y ∊ N → z ∊ N ∧ y + z = x }.

Definition nat_distance `{nd : NatDistance (N:=N)} : N ⇀ N ⇀ N := λ x y,
  match nat_distance_sig x y with
  | inl (exist _ n _) => n
  | inr (exist _ n _) => n
  end.
Instance: Params (@nat_distance_sig) 5.
Instance: Params (@nat_distance) 5.
