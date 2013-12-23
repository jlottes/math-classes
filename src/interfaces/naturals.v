Require Import
 abstract_algebra.

Class NaturalsToSemiRing `(N:set)
  := naturals_to_semiring: ∀ `(R:set) `{Mult R} `{Plus R} `{One R} `{Zero R}, N ⇀ R.
Arguments naturals_to_semiring {_} N {NaturalsToSemiRing _} R {_ _ _ _} _.
Instance: Params (@naturals_to_semiring) 9.

Section definition.
  Context `(N:set) `{CommutativeSemiRing _ (R:=N)}.
  Local Notation f := (naturals_to_semiring _ _).

  Class Naturals {U: NaturalsToSemiRing N} :=
  { naturals_ring :>> CommutativeSemiRing N
  ; naturals_to_semiring_mor `{CommutativeSemiRing (R:=R)} : SemiRing_Morphism N R f
  ; naturals_initial         `{CommutativeSemiRing (R:=R)}
      (h: N ⇀ R) `{!SemiRing_Morphism N R h} : h = f
  }.
End definition.

Hint Extern 2 (SemiRing_Morphism _ _ (naturals_to_semiring _ _)) => class_apply @naturals_to_semiring_mor : typeclass_instances.

(* Specializable operations: *)

Class NatDistance `{Equiv A} `{Plus A} (N:set)
  := nat_distance_sig x y : {z | x ∊ N → y ∊ N → z ∊ N ∧ x + z = y } 
                          + {z | x ∊ N → y ∊ N → z ∊ N ∧ y + z = x }.

Definition nat_distance `{nd : NatDistance (N:=N)} : N ⇀ N ⇀ N := λ x y,
  match nat_distance_sig x y with
  | inl (exist n _) => n
  | inr (exist n _) => n
  end.
Instance: Params (@nat_distance_sig) 5.
Instance: Params (@nat_distance) 5.
