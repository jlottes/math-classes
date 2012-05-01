Require Import
 abstract_algebra.

Class NaturalsToSemiRing `(N:Subset A)
  := naturals_to_semiring: ∀ `(R:Subset B) `{Mult B} `{Plus B} `{One B} `{Zero B}, A → B.
Arguments naturals_to_semiring {A} N {NaturalsToSemiRing B} R {_ _ _ _} _.
Instance: Params (@naturals_to_semiring) 9.

Class Naturals {A e plus mult zero one} (N:Subset A) {U: NaturalsToSemiRing N} :=
  { naturals_ring:> @CommutativeSemiRing A e plus mult zero one N
  ; naturals_to_semiring_mor:> ∀ `{CommutativeSemiRing (R:=R)}, SemiRing_Morphism (naturals_to_semiring N R) N R
  ; naturals_initial `{CommutativeSemiRing (R:=R)} h `{!SemiRing_Morphism h N R} :
      ((N,=)==>(=))%signature h (naturals_to_semiring N R)
  }.


(* Specializable operations: *)
(*
Class NatDistance `(N:Subset A) `{Equiv A} `{Plus A}
  := nat_distance_sig : ∀ x y : N, { z : N | x + z = y } + { z : N | y + z = x }.
Definition nat_distance `{nd : NatDistance N} (x y : N) :=
  match nat_distance_sig x y with
  | inl (n↾_) => n
  | inr (n↾_) => n
  end.
Instance: Params (@nat_distance_sig) 4.
Instance: Params (@nat_distance) 4.
*)