Require Import
  abstract_algebra.

Class IntegersToRing `(Z:Subset A)
  := integers_to_ring: ∀ `(R:Subset B) `{Mult B} `{Plus B} `{One B} `{Zero B} `{Negate B}, A → B.
Arguments integers_to_ring {A} Z {IntegersToRing B} R {_ _ _ _ _} _.
Instance: Params (@integers_to_ring) 10.

Class Integers {A e plus mult zero one negate} (Z:Subset A) {U: IntegersToRing Z} :=
  { integers_ring:> @CommutativeRing A e plus mult zero one negate Z
  ; integers_to_ring_mor:> ∀ `{CommutativeRing (R:=R)}, Ring_Morphism (integers_to_ring Z R) Z R
  ; integers_initial `{CommutativeRing (R:=R)} h `{!Ring_Morphism h Z R} :
      ((Z,=)==>(=))%signature h (integers_to_ring Z R)
  }.

(*
Section specializable.
  Context (Z N : Type) `{Integers Z} `{Naturals N}.

  Class IntAbs := int_abs_sig : ∀ x,
    { n : N | naturals_to_semiring N Z n = x } + { n : N | naturals_to_semiring N Z n = -x }.

  Definition int_abs `{ia : IntAbs} (x : Z) : N :=
    match int_abs_sig x with
    | inl (n↾_) => n
    | inr (n↾_) => n
    end.

  Definition int_to_nat `{Zero N} `{ia : IntAbs} (x : Z) : N :=
    match int_abs_sig x with
    | inl (n↾_) => n
    | inr (n↾_) => 0
    end.
End specializable.

Instance: Params (@int_abs) 10.
Instance: Params (@int_abs_sig) 10.
Instance: Params (@int_to_nat) 11.
*)
