Require Import
  abstract_algebra.

Class IntegersToRing `(Z:Subset A)
  := integers_to_ring: ∀ `(R:Subset B) `{Mult B} `{Plus B} `{One B} `{Zero B} `{Negate B}, Z ⇀ R.
Arguments integers_to_ring {A} Z {IntegersToRing B} R {_ _ _ _ _} _.
Instance: Params (@integers_to_ring) 10.

Class Integers {A plus mult zero one negate e} (Z:Subset A) {U: IntegersToRing Z} :=
  { integers_ring :> @CommutativeRing A plus mult zero one negate e Z
  ; integers_to_ring_mor :> ∀ `{CommutativeRing (R:=R)}, Ring_Morphism Z R (integers_to_ring Z R)
  ; integers_initial `{CommutativeRing (R:=R)} (h: Z ⇀ R) `{!Ring_Morphism Z R h} : h = integers_to_ring Z R
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
