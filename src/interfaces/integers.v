Require Import
  abstract_algebra interfaces.naturals.

Class IntegersToRing `(Z:Subset)
  := integers_to_ring: ∀ `(R:@Subset B) `{Mult B} `{Plus B} `{One B} `{Zero B} `{Negate B}, Z ⇀ R.
Arguments integers_to_ring {A} Z {IntegersToRing B} R {_ _ _ _ _} _.
Instance: Params (@integers_to_ring) 10.

Class Integers {A plus mult zero one negate e} (Z:@Subset A) {U: IntegersToRing Z} :=
  { integers_ring :>> @CommutativeRing A plus mult zero one negate e Z
  ; integers_to_ring_mor : ∀ `{CommutativeRing (R:=R)}, Ring_Morphism Z R (integers_to_ring Z R)
  ; integers_initial `{CommutativeRing (R:=R)} (h: Z ⇀ R) `{!Ring_Morphism Z R h} : h = integers_to_ring Z R
  }.

Hint Extern 2 (Ring_Morphism _ _ (integers_to_ring _ _)) => class_apply @integers_to_ring_mor : typeclass_instances.

Section specializable.
  Context `(Z:Subset) `(N:Subset) `{Integers _ (Z:=Z)} `{Naturals _ (N:=N)}.

  Class IntAbs := int_abs_sig x : {n | x ∊ Z → n ∊ N ∧ naturals_to_semiring N Z n = x } 
                                + {n | x ∊ Z → n ∊ N ∧ naturals_to_semiring N Z n = -x }.

  Definition int_abs `{ia : IntAbs} : Z ⇀ N := λ x,
    match int_abs_sig x with
    | inl (exist _ n _) => n
    | inr (exist _ n _) => n
    end.

  Definition int_to_nat `{Zero _} `{ia : IntAbs} : Z ⇀ N := λ x,
    match int_abs_sig x with
    | inl (exist _ n _) => n
    | inr (exist _ n _) => 0
    end.

End specializable.

Instance: Params (@int_abs) 12.
Instance: Params (@int_abs_sig) 12.
Instance: Params (@int_to_nat) 13.
