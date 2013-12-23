Require Import
  abstract_algebra interfaces.naturals.

Class IntegersToRing `(Z:set)
  := integers_to_ring: ∀ `(R:set) `{Mult R} `{Plus R} `{One R} `{Zero R} `{Negate R}, Z ⇀ R.
Arguments integers_to_ring {A} Z {IntegersToRing _} R {_ _ _ _ _} _.
Instance: Params (@integers_to_ring) 10.

Section definition.
  Context `{CommutativeRing (R:=Z)}.
  Notation f := (integers_to_ring _ _).

  Class Integers {U: IntegersToRing Z} :=
  { integers_ring :>> CommutativeRing Z
  ; integers_to_ring_mor `{CommutativeRing (R:=R)} : SemiRing_Morphism Z R f
  ; integers_initial     `{CommutativeRing (R:=R)}
      (h: Z ⇀ R) `{!SemiRing_Morphism Z R h} : h = f
  }.
End definition.
Arguments Integers {_ _ _ _ _ _ _} Z {U}.

Hint Extern 2 (SemiRing_Morphism _ _ (integers_to_ring _ _)) => class_apply @integers_to_ring_mor : typeclass_instances.

Section specializable.
  Context `(Z:set) `(N:set) `{Integers _ (Z:=Z)} `{Naturals _ (N:=N)}.

  Class IntAbs := int_abs_sig x : {n | x ∊ Z → n ∊ N ∧ naturals_to_semiring N Z n = x } 
                                + {n | x ∊ Z → n ∊ N ∧ naturals_to_semiring N Z n = -x }.

  Definition int_abs `{ia : IntAbs} : Z ⇀ N := λ x,
    match int_abs_sig x with
    | inl (exist n _) => n
    | inr (exist n _) => n
    end.

  Definition int_to_nat `{Zero _} `{ia : IntAbs} : Z ⇀ N := λ x,
    match int_abs_sig x with
    | inl (exist n _) => n
    | inr (exist n _) => 0
    end.

End specializable.

Instance: Params (@int_abs) 12.
Instance: Params (@int_abs_sig) 12.
Instance: Params (@int_to_nat) 13.
