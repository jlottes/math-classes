(* Interface for the complex numbers.

   Defined as a field C containing the reals R with the universal property
   of the quotient ring R[x]/< x^2+1 > .
*)

(*   E!g
   C----> S     Ring S, i in S, i^2+1 = 0, SemiRing_Morphism R S f
   ^      ^     E!g:C->S, SemiRing_Morphism C S g,
 id|     / f       (g : R -> S) = f,  g i = i
   R----/

*)

Require Import
  abstract_algebra interfaces.reals.

Class ImaginaryUnit A := i : A.
Typeclasses Transparent ImaginaryUnit.

Class ComplexReals `(C:@set A) := complex_reals : @set A.
Typeclasses Transparent ComplexReals.
Arguments complex_reals {_} C {_} _.

Local Notation R := (complex_reals _).

Class ComplexToRing {A} (C:@set A) `{!ComplexReals C}
  := complex_to_ring: ∀ {B} `{S:@set B} `{Plus B} `{Mult B} `{ImaginaryUnit B},
     (R ⇀ S) → (C ⇀ S).
Arguments complex_to_ring {_} C {_ _ _ S _ _ _} _ _.

Class ComplexRing `{Aplus:Plus A} {Amult:Mult A} {Azero:Zero A} {Aone:One A} {Anegate:Negate A}
         {Aunit:ImaginaryUnit A} {Ae:Equiv A} (C:set) : Prop :=
{ complex_ring_comring :>> CommutativeRing C
; imaginary_unit_exists :>> i ∊ C
; imaginary_unit_def : i*i + 1 = 0
}.

Section complex_ring_morphism.
  Context {A B} {Ae:Equiv A} {Be:Equiv B}.
  Context {Aplus:Plus A} {Bplus:Plus B}.
  Context {Amult:Mult A} {Bmult:Mult B}.
  Context {Azero:Zero A} {Bzero:Zero B}.
  Context {Aone :One  A} {Bone :One  B}.
  Context {Anegate:Negate A} {Bnegate:Negate B}.
  Context {Aunit:ImaginaryUnit  A} {Bunit:ImaginaryUnit  B}.

  Class ComplexRing_Morphism C₁ C₂ f :=
    { cringmor_a : ComplexRing (A:=A) C₁
    ; cringmor_b : ComplexRing (A:=B) C₂
    ; cringmor_sring_mor :>> SemiRing_Morphism C₁ C₂ f
    ; cringmor_preserves_i : f i = i
    }.
End complex_ring_morphism.
Definition preserves_i `{ComplexRing (C:=C₁)} `{ComplexRing (C:=C₂)} {f : C₁ ⇀ C₂} `{!ComplexRing_Morphism C₁ C₂ f} := cringmor_preserves_i.


Section definition.
  Context {A} (C:@set A) {Aunit: ImaginaryUnit C} `{!ComplexReals C} `{Reals _ (R:=R)}.
  Context `{!ComplexToRing C}.

  Section another_ring.
    Context `{S:set} `{ComplexRing _ (C:=S)} (f:R ⇀ S).

    Class ComplexToRingSpec (g : C ⇀ S) : Prop :=
    { complex_to_ring_mor : ComplexRing_Morphism C S g
    ; complex_to_ring_extends : f = (g : R ⇀ S)
    ; complex_to_ring_unique (h : C ⇀ S) `{!ComplexRing_Morphism C S h}
      : f = (h : R ⇀ S) → h = g
    }.
  End another_ring.

  Class ComplexNumbers : Prop :=
  { complex_field :>> Field C
  ; complex_numbers_reals :>> Reals R
  ; complex_reals_subsetoid :>> R ⊆ C
  ; complex_complex :>> ComplexRing C
  ; complex_spec `(S:set) `{ComplexRing _ (C:=S)}
      (f:R ⇀ S) `{!SemiRing_Morphism R S f}
    :> ComplexToRingSpec f (complex_to_ring C f)
  }.

End definition.

Hint Extern 2 (ComplexRing_Morphism ?C _ (complex_to_ring ?C ?f)) =>
 eapply (complex_to_ring_mor C f) : typeclass_instances.


(*

Class ComplexToRing {A} (R C:@set A)
  := complex_to_ring: ∀ `{P:set} `{Plus P} `{Mult P} `{Zero P} `{One P}
                        `{!ToPolynomialRing R P} `{!PolynomialVar P} `{!PolynomialEval R P}
                        `{S:set}, (P ⇀ S) → (C ⇀ S).
Arguments complex_to_ring {_} R C {_ _} P {_ _ _ _ _ _ _ _ _} _ _.

Section definition.
  Context {A} (R C:@set A) `{ArchimedeanField _ (F:=R)} {Cunit: ImaginaryUnit C}.
  Context `{!ToReals R} `{!ComplexToRing R C}.

  Section real_polynomials.
    Context `{CommutativeRing (R:=P)}.
    Context `{!ToPolynomialRing R P} `{!PolynomialVar P} `{!PolynomialEval R P}.

    Notation x := polynomial_var.
    Notation π := (polynomial_eval (id:R⇀C) i).

    Section another_ring.
      Context `(S:set) `{Ring _ (R:=S)} (f:P ⇀ S).

      Class ComplexToRingSpec (g : C ⇀ S) : Prop :=
      { complex_to_ring_srmor : SemiRing_Morphism C S g
      ; complex_to_ring_factors : f = g ∘ π
      ; complex_to_ring_unique (h : C ⇀ S) `{!SemiRing_Morphism C S h}
        : f = h ∘ π → h = g
      }.
    End another_ring.

    Class ComplexSpec : Prop :=
      complex_to_ring_spec `{S:set} `{Ring _ (R:=S)} (f:P ⇀ S) `{!SemiRing_Morphism P S f}
      : f (x*x+1) = 0 → ComplexToRingSpec S f (complex_to_ring R C P f)
    .
  End real_polynomials.

  Class ComplexNumbers : Prop :=
  { complex_field :>> Field C
  ; complex_reals :>> Reals R
  ; complex_reals_subsetoid :>> R ⊆ C
  ; imaginary_unit_exists :>> i ∊ C
  ; imaginary_unit_def : i*i + 1 = 0
  ; complex_spec `{CommutativeRing (R:=P)}
    `{!ToPolynomialRing R P} `{!PolynomialVar P} `{!PolynomialEval R P}
    `{!Dot R P} `{!Polynomial_Ring R P} : ComplexSpec (P:=P)
  }.
End definition.

*)
