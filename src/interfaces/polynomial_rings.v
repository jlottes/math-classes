Require Import abstract_algebra interfaces.modules.

Class ToPolynomialRing `(R:set) `(P:set) := to_polynomial_ring : R ⇀ P.
Arguments to_polynomial_ring {_ R} {_} P {ToPolynomialRing} _.
Instance: Params (@to_polynomial_ring) 5.

Class PolynomialVar `(P:set) := polynomial_var : P.

Class PolynomialEval `(R:set) `(P:set)
  := polynomial_eval : ∀ `{S:set} `{Plus S} `{Mult S} `{Zero S} `{One S} (φ:R ⇀ S), S → P ⇀ S.

Local Notation "#" := (to_polynomial_ring _).
Local Notation x := polynomial_var.

Section def.
  (*Context `{CommutativeRing (A:=A) (R:=R)} `{CommutativeRing (A:=B) (R:=P)}.*)
  Context `{UnitalCommutativeAlgebra (R:=R) (A:=P)}.
  Context `{!ToPolynomialRing R P} `{!PolynomialVar P} `{!PolynomialEval R P}.

  Section eval_spec.
    Context `{S:set} `{SemiRing _ (R:=S)} (φ:R ⇀ S).

    Class Polynomial_Evaluable a : Prop := polynomial_evaluable r `{r ∊ R} : a * φ r = φ r * a .

    Context `{!SemiRing_Morphism R S φ} a `{a ∊ S} `{!Polynomial_Evaluable a}.

    Class Polynomial_Eval_Spec (h:P ⇀ S) : Prop :=
    { polynomial_eval_mor    : SemiRing_Morphism P S h
    ; polynomial_eval_const  : h ∘ # = φ
    ; polynomial_eval_var    : h x = a
    ; polynomial_eval_unique (g:P ⇀ S) `{!SemiRing_Morphism P S g}
      : g ∘ # = φ → g x = a → g = h
    }.
  End eval_spec.

  Class Polynomial_Ring : Prop :=
  { poly_ring_comm_alg :>> UnitalCommutativeAlgebra R P
  ; poly_ring_inject_mor : SemiRing_Morphism R P #
  ; poly_ring_dot_def r `{r ∊ R} p `{p ∊ P} : r · p = #r * p 
  ; poly_ring_var_el : x ∊ P
  ; poly_ring_eval_mor `{S:set} `{SemiRing _ (R:=S)} (φ:R ⇀ S) `{!SemiRing_Morphism R S φ}
                       a `{a ∊ S} `{!Polynomial_Evaluable φ a}
    :> Polynomial_Eval_Spec φ a (polynomial_eval φ a)
  }.
End def.

Arguments Polynomial_Ring {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} R P {_ _ _}.

Hint Extern 2 (SemiRing_Morphism _ _ (to_polynomial_ring _)) => eapply @poly_ring_inject_mor : typeclass_instances.
Hint Extern 2 (polynomial_var (P:=?P) ∊ ?P) => eapply @poly_ring_var_el : typeclass_instances.
Hint Extern 2 (SemiRing_Morphism _ _ (polynomial_eval _ _)) => eapply @polynomial_eval_mor : typeclass_instances.

