Require Import
  abstract_algebra additional_operations
  interfaces.orders interfaces.naturals interfaces.integers interfaces.rationals
  interfaces.metric_spaces metric.metric_spaces metric.rationals
  theory.setoids implementations.dyadics
  implementations.intfrac_rationals
  orders.integers orders.rationals orders.abs
  nonneg_integers_naturals theory.nat_pow theory.shiftl
  misc.quote.

Local Open Scope mc_abs_scope.

Section contents.
  Context `{Integers (Z:=Z)} `{UnEq _} `{!DenialInequality Z}
          `{Le _} `{Lt _} `{!FullPseudoSemiRingOrder Z}.
  Context `{!StrongSubDecision Z Z (≤)} `{!StrongSubDecision Z Z (=)}.
  Context {pw} `{!ShiftLSpec Z Z⁺ pw}.

  Notation DtoFracZ := (DtoQ (cast Z (Frac Z))).

  Instance dyadic_ball: Ball (Dyadic Z) := projected_ball DtoFracZ.
  Instance dyadic_metric: MetricSpace (Dyadic Z) := projected_metric_space DtoFracZ.
End contents.

Hint Extern 2 (Ball (elt_type (Dyadic _))) => eapply @dyadic_ball : typeclass_instances.
Hint Extern 2 (Ball (DyadicT _)) => eapply @dyadic_ball : typeclass_instances.
Hint Extern 2 (MetricSpace (Dyadic _)) => eapply @dyadic_metric : typeclass_instances.

(*
Section another_rationals.
  Context `{Integers (Z:=Z)} `{UnEq _} `{!StandardUnEq Z}
          `{Le _} `{Lt _} `{!FullPseudoSemiRingOrder Z}.
  Context `{!StrongSubDecision Z Z (≤)} `{!StrongSubDecision Z Z (=)}.
  Context {pw} `{!ShiftLSpec Z Z⁺ pw}.

  Context `{Rationals (Q:=Q)} `{Le _} `{Lt _} `{!FullPseudoSemiRingOrder Q}.
  Context  (ZtoQ: Z ⇀ Q) `{!Ring_Morphism Z Q ZtoQ}.

  Notation DtoFracZ := (DtoQ (cast Z (Frac Z))).
  Notation DtoQ' := (DtoQ ZtoQ).
  Notation QtoFracZ := (rationals_to_field Q (Frac Z)).

  Lemma dyadic_ball_def `{Abs _} `{!DecAbs Z} ε `{ε ∊ Q}
    x `{x ∊ Dyadic Z} y `{y ∊ Dyadic Z} :
    ball ε x y ↔ DtoQ' (|x-y|) ≤ ε.
  Proof. unfold ball, dyadic_ball, projected_ball.
    rewrite (msp_ball_indp_Q (Q2:=Frac Z) _ _ _).
    rewrite (rationals_ball_def _ _ _).
    assert (DtoFracZ x - DtoFracZ y = QtoFracZ (DtoQ' (x-y))) as E.
      setoid_rewrite ( DtoQ_unique (QtoFracZ ∘ DtoQ') _ _ (_ : Proper (Dyadic Z,=) (x-y)) ).
      now preserves_simplify (DtoFracZ).
    rewrite_on (Frac Z) ->E, <- (preserves_abs QtoFracZ (DtoQ' (x-y))).
    rewrite (Q $ preserves_abs DtoQ' _).
    symmetry. exact (order_embedding _ _ _).
  Qed.
End another_rationals.
*)
