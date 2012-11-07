Require Import
  Ring Field abstract_algebra subsetsig theory.setoids theory.fields.
Require Export
  stdlib_ring.

Section field.

  Context `{Field (F:=F)} `{!StandardUnEq F} `{!SubDecision F F (=)}.

  Global Instance : SubsetSig_Closed (F ₀ ⇀ F ₀) inv := _ : Closed (F ₀ ⇀ F ₀) inv.

  Notation F' := (every (SubsetSig F)).

  Instance: StandardUnEq F' := subsetsig_standard_uneq F.
  Instance: Field F' := subsetsig_dec_field F.

  Lemma stdlib_field_theory :
    Field_theory.field_theory 0 1 (+) (.*.) (λ x y : SubsetSig F, x - y) (-)
                              (λ x y : SubsetSig F, x / y) inv (=).
  Proof. split. exact (stdlib_ring_theory F).
  + rewrite <- (standard_uneq _ _). solve_propholds.
  + reflexivity.
  + intros x E. rewrite <- (standard_uneq _ _) in E.
    assert (x ∊ F' ₀) by now split.
    exact (field_inv_l x).
  Qed.

End field.

Arguments stdlib_field_theory {_ _ _ _ _ _ _ _ _} F {_ _ _}.

Ltac subfield F := 
  let rec aux expr :=
    match expr with 
    | @equiv _ _ ?x ?y => aux x; aux y
    | @plus _ _ ?x ?y => aux x; aux y
    | @mult _ _ ?x ?y => aux x; aux y
    | @negate _ _ ?x => aux x
    | @inv _ _ ?x => aux x;
      let E := fresh "Eden" in
      try (destruct (_ : x ∊ F ₀) as [_ E];
           red in E; rewrite (standard_uneq _ _) in E)
    | _ => idtac
    end
  in match goal with |- ?e => aux e end;
  subsetsig_quote_equiv F; field; intuition.
