Require Import
  Ring Field abstract_algebra setsig theory.setoids theory.fields.
Require Export
  stdlib_ring.

Section field_ops.
  Context `(F:set) `{H:Field _ (F:=F)}.

  Instance stdlib_field_dec_inv_closed : Closed (F ₀ ⇀ F ₀) inv := _.
End field_ops.

Hint Extern 2 (Inv (setsig ?F)) => eapply (setsig_inv F (pf0:=stdlib_ring_zero_closed F) (pfi:=stdlib_field_dec_inv_closed F)) : typeclass_instances.


Section field.

  Context `{Field (F:=F)} `{!DenialInequality F} `{!SubDecision F F (=)}.

  Notation F' := (every (setsig F)).

  Instance: DenialInequality F' := setsig_denial_inequality F.
  Instance: Field F' := setsig_dec_field F.

  Lemma stdlib_field_dec_theory :
    Field_theory.field_theory (R:=setsig F) 0 1 (+) (.*.) (λ x y, x - y) (-)
                              (λ x y, x / y) inv (=).
  Proof. split. exact (stdlib_ring_theory F).
  + rewrite <- (denial_inequality _ _). now destruct field_nontrivial.
  + reflexivity.
  + intros x E. rewrite <- (denial_inequality _ _) in E.
    assert (x ∊ F' ₀) by now split.
    exact (field_inv_l x).
  Qed.

End field.

Arguments stdlib_field_dec_theory {_ _ _ _ _ _ _ _ _} F {_ _ _}.

Ltac stdlib_field_dec_quote F := 
  let H1 := constr:(_ : CommutativeSemiRing F) in
  let H2 := constr:(_ : CommutativeRing F) in
  let H3 := constr:(_ : Field F) in
  let zc := constr:(stdlib_ring_zero_closed F (H:=H1)) in
  let oc := constr:(stdlib_ring_one_closed  F (H:=H1)) in
  let pc := constr:(stdlib_ring_plus_closed F (H:=H1)) in
  let mc := constr:(stdlib_ring_mult_closed F (H:=H1)) in
  let nc := constr:(stdlib_ring_negate_closed F (H:=H2)) in
  let ic := constr:(stdlib_field_dec_inv_closed F (H:=H3)) in
  setsig_quote F zc oc pc mc nc ic.


Ltac decfield F := 
  let rec aux expr :=
    match expr with 
    | @equiv _ _ ?x ?y => aux x; aux y
    | @plus _ _ ?x ?y => aux x; aux y
    | @mult _ _ ?x ?y => aux x; aux y
    | @negate _ _ ?x => aux x
    | @inv _ _ ?x => aux x;
      let E := fresh "Eden" in
      try (destruct (_ : x ∊ F ₀) as [_ E];
           red in E; rewrite (denial_inequality _ _) in E)
    | _ => idtac
    end
  in match goal with |- ?e => aux e end;
  setsig_quote_equiv F ltac:(stdlib_field_dec_quote F); field; intuition.
