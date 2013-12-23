Require Import
  abstract_algebra interfaces.rationals interfaces.orders interfaces.affine_extension
  theory.sets theory.rationals orders.rationals
  orders.lattices orders.minmax lattice_ordered_rings orders.abs
  the_rationals implementations.affinely_extended_ring
  orders.affinely_extended_field
  stdlib_field_dec.

Module Type TheAERationalsSig.
  Parameter A : Type.
  Parameter Q : @set A.
  Parameter Qinf : AffExt Q.
  Parameter Qfull : AffExtFull Q.
  Parameter plus : Plus A.
  Parameter mult : Mult A.
  Parameter zero : Zero A.
  Parameter one  : One A.
  Parameter infty: Infty A.
  Parameter negate : Negate A.
  Parameter inv  : Inv A.
  Parameter equiv: Equiv A.
  Parameter uneq : UnEq A.
  Parameter U    : RationalsToField Q.
  Parameter rationals : @Rationals A Q plus mult zero one negate inv equiv uneq U.
  Parameter le   : Le A.
  Parameter lt   : Lt A.
  Parameter ae_field : AffinelyExtendedField Q.
  Parameter eq_dec : StrongSubDecision Qfull Qfull (=).
  Parameter le_dec : StrongSubDecision Qfull Qfull (≤).
End TheAERationalsSig.

Local Notation Q' := the_rationals.
Local Notation T := (AffineExtendT TheRationals.A).
Local Notation X := (AffineExtendImage Q').

Module TheAERationals : TheAERationalsSig.
  Definition A : Type := T.
  Definition Q : @set A := X.
  Definition Qinf := _ : AffExt X.
  Definition Qfull := _ : AffExtFull X.
  Definition plus  := _ : Plus T.
  Definition mult  := _ : Mult T.
  Definition zero  := _ : Zero T.
  Definition one   := _ : One T.
  Definition infty := _ : Infty T.
  Definition negate:= _ : Negate T.
  Definition inv   := _ : Inv T.
  Definition equiv := _ : Equiv T.
  Definition uneq  := _ : UnEq T.
  Instance: AffinelyExtendedField X := _.
  Definition U     := rationals.iso_to_field (cast Q' X).
  Definition rationals := rationals.iso_is_rationals (cast Q' X).
  Definition le := _ : Le T.
  Definition lt := _ : Lt T.
  Definition ae_field := _ : AffinelyExtendedField X.
  Definition eq_dec := _ : StrongSubDecision (AffineExtendFull Q') (AffineExtendFull Q') (=).
  Definition le_dec := _ : StrongSubDecision (AffineExtendFull Q') (AffineExtendFull Q') (≤).
End TheAERationals.

Notation the_ae_rationals := TheAERationals.Q.
Hint Extern 10 (@set TheAERationals.A) => eexact (aff_ext_full the_ae_rationals) : typeclass_instances.
Hint Extern 12 (@set TheAERationals.A) => eexact (aff_ext the_ae_rationals) : typeclass_instances.

Local Notation QA := TheAERationals.A.
Local Notation Q := the_ae_rationals.
Local Notation "Q∞" := (aff_ext Q).
Local Notation Qfull := (aff_ext_full Q).
Add Field Q : (stdlib_field_dec_theory Q).

Hint Extern 2 (Meet QA) => eexact (min (X:=Qfull)) : typeclass_instances.
Hint Extern 2 (Meet (elt_type Q)) => eexact (min (X:=Qfull)) : typeclass_instances.
Hint Extern 2 (Meet (elt_type Q∞)) => eexact (min (X:=Qfull)) : typeclass_instances.
Hint Extern 2 (Join QA) => eexact (max (X:=Qfull)) : typeclass_instances.
Hint Extern 2 (Join (elt_type Q)) => eexact (max (X:=Qfull)) : typeclass_instances.
Hint Extern 2 (Join (elt_type Q∞)) => eexact (max (X:=Qfull)) : typeclass_instances.

Instance: FullLatticeOrder Q := dec_full_lattice_order.
Instance: SemiRingLatticeOrder Q := dec_semiring_lattice_order.

Instance: FullLatticeOrder Q∞ := dec_full_lattice_order.

Ltac ae_rat_set_min δ a b Ea Eb :=
  set (δ := a ⊓ b); assert (δ ∊ Q∞₊) by (subst δ; apply _);
  assert (δ ≤ a) as Ea by (subst δ; exact (meet_lb_l (L:=Q∞) _ _));
  assert (δ ≤ b) as Eb by (subst δ; exact (meet_lb_r (L:=Q∞) _ _)).

(*
Ltac ae_rat_set_min δ a b Ea Eb :=
  set (δ := @meet _ (min (X:=Q∞)) a b); assert (δ ∊ Q∞₊) by (subst δ; apply _);
  assert (δ ≤ a) as Ea by (subst δ; exact (meet_lb_l (Ameet:=(min (X:=Q∞))) (L:=Q∞) _ _));
  assert (δ ≤ b) as Eb by (subst δ; exact (meet_lb_r (Ameet:=(min (X:=Q∞))) (L:=Q∞) _ _)).
*)
