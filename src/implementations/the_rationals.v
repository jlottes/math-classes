Require Import
  abstract_algebra interfaces.rationals interfaces.orders
  theory.rationals orders.rationals orders.abs
  orders.lattices orders.minmax lattice_ordered_rings
  the_integers intfrac_rationals
  stdlib_field_dec.

Module Type TheRationalsSig.
  Parameter A : Type.
  Parameter Q : @set A.
  Parameter plus : Plus A.
  Parameter mult : Mult A.
  Parameter zero : Zero A.
  Parameter one  : One A.
  Parameter negate : Negate A.
  Parameter inv  : Inv A.
  Parameter equiv: Equiv A.
  Parameter uneq : UnEq A.
  Parameter U    : RationalsToField Q.
  Parameter rationals : @Rationals A Q plus mult zero one negate inv equiv uneq U.
  Parameter le   : Le A.
  Parameter lt   : Lt A.
  Parameter order : FullPseudoSemiRingOrder Q.
End TheRationalsSig.

Local Notation Z := the_integers.
Local Notation T := (FracPair Z).
Local Notation X := (Frac Z).

Module TheRationals : TheRationalsSig.
  Definition A : Type := T.
  Definition Q : @set A := X.
  Definition plus  := _ : Plus T.
  Definition mult  := _ : Mult T.
  Definition zero  := _ : Zero T.
  Definition one   := _ : One T.
  Definition negate:= _ : Negate T.
  Definition inv   := _ : Inv T.
  Definition equiv := _ : Equiv T.
  Definition uneq  := _ : UnEq T.
  Definition U     := _ : RationalsToField X.
  Definition rationals := _ : Rationals X.
  Definition le := _ : Le X.
  Definition lt := _ : Lt X.
  Definition order := _ : FullPseudoSemiRingOrder X.
End TheRationals.

Notation the_rationals := TheRationals.Q.

Instance: FullLatticeOrder the_rationals := dec_full_lattice_order.
Instance: SemiRingLatticeOrder the_rationals := dec_semiring_lattice_order.

Add Field the_rationals : (stdlib_field_dec_theory the_rationals).
