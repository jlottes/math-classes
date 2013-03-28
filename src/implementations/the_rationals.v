Require Import
  abstract_algebra interfaces.rationals interfaces.orders
  theory.rationals orders.rationals orders.abs
  the_integers intfrac_rationals.

Module Type TheRationalsSig.
  Parameter A : Type.
  Parameter Q : @Subset A.
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
  Parameter abs : Abs A.
  Parameter dec_abs : DecAbs Q.
End TheRationalsSig.

Local Notation Z := the_integers.
Local Notation T := (FracPair Z).
Local Notation X := (Frac Z).

Module TheRationals : TheRationalsSig.
  Definition A : Type := T.
  Definition Q : @Subset A := X.
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
  Definition abs : Abs T := default_abs.
  Definition dec_abs := _ : DecAbs X.
End TheRationals.

Notation the_rationals := TheRationals.Q.
