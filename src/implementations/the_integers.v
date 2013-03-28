Require Import
  abstract_algebra interfaces.integers interfaces.orders
  theory.integers orders.integers
  the_naturals natpair_integers.

Module Type TheIntegersSig.
  Parameter A : Type.
  Parameter Z : @Subset A.
  Parameter plus : Plus A.
  Parameter mult : Mult A.
  Parameter zero : Zero A.
  Parameter one  : One A.
  Parameter negate : Negate A.
  Parameter equiv: Equiv A.
  Parameter U    : IntegersToRing Z.
  Parameter integers : @Integers A plus mult zero one negate equiv Z U.
  Parameter uneq : UnEq A.
  Parameter std_uneq : StandardUnEq Z.
  Parameter le   : Le A.
  Parameter lt   : Lt A.
  Parameter order : FullPseudoSemiRingOrder Z.
End TheIntegersSig.

Local Notation N := the_naturals.
Local Notation T := (SRpairT N).
Local Notation X := (SRpair N).

Module TheIntegers : TheIntegersSig.
  Definition A : Type := T.
  Definition Z : @Subset A := X.
  Definition plus  := _ : Plus T.
  Definition mult  := _ : Mult T.
  Definition zero  := _ : Zero T.
  Definition one   := _ : One T.
  Definition negate:= _ : Negate T.
  Definition equiv := _ : Equiv T.
  Definition U     := _ : IntegersToRing X.
  Definition integers := _ : Integers X.
  Definition uneq  := _ : UnEq T.
  Definition std_uneq := _ : StandardUnEq X.
  Definition le := _ : Le X.
  Definition lt := _ : Lt X.
  Definition order : FullPseudoSemiRingOrder Z := _ : FullPseudoSemiRingOrder X.
End TheIntegers.

Notation the_integers := TheIntegers.Z.

Instance: StrongSetoid the_integers := strong_setoids.dec_strong_setoid.

