Require Import
  abstract_algebra interfaces.naturals interfaces.orders
  theory.naturals orders.naturals
  peano_naturals.

Module Type TheNaturalsSig.
  Parameter A : Type.
  Parameter N : @Subset A.
  Parameter plus : Plus A.
  Parameter mult : Mult A.
  Parameter zero : Zero A.
  Parameter one  : One A.
  Parameter equiv: Equiv A.
  Parameter U    : NaturalsToSemiRing N.
  Parameter naturals : @Naturals A plus mult zero one equiv N U.
  Parameter uneq : UnEq A.
  Parameter std_uneq : StandardUnEq N.
  Parameter le   : Le A.
  Parameter lt   : Lt A.
  Parameter order : FullPseudoSemiRingOrder N.
End TheNaturalsSig.

Local Notation T := nat.
Local Notation X := (every nat).

Module TheNaturals : TheNaturalsSig.
  Definition A : Type := T.
  Definition N : @Subset A := X.
  Definition plus  := _ : Plus T.
  Definition mult  := _ : Mult T.
  Definition zero  := _ : Zero T.
  Definition one   := _ : One T.
  Definition equiv := _ : Equiv T.
  Definition U     := _ : NaturalsToSemiRing X.
  Definition naturals := _ : Naturals X.
  Definition uneq  := _ : UnEq T.
  Definition std_uneq := _ : StandardUnEq X.
  Definition le := _ : Le T.
  Definition lt := _ : Lt T.
  Definition order := _ : FullPseudoSemiRingOrder X.
End TheNaturals.

Notation the_naturals := TheNaturals.N.

Instance: StrongSetoid the_naturals := strong_setoids.dec_strong_setoid.
