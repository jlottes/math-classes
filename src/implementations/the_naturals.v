Require Import
  abstract_algebra interfaces.naturals interfaces.orders
  theory.rings theory.naturals orders.naturals
  orders.lattices orders.minmax lattice_ordered_rings
  peano_naturals.

Module Type TheNaturalsSig.
  Parameter A : Type.
  Parameter N : @set A.
  Parameter plus : Plus A.
  Parameter mult : Mult A.
  Parameter zero : Zero A.
  Parameter one  : One A.
  Parameter equiv: Equiv A.
  Parameter U    : NaturalsToSemiRing N.
  Parameter naturals : @Naturals A N plus mult zero one equiv U.
  Parameter uneq : UnEq A.
  Parameter denial_inequality : DenialInequality N.
  Parameter le   : Le A.
  Parameter lt   : Lt A.
  Parameter order : FullPseudoSemiRingOrder N.
End TheNaturalsSig.

Local Notation T := nat.
Local Notation X := (every nat).

Module TheNaturals : TheNaturalsSig.
  Definition A : Type := T.
  Definition N : @set A := X.
  Definition plus  := _ : Plus T.
  Definition mult  := _ : Mult T.
  Definition zero  := _ : Zero T.
  Definition one   := _ : One T.
  Definition equiv := _ : Equiv T.
  Definition U     := _ : NaturalsToSemiRing X.
  Definition naturals := _ : Naturals X.
  Definition uneq  := _ : UnEq T.
  Definition denial_inequality := _ : DenialInequality X.
  Definition le := _ : Le T.
  Definition lt := _ : Lt T.
  Definition order := _ : FullPseudoSemiRingOrder X.
End TheNaturals.

Notation the_naturals := TheNaturals.N.

Instance: StrongSetoid the_naturals := strong_setoids.dec_strong_setoid.

Instance: FullLatticeOrder the_naturals := dec_full_lattice_order.
Instance: SemiRingLatticeOrder the_naturals := dec_semiring_lattice_order.

Hint Extern 5 (?x * ?y ∊ the_naturals ₀) => eapply @dec_mult_nonzero: typeclass_instances.
