Require Import
  abstract_algebra interfaces.integers interfaces.orders
  theory.rings theory.integers orders.integers
  orders.lattices orders.minmax lattice_ordered_rings
  the_naturals natpair_integers
  stdlib_ring.

Module Type TheIntegersSig.
  Parameter A : Type.
  Parameter Z : @set A.
  Parameter plus : Plus A.
  Parameter mult : Mult A.
  Parameter zero : Zero A.
  Parameter one  : One A.
  Parameter negate : Negate A.
  Parameter equiv: Equiv A.
  Parameter U    : IntegersToRing Z.
  Parameter integers : @Integers A plus mult zero one negate equiv Z U.
  Parameter uneq : UnEq A.
  Parameter denial_inequality : DenialInequality Z.
  Parameter le   : Le A.
  Parameter lt   : Lt A.
  Parameter order : FullPseudoSemiRingOrder Z.
End TheIntegersSig.

Local Notation N := the_naturals.
Local Notation T := (SRpairT N).
Local Notation X := (SRpair N).

Module TheIntegers : TheIntegersSig.
  Definition A : Type := T.
  Definition Z : @set A := X.
  Definition plus  := _ : Plus T.
  Definition mult  := _ : Mult T.
  Definition zero  := _ : Zero T.
  Definition one   := _ : One T.
  Definition negate:= _ : Negate T.
  Definition equiv := _ : Equiv T.
  Definition U     := _ : IntegersToRing X.
  Definition integers := _ : Integers X.
  Definition uneq  := _ : UnEq T.
  Definition denial_inequality := _ : DenialInequality X.
  Definition le := _ : Le X.
  Definition lt := _ : Lt X.
  Definition order : @FullPseudoSemiRingOrder A equiv uneq plus mult zero one le lt Z
    := _ : FullPseudoSemiRingOrder X.
End TheIntegers.

Notation the_integers := TheIntegers.Z.

Instance: StrongSetoid the_integers := strong_setoids.dec_strong_setoid.
Instance: FullLatticeOrder the_integers := dec_full_lattice_order.
Instance: SemiRingLatticeOrder the_integers := dec_semiring_lattice_order.

Add Ring the_integers : (stdlib_ring_theory the_integers).

Hint Extern 5 (?x * ?y ∊ the_integers ₀) => eapply @dec_mult_nonzero: typeclass_instances.
