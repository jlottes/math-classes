Require Import
  abstract_algebra interfaces.reals interfaces.complex_numbers
  the_reals realpair_complexes
  stdlib_ring stdlib_field.

Module Type TheComplexNumbersSig.
  Parameter A : Type.
  Parameter C : @set A.
  Parameter plus : Plus A.
  Parameter mult : Mult A.
  Parameter zero : Zero A.
  Parameter one  : One A.
  Parameter negate : Negate A.
  Parameter inv  : Inv A.
  Parameter equiv: Equiv A.
  Parameter uneq : UnEq A.
  Parameter lt   : Lt A.
  Parameter le   : Le A.
  Parameter i    : ImaginaryUnit A.
  Parameter CR   : ComplexReals C.
  Parameter UR   : ToReals (complex_reals C).
  Parameter UC   : ComplexToRing C.
  Parameter complex_numbers : @ComplexNumbers A C i CR plus mult zero one negate inv equiv uneq lt le UR UC.
End TheComplexNumbersSig.

Local Notation XC := (ComplexPair the_reals).

Module TheComplexNumbers : TheComplexNumbersSig.
  Definition A : Type := elt_type XC.
  Definition C : @set A := XC.
  Instance plus   : Plus   XC := cp_plus.
  Instance mult   : Mult   XC := cp_mult.
  Instance zero   : Zero   XC := cp_zero.
  Instance one    : One    XC := cp_one.
  Instance negate : Negate XC := cp_negate.
  Instance inv    : Inv    XC := cp_inv.
  Instance equiv  : Equiv  XC := cp_equiv.
  Instance uneq   : UnEq   XC := cp_uneq.
  Instance le     : Le     XC := cp_le.
  Instance lt     : Lt     XC := cp_lt.
  Instance i      : ImaginaryUnit XC := cp_unit.
  Instance CR     : ComplexReals XC := _.
  Instance UR : ToReals (complex_reals XC) := cp_to_reals.
  Instance UC : ComplexToRing XC := cp_to_ring.
  Instance complex_numbers : ComplexNumbers XC := cp_complex_numbers.
End TheComplexNumbers.

Notation the_complex_numbers := TheComplexNumbers.C.

Add Ring the_complex_numbers : (stdlib_ring_theory the_complex_numbers).
Add Field the_complex_numbers' : (stdlib_field_theory the_complex_numbers).

