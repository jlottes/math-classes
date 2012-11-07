Require Import
  BigN interfaces.naturals abstract_algebra.
Require Export
  NType_naturals.

Module BigN_Integers := NType_Integers BigN.

Hint Extern 10 (@Subset bigN) => eexact (every bigN) : typeclass_instances.