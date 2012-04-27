Require Import
  abstract_algebra theory.sub_strong_setoids theory.strong_groups theory.rings.

(*
Local Open Scope grp_scope. (* notation for inverse *)
Local Notation e := mon_unit.
*)

Section contents.
  Context `{Rng (A:=A) (R:=R)} Aue `{!StrongSetoid A (Aue:=Aue)}.
  Context `{!SubStrongSetoid_Binary_Morphism (+)   R R R}.
  Context `{!SubStrongSetoid_Binary_Morphism (.*.) R R R}.

  Global Instance: StrongInjective (-) R R := _ : StrongInjective negate_is_inv R R.

End contents.

