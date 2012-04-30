Require Import
  abstract_algebra theory.sub_strong_setoids theory.strong_groups theory.rings.

(*
Local Open Scope grp_scope. (* notation for inverse *)
Local Notation e := mon_unit.
*)

Section semirngs.
  Context `{SemiRng (A:=A) (R:=R)} Aue `{!StrongSetoid A (Aue:=Aue)}.
  Context `{!SubStrongSetoid_Binary_Morphism (+)   R R R}.
  Context `{!SubStrongSetoid_Binary_Morphism (.*.) R R R}.

  Global Instance: NonZeroProduct R.
  Proof. intros x ? y ? ?. split; (split; [apply _|]); [
      apply (strong_extensionality (.* y) _ _); rewrite (mult_0_l _)
    | apply (strong_extensionality (x *.) _ _); rewrite (mult_0_r _) ];
    firstorder.
  Qed.

End semirngs.


Section rngs.
  Context `{Rng (A:=A) (R:=R)} Aue `{!StrongSetoid A (Aue:=Aue)}.
  Context `{!SubStrongSetoid_Binary_Morphism (+)   R R R}.
  Context `{!SubStrongSetoid_Binary_Morphism (.*.) R R R}.

  Global Instance: StrongInjective (-) R R := _ : StrongInjective negate_is_inv R R.

End rngs.

