Require Import
  abstract_algebra theory.strong_setoids theory.strong_groups theory.rings.

Lemma NonZero_strong_setoid         `{Zero A} `{StrongSetoid A (S:=R)} : StrongSetoid (R ₀). Proof. now rewrite (_:R ₀ ⊆ R). Qed.
Lemma NonNeg_strong_setoid  `{Le A} `{Zero A} `{StrongSetoid A (S:=R)} : StrongSetoid R⁺.    Proof. now rewrite (_:R⁺  ⊆ R). Qed.
Lemma NonPos_strong_setoid  `{Le A} `{Zero A} `{StrongSetoid A (S:=R)} : StrongSetoid R⁻.    Proof. now rewrite (_:R⁻  ⊆ R). Qed.
Lemma Pos_strong_setoid     `{Lt A} `{Zero A} `{StrongSetoid A (S:=R)} : StrongSetoid R₊.    Proof. now rewrite (_:R₊  ⊆ R). Qed.
Lemma Neg_strong_setoid     `{Lt A} `{Zero A} `{StrongSetoid A (S:=R)} : StrongSetoid R₋.    Proof. now rewrite (_:R₋  ⊆ R). Qed.

Hint Extern 2 (StrongSetoid (_ ₀)) => eapply @NonZero_strong_setoid : typeclass_instances. 
Hint Extern 2 (StrongSetoid _⁺   ) => eapply @NonNeg_strong_setoid  : typeclass_instances. 
Hint Extern 2 (StrongSetoid _₊   ) => eapply @Pos_strong_setoid     : typeclass_instances. 
Hint Extern 2 (StrongSetoid _⁻   ) => eapply @NonPos_strong_setoid  : typeclass_instances. 
Hint Extern 2 (StrongSetoid _₋   ) => eapply @Neg_strong_setoid     : typeclass_instances. 

(*
Local Open Scope grp_scope. (* notation for inverse *)
Local Notation e := mon_unit.
*)

Section semirngs.
  Context `{SemiRng A (R:=R)} `{UnEq A} `{!StrongSetoid R}.
  Context `{!StrongSetoid_Binary_Morphism R R R (+)}.
  Context `{!StrongSetoid_Binary_Morphism R R R (.*.)}.

  Global Instance: NonZeroProduct R.
  Proof. intros x ? y ? ?. split; (split; [apply _|]); [
      apply (strong_extensionality (.* y) _ _); rewrite_on R -> (mult_0_l y)
    | apply (strong_extensionality (x *.) _ _); rewrite_on R -> (mult_0_r x) ];
    firstorder.
  Qed.

End semirngs.


Section rngs.
  Context `{Rng A (R:=R)} `{UnEq A} `{!StrongSetoid R}.
  Context `{!StrongSetoid_Binary_Morphism R R R (+)}.
  Context `{!StrongSetoid_Binary_Morphism R R R (.*.)}.

  Global Instance: StrongInjective R R (-) := _ : StrongInjective R R negate_is_inv.

End rngs.

