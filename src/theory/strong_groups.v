Require Import
  abstract_algebra theory.strong_setoids.
Require Export theory.groups.

Local Open Scope grp_scope. (* notation for inverse *)
Local Notation e := mon_unit.

Section contents.
  Context `{Group A (G:=G)} `{UnEq A} `{!StrongSetoid G}.
  Context `{!StrongSetoid_Binary_Morphism G G G (&)}.

  Definition f := (&).
  Instance: StrongSetoid_Binary_Morphism G G G f.
  Proof. unfold f. apply _. Qed.

  Global Instance: StrongInjective G G (⁻¹).
  Proof. split.
  + intros x ? y ? E.
    apply (strong_extensionality (& x) _ _).
    rewrite_on G -> (left_inverse (&) x).
    apply (strong_extensionality (y &) _ _).
    rewrite_on G -> (right_identity (&) y), (associativity (&) y y⁻¹ x).
    rewrite_on G -> (right_inverse (&) y), (left_identity (&) x).
    subsymmetry.
  + split; try apply _.
    intros x ? y ? E.
    apply (strong_extensionality (& x⁻¹) x y).
    rewrite_on G -> (right_inverse (&) x).
    apply (strong_extensionality (y⁻¹ &) _ _).
    rewrite_on G -> (right_identity (&) y⁻¹), (associativity (&) y⁻¹ y x⁻¹).
    rewrite_on G -> (left_inverse (&) y), (left_identity (&) x⁻¹).
    subsymmetry.
  Qed.

End contents.

