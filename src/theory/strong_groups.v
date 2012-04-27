Require Import
  abstract_algebra theory.sub_strong_setoids.
Require Export theory.groups.

Local Open Scope grp_scope. (* notation for inverse *)
Local Notation e := mon_unit.

Section contents.
  Context `{Group (A:=A) (G:=G)} Aue `{!StrongSetoid A (Aue:=Aue)}.
  Context `{!SubStrongSetoid_Binary_Morphism (&) G G G}.

  Global Instance: StrongInjective (⁻¹) G G.
  Proof. split.
  + intros x ? y ? E.
    apply (strong_extensionality (& x) x⁻¹ y⁻¹).
    rewrite (left_inverse x).
    apply (strong_extensionality (y &) e (y⁻¹ & x)).
    rewrite (right_identity y).
    rewrite (associativity y y⁻¹ x).
    rewrite_on G -> (right_inverse y).
    rewrite (left_identity x).
    now symmetry.
  + split; try (split; apply _). intros ??; apply _.
    intros x ? y ? E.
    apply (strong_extensionality (& x⁻¹) x y).
    rewrite (right_inverse x).
    apply (strong_extensionality (y⁻¹ &) e (y & x⁻¹)).
    rewrite (right_identity y⁻¹).
    rewrite (associativity y⁻¹ y x⁻¹).
    rewrite_on G -> (left_inverse y).
    rewrite (left_identity x⁻¹).
    now symmetry.
  Qed.

End contents.

