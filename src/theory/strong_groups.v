Require Import
  abstract_algebra theory.strong_setoids.
Require Export theory.groups.

Local Open Scope grp_scope. (* notation for inverse *)
Local Notation e := mon_unit.

Lemma strong_sg_op_proper: Find_Proper_Signature (@StrongSemiGroupOp) 0
  (∀ A op Ae Aue, Proper ((=)==>impl) (@StrongSemiGroupOp A op Ae Aue)).
Proof. structure_proper. Qed.
Hint Extern 0 (Find_Proper_Signature (@StrongSemiGroupOp) 0 _) => eexact strong_sg_op_proper : typeclass_instances.

Section contents.
  Context `{Group (G:=G)} {Aue:UnEq _} `{!StrongSemiGroupOp G}.

  Instance grp_inv_strong_inj: StrongInjective G G (⁻¹).
  Proof. split.
  + intros x ? y ? E.
    apply (strong_extensionality (& x)).
    rewrite_on G -> (left_inverse (&) x).
    apply (strong_extensionality (y &)).
    rewrite_on G -> (right_identity (&) y), (associativity (&) y y⁻¹ x).
    rewrite_on G -> (right_inverse (&) y), (left_identity (&) x).
    subsymmetry.
  + split; try apply _. rewrite strong_ext_equiv_1.
    intros x ? y ? E.
    apply (strong_extensionality (& x⁻¹)).
    rewrite_on G -> (right_inverse (&) x).
    apply (strong_extensionality (y⁻¹ &)).
    rewrite_on G -> (right_identity (&) y⁻¹), (associativity (&) y⁻¹ y x⁻¹).
    rewrite_on G -> (left_inverse (&) y), (left_identity (&) x⁻¹).
    subsymmetry.
  Qed.

  Instance grp_inv_strong: Strong_Morphism G G (⁻¹).
  Proof strong_injective_mor _.

  Instance grp_strong_left_cancel z `{z ∊ G} : StrongLeftCancellation (&) z G.
  Proof. intros x ? y ? E. apply (strong_extensionality (z⁻¹ &)).
    now rewrite 2!(G $ associativity (&) _ _ _), (G $ inverse_l z), !(G $ left_identity (&) _).
  Qed.

  Instance grp_strong_right_cancel z `{z ∊ G} : StrongRightCancellation (&) z G.
  Proof. intros x ? y ? E. apply (strong_extensionality (& z⁻¹)).
    now rewrite <- 2!(G $ associativity (&) _ _ _), (G $ inverse_r z), !(G $ right_identity (&) _).
  Qed.

End contents.

Hint Extern 5 (StrongInjective _ _ (⁻¹)) => class_apply @grp_inv_strong_inj : typeclass_instances.
Hint Extern 5 (Strong_Morphism _ _ (⁻¹)) => class_apply @grp_inv_strong : typeclass_instances.
Hint Extern 5 (StrongLeftCancellation  (&) _ _) => class_apply @grp_strong_left_cancel  : typeclass_instances.
Hint Extern 5 (StrongRightCancellation (&) _ _) => class_apply @grp_strong_right_cancel : typeclass_instances.
