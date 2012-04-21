Require Import canonical_names.

Section restrict_rel.
  Context `(S:A → Prop) (R:relation A).

  Definition restrict_rel: relation A := λ x y, (S x ∧ S y) ∧ R x y .

  Lemma restrict_rel_sub: subrelation (restrict_rel) R.
  Proof. intros ??[? E]. exact E. Qed.

  Lemma restrict_rel_refl `{!Reflexive R} x : S x → Proper restrict_rel x.
  Proof. intro Sx. split. split; exact Sx. reflexivity. Qed.

  Lemma restrict_rel_sym `{!Symmetric R} : Symmetric restrict_rel.
  Proof. intros ? ? [[??]?]. split. now split. now symmetry. Qed.

  Lemma restrict_rel_trans `{!Transitive R} : Transitive restrict_rel.
  Proof. intros ? ? ? [[??]?] [[??]?]. split. now split. auto_trans. Qed.

End restrict_rel.

Hint Extern 0 (@subrelation _ (@restrict_rel _ _ ?R) ?R) => eapply @restrict_rel_sub : typeclass_instances.
Hint Extern 0 (@Symmetric  _ (@restrict_rel _ _ _)) => eapply @restrict_rel_sym   : typeclass_instances.
Hint Extern 0 (@Transitive _ (@restrict_rel _ _ _)) => eapply @restrict_rel_trans : typeclass_instances.

Notation " ( S , R ) " := (restrict_rel S (R%signature)) : signature_scope.
Notation " ( S ,=) " := (restrict_rel S (=)) : signature_scope.

Lemma restrict_rel_per `(S:A → Prop) (R:relation A) `{!RelationClasses.PER R}
  : RelationClasses.PER (S, R)%signature.
Proof. split; apply _. Qed.

Lemma restrict_sub_sub `(S:A → Prop) (R1 R2:relation A) {sub:subrelation R1 R2}
  : subrelation (S,R1)%signature (S,R2)%signature.
Proof. intros ?? [[??]?]. split. split; assumption. now apply sub. Qed.

Lemma restrict_antisym `(S:A → Prop) (eq le:relation A) `{!AntiSymmetric eq le}
  : AntiSymmetric (S,eq)%signature (S,le)%signature.
Proof. intros ?? [[??]?] [[??]?]. split. split; assumption. now apply (antisymmetry le). Qed.

Hint Extern 0 (@RelationClasses.PER _ (@restrict_rel _ _ _)) => eapply @restrict_rel_per : typeclass_instances.
Hint Extern 0 (@subrelation   _ (@restrict_rel _ ?S _) (@restrict_rel _ ?S _)) => eapply @restrict_sub_sub : typeclass_instances.
Hint Extern 0 (@AntiSymmetric _ (@restrict_rel _ ?S _) (@restrict_rel _ ?S _)) => eapply @restrict_antisym : typeclass_instances.

