Require Import canonical_names.

Section restrict_rel.
  Context `(S:A → Prop) (R:relation A).

  Lemma restrict_rel_sub: subrelation (S,R)%signature R.
  Proof. intros ??[? E]. exact E. Qed.

  Lemma restrict_rel_refl `{!Reflexive R} x : S x → Proper (S,R) x.
  Proof. intro Sx. split. split; exact Sx. reflexivity. Qed.

  Lemma restrict_rel_sym `{!Symmetric R} : Symmetric (S,R)%signature.
  Proof. intros ? ? [[??]?]. split. now split. now symmetry. Qed.

  Lemma restrict_rel_trans `{!Transitive R} : Transitive (S,R)%signature.
  Proof. intros ? ? ? [[??]?] [[??]?]. split. now split. auto_trans. Qed.

End restrict_rel.

Hint Extern 15 (@subrelation _ (@restrict_rel _ _ ?R) ?R) => eapply @restrict_rel_sub : typeclass_instances.
Hint Extern 15 (@Symmetric  _ (@restrict_rel _ _ _)) => eapply @restrict_rel_sym   : typeclass_instances.
Hint Extern 15 (@Transitive _ (@restrict_rel _ _ _)) => eapply @restrict_rel_trans : typeclass_instances.

Lemma restrict_rel_per `(S:A → Prop) (R:relation A) `{!RelationClasses.PER R}
  : RelationClasses.PER (S, R)%signature.
Proof. split; apply _. Qed.

Lemma restrict_sub_sub `(S:A → Prop) (R1 R2:relation A) {sub:subrelation R1 R2}
  : subrelation (S,R1)%signature (S,R2)%signature.
Proof. intros ?? [[??]?]. split. split; assumption. now apply sub. Qed.

Lemma restrict_antisym `(S:A → Prop) (eq le:relation A) `{!AntiSymmetric eq le}
  : AntiSymmetric (S,eq)%signature (S,le)%signature.
Proof. intros ?? [[??]?] [[??]?]. split. split; assumption. now apply (antisymmetry le). Qed.

Hint Extern 15 (@RelationClasses.PER _ (@restrict_rel _ _ _)) => eapply @restrict_rel_per : typeclass_instances.
Hint Extern 15 (@subrelation   _ (@restrict_rel _ ?S _) (@restrict_rel _ ?S _)) => eapply @restrict_sub_sub : typeclass_instances.
Hint Extern 15 (@AntiSymmetric _ (@restrict_rel _ ?S _) (@restrict_rel _ ?S _)) => eapply @restrict_antisym : typeclass_instances.

