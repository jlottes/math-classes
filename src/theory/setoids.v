Require Import
  abstract_algebra.

Instance: ∀ `{Setoid A}, Find_Proper_Symmetric (=). Proof. intros. red. apply _. Qed.
Instance: ∀ `{Setoid A}, Find_Proper_Reflexive (=).
Proof. intros ??? x. red. reflexivity. Qed.

Lemma equiv_proper : Find_Proper_Signature (@equiv) 0
  (∀ A Ae `{!Setoid A}, Proper ((=)==>(=)==>impl) (@equiv A Ae)).
Proof. intros ???. intros ?? E1 ?? E2 P. now rewrite <-E1, <-E2. Qed.
Hint Extern 0 (Find_Proper_Signature (@equiv) 0 _) => eexact equiv_proper : typeclass_instances.

Lemma ext_equiv_refl `{Setoid_Morphism A B f} : f = f.
Proof. intros ?? E. pose proof (setoidmor_b f). now rewrite E. Qed.

Instance ext_equiv_trans `{Equiv A} `{Equiv B} `{Reflexive (A:=A) (=)} `{Transitive (A:=B) (=)} : Transitive (_ : Equiv (A → B)).
Proof. intros ? y ???? w ?. transitivity (y w); firstorder. Qed.

Instance ext_equiv_sym `{Equiv A} `{Equiv B} `{Symmetric (A:=A) (=)} `{Symmetric (A:=B) (=)}: Symmetric (A:=A→B) (=).
Proof. firstorder. Qed.

Lemma ext_equiv_applied `{Setoid A} `{Equiv B} {f g : A → B} :
  f = g → ∀ x, f x = g x.
Proof. intros E x. now apply E. Qed.

Lemma ext_equiv_applied_iff `{Equiv A} `{Equiv B} `{!Setoid_Morphism (f : A → B)}
  `{!Setoid_Morphism (g : A → B)} : f = g ↔ ∀ x, f x = g x.
Proof.
  pose proof (setoidmor_a f). pose proof (setoidmor_b f).
  split; intros E1.
   now apply ext_equiv_applied.
  intros x y E2. now rewrite E2.
Qed.

Lemma morphism_ne `{Equiv A} `{Equiv B} (f : A → B) `{!Setoid_Morphism f} x y :
  f x ≠ f y → x ≠ y.
Proof. intros E1 E2. apply E1. now apply sm_proper. Qed.

Instance: Equiv Prop := iff.
Instance: Setoid Prop := {}.

Lemma projected_setoid `{Setoid B} `{Equiv A} (f : A → B)
  (eq_correct : ∀ x y, x = y ↔ f x = f y) : Setoid A.
Proof.
 constructor; repeat intro; apply eq_correct.
   reflexivity.
  symmetry; now apply eq_correct.
 transitivity (f y); now apply eq_correct.
Qed.

Instance id_morphism `{Setoid A} : Setoid_Morphism (@id A) := {}.

Lemma compose_setoid_morphism `{Equiv A} `{Equiv B} `{Equiv C} (f : A → B) (g : B → C) :
  Setoid_Morphism f → Setoid_Morphism g → Setoid_Morphism (g ∘ f).
Proof. firstorder. Qed.
Hint Extern 4 (Setoid_Morphism (_ ∘ _)) => class_apply @compose_setoid_morphism : typeclass_instances.

Class Setoid_Fun `{Equiv A} `{Equiv B} (f:A → B) : Prop :=
  { setoidfun_a : Setoid A
  ; setoidfun_b : Setoid B
  }.

Instance setoid_fun1 `{Setoid A} `{Setoid B} (f:A → B) : Setoid_Fun f := {}.
Instance setoid_fun2 `{Equiv A} `{Equiv B} (f:A → B) `{!Setoid_Morphism f}
  : ∀ (g:A → B), Setoid_Fun g.
Proof. intro. split. exact (setoidmor_a f). exact (setoidmor_b f). Qed.

Lemma morphism_refl `{Equiv A} `{Equiv B} (f:A → B) `{!Setoid_Morphism f}
  : Proper (Setoid_Fun,=) f.
Proof. split. split; apply _. exact ext_equiv_refl. Qed.

Instance morphism_proper `{Equiv A} `{Equiv B}
  : Proper ((Setoid_Fun,=) ==> impl) (@Setoid_Morphism A B _ _).
Proof. intros f g [[??] E1] ?. pose proof (setoidmor_a f). pose proof (setoidmor_b f).
  split; try apply _. intros x y E2.
  now rewrite <-!(ext_equiv_applied E1 _), E2.
Qed.
