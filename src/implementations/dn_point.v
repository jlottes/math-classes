Require Import
  abstract_algebra theory.setoids.

Local Hint Extern 2 (Setoid (every _)) => red : typeclass_instances.
Local Hint Extern 2 (Morphism (every _ ⇒ every _) _) => eapply @every_Morphism : typeclass_instances.
Local Hint Extern 2 (Morphism (every _ ⇒ every _ ⇒ every _) _) => eapply @every_binary_Morphism : typeclass_instances.

Lemma LEM_false (P : Prop) : ((P ∨ ¬P) → False) → False .
Proof. tauto. Qed.

Lemma LEM_negation (P Q : Prop) : ((P ∨ ¬P) → ¬Q) → ¬Q .
Proof. tauto. Qed.

Lemma DN_negation (P Q : Prop) : ¬¬P → (P → ¬Q) → ¬Q .
Proof. tauto. Qed.

Ltac DN_tac1 :=
  repeat match goal with
  | H : ¬¬ ?P |- False => destruct H; intro H
  | H : ¬¬ ?P |- ¬ ?Q => apply (DN_negation P Q H); clear H; intro H
  end.

Ltac DN_tac := DN_tac1; let P := fresh "P" in intro P; destruct P.

Definition IsPoint `(X:set) `{Equiv _} : set → Prop := λ U,
   U ⊆ X ∧ ¬(∃ `{x ∊ U} `{y ∊ U}, ¬ x = y) ∧ ¬¬Inhabited U .
Definition Point `(X:set) `{Equiv _} := { U | IsPoint X U }.

Instance point_equiv `(X:set) `{Equiv _} : Equiv (Point X) := λ U V, ¬(∃ `{x ∊ (` U)} `{y ∊ (` V)}, ¬ x = y).

Lemma point_equivalence `(X:set) `{Setoid _ (S:=X)} : EquivalenceT (@equiv (Point X) _).
Proof. unfold equiv, point_equiv. split.
+ now intros [?[?[P ?]]].
+ intros [?[?[P1 ?]]] [?[?[P2 ?]]]. simpl. intros P [a[?[b[? E]]]]. destruct P.
  exists_sub b a. DN_tac1. contradict E. subsymmetry.
+ intros [x[?[P1 ?]]] [y[?[P2 PI]]] [z[?[P3 ?]]]. simpl.
  intros E1 E2 [a[?[b[? E]]]]. DN_tac1.
  destruct (inhabited y) as [c ?].
  destruct E1. exists_sub a c. intro E1.
  destruct E2. exists_sub c b. contradict E.
  subtransitivity c.
Qed.

Hint Extern 2 (EquivalenceT (@equiv _ (point_equiv _))) => eapply @point_equivalence : typeclass_instances.
Hint Extern 2 (Equivalence _ (@equiv _ (point_equiv _))) => eapply @every_Equivalence : typeclass_instances.
Hint Extern 2 (@Setoid (Point _) _ _) => red : typeclass_instances.

Instance point_uneq `(X:set) `{Equiv _} : UnEq (Point X) := default_uneq.
Instance point_denial_inequality `(X:set) `{Equiv _} : DenialInequality (every (Point X)).
Proof. unfold point_uneq. apply _. Qed.

Section point.
  Context `{Setoid (S:=Y)} p {pf:p ∊ Y}.

  Definition point_set : set := (λ y, y ∊ Y ∧ ¬¬y = p).

  Instance point_el : p ∊ point_set.
  Proof. split. apply _. now DN_tac. Qed.

  Lemma point_obl : IsPoint Y point_set .
  Proof. split. 2: split.
  + apply subsetoid_alt. apply _.
    * intros ?? E. unfold_sigs. intros [? E2]. split. apply _. now rewrite <-(_ $ E).
    * now intros ?[??].
  + intros [x [[? Ex] [y[[? Ey] E]]]]. DN_tac1. destruct E. subtransitivity p. subsymmetry.
  + DN_tac. exists p. apply _.
  Qed.

  Definition point : Point Y := exist _ point_set point_obl.

End point.

Section map.
  Context `{Setoid (S:=X)} `{Setoid (S:=Y)}.
  Context (f:X ⇀ Y) `{!Morphism (X ⇒ Y) f}.

  Definition point_map_set (S : set) : set := λ y, y ∊ Y ∧ (∀ `{x ∊ S}, ¬¬ f x = y).

  Instance point_map_el (S:set) `{S ⊆ X} (P:¬(∃ `{x ∊ S} `{y ∊ S}, ¬ x = y))
    x `{x ∊ S} : f x ∊ point_map_set S.
  Proof. split. apply _. intros x2 ? E.
    destruct P. exists_sub x x2. intro Ex.
    destruct E. now rewrite (X $ Ex).
  Qed.

  Lemma point_map_obl (S : Point X) : IsPoint Y (point_map_set (` S)).
  Proof. destruct S as [S[?[P1 P2]]]. simpl. unfold point_map_set. split. 2: split.
  + apply subsetoid_alt. apply _.
    * intros ?? E. unfold_sigs. intros [? P]. red. split. apply _.
      intros a ?. pose proof (P a _). now rewrite <-(_ $ E).
    * now intros ? [??].
  + intros [y1[[? Py1] [y2[[? Py2] E]]]]. DN_tac1.
    destruct (inhabited S) as [x ?].
    pose proof (Py1 x _). pose proof (Py2 x _).
    DN_tac1. destruct E. subtransitivity (f x). subsymmetry.
  + DN_tac1. destruct (inhabited S) as [x ?]. DN_tac.
    exists (f x). exact (point_map_el S P1 x).
  Qed.

  Definition point_map : Point X → Point Y := λ S, exist _ _ (point_map_obl S) .

  Instance point_map_proper : Proper ((=)==>(=)) point_map.
  Proof. intros [S1[?[P1 ?]]] [S2[?[P2 ?]]].
    unfold equiv, point_equiv. simpl. intro E. DN_tac1.
    intros [y1[[? Py1] [y2[[? Py2] Ey]]]].
    destruct (inhabited S1) as [x1 ?].
    destruct (inhabited S2) as [x2 ?].
    destruct E. exists_sub x1 x2. intro Ex.
    assert (x1 ∊ S2) by now rewrite (_ $ Ex).
    pose proof (Py1 x1 _). pose proof (Py2 x1 _).
    DN_tac1. destruct Ey. subtransitivity (f x1). subsymmetry.
  Qed.
End map.

Hint Extern 2 (?f ?x ∊ point_map_set ?f _) => eapply @point_map_el;trivial : typeclass_instances.
Hint Extern 2 (Proper _ (point_map _)) => eapply @point_map_proper : typeclass_instances.

Section functor.
  Context `{Setoid (S:=X)}.

  Lemma point_map_id : ((=)==>(=))%signature (point_map (id:X ⇀ X)) id.
  Proof. intros [S1[?[P1 ?]]] [S2[?[P2 ?]]].
    unfold equiv, point_equiv. simpl. intro E. DN_tac1.
    intros [y1[[? Py1] [x2[? Ey]]]].
    destruct (inhabited S1) as [x1 ?].
    destruct E. exists_sub x1 x2. intro Ex.
    assert (x2 ∊ S1) by now rewrite <-(_ $ Ex).
    pose proof (Py1 x2 _).
    DN_tac1. destruct Ey. subsymmetry.
  Qed.

  Context `{Setoid (S:=Y)} `{Setoid (S:=Z)}.
  Context (f:X ⇀ Y) `{!Morphism (X ⇒ Y) f}.
  Context (g:Y ⇀ Z) `{!Morphism (Y ⇒ Z) g}.

  Lemma point_map_compose : ((=)==>(=))%signature
    (point_map (g ∘ f)) (Basics.compose (point_map g) (point_map f)).
  Proof. intros [S1[?[P1 ?]]] [S2[?[P2 ?]]].
    unfold equiv, point_equiv. simpl. intro E. DN_tac1.
    intros [y1[[? Py1] [y2[[? Py2] Ey]]]].
    destruct (inhabited S1) as [x1 ?].
    destruct (inhabited S2) as [x2 ?].
    destruct E. exists_sub x1 x2. intro Ex.
    assert (x1 ∊ S2) by now rewrite (_ $ Ex).
    pose proof (Py1 x1 _).
    pose proof (Py2 (f x1) _).
    DN_tac1. destruct Ey. subtransitivity (g (f x1)). subsymmetry.
  Qed.
End functor.

Section map_ext.
  Context `{Setoid (S:=X)} U `{U ⊆ X}.
  Context `{Setoid (S:=Y)} p `{p ∊ Y}.
  Context (f:U ⇀ Y) `{!Morphism (U ⇒ Y) f}.

  Definition point_map_ext_set (S : set) : set :=
    λ y, y ∊ Y ∧ (∀ `{x ∊ S}, (x ∊ U → ¬¬ f x = y) ∧ (¬ x ∊ U → ¬¬ y = p )).

  Instance point_map_ext_el (S:set) `{S ⊆ X} (P:¬(∃ `{x ∊ S} `{y ∊ S}, ¬ x = y))
    x `{x ∊ S} `{x ∊ U} : f x ∊ point_map_ext_set S.
  Proof. split. apply _. intros x' ?. split; intros ? E;
    destruct P; exists_sub x x'; intro Ex;
    assert (x' ∊ U) by now rewrite <-(X $ Ex).
    destruct E. now rewrite (U $ Ex). contradiction.
  Qed.

  Instance point_map_ext_el2 (S:set) `{S ⊆ X} (P:¬(∃ `{x ∊ S} `{y ∊ S}, ¬ x = y))
    x `{x ∊ S} `{¬x ∊ U} : p ∊ point_map_ext_set S.
  Proof. split. apply _. intros x' ?. split; intros ? E;
    destruct P; exists_sub x x'; intro Ex;
    assert (¬x' ∊ U) by now rewrite <-(X $ Ex).
    contradiction. now destruct E.
  Qed.

  Lemma point_map_ext_obl (S : Point X) : IsPoint Y (point_map_ext_set (` S)).
  Proof. destruct S as [S[?[P1 P2]]]. simpl. unfold point_map_ext_set. split. 2: split.
  + apply subsetoid_alt. apply _.
    * intros ?? E. unfold_sigs. intros [? P]. red. split. apply _.
      intros a ?. destruct (P a _). split; intro.
      rewrite <-(_ $ E). tauto. rewrite <-(_ $ E). tauto.
    * now intros ? [??].
  + intros [y1[[? Py1] [y2[[? Py2] E]]]]. DN_tac1.
    destruct (inhabited S) as [x ?].
    destruct (Py1 x _). destruct (Py2 x _).
    apply (LEM_false (x ∊ U)). intros [?|?];
    repeat match goal with H: ?P1 -> ?P2, _ : ?P1 |- _ => (assert P2 by now apply H); clear H end;
    DN_tac1; destruct E.
    * subtransitivity (f x). subsymmetry.
    * subtransitivity p. subsymmetry.
  + DN_tac1. destruct (inhabited S) as [x ?].
    apply (LEM_negation (x ∊ U)). intros [?|?]; DN_tac.
    * exists (f x). now apply point_map_ext_el.
    * exists p. now apply point_map_ext_el2 with x.
  Qed.

  Definition point_map_ext : Point X → Point Y := λ S, exist _ _ (point_map_ext_obl S) .

  Instance point_map_ext_proper : Proper ((=)==>(=)) point_map_ext.
  Proof. intros [S1[?[P1 ?]]] [S2[?[P2 ?]]].
    unfold equiv, point_equiv. simpl. intro E. DN_tac1.
    intros [y1[[? Py1] [y2[[? Py2] Ey]]]].
    destruct (inhabited S1) as [x1 ?].
    destruct (inhabited S2) as [x2 ?].
    destruct E. exists_sub x1 x2. intro Ex.
    assert (x1 ∊ S2) by now rewrite (_ $ Ex).
    destruct (Py1 x1 _). destruct (Py2 x1 _).
    apply (LEM_false (x1 ∊ U)). intros [?|?];
    repeat match goal with H: ?P1 -> ?P2, _ : ?P1 |- _ => (assert P2 by now apply H); clear H end;
    DN_tac1; destruct Ey.
    * subtransitivity (f x1). subsymmetry.
    * subtransitivity p. subsymmetry.
  Qed.

End map_ext.

Hint Extern 2 (Proper _ (point_map_ext _ _ _)) => eapply @point_map_ext_proper : typeclass_instances.

Section map_binary.
  Context `{Setoid (S:=X)} `{Setoid (S:=Y)} `{Setoid (S:=Z)}.
  Context (f:X ⇀ Y ⇀ Z) `{!Morphism (X ⇒ Y ⇒ Z) f}.

  Definition point_map_binary_set (S : set) (T : set) : set
    := λ z, z ∊ Z ∧ (∀ `{x ∊ S} `{y ∊ T}, ¬¬ f x y = z).

  Instance point_map_binary_el
    (S:set) `{S ⊆ X} (PS:¬(∃ `{x ∊ S} `{y ∊ S}, ¬ x = y))
    (T:set) `{T ⊆ Y} (PT:¬(∃ `{x ∊ T} `{y ∊ T}, ¬ x = y))
    x `{x ∊ S} y `{y ∊ T} : f x y ∊ point_map_binary_set S T.
  Proof. split. apply _. intros x' ? y' ? E.
    destruct PS. exists_sub x x'. intro Ex.
    destruct PT. exists_sub y y'. intro Ey.
    destruct E. now rewrite (X $ Ex), (Y $ Ey).
  Qed.

  Lemma point_map_binary_obl (S : Point X) (T : Point Y)
    : IsPoint Z (point_map_binary_set (` S) (` T)).
  Proof. destruct S as [S[?[PS ?]]], T as [T[?[PT ?]]].
    simpl. unfold point_map_binary_set. split. 2: split.
  + apply subsetoid_alt. apply _.
    * intros ?? E. unfold_sigs. intros [? P]. red. split. apply _.
      intros a ? b ?. pose proof (P a _ b _). now rewrite <-(_ $ E).
    * now intros ? [??].
  + intros [z1[[? Pz1] [z2[[? Pz2] E]]]]. DN_tac1.
    destruct (inhabited S) as [x ?].
    destruct (inhabited T) as [y ?].
    pose proof (Pz1 x _ y _). pose proof (Pz2 x _ y _).
    DN_tac1. destruct E. subtransitivity (f x y). subsymmetry.
  + DN_tac1.
    destruct (inhabited S) as [x ?].
    destruct (inhabited T) as [y ?].
    DN_tac. exists (f x y). now apply point_map_binary_el.
  Qed.

  Definition point_map_binary : Point X → Point Y → Point Z
    := λ S T, exist _ _ (point_map_binary_obl S T) .

  Instance point_map_binary_proper : Proper ((=)==>(=)==>(=)) point_map_binary.
  Proof.
    intros [S1[?[PS1 ?]]] [S2[?[PS2 ?]]] ES.
    intros [T1[?[PT1 ?]]] [T2[?[PT2 ?]]] ET.
    revert ES ET. unfold equiv, point_equiv. simpl. intros ES ET. DN_tac1.
    intros [z1[[? Pz1] [z2[[? Pz2] E]]]].
    destruct (inhabited S1) as [x1 ?].
    destruct (inhabited S2) as [x2 ?].
    destruct ES. exists_sub x1 x2. intro Ex.
    assert (x1 ∊ S2) by now rewrite (_ $ Ex).
    destruct (inhabited T1) as [y1 ?].
    destruct (inhabited T2) as [y2 ?].
    destruct ET. exists_sub y1 y2. intro Ey.
    assert (y1 ∊ T2) by now rewrite (_ $ Ey).
    pose proof (Pz1 x1 _ y1 _). pose proof (Pz2 x1 _ y1 _).
    DN_tac1. destruct E. subtransitivity (f x1 y1). subsymmetry.
  Qed.
End map_binary.

Hint Extern 2 (Proper _ (point_map_binary _)) => eapply @point_map_binary_proper : typeclass_instances.

Require Import theory.strong_setoids theory.common_props.

Section props.
  Context `{S:set} `{Setoid _ (S:=S)} `{Setoid (S:=T)} `{Setoid (S:=U)}.
  Notation S' := (every (Point S)).
  Notation T' := (every (Point T)).
  Notation U' := (every (Point U)).
  Notation "#" := point_map_binary.

  Instance point_map_commutative 
    (f:S ⇀ S ⇀ T) `{!Morphism (S ⇒ S ⇒ T) f} `{!Commutative f S}
    : Commutative (# f) S'.
  Proof.
    intros [X[?[PX ?]]] _ [Y[?[PY ?]]] _.
    unfold equiv, point_equiv.
    intros [l [[? Pl] [r[[? Pr] E]]]]. simpl in *. DN_tac1.
    destruct (inhabited X) as [x ?].
    destruct (inhabited Y) as [y ?].
    cut(¬¬f x y = l ∧ ¬¬f y x = r).
      intros [E1 E2]. DN_tac1. destruct E.
      rewrite <-(_ $ E1), <-(_ $ E2).
      exact (commutativity f _ _).
    split.
    * apply Pl; trivial.
    * apply Pr; trivial.
  Qed.

  Instance point_map_associative
    (f:S ⇀ S ⇀ S) `{!Morphism (S ⇒ S ⇒ S) f} `{!Associative f S}
    : Associative (# f) S'.
  Proof.
    intros [X[?[PX ?]]] _ [Y[?[PY ?]]] _ [Z[?[PZ ?]]] _.
    unfold equiv, point_equiv.
    intros [l [[? Pl] [r[[? Pr] E]]]]. simpl in *. DN_tac1.
    destruct (inhabited X) as [x ?].
    destruct (inhabited Y) as [y ?].
    destruct (inhabited Z) as [z ?].
    cut(¬¬f x (f y z) = l ∧ ¬¬f (f x y) z = r).
      intros [E1 E2]. DN_tac1. destruct E.
      rewrite <-(_ $ E1), <-(_ $ E2).
      exact (associativity (f) _ _ _).
    split.
    * apply Pl; trivial. now apply point_map_binary_el.
    * apply Pr; trivial. now apply point_map_binary_el.
  Qed.

  Instance point_map_left_id
    (f:S ⇀ T ⇀ T) `{!Morphism (S ⇒ T ⇒ T) f} x `{x ∊ S} `{!LeftIdentity f x T}
    : LeftIdentity (# f) (point x) T'.
  Proof.
    intros [Y[?[PY ?]]] _.
    unfold equiv, point_equiv. simpl.
    intros [l [[? Pl] [y[? E]]]].
    cut(¬¬f x y = l).
      intros E1. DN_tac1. destruct E.
      rewrite <-(_ $ E1).
      exact (left_identity f _).
    apply Pl; trivial. now apply point_el.
  Qed.

  Instance point_map_right_id
    (f:S ⇀ T ⇀ S) `{!Morphism (S ⇒ T ⇒ S) f} y `{y ∊ T} `{!RightIdentity f y S}
    : RightIdentity (# f) (point y) S'.
  Proof.
    intros [X[?[PX ?]]] _.
    unfold equiv, point_equiv. simpl.
    intros [l [[? Pl] [x[? E]]]].
    cut(¬¬f x y = l).
      intros E1. DN_tac1. destruct E.
      rewrite <-(_ $ E1).
      exact (right_identity f _).
    apply Pl; trivial. now apply point_el.
  Qed.

  Instance point_map_left_absorb
    (f:S ⇀ T ⇀ S) `{!Morphism (S ⇒ T ⇒ S) f} x `{x ∊ S} `{!LeftAbsorb f x T}
    : LeftAbsorb (# f) (point x) T'.
  Proof.
    intros [Y[?[PY ?]]] _.
    unfold equiv, point_equiv. simpl.
    intros [l [[? Pl] [r[[? Er] E]]]]. DN_tac1.
    destruct (inhabited Y) as [y ?].
    cut(¬¬f x y = l).
      intros E1. DN_tac1. destruct E.
      rewrite <-(_ $ E1), (_ $ Er).
      exact (left_absorb f _).
    apply Pl; trivial. now apply point_el.
  Qed.

  Instance point_map_right_absorb
    (f:S ⇀ T ⇀ T) `{!Morphism (S ⇒ T ⇒ T) f} y `{y ∊ T} `{!RightAbsorb f y S}
    : RightAbsorb (# f) (point y) S'.
  Proof.
    intros [X[?[PX ?]]] _.
    unfold equiv, point_equiv. simpl.
    intros [l [[? Pl] [r[[? Er] E]]]]. DN_tac1.
    destruct (inhabited X) as [x ?].
    cut(¬¬f x y = l).
      intros E1. DN_tac1. destruct E.
      rewrite <-(_ $ E1), (_ $ Er).
      exact (right_absorb f _).
    apply Pl; trivial. now apply point_el.
  Qed.

  Instance point_map_left_inverse
    (op:S ⇀ T ⇀ U) `{!Morphism (S ⇒ T ⇒ U) op}
    (inv:T ⇀ S) `{!Morphism (T ⇒ S) inv}
    unit `{unit ∊ U} `{!LeftInverse op inv unit T}
    : LeftInverse (# op) (point_map inv) (point unit) T'.
  Proof.
    intros [Y[?[PY ?]]] _.
    unfold equiv, point_equiv. simpl.
    intros [l [[? Pl] [r[[? Er] E]]]]. DN_tac1.
    destruct (inhabited Y) as [y ?].
    cut(¬¬op (inv y) y = l).
      intros E1. DN_tac1. destruct E.
      rewrite <-(_ $ E1), (_ $ Er).
      exact (left_inverse op _).
    apply Pl; trivial. now apply point_map_el.
  Qed.

  Instance point_map_right_inverse
    (op:S ⇀ T ⇀ U) `{!Morphism (S ⇒ T ⇒ U) op}
    (inv:S ⇀ T) `{!Morphism (S ⇒ T) inv}
    unit `{unit ∊ U} `{!RightInverse op inv unit S}
    : RightInverse (# op) (point_map inv) (point unit) S'.
  Proof.
    intros [X[?[PX ?]]] _.
    unfold equiv, point_equiv. simpl.
    intros [l [[? Pl] [r[[? Er] E]]]]. DN_tac1.
    destruct (inhabited X) as [x ?].
    cut(¬¬op x (inv x) = l).
      intros E1. DN_tac1. destruct E.
      rewrite <-(_ $ E1), (_ $ Er).
      exact (right_inverse op _).
    apply Pl; trivial. now apply point_map_el.
  Qed.

  Instance point_map_distr_l
    (f:S ⇀ S ⇀ S) `{!Morphism (S ⇒ S ⇒ S) f}
    (g:S ⇀ S ⇀ S) `{!Morphism (S ⇒ S ⇒ S) g}
    `{!LeftDistribute f g S}
    : LeftDistribute (# f) (# g) S'.
  Proof.
    intros [X[?[PX ?]]] _ [Y[?[PY ?]]] _ [Z[?[PZ ?]]] _.
    unfold equiv, point_equiv.
    intros [l [[? Pl] [r[[? Pr] E]]]]. simpl in *. DN_tac1.
    destruct (inhabited X) as [x ?].
    destruct (inhabited Y) as [y ?].
    destruct (inhabited Z) as [z ?].
    cut(¬¬f x (g y z) = l ∧ ¬¬g (f x y) (f x z) = r).
      intros [E1 E2]. DN_tac1. destruct E.
      rewrite <-(_ $ E1), <-(_ $ E2).
      exact (distribute_l _ _ _).
    split.
    * apply Pl; trivial. now apply point_map_binary_el.
    * apply Pr; trivial; now apply point_map_binary_el.
  Qed.

  Instance point_map_distr_r
    (f:S ⇀ S ⇀ S) `{!Morphism (S ⇒ S ⇒ S) f}
    (g:S ⇀ S ⇀ S) `{!Morphism (S ⇒ S ⇒ S) g}
    `{!RightDistribute f g S}
    : RightDistribute (# f) (# g) S'.
  Proof.
    intros [X[?[PX ?]]] _ [Y[?[PY ?]]] _ [Z[?[PZ ?]]] _.
    unfold equiv, point_equiv.
    intros [l [[? Pl] [r[[? Pr] E]]]]. simpl in *. DN_tac1.
    destruct (inhabited X) as [x ?].
    destruct (inhabited Y) as [y ?].
    destruct (inhabited Z) as [z ?].
    cut(¬¬f (g x y) z = l ∧ ¬¬g (f x z) (f y z) = r).
      intros [E1 E2]. DN_tac1. destruct E.
      rewrite <-(_ $ E1), <-(_ $ E2).
      exact (distribute_r _ _ _).
    split.
    * apply Pl; trivial. now apply point_map_binary_el.
    * apply Pr; trivial; now apply point_map_binary_el.
  Qed.
End props.



Section ops.
  Context `(S:set) `{pfs:Setoid _ (S:=S)}.

  Instance point_zero `{Zero _} {pf:0 ∊ S} : Zero (Point S) := point 0.
  Instance point_one  `{One  _} {pf:1 ∊ S} : One  (Point S) := point 1.

  Instance point_plus `{Plus _} {pf:Morphism (S ⇒ S ⇒ S) (+)  } : Plus (Point S) := point_map_binary (+).
  Instance point_mult `{Mult _} {pf:Morphism (S ⇒ S ⇒ S) (.*.)} : Mult (Point S) := point_map_binary (.*.).

  Instance point_negate `{Negate _} {pf:Morphism (S ⇒ S) (-)  } : Negate (Point S) := point_map (-).
End ops.

Section mult_inv.
  Context `(F:set) `{pfs:StrongSetoid _ (S:=F)}.

  Instance point_mult_inv_mor : ∀ `{Inv _} `{Zero _}, Morphism (F ₀ ⇒ F ₀) inv → Morphism (F ₀ ⇒ F) inv.
  Proof. intros. now rewrite <-(_ : Subset (F ₀ ⇒ F ₀) (F ₀ ⇒ F)). Qed.

  Instance point_mult_inv `{Inv _} `{Zero _} {pf0:0 ∊ F} {pfi:Morphism (F ₀ ⇒ F ₀) inv}
    : Inv (Point F) := point_map_ext (F ₀) 0 inv.
End mult_inv.

Hint Extern 5 (@set (Point ?S)) => eexact (every (Point S)) : typeclass_instances.

Local Hint Extern 2 (Zero   (Point ?S)) => eapply (point_zero     S) : typeclass_instances.
Local Hint Extern 2 (One    (Point ?S)) => eapply (point_one      S) : typeclass_instances.
Local Hint Extern 2 (Plus   (Point ?S)) => eapply (point_plus     S) : typeclass_instances.
Local Hint Extern 2 (Mult   (Point ?S)) => eapply (point_mult     S) : typeclass_instances.
Local Hint Extern 2 (Negate (Point ?S)) => eapply (point_negate   S) : typeclass_instances.
Local Hint Extern 2 (Inv    (Point ?S)) => eapply (point_mult_inv S) : typeclass_instances.

Definition Point_Quote `{Equiv} S x (px : Point S) := x ∊ ` px.
Local Notation Quote := Point_Quote.

Section quoting.

  Context {A} {Ae : Equiv A} {Azero:Zero A} {Aone: One A} {Aplus:Plus A} {Amult:Mult A} {Anegate:Negate A}.

  Context S (setoid: Setoid S).

  Context (zero_closed  :0 ∊ S).
  Context (one_closed   :1 ∊ S).

  Context (plus_proper  :Morphism (S ⇒ S ⇒ S) (+)).
  Context (mult_proper  :Morphism (S ⇒ S ⇒ S) (.*.)).
  Context (negate_proper:Morphism (S ⇒ S) (-)).

  Lemma point_quote_base x {pf:x ∊ S} : Quote S x (point x).  Proof. now apply point_el. Qed.
  Lemma point_quote_zero : Quote S 0 0.                       Proof. now apply point_el. Qed.
  Lemma point_quote_one  : Quote S 1 1.                       Proof. now apply point_el. Qed.

  Ltac solve_binary sx sy :=
    destruct sx as [X[?[PX ?]]], sy as [Y[?[PY ?]]] ;
    unfold Quote in * ; simpl in * ;
    now apply point_map_binary_el.

  Lemma point_quote_plus `(E1:Quote S x sx) `(E2:Quote S y sy) : Quote S (x+y) (sx+sy).  Proof. solve_binary sx sy. Qed.
  Lemma point_quote_mult `(E1:Quote S x sx) `(E2:Quote S y sy) : Quote S (x*y) (sx*sy).  Proof. solve_binary sx sy. Qed.

  Lemma point_quote_negate `(E:Quote S x sx) : Quote S (-x) (-sx).
  Proof.
    destruct sx as [X[?[PX ?]]];
    unfold Quote in * ; simpl in * ;
    now apply point_map_el.
  Qed.

  Context {equal_stable : ∀ `{x ∊ S} `{y ∊ S}, Stable (x = y)} .

  Lemma point_quote_equiv_correct {x sx y sy} (E1:Quote S x sx) (E2:Quote S y sy) : sx = sy ↔ x = y.
  Proof. change (point_equiv _ sx sy ↔ x = y).
    destruct sx as [X[?[PX ?]]], sy as [Y[?[PY ?]]] .
    unfold Quote in *. unfold point_equiv. simpl in *.
    split.
    + intro E. apply (equal_stable _ _ _ _). intro E'.
      destruct E. now exists_sub x y.
    + intro E. intros [x' [? [y' [? E']]]].
      destruct PX. exists_sub x x'. intro Ex.
      destruct PY. exists_sub y y'. intro Ey.
      destruct E'. now rewrite <-(S $ Ex), <-(S $ Ey).
  Qed.
End quoting.

Section quoting_inv.
  Context {A} {Ae : Equiv A} {Aue : UnEq A} {Azero:Zero A} {Ainv : Inv A}.

  Context S (strong_setoid:StrongSetoid S).

  Context (zero_closed  :0 ∊ S).
  Context (inv_proper : Morphism (S ₀ ⇒ S ₀) inv).

  Existing Instance point_mult_inv_mor.

  Lemma point_quote_inv `{x ∊ S ₀} `(E:Quote S x sx) : Quote S (inv x) (inv sx).
  Proof.
    destruct sx as [X[?[PX ?]]];
    unfold Quote in * ; simpl in * .
    apply (point_map_ext_el (X:=S)); trivial; apply _.
  Qed.
End quoting_inv.


Ltac point_quote S s ss zc oc pp mp np ip :=
  let rec aux expr k :=
    match expr with
    | @zero _ _ => let q := constr:(point_quote_zero S s zc) in k q
    | @one _ _ => let q := constr:(point_quote_one S s oc) in k q
    | @plus _ _ ?x ?y =>
      let k2 qx qy := let q := constr:(point_quote_plus S s pp qx qy) in k q
      in let k1 qx := aux y ltac:(k2 qx)
      in aux x k1
    | @mult _ _ ?x ?y =>
      let k2 qx qy := let q := constr:(point_quote_mult S s mp qx qy) in k q
      in let k1 qx := aux y ltac:(k2 qx)
      in aux x k1
    | @negate _ _ ?x =>
      let k1 qx := let q := constr:(point_quote_negate S s np qx) in k q
      in aux x k1
    | @inv _ _ ?x =>
      let k1 qx := first [
          let q := constr:(point_quote_inv S ss zc ip qx) in k q
        | cut (x ∊ S ₀); [ intro; let q := constr:(point_quote_inv S ss zc ip qx) in k q |]
      ] in aux x k1
    | @point _ _ S _ ?x ?pf =>
           let q := constr:(@point_quote_base _ _ S s x pf) in k q
    | _ => let q:= constr:(point_quote_base S s expr) in k q
    end
  in aux.

Ltac point_quote_equiv S q :=
  match goal with |- @equiv _ _ ?x ?y =>
    let k2 qx qy := (apply (proj1 (point_quote_equiv_correct S _ qx qy)))
    in let k1 qx := q y ltac:(k2 qx)
    in q x k1
  end.

Section propers.
  Context {A} {Ae : Equiv A} {Azero:Zero A} {Aone: One A} {Aplus:Plus A} {Amult:Mult A} {Anegate:Negate A}.

  Context S (setoid: Setoid S).

  Context (zero_closed  :0 ∊ S).
  Context (one_closed   :1 ∊ S).

  Context (plus_proper  :Morphism (S ⇒ S ⇒ S) (+)).
  Context (mult_proper  :Morphism (S ⇒ S ⇒ S) (.*.)).
  Context (negate_proper:Morphism (S ⇒ S) (-)).

  Instance point_plus_proper: Proper ((=)==>(=)==>(=)) (@plus (Point S) _).
  Proof. unfold plus, point_plus. apply _. Qed.

  Instance point_mult_proper: Proper ((=)==>(=)==>(=)) (@mult (Point S) _).
  Proof. unfold mult, point_mult. apply _. Qed.

  Instance point_negate_proper: Proper ((=)==>(=)) (@negate (Point S) _).
  Proof. unfold negate, point_negate. apply _. Qed.
End propers.

Section inv_propers.
  Context {A} {Ae : Equiv A} {Aue : UnEq A} {Azero:Zero A} {Ainv : Inv A}.

  Context S (strong_setoid:StrongSetoid S).

  Context (zero_closed  :0 ∊ S).
  Context (inv_proper : Morphism (S ₀ ⇒ S ₀) inv).

  Instance point_inv_proper: Proper ((=)==>(=)) (@inv (Point S) _).
  Proof. unfold inv, point_mult_inv. apply _. Qed.
End inv_propers.

Hint Extern 2 (Proper _ (@plus   _ (point_plus     _))) => eapply @point_plus_proper : typeclass_instances.
Hint Extern 2 (Proper _ (@mult   _ (point_mult     _))) => eapply @point_mult_proper : typeclass_instances.
Hint Extern 2 (Proper _ (@negate _ (point_negate   _))) => eapply @point_negate_proper : typeclass_instances.
Hint Extern 2 (Proper _ (@inv    _ (point_mult_inv _))) => eapply @point_inv_proper : typeclass_instances.

Require Import theory.rings.

Section transference.
  Context {A} {Ae : Equiv A} {Azero:Zero A} {Aone: One A} {Aplus:Plus A} {Amult:Mult A} {Anegate:Negate A}.
  Context S (setoid: Setoid S).

  Context (zero_closed  :0 ∊ S).
  Context (one_closed   :1 ∊ S).

  Context (plus_proper  :Morphism (S ⇒ S ⇒ S) (+)).
  Context (mult_proper  :Morphism (S ⇒ S ⇒ S) (.*.)).
  Context (negate_proper:Morphism (S ⇒ S) (-)).

  Local Notation S' := (every (Point S)).

  Instance point_plus_monoid `{!AdditiveMonoid S} : AdditiveMonoid S'.
  Proof. split. split. split. apply _.
  + apply point_map_associative. apply _.
  + change (Morphism (S' ⇒ S' ⇒ S') (+)). apply _.
  + apply point_map_commutative. apply _.
  + apply _.
  + apply point_map_left_id. apply _.
  Qed.

  Instance point_plus_group `{!AdditiveGroup S} : AdditiveGroup S'.
  Proof. split. apply _.
  + change (Morphism (S' ⇒ S') (-)). apply _.
  + apply point_map_left_inverse. apply abgroup_inverse_l.
  Qed.

  Instance point_mult_semigroup `{!MultiplicativeSemiGroup S} : MultiplicativeSemiGroup S'.
  Proof. split. apply _.
  + apply point_map_associative. apply _.
  + change (Morphism (S' ⇒ S' ⇒ S') (.*.)). apply _.
  Qed.

  Instance point_mult_commonoid `{!MultiplicativeComMonoid S} : MultiplicativeComMonoid S'.
  Proof. split. split. apply _.
  + apply point_map_commutative. apply _.
  + apply _.
  + apply point_map_left_id. apply commonoid_left_id.
  Qed.

  Instance point_semirng `{!SemiRng S} : SemiRng S'.
  Proof. split. apply _. apply _.
  + apply point_map_distr_l. apply _.
  + apply point_map_distr_r. apply _.
  + apply point_map_left_absorb. apply _.
  + apply point_map_right_absorb. apply _.
  Qed.

  Instance point_semiring `{!SemiRing S} : SemiRing S'.
  Proof. split. apply _. apply _.
  + apply point_map_left_id. apply _.
  + apply point_map_right_id. apply _.
  Qed.

  Instance point_comsemiring `{!CommutativeSemiRing S} : CommutativeSemiRing S' := {}.

  Instance point_rng `{!Rng S} : Rng S' := {}.

  Instance point_ring `{!Ring S} : Ring S' := {}.

  Instance point_comring `{!CommutativeRing S} : CommutativeRing S' := {}.

End transference.

Require Import theory.fields.

Section field.
  Context {A} {Ae : Equiv A} {Aue : UnEq A} {Azero:Zero A} {Ainv : Inv A}.
  Context {Aone: One A} {Aplus:Plus A} {Amult:Mult A} {Anegate:Negate A}.

  Context S (setoid: Setoid S) (strong_setoid:StrongSetoid S).

  Context (zero_closed  :0 ∊ S).
  Context (one_closed   :1 ∊ S).

  Context (plus_proper  :Morphism (S ⇒ S ⇒ S) (+)).
  Context (mult_proper  :Morphism (S ⇒ S ⇒ S) (.*.)).
  Context (negate_proper:Morphism (S ⇒ S) (-)).
  Context (inv_proper   :Morphism (S ₀ ⇒ S ₀) inv).

  Lemma point_nonzero x `{x ∊ S ₀} (px : Point S) : x ∊ (` px) → ¬ px = 0.
  Proof. destruct px as [X[?[PX ?]]].
    unfold equiv, point_equiv. simpl. intro. DN_tac.
    assert (0 ∊ point_set (Y:=S) 0) by (apply point_el; apply _).
    exists_sub x 0. apply (uneq_ne _ _). apply (_ : x ∊ S ₀).
  Qed.

  Lemma point_nonzero_pt x `{x ∊ S} `{x ∊ S ₀} : ¬ point x = 0.
  Proof. apply (point_nonzero x). simpl. now apply point_el. Qed.

  Context `{!Field S}.

  Lemma point_field_nontrivial : ¬ 1 = (0:Point S).
  Proof point_nonzero_pt 1.

  Notation pinv := (@inv _ (point_mult_inv (pfs:=strong_setoid) S)). 

  Existing Instance point_mult_inv_mor.

  Lemma point_field_inv_l  (x : Point S) : ¬ x = 0 → pinv x * x = 1.
  Proof. unfold equiv, point_equiv.
    destruct x as [X [?[P ?]]]. simpl. intros E. DN_tac1.
    destruct E as [x[?[z[[? Ez'] Ez]]]]. DN_tac1.
    rewrite (_ $ Ez') in Ez. clear dependent z.
    apply (LEM_negation (x ≠ 0)).
    rewrite (tight_apart _ _). intros [?|?]; [|contradiction].
    assert (x ∊ S ₀). split; trivial. apply _.
    intros [p[[? Pp] [one [[? Eone] E] ]]]. DN_tac1.
    rewrite (_ $ Eone) in E. clear dependent one.
    cut (¬¬inv x * x = p). intro Ep. DN_tac1.
      destruct E. rewrite <-(_ $ Ep). exact (field_inv_l _).
    apply Pp; trivial. apply (point_map_ext_el (X:=S)); trivial; apply _.
  Qed.
End field.
