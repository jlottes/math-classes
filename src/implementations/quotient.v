Require Import abstract_algebra theory.setoids theory.common_props.

Inductive Quotient {A} (X Y:@set A) := equiv_class { rep : A }.
Infix "/" := Quotient : type_scope.
Arguments rep {A X Y} _.
Arguments equiv_class {A} X Y _.

Definition quotient_set {A} (X Y:@set A) : @set (X/Y) := λ p, rep p ∊ X.
Infix "/" := quotient_set : set_scope.

Hint Extern 10 (@set (_/_)) => class_apply @quotient_set : typeclass_instances.

Local Notation "# x" := (equiv_class _ _ x) (at level 20, format "# x") : mc_scope.

Lemma quotient_el `(X:set) Y x `{x ∊ X} : #x ∊ X/Y.
Proof. firstorder. Qed.
Hint Extern 5 (equiv_class ?X ?Y _ ∊ ?X / ?Y) => eapply @quotient_el : typeclass_instances.

Definition Quotient_lift_arg {A B} {X1 Y1:@set A} {X2:@set B} f : (X1/Y1) → B
  := λ x  , f (rep x).
Definition Quotient_lift1 {A B} {X1 Y1:@set A} {X2 Y2:@set B} f : (X1/Y1) → (X2/Y2)
  := λ x  , #(f (rep x)).
Definition Quotient_lift2 {A B C} {X1 Y1:@set A} {X2 Y2:@set B} {X3 Y3:@set C} f : (X1/Y1) → (X2/Y2) → (X3/Y3)
  := λ x y, #(f (rep x) (rep y)).

Section ops.
  Context {A} (X Y:@set A).

  Definition Quotient_inject : Cast X (X/Y) := equiv_class X Y.

  Definition Quotient_sg_op    `{SgOp    A} : SgOp    (X/Y) := Quotient_lift2 (&).
  Definition Quotient_mon_unit `{MonUnit A} : MonUnit (X/Y) := # mon_unit.
  Definition Quotient_inv      `{Inv     A} : Inv     (X/Y) := Quotient_lift1 inv.
  Definition Quotient_zero     `{Zero    A} : Zero    (X/Y) := # 0.
  Definition Quotient_one      `{One     A} : One     (X/Y) := # 1.
  Definition Quotient_plus     `{Plus    A} : Plus    (X/Y) := Quotient_lift2 (+).
  Definition Quotient_mult     `{Mult    A} : Mult    (X/Y) := Quotient_lift2 (.*.).
  Definition Quotient_negate   `{Negate  A} : Negate  (X/Y) := Quotient_lift1 (-).
End ops.

Hint Extern 5 (Cast  _ (_/_)) => class_apply @Quotient_inject : typeclass_instances.
Hint Extern 0 (SgOp    (_/_)) => eapply @Quotient_sg_op    : typeclass_instances.
Hint Extern 0 (MonUnit (_/_)) => eapply @Quotient_mon_unit : typeclass_instances.
Hint Extern 0 (Inv     (_/_)) => eapply @Quotient_inv      : typeclass_instances.
Hint Extern 0 (Zero    (_/_)) => eapply @Quotient_zero     : typeclass_instances.
Hint Extern 0 (One     (_/_)) => eapply @Quotient_one      : typeclass_instances.
Hint Extern 0 (Plus    (_/_)) => eapply @Quotient_plus     : typeclass_instances.
Hint Extern 0 (Mult    (_/_)) => eapply @Quotient_mult     : typeclass_instances.
Hint Extern 0 (Negate  (_/_)) => eapply @Quotient_negate   : typeclass_instances.

Ltac quotient_destr :=
  repeat match goal with a : Quotient ?X ?Y |- _ => destruct a as [a] end;
  repeat match goal with el : {| rep := ?x |} ∊ ?X / ?Y |- _ => change (x ∊ X) in el end.

Section setoid.
  Context {A} {X Y:@set A} {R} `{!Equivalence X R}.

  Lemma quotient_equivalence : Equivalence (X/Y) (λ a b, R (rep a) (rep b)).
  Proof. split; [intros ?? | intros ???? | intros ??????]; quotient_destr; simpl; intros; try easy.
    subtransitivity y.
  Qed.

  Instance quotient_equiv: Equiv (X/Y) := λ a b, R (rep a) (rep b).

  Instance quotient_setoid : Setoid (X/Y).
  Proof quotient_equivalence.

End setoid.

Local Hint Extern 10 (Setoid (?X/?Y)) => eapply @quotient_setoid : typeclass_instances.

Section morphisms.
  Context {A} {X1 Y1:@set A} {R1} `{!Equivalence X1 R1}.
  Context {B} {X2 Y2:@set B} {R2} `{!Equivalence X2 R2}.
  Context {C} {X3 Y3:@set C} {R3} `{!Equivalence X3 R3}.

  Notation R1' := (restrict_rel X1 R1).
  Notation R2' := (restrict_rel X2 R2).
  Notation R3' := (restrict_rel X3 R3).

  Instance: Equiv (X1/Y1) := λ a b, R1 (rep a) (rep b).
  Instance: Equiv (X2/Y2) := λ a b, R2 (rep a) (rep b).
  Instance: Equiv (X3/Y3) := λ a b, R3 (rep a) (rep b).

  Lemma quotient_morphism f : Proper (R1'==>R2') f
    → Morphism (X1/Y1 ⇒ X2/Y2) (Quotient_lift1 f).
  Proof. intros P x1 y1 E1. exact (P (rep x1) (rep y1) E1). Qed.

  Lemma quotient_morphism_arg `{Equiv B} `{!Setoid X2} f : Proper (R1'==>(X2,=)) f
  → Morphism (X1/Y1 ⇒ X2) (Quotient_lift_arg f).
  Proof. intros P x1 y1 E1. exact (P (rep x1) (rep y1) E1). Qed.

  Lemma quotient_binary_morphism f : Proper (R1'==>R2'==>R3') f
  → Morphism (X1/Y1 ⇒ X2/Y2 ⇒ X3/Y3) (Quotient_lift2 f).
  Proof. intro P. apply binary_morphism_proper_back.
    intros x1 y1 E1 x2 y2 E2. exact (P (rep x1) (rep y1) E1 (rep x2) (rep y2) E2).
  Qed.

  Context `{Equiv A} `{!SubRelation X1 (=) R1}.
  Context `{Equiv B} `{!SubRelation X2 (=) R2}.
  Context `{Equiv C} `{!SubRelation X3 (=) R3}.

  Lemma equiv_class_morphism `{!Setoid X1} : Morphism (X1 ⇒ X1/Y1) (equiv_class X1 Y1).
  Proof.
    intros x y E. unfold_sigs. red_sig.
    exact ((_:SubRelation X1 (=) R1) x _ y _ E).
  Qed.

  Lemma quotient_inject_morphism `{!Setoid X1} : Morphism (X1 ⇒ X1/Y1) (').
  Proof equiv_class_morphism.

  Lemma quotient_assoc f `{!Closed (X1 ⇀ X1 ⇀ X1) f} `{!Associative f X1}
  : Associative (A:=X1/Y1) (Quotient_lift2 f) (X1/Y1).
  Proof. assert (Associative f X1 (Ae:=R1)) by now rewrite <- (_:SubRelation X1 (=) R1).
    intros ??????. quotient_destr. exact (associativity f _ _ _).
  Qed.

  Lemma quotient_comm f `{!Closed (X1 ⇀ X1 ⇀ X2) f} `{!Commutative f X1}
  : Commutative (A:=X1/Y1) (B:=X2/Y2) (Quotient_lift2 f) (X1/Y1).
  Proof. assert (Commutative f X1 (Be:=R2)) by now rewrite <- (_:SubRelation X2 (=) R2).
    intros ????. quotient_destr. exact (commutativity f _ _).
  Qed.

  Lemma quotient_left_id op x `{x ∊ X1} `{!Closed (X1 ⇀ X1 ⇀ X1) op} `{!LeftIdentity op x X1}
  : LeftIdentity (A:=X1/Y1) (B:=X1/Y1) (Quotient_lift2 op) (# x) (X1/Y1).
  Proof. assert (LeftIdentity op x X1 (Be:=R1)) by now rewrite <- (_:SubRelation X1 (=) R1).
    intros y ?. quotient_destr. exact (left_identity op y).
  Qed.

  Lemma quotient_right_id op y `{y ∊ X1} `{!Closed (X1 ⇀ X1 ⇀ X1) op} `{!RightIdentity op y X1}
  : RightIdentity (A:=X1/Y1) (B:=X1/Y1) (Quotient_lift2 op) (# y) (X1/Y1).
  Proof. assert (RightIdentity op y X1 (Ae:=R1)) by now rewrite <- (_:SubRelation X1 (=) R1).
    intros x ?. quotient_destr. exact (right_identity op x).
  Qed.

  Lemma quotient_left_inv op inv unit `{unit ∊ X3} `{!Closed (X1 ⇀ X1 ⇀ X3) op} `{!Closed (X1 ⇀ X1) inv}
    `{!LeftInverse op inv unit X1}
  : LeftInverse (A:=X1/Y1) (B:=X1/Y1) (C:=X3/Y3) (Quotient_lift2 op) (Quotient_lift1 inv) (# unit) (X1/Y1).
  Proof. assert (LeftInverse op inv unit X1 (Ce:=R3)) by now rewrite <- (_:SubRelation X3 (=) R3).
    intros y ?. quotient_destr. exact (left_inverse op y).
  Qed.

  Lemma quotient_right_inv op inv unit `{unit ∊ X3} `{!Closed (X1 ⇀ X1 ⇀ X3) op} `{!Closed (X1 ⇀ X1) inv}
    `{!RightInverse op inv unit X1}
  : RightInverse (A:=X1/Y1) (B:=X1/Y1) (C:=X3/Y3) (Quotient_lift2 op) (Quotient_lift1 inv) (# unit) (X1/Y1).
  Proof. assert (RightInverse op inv unit X1 (Ce:=R3)) by now rewrite <- (_:SubRelation X3 (=) R3).
    intros x ?. quotient_destr. exact (right_inverse op x).
  Qed.

  Lemma quotient_left_distr f g `{!Closed (X1 ⇀ X1 ⇀ X1) f} `{!Closed (X1 ⇀ X1 ⇀ X1) g} `{!LeftDistribute f g X1}
  : LeftDistribute (A:=X1/Y1) (Quotient_lift2 f) (Quotient_lift2 g) (X1/Y1).
  Proof. assert (LeftDistribute f g X1 (Ae:=R1)) by now rewrite <- (_:SubRelation X1 (=) R1).
    intros ??????. quotient_destr. exact (distribute_l (f:=f) (g:=g) _ _ _).
  Qed.

  Lemma quotient_right_distr f g `{!Closed (X1 ⇀ X1 ⇀ X1) f} `{!Closed (X1 ⇀ X1 ⇀ X1) g} `{!RightDistribute f g X1}
  : RightDistribute (A:=X1/Y1) (Quotient_lift2 f) (Quotient_lift2 g) (X1/Y1).
  Proof. assert (RightDistribute f g X1 (Ae:=R1)) by now rewrite <- (_:SubRelation X1 (=) R1).
    intros ??????. quotient_destr. exact (distribute_r (f:=f) (g:=g) _ _ _).
  Qed.

End morphisms.

Hint Extern 5 (Morphism _ (equiv_class _ _)) => eapply @equiv_class_morphism : typeclass_instances.
Hint Extern 5 (Morphism _ (cast _ (_/_))) => eapply @quotient_inject_morphism : typeclass_instances.

Section sg_props.
  Context `{Equiv A} {X Y:@set A} {R} `{!Equivalence X R} `{!SubRelation X (=) R}.

  Instance: Equiv (X/Y) := λ a b, R (rep a) (rep b).

  Context `{SgOp _} `{!Closed (X ⇀ X ⇀ X) (&)}.

  Lemma quotient_sg_op_assoc `{!Associative (&) X} : Associative (&) (X/Y).
  Proof quotient_assoc (&).

  Lemma quotient_sg_op_comm `{!Commutative (&) X} : Commutative (&) (X/Y).
  Proof quotient_comm (&).

  Context `{MonUnit _} `{mon_unit ∊ X}.

  Lemma quotient_mon_unit_exists : mon_unit ∊ X/Y.
  Proof _ : mon_unit ∊ X.

  Lemma quotient_sg_op_left_id `{!LeftIdentity (&) mon_unit X} : LeftIdentity (&) mon_unit (X/Y).
  Proof quotient_left_id (&) mon_unit.

  Lemma quotient_sg_op_right_id `{!RightIdentity (&) mon_unit X} : RightIdentity (&) mon_unit (X/Y).
  Proof quotient_right_id (&) mon_unit.

  Context `{Inv _} `{!Closed (X ⇀ X) inv}.

  Lemma quotient_sg_op_left_inv `{!LeftInverse (&) inv mon_unit X} : LeftInverse (&) inv mon_unit (X/Y).
  Proof quotient_left_inv (&) inv mon_unit.

  Lemma quotient_sg_op_right_inv `{!RightInverse (&) inv mon_unit X} : RightInverse (&) inv mon_unit (X/Y).
  Proof quotient_right_inv (&) inv mon_unit.

End sg_props.

Hint Extern 10 (Associative (&) (?X/?Y)) => eapply @quotient_sg_op_assoc : typeclass_instances.
Hint Extern 10 (Commutative (&) (?X/?Y)) => eapply @quotient_sg_op_comm : typeclass_instances.
Hint Extern 10 (mon_unit ∊ ?X/?Y) => eapply @quotient_mon_unit_exists : typeclass_instances.
Hint Extern 10 (LeftIdentity (&) mon_unit (?X/?Y)) => eapply @quotient_sg_op_left_id : typeclass_instances.
Hint Extern 10 (RightIdentity (&) mon_unit (?X/?Y)) => eapply @quotient_sg_op_right_id : typeclass_instances.
Hint Extern 10 (LeftInverse (&) inv mon_unit (?X/?Y)) => eapply @quotient_sg_op_left_inv : typeclass_instances.
Hint Extern 10 (RightInverse (&) inv mon_unit (?X/?Y)) => eapply @quotient_sg_op_right_inv : typeclass_instances.

Section rng_props.
  Context `{Equiv A} {X Y:@set A} {R} `{!Equivalence X R} `{!SubRelation X (=) R}.

  Instance: Equiv (X/Y) := λ a b, R (rep a) (rep b).

  Context `{Plus A} `{!Closed (X ⇀ X ⇀ X) (+)}.
  Context `{Mult A} `{!Closed (X ⇀ X ⇀ X) (.*.)}.

  Lemma quotient_rng_left_distr `{!LeftDistribute (.*.) (+) X} : LeftDistribute (.*.) (+) (X/Y).
  Proof quotient_left_distr (.*.) (+).

  Lemma quotient_rng_right_distr `{!RightDistribute (.*.) (+) X} : RightDistribute (.*.) (+) (X/Y).
  Proof quotient_right_distr (.*.) (+).

  Context `{One _} `{1 ∊ X}.

  Lemma quotient_one_exists : 1 ∊ X/Y.
  Proof _ : 1 ∊ X.

  Lemma quotient_mult_left_id `{!LeftIdentity (.*.) 1 X} : LeftIdentity (.*.) 1 (X/Y).
  Proof quotient_left_id (.*.) 1.

  Lemma quotient_mult_right_id `{!RightIdentity (.*.) 1 X} : RightIdentity (.*.) 1 (X/Y).
  Proof quotient_right_id (.*.) 1.

End rng_props.

Hint Extern 10 (LeftDistribute (.*.) (+) (?X/?Y)) => eapply @quotient_rng_left_distr : typeclass_instances.
Hint Extern 10 (RightDistribute (.*.) (+) (?X/?Y)) => eapply @quotient_rng_right_distr : typeclass_instances.
Hint Extern 10 (1 ∊ ?X/?Y) => eapply @quotient_one_exists : typeclass_instances.
Hint Extern 10 (LeftIdentity (.*.) 1 (?X/?Y)) => eapply @quotient_mult_left_id : typeclass_instances.
Hint Extern 10 (RightIdentity (.*.) 1 (?X/?Y)) => eapply @quotient_mult_right_id : typeclass_instances.
