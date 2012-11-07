Require Import
  abstract_algebra theory.strong_setoids theory.common_props
  theory.subgroups theory.subrings theory.strong_groups.
Require Export
  theory.integral_domains.

Local Open Scope grp_scope. (* notation for inverse *)

Lemma field_proper: Find_Proper_Signature (@Field) 0
  (∀ A Aplus Amult Azero Aone Anegate Ainv Ae Aue,
   Proper ((=)==>impl) (@Field A Aplus Amult Azero Aone Anegate Ainv Ae Aue)).
Proof. structure_proper.
  match goal with E : ?X = ?Y |- Morphism (?Y ₀ ⇒ ?Y ₀) (⁻¹) =>
    assert (SubsetOf (X ₀) (Y ₀)) by (rewrite E; apply _);
    assert (SubsetOf (Y ₀) (X ₀)) by (rewrite E; apply _);
    now rewrite <-(_ : SubsetOf (X ₀ ⇒ X ₀) (Y ₀ ⇒ Y ₀))
  end.
Qed.
Hint Extern 0 (Find_Proper_Signature (@Field) 0 _) => eexact field_proper : typeclass_instances.

Lemma mult_inv_closed `{Field (F:=F)} x `{x ∊ F ₀} : x⁻¹ ∊ F ₀.
Proof. apply (closed_range (F ₀)); apply _. Qed.
Hint Extern 4 (_⁻¹ ∊ _ ₀) => eapply @mult_inv_closed : typeclass_instances. 

Lemma mult_inv_closed2 `{Field (F:=F)} x `{x ∊ F ₀} : x⁻¹ ∊ F.
Proof. pose proof _ : x⁻¹ ∊ F ₀. apply _. Qed.
Hint Extern 6 (_⁻¹ ∊ _) => eapply @mult_inv_closed2 : typeclass_instances. 


Section props.
  Context `{Field (F:=F)}.

  Existing Instance field_nontrivial.

  Lemma field_inv_r x `{x ∊ F ₀} : x / x = 1.
  Proof. rewrite (F $ commutativity (.*.) _ _). exact (field_inv_l x). Qed.

  Lemma field_units : RingUnits F = F ₀.
  Proof. intro x. split.
  + intros [?[y[?[E ?]]]]. split. apply _.
    apply (strong_extensionality (.* y)). rewrite_on F -> E, (mult_0_l y).
    solve_propholds.
  + intros ?. split. apply _. exists_sub (x⁻¹).
    split; [ exact (field_inv_r x) | exact (field_inv_l x) ].
  Qed.

  Instance: ∀ `{x ∊ F ₀}, x ∊ RingUnits F.
  Proof. intros. now apply field_units. Qed.

  Global Instance field_multgroup : MultiplicativeAbGroup (F ₀).
  Proof. rewrite <- field_units. apply RingUnits_abgroup.
    pose proof field_units. rewrite <- (_ : SubsetOf (F ₀ ⇒ F ₀) (RingUnits F ⇒ RingUnits F)).
    apply _. rewrite field_units; apply _.
  Qed.

  Global Instance : IntegralDomain F := {}.

  (*Instance field_mult_nonzero: Closed (F ₀ ==> F ₀ ==> F ₀) (.*.) := _.*)
  (*Instance field_strong_mult_nonzero: StrongSemiGroupOp (op:=mult_is_sg_op) (F ₀) := _.*)

  (*Instance mult_inv_strong_inj: StrongInjective (F ₀) (F ₀) (⁻¹) := _.
  Instance mult_inv_strong: StrongSetoid_Morphism (F ₀) (F ₀) (⁻¹) := _.*)

  Lemma mult_inv_involutive x `{x ∊ F ₀} : (x⁻¹)⁻¹ = x. Proof involutive (S:=(F ₀)) x.

  Lemma mult_inv_1 : 1⁻¹ = 1. Proof inv_mon_unit (G:=(F ₀)).
  Lemma mult_inv_distr x `{x ∊ F ₀} y `{y ∊ F ₀}: (x * y)⁻¹ = x⁻¹ * y⁻¹. Proof abgroup_inv_distr (G:=(F ₀)) x y.

  Lemma mult_inv_negate x `{x ∊ F ₀} : (-x)⁻¹ = - x⁻¹.
  Proof. apply (left_cancellation (.*.) (-x) F _ _).
    now rewrite (F $ negate_mult_negate _ _), !(F $ field_inv_r _).
  Qed.

  Lemma mult_inv_cancel_l z `{z ∊ F ₀} x `{x ∊ F} y `{y ∊ F} : x = y * z ↔ x / z = y.
  Proof. split.
  + intro. apply (right_cancellation (.*.) z F _ _).
    now rewrite <- (F $ associativity (.*.) _ _ _), (F $ field_inv_l z), (F $ mult_1_r _).
  + intro.  apply (right_cancellation (.*.) z⁻¹ F _ _).
    now rewrite <- (F $ associativity (.*.) _ _ _), (F $ field_inv_r z), (F $ mult_1_r _).
  Qed.

  Lemma mult_inv_cancel_r z `{z ∊ F ₀} x `{x ∊ F} y `{y ∊ F} : x * z = y ↔ x = y / z.
  Proof. split.
  + intro. apply (right_cancellation (.*.) z F _ _).
    now rewrite <- (F $ associativity (.*.) _ _ _), (F $ field_inv_l z), (F $ mult_1_r _).
  + intro.  apply (right_cancellation (.*.) z⁻¹ F _ _).
    now rewrite <- (F $ associativity (.*.) _ _ _), (F $ field_inv_r z), (F $ mult_1_r _).
  Qed.

  Lemma mult_inv_cancel_both  a `{a ∊ F} b `{b ∊ F ₀} c `{c ∊ F} d `{d ∊ F ₀}
    : a*d = b*c ↔ a/b = c/d.
  Proof. rewrite (mult_inv_cancel_r _ _ _).
    rewrite <- (F $ associativity (.*.) b c (inv d)).
    rewrite (F $ commutativity (.*.) b (c/d)).
    exact (mult_inv_cancel_l _ _ _).
  Qed.

  Lemma mult_inv_strong_cancel_l z `{z ∊ F ₀} x `{x ∊ F} y `{y ∊ F} : x ≠ y * z ↔ x / z ≠ y.
  Proof. split; intro E.
  + apply (strong_right_cancellation (.*.) z⁻¹ F _ _) in E.
    now rewrite <- (F $ associativity (.*.) _ _ _), (F $ field_inv_r z), (F $ mult_1_r _) in E.
  + apply (strong_right_cancellation (.*.) z F _ _) in E.
    now rewrite <- (F $ associativity (.*.) _ _ _), (F $ field_inv_l _), (F $ mult_1_r _) in E.
  Qed.

  Lemma mult_inv_strong_cancel_r z `{z ∊ F ₀} x `{x ∊ F} y `{y ∊ F} : x * z ≠ y ↔ x ≠ y / z.
  Proof. split; intro E.
  + apply (strong_right_cancellation (.*.) z⁻¹ F _ _) in E.
    now rewrite <- (F $ associativity (.*.) _ _ _), (F $ field_inv_r z), (F $ mult_1_r _) in E.
  + apply (strong_right_cancellation (.*.) z F _ _) in E.
    now rewrite <- (F $ associativity (.*.) _ _ _), (F $ field_inv_l _), (F $ mult_1_r _) in E.
  Qed.

  Lemma mult_inv_strong_cancel_both  a `{a ∊ F} b `{b ∊ F ₀} c `{c ∊ F} d `{d ∊ F ₀}
    : a*d ≠ b*c ↔ a/b ≠ c/d.
  Proof. rewrite (mult_inv_strong_cancel_r _ _ _).
    rewrite <- (F $ associativity (.*.) b c (inv d)).
    rewrite (F $ commutativity (.*.) b (c/d)).
    exact (mult_inv_strong_cancel_l _ _ _).
  Qed.

End props.

(* Hint Extern 5 (AbGroup (_ ₀)) => eapply @field_multgroup : typeclass_instances. *)

(*
Check fun `{Field (F:=F)} => _ : StrongInjective F F (-).
Check fun `{Field (F:=F)} `{z ∊ F ₀} => _ : StrongRightCancellation (.*.) z F.
Check fun `{Field (F:=F)} => _ : StrongInjective (F ₀) (F ₀) (⁻¹).
*)

Section dec_field.
  Context `{CommutativeRing A (R:=F)} `{Inv A}.
  Context `{UnEq A} `{!StandardUnEq F} `{!SubDecision F F (=)}.

  Lemma dec_field
    : Morphism (F ₀ ⇒ F ₀) (⁻¹)
    → PropHolds (1 ≠ 0)
    → LeftInverse (.*.) (⁻¹) 1 (F ₀)
    → Field F.
  Proof with try apply _. pose proof dec_strong_setoid. split... split...
    exact (dec_strong_binary_morphism (+)).
    exact (dec_strong_binary_morphism (.*.)).
  Qed.
End dec_field.

Section morphisms.
  Context `{Field (F:=F1)} `{Field (F:=F2)} {f:F1 ⇀ F2} `{!Strong_Morphism F1 F2 f}
          `{!Ring_Morphism F1 F2 f}.

  Instance field_mor_nonzero: Strong_Morphism (F1 ₀) (F2 ₀) f.
  Proof. split; try apply _.
  + intros x ?. apply (mult_apart_zero_l _ (f (x⁻¹))).
    rewrite <- (F2 $ preserves_mult _ _), (F1 $ field_inv_r _), (F2 $ preserves_1). apply _.
  + rewrite strong_ext_equiv_1. intros. now apply (strong_extensionality f).
  Qed.

  Global Instance: StrongInjective F1 F2 f.
  Proof. apply strong_injective_preserves_0. apply _. Qed.

  Global Instance field_multgroup_mor: MultiplicativeSemiGroup_Morphism (F1 ₀) (F2 ₀) f.
  Proof. split; try apply _. intros. exact (preserves_mult _ _). Qed.

  Lemma preserves_mult_inv x `{x ∊ F1 ₀} : f x⁻¹ = (f x)⁻¹.
  Proof preserves_inverse (G1:=(F1 ₀)) (G2:=(F2 ₀)) x.
End morphisms.

