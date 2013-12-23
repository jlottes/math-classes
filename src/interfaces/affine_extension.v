Require Import abstract_algebra interfaces.orders.

Class AffExtFull `(R:@set A) := aff_ext_full : @set A.
Class AffExt     `(R:@set A) := aff_ext      : @set A.

Arguments aff_ext_full {_} R {_} _.
Arguments aff_ext {_} R {_} _.

Local Notation F  := (aff_ext_full _).
Local Notation "R∞" := (aff_ext _).

Definition ae_undef `(R:@set A) `{!AffExtFull R} `{!AffExt R} : @set A
  := λ x, x ∊ F ∧ ¬ x ∊ R∞.

Local Notation U := (ae_undef _).

Definition ae_inf_undef `(R:@set A) `{!AffExtFull R} : @set A
  := λ x, x ∊ F ∧ ¬ x ∊ R.

Section ring.
  Context {A} {R:@set A}
    `{Equiv A} `{Plus A} `{Mult A} `{Zero A} `{One A} `{Negate A}
    `{UnEq A} `{Le A} `{Lt A} `{Infty A}.

  Context `{!AffExtFull R} `{!AffExt R}.

  Class AffinelyExtendedRing : Prop :=
  { ae_cring :>> CommutativeRing R
  ; ae_order :>> FullPseudoSemiRingOrder R
  ; ae_order_ext :>> FullPseudoOrder R∞
  ; ae_order_full :>> FullPartialOrder F
  ; ae_set_def : R∞ = (λ x, x ∊ R ∨ (x ∊ F ∧ (x = ∞ ∨ x = -∞)))
  ; ae_subsetoid : R ⊆ F
  ; ae_decompose_full x `{x ∊ F} : x ∊ R∞ ∨ x ∊ U
  ; ae_undef_eq x `{x ∊ U} y `{y ∊ U} : x = y
  ; ae_undef_uneq x `{x ∊ U} y `{y ∊ R∞} : x ≠ y
  ; ae_plus_mor : Morphism (F ⇒ F ⇒ F) (+)
  ; ae_negate_mor : Morphism (F ⇒ F) (-)
  ; ae_mult_mor : Strong_Binary_Morphism F F F (.*.)
  ; ae_inf_el_F : ∞ ∊ F
  ; ae_inf_not_el : ¬ ∞ ∊ R
  ; ae_lt_defined x `{x ∊ F} y `{y ∊ F} : x < y → x ∊ R∞ ∧ y ∊ R∞
  ; ae_inf_sub x `{x ∊ R} : x < ∞
  ; ae_minf_slb x `{x ∊ R} : -∞ < x
  ; ae_neg_inf_invl : - - ∞ = ∞
  ; ae_neg_undef : Closed (U ⇀ U) (-)
  ; ae_plus_inf_r x `{x ∊ R∞} : -∞ < x → x + ∞ = ∞
  ; ae_plus_inf_l x `{x ∊ R∞} : -∞ < x → ∞ + x = ∞
  ; ae_minus_inf_r x `{x ∊ R∞} : x < ∞ →  x - ∞ = -∞
  ; ae_minus_inf_l x `{x ∊ R∞} : x < ∞ → -∞ + x = -∞
  ; ae_inf_minus_inf_r :  ∞ - ∞ ∊ U
  ; ae_inf_minus_inf_l : -∞ + ∞ ∊ U
  ; ae_plus_undef_l : Closed (U ⇀ F ⇀ U) (+)
  ; ae_plus_undef_r : Closed (F ⇀ U ⇀ U) (+)
  ; ae_pos_mult_inf_r x `{x ∊ R∞₊} : x * ∞ = ∞
  ; ae_pos_mult_inf_l x `{x ∊ R∞₊} : ∞ * x = ∞
  ; ae_neg_mult_inf_r x `{x ∊ R∞₋} : x * ∞ = -∞
  ; ae_neg_mult_inf_l x `{x ∊ R∞₋} : ∞ * x = -∞
  ; ae_pos_mult_minf_r x `{x ∊ R∞₊} :  x * -∞ = -∞
  ; ae_pos_mult_minf_l x `{x ∊ R∞₊} : -∞ *  x = -∞
  ; ae_neg_mult_minf_r x `{x ∊ R∞₋} :  x * -∞ = ∞
  ; ae_neg_mult_minf_l x `{x ∊ R∞₋} : -∞ *  x = ∞
  ; ae_zero_mult_inf : 0 * ∞ ∊ U
  ; ae_zero_mult_minf : 0 * -∞ ∊ U
  ; ae_inf_mult_zero : ∞ * 0 ∊ U
  ; ae_minf_mult_zero : -∞ * 0 ∊ U
  ; ae_mult_undef_l : Closed (U ⇀ F ⇀ U) (.*.)
  ; ae_mult_undef_r : Closed (F ⇀ U ⇀ U) (.*.)
  }.
End ring.

Arguments AffinelyExtendedRing {_} R {_ _ _ _ _ _ _ _ _ _ _ _}.

Hint Extern 2 (StrongSetoid R∞) => eapply @pseudo_order_setoid : typeclass_instances.
Hint Extern 2 (StrongSetoid F) => eapply @strict_po_setoid : typeclass_instances.
Hint Extern 2 (?R ⊆ aff_ext_full ?R) => eapply @ae_subsetoid : typeclass_instances.
Hint Extern 2 (Morphism (F ⇒ F ⇒ F) (+)) => eapply @ae_plus_mor : typeclass_instances.
Hint Extern 2 (Morphism (F ⇒ F) (-)) => eapply @ae_negate_mor : typeclass_instances.
Hint Extern 2 (Strong_Binary_Morphism F F F (.*.)) => eapply @ae_mult_mor : typeclass_instances.
Hint Extern 2 (∞ ∊ F) => eapply @ae_inf_el_F : typeclass_instances.
Hint Extern 4 (- _ ∊ U) => eapply @ae_neg_undef : typeclass_instances.
Hint Extern 3 ( ∞ - ∞ ∊ U) => eexact ae_inf_minus_inf_r : typeclass_instances.
Hint Extern 3 (-∞ + ∞ ∊ U) => eexact ae_inf_minus_inf_l : typeclass_instances.
Hint Extern 4 (_ + _ ∊ U) => eapply @ae_plus_undef_l : typeclass_instances.
Hint Extern 4 (_ + _ ∊ U) => eapply @ae_plus_undef_r : typeclass_instances.
Hint Extern 3 (0 * ∞ ∊ U) => eexact ae_zero_mult_inf : typeclass_instances.
Hint Extern 3 (0 * -∞ ∊ U) => eexact ae_zero_mult_minf : typeclass_instances.
Hint Extern 3 (∞ * 0 ∊ U) => eexact ae_inf_mult_zero : typeclass_instances.
Hint Extern 3 (-∞ * 0 ∊ U) => eexact ae_minf_mult_zero : typeclass_instances.
Hint Extern 4 (_ * _ ∊ U) => eapply @ae_mult_undef_l : typeclass_instances.
Hint Extern 4 (_ * _ ∊ U) => eapply @ae_mult_undef_r : typeclass_instances.

Local Open Scope grp_scope.

Section field.
  Context {A} {F:@set A}
    `{Equiv A} `{Plus A} `{Mult A} `{Zero A} `{One A} `{Negate A} `{Inv A}
    `{UnEq A} `{Le A} `{Lt A} `{Infty A}.

  Context `{!AffExtFull F} `{!AffExt F}.

  Local Notation T := (aff_ext_full F).

  Class AffinelyExtendedField : Prop :=
  { ae_field :>> Field F
  ; ae_field_ae_ring :>> AffinelyExtendedRing F
  ; ae_inv_mor : Morphism (T ⇒ T) (⁻¹)
  ; ae_inv_inf : ∞⁻¹ = 0
  ; ae_inv_minf : (-∞)⁻¹ = 0
  ; ae_inv_0 : 0⁻¹ ∊ U
  ; ae_inv_undef : Closed (U ⇀ U) (⁻¹)
  }.
End field.

Arguments AffinelyExtendedField {_} F {_ _ _ _ _ _ _ _ _ _ _ _ _}.

Hint Extern 2 (Morphism (F ⇒ F) (inv)) => eapply @ae_inv_mor : typeclass_instances.
Hint Extern 4 (inv _ ∊ U) => eapply @ae_inv_undef : typeclass_instances.
Hint Extern 3 (inv 0 ∊ U) => eexact ae_inv_0 : typeclass_instances.

