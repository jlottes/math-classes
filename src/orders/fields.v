Require Import
  abstract_algebra interfaces.orders theory.setoids theory.rings theory.fields.
Require Export
  orders.rings.

Local Open Scope grp_scope. (* notation for inverse *)

Section contents.
Context `{Field (F:=F)} `{Le _} `{Lt _} `{!FullPseudoSemiRingOrder F}.

Existing Instance closed_range.

Instance pos_mult_inv_compat : Closed (F₊ ⇀ F₊) (⁻¹).
Proof. intros x ?. split. apply _.
  apply (strictly_order_reflecting (x *.) _ _).
  rewrite_on F -> (mult_0_r x), (field_inv_r x).
  solve_propholds.
Qed.

Instance neg_mult_inv_compat : Closed (F₋ ⇀ F₋) (⁻¹).
Proof. intros x ?. apply (negate_pos_neg _).
  rewrite <- (F $ mult_inv_negate _). apply _.
Qed.

Let ge_pos_pos x `{x ∊ F} y `{y ∊ F₊} : y ≤ x → x ∊ F₊.
Proof. split. apply _. apply (lt_le_trans 0 y x); firstorder. Qed.

Lemma flip_le_mult_inv x `{x ∊ F} y `{y ∊ F₊} : y ≤ x → x⁻¹ ≤ y⁻¹.
Proof. intro E. pose proof ge_pos_pos x y E.
  apply (order_reflecting (x *.) _ _). rewrite_on F -> (field_inv_r x).
  apply (order_reflecting (.* y) _ _).
  rewrite (F $ mult_1_l y), <- (F $ associativity (.*.) _ _ _), (F $ commutativity (.*.) _ y).
  now rewrite_on F -> (field_inv_r y), (mult_1_r x).
Qed.

Lemma flip_le_mult_inv_l x `{x ∊ F} y `{y ∊ F₊} : y⁻¹ ≤ x → x⁻¹ ≤ y.
Proof. intro E. pose proof ge_pos_pos _ _ E.
  rewrite <- (F $ mult_inv_involutive y).
  exact (flip_le_mult_inv _ _ E).
Qed.

Lemma flip_le_mult_inv_r x `{x ∊ F ₀} y `{y ∊ F₊} : y ≤ x⁻¹ → x ≤ y⁻¹.
Proof. intro E.
  rewrite <- (F $ mult_inv_involutive x).
  exact (flip_le_mult_inv _ _ E).
Qed.

Lemma mult_inv_le_cancel_l z `{z ∊ F₊} x `{x ∊ F} y `{y ∊ F} : x ≤ y * z ↔ x / z ≤ y.
Proof. split; intro E.
+ apply (order_reflecting (.* z) _ _).
  now rewrite <- (F $ associativity _ _ _ _), (F $ field_inv_l _), (F $ mult_1_r _).
+ rewrite <-(F $ mult_1_r _), <-(F $ field_inv_l z), (F $ associativity _ _ _ _).
  now apply (order_preserving (.* z) _ _).
Qed.

Lemma mult_inv_le_cancel_r z `{z ∊ F₊} x `{x ∊ F} y `{y ∊ F} : x * z ≤ y ↔ x ≤ y / z.
Proof. split; intro E.
+ apply (order_reflecting (.* z) _ _).
  now rewrite <- (F $ associativity _ _ _ _), (F $ field_inv_l _), (F $ mult_1_r _).
+ rewrite <-(F $ mult_1_r y), <-(F $ field_inv_l z), (F $ associativity _ _ _ _).
  now apply (order_preserving (.* z) _ _).
Qed.

Lemma mult_inv_le_cancel_both a `{a ∊ F} b `{b ∊ F₊} c `{c ∊ F} d `{d ∊ F₊}
    : a * d ≤ b * c ↔ a/b ≤ c/d.
Proof. rewrite (mult_inv_le_cancel_r _ _ _).
  rewrite <-(F $ associativity _ _ _ _), (F $ commutativity _ b _).
  exact (mult_inv_le_cancel_l _ _ _).
Qed.

Let gt_pos_pos x `{x ∊ F} y `{y ∊ F₊} : y < x → x ∊ F₊.
Proof. split. apply _. subtransitivity y. firstorder. Qed.

Lemma flip_lt_mult_inv x `{x ∊ F} y `{y ∊ F₊} : y < x → x⁻¹ < y⁻¹.
Proof. intro E. pose proof gt_pos_pos x y E.
  apply (strictly_order_reflecting (x *.) _ _). rewrite_on F -> (field_inv_r x).
  apply (strictly_order_reflecting (.* y) _ _).
  rewrite (F $ mult_1_l y), <- (F $ associativity (.*.) _ _ _), (F $ commutativity (.*.) _ y).
  now rewrite_on F -> (field_inv_r y), (mult_1_r x).
Qed.

Lemma flip_lt_mult_inv_l x `{x ∊ F} y `{y ∊ F₊} : y⁻¹ < x → x⁻¹ < y.
Proof. intro E. pose proof gt_pos_pos _ _ E.
  rewrite <- (F $ mult_inv_involutive y).
  exact (flip_lt_mult_inv _ _ E).
Qed.

Lemma flip_lt_mult_inv_r x `{x ∊ F ₀} y `{y ∊ F₊} : y < x⁻¹ → x < y⁻¹.
Proof. intro E.
  rewrite <- (F $ mult_inv_involutive x).
  exact (flip_lt_mult_inv _ _ E).
Qed.

Lemma mult_inv_lt_cancel_l z `{z ∊ F₊} x `{x ∊ F} y `{y ∊ F} : x < y * z ↔ x / z < y.
Proof. split; intro E.
+ apply (strictly_order_reflecting (.* z) _ _).
  now rewrite <- (F $ associativity _ _ _ _), (F $ field_inv_l _), (F $ mult_1_r _).
+ rewrite <-(F $ mult_1_r _), <-(F $ field_inv_l z), (F $ associativity _ _ _ _).
  now apply (strictly_order_preserving (.* z) _ _).
Qed.

Lemma mult_inv_lt_cancel_r z `{z ∊ F₊} x `{x ∊ F} y `{y ∊ F} : x * z < y ↔ x < y / z.
Proof. split; intro E.
+ apply (strictly_order_reflecting (.* z) _ _).
  now rewrite <- (F $ associativity _ _ _ _), (F $ field_inv_l _), (F $ mult_1_r _).
+ rewrite <-(F $ mult_1_r y), <-(F $ field_inv_l z), (F $ associativity _ _ _ _).
  now apply (strictly_order_preserving (.* z) _ _).
Qed.

Lemma mult_inv_lt_cancel_both a `{a ∊ F} b `{b ∊ F₊} c `{c ∊ F} d `{d ∊ F₊}
    : a * d < b * c ↔ a/b < c/d.
Proof. rewrite (mult_inv_lt_cancel_r _ _ _).
  rewrite <-(F $ associativity _ _ _ _), (F $ commutativity _ b _).
  exact (mult_inv_lt_cancel_l _ _ _).
Qed.
End contents.
Hint Extern 4 (_⁻¹ ∊ _₊) => eapply @pos_mult_inv_compat : typeclass_instances.
Hint Extern 4 (_⁻¹ ∊ _₋) => eapply @neg_mult_inv_compat : typeclass_instances.
Hint Extern 4 (_⁻¹ ∊ _⁺) => eapply @pos_nonneg : typeclass_instances.
Hint Extern 4 (_⁻¹ ∊ _⁻) => eapply @neg_nonpos : typeclass_instances.

