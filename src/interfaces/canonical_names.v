Global Generalizable All Variables.
Global Set Automatic Introduction.
Global Set Automatic Coercions Import.

Require Import Streams.
Require Export Morphisms Setoid Program Unicode.Utf8 Utf8_core stdlib_hints.

(* Equality *)
Class Equiv A := equiv: relation A.

(* Revert to transparency to allow conversions during unification. *)
Typeclasses Transparent Equiv.
Typeclasses Transparent compose flip.

(* We use this virtually everywhere, and so use "=" for it: *)
Infix "=" := equiv : type_scope.
Notation "(=)" := equiv (only parsing) : mc_scope.
Notation "( x =)" := (equiv x) (only parsing) : mc_scope.
Notation "(= x )" := (λ y, equiv y x) (only parsing) : mc_scope.

Class UnEq A := uneq : relation A.
Notation "(≠)" := uneq (only parsing) : mc_scope.
Infix "≠":= uneq : type_scope.
Notation "( x ≠)" := (uneq x) (only parsing) : mc_scope.
Notation "(≠ x )" := (λ y, uneq y x) (only parsing) : mc_scope.

Class StandardUnEq A `{Equiv A} `{UnEq A} := standard_uneq x y : x ≠ y ↔ ¬ x = y.

Delimit Scope mc_scope with mc. 
Global Open Scope mc_scope.

Hint Extern 2 (?x = ?x) => reflexivity.
Hint Extern 2 (?x = ?y) => auto_symm.
Hint Extern 2 (?x = ?y) => auto_trans.

(* Coq sometimes uses an incorrect DefaultRelation, so we override it. *)
Instance equiv_default_relation `{Equiv A} : DefaultRelation (=) | 3.

(* For Leibniz equality we use "≡", We do not define it as setoid equality with
low priority because sometimes we are interested in both setoid and Leibniz
equality on the same structure. *)
Infix "≡" := eq (at level 70, no associativity) : mc_scope.
Notation "(≡)" := eq (only parsing) : mc_scope.
Notation "( x ≡)" := (eq x) (only parsing) : mc_scope.
Notation "(≡ x )" := (λ y, eq y x) (only parsing) : mc_scope.
Notation "(≢)" := (λ x y, ¬x ≡ y) (only parsing) : mc_scope.
Notation "x ≢ y":= (¬x ≡ y) (at level 70, no associativity) : mc_scope.
Notation "( x ≢)" := (λ y, x ≢ y) (only parsing) : mc_scope.
Notation "(≢ x )" := (λ y, y ≢ x) (only parsing) : mc_scope.

(* Some common notions of equality *)
Definition ext_equiv `{Equiv A} `{Equiv B} : Equiv (A → B) := ((=) ==> (=))%signature.
Hint Extern 10 (Equiv (_ → _)) => apply @ext_equiv : typeclass_instances.
Hint Extern 10 (Equiv (relation _)) => apply @ext_equiv : typeclass_instances. (* Due to bug #2491 *)
(** Interestingly, most of the development works fine if this is defined as
  ∀ x, f x = g x.
However, in the end that version was just not strong enough for comfortable rewriting
in setoid-pervasive contexts. *)

Class Cast A B := cast: A → B.
Arguments cast _ _ {Cast} _.
Notation "' x" := (cast _ _ x) (at level 20) : mc_scope.
Instance: Params (@cast) 3.
Typeclasses Transparent Cast.

(* Other canonically named relations/operations/constants: *)
Class SgOp A := sg_op: A → A → A.
Class MonUnit A := mon_unit: A.
Class Inv A := inv : A → A.
Class Plus A := plus: A → A → A.
Class Mult A := mult: A → A → A.
Class One A := one: A.
Class Zero A := zero: A.
Class Negate A := negate: A → A.
Typeclasses Transparent SgOp MonUnit Inv Plus Mult Zero One Negate.

Class Singleton A B := singleton: A → B.
Typeclasses Transparent Singleton.

Class Le A := le: relation A.
Class Lt A := lt: relation A.
Typeclasses Transparent Le Lt.

Instance: Params (@inv) 1.
Instance: Params (@mult) 2.
Instance: Params (@plus) 2.
Instance: Params (@negate) 1.
Instance: Params (@equiv) 2.
Instance: Params (@le) 2.
Instance: Params (@lt) 2.

Instance plus_is_sg_op `{f : Plus A} : SgOp A := f.
Instance mult_is_sg_op `{f : Mult A} : SgOp A := f.
Instance one_is_mon_unit `{c : One A} : MonUnit A := c.
Instance zero_is_mon_unit `{c : Zero A} : MonUnit A := c.
Instance negate_is_inv `{f : Negate A} : Inv A | 5 := f.

(* Notations: *)
Infix "&" := sg_op (at level 50, left associativity) : mc_scope.
Notation "(&)" := sg_op (only parsing) : mc_scope.
Notation "( x &)" := (sg_op x) (only parsing) : mc_scope.
Notation "(& x )" := (λ y, y & x) (only parsing) : mc_scope.

Notation "x ⁻¹" := (inv x) (at level 1, format "x ⁻¹") : grp_scope. (* to co-exist with function inverse *)
Notation "(⁻¹)" := inv (only parsing) : mc_scope.

Infix "+" := plus : mc_scope.
Notation "(+)" := plus (only parsing) : mc_scope.
Notation "( x +)" := (plus x) (only parsing) : mc_scope.
Notation "(+ x )" := (λ y, y + x) (only parsing) : mc_scope.

Infix "*" := mult : mc_scope.
(* We don't add "( * )", "( * x )" and "( x * )" notations because they conflict with comments. *)
Notation "( x *.)" := (mult x) (only parsing) : mc_scope.
Notation "(.*.)" := mult (only parsing) : mc_scope.
Notation "(.* x )" := (λ y, y * x) (only parsing) : mc_scope.

Notation "- x" := (negate x) : mc_scope.
Notation "(-)" := negate (only parsing) : mc_scope.
Notation "x - y" := (x + -y) : mc_scope.

Notation "x / y" := (x * inv y) : mc_scope.

Notation "0" := zero : mc_scope.
Notation "1" := one : mc_scope.
Notation "2" := (1 + 1) : mc_scope.
Notation "3" := (1 + (1 + 1)) : mc_scope.
Notation "4" := (1 + (1 + (1 + 1))) : mc_scope.
Notation "- 1" := (-(1)) : mc_scope.
Notation "- 2" := (-(2)) : mc_scope.
Notation "- 3" := (-(3)) : mc_scope.
Notation "- 4" := (-(4)) : mc_scope.

Infix "≤" := le : mc_scope.
Notation "(≤)" := le (only parsing) : mc_scope.
Notation "( x ≤)" := (le x) (only parsing) : mc_scope.
Notation "(≤ x )" := (λ y, y ≤ x) (only parsing) : mc_scope.

Infix "<" := lt : mc_scope.
Notation "(<)" := lt (only parsing) : mc_scope.
Notation "( x <)" := (lt x) (only parsing) : mc_scope.
Notation "(< x )" := (λ y, y < x) (only parsing) : mc_scope.

Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z) (at level 70, y at next level) : mc_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z) (at level 70, y at next level) : mc_scope.
Notation "x < y < z" := (x < y ∧ y < z) (at level 70, y at next level) : mc_scope.
Notation "x < y ≤ z" := (x < y ∧ y ≤ z) (at level 70, y at next level) : mc_scope.

Notation "{{ x }}" := (singleton x) : mc_scope.

(* Haskell style! *)
Notation "(→)" := (λ x y, x → y) : mc_scope.
Notation "t $ r" := (t r) (at level 65, right associativity, only parsing) : mc_scope.
Notation "(∘)" := compose (only parsing) : mc_scope.

Hint Extern 2 (?x ≤ ?y) => reflexivity.
Hint Extern 4 (?x ≤ ?z) => auto_trans.
Hint Extern 4 (?x < ?z) => auto_trans.

Class AntiSymmetric {A} (eq le: relation A) : Prop := antisymmetry: ∀ x y, le x y → le y x → eq x y.
Arguments antisymmetry {A eq} le {AntiSymmetric} _ _ _ _.

