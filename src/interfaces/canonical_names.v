Global Generalizable All Variables.
Global Set Automatic Introduction.
Global Set Automatic Coercions Import.

Require Import Streams.
Require Export Morphisms Setoid Program Unicode.Utf8 Utf8_core stdlib_hints.

Delimit Scope mc_scope with mc. 
Global Open Scope mc_scope.

Class Subset A := set_comp : A → Prop.
Delimit Scope subset_scope with subset.
Bind Scope subset_scope with Subset.

(* Element is a typeclass so that instances can be inferred.
   The notation is set up so that `{x ∊ S} works in a binder context.
 *)
Class Element `{S:Subset A} x := element : S x.
Notation "x ∊ S" := (Element (A:=_) (S:=S) x) (at level 70) : mc_scope.
Notation "(∊ S )" := (Element (S:=S)) (only parsing) : mc_scope.

Definition every A : Subset A := λ _, True.
Hint Extern 0 (_ ∊ (every _)) => eexact I : typeclass_instances.
(*Hint Extern 20 (Subset _) => eapply every : typeclass_instances.*)

Definition subset_to_type `(S:Subset A) := A.
(* Coercion subset_to_type: Subset >-> Sortclass. *)

(* The coercion permits the following hack to omit "every":
Notation nat := (every nat).
Check (0:nat).
Check (_ : 0 ∊ nat).

We would have prefered,

Coercion every: Sortclass >-> Subset.

But alas, this is not possible. (Sortclass cannot be the source of a coercion)
*)

Definition restrict_rel `(S:Subset A) (R:relation A): relation A := λ x y, (x ∊ S ∧ y ∊ S) ∧ R x y .
Notation " ( S , R ) " := (restrict_rel S (R%signature)) : signature_scope.

Class SubsetOf `(S:Subset A) (T:Subset A) := subset x `{x ∊ S} : x ∊ T.
(* Hint Extern 15 (_ ∊ ?T) => class_apply @subset : typeclass_instances. *)
Notation "S ⊆ T" := (SubsetOf S T) (at level 70) : mc_scope.
Notation "(⊆)" := (SubsetOf) (only parsing) : mc_scope.
Notation "( S ⊆)" := (SubsetOf S) (only parsing) : mc_scope.
Notation "(⊆ T )" := (λ S, S ⊆ T) (only parsing) : mc_scope.
Hint Extern 2 (?x ⊆ ?x) => reflexivity : typeclass_instances.
Hint Extern 2 (?x ⊆ ?y) => auto_trans : typeclass_instances.
Notation " ( S ,⊆) " := (restrict_rel S (⊆)) : signature_scope.

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
Notation "( S ,=)" := (restrict_rel S (=)) : signature_scope.

(* "≠" is sometimes standard inequality, sometimes apartness *)
Class UnEq A := uneq : relation A.
Notation "(≠)" := uneq (only parsing) : mc_scope.
Infix "≠":= uneq : type_scope.
Notation "( x ≠)" := (uneq x) (only parsing) : mc_scope.
Notation "(≠ x )" := (λ y, uneq y x) (only parsing) : mc_scope.
Notation "( S ,≠)" := (restrict_rel S (≠)) : signature_scope.
Typeclasses Transparent UnEq.

Class StandardUnEq `{Ae:Equiv A} {Aue:UnEq A} (S:Subset A) : Prop
  := standard_uneq x `{x ∊ S} y `{y ∊ S} : x ≠ y ↔ ¬ x = y.
Class TightApart `{Ae:Equiv A} {Aue:UnEq A} (S:Subset A) : Prop
  := tight_apart   x `{x ∊ S} y `{y ∊ S} : ¬ x ≠ y ↔ x = y.

Hint Extern 2 (?x = ?x) => reflexivity.
Hint Extern 2 (?x = ?y) => auto_symm.
Hint Extern 2 (?x = ?y) => auto_trans.

Definition subset_singleton `{Equiv A } S x : Subset _ := λ y, y ∊ S ∧ y = x.

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
Definition subset_equiv {T} : @Equiv (Subset T) := λ A B, ∀ x, x ∊ A ↔ x ∊ B.
Hint Extern 2 (Equiv (Subset _)) => eapply @subset_equiv : typeclass_instances.
Hint Extern 2 (Equiv (relation _)) => eapply @relation_equivalence : typeclass_instances.
Hint Extern 5 (Equiv (Equiv _)) => eapply @relation_equivalence : typeclass_instances.
Hint Extern 5 (Equiv (UnEq _)) => eapply @relation_equivalence : typeclass_instances.

Definition Fun   {A B}   (S:Subset A) (T:Subset B)              := A → B.
Definition BiFun {A B C} (S:Subset A) (T:Subset B) (U:Subset C) := A → B → C.
Infix "⇀" := Fun (at level 90, no associativity) : mc_scope.
Notation "S ⇀ T ⇀ U" := (BiFun S T U) (at level 90, T at next level) : mc_scope.

Definition compose {A B C S T U} (g:@Fun B C T U) (f:@Fun A B S T) := (λ x, g (f x)) : S ⇀ U.
Infix "∘" := compose : mc_scope.
Typeclasses Transparent compose.

Definition ext_equiv        {A B}   `{Equiv A} `{Equiv B}            S T   : @Equiv (@Fun A B S T)       := ((S,=)==>(T,=))%signature.
Definition binary_ext_equiv {A B C} `{Equiv A} `{Equiv B} `{Equiv C} S T U : @Equiv (@BiFun A B C S T U) := ((S,=)==>(T,=)==>(U,=))%signature.
Hint Extern 2 (@Equiv (Fun _ _)) => eapply @ext_equiv : typeclass_instances.
Hint Extern 2 (@Equiv (BiFun _ _ _)) => eapply @binary_ext_equiv : typeclass_instances.

Definition image     {A B} `{Equiv B} {X Y} (f:X ⇀ Y) (S:Subset A) : Subset B := λ y, y ∊ Y ∧ ∃ `{x ∊ S}, f x = y.
Definition inv_image {A B} `{Equiv A} {X Y} (f:X ⇀ Y) (T:Subset B) : Subset A := λ x, x ∊ X ∧ f x ∊ T.

Notation "f ⁺¹( T )" :=     (image f T) (at level 1, format "f ⁺¹( T )" ) : mc_scope.
Notation "f ⁻¹( T )" := (inv_image f T) (at level 1, format "f ⁻¹( T )") : mc_scope.

Class Cast A B := cast: A → B.
Arguments cast _ _ {Cast} _.
Notation "' x" := (cast _ _ x) (at level 20) : mc_scope.
Instance: Params (@cast) 3.
Typeclasses Transparent Cast.

(* Other canonically named relations/operations/constants: *)
Class SgOp    A := sg_op   : A → A → A.
Class MonUnit A := mon_unit: A.
Class Inv     A := inv     : A → A.
Class Plus    A := plus    : A → A → A.
Class Mult    A := mult    : A → A → A.
Class One     A := one     : A.
Class Zero    A := zero    : A.
Class Negate  A := negate  : A → A.
Typeclasses Transparent SgOp MonUnit Inv Plus Mult Zero One Negate.

Class Le A := le: relation A.
Class Lt A := lt: relation A.
Typeclasses Transparent Le Lt.

Instance: Params (@inv)    2.
Instance: Params (@mult)   2.
Instance: Params (@plus)   2.
Instance: Params (@negate) 2.
Instance: Params (@equiv)  2.
Instance: Params (@le)     2.
Instance: Params (@lt)     2.

Instance plus_is_sg_op    `{f : Plus   A}: SgOp A := f.
Instance mult_is_sg_op    `{f : Mult   A}: SgOp A := f.
Instance one_is_mon_unit  `{c : One    A}: MonUnit A := c.
Instance zero_is_mon_unit `{c : Zero   A}: MonUnit A := c.
Instance negate_is_inv    `{f : Negate A}: Inv A | 10 := f.

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
Notation "( S ,≤)" := (restrict_rel S (≤)) : signature_scope.

Infix "<" := lt : mc_scope.
Notation "(<)" := lt (only parsing) : mc_scope.
Notation "( x <)" := (lt x) (only parsing) : mc_scope.
Notation "(< x )" := (λ y, y < x) (only parsing) : mc_scope.
Notation "( S ,<)" := (restrict_rel S (<)) : signature_scope.

Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z) (at level 70, y at next level) : mc_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z) (at level 70, y at next level) : mc_scope.
Notation "x < y < z" := (x < y ∧ y < z) (at level 70, y at next level) : mc_scope.
Notation "x < y ≤ z" := (x < y ∧ y ≤ z) (at level 70, y at next level) : mc_scope.

Notation "{{ x }}" := (subset_singleton _ x) : mc_scope.
Notation "{{ x | S }}" := (subset_singleton S x) (only parsing) : mc_scope.

(* Haskell style! *)
Notation "(→)" := (λ x y, x → y) : mc_scope.
(* Notation "t $ r" := (t r) (at level 65, right associativity, only parsing) : mc_scope. *)
Notation "(∘)" := compose (only parsing) : mc_scope.

Hint Extern 2 (?x ≤ ?y) => reflexivity.
Hint Extern 4 (?x ≤ ?z) => auto_trans.
Hint Extern 4 (?x < ?z) => auto_trans.

(*
Class Inverse `(A → B) : Type := inverse: B → A.
Arguments inverse {A B} _ {Inverse} _.
*)
Class Inverse `(@Fun A B X Y) : Type := inverse: Fun Y X.
Arguments inverse {A B X Y} _ {Inverse} _.
Typeclasses Transparent Inverse.
Notation "f ⁻¹" := (inverse f) (at level 1, format "f ⁻¹") : mc_fun_scope. (* to co-exist with group inverse *)

Class AntiSymmetric {A} (eq le: relation A) : Prop := antisymmetry: ∀ x y, le x y → le y x → eq x y.
Arguments antisymmetry {A eq} le {AntiSymmetric} _ _ _ _.

Class SubRelation `(S:Subset A) (R1 R2 : relation A) : Prop :=
  subrelation_relative x `{x ∊ S} y `{y ∊ S} : R1 x y → R2 x y.

(** Define the [Prop]

        [Closed (S ==> T ==> ... ==> U) f]
 
    to mean
     
        [x ∊ S → y ∊ T → ... → f x y ... ∊ U.]
*)

(* Closed is just another name for Element *)
Class Closed {A} (S:Subset A) f := closed_prf : f ∊ S.
Definition closed {A B} (S:Subset A) (T:Subset B) : Subset (A → B) := λ f, ∀ x, x ∊ S → (f x) ∊ T.

Delimit Scope closed_sig_scope with closed_sig.

Arguments Closed {A}%type (S)%closed_sig _.
Arguments closed {A B}%type (S T)%closed_sig _.

Module ClosedNotations.

  Notation " S ==> T " := (@closed _ _ (S%closed_sig) (T%closed_sig))
    (right associativity, at level 55) : closed_sig_scope.

End ClosedNotations.

Export ClosedNotations.
