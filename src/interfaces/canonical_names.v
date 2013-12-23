Global Generalizable All Variables.
Global Set Automatic Introduction.
Global Set Automatic Coercions Import.

Require Import Streams.
Require Export Morphisms Setoid Program Unicode.Utf8 Utf8_core stdlib_hints.

Delimit Scope mc_scope with mc. 
Global Open Scope mc_scope.

(** remove printing * *)
(** remove printing => *)
(** remove printing exists *)
(** remove printing forall *)

Class set {A} := set_comp : A → Prop.
Delimit Scope set_scope with set.
Bind Scope set_scope with set.

(** Element is a typeclass so that instances can be inferred.
    The notation is set up so that `{x ∊ S} works in a binder context.
 *)
Class Element `{S:set} x := element : S x.
Notation "x ∊ S" := (Element (A:=_) (S:=S) x) (at level 70) : mc_scope.
Notation "(∊ S )" := (Element (S:=S)) (only parsing) : mc_scope.

Class Inhabited `(X:set) := inhabited : ∃ x, x ∊ X.
Arguments inhabited {_} X {_}.

Definition every A : set := λ (_:A), True.
Hint Extern 0 (_ ∊ (every _)) => eexact I : typeclass_instances.

Definition prod_set {A B} (S:set) (T:set) : set
  := λ (x:A*B), fst x ∊ S ∧ snd x ∊ T.
Infix "*" := prod_set : set_scope.
Notation "()" := (every ()) : set_scope.

Definition elt_type `(S:@set A) := A.
Coercion elt_type: set >-> Sortclass.
Typeclasses Transparent elt_type.

Definition restrict_rel `(S:set) (R:relation _): relation _ := λ x y, (x ∊ S ∧ y ∊ S) ∧ R x y .

Class Subset `(S:set) T := subset x `{x ∊ S} : x ∊ T.

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

(* "≠" is not necessarily a denial inequality. *)
Class UnEq A := uneq : relation A.
Notation "(≠)" := uneq (only parsing) : mc_scope.
Infix "≠":= uneq : type_scope.
Notation "( x ≠)" := (uneq x) (only parsing) : mc_scope.
Notation "(≠ x )" := (λ y, uneq y x) (only parsing) : mc_scope.
Notation "( S ,≠)" := (restrict_rel S (≠)) : signature_scope.
Typeclasses Transparent UnEq.

Class DenialInequality `{Ae:Equiv A} {Aue:UnEq A} S : Prop
  := denial_inequality x `{x ∊ S} y `{y ∊ S} : x ≠ y ↔ ¬ x = y.
Class TightApart `{Ae:Equiv A} {Aue:UnEq A} S : Prop
  := tight_apart   x `{x ∊ S} y `{y ∊ S} : ¬ x ≠ y ↔ x = y.

(*
Hint Extern 2 (?x = ?x) => reflexivity.
Hint Extern 2 (?x = ?y) => auto_symm.
Hint Extern 2 (?x = ?y) => auto_trans.
*)

Definition singleton `(S:set) `{Equiv _} x : set := λ y, y ∊ S ∧ y = x.

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
Definition set_equiv {T} : Equiv (@set T) := λ A B, ∀ x, x ∊ A ↔ x ∊ B.
Hint Extern 2 (Equiv set) => eapply @set_equiv : typeclass_instances.
Hint Extern 2 (Equiv (relation _)) => eapply @relation_equivalence : typeclass_instances.
Hint Extern 5 (Equiv (Equiv _)) => eapply @relation_equivalence : typeclass_instances.
Hint Extern 5 (Equiv (UnEq _)) => eapply @relation_equivalence : typeclass_instances.

Definition prod_equiv `{Equiv A} `{Equiv B} : Equiv (A * B) :=
  λ x y, fst x = fst y ∧ snd x = snd y.
Definition prod_uneq `{UnEq A} `{UnEq B} : UnEq (A * B) :=
  λ x y, fst x ≠ fst y ∨ snd x ≠ snd y.

Hint Extern 10 (Equiv (_ * _)) => class_apply @prod_equiv : typeclass_instances.
Hint Extern 10 (UnEq  (_ * _)) => class_apply @prod_uneq  : typeclass_instances.
Hint Extern 10 (Equiv (elt_type (_ * _))) => class_apply @prod_equiv : typeclass_instances.
Hint Extern 10 (UnEq  (elt_type (_ * _))) => class_apply @prod_uneq  : typeclass_instances.


(** Morphisms between [Subset]s. We define the [Subset] [ X ⇀ Y ⇀ ... ⇀ Z ] so
 that a function [f] is a member when
  [x ∊ X → y ∊ Y → ... → f x y ... ∊ Z.]
We introduce a typeclass [Closed] where [Closed (X ⇀ Y ⇀ ... ⇀ Z) f]
is just a synonym for [f ∊ (X ⇀ Y ⇀ ... ⇀ Z)]. The idea is to isolate such instances
from more general [Element] instances, to speed instance resolution.

Also, because of the implicit coercion [elt_type] of a [Subset] to its underlying [Type],
we can write [ f : X ⇀ Y ⇀ ... ⇀ Z ]. While the [Subset]s are discarded by the coercion,
they can be used for implicit argument resolution, essentially acting as "hints" that
the domains and codomain of [f] are the specified [Subset]s.
*)

Definition closed_fun {A B} X Y : @set (A → B) := λ f, ∀ `{x ∊ X}, f x ∊ Y.
Infix "⇀" := closed_fun (at level 65, right associativity) : mc_scope.
Class Closed `(S:set) f := closed_prf : f ∊ S.
Hint Extern 0 (_ ∊ _ ⇀ _) => eapply @closed_prf : typeclass_instances.

Definition compose `{X:set} `{Y:set} `{Z:set} (g:Y ⇀ Z) (f:X ⇀ Y) : X ⇀ Z  := λ x, g (f x).
Infix "∘" := compose : mc_scope.
Notation "( f ∘)" := (λ g, f ∘ g) (only parsing) : mc_scope.
Notation "(∘ f )" := (λ g, g ∘ f) (only parsing) : mc_scope.
Typeclasses Transparent compose.

Definition uncurry `{X:set} `{Y:set} `{Z:set} (f:X ⇀ Y ⇀ Z) : X * Y ⇀ Z := 
  λ x, f (fst x) (snd x).

Definition curry `{X:set} `{Y:set} `{Z:set} (f:X * Y ⇀ Z) : X ⇀ Y ⇀ Z := λ x y, f (x,y).

Definition ext_equiv `{X:set} `{Y:set} `{Equiv X} `{Equiv Y}
  : Equiv (X ⇀ Y) := ((X,=)==>(Y,=))%signature.
Hint Extern 2 (Equiv (elt_type (?X ⇀ ?Y))) => eapply (ext_equiv (X:=X) (Y:=Y)) : typeclass_instances.
Hint Extern 5 (Equiv (_ → _)) => eapply @ext_equiv : typeclass_instances.

Definition strong_ext_equiv `{X:set} `{Y:set} `{UnEq X} `{UnEq Y} : Equiv (X ⇀ Y)
  := λ f g, ∀ x `{x ∊ X} y `{y ∊ X}, f x ≠ g y → x ≠ y.

(*
Definition TypedSubset := { A : Type & @Subset A }.
Definition unpack_subset : ∀ S : TypedSubset, @Subset (projT1 S) := λ S, projT2 S.
Definition pack_subset `(S:Subset A) : TypedSubset := existT (@Subset) A S.
Coercion unpack_subset: TypedSubset >-> Subset.
*)

Definition image     `{X:set} `{Y:set} `{Equiv Y} (f:X ⇀ Y) S : set := λ y, y ∊ Y ∧ ∃ `{x ∊ S}, f x = y.
Definition inv_image `{X:set} `{Y:set}            (f:X ⇀ Y) T : set := λ x, x ∊ X ∧ f x ∊ T.

Notation "f ⁺¹( T )" :=     (image f T) (at level 1, format "f ⁺¹( T )") : mc_scope.
Notation "f ⁻¹( T )" := (inv_image f T) (at level 1, format "f ⁻¹( T )") : mc_scope.

Class Cast `(S:set) `(T:set) := cast: S ⇀ T.
Arguments cast {_} S {_} T {Cast} _.
Notation "' x" := (cast _ _ x) (at level 20) : mc_scope.
Notation "(')" := (cast _ _) (only parsing) : mc_scope.
Instance: Params (@cast) 5.
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

Class Meet A := meet: A → A → A.
Class Join A := join: A → A → A.
Class Top A := top: A.
Class Bottom A := bottom: A.
Typeclasses Transparent Meet Join Top Bottom.

Class Tilde A := tilde : A → A.
Typeclasses Transparent tilde.

Class Le A := le: relation A.
Class Lt A := lt: relation A.
Typeclasses Transparent Le Lt.

Class Infty A := infty : A.
Typeclasses Transparent Infty.

Class Abs A := abs : A → A.
Typeclasses Transparent Abs.

Instance: Params (@inv)    2.
Instance: Params (@mult)   2.
Instance: Params (@plus)   2.
Instance: Params (@negate) 2.
Instance: Params (@equiv)  2.
Instance: Params (@le)     2.
Instance: Params (@lt)     2.
Instance: Params (@meet)   2.
Instance: Params (@join)   2.
Instance: Params (@tilde)  2.
Instance: Params (@abs)    2.

Instance plus_is_sg_op      `{f : Plus   A}: SgOp A | 5 := f.
Instance mult_is_sg_op      `{f : Mult   A}: SgOp A | 5 := f.
Instance one_is_mon_unit    `{c : One    A}: MonUnit A | 5 := c.
Instance zero_is_mon_unit   `{c : Zero   A}: MonUnit A | 5 := c.
Instance negate_is_inv      `{f : Negate A}: Inv A | 10 := f.
Instance meet_is_sg_op      `{f : Meet   A}: SgOp A | 5 := f.
Instance join_is_sg_op      `{f : Join   A}: SgOp A | 5 := f.
Instance top_is_mon_unit    `{s : Top    A}: MonUnit A | 5 := s.
Instance bottom_is_mon_unit `{s : Bottom A}: MonUnit A | 5 := s.

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

Notation "⊤" := top : mc_scope.
Notation "⊥" := bottom : mc_scope.

Infix "⊓" := meet (at level 50, left associativity) : mc_scope.
Notation "(⊓)" := meet (only parsing) : mc_scope.
Notation "( X ⊓)" := (meet X) (only parsing) : mc_scope.
Notation "(⊓ X )" := (λ Y, Y ⊓ X) (only parsing) : mc_scope.

Infix "⊔" := join (at level 50, left associativity) : mc_scope.
Notation "(⊔)" := join (only parsing) : mc_scope.
Notation "( X ⊔)" := (join X) (only parsing) : mc_scope.
Notation "(⊔ X )" := (λ Y, Y ⊔ X) (only parsing) : mc_scope.

Notation "∼ x" := (tilde x) (at level 35, right associativity) : mc_scope.
Notation "(∼)" := tilde (only parsing) : mc_scope.

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

Notation "∞" := infty : mc_scope.

Notation "{{ x }}" := (singleton _ x) : mc_scope.
Notation "{{ x | S }}" := (singleton S x) (only parsing) : mc_scope.

Notation "| x |" := (abs x) (at level 50, format "| x |") : mc_abs_scope.
Notation "|·|" := abs (only parsing) : mc_abs_scope.

(* Haskell style! *)
Notation "(→)" := (λ x y, x → y) : mc_scope.
(* Notation "t $ r" := (t r) (at level 65, right associativity, only parsing) : mc_scope. *)
Notation "(∘)" := compose (only parsing) : mc_scope.

(*
Hint Extern 2 (?x ≤ ?y) => reflexivity.
Hint Extern 4 (?x ≤ ?z) => auto_trans.
Hint Extern 4 (?x < ?z) => auto_trans.
*)

Class Inverse `{X:set} `{Y:set} (f:X ⇀ Y) : Type := inverse: Y ⇀ X.
Arguments inverse {_ _ _ _} f {Inverse} _.
Typeclasses Transparent Inverse.
Notation "f ⁻¹" := (inverse f) (at level 1, format "f ⁻¹") : mc_fun_scope. (* to co-exist with group inverse *)

Definition set_empty        {A} : Bottom (@set A) := λ x, False.
Definition set_intersection {A} : Meet (@set A) := λ S T x, x ∊ S ∧ x ∊ T.
Definition set_union        {A} : Join (@set A) := λ S T x, x ∊ S ∨ x ∊ T.
Hint Extern 2 (Bottom set) => eapply @set_empty : typeclass_instances.
Hint Extern 2 (Meet set) => eapply @set_intersection : typeclass_instances.
Hint Extern 2 (Join set) => eapply @set_union : typeclass_instances.
Hint Extern 10 (Top set) => eapply @every : typeclass_instances.
Hint Extern 10 (Meet (_ → Prop)) => eapply @set_intersection : typeclass_instances.
Hint Extern 10 (Join (_ → Prop)) => eapply @set_union : typeclass_instances.

Class AntiSymmetricT {A} (eq le: relation A) : Prop := antisymmetry_t: ∀ x y, le x y → le y x → eq x y.
Arguments antisymmetry_t {A eq} le {AntiSymmetricT} _ _ _ _.

Class SubRelation `(S:set) (R₁ R₂ : relation _) : Prop := subrel x `{x ∊ S} y `{y ∊ S} : R₁ x y → R₂ x y.
