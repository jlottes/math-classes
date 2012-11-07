Require Import
  abstract_algebra.

Class Pow A B := pow : A → B → A.
Infix "^" := pow.
Notation "(^)" := pow (only parsing).
Notation "( x ^)" := (pow x) (only parsing).
Notation "(^ n )" := (λ x, x ^ n) (only parsing).
Instance: Params (@pow) 3.

(* If we make [nat_pow_proper] a subclass, Coq is unable to find it.
However, if we make a global instance in theory.nat_pow, it works? *)
Class NatPowSpec {A B} R N (pw : Pow A B) `{Equiv A} `{Equiv B} `{One A} `{Mult A} `{Zero B} `{One B} `{Plus B} :=
  { nat_pow_proper : Morphism (R ⇒ N ⇒ R) (^)
  ; nat_pow_0 x `{x ∊ R} : x ^ 0 = 1
  ; nat_pow_S x `{x ∊ R} n `{n ∊ N} : x ^ (1 + n) = x * x ^ n
  }.

(* This version of the spec does not require F to have decidable equality. *)
Class IntPowSpec {A B} F Z (pow : Pow A B) `{Equiv A} `{Equiv B} `{UnEq A} `{Le B} `{Lt B} `{Zero A} `{One A} `{Mult A} `{Zero B} `{One B} `{Plus B} `{Negate B} :=
  { int_pow_nat_spec :>> NatPowSpec F Z⁺ pow
  ; int_pow_neg_closed : Closed (F ₀ ⇀ Z₋ ⇀ F) (^)
  ; int_pow_neg x `{x ∊ F ₀} n `{n ∊ Z₋} : x ^ n * (x ^ (-n)) = 1
  }.

Hint Extern 5 (Morphism _ (^)  ) => class_apply @nat_pow_proper : typeclass_instances.

Class ShiftL A B := shiftl: A → B → A.
Infix "≪" := shiftl (at level 33, left associativity).
Notation "(≪)" := shiftl (only parsing).
Notation "( x ≪)" := (shiftl x) (only parsing).
Notation "(≪ n )" := (λ x, x ≪ n) (only parsing).
Instance: Params (@shiftl) 3.

Class ShiftLSpec {A B} R N (sl : ShiftL A B) `{Equiv A} `{Equiv B} `{One A} `{Plus A} `{Mult A} `{Zero B} `{One B} `{Plus B} :=
  { shiftl_proper : Morphism (R ⇒ N ⇒ R) (≪)
  ; shiftl_0 : RightIdentity (≪) 0 R
  ; shiftl_S x `{x ∊ R} n `{n ∊ N} : x ≪ (1 + n) = 2 * x ≪ n
  }.
Arguments shiftl_0 {A B R N sl _ _ _ _ _ _ _ _ ShiftLSpec} _ {_}.
Hint Extern 5 (Morphism _ (≪) ) => eapply @shiftl_proper : typeclass_instances.
Hint Extern 5 (RightIdentity (≪) _ _) => eapply @shiftl_0 : typeclass_instances.

Class ShiftR A B := shiftr: A → B → A.
Infix "≫" := shiftr (at level 33, left associativity).
Notation "(≫)" := shiftr (only parsing).
Instance: Params (@shiftr) 3.

Class ShiftRSpec {A B} R N (sr : ShiftR A B) `{Equiv A} `{Equiv B} `{One A} `{Plus A} `{Mult A} `{Zero B} `{One B} `{Plus B} :=
  { shiftr_proper : Morphism (R ⇒ N ⇒ R) (≫)
  ; shiftr_0 :> RightIdentity (≫) 0 R
  ; shiftr_S x `{x ∊ R} n `{n ∊ N} : x ≫ n = 2 * x ≫ (1 + n) ∨ x ≫ n = 2 * x ≫ (1 + n) + 1
  }.
Arguments shiftr_0 {A B R N sr _ _ _ _ _ _ _ _ ShiftRSpec} _ {_}.
Hint Extern 5 (Morphism _ (≫) ) => eapply @shiftr_proper : typeclass_instances.
Hint Extern 5 (RightIdentity (≫) _ _) => eapply @shiftr_0 : typeclass_instances.

(*
Class DivEuclid A := div_euclid : A → A → A.
Class ModEuclid A := mod_euclid : A → A → A.
Infix "`div`" := div_euclid (at level 35).
Notation "(`div`)" := div_euclid (only parsing).
Notation "( x `div`)" := (div_euclid x) (only parsing).
Notation "(`div` y )" := (λ x, x `div` y) (only parsing).
Infix "`mod`" := mod_euclid (at level 40).
Notation "(`mod` )" := mod_euclid (only parsing).
Notation "( x `mod`)" := (mod_euclid x) (only parsing).
Notation "(`mod` y )" := (λ x, x `mod` y) (only parsing).
Instance: Params (@div_euclid) 2.
Instance: Params (@mod_euclid) 2.

Class EuclidSpec A (d : DivEuclid A) (m : ModEuclid A) `{Equiv A} `{Le A} `{Lt A} `{Zero A} `{Plus A} `{Mult A} := {
  div_proper : Proper ((=) ==> (=) ==> (=)) (`div`) ;
  mod_proper : Proper ((=) ==> (=) ==> (=)) (`mod`) ;
  div_mod : ∀ x y, y ≠ 0 → x = y * x `div` y + x `mod` y ;
  mod_rem : ∀ x y, y ≠ 0 → 0 ≤ x `mod` y < y ∨ y < x `mod` y ≤ 0 ;
  div_0 : ∀ x, x `div` 0 = 0 ;
  mod_0 : ∀ x, x `mod` 0 = 0
}.
*)

Class CutMinus A := cut_minus : A → A → A.
Infix "∸" := cut_minus (at level 50, left associativity).
Notation "(∸)" := cut_minus (only parsing).
Notation "( x ∸)" := (cut_minus x) (only parsing).
Notation "(∸ y )" := (λ x, x ∸ y) (only parsing).
Instance: Params (@cut_minus) 2.

Class CutMinusSpec {A} N (cm : CutMinus A) `{Equiv A} `{Zero A} `{Plus A} `{Le A} :=
  { cut_minus_proper : Morphism (N ⇒ N ⇒ N) (∸)
  ; cut_minus_le x `{x ∊ N} y `{y ∊ N} : y ≤ x → x ∸ y + y = x
  ; cut_minus_0 x `{x ∊ N} y `{y ∊ N} : x ≤ y → x ∸ y = 0
  }.
Hint Extern 0 (Morphism _ (∸) ) => eapply @cut_minus_proper : typeclass_instances.
