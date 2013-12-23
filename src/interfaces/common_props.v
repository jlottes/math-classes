Require Import canonical_names.

(*
Class AntiSymmetric {A} (eq le: relation A) : Prop := antisymmetry: ∀ x y, le x y → le y x → eq x y.
Arguments antisymmetry {A eq} le {AntiSymmetric} _ _ _ _.

Class SubRelation `(S:Subset) (R1 R2 : relation _) : Prop :=
  subrelation_relative x `{x ∊ S} y `{y ∊ S} : R1 x y → R2 x y.
*)

Section common_subsets.
  Context `{Aue:UnEq A} {Ale: Le A} {Alt: Lt A} {Azero:Zero A} (R:@set A).

  Definition NonZero : set := R ⊓ (≠ 0).
  Definition NonNeg  : set := R ⊓ (0 ≤).
  Definition Pos     : set := R ⊓ (0 <).
  Definition NonPos  : set := R ⊓ (≤ 0).
  Definition Neg     : set := R ⊓ (< 0).
End common_subsets.

Notation "R ₀" := (NonZero R) (at level 20, no associativity) : mc_scope.
Notation "R ⁺" := (NonNeg  R) (at level  1, no associativity, format "R ⁺") : mc_scope.
Notation "R ₊" := (Pos     R) (at level  1, no associativity, format "R ₊") : mc_scope.
Notation "R ⁻" := (NonPos  R) (at level  1, no associativity, format "R ⁻") : mc_scope.
Notation "R ₋" := (Neg     R) (at level  1, no associativity, format "R ₋") : mc_scope.

Notation ReflexiveT   := Reflexive.
Notation IrreflexiveT := Irreflexive.
Notation SymmetricT   := Symmetric.
Notation TransitiveT  := Transitive.
Notation EquivalenceT := Equivalence.

Class Reflexive    `(S:set) (R : relation _) : Prop := reflexivity    x `{x ∊ S} : R x x.
Class Irreflexive  `(S:set) (R : relation _) : Prop := irreflexivity  x `{x ∊ S} : ¬ R x x.
Class Symmetric    `(S:set) (R : relation _) : Prop := symmetry       x `{x ∊ S} y `{y ∊ S} : R x y → R y x.
Class Transitive   `(S:set) (R : relation _) : Prop := transitivity   x `{x ∊ S} y `{y ∊ S} z `{z ∊ S} : R x y → R y z → R x z.
Class CoTransitive `(S:set) (R : relation _) : Prop := cotransitivity `{x ∊ S} `{y ∊ S} (_:R x y) z `{z ∊ S} : R x z ∨ R z y.

Arguments irreflexivity {_ S} R {Irreflexive} x {_} _.

Class Equivalence `(S:set) (R : relation _) : Prop :=
  { equiv_reflexive  : Reflexive  S R
  ; equiv_symmetric  : Symmetric  S R
  ; equiv_transitive : Transitive S R
  }.
Hint Extern 2 (Reflexive _ _)  => eapply @equiv_reflexive : typeclass_instances.
Hint Extern 2 (Symmetric _ _)  => eapply @equiv_symmetric : typeclass_instances.
Hint Extern 2 (Transitive _ _) => eapply @equiv_transitive : typeclass_instances.


Class Apartness `(S:set) (R : relation _) : Prop :=
  { apart_irreflexive  :> Irreflexive  S R
  ; apart_symmetric    :> Symmetric    S R
  ; apart_cotransitive :> CoTransitive S R
  }.

Class AntiSymmetric `{Ae:Equiv A} S (R: relation A) : Prop := antisymmetry `{x ∊ S} `{y ∊ S} : R x y → R y x → x = y.
Arguments antisymmetry {A Ae S} R {AntiSymmetric} _ {_} _ {_} _ _.

Class TotalRelation `(S:set) (R : relation _) : Prop := total `{x ∊ S} `{y ∊ S} : R x y ∨ R y x.
Arguments total {_ S} R {TotalRelation} x {_} y {_}.

Class Trichotomy `{Ae:Equiv A} S (R : relation A) := trichotomy `{x ∊ S} `{y ∊ S} : R x y ∨ x = y ∨ R y x.
Arguments trichotomy {A Ae S} R {Trichotomy} x {_} y {_}.

Class Idempotent `(S:set) `{Equiv S} f x : Prop := idempotency: f x x = x.
Arguments idempotency {_ S _} f x {Idempotent}.

Class UnaryIdempotent {A} S {Ae:Equiv A} (f:A→A) : Prop := unary_idempotent :> Idempotent (S ⇀ S) (∘) (f).
Class BinaryIdempotent {A} (op:A→A→A) S {Ae:Equiv A} : Prop := binary_idempotent x `{x ∊ S} :> Idempotent S op x.

Class Associative {A} f S {Ae:Equiv A} := associativity `{x ∊ S} `{y ∊ S} `{z ∊ S} : f x (f y z) = f (f x y) z.
Arguments associativity {A} f {S _ _} x {_} y {_} z {_}.

Class HeteroAssociative {A B C AB BC ABC}
  (fA_BC: A → BC → ABC) (fBC: B → C → BC) (fAB_C: AB → C → ABC) (fAB : A → B → AB)
  S T U {ABCe : Equiv ABC} : Prop
  := hetero_associativity `{x ∊ S} `{y ∊ T} `{z ∊ U} : fA_BC x (fBC y z) = fAB_C (fAB x y) z.

Class Commutative {A B} f S {Be:Equiv B} : Prop := commutativity (x:A) `{x ∊ S} `{y ∊ S} : f x y = f y x.
Arguments commutativity {A B} f {S _ _} x {_} y {_}.

Class LeftIdentity  {A B} op (x:A) T {Be:Equiv B} := left_identity  `{y ∊ T} : op x y = y.
Class RightIdentity {A B} op (y:B) S {Ae:Equiv A} := right_identity `{x ∊ S} : op x y = x.
Arguments left_identity  {A B} op {x T _ _} y {_}.
Arguments right_identity {A B} op {y S _ _} x {_}.

Class Absorption {A B C} op1 (op2:A→B→C) S T {Ae:Equiv A} := absorption x `{x ∊ S} y `{y ∊ T} : op1 x (op2 x y) = x.

Class LeftAbsorb  {A B} op (x:A) T {Ae:Equiv A} := left_absorb  (y:B) `{y ∊ T} : op x y = x.
Class RightAbsorb {A B} op (y:B) S {Be:Equiv B} := right_absorb (x:A) `{x ∊ S} : op x y = y.
Arguments left_absorb  {A B} op {x T _ _} y {_}.
Arguments right_absorb {A B} op {y S _ _} x {_}.

Class LeftInverse  {A B C} op (inv:B→A) unit T {Ce:Equiv C} := left_inverse   `{y ∊ T} : op (inv y) y = unit.
Class RightInverse {A B C} op (inv:A→B) unit S {Ce:Equiv C} := right_inverse  `{x ∊ S} : op x (inv x) = unit.
Arguments left_inverse  {A B C} op {inv unit T _ _} y {_}.
Arguments right_inverse {A B C} op {inv unit S _ _} x {_}.

Class Involutive {A} f S {Ae:Equiv A} := involutive x `{x ∊ S} : f (f x) = x.
Arguments involutive {A} f {S _ _} x {_}.

Class LeftDistribute  {A} f g S {Ae:Equiv A} := distribute_l x `{x ∊ S} y `{y ∊ S} z `{z ∊ S} : f x (g y z) = g (f x y) (f x z).
Class RightDistribute {A} f g S {Ae:Equiv A} := distribute_r x `{x ∊ S} y `{y ∊ S} z `{z ∊ S} : f (g x y) z = g (f x z) (f y z).

Class LeftHeteroDistribute  {A B C} (f:A → B → C) (g:B → B → B) (h:C → C → C) S T {Ce:Equiv C}
  := hetero_distribute_l x `{x ∊ S} y `{y ∊ T} z `{z ∊ T} : f x (g y z) = h (f x y) (f x z).

Class RightHeteroDistribute  {A B C} (f:A → B → C) (g:A → A → A) (h:C → C → C) S T {Ce:Equiv C}
  := hetero_distribute_r x `{x ∊ S} y `{y ∊ S} z `{z ∊ T} : f (g x y) z = h (f x z) (f y z).

(* Although cancellation is the same as being injective, we want a proper
  name to refer to this commonly used property. *)
Section cancellation.
  Context `(op: A→A→A) (z:A) (S:@set A) `{Equiv A} `{UnEq A}.

  Class LeftCancellation  := left_cancellation  x `{x ∊ S} y `{y ∊ S} : op z x = op z y → x = y.
  Class RightCancellation := right_cancellation x `{x ∊ S} y `{y ∊ S} : op x z = op y z → x = y.

  Class StrongLeftCancellation  := strong_left_cancellation  x `{x ∊ S} y `{y ∊ S} : x ≠ y → op z x ≠ op z y.
  Class StrongRightCancellation := strong_right_cancellation x `{x ∊ S} y `{y ∊ S} : x ≠ y → op x z ≠ op y z.
End cancellation.

Class ZeroProduct `{Equiv A} `{Mult A} `{Zero A} R : Prop
  := zero_product x `{x ∊ R} y `{y ∊ R} : x * y = 0 → x = 0 ∨ y = 0.

Class NonZeroProduct `{UnEq A} `{Mult A} `{Zero A} R : Prop
  := nonzero_product x `{x ∊ R} y `{y ∊ R} `{x * y ∊ R ₀} : x ∊ R ₀ ∧ y ∊ R ₀.

Class ZeroDivisor `{UnEq A} `{Equiv A} `{Zero A} `{Mult A} R x : Prop
  := zero_divisor : x ∊ R ₀ ∧ ∃ `{y ∊ R ₀}, x * y = 0 ∨ y * x = 0.
Arguments zero_divisor {A _ _ _ _ R} x {_}.

Class NoZeroDivisors `{UnEq A} `{Equiv A} `{Zero A} `{Mult A} R : Prop
  := no_zero_divisors x : ¬ZeroDivisor R x.

Definition RingUnits `{Equiv A} `{Mult A} `{One A} R : set
  := λ x, x ∊ R ∧ ∃ `{y ∊ R}, x * y = 1 ∧ y * x = 1.

Class Biinduction `{Equiv A} `{Zero A} `{One A} `{Plus A} R : Prop
  := biinduction P `{!Proper ((R,=) ==> iff) P} : P 0 → (∀ `{n ∊ R}, P n ↔ P (1 + n)) → ∀ `{n ∊ R}, P n.

Local Open Scope mc_abs_scope.
Class AbsMult `{Equiv A} `{Mult A} {a:Abs A} R : Prop
  := abs_mult x `{x ∊ R} y `{y ∊ R} : |x*y| = |x|*|y| .

