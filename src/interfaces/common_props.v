Require Import canonical_names interfaces.subset propholds.

Definition NonZero `{UnEq A} {Azero:Zero A} (S:Subset A) : Subset A
  := λ x, x ∊ S ∧ PropHolds (x ≠ 0).
Notation "R ₀" := (NonZero R) (at level 20, no associativity) : mc_scope.

Arguments irreflexivity {A} _ {Irreflexive} _ _.

Class CoTransitive `(R : relation A) : Prop := cotransitive : ∀ x y, R x y → ∀ z, R x z ∨ R z y.
Arguments cotransitive {A R CoTransitive x y} _ _.

(* dual to Equivalence *)
Class Apartness `(R : relation A) : Prop :=
  { apartness_irreflexive  :> Irreflexive  R
  ; apartness_symmetric    :> Symmetric    R
  ; apartness_cotransitive :> CoTransitive R
  }.

Class SubReflexive   `(R : relation A) (S:Subset A) : Prop := subreflexivity   x `{!x ∊ S}                         : R x x.
Class SubIrreflexive `(R : relation A) (S:Subset A) : Prop := subirreflexivity x `{!x ∊ S}                         : ¬ R x x.
Class SubSymmetric   `(R : relation A) (S:Subset A) : Prop := subsymmetry      x `{!x ∊ S} y `{!y ∊ S}             : R x y → R y x.
Class SubTransitive  `(R : relation A) (S:Subset A) : Prop := subtransitivity  x `{!x ∊ S} y `{!y ∊ S} z `{!z ∊ S} : R x y → R y z → R x z.

Arguments subirreflexivity {A} R {S SubIrreflexive} x {_} _.

Class SubEquivalence `(R : relation A) (S:Subset A) : Prop :=
  { subequiv_reflexive  :> SubReflexive  R S
  ; subequiv_symmetric  :> SubSymmetric  R S
  ; subequiv_transitive :> SubTransitive R S
  }.

Class SubAntiSymmetric `{Ae:Equiv A} (R: relation A) (S:Subset A) : Prop := subantisymmetry x `{!x ∊ S} y `{!y ∊ S} : R x y → R y x → x = y.
Arguments subantisymmetry {A Ae} R {S SubAntiSymmetric} _ {_} _ {_} _ _.


Class TotalRelation `(R : relation A) (S:Subset A) : Prop := total x `{!x ∊ S} y `{!y ∊ S} : R x y ∨ R y x.
Arguments total {A} _ {S TotalRelation} x {_} y {_}.

Class Associative {A} f `{!Equiv A} (S:Subset A) :=
  associativity x `{!x ∊ S} y `{!y ∊ S} z `{!z ∊ S} : f x (f y z) = f (f x y) z.

Class Commutative `(f : A → A → B) `{!Equiv B} (S:Subset A) : Prop := commutativity x `{!x ∊ S} y `{!y ∊ S} : f x y = f y x.

Class LeftIdentity  {A B} (op : A → B → B) x `{!Equiv B} (T:Subset B) := left_identity  y `{!y ∊ T} : op x y = y.
Class RightIdentity {A B} (op : A → B → A) y `{!Equiv A} (S:Subset A) := right_identity x `{!x ∊ S} : op x y = x.

Class LeftAbsorb  {A B} (op : A → B → A) x `{!Equiv A} (T:Subset B) := left_absorb  y `{!y ∊ T} : op x y = x.
Class RightAbsorb {A B} (op : A → B → B) y `{!Equiv B} (S:Subset A) := right_absorb x `{!x ∊ S} : op x y = y.

Class LeftInverse  {A B C} (op : A → B → C) (inv : B → A) (unit : C) `{!Equiv C} (T:Subset B) := left_inverse  y `{!y ∊ T} : op (inv y) y = unit.
Class RightInverse {A B C} (op : A → B → C) (inv : A → B) (unit : C) `{!Equiv C} (S:Subset A) := right_inverse x `{!x ∊ S} : op x (inv x) = unit.

Class Involutive {A} (f : A → A) `{!Equiv A} (S:Subset A) := involutive x `{!x ∊ S} : f (f x) = x.

Class LeftDistribute  {A} (f g: A → A → A) `{!Equiv A} (S:Subset A) := distribute_l x `{!x ∊ S} y `{!y ∊ S} z `{!z ∊ S} : f x (g y z) = g (f x y) (f x z).
Class RightDistribute {A} (f g: A → A → A) `{!Equiv A} (S:Subset A) := distribute_r x `{!x ∊ S} y `{!y ∊ S} z `{!z ∊ S} : f (g x y) z = g (f x z) (f y z).


(* Although cancellation is the same as being injective, we want a proper
  name to refer to this commonly used property. *)
Section cancellation.
  Context `{Ae : Equiv A} (op : A → A → A) (z:A) (S:Subset A).

  Class LeftCancellation  := left_cancellation  x `{!x ∊ S} y `{!y ∊ S} : op z x = op z y → x = y.
  Class RightCancellation := right_cancellation x `{!x ∊ S} y `{!y ∊ S} : op x z = op y z → x = y.
End cancellation.

Class ZeroProduct {A} `{Equiv A} `{Mult A} `{Zero A} (R:Subset A): Prop
  := zero_product x `{!x ∊ R} y `{!y ∊ R} : x * y = 0 → x = 0 ∨ y = 0.

Class ZeroDivisor {A} `{UnEq A} `{Equiv A} `{Zero A} `{Mult A} (R:Subset A) (x : A) : Prop
  := zero_divisor : x ∊ R ₀ ∧ ∃ y, y ∊ R ₀ ∧ (x * y = 0 ∨ y * x = 0).
Arguments zero_divisor {A _ _ _ _ R} x {_}.

Class NoZeroDivisors {A} `{UnEq A} `{Equiv A} `{Zero A} `{Mult A} (R:Subset A) : Prop
  := no_zero_divisors x : ¬ZeroDivisor R x.

Definition RingUnits {A} `{Equiv A} `{Mult A} `{One A} (R:Subset A) : Subset A
  := λ x, x ∊ R ∧ ∃ y, y ∊ R ∧ x * y = 1 ∧ y * x = 1.
