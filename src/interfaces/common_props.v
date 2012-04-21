Require Import canonical_names interfaces.subset propholds.

Definition NonZero `{Equiv A} {Azero:Zero A} (S:Subset A) : Subset A
  := λ x, x ∊ S ∧ PropHolds (x ≠ 0).
Notation "R ₀" := (NonZero R) (at level 20, no associativity) : mc_scope.

Class SubReflexive  `(S:Subset A) (R : relation A) : Prop := subreflexivity  x `{!x ∊ S}                         : R x x.
Class SubSymmetric  `(S:Subset A) (R : relation A) : Prop := subsymmetry     x `{!x ∊ S} y `{!y ∊ S}             : R x y → R y x.
Class SubTransitive `(S:Subset A) (R : relation A) : Prop := subtransitivity x `{!x ∊ S} y `{!y ∊ S} z `{!z ∊ S} : R x y → R y z → R x z.

Class SubEquivalence `(S:Subset A) (R : relation A) : Prop :=
  { subequiv_reflexive  :> SubReflexive  S R
  ; subequiv_symmetric  :> SubSymmetric  S R
  ; subequiv_transitive :> SubTransitive S R
  }.

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

Class ZeroDivisor {A} `{Equiv A} `{Zero A} `{Mult A} (R:Subset A) (x : A) : Prop
  := zero_divisor : x ∊ R ₀ ∧ ∃ y, y ∊ R ₀ ∧ (x * y = 0 ∨ y * x = 0).
Arguments zero_divisor {A _ _ _ R} x {_}.

Class NoZeroDivisors {A} `{Equiv A} `{Zero A} `{Mult A} (R:Subset A) : Prop
  := no_zero_divisors x : ¬ZeroDivisor R x.

Definition RingUnits {A} `{Equiv A} `{Mult A} `{One A} (R:Subset A) : Subset A
  := λ x, x ∊ R ∧ ∃ y, y ∊ R ∧ x * y = 1 ∧ y * x = 1.


(*
Class Idempotent `{ea : Equiv A} (f: A → A → A) (x : A) : Prop := idempotency: f x x = x.
Arguments idempotency {A ea} _ _ {Idempotent}.

Class UnaryIdempotent `{Equiv A} (f: A → A) : Prop := unary_idempotent :> Idempotent (∘) f.
Lemma unary_idempotency `{Equiv A} `{!Reflexive (=)} `{!UnaryIdempotent f} x : f (f x) = f x.
Proof. firstorder. Qed.

Class BinaryIdempotent `{Equiv A} (op: A → A → A) : Prop := binary_idempotent :> ∀ x, Idempotent op x.

Class LeftIdentity {A} `{Equiv B} (op : A → B → B) (x : A): Prop := left_identity: ∀ y, op x y = y.
Class RightIdentity `{Equiv A} {B} (op : A → B → A) (y : B): Prop := right_identity: ∀ x, op x y = x.

Class Absorption `{Equiv A} {B} {C} (op1: A → C → A) (op2: A → B → C) : Prop := absorption: ∀ x y, op1 x (op2 x y) = x.

Class LeftAbsorb `{Equiv A} {B} (op : A → B → A) (x : A): Prop := left_absorb: ∀ y, op x y = x.
Class RightAbsorb {A} `{Equiv B} (op : A → B → B) (y : B): Prop := right_absorb: ∀ x, op x y = y.

Class LeftInverse {A} {B} `{Equiv C} (op : A → B → C) (inv : B → A) (unit : C) := left_inverse: ∀ x, op (inv x) x = unit.
Class RightInverse {A} {B} `{Equiv C} (op : A → B → C) (inv : A → B) (unit : C) := right_inverse: ∀ x, op x (inv x) = unit.

Class Commutative `{Equiv B} `(f : A → A → B) : Prop := commutativity: ∀ x y, f x y = f y x.

Class HeteroAssociative {A B C AB BC} `{Equiv ABC}
     (fA_BC: A → BC → ABC) (fBC: B → C → BC) (fAB_C: AB → C → ABC) (fAB : A → B → AB): Prop
   := associativity : ∀ x y z, fA_BC x (fBC y z) = fAB_C (fAB x y) z.
Class Associative `{Equiv A} f := simple_associativity:> HeteroAssociative f f f f.

Class Involutive `{Equiv A} (f : A → A) := involutive: ∀ x, f (f x) = x.

Class TotalRelation `(R : relation A) : Prop := total : ∀ x y : A, R x y ∨ R y x.
Arguments total {A} _ {TotalRelation} _ _.

Class Trichotomy `{Ae : Equiv A} `(R : relation A) := trichotomy : ∀ x y : A, R x y ∨ x = y ∨ R y x.
Arguments trichotomy {A Ae} _ {Trichotomy} _ _.

Arguments irreflexivity {A} _ {Irreflexive} _ _.

Class CoTransitive `(R : relation A) : Prop := cotransitive : ∀ x y, R x y → ∀ z, R x z ∨ R z y.
Arguments cotransitive {A R CoTransitive x y} _ _.

Class AntiSymmetric `{Ae : Equiv A} (R : relation A) : Prop := antisymmetry: ∀ x y, R x y → R y x → x = y.
Arguments antisymmetry {A Ae} _ {AntiSymmetric} _ _ _ _.

Class LeftHeteroDistribute {A B} `{Equiv C} (f : A → B → C) (g_r : B → B → B) (g : C → C → C) : Prop
  := distribute_l : ∀ a b c, f a (g_r b c) = g (f a b) (f a c).
Class RightHeteroDistribute {A B} `{Equiv C} (f : A → B → C) (g_l : A → A → A) (g : C → C → C) : Prop
  := distribute_r: ∀ a b c, f (g_l a b) c = g (f a c) (f b c).
Class LeftDistribute`{Equiv A} (f g: A → A → A) := simple_distribute_l :> LeftHeteroDistribute f g g.
Class RightDistribute `{Equiv A} (f g: A → A → A) := simple_distribute_r :> RightHeteroDistribute f g g.

Class HeteroSymmetric {A} {T : A → A → Type} (R : ∀ {x y}, T x y → T y x → Prop) : Prop :=
  hetero_symmetric `(a : T x y) (b : T y x) : R a b → R b a.

(* Although cancellation is the same as being injective, we want a proper
  name to refer to this commonly used property. *)
Section cancellation.
  Context `{Ae : Equiv A} `{Aap : Apart A} (op : A → A → A) (z : A).

  Class LeftCancellation := left_cancellation : ∀ x y, op z x = op z y → x = y.
  Class RightCancellation := right_cancellation : ∀ x y, op x z = op y z → x = y.

End cancellation.

(* Common names for properties that hold in N, Z, Q, ... *)
Class ZeroProduct A `{Equiv A} `{!Mult A} `{!Zero A} : Prop
  := zero_product : ∀ x y, x * y = 0 → x = 0 ∨ y = 0.

Class ZeroDivisor {R} `{Equiv R} `{Zero R} `{Mult R} (x : R) : Prop
  := zero_divisor : x ≠ 0 ∧ ∃ y, y ≠ 0 ∧ x * y = 0.

Class NoZeroDivisors R `{Equiv R} `{Zero R} `{Mult R} : Prop
  := no_zero_divisors x : ¬ZeroDivisor x.

Instance zero_product_no_zero_divisors `{ZeroProduct A} : NoZeroDivisors A.
Proof. intros x [? [? [? E]]]. destruct (zero_product _ _ E); intuition. Qed.

Class RingUnit `{Equiv R} `{Mult R} `{One R} (x : R) : Prop := ring_unit : ∃ y, x * y = 1.

(* A common induction principle for both the naturals and integers *)
Class Biinduction R `{Equiv R} `{Zero R} `{One R} `{Plus R} : Prop
  := biinduction (P : R → Prop) `{!Proper ((=) ==> iff) P} : P 0 → (∀ n, P n ↔ P (1 + n)) → ∀ n, P n.
*)
