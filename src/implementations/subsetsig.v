Require Import abstract_algebra theory.setoids.

Class SubsetSig_Closed {A} (R:Subset A) (f:A) := subsetsig_closed : Closed R f.
Arguments SubsetSig_Closed {A}%type_scope R%closed_sig_scope f.

Section defs.

  Context `(S:Subset A).

  Definition SubsetSig := {x:A | x ∊ S}.

  Definition to_sig x {pf:x ∊ S} : SubsetSig := exist _ x pf.

  Instance subsetsig_element (sx:SubsetSig) : ` sx ∊ S. Proof. destruct sx as [? el]. exact el. Qed.

  Existing Instance subsetsig_closed.

  Instance subsetsig_equiv `{Equiv A} : Equiv SubsetSig := λ x y, ` x = ` y.
  Program Instance subsetsig_zero `{Zero A} `{!SubsetSig_Closed S 0} : Zero SubsetSig := exist _ 0 _.
  Program Instance subsetsig_one  `{One  A} `{!SubsetSig_Closed S 1} : One  SubsetSig := exist _ 1 _.
  Program Instance subsetsig_plus `{Plus A} `{!SubsetSig_Closed (S==>S==>S) (+)} : Plus SubsetSig := λ x y, exist _ (`x + `y) _.
  Program Instance subsetsig_mult `{Mult A} `{!SubsetSig_Closed (S==>S==>S) (.*.)}:Mult SubsetSig := λ x y, exist _ (`x * `y) _.
  Program Instance subsetsig_negate `{Negate A} `{!SubsetSig_Closed (S==>S) (-)} : Negate SubsetSig := λ x, exist _ (- `x) _.
  Solve All Obligations with (apply _).

End defs.

Hint Extern 0 (Subset (SubsetSig ?S)) => eexact (every (SubsetSig S)) : typeclass_instances.

Hint Extern 0 (Equiv  (SubsetSig ?S)) => eapply (subsetsig_equiv  S) : typeclass_instances.
Hint Extern 0 (Zero   (SubsetSig ?S)) => eapply (subsetsig_zero   S) : typeclass_instances.
Hint Extern 0 (One    (SubsetSig ?S)) => eapply (subsetsig_one    S) : typeclass_instances.
Hint Extern 0 (Plus   (SubsetSig ?S)) => eapply (subsetsig_plus   S) : typeclass_instances.
Hint Extern 0 (Mult   (SubsetSig ?S)) => eapply (subsetsig_mult   S) : typeclass_instances.
Hint Extern 0 (Negate (SubsetSig ?S)) => eapply (subsetsig_negate S) : typeclass_instances.


Definition SubsetSig_Quote `{Ae:Equiv A} (S:Subset A) x (sx : SubsetSig S) := x ∊ S ∧ x = ` sx.
Local Notation Quote := SubsetSig_Quote.

Section quoting.

  Context {A} {Ae : Equiv A} {Azero:Zero A} {Aone: One A} {Aplus:Plus A} {Amult:Mult A} {Anegate:Negate A}.

  Context (S:Subset A) `{!Setoid S}.

  Context {zero_closed  :SubsetSig_Closed S 0}.
  Context {one_closed   :SubsetSig_Closed S 1}.
  Context {plus_closed  :SubsetSig_Closed (S==>S==>S) (+)}.
  Context {mult_closed  :SubsetSig_Closed (S==>S==>S) (.*.)}.
  Context {negate_closed:SubsetSig_Closed (S==>S) (-)}.

  Context {plus_proper  :Setoid_Binary_Morphism S S S (+)}.
  Context {mult_proper  :Setoid_Binary_Morphism S S S (.*.)}.
  Context {negate_proper:Setoid_Morphism S S (-)}.

  Existing Instance subsetsig_element.
  Existing Instance subsetsig_closed.

  Local Ltac destr E := match type of E with Quote _ _ ?sx => destruct E as [? E], sx as [??]; simpl in E end.

  Lemma subsetsig_quote_equiv_correct {x sx y sy} (E1:Quote S x sx) (E2:Quote S y sy) : sx = sy ↔ x = y.
  Proof. destr E1. destr E2. unfold equiv at 1, subsetsig_equiv. simpl. now rewrite_on S -> E1, E2. Qed.

  Local Ltac solve E      := destr E;            split; [ apply _ |]; simpl; now rewrite_on S -> E.
  Local Ltac solve2 E1 E2 := destr E1; destr E2; split; [ apply _ |]; simpl; now rewrite_on S -> E1, E2.


  Lemma subsetsig_quote_base x `{x ∊ S} : Quote S x (to_sig S x). Proof. split. apply _. subreflexivity. Qed.
  Lemma subsetsig_quote_zero : Quote S 0 0. Proof. split. apply zero_closed. subreflexivity. Qed.
  Lemma subsetsig_quote_one  : Quote S 1 1. Proof. split. apply one_closed. subreflexivity. Qed.
  Lemma subsetsig_quote_plus `(E1:Quote S x sx) `(E2:Quote S y sy) : Quote S (x+y) (sx+sy). Proof. solve2 E1 E2. Qed.
  Lemma subsetsig_quote_mult `(E1:Quote S x sx) `(E2:Quote S y sy) : Quote S (x*y) (sx*sy). Proof. solve2 E1 E2. Qed.
  Lemma subsetsig_quote_negate `(E:Quote S x sx) : Quote S (-x) (-sx). Proof. solve E. Qed.

End quoting.

Ltac subsetsig_quote S :=
  let rec aux expr :=
    match expr with
    | @zero _ _ => constr:(subsetsig_quote_zero S)
    | @one _ _ => constr:(subsetsig_quote_one S)
    | @plus _ _ ?x ?y => let qx := aux x in let qy := aux y in constr:(subsetsig_quote_plus S qx qy)
    | @mult _ _ ?x ?y => let qx := aux x in let qy := aux y in constr:(subsetsig_quote_mult S qx qy)
    | @negate _ _ ?x => let qx := aux x in constr:(subsetsig_quote_negate S qx)
    | _ => constr:(subsetsig_quote_base S expr)
    end
  in aux.

Ltac subsetsig_quote_equiv S :=
  match goal with |- @equiv _ _ ?x ?y =>
    let qx := subsetsig_quote S x in
    let qy := subsetsig_quote S y in
    apply (proj1 (subsetsig_quote_equiv_correct S qx qy))
  end.

Require Import theory.groups theory.rings.

Lemma subsetsig_eq_equiv {A S} `{Setoid A (S:=S)} : Equivalence (@equiv (SubsetSig S) _).
Proof. split.
+ intros [x ?]. change (x=x). subreflexivity.
+ intros [x ?] [y ?] P. change (x=y) in P. change (y=x). subsymmetry.
+ intros [x ?] [y ?] [z ?] P Q. change (x=y) in P. change (y=z) in Q. change (x=z). subtransitivity y.
Qed.
Hint Extern 0 (Equivalence (@equiv (SubsetSig _) _)) => eapply @subsetsig_eq_equiv : typeclass_instances.

Lemma subsetsig_setoid {A S} `{Setoid A (S:=S)} : Setoid (every (SubsetSig S)).
Proof. red. apply _. Qed.
Hint Extern 0 (@Setoid (SubsetSig _) _ _) => eapply @subsetsig_setoid : typeclass_instances.

Section propers.
  Context {A} {Ae : Equiv A} {Azero:Zero A} {Aone: One A} {Aplus:Plus A} {Amult:Mult A} {Anegate:Negate A}.

  Context (S:Subset A).

  Context {zero_closed  :SubsetSig_Closed S 0}.
  Context {one_closed   :SubsetSig_Closed S 1}.
  Context {plus_closed  :SubsetSig_Closed (S==>S==>S) (+)}.
  Context {mult_closed  :SubsetSig_Closed (S==>S==>S) (.*.)}.
  Context {negate_closed:SubsetSig_Closed (S==>S) (-)}.

  Context `{!Setoid S}.
  Context {plus_proper  :Setoid_Binary_Morphism S S S (+)}.
  Context {mult_proper  :Setoid_Binary_Morphism S S S (.*.)}.
  Context {negate_proper:Setoid_Morphism S S (-)}.

  Global Instance: Proper ((=)==>(=)==>(=)) (@plus (SubsetSig S) _).
  Proof. intros [x1 ?] [x2 ?] E1 [y1 ?] [y2 ?] E2.
      change (x1=x2) in E1. change (y1=y2) in E2. change (x1+y1 = x2+y2).
      rewrite_on S -> E1. now rewrite_on S -> E2.
  Qed.

  Global Instance: Proper ((=)==>(=)==>(=)) (@mult (SubsetSig S) _).
  Proof. intros [x1 ?] [x2 ?] E1 [y1 ?] [y2 ?] E2.
      change (x1=x2) in E1. change (y1=y2) in E2. change (x1*y1 = x2*y2).
      rewrite_on S -> E1. now rewrite_on S -> E2.
  Qed.

  Global Instance: Proper ((=)==>(=)) (@negate (SubsetSig S) _).
  Proof. intros [x1 ?] [x2 ?] E1.
      change (x1=x2) in E1. change (-x1 = -x2).
      now rewrite_on S -> E1.
  Qed.

End propers.


Section transference.
  Context {A} {Ae : Equiv A} {Azero:Zero A} {Aone: One A} {Aplus:Plus A} {Amult:Mult A} {Anegate:Negate A}.

  Context (S:Subset A).

  Context {zero_closed  :SubsetSig_Closed S 0}.
  Context {one_closed   :SubsetSig_Closed S 1}.
  Context {plus_closed  :SubsetSig_Closed (S==>S==>S) (+)}.
  Context {mult_closed  :SubsetSig_Closed (S==>S==>S) (.*.)}.
  Context {negate_closed:SubsetSig_Closed (S==>S) (-)}.

  Local Notation S' := (every (SubsetSig S)).

  Instance subsetsig_plus_monoid `{!AdditiveMonoid S} : AdditiveMonoid S'.
  Proof. split. split. split. apply _.
  + intros [x ?] _ [y ?] _ [z ?] _. exact (associativity (+) x y z).
  + split; try apply _. intros x1 x2 [_ E1] y1 y2 [_ E2]. red_sig. change (x1+y1 = x2+y2). now rewrite E1, E2.
  + intros [x ?] _ [y ?] _. exact (commutativity (+) x y).
  + apply _.
  + intros [x ?] ?. exact (left_identity (+) x).
  Qed.

  Instance subsetsig_plus_group `{!AdditiveGroup S} : AdditiveGroup S'.
  Proof. split. apply _.
  + split; try apply _. intros x1 x2 [_ E1]. red_sig. change (-x1 = -x2). now rewrite E1.
  + intros [x ?] ?. exact (left_inverse (&) x).
  Qed.

  Instance subsetsig_mult_semigroup `{!MultiplicativeSemiGroup S} : MultiplicativeSemiGroup S'.
  Proof. split. apply _.
  + intros [x ?] _ [y ?] _ [z ?] _. exact (associativity (.*.) x y z).
  + split; try apply _. intros x1 x2 [_ E1] y1 y2 [_ E2]. red_sig. change (x1*y1 = x2*y2). now rewrite E1, E2.
  Qed.

  Instance subsetsig_mult_commonoid `{!MultiplicativeComMonoid S} : MultiplicativeComMonoid S'.
  Proof. split. split. apply _.
  + intros [x ?] _ [y ?] _. exact (commutativity (.*.) x y).
  + apply _.
  + intros [x ?] _. exact (left_identity (&) x).
  Qed.

  Instance subsetsig_semirng `{!SemiRng S} : SemiRng S'.
  Proof. split. apply _. apply _.
  + intros [x ?] _ [y ?] _ [z ?] _. exact (plus_mult_distr_l x y z).
  + intros [x ?] _ [y ?] _ [z ?] _. exact (plus_mult_distr_r x y z).
  + intros [x ?] _. exact (mult_0_l x).
  + intros [x ?] _. exact (mult_0_r x).
  Qed.

  Instance subsetsig_semiring `{!SemiRing S} : SemiRing S'.
  Proof. split. apply _. apply _.
  + intros [x ?] _. exact (mult_1_l x).
  + intros [x ?] _. exact (mult_1_r x).
  Qed.

  Instance subsetsig_comsemiring `{!CommutativeSemiRing S} : CommutativeSemiRing S' := {}.

  Instance subsetsig_rng `{!Rng S} : Rng S' := {}.

  Instance subsetsig_ring `{!Ring S} : Ring S' := {}.

  Instance subsetsig_comring `{!CommutativeRing S} : CommutativeRing S' := {}.

End transference.
