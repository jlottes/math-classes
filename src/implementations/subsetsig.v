Require Import
  canonical_names restrict_rel interfaces.subset theory.subset.

Class SubsetSig_Closed {A} (R:Subset A) (f:A) := subsetsig_closed : Closed R f.
Arguments SubsetSig_Closed {A}%type_scope R%closed_sig_scope f.

Section defs.

  Context {A} {Ae : Equiv A} {Azero:Zero A} {Aone: One A} {Aplus:Plus A} {Amult:Mult A} {Anegate:Negate A}.

  Context (S:Subset A).

  Context {zero_closed  :SubsetSig_Closed S 0}.
  Context {one_closed   :SubsetSig_Closed S 1}.
  Context {plus_closed  :SubsetSig_Closed (S==>S==>S) (+)}.
  Context {mult_closed  :SubsetSig_Closed (S==>S==>S) (.*.)}.
  Context {negate_closed:SubsetSig_Closed (S==>S) (-)}.

  Definition SubsetSig := {x:A | x ∊ S}.

  Definition to_sig x {pf:x ∊ S} : SubsetSig := exist _ x pf.

  Instance subsetsig_element (sx:SubsetSig) : ` sx ∊ S. Proof. destruct sx as [? el]. exact el. Qed.

  Existing Instance subsetsig_closed.

  Instance subsetsig_equiv : Equiv SubsetSig := λ x y, ` x = ` y.
  Program Instance subsetsig_zero  : Zero SubsetSig := exist _ 0 _.
  Program Instance subsetsig_one   : One  SubsetSig := exist _ 1 _.
  Program Instance subsetsig_plus  : Plus SubsetSig := λ x y, exist _ (`x + `y) _.  Next Obligation. apply _. Qed.
  Program Instance subsetsig_mult  : Mult SubsetSig := λ x y, exist _ (`x * `y) _.  Next Obligation. apply _. Qed.
  Program Instance subsetsig_negate: Negate SubsetSig := λ x, exist _ (- `x) _.

End defs.

Hint Extern 0 (@Equiv  (@SubsetSig _ _)) => eapply @subsetsig_equiv  : typeclass_instances.
Hint Extern 0 (@Zero   (@SubsetSig _ _)) => eapply @subsetsig_zero   : typeclass_instances.
Hint Extern 0 (@One    (@SubsetSig _ _)) => eapply @subsetsig_one    : typeclass_instances.
Hint Extern 0 (@Plus   (@SubsetSig _ _)) => eapply @subsetsig_plus   : typeclass_instances.
Hint Extern 0 (@Mult   (@SubsetSig _ _)) => eapply @subsetsig_mult   : typeclass_instances.
Hint Extern 0 (@Negate (@SubsetSig _ _)) => eapply @subsetsig_negate : typeclass_instances.


Class SubsetSig_Quote `{Ae:Equiv A} (S:Subset A) x (sx : SubsetSig S) := subsetsig_quote_eq : x = ` sx.
Local Notation Quote := SubsetSig_Quote.

Section quoting.

  Context {A} {Ae : Equiv A} {Azero:Zero A} {Aone: One A} {Aplus:Plus A} {Amult:Mult A} {Anegate:Negate A}.

  Context (S:Subset A).

  Context {zero_closed  :SubsetSig_Closed S 0}.
  Context {one_closed   :SubsetSig_Closed S 1}.
  Context {plus_closed  :SubsetSig_Closed (S==>S==>S) (+)}.
  Context {mult_closed  :SubsetSig_Closed (S==>S==>S) (.*.)}.
  Context {negate_closed:SubsetSig_Closed (S==>S) (-)}.

  Context `{!Equivalence (=)}.

  Lemma subsetsig_quote_equiv_correct {x sx y sy} (E1:Quote S x sx) (E2:Quote S y sy) : sx = sy ↔ x = y.
  Proof. unfold Quote in *. destruct sx as [x' ?], sy as [y' ?]. simpl in E1,E2.
    change (x' = y' ↔ x = y). now rewrite E1, E2.
  Qed.

  Local Ltac solve  E     := unfold Quote in *; rewrite_on S -> E; reflexivity.
  Local Ltac solve2 E1 E2 := unfold Quote in *; rewrite_on S -> E1; rewrite_on S -> E2; reflexivity.

  Lemma subsetsig_quote_base x `{!x ∊ S} : Quote S x (to_sig S x). Proof. red. reflexivity. Qed.
  Lemma subsetsig_quote_zero : Quote S 0 0. Proof. red. reflexivity. Qed.
  Lemma subsetsig_quote_one  : Quote S 1 1. Proof. red. reflexivity. Qed.
  Lemma subsetsig_quote_plus `{!SubProper ((S,=) ==> (S,=) ==> (S,=)) (+)  } `{x ∊ S} `{y ∊ S} {sx sy} (E1:Quote S x sx) (E2:Quote S y sy) : Quote S (x+y) (sx+sy). Proof. solve2 E1 E2. Qed.
  Lemma subsetsig_quote_mult `{!SubProper ((S,=) ==> (S,=) ==> (S,=)) (.*.)} `{x ∊ S} `{y ∊ S} {sx sy} (E1:Quote S x sx) (E2:Quote S y sy) : Quote S (x*y) (sx*sy). Proof. solve2 E1 E2. Qed.
  Lemma subsetsig_quote_negate `{!SubProper ((S,=) ==> (S,=)) (-) } `{x ∊ S} {sx} (E:Quote S x sx) : Quote S (-x) (-sx). Proof. solve E. Qed.

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

Require Import abstract_algebra theory.subsetoids theory.groups.

Lemma subsetsig_setoid `{Setoid A} (S:Subset A) : Setoid (SubsetSig S).
Proof. split.
+ intros [x ?]. change (x=x). reflexivity.
+ intros [x ?] [y ?] P. change (x=y) in P. change (y=x). now symmetry.
+ intros [x ?] [y ?] [z ?] P Q. change (x=y) in P. change (y=z) in Q. change (x=z). auto_trans.
Qed.
Hint Extern 0 (@Setoid (@SubsetSig _ _) _) => eapply @subsetsig_setoid : typeclass_instances.

Section propers.
  Context {A} {Ae : Equiv A} {Azero:Zero A} {Aone: One A} {Aplus:Plus A} {Amult:Mult A} {Anegate:Negate A}.

  Context (S:Subset A).

  Context {zero_closed  :SubsetSig_Closed S 0}.
  Context {one_closed   :SubsetSig_Closed S 1}.
  Context {plus_closed  :SubsetSig_Closed (S==>S==>S) (+)}.
  Context {mult_closed  :SubsetSig_Closed (S==>S==>S) (.*.)}.
  Context {negate_closed:SubsetSig_Closed (S==>S) (-)}.

  Context `{!Setoid A}.
  Context `{!SubProper ((S,=) ==> (S,=) ==> (S,=)) (+)}.
  Context `{!SubProper ((S,=) ==> (S,=) ==> (S,=)) (.*.)}.
  Context `{!SubProper ((S,=) ==> (S,=)) (-)}.

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

  Local Notation S' := (Every (SubsetSig S)).

  Instance subsetsig_plus_monoid `{!@Monoid A Ae plus_is_sg_op zero_is_mon_unit S}
    : @Monoid _ _ plus_is_sg_op zero_is_mon_unit S'.
  Proof. split. split. apply _.
  + intros [x ?] ? [y ?] ? [z ?] ?. exact (associativity x y z).
  + split; try apply _. intros x1 x2 E1 y1 y2 E2. unfold_sigs. red_sig.
    change (x1+y1 = x2+y2). now rewrite E1, E2.
  + apply _.
  + intros [x ?] ?. exact (left_identity x).
  + intros [x ?] ?. exact (right_identity x).
  Qed.

  Instance subsetsig_mult_semigroup `{!@SemiGroup A Ae mult_is_sg_op S}
    : @SemiGroup _ _ mult_is_sg_op S'.
  Proof. split. apply _.
  + intros [x ?] ? [y ?] ? [z ?] ?. exact (associativity x y z).
  + split; try apply _. intros x1 x2 E1 y1 y2 E2. unfold_sigs. red_sig.
    change (x1*y1 = x2*y2). now rewrite E1,E2.
  Qed.

  Instance subsetsig_mult_1_l `{!@SemiGroup A Ae mult_is_sg_op S}
    `{!LeftIdentity (.*.) 1 S} : LeftIdentity (.*.) 1 S'.
  Proof. intros [x ?] ?. exact (left_identity x). Qed.

  Instance subsetsig_mult_1_r `{!@SemiGroup A Ae mult_is_sg_op S}
    `{!RightIdentity (.*.) 1 S} : RightIdentity (.*.) 1 S'.
  Proof. intros [x ?] ?. exact (right_identity x). Qed.

  Instance subsetsig_mult_monoid `{!@Monoid A Ae mult_is_sg_op one_is_mon_unit S}
    : @Monoid _ _ mult_is_sg_op one_is_mon_unit S' := {}.

  Instance subsetsig_plus_comm `{!Commutative (+) S} : Commutative (+) S'.
  Proof. intros [x ?] ? [y ?] ?. pose proof (commutativity x y) as E. exact E. Qed.

  Instance subsetsig_mult_comm `{!Commutative (.*.) S} : Commutative (.*.) S'.
  Proof. intros [x ?] ? [y ?] ?. pose proof (commutativity x y) as E. exact E. Qed.

  Instance subsetsig_plus_commonoid `{!@CommutativeMonoid A Ae plus_is_sg_op zero_is_mon_unit S}
    : @CommutativeMonoid _ _ plus_is_sg_op zero_is_mon_unit S' := {}.

  Instance subsetsig_mult_commonoid `{!@CommutativeMonoid A Ae mult_is_sg_op one_is_mon_unit S}
    : @CommutativeMonoid _ _ mult_is_sg_op one_is_mon_unit S' := {}.

  Instance subsetsig_plus_abgroup
    `{!@AbGroup A Ae plus_is_sg_op zero_is_mon_unit negate_is_inv S}
    :  @AbGroup _ _  plus_is_sg_op zero_is_mon_unit negate_is_inv S'.
  Proof. split. split. apply _.
  + split; try apply _. intros x1 x2 E1. unfold_sigs. red_sig.
    change (-x1 = -x2). now rewrite E1.
  + intros [x ?] ?. pose proof (left_inverse x) as E. exact E.
  + intros [x ?] ?. pose proof (right_inverse x) as E. exact E.
  + apply _.
  Qed.

  Instance subsetsig_mult_plus_distr_l
    `{!@CommutativeMonoid A Ae plus_is_sg_op zero_is_mon_unit S}
    `{!@SemiGroup A Ae mult_is_sg_op S}
    `{!LeftDistribute (.*.) (+) S}
    : LeftDistribute (.*.) (+) S'.
  Proof. intros [x ?] ? [y ?] ? [z ?] ?. pose proof (distribute_l x y z) as E. exact E. Qed.

  Instance subsetsig_mult_plus_distr_r
    `{!@CommutativeMonoid A Ae plus_is_sg_op zero_is_mon_unit S}
    `{!@SemiGroup A Ae mult_is_sg_op S}
    `{!RightDistribute (.*.) (+) S}
    : RightDistribute (.*.) (+) S'.
  Proof. intros [x ?] ? [y ?] ? [z ?] ?. pose proof (distribute_r x y z) as E. exact E. Qed.

  Instance subsetsig_semirng `{!SemiRng S} : SemiRng S'.
  Proof. split; try apply _.
  + intros [x ?] ?. pose proof (left_absorb x) as E. exact E.
  + intros [x ?] ?. pose proof (right_absorb x) as E. exact E.
  Qed.

  Instance subsetsig_semiring `{!SemiRing S} : SemiRing S' := {}.

  Instance subsetsig_rng `{!Rng S} : Rng S' := {}.

  Instance subsetsig_ring `{!Ring S} : Ring S' := {}.

  Instance subsetsig_comring `{!CommutativeRing S} : CommutativeRing S' := {}.

End transference.
