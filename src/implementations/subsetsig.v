Require Import abstract_algebra theory.setoids theory.common_props.

Class SubsetSig_Closed {A} (R:@Subset A) (f:A) := subsetsig_closed : Closed R f.

Local Existing Instance subsetsig_closed.
Local Existing Instance closed_range.
Local Existing Instance closed_binary.

Section defs.

  Context `(S:Subset).

  Definition SubsetSig := {x | x ∊ S}.

  Definition to_sig x {pf:x ∊ S} : SubsetSig := exist _ x pf.

  Instance subsetsig_element (sx:SubsetSig) : ` sx ∊ S. Proof. destruct sx as [? el]. exact el. Qed.

  Instance subsetsig_equiv `{Equiv A} : Equiv SubsetSig := λ x y, ` x = ` y.
  Instance subsetsig_uneq  `{UnEq  A} : UnEq  SubsetSig := λ x y, ` x ≠ ` y.
  Program Instance subsetsig_zero `{Zero A} `{!SubsetSig_Closed S 0} : Zero SubsetSig := exist _ 0 _.
  Program Instance subsetsig_one  `{One  A} `{!SubsetSig_Closed S 1} : One  SubsetSig := exist _ 1 _.
  Program Instance subsetsig_plus `{Plus A} `{!SubsetSig_Closed (S⇀S⇀S) (+)} : Plus SubsetSig := λ x y, exist _ (`x + `y) _.
  Program Instance subsetsig_mult `{Mult A} `{!SubsetSig_Closed (S⇀S⇀S) (.*.)}:Mult SubsetSig := λ x y, exist _ (`x * `y) _.
  Program Instance subsetsig_negate `{Negate A} `{!SubsetSig_Closed (S⇀S) (-)} : Negate SubsetSig := λ x, exist _ (- `x) _.
  Solve All Obligations with (apply _).

  Instance: ∀ `{Zero A} `{!SubsetSig_Closed S 0}, 0 ∊ S := λ _ _, subsetsig_closed.

  Program Instance subsetsig_inv `{Inv A} `{Equiv A} `{UnEq A} `{!StandardUnEq S} `{!SubDecision S S (=)}
    `{Zero A} `{!SubsetSig_Closed S 0} `{!SubsetSig_Closed (S ₀ ⇀ S ₀) inv} : Inv SubsetSig :=
   λ x, if (decide_sub (=) (`x) 0) then exist _ 0 _ else exist _ (inv (`x)) _.
  Next Obligation. destruct x as [x ?]; simpl in *.
    assert (x ∊ S ₀). split. apply _. now rewrite (standard_uneq x 0).
    apply NonZero_subset. apply _.
  Qed.

End defs.

Hint Extern 0 (@Subset (SubsetSig ?S)) => eexact (every (SubsetSig S)) : typeclass_instances.

Hint Extern 0 (Equiv  (SubsetSig ?S)) => eapply (subsetsig_equiv  S) : typeclass_instances.
Hint Extern 0 (UnEq   (SubsetSig ?S)) => eapply (subsetsig_uneq   S) : typeclass_instances.
Hint Extern 0 (Zero   (SubsetSig ?S)) => eapply (subsetsig_zero   S) : typeclass_instances.
Hint Extern 0 (One    (SubsetSig ?S)) => eapply (subsetsig_one    S) : typeclass_instances.
Hint Extern 0 (Plus   (SubsetSig ?S)) => eapply (subsetsig_plus   S) : typeclass_instances.
Hint Extern 0 (Mult   (SubsetSig ?S)) => eapply (subsetsig_mult   S) : typeclass_instances.
Hint Extern 0 (Negate (SubsetSig ?S)) => eapply (subsetsig_negate S) : typeclass_instances.
Hint Extern 0 (Inv    (SubsetSig ?S)) => eapply (subsetsig_inv    S) : typeclass_instances.


Definition SubsetSig_Quote `{Equiv} S x (sx : SubsetSig S) := x ∊ S ∧ x = ` sx.
Local Notation Quote := SubsetSig_Quote.

Local Existing Instance subsetsig_element.


Section quoting.

  Context {A} {Ae : Equiv A} {Azero:Zero A} {Aone: One A} {Aplus:Plus A} {Amult:Mult A} {Anegate:Negate A}.

  Context S `{!Setoid S}.

  Context {zero_closed  :SubsetSig_Closed S 0}.
  Context {one_closed   :SubsetSig_Closed S 1}.
  Context {plus_closed  :SubsetSig_Closed (S⇀S⇀S) (+)}.
  Context {mult_closed  :SubsetSig_Closed (S⇀S⇀S) (.*.)}.
  Context {negate_closed:SubsetSig_Closed (S⇀S) (-)}.

  Context {plus_proper  :Morphism (S ⇒ S ⇒ S) (+)}.
  Context {mult_proper  :Morphism (S ⇒ S ⇒ S) (.*.)}.
  Context {negate_proper:Morphism (S ⇒ S) (-)}.

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

  Context {Aue : UnEq A} {Ainv : Inv A} `{!StandardUnEq S} `{!SubDecision S S (=)}
    {inv_closed : SubsetSig_Closed (S ₀ ⇀ S ₀) inv}
    {inv_proper : Morphism (S ₀ ⇒ S ₀) inv}.

  Instance: 0 ∊ S := zero_closed.

  Lemma subsetsig_quote_inv `{x ∊ S ₀} `(E:Quote S x sx) : Quote S (inv x) (inv sx).
  Proof. destruct E as [? E]. unfold inv at 2. unfold subsetsig_inv.
    destruct sx as [y ?]; simpl in *. assert (y ∊ S ₀) by now rewrite <- (S $ E).
    destruct (decide_sub (=) y 0) as [E1|E2].
    + contradict E1. rewrite <- (standard_uneq _ _). now destruct (_ : y ∊ S ₀).
    + pose proof _ : inv x ∊ S ₀ . split. apply _. simpl. now rewrite <- (S ₀ $ E).
  Qed.

End quoting.

Ltac subsetsig_quote S :=
  let rec aux expr :=
    match expr with
    | @zero _ _ => constr:(subsetsig_quote_zero S)
    | @one _ _ => constr:(subsetsig_quote_one S)
    | @plus _ _ ?x ?y => let qx := aux x in let qy := aux y in constr:(subsetsig_quote_plus S qx qy)
    | @mult _ _ ?x ?y => let qx := aux x in let qy := aux y in constr:(subsetsig_quote_mult S qx qy)
    | @negate _ _ ?x => let qx := aux x in constr:(subsetsig_quote_negate S qx)
    | @inv _ _ ?x => let qx := aux x in constr:(subsetsig_quote_inv S qx)
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

Lemma subsetsig_eq_equiv `{S:Subset} `{Setoid _ (S:=S)} : Equivalence (@equiv (SubsetSig S) _).
Proof. split.
+ intros [x ?]. change (x=x). subreflexivity.
+ intros [x ?] [y ?] P. change (x=y) in P. change (y=x). subsymmetry.
+ intros [x ?] [y ?] [z ?] P Q. change (x=y) in P. change (y=z) in Q. change (x=z). subtransitivity y.
Qed.
Hint Extern 0 (Equivalence (@equiv (SubsetSig _) _)) => eapply @subsetsig_eq_equiv : typeclass_instances.

Lemma subsetsig_setoid `{S:Subset} `{Setoid _ (S:=S)} : Setoid (every (SubsetSig S)).
Proof. red. apply _. Qed.
Hint Extern 0 (@Setoid (SubsetSig _) _ _) => eapply @subsetsig_setoid : typeclass_instances.

Section propers.
  Context {A} {Ae : Equiv A} {Azero:Zero A} {Aone: One A} {Aplus:Plus A} {Amult:Mult A} {Anegate:Negate A}.

  Context (S:@Subset A).

  Context {zero_closed  :SubsetSig_Closed S 0}.
  Context {one_closed   :SubsetSig_Closed S 1}.
  Context {plus_closed  :SubsetSig_Closed (S⇀S⇀S) (+)}.
  Context {mult_closed  :SubsetSig_Closed (S⇀S⇀S) (.*.)}.
  Context {negate_closed:SubsetSig_Closed (S⇀S) (-)}.

  Context `{!Setoid S}.
  Context {plus_proper  :Morphism (S ⇒ S ⇒ S) (+)}.
  Context {mult_proper  :Morphism (S ⇒ S ⇒ S) (.*.)}.
  Context {negate_proper:Morphism (S ⇒ S) (-)}.

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

  Context {Aue : UnEq A} {Ainv : Inv A} `{!StandardUnEq S} `{!SubDecision S S (=)}
    {inv_closed : SubsetSig_Closed (S ₀ ⇀ S ₀) inv}
    {inv_proper : Morphism (S ₀ ⇒ S ₀) inv}.

  Instance: 0 ∊ S := zero_closed.

  Global Instance: Proper ((=)==>(=)) (@inv (SubsetSig S) _).
  Proof. intros [x1 ?] [x2 ?] E1. change (x1=x2) in E1.
    unfold inv, subsetsig_inv; simpl.
    destruct (decide_sub (=) x1 0) as [E0|E0]; destruct (decide_sub (=) x2 0) as [E0'|E0'];
    unfold equiv, subsetsig_equiv; simpl.
    + easy.
    + contradict E0'. subtransitivity x1; subsymmetry.
    + contradict E0. subtransitivity x2.
    + rewrite <- (standard_uneq _ _) in E0. rewrite <- (standard_uneq _ _) in E0'.
      assert (x1 ∊ S ₀) by now split. assert (x2 ∊ S ₀) by now split.
      pose proof _ : inv x1 ∊ S ₀ . now rewrite <- (S ₀ $ E1).
  Qed.
End propers.

Require Import theory.fields.

Section transference.
  Context {A} {Ae : Equiv A} {Azero:Zero A} {Aone: One A} {Aplus:Plus A} {Amult:Mult A} {Anegate:Negate A}.

  Context (S:@Subset A).

  Context {zero_closed  :SubsetSig_Closed S 0}.
  Context {one_closed   :SubsetSig_Closed S 1}.
  Context {plus_closed  :SubsetSig_Closed (S⇀S⇀S) (+)}.
  Context {mult_closed  :SubsetSig_Closed (S⇀S⇀S) (.*.)}.
  Context {negate_closed:SubsetSig_Closed (S⇀S) (-)}.

  Local Notation S' := (every (SubsetSig S)).

  Instance subsetsig_plus_monoid `{!AdditiveMonoid S} : AdditiveMonoid S'.
  Proof. split. split. split. apply _.
  + intros [x ?] _ [y ?] _ [z ?] _. exact (associativity (+) x y z).
  + apply binary_morphism_proper_back.
    intros x1 x2 [_ E1] y1 y2 [_ E2]. red_sig. change (x1+y1 = x2+y2). now rewrite E1, E2.
  + intros [x ?] _ [y ?] _. exact (commutativity (+) x y).
  + apply _.
  + intros [x ?] ?. exact (left_identity (+) x).
  Qed.

  Instance subsetsig_plus_group `{!AdditiveGroup S} : AdditiveGroup S'.
  Proof. split. apply _.
  + intros x1 x2 [_ E1]. red_sig. change (-x1 = -x2). now rewrite E1.
  + intros [x ?] ?. exact (left_inverse (&) x).
  Qed.

  Instance subsetsig_mult_semigroup `{!MultiplicativeSemiGroup S} : MultiplicativeSemiGroup S'.
  Proof. split. apply _.
  + intros [x ?] _ [y ?] _ [z ?] _. exact (associativity (.*.) x y z).
  + apply binary_morphism_proper_back.
    intros x1 x2 [_ E1] y1 y2 [_ E2]. red_sig. change (x1*y1 = x2*y2). now rewrite E1, E2.
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


  Instance subsetsig_standard_uneq {Aue : UnEq A} `{!StandardUnEq S} : StandardUnEq S'.
  Proof. intros [x ?] _ [y ?] _. exact (standard_uneq x y). Qed.

  Instance subsetsig_dec_eq `{!SubDecision S S (=)} (x y : SubsetSig S) : Decision (x = y).
  Proof. destruct x as [x ?]. destruct y as [y ?]. exact (decide_sub (=) x y). Qed.

  Context {Aue : UnEq A} {Ainv : Inv A} `{!StandardUnEq S} `{!SubDecision S S (=)}
    {inv_closed : SubsetSig_Closed (S ₀ ⇀ S ₀) inv}.

  Instance subsetsig_nontrivial `{el: 1 ∊ S ₀} : 1 ∊ S' ₀.
  Proof. destruct el. split. apply _. trivial. Qed.

  Instance subsetsig_dec_field `{!Field S} : Field S'.
  Proof. apply dec_field.
  + intros x y [[[_ Ex] [_ Ey]] E].
    split; [| now rewrite E].
    destruct x as [x ?], y as [y ?].
    assert (x ∊ S ₀) by now split. assert (y ∊ S ₀) by now split.
    unfold inv, subsetsig_inv; simpl.
    destruct (decide_sub (=) x 0). rewrite (standard_uneq _ _) in Ex. contradiction.
    destruct (decide_sub (=) y 0). rewrite (standard_uneq _ _) in Ey. contradiction.
    split; (split; [apply _ |]).
    now destruct (_ : inv x ∊ S ₀).
    now destruct (_ : inv y ∊ S ₀).
  + apply _.
  + intros [x ?] [_ Ex]. assert (x ∊ S ₀) by now split.
    unfold inv, subsetsig_inv; simpl.
    destruct (decide_sub (=) x 0). rewrite (standard_uneq _ _) in Ex. contradiction.
    exact (field_inv_l x).
  Qed.

End transference.
