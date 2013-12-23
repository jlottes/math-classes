Require Import abstract_algebra theory.setoids theory.common_props.

(*
Class SubsetSig_Closed {A} (R:@Subset A) (f:A) := subsetsig_closed : Closed R f.
*)

(*Local Existing Instance subsetsig_closed.*)
Local Existing Instance closed_range.
Local Existing Instance closed_binary.

Section defs.

  Context `(S:set).

  Definition setsig := {x | x ∊ S}.

  Definition to_sig x {pf:x ∊ S} : setsig := exist _ x pf.

  Instance setsig_element (sx: setsig) : ` sx ∊ S. Proof. destruct sx as [? el]. exact el. Qed.

  Instance setsig_equiv `{Equiv _} : Equiv setsig := λ x y, ` x = ` y.
  Instance setsig_uneq  `{UnEq  _} : UnEq  setsig := λ x y, ` x ≠ ` y.
  Program Instance setsig_zero   `{Zero   _} {pf:0 ∊ S}                : Zero   setsig := 0:S.
  Program Instance setsig_one    `{One    _} {pf:1 ∊ S}                : One    setsig := 1:S.
  Program Instance setsig_plus   `{Plus   _} {pf:Closed (S⇀S⇀S) (+)  } : Plus   setsig := (+) : S⇀S⇀S.
  Program Instance setsig_mult   `{Mult   _} {pf:Closed (S⇀S⇀S) (.*.)} : Mult   setsig := (.*.) : S⇀S⇀S.
  Program Instance setsig_negate `{Negate _} {pf:Closed (S⇀S)   (-)  } : Negate setsig := (-) : S⇀S.
  Solve All Obligations using (apply _).

  (*Instance: ∀ `{Zero A} `{!SubsetSig_Closed S 0}, 0 ∊ S := λ _ _, subsetsig_closed.*)

  Program Instance setsig_inv `{Inv _} `{Equiv _} `{UnEq _} `{!DenialInequality S} `{!SubDecision S S (=)}
    `{Zero _} {pf0:0 ∊ S} {pfi:Closed (S ₀ ⇀ S ₀) inv} : Inv setsig :=
   λ x, if (decide_sub (=) (`x) 0) then 0:S else inv (`x).
  Next Obligation. destruct x as [x ?]. simpl in *.
    assert (x ∊ S ₀). split. apply _. red. now rewrite (denial_inequality x 0).
    apply NonZero_subset. apply _.
  Qed.

End defs.

Hint Extern 5 (@set (setsig ?S)) => eexact (every (setsig S)) : typeclass_instances.

Hint Extern 2 (Equiv  (setsig ?S)) => eapply (setsig_equiv  S) : typeclass_instances.
Hint Extern 2 (UnEq   (setsig ?S)) => eapply (setsig_uneq   S) : typeclass_instances.
Hint Extern 2 (Equiv  {x | x ∊ ?S}) => eapply (setsig_equiv  S) : typeclass_instances.
Hint Extern 2 (UnEq   {x | x ∊ ?S}) => eapply (setsig_uneq   S) : typeclass_instances.
Hint Extern 2 (Equiv  (@sig _ (@Element _ ?S))) => eapply (setsig_equiv  S) : typeclass_instances.
Hint Extern 2 (UnEq   (@sig _ (@Element _ ?S))) => eapply (setsig_uneq   S) : typeclass_instances.
Local Hint Extern 2 (Zero   (setsig ?S)) => eapply (setsig_zero   S) : typeclass_instances.
Local Hint Extern 2 (One    (setsig ?S)) => eapply (setsig_one    S) : typeclass_instances.
Local Hint Extern 2 (Plus   (setsig ?S)) => eapply (setsig_plus   S) : typeclass_instances.
Local Hint Extern 2 (Mult   (setsig ?S)) => eapply (setsig_mult   S) : typeclass_instances.
Local Hint Extern 2 (Negate (setsig ?S)) => eapply (setsig_negate S) : typeclass_instances.
Local Hint Extern 2 (Inv    (setsig ?S)) => eapply (setsig_inv    S) : typeclass_instances.


Definition Setsig_Quote `{Equiv} S x (sx : setsig S) := (S,=)%signature x (`sx).
Local Notation Quote := Setsig_Quote.

Local Existing Instance setsig_element.


Section quoting.

  Context {A} {Ae : Equiv A} {Azero:Zero A} {Aone: One A} {Aplus:Plus A} {Amult:Mult A} {Anegate:Negate A}.

  Context S `{!Setoid S}.

  Context (zero_closed  :0 ∊ S).
  Context (one_closed   :1 ∊ S).
  Context (plus_closed  :Closed (S⇀S⇀S) (+)).
  Context (mult_closed  :Closed (S⇀S⇀S) (.*.)).
  Context (negate_closed:Closed (S⇀S) (-)).

  Context {plus_proper  :Morphism (S ⇒ S ⇒ S) (+)}.
  Context {mult_proper  :Morphism (S ⇒ S ⇒ S) (.*.)}.
  Context {negate_proper:Morphism (S ⇒ S) (-)}.

  Local Ltac destr E := match type of E with Quote _ _ ?sx => destruct E as [[? _] E], sx as [??]; simpl in E end.

  Lemma setsig_quote_equiv_correct {x sx y sy} (E1:Quote S x sx) (E2:Quote S y sy) : sx = sy ↔ x = y.
  Proof. destr E1. destr E2. unfold equiv at 1, setsig_equiv. simpl. now rewrite_on S -> E1, E2. Qed.

  Local Ltac solve E      := destr E;            red; red_sig; simpl; now rewrite_on S -> E.
  Local Ltac solve2 E1 E2 := destr E1; destr E2; red; red_sig; simpl; now rewrite_on S -> E1, E2.

  Lemma setsig_quote_base x {pf:x ∊ S} : Quote S x (@to_sig _ _ x pf). Proof. red. now red_sig. Qed.
  Lemma setsig_quote_zero : Quote S 0 0. Proof. red. now red_sig. Qed.
  Lemma setsig_quote_one  : Quote S 1 1. Proof. red. now red_sig. Qed.
  Lemma setsig_quote_plus `(E1:Quote S x sx) `(E2:Quote S y sy) : Quote S (x+y) (sx+sy). Proof. solve2 E1 E2. Qed.
  Lemma setsig_quote_mult `(E1:Quote S x sx) `(E2:Quote S y sy) : Quote S (x*y) (sx*sy). Proof. solve2 E1 E2. Qed.
  Lemma setsig_quote_negate `(E:Quote S x sx) : Quote S (-x) (-sx). Proof. solve E. Qed.

  Context {Aue : UnEq A} {Ainv : Inv A} `{!DenialInequality S} `{!SubDecision S S (=)}
    (inv_closed : Closed (S ₀ ⇀ S ₀) inv)
    {inv_proper : Morphism (S ₀ ⇒ S ₀) inv}.

  (*Instance: 0 ∊ S := zero_closed.*)

  Lemma setsig_quote_inv `{x ∊ S ₀} `(E:Quote S x sx) : Quote S (inv x) (inv sx).
  Proof. destruct E as [[? _] E], sx as [y ?]; simpl in E. unfold inv at 2. unfold setsig_inv. simpl.
    destruct (decide_sub equiv y 0) as [E1|E1].
    + contradict E1. rewrite <-(_ $ E), <- (denial_inequality _ _). now destruct (_ : x ∊ S ₀).
    + pose proof _ : inv x ∊ S ₀ . red. red_sig. simpl.
      assert (y ∊ S ₀). split. apply _. red. now rewrite (denial_inequality _ _).
      now rewrite <- (S ₀ $ E).
  Qed.

End quoting.

Ltac setsig_quote S zc oc pc mc nc ic :=
  let rec aux expr :=
    match expr with
    | @zero _ _ => constr:(setsig_quote_zero S zc)
    | @one _ _ => constr:(setsig_quote_one S oc)
    | @plus _ _ ?x ?y => let qx := aux x in let qy := aux y in constr:(setsig_quote_plus S pc qx qy)
    | @mult _ _ ?x ?y => let qx := aux x in let qy := aux y in constr:(setsig_quote_mult S mc qx qy)
    | @negate _ _ ?x => let qx := aux x in constr:(setsig_quote_negate S nc qx)
    | @inv _ _ ?x => let qx := aux x in constr:(setsig_quote_inv S zc ic qx)
    | _ => constr:(setsig_quote_base S expr)
    end
  in aux.

Ltac setsig_quote_equiv S q :=
  match goal with |- @equiv _ _ ?x ?y =>
    let qx := q x in
    let qy := q y in
    apply (proj1 (setsig_quote_equiv_correct S qx qy))
  end.

Require Import theory.groups theory.rings.

Lemma subsetsig_eq_equiv `{S:set} `{Setoid _ (S:=S)} : EquivalenceT (@equiv (setsig S) _).
Proof. split.
+ intros [x ?]. change (x=x). subreflexivity.
+ intros [x ?] [y ?] P. change (x=y) in P. change (y=x). subsymmetry.
+ intros [x ?] [y ?] [z ?] P Q. change (x=y) in P. change (y=z) in Q. change (x=z). subtransitivity y.
Qed.
Hint Extern 2 (EquivalenceT (@equiv _ (setsig_equiv _))) => eapply @subsetsig_eq_equiv : typeclass_instances.
Hint Extern 2 (Equivalence _ (@equiv _ (setsig_equiv _))) => eapply @every_Equivalence : typeclass_instances.
Hint Extern 2 (@Setoid (setsig _) _ _) => red : typeclass_instances.
Hint Extern 2 (@Setoid {x | x ∊ ?S} _ _) => red : typeclass_instances.

Section propers.
  Context {A} {Ae : Equiv A} {Azero:Zero A} {Aone: One A} {Aplus:Plus A} {Amult:Mult A} {Anegate:Negate A}.

  Context (S:@set A).

  Context {zero_closed  :0 ∊ S}.
  Context {one_closed   :1 ∊ S}.
  Context {plus_closed  :Closed (S⇀S⇀S) (+)}.
  Context {mult_closed  :Closed (S⇀S⇀S) (.*.)}.
  Context {negate_closed:Closed (S⇀S) (-)}.

  Context `{!Setoid S}.
  Context {plus_proper  :Morphism (S ⇒ S ⇒ S) (+)}.
  Context {mult_proper  :Morphism (S ⇒ S ⇒ S) (.*.)}.
  Context {negate_proper:Morphism (S ⇒ S) (-)}.

  Instance setsig_plus_proper: Proper ((=)==>(=)==>(=)) (@plus (setsig S) _).
  Proof. intros [x1 ?] [x2 ?] E1 [y1 ?] [y2 ?] E2.
      change (x1=x2) in E1. change (y1=y2) in E2. change (x1+y1 = x2+y2).
      rewrite_on S -> E1. now rewrite_on S -> E2.
  Qed.

  Instance setsig_mult_proper: Proper ((=)==>(=)==>(=)) (@mult (setsig S) _).
  Proof. intros [x1 ?] [x2 ?] E1 [y1 ?] [y2 ?] E2.
      change (x1=x2) in E1. change (y1=y2) in E2. change (x1*y1 = x2*y2).
      rewrite_on S -> E1. now rewrite_on S -> E2.
  Qed.

  Instance setsig_negate_proper: Proper ((=)==>(=)) (@negate (setsig S) _).
  Proof. intros [x1 ?] [x2 ?] E1.
      change (x1=x2) in E1. change (-x1 = -x2).
      now rewrite_on S -> E1.
  Qed.

  Context {Aue : UnEq A} {Ainv : Inv A} `{!DenialInequality S} `{!SubDecision S S (=)}
    {inv_closed : Closed (S ₀ ⇀ S ₀) inv}
    {inv_proper : Morphism (S ₀ ⇒ S ₀) inv}.

  (*Instance: 0 ∊ S := zero_closed.*)

  Instance setsig_inv_proper: Proper ((=)==>(=)) (@inv (setsig S) _).
  Proof. intros [x1 ?] [x2 ?] E1. change (x1=x2) in E1.
    unfold inv, setsig_inv; simpl.
    destruct (decide_sub (=) x1 0) as [E0|E0]; destruct (decide_sub (=) x2 0) as [E0'|E0'];
    unfold equiv, setsig_equiv; simpl.
    + easy.
    + contradict E0'. subtransitivity x1; subsymmetry.
    + contradict E0. subtransitivity x2.
    + rewrite <- (denial_inequality _ _) in E0. rewrite <- (denial_inequality _ _) in E0'.
      assert (x1 ∊ S ₀) by now split. assert (x2 ∊ S ₀) by now split.
      pose proof _ : inv x1 ∊ S ₀ . now rewrite <- (S ₀ $ E1).
  Qed.
End propers.

Hint Extern 2 (Proper _ (@plus   _ (setsig_plus   _))) => eapply @setsig_plus_proper : typeclass_instances.
Hint Extern 2 (Proper _ (@mult   _ (setsig_mult   _))) => eapply @setsig_mult_proper : typeclass_instances.
Hint Extern 2 (Proper _ (@negate _ (setsig_negate _))) => eapply @setsig_negate_proper : typeclass_instances.
Hint Extern 2 (Proper _ (@inv    _ (setsig_inv    _))) => eapply @setsig_inv_proper : typeclass_instances.

Require Import theory.fields.

Section transference.
  Context {A} {Ae : Equiv A} {Azero:Zero A} {Aone: One A} {Aplus:Plus A} {Amult:Mult A} {Anegate:Negate A}.

  Context (S:@set A).

  Context {zero_closed  :0 ∊ S}.
  Context {one_closed   :1 ∊ S}.
  Context {plus_closed  :Closed (S⇀S⇀S) (+)}.
  Context {mult_closed  :Closed (S⇀S⇀S) (.*.)}.
  Context {negate_closed:Closed (S⇀S) (-)}.

  Local Notation S' := (every (setsig S)).

  Instance setsig_plus_monoid `{!AdditiveMonoid S} : AdditiveMonoid S'.
  Proof. split. split. split. apply _.
  + intros [x ?] _ [y ?] _ [z ?] _. exact (associativity (+) x y z).
  + apply @binary_morphism_proper_back; try apply _.
    intros x1 x2 [_ E1] y1 y2 [_ E2]. red_sig. change (x1+y1 = x2+y2). now rewrite E1, E2.
  + intros [x ?] _ [y ?] _. exact (commutativity (+) x y).
  + apply _.
  + intros [x ?] ?. exact (left_identity (+) x).
  Qed.

  Instance setsig_plus_group `{!AdditiveGroup S} : AdditiveGroup S'.
  Proof. split. apply _.
  + intros x1 x2 [_ E1]. red_sig. change (-x1 = -x2). now rewrite E1.
  + intros [x ?] ?. exact (left_inverse (&) x).
  Qed.

  Instance setsig_mult_semigroup `{!MultiplicativeSemiGroup S} : MultiplicativeSemiGroup S'.
  Proof. split. apply _.
  + intros [x ?] _ [y ?] _ [z ?] _. exact (associativity (.*.) x y z).
  + apply @binary_morphism_proper_back; try apply _.
    intros x1 x2 [_ E1] y1 y2 [_ E2]. red_sig. change (x1*y1 = x2*y2). now rewrite E1, E2.
  Qed.

  Instance setsig_mult_commonoid `{!MultiplicativeComMonoid S} : MultiplicativeComMonoid S'.
  Proof. split. split. apply _.
  + intros [x ?] _ [y ?] _. exact (commutativity (.*.) x y).
  + apply _.
  + intros [x ?] _. exact (left_identity (&) x).
  Qed.

  Instance setsig_semirng `{!SemiRng S} : SemiRng S'.
  Proof. split. apply _. apply _.
  + intros [x ?] _ [y ?] _ [z ?] _. exact (plus_mult_distr_l x y z).
  + intros [x ?] _ [y ?] _ [z ?] _. exact (plus_mult_distr_r x y z).
  + intros [x ?] _. exact (mult_0_l x).
  + intros [x ?] _. exact (mult_0_r x).
  Qed.

  Instance setsig_semiring `{!SemiRing S} : SemiRing S'.
  Proof. split. apply _. apply _.
  + intros [x ?] _. exact (mult_1_l x).
  + intros [x ?] _. exact (mult_1_r x).
  Qed.

  Instance setsig_comsemiring `{!CommutativeSemiRing S} : CommutativeSemiRing S' := {}.

  Instance setsig_rng `{!Rng S} : Rng S' := {}.

  Instance setsig_ring `{!Ring S} : Ring S' := {}.

  Instance setsig_comring `{!CommutativeRing S} : CommutativeRing S' := {}.


  Instance setsig_denial_inequality {Aue : UnEq A} `{!DenialInequality S} : DenialInequality S'.
  Proof. intros [x ?] _ [y ?] _. exact (denial_inequality x y). Qed.

  Instance setsig_dec_eq `{!SubDecision S S (=)} (x y : {x | x ∊ S}) : Decision (x = y).
  Proof. destruct x as [x ?]. destruct y as [y ?]. exact (decide_sub (=) x y). Qed.

  Context {Aue : UnEq A} {Ainv : Inv A} `{!DenialInequality S} `{!SubDecision S S (=)}
    {inv_closed : Closed (S ₀ ⇀ S ₀) inv}.

  Instance setsig_nontrivial `{el: 1 ∊ S ₀} : 1 ∊ S' ₀.
  Proof. destruct el. split. apply _. trivial. Qed.

  Instance setsig_dec_field `{!Field S} : Field S'.
  Proof. apply dec_field.
  + intros x y [[[_ Ex] [_ Ey]] E]. red in Ex,Ey.
    split; [| now rewrite E].
    destruct x as [x ?], y as [y ?].
    assert (x ∊ S ₀) by now split. assert (y ∊ S ₀) by now split.
    unfold inv, setsig_inv; simpl.
    destruct (decide_sub (=) x 0). rewrite (denial_inequality _ _) in Ex. contradiction.
    destruct (decide_sub (=) y 0). rewrite (denial_inequality _ _) in Ey. contradiction.
    split; (split; [apply _ |]).
    now destruct (_ : inv x ∊ S ₀).
    now destruct (_ : inv y ∊ S ₀).
  + apply _.
  + intros [x ?] [_ Ex]. red in Ex. assert (x ∊ S ₀) by now split.
    unfold inv, setsig_inv; simpl.
    destruct (decide_sub (=) x 0). rewrite (denial_inequality _ _) in Ex. contradiction.
    exact (field_inv_l x).
  Qed.

End transference.
