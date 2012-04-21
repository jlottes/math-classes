Require Import
  abstract_algebra theory.subsetoids theory.common_props theory.subrings theory.products.
Require Import Ring stdlib_ring.

Local Open Scope grp_scope. (* notation for inverse *)

Definition FracPair (A:Type) := (A*A)%type.

Definition Frac {A} {Ae:Equiv A} {Azero:Zero A} D : Subset (FracPair _) 
  := λ f, let (a,b) := f in a ∊ D ∧ b ∊ D ₀.

Definition frac_equiv {A} {Ae:Equiv A} {Amult:Mult A} (f f' : FracPair _)
  := let (a,b) := f in let (c,d) := f' in a*d = b*c.

Lemma frac_equiv_proper : Find_Proper_Signature (@frac_equiv) 0
  (∀ `{CommutativeRing (R:=D)}, 
    Proper ((Frac D,prod_equiv) ==> (Frac D,prod_equiv) ==> impl) frac_equiv).
Proof. intro. intros. intros [a b] [c d] [[[??][??]][E1 E2]]
                             [e f] [g h] [[[??][??]][E3 E4]].
  intro E. simpl in E1,E2,E3,E4,E. simpl.
  rewrite_on D <- E1. rewrite_on D <- E2. rewrite_on D <- E3. now rewrite_on D <- E4.
Qed.
Hint Extern 0 (Find_Proper_Signature (@frac_equiv) 0 _) => eexact frac_equiv_proper : typeclass_instances.

Existing Instance NonZero_subset.

Section contents.

  Context `(D:Subset A) `{CommutativeRing (A:=A) (R:=D)} `{!IntegralDomain D} `{∀ x y, Stable (x = y)}.

  Instance: SubSetoid (Ae:=prod_equiv) (Frac D).
  Proof. split. apply _. intros [a b] [c d] [E1 E2] [??].
    simpl in E1, E2. split. now rewrite <-E1. now rewrite <-E2.
  Qed.

  Add Ring D1 : (stdlib_ring_theory D).

  Global Instance: SubEquivalence (Frac D) (frac_equiv).
  Proof. split.
  + intros [a b] [??]. exact (commutativity a b).
  + intros [a b] [??] [c d] [??] E. change (a*d = b*c) in E.
    change (c*b = d*a). rewrite (commutativity (f:=(.*.)) c b).
    rewrite <- E. exact (commutativity a d).
  + intros [a b] [??] [c d] [??] [e f] [??] E1 E2.
    change (a*d = b*c) in E1.
    change (c*f = d*e) in E2.
    change (a*f = b*e).
    apply (left_cancellation (.*.) d D (a*f) (b*e)).
    rewrite_on D -> (commutativity (f:=(.*.)) b e).
    rewrite (associativity (f:=(.*.)) d e b).
    rewrite (associativity (f:=(.*.)) d a f).
    rewrite_on D -> (commutativity (f:=(.*.)) d a).
    rewrite_on D -> E1. rewrite_on D <- E2.
    subring D.
  Qed.

  Instance frac_equiv_ext : Equiv (FracPair _) :=
    equiv_ext (Ae := prod_equiv) (Frac D) frac_equiv.

  Instance: SubSetoid (Frac D) := equiv_ext_subsetoid (Ae:=prod_equiv) (Frac D) frac_equiv.

  Instance frac_inject : Cast A (FracPair A) := λ x, pair x 1.

  Instance frac_zero   : Zero   (FracPair _) := pair 0 1.
  Instance frac_one    : One    (FracPair _) := pair 1 1.
  Instance frac_plus   : Plus   (FracPair _) := λ f f', let (a,b) := f in let (c,d) := f' in pair (a*d + b*c) (b*d).
  Instance frac_mult   : Mult   (FracPair _) := λ f f', let (a,b) := f in let (c,d) := f' in pair (a*c) (b*d).
  Instance frac_negate : Negate (FracPair _) := λ f, let (a,b) := f in pair (- a) b.
  Instance frac_inv    : Inv    (FracPair A) := λ f, let (a,b) := f in pair b a.

  Let ext_correct x `{!x ∊ Frac D} y `{!y ∊ Frac D} : x = y ↔ frac_equiv x y
    := equiv_ext_correct (Ae:=prod_equiv) (Frac D) frac_equiv x y.

  Local Ltac reduce :=
   rewrite ext_correct; [ simpl | split; apply _ .. ].
  Local Ltac dispatch1 E := change E; intros [a b] [??]; reduce; subring D.
  Local Ltac dispatch2 E := change E; intros [a b] [??] [c d] [??]; reduce; subring D.
  Local Ltac dispatch3 E := change E; intros [a b] [??] [c d] [??] [e f] [??]; reduce; subring D.

  Instance: CommutativeRing (Frac D).
  Proof. split. split. split. split. split. apply _.
  + dispatch3 (Associative (+) (Frac D)).
  + change (SubSetoid_Binary_Morphism (+) (Frac D) (Frac D) (Frac D)).
    split; try apply _. intros [a1 b1] [a2 b2] E1 [c1 d1] [c2 d2] E2. unfold_sigs.
    rewrite ext_correct in E1,E2; try apply _. simpl in E1,E2.
    destruct el, el0, el1, el2. split. split; split; apply _.
    reduce. transitivity (d1 * (a1 * b2) * d2 + b1 * (c1 * d2) * b2). subring D.
    rewrite_on D -> E1. rewrite_on D -> E2. subring D.
  + change (0 ∊ (Frac D)). split; apply _.
  + dispatch1 (LeftIdentity (+) 0 (Frac D)).
  + dispatch1 (RightIdentity (+) 0 (Frac D)).
  + change (SubSetoid_Morphism (-) (Frac D) (Frac D)).
    split; try apply _. intros [a1 b1] [a2 b2] E1. unfold_sigs.
    rewrite ext_correct in E1; try apply _. simpl in E1.
    destruct el, el0. split. split; split; apply _.
    reduce. rewrite <- (negate_mult_distr_l a1 b2). rewrite_on D -> E1. subring D.
  + dispatch1 (LeftInverse (+) (-) 0 (Frac D)).
  + dispatch1 (RightInverse (+) (-) 0 (Frac D)).
  + dispatch2 (Commutative (+) (Frac D)).
  + split. split. split. apply _.
  - dispatch3 (Associative (.*.) (Frac D)).
  - change (SubSetoid_Binary_Morphism (.*.) (Frac D) (Frac D) (Frac D)).
    split; try apply _. intros [a1 b1] [a2 b2] E1 [c1 d1] [c2 d2] E2. unfold_sigs.
    rewrite ext_correct in E1,E2; try apply _. simpl in E1,E2.
    destruct el, el0, el1, el2. split. split; split; apply _.
    reduce. transitivity ((a1*b2)*(c1*d2)). subring D.
    rewrite_on D -> E1. rewrite_on D -> E2. subring D.
  - change (1 ∊ (Frac D)). split; apply _.
  - dispatch1 (LeftIdentity (.*.) 1 (Frac D)).
  - dispatch1 (RightIdentity (.*.) 1 (Frac D)).
  - dispatch2 (Commutative (.*.) (Frac D)).
  + dispatch3 (LeftDistribute (.*.) (+) (Frac D)).
  Qed.

  Instance: SubSetoid_Morphism (cast A (FracPair A)) D (Frac D).
  Proof. split; try apply _. intros ?? E. unfold_sigs.
    split. split; split; apply _. unfold cast, frac_inject.
    reduce. rewrite_on D -> E. subring D.
  Qed.

  Instance: Ring_Morphism (cast A (FracPair A)) D (Frac D).
  Proof with try apply _. split... split...
  + split... intros x ? y ?. change ( ' (x+y) = 'x + 'y ). unfold cast, frac_inject.
    reduce. subring D.
  + split... intros x ? y ?. change ( ' (x*y) = 'x * 'y ). unfold cast, frac_inject.
    reduce. subring D.
  + exists (1:A). exists (_:1 ∊ D). reflexivity.
  Qed.

  Instance: Injective (cast A (FracPair A)) D (Frac D).
  Proof. rewrite <- (rng_mor_injective (R:=D) (R':=Frac D) (cast A (FracPair A))).
    intros x ? E. change (pair x 1 = 0) in E.
    rewrite ext_correct in E. simpl in E.
    transitivity (x*1). now rewrite (mult_1_r x). rewrite E. exact (right_absorb 1).
    split; apply _. apply _.
  Qed.

  Lemma frac_nonzero : (Frac D) ₀ = λ f, let (a,b) := f in a ∊ D ₀ ∧ b ∊ D ₀.
  Proof. intros [a b]. split.
  + intros [[??]nz]. split. split. apply _. mc_contradict nz.
    reduce. rewrite_on D -> nz. subring D. apply _.
  + intros [[? anz]?]. split. split; apply _. intro E1.
    rewrite ext_correct in E1. simpl in E1.
    mc_contradict anz. rewrite (mult_1_r a) in E1. now rewrite (right_absorb b) in E1.
    split; apply _. apply _.
  Qed.

  Instance: Field (Frac D).
  Proof. split. apply _.
  + intro E1. rewrite ext_correct in E1; try apply _. simpl in E1.
    rewrite (mult_1_l 1), (mult_1_l 0) in E1.
    pose proof intdom_nontrivial. contradiction.
  + change (SubSetoid_Morphism (⁻¹) (Frac D ₀) (Frac D ₀)).
    split; try apply _. intros [a1 b1] [a2 b2] E1. unfold_sigs.
    rewrite ext_correct in E1; try apply _. simpl in E1.
    rewrite frac_nonzero in el, el0. destruct el, el0.
    split. split. change ( (pair a1 b1)⁻¹ ∊ (Frac D) ₀ ). rewrite frac_nonzero. now split.
                  change ( (pair a2 b2)⁻¹ ∊ (Frac D) ₀ ). rewrite frac_nonzero. now split.
    reduce. now symmetry.
  + intros [a b] el. rewrite frac_nonzero in el. destruct el. reduce. subring D.
  Qed.

End contents.




